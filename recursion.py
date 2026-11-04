"""
recursion.py
------------
Turns a directly recursive function into a recurrence relation.

Steps
  1. Walk every execution path of the body and collect the recursive calls on
     that path. (A path that RETURNs stops there, so  IF n<=1 RETURN ... END
     followed by f(n-1)  gives the paths  []  and  [f(n-1)] .)
  2. Choose a *size measure*: a parameter p (size = p) or a range pair such as
     (lo, hi) (size = hi - lo). The measure must strictly shrink in every
     recursive call. Arguments are understood through linear forms, so
     mid = (lo+hi)/2 ; f(A, lo, mid) ; f(A, mid+1, hi)  halves the size.
  3. Estimate the non-recursive work f(n) with ComplexityAnalyzer.
"""

import re
from fractions import Fraction

from complexity import (
    SIZE_VAR, Complexity, ComplexityAnalyzer, Unsupported, sum_over_vertices,
)
from expressions import (
    CONST, ExprError, assigned_variables, classify_collection, extract_calls,
    find_range_pair, has_guard_text, linear_form, new_value_tree, node_texts,
    numeric_value, parse_assignment, parse_expr, variables_of, walk,
)

_TREE_ATTR = re.compile(
    r"^(?:\w+|tree\[\w+\]|t\[\w+\])\.(?:left|right|next|child\w*|lchild|rchild|son\w*|kid\w*|first\w*"
    r"|sibling|nextsibling|left_child|right_child)$", re.IGNORECASE)
_TREE_FUNC = re.compile(
    r"^(?:left|right|child|lchild|rchild|first_?child|next_?sibling|left_?child|right_?child)\w*\(\s*\w+\s*\)$",
    re.IGNORECASE)
_TREE_INDEX = re.compile(r"^(?:left|right|lchild|rchild|child)\w*\[.+\]$", re.IGNORECASE)

MAX_PATHS = 128


class RecCall:
    """One recursive call:  mult * T(size')  with size' = n-k  or  c*n."""

    def __init__(self, kind, amount, mult=1):
        self.kind = kind          # 'DEC' (n - amount)  or  'DIV' (amount * n)
        self.amount = Fraction(amount)
        self.mult = mult          # int, or Complexity for calls inside loops

    def __str__(self):
        if self.kind == "SPLIT":
            term = "T(part)"
        elif self.kind == "SQRT":
            term = "T(sqrt(n))"
        elif self.kind == "MOD":
            term = "T(n mod k)"
        elif self.kind == "DEC":
            term = f"T(n-{_num(self.amount)})"
        else:
            c = self.amount
            term = (f"T(n/{c.denominator})" if c.numerator == 1
                    else f"T({c.numerator}n/{c.denominator})")
        if isinstance(self.mult, Complexity):
            return f"({self.mult.body()})*{term}"
        return term if self.mult == 1 else f"{self.mult}{term}"


def _num(q):
    return str(q.numerator) if q.denominator == 1 else f"{float(q):g}"


class Recurrence:
    def __init__(self, function_name, parameters):
        self.function_name = function_name
        self.parameters = parameters
        self.measure = None            # ('single', index) | ('range', lo, hi)
        self.size_text = ""
        self.alternatives = []         # list of list[RecCall]
        self.work = Complexity.const()
        self.warnings = []
        self.error = None
        self.direct_result = None      # set for traversal (structural) recursion
        self.notes = []
        self.shared = False
        self.description_lines = None

    @property
    def recursive_calls(self):
        return max(self.alternatives, key=len, default=[])

    def describe(self):
        if self.description_lines is not None:
            return list(self.description_lines)
        lines = []
        for calls in self.alternatives:
            if not calls:
                continue
            merged = {}
            for call in calls:
                key = (call.kind, call.amount, id(call.mult)
                       if isinstance(call.mult, Complexity) else None)
                if key in merged and not isinstance(call.mult, Complexity):
                    merged[key].mult += call.mult
                else:
                    merged[key] = RecCall(call.kind, call.amount, call.mult)
            text = " + ".join(str(c) for c in merged.values())
            line = f"T(n) = {text} + {self.work}"
            if line not in lines:
                lines.append(line)
        return lines


class Summary:
    """What other functions need to know to cost a call to a recursive one."""

    def __init__(self, complexity, measure, shared=False):
        self.complexity = complexity
        self.measure = measure
        self.shared = shared

    def measure_value(self, args, evaluate, default):
        if self.measure[0] == "single":
            index = self.measure[1]
            return evaluate(args[index]) if index < len(args) else default
        _, lo, hi = self.measure
        if hi >= len(args) or lo >= len(args):
            return default
        return evaluate(args[hi]).add(evaluate(args[lo]))


class _Call:
    __slots__ = ("args", "factor", "loops")

    def __init__(self, args, factor=1, loops=()):
        self.args, self.factor, self.loops = tuple(args), factor, tuple(loops)

    def signature(self):
        return (self.args, self.factor, tuple(id(l) for l in self.loops))


def _tree_vars(tree, out):
    if tree[0] == "var":
        out.add(tree[1])
    for part in tree[1:]:
        if isinstance(part, tuple):
            _tree_vars(part, out)
        elif isinstance(part, list):
            for item in part:
                if isinstance(item, tuple):
                    _tree_vars(item, out)


class RecursionAnalyzer:
    def __init__(self, program=None):
        self.program = program

    # ------------------------------------------------------------------
    def analyze(self, nodes):
        """Recurrences for every directly recursive function in `nodes`."""
        results = []
        for node in nodes:
            if node.get("type") == "FUNCTION":
                recurrence = self.analyze_function(node)
                if recurrence is not None:
                    results.append(recurrence)
        return results

    def analyze_function(self, node):
        name = node["name"]
        params = node.get("parameters", [])
        recurrence = Recurrence(name, params)
        try:
            paths = self._paths(node.get("body", []), name)
        except Unsupported as error:
            recurrence.error = str(error)
            return recurrence if self._calls_itself(node) else None

        if not any(calls for calls, _ in paths):
            return None

        if all(calls for calls, _ in paths):
            recurrence.warnings.append(
                "No execution path without a recursive call was found; the "
                "recursion may never terminate (missing base case?)."
            )

        defs, self._unknown = self._local_definitions(node, params)
        chosen = None
        seen_args = []
        for measure in self._candidates(params):
            outcome = self._apply_measure(measure, params, paths, defs)
            if outcome is not None:
                chosen = (measure, outcome)
                break
        if chosen is None:
            structural = self._structural(node, paths, params, recurrence)
            if structural is not None:
                return structural
            for calls, _ in paths:
                for call in calls:
                    seen_args.append(f"{name}({', '.join(call.args)})")
            shown = ", ".join(list(dict.fromkeys(seen_args))[:3])
            recurrence.error = (
                "no parameter (or lo/hi range) strictly shrinks by a constant "
                f"amount or factor in every recursive call. Calls seen: {shown}. "
                "Data-dependent arguments (e.g. a pivot position) cannot be solved."
            )
            return recurrence

        measure, rec_paths = chosen
        analyzer = self._work_analyzer(node, measure, params)

        for calls in rec_paths:
            resolved = []
            for kind, amount, call in calls:
                resolved.append(RecCall(kind, amount,
                                        self._resolve_mult(call, analyzer)))
            recurrence.alternatives.append(resolved)

        recurrence.work = analyzer.analyze(node.get("body", []))
        recurrence.warnings.extend(analyzer.warnings)
        if measure[0] == "single":
            recurrence.measure = ("single", params.index(measure[1]))
            recurrence.size_text = f"n = {measure[1]}"
        else:
            recurrence.measure = ("range", params.index(measure[1]),
                                  params.index(measure[2]))
            recurrence.size_text = f"n = {measure[2]} - {measure[1]}"
        return recurrence

    # ------------------------------------------------------------------
    def _calls_itself(self, node):
        for inner in walk(node.get("body", [])):
            for text in node_texts(inner):
                if any(n == node["name"] for n, _ in extract_calls(text)):
                    return True
        return False

    # ---- paths ---------------------------------------------------------
    def _paths(self, nodes, name):
        paths = [((), False)]
        for node in nodes:
            options = self._node_paths(node, name)
            expanded = []
            for calls, done in paths:
                if done:
                    expanded.append((calls, done))
                    continue
                for more, finished in options:
                    expanded.append((calls + more, finished))
            paths = self._dedupe(expanded)
        return paths

    @staticmethod
    def _dedupe(paths):
        seen, unique = set(), []
        for calls, done in paths:
            key = (tuple(c.signature() for c in calls), done)
            if key not in seen:
                seen.add(key)
                unique.append((calls, done))
        if len(unique) > MAX_PATHS:
            raise Unsupported("too many different execution paths to analyse")
        return unique

    @staticmethod
    def _calls_in(text, name):
        return tuple(_Call(args) for n, args in extract_calls(text) if n == name)

    def _node_paths(self, node, name):
        kind = node.get("type")
        if kind in ("OPERATION", "FUNCTION_CALL"):
            return [(self._calls_in(" ".join(node_texts(node)), name), False)]
        if kind == "RETURN":
            return [(self._calls_in(node.get("value") or "", name), True)]
        if kind == "IF":
            prefix = self._calls_in(node.get("condition", ""), name)
            options = self._paths(node.get("true_body", []), name)
            options += self._paths(node.get("false_body", []), name)
            return [(prefix + calls, done) for calls, done in options]
        if kind in ("FOR", "WHILE", "REPEAT_UNTIL", "DO_WHILE"):
            prefix = self._calls_in(" ".join(node_texts(node)), name)
            scaled = []
            for calls, _ in self._paths(node.get("body", []), name):
                scaled.append((tuple(
                    _Call(c.args, c.factor, c.loops + (node,)) for c in calls
                ), False))
            return [(prefix + calls, False) for calls, _ in scaled]
        return [((), False)]

    # ---- measures ------------------------------------------------------
    @staticmethod
    def _candidates(params):
        candidates = []
        pair = find_range_pair(params)
        if pair:
            candidates.append(("range", pair[0], pair[1]))
        candidates.extend(("single", p) for p in params)
        # a counter that grows towards a fixed bound: size = bound - counter
        for lo in params:
            for hi in params:
                if lo != hi and (pair is None or (lo, hi) != pair):
                    candidates.append(("range", lo, hi))
        return candidates

    @staticmethod
    def _local_definitions(node, params):
        defs, bad = {}, set()
        for inner in walk(node.get("body", [])):
            if inner.get("type") == "FOR":
                bad.add(inner.get("variable"))
            if inner.get("type") != "OPERATION":
                continue
            assignment = parse_assignment(inner.get("code", ""))
            if not assignment:
                continue
            for target in assignment.targets:
                if target in params:
                    continue
                if len(assignment.targets) > 1 or assignment.op != "=":
                    bad.add(target)
                    continue
                tree = new_value_tree(assignment)
                used = set()
                if tree is not None:
                    _tree_vars(tree, used)
                if tree is None or target in used:
                    bad.add(target)
                elif target in defs and defs[target] != tree:
                    bad.add(target)
                else:
                    defs[target] = tree
        unknown = {k for k, v in defs.items()
                   if k not in bad and linear_form(v) is None}
        linear = {k: v for k, v in defs.items()
                  if k not in bad and linear_form(v) is not None}
        return linear, unknown

    def _transform(self, measure, params, call, defs):
        """-> ('DEC', k) | ('DIV', c) | ('SQRT', c) | ('MOD', c) | ('CONST',) | None"""
        try:
            if measure[0] == "single":
                index = params.index(measure[1])
                if index >= len(call.args):
                    return None
                arg_raw = call.args[index]
                clean_arg = re.sub(r"\s+", "", arg_raw).lower()
                m_var = measure[1].lower()
                if (clean_arg in (f"sqrt({m_var})", f"floor(sqrt({m_var}))", f"ceil(sqrt({m_var}))", f"{m_var}^(1/2)", f"{m_var}^0.5")
                    or re.fullmatch(rf"(?:floor|ceil)?\(?sqrt\({m_var}\)\)?", clean_arg)):
                    return ("SQRT", Fraction(1, 2))
                if ("%" in clean_arg or "mod" in clean_arg) or any(("%" in a or "mod" in a) for a in call.args):
                    return ("MOD", Fraction(1, 2))
                out = linear_form(parse_expr(arg_raw), defs)
                inner = {measure[1]: Fraction(1)}
            else:
                _, lo, hi = measure
                lo_i, hi_i = params.index(lo), params.index(hi)
                if max(lo_i, hi_i) >= len(call.args):
                    return None
                low = linear_form(parse_expr(call.args[lo_i]), defs)
                high = linear_form(parse_expr(call.args[hi_i]), defs)
                if low is None or high is None:
                    return None
                out = dict(high)
                for key, value in low.items():
                    out[key] = out.get(key, 0) - value
                inner = {hi: Fraction(1), lo: Fraction(-1)}
        except (ExprError, ValueError):
            return None
        if out is None:
            return None
        out_vars = {k: v for k, v in out.items() if k != CONST and v != 0}
        offset = out.get(CONST, Fraction(0))
        if not out_vars:
            return ("CONST",)
        extra = set(out_vars) - set(inner)
        if extra:
            if extra <= getattr(self, "_unknown", set()) \
                    and extra.isdisjoint(params):
                return ("SPLIT", Fraction(1))      # data-dependent split point
            return None
        ratios = {out_vars.get(v, Fraction(0)) / c for v, c in inner.items()}
        if len(ratios) != 1:
            return None
        ratio = ratios.pop()
        if ratio <= 0:
            return None
        if ratio < 1:
            return ("DIV", ratio)
        if ratio == 1 and offset < 0:
            return ("DEC", -offset)
        return None

    def _apply_measure(self, measure, params, paths, defs):
        result, shrinks = [], False
        for calls, _ in paths:
            row = []
            for call in calls:
                transform = self._transform(measure, params, call, defs)
                if transform is None:
                    return None
                if transform[0] == "CONST":
                    continue            # size-independent call: O(1) leaf
                shrinks = True
                row.append((transform[0], transform[1], call))
            result.append(row)
        return result if shrinks else None

    # ---- traversal recursion (trees and graphs) -----------------------
    def _arg_kind(self, arg, call):
        text = re.sub(r"\s+", "", arg)
        if _TREE_ATTR.match(text) or _TREE_FUNC.match(text) or _TREE_INDEX.match(text):
            return "tree"
        kind = classify_collection(text)
        if kind == "children":
            return "tree"
        if kind == "adj":
            return "graph"
        if re.fullmatch(r"\w+", text):
            for loop in call.loops:
                if loop.get("type") == "FOR" and loop.get("collection") is not None:
                    names = loop.get("variables") or [loop.get("variable")]
                    if text in names:
                        found = classify_collection(loop["collection"])
                        if found == "children":
                            return "tree"
                        if found == "adj":
                            return "graph"
        return None

    def _structural(self, node, paths, params, recurrence):
        """
        Recursion that walks a tree (node.left, children ...) or a graph
        (neighbours of v, guarded by a visited check). Every vertex is entered
        once, so  total = sum over vertices of the work of one call, where the
        work of looping over a vertex's neighbours adds up to E overall.
        """
        calls = [c for calls_, _ in paths for c in calls_]
        kinds = None
        for index in range(len(params)):
            row = [self._arg_kind(c.args[index], c) if index < len(c.args) else None
                   for c in calls]
            if row and all(row):
                kinds = row
                break
        if kinds is None:
            return None
        graph = "graph" in kinds
        body = node.get("body", [])
        if graph and not any(
            has_guard_text(n.get("condition", ""))
            for n in walk(body) if n.get("type") == "IF"
        ):
            recurrence.error = (
                "the recursion follows graph edges but no visited/marked check "
                "was found, so a vertex may be entered many times (or forever "
                "on a cycle); add a visited test to bound it"
            )
            return recurrence

        program = self.program
        node_var = getattr(program, "node_var", "n")
        edge_var = getattr(program, "edge_var", "m")
        analyzer = ComplexityAnalyzer(
            program=program, assigned=assigned_variables(body),
            default=Complexity.var(node_var), self_name=node["name"],
        )
        work = analyzer.analyze(body)
        total = sum_over_vertices(work, node_var, edge_var)

        what = "vertex" if graph else "tree node"
        plural = "vertices" if graph else "tree nodes"
        recurrence.work = work
        recurrence.measure = ("structural",)
        recurrence.direct_result = total
        recurrence.shared = graph
        recurrence.warnings.extend(analyzer.warnings)
        recurrence.description_lines = [
            f"Traversal recursion: each {what} is entered at most once"
            + (" (guarded by a visited check)" if graph else ""),
            f"Work of one call: {work}   ->   summed over all {plural}: {total}",
        ]
        if work.variables() & {"deg", "cdeg"}:
            recurrence.notes.append(
                "The neighbour loops of all calls add up to "
                + (edge_var if graph else node_var + " - 1")
                + " iterations in total (each edge is looked at once), not "
                + node_var + " x degree."
            )
        if all(len(c) <= 1 for c, _ in paths) and not any(
                call.loops for call in calls):
            recurrence.notes.append(
                "Only one recursive call runs per invocation, so the real "
                "cost is O(h) for a tree of height h; O(n) is the worst case "
                "(a degenerate, list-shaped tree)."
            )
        return recurrence

    # ---- work and multiplicities --------------------------------------
    def _work_analyzer(self, node, measure, params):
        env = {}
        if measure[0] == "single":
            env[measure[1]] = Complexity.var(SIZE_VAR)
        else:
            env[measure[1]] = Complexity.const()
            env[measure[2]] = Complexity.var(SIZE_VAR)
        return ComplexityAnalyzer(
            program=self.program, env=env,
            assigned=assigned_variables(node.get("body", [])),
            default=Complexity.var(SIZE_VAR), self_name=node["name"],
        )

    @staticmethod
    def _numeric_iterations(loop):
        if loop.get("type") != "FOR" or loop.get("collection") is not None:
            return None
        try:
            start = numeric_value(parse_expr(loop.get("start", "")))
            end = numeric_value(parse_expr(loop.get("end", "")))
            step = loop.get("step")
            step = numeric_value(parse_expr(step)) if step else Fraction(1)
        except ExprError:
            return None
        if start is None or end is None or not step:
            return None
        return max(0, int((abs(end - start) / abs(step)))) + 1

    def _resolve_mult(self, call, analyzer):
        count, symbolic = call.factor, None
        for loop in call.loops:
            fixed = self._numeric_iterations(loop)
            if fixed is not None:
                count *= fixed
                continue
            estimate = analyzer.loop_iteration_estimate(loop)
            if estimate.is_const:
                analyzer.warn(
                    "A recursive call inside a loop with an unknown constant "
                    "iteration count was counted once."
                )
                continue
            symbolic = estimate if symbolic is None else symbolic.mul(estimate)
        return symbolic if symbolic is not None else count
