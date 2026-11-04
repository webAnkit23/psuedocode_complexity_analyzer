"""
complexity.py
-------------
1. A small symbolic algebra for asymptotic costs:
       n^a * (log n)^b * c^n * n!      (possibly in several variables)
   `Complexity` keeps a sum of such terms and drops every term that is
   dominated by another one, so  n^2 + n  becomes  n^2  but  n + m  stays.

2. `ComplexityAnalyzer`, which walks the AST produced by Parser.py and
   estimates the WORST-CASE running time of loops, branches and calls.

This is a heuristic tool for pseudocode. Where it cannot prove a bound it
falls back to O(n) and records a warning instead of failing silently.
"""

import math
import re
from fractions import Fraction

from expressions import (
    CONST, ExprError, assigned_variables, classify_collection, classify_tree,
    extract_calls_full, has_guard_text, linear_form, negate_condition,
    new_value_tree, numeric_value, parse_assignment, parse_condition,
    parse_expr, variables_of, walk, worklist_condition, node_texts,
)


class Unsupported(Exception):
    """A construct the analyzer cannot express or solve."""


EPS = 1e-9
SIZE_VAR = "n"


# ======================================================================
# Algebra
# ======================================================================

def _fmt_q(q):
    q = Fraction(q)
    if q.denominator == 1:
        return str(q.numerator)
    return f"{float(q):.3f}".rstrip("0").rstrip(".")


def _fmt_pow(q):
    text = _fmt_q(q)
    if Fraction(q).denominator in (2, 3, 4):
        return f"({Fraction(q).numerator}/{Fraction(q).denominator})"
    return text


def _fmt_base(base):
    if abs(base - round(base)) < 1e-9:
        return str(int(round(base)))
    return f"{base:.3f}".rstrip("0").rstrip(".")


_NEUTRAL = (Fraction(0), 1.0, Fraction(0), Fraction(0), Fraction(0))
_VAR_ORDER = {"V": 0, "n": 1, "N": 1, "E": 2, "m": 3, "M": 3, "deg": 8, "cdeg": 8}


def var_order(name):
    return (_VAR_ORDER.get(name, 5), name)


class Term:
    """One product  prod_v  v!^f * e^v * v^p * (log v)^l * (log log v)^ll ."""

    __slots__ = ("parts",)

    def __init__(self, parts=()):
        self.parts = tuple(parts)

    @staticmethod
    def make(items):
        parts = []
        for var in sorted(items):
            entry = items[var]
            if len(entry) == 4:
                fact, exp, power, log = entry
                loglog = Fraction(0)
            else:
                fact, exp, power, log, loglog = entry
            exp = round(float(exp), 9)
            fact, power, log, loglog = (
                Fraction(fact), Fraction(power), Fraction(log), Fraction(loglog)
            )
            if fact or exp != 1.0 or power or log or loglog:
                parts.append((var, fact, exp, power, log, loglog))
        return Term(tuple(parts))

    def as_dict(self):
        return {v: (f, e, p, l, ll) for v, f, e, p, l, ll in self.parts}

    def key(self, var):
        return self.as_dict().get(var, _NEUTRAL)

    def variables(self):
        return [part[0] for part in self.parts]

    def is_constant(self):
        return not self.parts

    def mul(self, other):
        a, b = self.as_dict(), other.as_dict()
        out = {}
        for var in set(a) | set(b):
            f1, e1, p1, l1, ll1 = a.get(var, _NEUTRAL)
            f2, e2, p2, l2, ll2 = b.get(var, _NEUTRAL)
            out[var] = (f1 + f2, e1 * e2, p1 + p2, l1 + l2, ll1 + ll2)
        return Term.make(out)

    def pow(self, q):
        q = Fraction(q)
        return Term.make({
            v: (f * q, e ** float(q), p * q, l * q, ll * q)
            for v, (f, e, p, l, ll) in self.as_dict().items()
        })

    def dominates(self, other):
        a, b = self.as_dict(), other.as_dict()
        for degree in ("deg", "cdeg"):
            if (degree in a) != (degree in b):
                return False
        for var in set(a) | set(b):
            if a.get(var, _NEUTRAL) < b.get(var, _NEUTRAL):
                return False
        return True

    def split(self, var):
        """Return (key of `var`, remaining Term without `var`)."""
        d = self.as_dict()
        key = d.pop(var, _NEUTRAL)
        return key, Term.make(d)

    def rank(self):
        facts = sum(float(f) for _, f, _, _, _, _ in self.parts)
        exps = sum(math.log(e) for _, _, e, _, _, _ in self.parts)
        pows = sum(float(p) for _, _, _, p, _, _ in self.parts)
        logs = sum(float(l) for _, _, _, _, l, _ in self.parts)
        loglogs = sum(float(ll) for _, _, _, _, _, ll in self.parts)
        return (facts, exps, pows, logs, loglogs)

    def __eq__(self, other):
        return isinstance(other, Term) and self.parts == other.parts

    def __hash__(self):
        return hash(self.parts)

    def __str__(self):
        if not self.parts:
            return "1"
        special, poly, logs = [], [], []
        for var, fact, exp, power, log, loglog in sorted(
                self.parts, key=lambda part: var_order(part[0])):
            if fact:
                special.append(f"{var}!" if fact == 1 else f"({var}!)^{_fmt_q(fact)}")
            if exp != 1.0:
                special.append(f"{_fmt_base(exp)}^{var}")
            if power:
                poly.append(var if power == 1 else f"{var}^{_fmt_pow(power)}")
            if log:
                logs.append(f"log {var}" if log == 1 else f"log^{_fmt_q(log)} {var}")
            if loglog:
                logs.append(f"log(log {var})" if loglog == 1 else f"log^{_fmt_q(loglog)}(log {var})")
        text = " * ".join(special + [" * ".join(poly)] if poly else special)
        if logs:
            text = (text + " " if text else "") + " ".join(logs)
        return text


def _reduce(terms):
    unique = []
    for term in terms:
        if term not in unique:
            unique.append(term)
    kept = [
        t for t in unique
        if not any(o is not t and o.dominates(t) for o in unique)
    ]
    kept.sort(key=lambda t: (tuple(-x for x in t.rank()),
                             tuple(var_order(v) for v in t.variables()), str(t)))
    return tuple(kept)


class Complexity:
    """A sum of Terms with dominated terms removed."""

    def __init__(self, terms=None):
        self.terms = _reduce(terms or [Term()])

    # ---- constructors ----
    @staticmethod
    def const():
        return Complexity([Term()])

    @staticmethod
    def var(name, power=1):
        return Complexity([Term.make({name: (0, 1.0, power, 0)})])

    @staticmethod
    def log(name):
        return Complexity([Term.make({name: (0, 1.0, 0, 1, 0)})])

    @staticmethod
    def loglog(name):
        return Complexity([Term.make({name: (0, 1.0, 0, 0, 1)})])

    @staticmethod
    def exp(base, name):
        return Complexity([Term.make({name: (0, base, 0, 0, 0)})])

    @staticmethod
    def fact(name):
        return Complexity([Term.make({name: (1, 1.0, 0, 0, 0)})])

    # ---- queries ----
    @property
    def is_const(self):
        return all(t.is_constant() for t in self.terms)

    def rank(self):
        return max(t.rank() for t in self.terms)

    def variables(self):
        names = set()
        for term in self.terms:
            names.update(term.variables())
        return names

    # ---- arithmetic ----
    def add(self, other):
        return Complexity(list(self.terms) + list(other.terms))

    def mul(self, other):
        return Complexity([a.mul(b) for a in self.terms for b in other.terms])

    def pow(self, q):
        q = Fraction(q)
        if q == 0:
            return Complexity.const()
        return Complexity([t.pow(q) for t in self.terms])

    def log_of(self):
        """Asymptotic order of log(self)."""
        result = Complexity.const()
        for term in self.terms:
            for var, fact, exp, power, log, loglog in term.parts:
                if fact:
                    part = Complexity([Term.make({var: (0, 1.0, 1, 1, 0)})])
                elif exp != 1.0:
                    part = Complexity.var(var)
                elif power:
                    part = Complexity.log(var)
                elif log:
                    part = Complexity.loglog(var)
                else:
                    continue
                result = result.add(part)
        return result

    def substitute(self, mapping):
        """Replace variables by Complexities (used when calling functions)."""
        total = None
        for term in self.terms:
            product = Complexity.const()
            for var, fact, exp, power, log, loglog in term.parts:
                rep = mapping.get(var, Complexity.var(var))
                if power:
                    product = product.mul(rep.pow(power))
                if log:
                    product = product.mul(rep.log_of().pow(log))
                if loglog:
                    product = product.mul(rep.log_of().log_of().pow(loglog))
                if exp != 1.0 or fact:
                    if rep.is_const:
                        continue
                    if len(rep.terms) == 1 and _is_plain_variable(rep.terms[0]):
                        name = rep.terms[0].variables()[0]
                        if exp != 1.0:
                            product = product.mul(Complexity.exp(exp, name))
                        if fact:
                            product = product.mul(Complexity.fact(name))
                    else:
                        raise Unsupported(
                            "exponential cost with a non-linear argument"
                        )
            total = product if total is None else total.add(product)
        return total or Complexity.const()

    # ---- misc ----
    def __eq__(self, other):
        return isinstance(other, Complexity) and self.terms == other.terms

    def __hash__(self):
        return hash(self.terms)

    def body(self):
        return " + ".join(str(t) for t in self.terms)

    def __str__(self):
        return f"O({self.body()})"

    __repr__ = __str__


def _is_plain_variable(term):
    if len(term.parts) != 1:
        return False
    _, fact, exp, power, log, loglog = term.parts[0]
    return not fact and exp == 1.0 and power == 1 and not log and not loglog


def sum_over_vertices(cost, node_var, edge_var):
    """
    Total cost of running `cost` once for every vertex, where `deg` is the
    degree of the current vertex (sum of degrees = E) and `cdeg` its number of
    children (sum = V - 1).   deg^k  ->  E * V^(k-1)     cdeg^k -> V^k
    """
    vertices, edges = Complexity.var(node_var), Complexity.var(edge_var)
    total = None
    for term in cost.terms:
        deg_key, rest = term.split("deg")
        child_key, rest = rest.split("cdeg")
        degree = deg_key[2] + child_key[2]
        logs = deg_key[3] + child_key[3]
        part = Complexity([rest])
        if logs:
            part = part.mul(Complexity.log(node_var).pow(logs))
        if degree == 0:
            part = part.mul(vertices)
        else:
            first = edges if deg_key[2] > 0 else vertices
            part = part.mul(first).mul(vertices.pow(degree - 1))
        total = part if total is None else total.add(part)
    # every vertex costs at least O(1), even when deg terms dominate the body
    return (total or Complexity.const()).add(vertices)


def uses_degree(cost):
    return bool(cost.variables() & {"deg", "cdeg"})


def polynomially_greater(a, b):
    """True if `a` has a higher polynomial degree than `b` in some variable."""
    def degrees(c):
        out = {}
        for term in c.terms:
            for var, _, _, power, _, _ in term.parts:
                out[var] = max(out.get(var, Fraction(0)), power)
        return out
    da, db = degrees(a), degrees(b)
    return any(da[v] > db.get(v, Fraction(0)) for v in da)


# ======================================================================
# Analyzer
# ======================================================================

class LoopInfo:
    def __init__(self, iterations, geometric=False, controlled=None, post=None,
                 guarded=False):
        self.guarded = guarded
        self.iterations = iterations
        self.geometric = geometric
        self.controlled = controlled or {}   # var -> max value inside the body
        self.post = post or {}               # var -> value after the loop


_SWAP = {"<": ">", "<=": ">=", ">": "<", ">=": "<=", "!=": "!=", "==": "=="}
_SIZE_FUNCS = {"len", "length", "size", "count", "card"}
_LOG_FUNCS = {"log", "lg", "ln", "log2", "log10"}
_PASS_FUNCS = {"floor", "ceil", "ceiling", "round", "abs", "int", "trunc"}


_LOG_OPS = {
    "extract_min", "extract_max", "decrease_key", "increase_key", "heappush",
    "heappop", "heap_push", "heap_pop", "heap_insert", "heap_extract_min",
    "heap_extract_max", "pq_insert", "pq_push", "pq_pop", "insert_heap",
    "delete_min", "delete_max", "bubble_up", "bubble_down", "sift_up",
    "sift_down", "siftup", "siftdown", "min_heapify", "max_heapify",
    "heapify_up", "heapify_down", "pop_min", "pop_max", "remove_min",
}
_QUEUE_OPS = {"enqueue", "dequeue", "push", "pop", "insert", "add", "put",
              "offer", "poll", "delete", "update"}
_PQ_NAME = re.compile(r"pq|heap|priority|prio", re.IGNORECASE)
_DEGREE_FUNCS = {"deg", "degree", "outdegree", "indegree", "out_degree",
                 "in_degree", "numneighbors", "num_neighbors"}


class ComplexityAnalyzer:
    """
    Estimates worst-case time of statements.

    program  : optional ProgramAnalyzer, needed to cost calls to other
               user-defined functions
    env      : variable -> Complexity (the largest value the variable takes)
    default  : Complexity used for len(...), unknown locals, fallbacks (n)
    self_name: function whose own recursive calls are costed as O(1)
               (recursion is handled by the recurrence solver)
    """

    def __init__(self, program=None, env=None, assigned=None, default=None,
                 self_name=None, inline_stack=(), warnings=None, notes=None):
        self.program = program
        self.node_var = getattr(program, "node_var", "n")
        self.edge_var = getattr(program, "edge_var", "m")
        self.env = dict(env or {})
        self.assigned = set(assigned or ())
        self.default = default or Complexity.var(self.node_var)
        self.shared = Complexity.const()      # one-time (shared) traversal cost
        self.guarded_worklist = False
        self.top_vertex_loop = False
        self._depth = 0
        self._enclosing = []
        self.self_name = self_name
        self.inline_stack = tuple(inline_stack)
        self.warnings = warnings if warnings is not None else []
        self.notes = notes if notes is not None else []

    # ------------------------------------------------------------------
    def warn(self, message):
        if message not in self.warnings:
            self.warnings.append(message)

    def note(self, message):
        if message not in self.notes:
            self.notes.append(message)

    @property
    def node_complexity(self):
        return Complexity.var(self.node_var)

    def analyze(self, nodes):
        """Estimate the cost of a list of statements."""
        cost, shared = self.analyze_split(nodes)
        return cost.add(shared)

    def analyze_split(self, nodes):
        """-> (cost, shared traversal cost that loops must not multiply)"""
        self.assigned |= assigned_variables(nodes)
        return self._block(nodes), self.shared

    # ------------------------------------------------------------------
    # Expression evaluation (value of an expression, as a Complexity)
    # ------------------------------------------------------------------
    def lookup(self, name):
        if name in self.env:
            return self.env[name]
        if name.upper() in {"TRUE", "FALSE", "NULL", "NIL", "NONE", "INF", "INFINITY"}:
            return Complexity.const()
        if name in self.assigned:
            return self.default
        if name.lower() in ("vertices", "nodes", "verts", "numvertices",
                            "num_vertices", "numnodes", "num_nodes"):
            return self.node_complexity
        if name.lower() in ("edges", "numedges", "num_edges"):
            return Complexity.var(self.edge_var)
        return Complexity.var(name)

    def eval(self, tree):
        kind = tree[0]
        if kind == "num":
            return Complexity.const()
        if kind == "var":
            return self.lookup(tree[1])
        if kind in ("unk", "index"):
            return self.default
        if kind == "neg":
            return self.eval(tree[1])
        if kind == "fact":
            value = self.eval(tree[1])
            if value.is_const:
                return value
            if len(value.terms) == 1 and _is_plain_variable(value.terms[0]):
                return Complexity.fact(value.terms[0].variables()[0])
            raise Unsupported("factorial of a non-linear expression")
        if kind == "pow":
            return self._eval_pow(tree[1], tree[2])
        if kind == "bin":
            op = tree[1]
            left, right = self.eval(tree[2]), self.eval(tree[3])
            if op in "+-":
                return left.add(right)
            if op == "*":
                return left.mul(right)
            if op == "/":
                # n / log(n)  ->  n^1 * log^(-1) n  (important for Akra-Bazzi Case 2b)
                if not right.is_const:
                    right_log = right.log_of()   # order of log(right)
                    if not right_log.is_const:
                        return left.mul(right.pow(Fraction(-1)))
                return left
            if op == "%":
                return right
        if kind == "call":
            return self._eval_call(tree[1], tree[2])
        raise Unsupported(f"cannot evaluate {tree[0]}")

    def _eval_call(self, name, args):
        low = name.lower()
        if low in _SIZE_FUNCS:
            kind = classify_tree(args[0]) if args else None
            if kind == "adj" and args[0][0] == "var":
                kind = "vertices"            # len(adj) = number of vertices
            return self._collection_value(kind)
        if low in _DEGREE_FUNCS:
            return Complexity.var("deg")
        if low in _LOG_FUNCS and args:
            return self.eval(args[0]).log_of()
        if low in ("sqrt",) and args:
            return self.eval(args[0]).pow(Fraction(1, 2))
        if low == "cbrt" and args:
            return self.eval(args[0]).pow(Fraction(1, 3))
        if low in _PASS_FUNCS and args:
            return self.eval(args[0])
        if low == "min" and args:
            values = [self.eval(a) for a in args]
            return min(values, key=lambda v: v.rank())
        if low == "max" and args:
            result = self.eval(args[0])
            for a in args[1:]:
                result = result.add(self.eval(a))
            return result
        if low == "pow" and len(args) == 2:
            return self._eval_pow(args[0], args[1])
        if low in ("factorial", "fact") and args:
            return self.eval(("fact", args[0]))
        return self.default

    def _collection_value(self, kind):
        if kind == "adj":
            return Complexity.var("deg")
        if kind == "children":
            return Complexity.var("cdeg")
        if kind == "vertices":
            return self.node_complexity
        if kind == "edges":
            return Complexity.var(self.edge_var)
        return self.default

    def _eval_pow(self, base_tree, exp_tree):
        exponent = numeric_value(exp_tree)
        base = self.eval(base_tree)
        if exponent is not None:
            return base.pow(exponent) if exponent > 0 else Complexity.const()
        form = linear_form(exp_tree)
        if form is None:
            raise Unsupported("non-linear exponent")
        names = variables_of(form)
        if not names:
            return base
        base_value = numeric_value(base_tree)
        if base_value is None or len(names) != 1:
            raise Unsupported("variable raised to a variable power")
        if base_value <= 1:
            return Complexity.const()
        (name, coeff), = names.items()
        rep = self.lookup(name)
        if rep.is_const:
            return Complexity.const()
        if len(rep.terms) == 1 and _is_plain_variable(rep.terms[0]):
            return Complexity.exp(float(base_value) ** float(coeff),
                                  rep.terms[0].variables()[0])
        raise Unsupported("exponential of a non-linear expression")

    def _safe_eval(self, text, what):
        try:
            return self.eval(parse_expr(text))
        except (ExprError, Unsupported) as error:
            self.warn(f"Could not read {what} '{text}' ({error}); assumed O(n).")
            return self.default

    # ------------------------------------------------------------------
    # Statements
    # ------------------------------------------------------------------
    def _block(self, nodes):
        total = Complexity.const()
        for node in nodes:
            total = total.add(self._node(node))
        return total

    def _node(self, node):
        kind = node.get("type")
        if kind == "FUNCTION":
            return Complexity.const()
        if kind == "OPERATION":
            cost = self._calls_cost(node.get("code", ""))
            self._apply_assignment(node.get("code", ""))
            return cost
        if kind == "FUNCTION_CALL":
            args = ", ".join(node.get("arguments", []))
            return self._calls_cost(f"{node['name']}({args})")
        if kind == "RETURN":
            return self._calls_cost(node.get("value") or "")
        if kind in ("BREAK", "CONTINUE"):
            return Complexity.const()
        if kind in ("GOTO", "LABEL"):
            self.warn("GOTO/LABEL jumps are not analysed; the estimate ignores them.")
            return Complexity.const()
        if kind == "IF":
            return self._if(node)
        if kind == "FOR":
            return self._for(node)
        if kind in ("WHILE", "REPEAT_UNTIL", "DO_WHILE"):
            return self._conditional_loop(node)
        return Complexity.const()

    def _apply_assignment(self, code):
        assignment = parse_assignment(code)
        if not assignment:
            return
        if len(assignment.targets) != 1:
            for target in assignment.targets:
                self.env.pop(target, None)
            return
        target = assignment.targets[0]
        tree = new_value_tree(assignment)
        try:
            if tree is None:
                raise Unsupported("unreadable")
            self.env[target] = self.eval(tree)
        except (ExprError, Unsupported):
            self.env.pop(target, None)

    def _if(self, node):
        cond_cost = self._calls_cost(node.get("condition", ""))
        base = dict(self.env)
        self.env = dict(base)
        true_cost = self._block(node.get("true_body", []))
        env_true = self.env
        self.env = dict(base)
        false_cost = self._block(node.get("false_body", []))
        env_false = self.env
        self.env = {
            v: env_true[v].add(env_false[v])
            for v in set(env_true) & set(env_false)
        }
        return cond_cost.add(true_cost).add(false_cost)

    # ------------------------------------------------------------------
    # Calls
    # ------------------------------------------------------------------
    def _calls_cost(self, text):
        total = Complexity.const()
        for name, args, receiver in extract_calls_full(text):
            total = total.add(self._call_cost(name, args, receiver))
        return total

    def _size_of(self, text):
        kind = classify_collection(text)
        return self._collection_value(kind)

    def _call_cost(self, name, args, receiver=None):
        low = name.lower()
        if name == self.self_name:
            return Complexity.const()          # handled by the recurrence
        if self.program is not None and name in self.program.functions:
            return self._user_call_cost(name, args)
        if name == "WORK":
            if not args:
                return Complexity.const()
            return self._safe_eval(args[0], "WORK(...) argument")
        if low in ("sort", "sorted", "heapsort", "heap_sort", "mergesort",
                   "merge_sort", "sorted_edges", "sort_edges"):
            size = self._size_of(args[0]) if args else self.default
            return size.mul(size.log_of())
        if low in ("build_heap", "build_max_heap", "build_min_heap", "heapify", "make_heap"):
            return self._size_of(args[0]) if args else self.default
        if low in ("relax",):
            if self._pq_in_scope():
                return self.node_complexity.log_of()
            return Complexity.const()
        if low in ("initialize_single_source", "init_single_source", "initialize"):
            return self.node_complexity
        if low in ("make_set", "find_set", "union", "find", "link"):
            return Complexity.const()
        if low in ("connected", "same_component", "in_same_set"):
            return Complexity.const()
        if low in ("transpose", "reverse_graph"):
            return Complexity.var(self.edge_var)
        if low in _LOG_OPS:
            return self.node_complexity.log_of()
        if low in _QUEUE_OPS:
            owners = [receiver] + args[:1]
            if any(o and _PQ_NAME.search(o) for o in owners):
                return self.node_complexity.log_of()
        return Complexity.const()

    def _pq_in_scope(self):
        for env_var in self.env:
            if _PQ_NAME.search(env_var):
                return True
        if self._enclosing:
            for block in self._enclosing:
                for node in walk(block):
                    for text in node_texts(node):
                        if _PQ_NAME.search(text) or any(
                            op in text.lower() for op in ("extract_min", "extract_max", "decrease_key", "heappush", "heappop")
                        ):
                            return True
        return False

    def _value_of_arg(self, text):
        try:
            return self.eval(parse_expr(text))
        except (ExprError, Unsupported):
            return self.default

    def _user_call_cost(self, name, args):
        program = self.program
        if program.is_recursive(name):
            summary = program.recursive_summary(name)
            if summary is None:
                self.warn(
                    f"Cost of recursive function {name}() could not be "
                    "determined; its calls were counted as O(1)."
                )
                return Complexity.const()
            if summary.measure[0] == "structural":
                if summary.shared:
                    self.shared = self.shared.add(summary.complexity)
                    return Complexity.const()
                return summary.complexity
            size = summary.measure_value(args, self._value_of_arg, self.default)
            try:
                return summary.complexity.substitute({SIZE_VAR: size})
            except Unsupported as error:
                self.warn(f"Call to {name}(): {error}.")
                return Complexity.const()

        node = program.functions[name]
        if name in self.inline_stack or len(self.inline_stack) >= 12:
            self.warn(f"Call to {name}() is part of a call cycle; counted as O(1).")
            return Complexity.const()
        params = node.get("parameters", [])
        values = []
        for index, param in enumerate(params):
            if index < len(args):
                values.append(self._value_of_arg(args[index]))
            else:
                values.append(Complexity.var(param))
        key = (name, tuple(str(v) for v in values), str(self.default))
        if key not in program.inline_cache:
            sub = ComplexityAnalyzer(
                program=program,
                env=dict(zip(params, values)),
                assigned=assigned_variables(node.get("body", [])),
                default=self.default,
                inline_stack=self.inline_stack + (name,),
            )
            cost, shared = sub.analyze_split(node.get("body", []))
            traversal = sub.guarded_worklist and not sub.top_vertex_loop
            program.inline_cache[key] = (cost, shared, traversal,
                                         list(sub.warnings))
        cost, shared, traversal, warnings = program.inline_cache[key]
        for message in warnings:
            self.warn(message)
        self.shared = self.shared.add(shared)
        if traversal:
            # A visited-guarded traversal started from several places still
            # touches every vertex/edge only once overall.
            self.shared = self.shared.add(cost)
            return Complexity.const()
        return cost

    # ------------------------------------------------------------------
    # FOR loops
    # ------------------------------------------------------------------
    def _step_is_geometric(self, step, variable):
        text = re.sub(r"\s+", "", step)
        v = re.escape(variable)
        patterns = (
            r"\*\d+(?:\.\d+)?", r"/\d+(?:\.\d+)?",
            rf"{v}\*\d+(?:\.\d+)?", rf"\d+(?:\.\d+)?\*{v}",
            rf"{v}/\d+(?:\.\d+)?", rf"{v}\+{v}",
        )
        return any(re.fullmatch(p, text) for p in patterns)

    def _for_info(self, node):
        """-> (iterations, is_geometric, largest value of the loop variable)"""
        if node.get("collection") is not None:
            value = self._size_of(node["collection"])
            return value, False, value
        start = self._safe_eval(node.get("start", "1"), "loop start")
        end = self._safe_eval(node.get("end", "n"), "loop bound")
        bound = start.add(end)
        geometric = bool(node.get("step")) and self._step_is_geometric(
            node["step"], node.get("variable", "")
        )
        iterations = bound.log_of() if geometric else bound
        if not geometric and not iterations.is_const \
                and self._exits_after_constant(node):
            iterations = Complexity.const()
        return iterations, geometric, bound

    def _exits_after_constant(self, node):
        """FOR i ... : IF i > 5 BREAK  ->  at most 5 iterations."""
        variable, down = node.get("variable"), node.get("direction") == "DOWN"
        wanted = ("<", "<=", "==") if down else (">", ">=", "==")
        for child in node.get("body", []):
            if child.get("type") != "IF" or child.get("false_body"):
                continue
            body = child.get("true_body", [])
            if len(body) != 1 or body[0].get("type") not in ("BREAK", "RETURN"):
                continue
            tree = parse_condition(child.get("condition", ""))
            if tree[0] != "cmp":
                continue
            _, op, left, right = tree
            if left == ("var", variable) and numeric_value(right) is not None:
                relation = op
            elif right == ("var", variable) and numeric_value(left) is not None:
                relation = _SWAP.get(op, op)
            else:
                continue
            if relation in wanted:
                return True
        return False

    def _for(self, node):
        iterations, geometric, bound = self._for_info(node)
        variable = node.get("variable")
        names = node.get("variables") or ([variable] if variable else [])
        controlled = {name: bound for name in names}
        bounds_cost = self._calls_cost(
            " ".join(str(node.get(k) or "") for k in ("start", "end", "step"))
        )
        cost = self._loop_cost(iterations, node.get("body", []), geometric,
                               controlled, bounds_cost, outer_var=variable)
        self._after_loop(node.get("body", []), controlled)
        return cost

    # ------------------------------------------------------------------
    # WHILE / REPEAT-UNTIL / DO-WHILE
    # ------------------------------------------------------------------
    def _loop_info(self, node):
        text = node.get("condition", "")
        tree = parse_condition(text)
        if node.get("type") == "REPEAT_UNTIL":
            tree = negate_condition(tree)     # repeats while NOT condition
        return self._cond_info(tree, node.get("body", []))

    def _worklist_info(self, node):
        found = worklist_condition(node.get("condition", ""))
        if not found:
            return None
        name, nonempty = found
        repeats = nonempty if node.get("type") in ("WHILE", "DO_WHILE") \
            else not nonempty
        if not repeats:
            return None
        body = node.get("body", [])
        guarded = has_guard_text(node.get("condition", "")) or any(
            has_guard_text(n.get("condition", ""))
            for n in walk(body) if n.get("type") == "IF"
        )
        tree_like = any(
            re.search(r"\.\s*(?:left|right|child\w*|kids)\b|children", text, re.I)
            for n in walk(body) for text in node_texts(n)
        )
        if guarded:
            self.guarded_worklist = True
        elif tree_like:
            pass            # a tree has no cycles: nothing is queued twice
        else:
            self.warn(
                f"The loop over '{name}' has no visited/marked check; assumed "
                "that every item is queued at most once (O(n) iterations)."
            )
        return LoopInfo(self.node_complexity, guarded=guarded)

    def _has_init_loop(self, body):
        """Does this loop body contain a loop over all vertices/edges?"""
        for inner in walk(body):
            if inner.get("type") != "FOR":
                continue
            if inner.get("collection") is not None:
                if classify_collection(inner["collection"]) in ("vertices", "edges"):
                    return True
            elif re.search(rf"(?:\b{self.node_var}\b|\|\s*V\s*\|)",
                           str(inner.get("end", ""))):
                return True
        return False

    def _pointer_chase(self, node):
        """WHILE x != NULL ... x = x.next / x = parent[x] -> O(n) steps."""
        text = node.get("condition", "")
        for child in walk(node.get("body", [])):
            if child.get("type") != "OPERATION":
                continue
            assignment = parse_assignment(child.get("code", ""))
            if not assignment or len(assignment.targets) != 1:
                continue
            x = re.escape(assignment.targets[0])
            if not re.search(rf"\b{x}\b", text):
                continue
            rhs = assignment.rhs.strip()
            if assignment.op == "=" and re.fullmatch(
                rf"{x}\s*\.\s*\w+|\w+\s*\[\s*{x}\s*\]|\w+\s*\(\s*{x}\s*\)",
                rhs,
            ):
                if re.search(r"\.\s*(?:left|right|lchild|rchild|next)\b", rhs, re.I):
                    self.note(
                        f"Pointer-chase on tree/list node '{assignment.targets[0]}': runs in O(h) "
                        "where h is height (worst-case O(n) for a degenerate tree/list, O(log n) if balanced)."
                    )
                return True
        return False

    def _conditional_loop(self, node):
        if node.get("_amortized"):
            info = LoopInfo(Complexity.const())
            worklist = None
            q = node.get("_amortized_q", "stack/queue")
            if node.get("_two_pointer"):
                self.note(
                    f"Two-pointer amortized analysis on '{q}': pointer only advances forward "
                    "and is bounded by the outer loop, executing at most O(n) times in total "
                    "(O(1) amortized per iteration)."
                )
            else:
                self.note(
                    f"Amortized stack/queue analysis on '{q}': each item is pushed at most "
                    f"once and popped at most once across the outer loop, giving O(1) "
                    f"amortized time per iteration (O(n) in total)."
                )
        else:
            worklist = self._worklist_info(node)
            info = worklist or self._loop_info(node)
            text = node.get("condition", "")
            if info is None and self._pointer_chase(node):
                info = LoopInfo(self.default)
            if info is None:
                self.warn(
                    f"Could not determine how many times the loop with condition "
                    f"'{text}' runs; assumed O(n)."
                )
                info = LoopInfo(self.default)
        cond_cost = self._calls_cost(node.get("condition", ""))
        cost = self._loop_cost(info.iterations, node.get("body", []),
                               info.geometric, info.controlled, cond_cost,
                               worklist=worklist is not None)
        self._after_loop(node.get("body", []), info.post)
        if (worklist is not None and worklist.guarded and self._enclosing
                and not self._has_init_loop(self._enclosing[-1])):
            self.shared = self.shared.add(cost)
            return Complexity.const()
        return cost

    def _detect_amortized_loops(self, body, outer_var=None):
        push_ops = {"push", "enqueue", "add", "put", "append", "push_back", "push_front"}
        pop_ops = {"pop", "dequeue", "poll", "remove", "pop_back", "pop_front"}

        pushes_per_queue = {}
        for node in body:
            if node.get("type") in ("WHILE", "REPEAT_UNTIL", "DO_WHILE", "FOR"):
                continue
            for name, args, recv in extract_calls_full(" ".join(node_texts(node))):
                low = name.lower()
                if low in push_ops:
                    q = recv or (args[0] if args else None)
                    if q:
                        pushes_per_queue[q] = pushes_per_queue.get(q, 0) + 1

        for node in body:
            if node.get("type") not in ("WHILE", "REPEAT_UNTIL", "DO_WHILE"):
                continue
            found = worklist_condition(node.get("condition", ""))
            if found:
                q_name, nonempty = found
                if nonempty and q_name in pushes_per_queue:
                    inner_body = node.get("body", [])
                    has_pop = False
                    has_push = False
                    for inner in walk(inner_body):
                        for name, args, recv in extract_calls_full(" ".join(node_texts(inner))):
                            low = name.lower()
                            target_q = recv or (args[0] if args else None)
                            if target_q == q_name:
                                if low in pop_ops:
                                    has_pop = True
                                elif low in push_ops:
                                    has_push = True

                    if has_pop and not has_push:
                        node["_amortized"] = True
                        node["_amortized_q"] = q_name
                        continue

            # Two-pointer sliding window amortized pattern
            cond_text = node.get("condition", "")
            inner_body = node.get("body", [])
            inc_vars = set()
            for inner in walk(inner_body):
                if inner.get("type") == "OPERATION":
                    asn = parse_assignment(inner.get("code", ""))
                    if asn and len(asn.targets) == 1:
                        target = asn.targets[0]
                        code_clean = re.sub(r"\s+", "", inner.get("code", ""))
                        if code_clean in (f"{target}={target}+1", f"{target}+=1", f"{target}++", f"++{target}", f"{target}<-{target}+1"):
                            inc_vars.add(target)

            for ptr in inc_vars:
                if outer_var and re.search(rf"\b{ptr}\b\s*(?:<|<=)\s*\b{re.escape(outer_var)}\b", cond_text):
                    assigned_outside = False
                    for other in body:
                        if other is node:
                            continue
                        for inner in walk([other]):
                            if inner.get("type") == "OPERATION":
                                asn = parse_assignment(inner.get("code", ""))
                                if asn and ptr in asn.targets:
                                    assigned_outside = True
                    if not assigned_outside:
                        node["_amortized"] = True
                        node["_amortized_q"] = ptr
                        node["_two_pointer"] = True
                        break

    def loop_iteration_estimate(self, node):
        """Number of iterations of any loop node, as a Complexity."""
        if node.get("type") == "FOR":
            return self._for_info(node)[0]
        info = self._loop_info(node)
        return info.iterations if info else self.default

    def _loop_cost(self, iterations, body, geometric, controlled, extra,
                   worklist=False, outer_var=None):
        self._detect_amortized_loops(body, outer_var=outer_var)
        before = dict(self.env)
        self.env.update(controlled)
        if (self._depth == 0 and not worklist
                and iterations == self.node_complexity):
            self.top_vertex_loop = True
        self._depth += 1
        self._enclosing.append(body)
        try:
            high = self._block(body).add(extra)
        finally:
            self._depth -= 1
            self._enclosing.pop()
        if iterations == self.node_complexity and uses_degree(high):
            return sum_over_vertices(high, self.node_var, self.edge_var)
        if geometric and not iterations.is_const and controlled:
            env_after, warn_count = dict(self.env), len(self.warnings)
            self.env = dict(before)
            for variable in controlled:
                self.env[variable] = Complexity.const()
            self._depth += 1
            try:
                low = self._block(body).add(extra)
            finally:
                self._depth -= 1
            del self.warnings[warn_count:]
            self.env = env_after
            if polynomially_greater(high, low):
                # Geometric series: the last iteration dominates.
                return high
        return iterations.mul(high)

    def _after_loop(self, body, post):
        for name in assigned_variables(body):
            self.env.pop(name, None)
        self.env.update(post)

    # ------------------------------------------------------------------
    # Loop condition analysis
    # ------------------------------------------------------------------
    def _cond_info(self, tree, body):
        kind = tree[0]
        if kind == "and":
            infos = [i for i in (self._cond_info(t, body) for t in tree[1]) if i]
            if not infos:
                return None
            return min(infos, key=lambda i: i.iterations.rank())
        if kind == "or":
            infos = [self._cond_info(t, body) for t in tree[1]]
            if any(i is None for i in infos):
                return None
            return max(infos, key=lambda i: i.iterations.rank())
        if kind == "not":
            return self._cond_info(negate_condition(tree[1]), body)
        if kind == "cmp":
            try:
                return self._cmp_info(tree, body)
            except (ExprError, Unsupported):
                return None
        return None

    @staticmethod
    def _square_of(tree):
        if tree[0] == "bin" and tree[1] == "*" and tree[2] == tree[3] \
                and tree[2][0] == "var":
            return tree[2][1]
        if tree[0] == "pow" and tree[1][0] == "var" and numeric_value(tree[2]) == 2:
            return tree[1][1]
        return None

    def _updated_in(self, body):
        return assigned_variables(body)

    def _cmp_info(self, tree, body):
        _, op, left, right = tree
        if op == "==":
            return None
        updated = self._updated_in(body)
        form = linear_form(("bin", "-", left, right))

        candidates = []          # (variable, sign)
        square = False
        if form is not None:
            for name, coeff in variables_of(form).items():
                if name in updated:
                    candidates.append((name, 1 if coeff > 0 else -1))
            others = lambda x: [v for v in variables_of(form) if v != x]
            inc_dist = lambda x: self._sum_values(others(x))
            names_in_cond = list(variables_of(form))
        else:
            name = self._square_of(left)
            bound_tree, relation = right, op
            if name is None:
                name = self._square_of(right)
                bound_tree, relation = left, _SWAP[op]
            if name is None or name not in updated:
                return None
            square = True
            op = relation
            candidates.append((name, 1))
            inc_dist = lambda x: self.eval(bound_tree)
            names_in_cond = [name]

        if not candidates:
            return None
        if len(candidates) >= 2 and self._binary_search(names_in_cond, body):
            size = self._sum_values(names_in_cond)
            return LoopInfo(size.log_of())

        infos = []
        for variable, sign in candidates:
            update = self._classify_update(variable, body)
            if update is None:
                return None
            needed = None
            if op in ("<", "<="):
                needed = sign
            elif op in (">", ">="):
                needed = -sign
            if update[0] in ("lin", "geom") and needed is not None \
                    and update[1] != needed:
                self.warn(
                    f"'{variable}' moves away from the loop bound; the loop "
                    "may never terminate."
                )
                return None
            current = self.lookup(variable)
            upper = inc_dist(variable)
            if needed == 1:
                distance = upper
            elif needed == -1:
                distance = current
            else:
                distance = current.add(upper)
            if update[0] == "lin":
                iterations = distance.pow(Fraction(1, 2)) \
                    if square and needed == 1 else distance
                geometric = False
            elif update[0] == "geom":
                iterations, geometric = distance.log_of(), True
            else:  # Euclid-style  x = a mod x
                distance = current.add(self.eval(update[1]))
                iterations, geometric = distance.log_of(), True
            infos.append(LoopInfo(
                iterations, geometric,
                controlled={variable: current.add(upper)},
                post={variable: upper if update[0] == "lin" or update[0] == "geom"
                      else Complexity.const()},
            ))

        best = min(infos, key=lambda i: i.iterations.rank())
        best.controlled = {k: v for i in infos for k, v in i.controlled.items()}
        best.post = {k: v for i in infos for k, v in i.post.items()}
        return best

    def _sum_values(self, names):
        total = Complexity.const()
        for name in names:
            total = total.add(self.lookup(name))
        return total

    def _classify_update(self, variable, body):
        """
        ('lin', +1/-1)  x changes by a constant each iteration
        ('geom', +1/-1) x is multiplied/divided by a constant
        ('mod', tree)   x = a mod x   (Euclid)
        or None when the update is not a single, unconditional statement.
        """
        direct, total = [], 0
        for node in walk(body):
            if node.get("type") == "OPERATION":
                assignment = parse_assignment(node.get("code", ""))
                if assignment and variable in assignment.targets:
                    total += 1
            elif node.get("type") == "FOR" and node.get("variable") == variable:
                total += 2
        for node in body:
            if node.get("type") == "OPERATION":
                assignment = parse_assignment(node.get("code", ""))
                if assignment and variable in assignment.targets:
                    direct.append(assignment)
        if len(direct) != 1 or total != 1:
            return None
        tree = new_value_tree(direct[0])
        if tree is None:
            return None
        form = linear_form(tree)
        if form is not None:
            coeff = form.get(variable, Fraction(0))
            if any(name != variable for name in variables_of(form)):
                return None
            const = form.get(CONST, Fraction(0))
            if coeff == 1:
                if const > 0:
                    return ("lin", 1)
                if const < 0:
                    return ("lin", -1)
                return None
            if coeff > 1 and const >= 0:
                return ("geom", 1)
            if 0 < coeff < 1 and const <= 0:
                return ("geom", -1)
            return None
        if tree[0] == "bin" and tree[1] == "%" and tree[3] == ("var", variable):
            return ("mod", tree[2])
        return None

    def _binary_search(self, names, body):
        """Recognise  mid = (lo+hi)/2 ; lo = mid+1 / hi = mid-1  loops."""
        definitions = {}
        for node in body:
            if node.get("type") == "OPERATION":
                assignment = parse_assignment(node.get("code", ""))
                if assignment and len(assignment.targets) == 1 \
                        and assignment.op == "=":
                    definitions[assignment.targets[0]] = new_value_tree(assignment)
        for mid, tree in definitions.items():
            if mid in names or tree is None:
                continue
            form = linear_form(tree)
            if form is None:
                continue
            coeffs = [form.get(n, Fraction(0)) for n in names]
            if not (all(c >= 0 for c in coeffs)
                    and sum(1 for c in coeffs if c > 0) >= 2
                    and abs(float(sum(coeffs)) - 1.0) < EPS):
                continue
            updated = set()
            ok = True
            for var, new_tree in self._branch_assignments(body):
                if var not in names:
                    continue
                update_form = new_tree and linear_form(new_tree)
                if (not update_form
                        or update_form.get(mid) != 1
                        or any(k not in (mid, CONST) for k in variables_of(update_form)
                               if k != mid)):
                    ok = False
                    break
                updated.add(var)
            if ok and len(updated) >= 2:
                return True
        return False

    def _branch_assignments(self, nodes):
        for node in nodes:
            kind = node.get("type")
            if kind == "OPERATION":
                assignment = parse_assignment(node.get("code", ""))
                if assignment and len(assignment.targets) == 1:
                    yield assignment.targets[0], new_value_tree(assignment)
            elif kind == "IF":
                yield from self._branch_assignments(node.get("true_body", []))
                yield from self._branch_assignments(node.get("false_body", []))
