"""
program_analyzer.py
-------------------
Analyzes a whole program (several functions plus optional top-level code).

* builds the call graph and finds direct and mutual recursion
* directly recursive functions -> RecursionAnalyzer + RecurrenceSolver
* everything else               -> ComplexityAnalyzer
* calls between functions are costed (non-recursive callees are analysed at
  the call site with the real arguments; recursive callees use their solved
  complexity)
"""

import copy
import re

from complexity import (
    SIZE_VAR, Complexity, ComplexityAnalyzer, Unsupported,
)
from expressions import (
    assigned_variables, extract_calls, find_range_pair, node_texts, walk,
)
from goto_resolver import GotoResolver
from recurrence_solver import RecurrenceSolver
from recursion import RecursionAnalyzer, Summary


class FunctionResult:
    def __init__(self, name, kind="function"):
        self.name = name
        self.kind = kind            # 'function' or 'main'
        self.complexity = None      # Complexity, or None if unsolved
        self.recurrence = None      # Recurrence for directly recursive functions
        self.notes = []
        self.warnings = []
        self.error = None

    @property
    def text(self):
        if self.complexity is not None:
            return str(self.complexity)
        return f"Unable to solve: {self.error}"


class ProgramAnalyzer:
    def __init__(self, ast):
        self.ast = ast
        self._pick_graph_variables(ast)
        self.functions = {}
        self.goto_notes = {}
        self.goto_warnings = {}
        for node in ast:
            if node.get("type") == "FUNCTION":
                resolver = GotoResolver()
                fixed = copy.deepcopy(node)
                fixed["body"] = resolver.resolve(node.get("body", []))
                self.functions[node["name"]] = fixed
                self.goto_notes[node["name"]] = resolver.notes
                self.goto_warnings[node["name"]] = resolver.warnings
        resolver = GotoResolver()
        self.top_level = resolver.resolve(
            [n for n in ast if n.get("type") != "FUNCTION"])
        self.goto_notes["<main program>"] = resolver.notes
        self.goto_warnings["<main program>"] = resolver.warnings
        self.inline_cache = {}
        self._solved = {}
        self._graph = self._build_call_graph()
        self._direct = {n for n, callees in self._graph.items() if n in callees}
        self._mutual = self._find_mutual()

    def _pick_graph_variables(self, ast):
        """V/E (or n/m) are the graph sizes; names follow the pseudocode."""
        words = set()
        for node in walk(ast):
            for text in node_texts(node):
                words.update(re.findall(r"[A-Za-z_]\w*", text))
            words.update(node.get("parameters", []))
        lowered = {w.lower() for w in words}
        graph_words = {"adj", "adjacency", "neighbors", "neighbours", "vertices",
                       "vertex", "edges", "edge", "graph", "g", "successors"}
        graph_like = bool(lowered & graph_words) or any(
            w.lower().startswith("adj") for w in words)
        if "V" in words or "E" in words:
            self.node_var, self.edge_var = "V", "E"
        elif graph_like and not ("n" in words and "m" in words):
            self.node_var, self.edge_var = "V", "E"
        else:
            self.node_var, self.edge_var = "n", "m"

    # ------------------------------------------------------------------
    # call graph
    # ------------------------------------------------------------------
    def _build_call_graph(self):
        graph = {}
        for name, node in self.functions.items():
            callees = set()
            for inner in walk(node.get("body", [])):
                for text in node_texts(inner):
                    for called, _ in extract_calls(text):
                        if called in self.functions:
                            callees.add(called)
            graph[name] = callees
        return graph

    def _find_mutual(self):
        """Functions that belong to a call cycle of length >= 2."""
        mutual = set()
        for start in self.functions:
            stack, seen = list(self._graph[start] - {start}), set()
            while stack:
                current = stack.pop()
                if current == start:
                    mutual.add(start)
                    break
                if current in seen:
                    continue
                seen.add(current)
                stack.extend(self._graph.get(current, ()) - {current})
        return mutual

    def is_recursive(self, name):
        return name in self._direct or name in self._mutual

    # ------------------------------------------------------------------
    # recursive functions
    # ------------------------------------------------------------------
    def _solve_recursive(self, name):
        if name in self._solved:
            return self._solved[name]
        node = self.functions[name]
        recurrence = RecursionAnalyzer(self).analyze_function(node)
        if recurrence is None:
            outcome = (None, None, None)
        elif recurrence.error:
            outcome = (recurrence, None, recurrence.error)
        elif recurrence.direct_result is not None:
            from recurrence_solver import SolveResult
            outcome = (recurrence,
                       SolveResult(recurrence.direct_result, recurrence.notes),
                       None)
        else:
            solved = RecurrenceSolver().solve(recurrence)
            if solved.complexity is None:
                outcome = (recurrence, None, solved.error)
            else:
                outcome = (recurrence, solved, None)
        self._solved[name] = outcome
        return outcome

    def recursive_summary(self, name):
        if name in self._mutual:
            return None
        recurrence, solved, _ = self._solve_recursive(name)
        if recurrence is None or solved is None:
            return None
        return Summary(solved.complexity, recurrence.measure,
                       shared=recurrence.shared)

    # ------------------------------------------------------------------
    # public API
    # ------------------------------------------------------------------
    def analyze(self):
        results = [self.analyze_function(name) for name in self.functions]
        if self.top_level:
            results.append(self._analyze_main(self.top_level))
        return results

    def analyze_function(self, name):
        node = self.functions[name]
        result = FunctionResult(name)

        if name in self._mutual:
            result.error = (
                "mutual recursion (functions that call each other in a cycle) "
                "is not supported"
            )
            return result

        if name in self._direct:
            recurrence, solved, error = self._solve_recursive(name)
            if recurrence is None:       # call found only in unreachable text
                return self._analyze_plain(node, result)
            result.recurrence = recurrence
            result.warnings.extend(recurrence.warnings)
            if solved is None:
                result.error = error
                return result
            result.complexity = solved.complexity
            result.notes = solved.notes + self.goto_notes.get(name, [])
            result.warnings.extend(self.goto_warnings.get(name, []))
            if recurrence.measure[0] == "structural":
                return result
            # Show the answer in the parameter's own name (f(k) -> O(k)).
            if (recurrence.measure[0] == "single"
                    and SIZE_VAR not in node.get("parameters", [])):
                param = node["parameters"][recurrence.measure[1]]
                if param != SIZE_VAR:
                    result.complexity = solved.complexity.substitute(
                        {SIZE_VAR: Complexity.var(param)})
            return result

        return self._analyze_plain(node, result)

    def _analyze_plain(self, node, result):
        params = node.get("parameters", [])
        env = {}
        pair = find_range_pair(params)
        if pair:
            env[pair[0]] = Complexity.const()
            env[pair[1]] = Complexity.var(SIZE_VAR)
        analyzer = ComplexityAnalyzer(
            program=self, env=env,
            assigned=assigned_variables(node.get("body", [])),
        )
        try:
            result.complexity = analyzer.analyze(node.get("body", []))
        except Unsupported as error:
            result.error = str(error)
        result.warnings.extend(analyzer.warnings)
        result.notes.extend(analyzer.notes)
        result.notes.extend(self.goto_notes.get(node["name"], []))
        result.warnings.extend(self.goto_warnings.get(node["name"], []))
        return result

    def _analyze_main(self, nodes):
        result = FunctionResult("<main program>", kind="main")
        analyzer = ComplexityAnalyzer(program=self)
        try:
            result.complexity = analyzer.analyze(nodes)
        except Unsupported as error:
            result.error = str(error)
        result.warnings.extend(analyzer.warnings)
        result.notes.extend(analyzer.notes)
        result.notes.extend(self.goto_notes.get("<main program>", []))
        result.warnings.extend(self.goto_warnings.get("<main program>", []))
        return result


def analyze_source(code):
    """Parse pseudocode text and analyze it. Returns (ast, results)."""
    from Parser import Parser
    ast = Parser(code).parse()
    return ast, ProgramAnalyzer(ast).analyze()
