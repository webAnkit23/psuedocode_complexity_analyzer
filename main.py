"""
main.py - Time Complexity Analyzer for Pseudocode (V7)

Supports textbook-style pseudocode from CLRS, Cormen, Sedgewick, and similar sources.
Handles Stack, Queue, Graph, Tree algorithms with full recursive recurrence solving.

Usage
-----
    python main.py                      # interactive mode  (type DONE to finish)
    python main.py file.txt             # analyze a file
    python main.py file.txt --no-ast    # skip the parsed-AST section
    python main.py file.txt --json      # output JSON (machine-readable)
    python main.py file.txt --no-notes  # suppress pedagogical notes
    python main.py --stdin              # read from stdin (same as piping)
    python main.py --version            # print version and exit
    python main.py --help               # show this help

Pseudocode dialects recognized
------------------------------
    - Classic keyword style  : FOR i = 1 TO n, WHILE, IF/ELSE, FUNCTION/END
    - CLRS (bare headers)    : MERGE-SORT(A, p, r) at indent 0, indented body
    - Indented / Python-like : def f(n):, for i in range(n):, if ...:
    - C-style                : for (int i=0; i<n; i++), { } braces
    - Line-numbered          : "1. FOR i..." or "(2) WHILE..."
    - Unicode math           : ⌊n/2⌋, ←, ≤, ≥, ≠, ∈, ∅, ▷ (comments), lg

Recurrence solving
------------------
    - Master Theorem (all 3 cases + extended Case 2b: f(n)=n^p/log n)
    - Akra-Bazzi method (unequal sub-problems, e.g. T(n/3)+T(2n/3)+n)
    - Subtract recurrences  T(n) = T(n-k) + f(n)
    - Square-root recurrences  T(n) = a·T(√n) + f(n)  → O(log log n) family
    - Euclidean GCD recurrence  T(n) = T(n mod m) + O(1)  → O(log n)

Amortized analysis
------------------
    - Monotonic stack / queue: push outside loop, pop inside → O(1) amortized
    - Two-pointer / sliding window: single-direction pointers → O(1) amortized

Graph / Tree helpers recognized
--------------------------------
    - RELAX(u,v,w) → O(log V) when a priority queue is in scope, else O(1)
    - INITIALIZE-SINGLE-SOURCE, INITIALIZE → O(V)
    - MAKE-SET, FIND-SET, UNION (union-find) → O(1) amortized
    - TRANSPOSE, REVERSE-GRAPH → O(E)
    - SORT-EDGES → O(E log E)
"""

import json             
import sys

from Parser import Parser
from program_analyzer import ProgramAnalyzer

VERSION = "7.0"
BANNER = f"TIME COMPLEXITY ANALYZER  v{VERSION}"



def print_ast(nodes, level=0):
    pad = "  " * level
    for node in nodes:
        kind = node["type"]
        print(pad + kind)
        if kind == "FUNCTION":
            print(f"{pad}  Name: {node['name']}")
            print(f"{pad}  Parameters: {node['parameters']}")
            print_ast(node["body"], level + 1)
        elif kind == "FUNCTION_CALL":
            print(f"{pad}  Call: {node['name']}({', '.join(node['arguments'])})")
        elif kind == "FOR":
            if node.get("collection") is not None:
                names = node.get("variables") or [node["variable"]]
                shown = names[0] if len(names) == 1 else "(" + ", ".join(names) + ")"
                print(f"{pad}  {shown} IN {node['collection']}")
            else:
                word = "DOWNTO" if node.get("direction") == "DOWN" else "TO"
                step = f" STEP {node['step']}" if node.get("step") else ""
                print(f"{pad}  {node['variable']} = {node['start']} {word} {node['end']}{step}")
            print_ast(node["body"], level + 1)
        elif kind in ("WHILE", "REPEAT_UNTIL", "DO_WHILE"):
            print(f"{pad}  Condition: {node['condition']}")
            print_ast(node["body"], level + 1)
        elif kind == "IF":
            print(f"{pad}  Condition: {node['condition']}")
            print(f"{pad}  TRUE:")
            print_ast(node["true_body"], level + 2)
            if node.get("false_body"):
                print(f"{pad}  FALSE:")
                print_ast(node["false_body"], level + 2)
        elif kind == "RETURN":
            print(f"{pad}  RETURN" + (f" {node['value']}" if node.get("value") else ""))
        elif kind == "OPERATION":
            print(f"{pad}  {node['code']}")
        elif kind == "GOTO":
            print(f"{pad}  Target: {node.get('label', '')}")
        elif kind == "LABEL":
            print(f"{pad}  Name: {node.get('name', '')}")


# ---------------------------------------------------------------------------
# Human-readable results printer
# ---------------------------------------------------------------------------

def print_results(results, show_notes=True):
    """Print analysis results in a human-readable format."""
    for r in results:
        label = "Program" if r.kind == "main" else "Function"
        print(f"\n{label}: {r.name}")
        if r.recurrence is not None:
            structural = r.recurrence.measure == ("structural",)
            for line in r.recurrence.describe():
                print(f"  {'  ' if structural else 'Recurrence: '}{line}")
            if r.recurrence.size_text and r.recurrence.size_text != "n = n":
                print(f"  ({r.recurrence.size_text})")
        print(f"  Time Complexity: {r.text}")
        if show_notes:
            for note in r.notes:
                print(f"  - {note}")
        for warning in r.warnings:
            print(f"  ! {warning}")


def _result_to_dict(r):
    """Convert one AnalysisResult to a JSON-serializable dict."""
    d = {
        "name": r.name,
        "kind": r.kind,
        "complexity": r.text,
        "notes": list(r.notes),
        "warnings": list(r.warnings),
    }
    if r.recurrence is not None:
        d["recurrence"] = {
            "lines": r.recurrence.describe(),
            "size_text": r.recurrence.size_text,
        }
    return d


# ---------------------------------------------------------------------------
# Interactive input
# ---------------------------------------------------------------------------

def read_interactive():
    sep = "=" * 60
    print(sep)
    print(f"       {BANNER}")
    print(sep)
    print()
    print("Supported dialects: classic keywords, CLRS-style, Python-like,")
    print("C-style for-loops, line-numbered, Unicode math (⌊⌋, ←, ≤, ∈, ▷ …)")
    print()
    print("Enter pseudocode below. Type  DONE  on its own line to finish.")
    print()
    lines = []
    while True:
        try:
            line = input()
        except EOFError:
            break
        if line.strip().upper() == "DONE":
            break
        lines.append(line)
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# CLI argument parsing  (stdlib only – no argparse import needed)
# ---------------------------------------------------------------------------

def _parse_argv(argv):
    flags = set()
    paths = []
    for a in argv:
        if a.startswith("--"):
            flags.add(a)
        else:
            paths.append(a)
    return flags, paths


# ---------------------------------------------------------------------------
# Main entry point
# ---------------------------------------------------------------------------

def main(argv):
    flags, paths = _parse_argv(argv)

    if "--help" in flags or "-h" in flags:
        print(__doc__)
        return 0

    if "--version" in flags:
        print(BANNER)
        return 0

    show_ast   = "--no-ast"   not in flags
    show_notes = "--no-notes" not in flags
    json_out   = "--json"     in flags
    use_stdin  = "--stdin"    in flags

    # ---- read source code ----
    if paths:
        try:
            with open(paths[0], encoding="utf-8") as fh:
                code = fh.read()
        except FileNotFoundError:
            print(f"Error: file not found: {paths[0]}", file=sys.stderr)
            return 1
    elif use_stdin or not sys.stdin.isatty():
        code = sys.stdin.read()
    else:
        code = read_interactive()

    # ---- parse ----
    try:
        ast = Parser(code).parse()
    except SyntaxError as error:
        if json_out:
            print(json.dumps({"error": str(error)}, indent=2))
        else:
            sep = "=" * 60
            print(f"\n{sep}\nSYNTAX ERROR\n{sep}")
            print(error)
        return 1

    # ---- analyze ----
    results = ProgramAnalyzer(ast).analyze()

    # ---- output ----
    if json_out:
        print(json.dumps([_result_to_dict(r) for r in results], indent=2))
        return 0

    sep = "=" * 60

    if show_ast:
        print(f"\n{sep}\nPARSED STRUCTURE\n{sep}\n")
        print_ast(ast)

    print(f"\n{sep}\nANALYSIS RESULTS (worst case)  —  {BANNER}\n{sep}")
    print_results(results, show_notes=show_notes)
    print()

    # ---- summary footer ----
    funcs    = [r for r in results if r.kind == "function"]
    warnings = sum(len(r.warnings) for r in results)
    print(f"Analyzed: {len(results)} unit(s) "
          f"({len(funcs)} function(s)), {warnings} warning(s)")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
