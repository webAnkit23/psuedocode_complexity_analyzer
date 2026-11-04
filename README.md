# Time Complexity Analyzer — v7

A pure-Python tool that parses pseudocode and automatically computes its **worst-case time complexity**, including full recurrence solving for recursive algorithms.

---

## Quick Start

```bash
# interactive mode – type DONE when finished
python main.py

# analyze a file
python main.py examples/graph_dijkstra.txt

# skip the AST dump
python main.py examples/tree_bst.txt --no-ast

# machine-readable JSON
python main.py examples/dp_basics.txt --json

# suppress pedagogical notes
python main.py examples/graph_bfs.txt --no-notes

# pipe / stdin
cat my_algo.txt | python main.py
```

---

## Pseudocode Dialects Supported

The parser automatically detects and handles **all** of the following styles — you do **not** need to pick one.

### Classic keyword style
```
FUNCTION BINARY_SEARCH(A, lo, hi, key)
    WHILE lo <= hi
        mid = (lo + hi) / 2
        IF A[mid] == key THEN
            RETURN mid
        ELSEIF A[mid] < key THEN
            lo = mid + 1
        ELSE
            hi = mid - 1
        ENDIF
    ENDWHILE
    RETURN -1
ENDFUNCTION
```

### CLRS / textbook style (bare function header, indented body)
```
INSERTION-SORT(A)
    for j = 2 to A.length
        key = A[j]
        i = j - 1
        while i > 0 and A[i] > key
            A[i+1] = A[i]
            i = i - 1
        A[i+1] = key
```

### Python-like style
```python
def merge_sort(A, p, r):
    if p < r:
        q = (p + r) // 2
        merge_sort(A, p, q)
        merge_sort(A, q+1, r)
        merge(A, p, q, r)
```

### C-style for-loops and braces
```c
for (int i = 0; i < n; i++) {
    for (int j = 0; j < n; j++) {
        C[i][j] = 0;
        for (int k = 0; k < n; k++) {
            C[i][j] += A[i][k] * B[k][j];
        }
    }
}
```

### Line-numbered pseudocode (textbook style)
```
1.  FOR i = 1 TO n
2.      FOR j = 1 TO n
3.          A[i][j] = 0
4.  ENDFOR
```

### Unicode / CLRS math symbols

| Symbol | Meaning | Converted to |
|--------|---------|-------------|
| `⌊x⌋` | floor | `floor(x)` |
| `⌈x⌉` | ceiling | `ceil(x)` |
| `←` or `⟵` | assignment | `<-` |
| `≤ ≥ ≠` | comparisons | `<= >= !=` |
| `∈` | membership | `IN` |
| `∉` | non-membership | `NOT IN` |
| `∅` | empty set | `EMPTY` |
| `▷` or `▶` | CLRS comment | stripped |
| `lg` | log base 2 | `log` |
| `∞` | infinity | `INF` |

---

## Recurrence Solving

### Master Theorem

For T(n) = a·T(n/b) + f(n):

| Case | Condition | Result |
|------|-----------|--------|
| 1 | f(n) = O(n^(log_b a − ε)) | T(n) = Θ(n^(log_b a)) |
| 2 | f(n) = Θ(n^(log_b a)) | T(n) = Θ(n^(log_b a) · log n) |
| 2b | f(n) = Θ(n^p / log n) | T(n) = Θ(n^p · log log n) |
| 3 | f(n) = Ω(n^(log_b a + ε)) | T(n) = Θ(f(n)) |

```
FUNCTION MERGE_SORT(A, p, r)   // T(n) = 2T(n/2) + n  →  O(n log n)
    IF p < r THEN
        q = FLOOR((p + r) / 2)
        MERGE_SORT(A, p, q)
        MERGE_SORT(A, q+1, r)
        MERGE(A, p, q, r)
    ENDIF
ENDFUNCTION
```

### Akra-Bazzi Method

For unequal sub-problems (e.g. T(n/3) + T(2n/3) + n):

Finds exponent *p* such that Σ aᵢ·(bᵢ)^p = 1, then applies:

```
T(n) = Θ(n^p · (1 + ∫₁⿰ f(u)/u^(p+1) du))
```

Example: T(n/3) + T(2n/3) + n → **O(n log n)**

### Square-root Recurrences

Substitutes m = log n to convert T(√n) recurrences:

| Recurrence | Solution |
|-----------|---------|
| T(n) = T(√n) + 1 | O(log log n) |
| T(n) = 2·T(√n) + log n | O(log n · log log n) |

### Subtract Recurrences

| Recurrence | Solution |
|-----------|---------|
| T(n) = T(n−1) + 1 | O(n) |
| T(n) = T(n−1) + n | O(n²) |
| T(n) = 2·T(n−1) + 1 | O(2ⁿ) |

### Euclidean GCD

T(n) = T(n mod m) + O(1) → **O(log n)**

---

## Data Structures & Algorithm Primitives

### Stack / Queue Operations

The analyzer detects **amortized O(1)** patterns:
- **Monotonic stack**: elements pushed once outside loop, popped inside `WHILE` → O(1) amortized per element
- **Sliding-window / two-pointer**: pointer only increments, bounded by outer loop variable → O(1) amortized

```
FUNCTION NEXT_GREATER(A, n)    // → O(n) via amortized analysis
    stack = EMPTY_STACK
    FOR i = 1 TO n
        WHILE NOT IS_EMPTY(stack) AND A[TOP(stack)] < A[i]
            POP(stack)
        ENDWHILE
        PUSH(stack, i)
    ENDFOR
ENDFUNCTION
```

### Graph Algorithms

Built-in cost model for CLRS graph primitives:

| Primitive | Cost |
|-----------|------|
| `RELAX(u,v,w)` | O(log V) if PQ in scope, else O(1) |
| `INITIALIZE-SINGLE-SOURCE(G,s)` | O(V) |
| `MAKE-SET(x)`, `FIND-SET(x)`, `UNION(x,y)` | O(1) amortized |
| `TRANSPOSE(G)`, `REVERSE-GRAPH(G)` | O(E) |
| `SORT-EDGES(G)` | O(E log E) |

### Tree Algorithms

Recognizes pointer chasing patterns through `.left`, `.right`, `.parent`, `.next`:
- Tree height noted as O(h); h = O(log n) balanced, O(n) worst-case
- Recursive traversals: INORDER/PREORDER/POSTORDER → T(n) = 2T(n/2) + O(1) → O(n)

---

## Output Explained

```
Function: MERGE_SORT
  Recurrence: T(n) = 2·T(n/2) + n
  Time Complexity: O(n log n)
  - Master Theorem Case 2: f(n) = Θ(n^1) = Θ(n^log_2(2)), so T(n) = Θ(n log n)
```

| Line | Meaning |
|------|---------|
| `Recurrence:` | The recurrence relation detected from recursive calls |
| `Time Complexity:` | The solved Big-O result |
| `- note` | Pedagogical explanation of WHY (theorem used, case number) |
| `! warning` | Ambiguity or limitation in the analysis |

### Flags

| Flag | Effect |
|------|--------|
| `--no-ast` | Hide the parsed AST (cleaner output) |
| `--no-notes` | Hide pedagogical notes |
| `--json` | Output JSON array for programmatic use |
| `--stdin` | Force reading from stdin |
| `--version` | Print version and exit |
| `--help` | Show full help text |

---

## Project Structure

```
complexity_analyzer/
├── main.py                # CLI entry point (v7)
├── Parser.py              # Pseudocode parser → AST
├── expressions.py         # Expression & collection analysis
├── complexity.py          # Complexity algebra (O-notation arithmetic)
├── recurrence_solver.py   # Master, Akra-Bazzi, subtract, sqrt, GCD
├── recursion.py           # Recursive call detection
├── program_analyzer.py    # Top-level analysis orchestrator
├── goto_resolver.py       # GOTO/LABEL flattening
├── run_all_examples.py    # Batch-run examples/ → ANALYSIS_REPORT.md
├── test_all_cases.py      # 180-case regression suite
├── ANALYSIS_REPORT.md     # Auto-generated report
└── examples/
    ├── graph_dijkstra.txt         # Dijkstra → O(V log V + E log V)
    ├── graph_bellman_ford.txt     # Bellman-Ford → O(VE)
    ├── graph_bfs.txt              # BFS → O(V + E)
    ├── graph_dfs_recursive.txt    # DFS → O(V + E)
    ├── graph_floyd_warshall.txt   # Floyd-Warshall → O(V³)
    ├── graph_kruskal.txt          # Kruskal → O(E log E)
    ├── graph_prim.txt             # Prim → O(E log V)
    ├── graph_components.txt       # Connected components
    ├── graph_topological_kahn.txt # Kahn BFS topo sort
    ├── graph_dfs_iterative.txt    # Iterative DFS
    ├── graph_adjacency_matrix.txt # Matrix-based graph ops
    ├── tree_traversals.txt        # In/Pre/Post-order → O(n)
    ├── tree_bst.txt               # BST search/insert → O(h)
    ├── stack_monotonic.txt        # Monotonic stack → O(n) amortized
    ├── two_pointer.txt            # Sliding window → O(n)
    ├── dp_basics.txt              # DP: Fibonacci, LCS, Knapsack
    ├── sqrt_recurrence.txt        # T(√n) recurrences → O(log log n)
    ├── recursion_mix.txt          # Mixed recursive examples
    └── nested_repeat_until.txt    # REPEAT-UNTIL nesting
```

---

## Running Tests

```bash
python test_all_cases.py
# RESULT: 180 passed, 0 failed, 180 total
```

## Regenerate Analysis Report

```bash
python run_all_examples.py
# writes ANALYSIS_REPORT.md
```

---

## Complexity Algebra Reference

The engine computes with symbolic complexity expressions:

| Expression | Example | Class |
|-----------|---------|-------|
| O(1) | constant | `Complexity.const()` |
| O(log n) | binary search | `Complexity.log("n")` |
| O(log log n) | √n recurrence | `Complexity.loglog("n")` |
| O(n) | linear scan | `Complexity.var("n")` |
| O(n log n) | merge sort | `Complexity.var("n").mul(Complexity.log("n"))` |
| O(n²) | bubble sort | `Complexity.var("n").pow(2)` |
| O(n^k) | k nested loops | `Complexity.var("n").pow(k)` |
| O(2ⁿ) | exponential | `Complexity.exp(2, "n")` |
| O(n^p log n) | Master Thm Case 2 | combined |

---

## Supported Constructs

| Construct | Keyword forms |
|-----------|--------------|
| For loop (up) | `FOR i = 1 TO n`, `for i in range(n)`, `for (int i=0; i<n; i++)` |
| For loop (down) | `FOR i = n DOWNTO 1` |
| For loop (step) | `FOR i = 1 TO n STEP 2`, `for (int i=1; i<n; i*=2)` |
| For-each | `FOR EACH x IN collection`, `for x in list`, `for (auto x : arr)` |
| While | `WHILE cond`, `while cond:` |
| Do-while | `DO ... WHILE cond`, `REPEAT ... UNTIL cond` |
| If/Else | `IF ... THEN ... ELSE ... ENDIF`, `if ...: ... else:` |
| Function | `FUNCTION f(x) ... ENDFUNCTION`, `def f(x):`, `F(A, n)` at column 0 |
| Recursion | any call to the function itself, with any sub-problem expression |
| Return | `RETURN value` |
| Comments | `// ...`, `# ...`, `/* ... */`, `-- ...`, `▷ ...` |
