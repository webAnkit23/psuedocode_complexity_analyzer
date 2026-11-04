"""
test_all_cases.py - regression suite for the Time Complexity Analyzer (V5)

Run:  python test_all_cases.py
Every case gives pseudocode and the complexity the analyzer must report for the
named function (or for the top-level program when no name is given).
"""

import sys
import traceback

from Parser import Parser
from program_analyzer import analyze_source


def result_for(code, name=None):
    _, results = analyze_source(code)
    if name is None:
        name = results[0].name
    return next(r for r in results if r.name == name)


# (title, code, expected "O(...)" or "ERROR:<substring>", function name or None)
CASES = []


def case(title, code, expected, name=None):
    CASES.append((title, code, expected, name))


# ----------------------------------------------------------------- loops
case("constant work", "x = 1\ny = 2", "O(1)")
case("linear FOR", "FOR i = 1 TO n\n  x = x + 1\nEND", "O(n)")
case("FOR with arrow and END FOR",
     "FOR i <- 1 TO n\n  x <- x + 1\nEND FOR", "O(n)")
case("FOR ... DO", "FOR i = 1 TO n DO\n  x = x + 1\nEND", "O(n)")
case("FOR with constant bound", "FOR i = 1 TO 10\n  x = x + 1\nEND", "O(1)")
case("nested FOR", "FOR i = 1 TO n\n FOR j = 1 TO n\n  x = 1\n END\nEND", "O(n^2)")
case("triple FOR",
     "FOR i = 1 TO n\n FOR j = 1 TO n\n  FOR k = 1 TO n\n   x = 1\n  END\n END\nEND",
     "O(n^3)")
case("dependent inner loop (j up to i)",
     "FOR i = 1 TO n\n FOR j = 1 TO i\n  x = 1\n END\nEND", "O(n^2)")
case("bubble sort",
     "FOR i = 1 TO n\n FOR j = 1 TO n-i\n  IF A[j] > A[j+1]\n   t = A[j]\n   A[j] = A[j+1]\n   A[j+1] = t\n  END\n END\nEND",
     "O(n^2)")
case("FOR bound n*n", "FOR i = 1 TO n*n\n x = 1\nEND", "O(n^2)")
case("FOR bound n*n + n", "FOR i = 1 TO n*n + n\n x = 1\nEND", "O(n^2)")
case("FOR bound n/2", "FOR i = 1 TO n/2\n x = 1\nEND", "O(n)")
case("FOR bound log n", "FOR i = 1 TO log(n)\n x = 1\nEND", "O(log n)")
case("FOR bound sqrt n", "FOR i = 1 TO sqrt(n)\n x = 1\nEND", "O(n^(1/2))")
case("FOR bound 2^n", "FOR i = 1 TO 2^n\n x = 1\nEND", "O(2^n)")
case("FOR STEP 2", "FOR i = 1 TO n STEP 2\n x = 1\nEND", "O(n)")
case("FOR STEP *2 (logarithmic)", "FOR i = 1 TO n STEP *2\n x = 1\nEND", "O(log n)")
case("FOR DOWNTO", "FOR i = n DOWNTO 1\n x = 1\nEND", "O(n)")
case("FOR EACH", "FOR EACH x IN A\n s = s + x\nEND", "O(n)")
case("different variables n and m",
     "FOR i = 1 TO n\n FOR j = 1 TO m\n  x = 1\n END\nEND", "O(n * m)")
case("sequential loops add",
     "FOR i = 1 TO n\n x = 1\nEND\nFOR j = 1 TO m\n y = 1\nEND", "O(n + m)")
case("sequential n and n^2",
     "FOR i = 1 TO n\n x = 1\nEND\nFOR i = 1 TO n\n FOR j = 1 TO n\n  y = 1\n END\nEND",
     "O(n^2)")
case("n log n: FOR with halving WHILE inside",
     "FOR i = 1 TO n\n j = n\n WHILE j > 1\n  j = j / 2\n END\nEND", "O(n log n)")

case("WHILE i < n, i++", "i = 0\nWHILE i < n\n i = i + 1\nEND", "O(n)")
case("WHILE with END WHILE", "WHILE i < n\n i <- i + 1\nEND WHILE", "O(n)")
case("WHILE with ENDWHILE", "WHILE i < n\n i <- i + 1\nENDWHILE", "O(n)")
case("WHILE i += 1", "i = 0\nWHILE i < n\n i += 1\nEND", "O(n)")
case("WHILE i++", "i = 0\nWHILE i < n\n i++\nEND", "O(n)")
case("WHILE counting down", "WHILE n > 0\n n = n - 1\nEND", "O(n)")
case("WHILE halving", "WHILE n > 1\n n = n / 2\nEND", "O(log n)")
case("WHILE doubling", "i = 1\nWHILE i < n\n i = i * 2\nEND", "O(log n)")
case("WHILE doubling *=", "i = 1\nWHILE i < n\n i *= 2\nEND", "O(log n)")
case("WHILE tripling", "i = 1\nWHILE i <= n\n i = 3 * i\nEND", "O(log n)")
case("WHILE halving with floor", "WHILE n >= 1\n n = floor(n / 2)\nEND", "O(log n)")
case("WHILE i*i <= n (sqrt)", "i = 1\nWHILE i * i <= n\n i = i + 1\nEND", "O(n^(1/2))")
case("WHILE with AND takes the smaller bound",
     "WHILE i < n AND j < 5\n i = i + 1\n j = j + 1\nEND", "O(1)")
case("nested WHILE inside FOR (n^2)",
     "FOR i = 1 TO n\n j = 0\n WHILE j < n\n  j = j + 1\n END\nEND", "O(n^2)")
case("binary search (iterative)",
     "lo = 1\nhi = n\nWHILE lo <= hi\n mid = (lo + hi) / 2\n IF A[mid] == x\n  RETURN mid\n ELSE IF A[mid] < x\n  lo = mid + 1\n ELSE\n  hi = mid - 1\n END\nEND",
     "O(log n)")
case("two pointers", "i = 1\nj = n\nWHILE i < j\n i = i + 1\n j = j - 1\nEND", "O(n)")
case("Euclid gcd (a mod b)",
     "WHILE b != 0\n t = b\n b = a % b\n a = t\nEND", "O(log n)")
case("geometric sum: inner loop up to i where i doubles",
     "i = 1\nWHILE i < n\n FOR j = 1 TO i\n  x = 1\n END\n i = i * 2\nEND", "O(n)")
case("geometric sum: n + n/2 + n/4 ...",
     "WHILE n > 1\n FOR i = 1 TO n\n  x = 1\n END\n n = n / 2\nEND", "O(n)")
case("unknown WHILE falls back to O(n)", "WHILE x != 0\n x = A[x]\nEND", "O(n)")
case("WHILE TRUE with break falls back to O(n)",
     "WHILE TRUE\n IF x > 3\n  BREAK\n END\n x = x + 1\nEND", "O(n)")

case("REPEAT UNTIL counting down", "REPEAT\n n = n - 1\nUNTIL n <= 1", "O(n)")
case("REPEAT UNTIL halving", "REPEAT\n n = n / 2\nUNTIL n <= 1", "O(log n)")
case("REPEAT UNTIL doubling", "i = 1\nREPEAT\n i = i * 2\nUNTIL i >= n", "O(log n)")
case("REPEAT UNTIL counting up", "i = 0\nREPEAT\n i = i + 1\nUNTIL i == n", "O(n)")
case("DO WHILE halving", "DO\n n = n / 2\nEND DO WHILE n > 1", "O(log n)")
case("DO WHILE counting", "DO\n i = i + 1\nEND DO WHILE i < n", "O(n)")
case("DO WHILE colon form", "DO:\n i = i + 1\nENDDO WHILE i < n", "O(n)")

# ---------------------------------------------------------- control flow
case("IF takes worst branch",
     "IF x > 0\n FOR i = 1 TO n\n  y = 1\n END\nELSE\n y = 2\nEND", "O(n)")
case("IF / ELSE IF / ELSE chain (shared END)",
     "IF x > 0\n y = 1\nELSE IF x < 0\n FOR i = 1 TO n\n  y = 2\n END\nELSE\n y = 3\nEND IF",
     "O(n)")
case("OTHERWISE keyword",
     "IF x > 0\n y = 1\nOTHERWISE\n FOR i = 1 TO n\n  y = 2\n END\nEND", "O(n)")
case("one-line IF THEN", "IF x > 0 THEN y = 1\nFOR i = 1 TO n\n x = 1\nEND", "O(n)")
case("BREAK and CONTINUE",
     "FOR i = 1 TO n\n IF i > 5\n  BREAK\n ELSE\n  CONTINUE\n END\nEND", "O(n)")
case("comments are ignored",
     "// linear scan\nFOR i = 1 TO n   # loop\n x = 1 // body\nEND", "O(n)")
case("lowercase keywords", "for i = 1 to n\n x = 1\nend", "O(n)")
case("legacy compact terminators",
     "FUNCTION test(n)\n FOR i <- 1 TO n\n  WHILE j < n\n   j <- j + 1\n  ENDWHILE\n ENDFOR\n RETURN n\nENDFUNCTION",
     "O(n^2)")
case("GOTO is parsed (estimate ignores jumps)",
     "FUNCTION test(n)\n GOTO finish\n retry:\n GOTO retry\n finish:\n RETURN n\nEND FUNCTION",
     "O(1)")

# ----------------------------------------------------------- functions
case("function with loop (params named)",
     "FUNCTION scan(n)\n FOR i = 1 TO n\n  x = x + 1\n END\nEND", "O(n)")
case("function with array param uses len()",
     "FUNCTION f(A)\n FOR i = 1 TO len(A)\n  x = 1\n END\nEND", "O(n)")
case("helper call is costed with real arguments",
     "FUNCTION helper(k)\n FOR i = 1 TO k\n  x = 1\n END\nEND\nFUNCTION main_fn(n)\n FOR i = 1 TO n\n  helper(n)\n END\nEND",
     "O(n^2)", "main_fn")
case("helper called with a constant",
     "FUNCTION helper(k)\n FOR i = 1 TO k\n  x = 1\n END\nEND\nFUNCTION main_fn(n)\n FOR i = 1 TO n\n  helper(5)\n END\nEND",
     "O(n)", "main_fn")
case("builtin sort() is n log n", "FUNCTION f(A)\n sort(A)\nEND", "O(n log n)")
case("WORK(n) placeholder", "FUNCTION f(n)\n WORK(n)\nEND", "O(n)")
case("WORK(n^2) placeholder", "FUNCTION f(n)\n WORK(n^2)\nEND", "O(n^2)")

# ----------------------------------------------------------- recursion
case("T(n)=T(n-1)  (README example 2)",
     "FUNCTION f(n)\n IF n <= 1\n  RETURN\n END\n f(n - 1)\nEND", "O(n)", "f")
case("T(n)=2T(n-1)  (README example 1)",
     "FUNCTION f(n)\n IF n <= 1\n  RETURN\n END\n f(n - 1)\n f(n - 1)\nEND",
     "O(2^n)", "f")
case("T(n)=3T(n-1)",
     "FUNCTION f(n)\n IF n <= 0\n  RETURN\n END\n f(n-1)\n f(n-1)\n f(n-1)\nEND",
     "O(3^n)", "f")
case("Fibonacci",
     "FUNCTION fib(n)\n IF n <= 1\n  RETURN n\n END\n RETURN fib(n-1) + fib(n-2)\nEND",
     "O(1.618^n)", "fib")
case("factorial (RETURN n * f(n-1))",
     "FUNCTION fact(n)\n IF n <= 1\n  RETURN 1\n END\n RETURN n * fact(n - 1)\nEND",
     "O(n)", "fact")
case("T(n)=T(n/2)  (log n)",
     "FUNCTION f(n)\n IF n <= 1\n  RETURN\n END\n f(n / 2)\nEND", "O(log n)", "f")
case("T(n)=T(n/2)+O(1) via RETURN",
     "FUNCTION h(n)\n IF n <= 1\n  RETURN n\n END\n RETURN h(n / 2)\nEND", "O(log n)", "h")
case("T(n)=2T(n/2)  -> n",
     "FUNCTION f(n)\n IF n <= 1\n  RETURN\n END\n f(n/2)\n f(n/2)\nEND", "O(n)", "f")
case("T(n)=2T(n/2)+WORK(n)  (README example 3)",
     "FUNCTION f(n)\n IF n <= 1\n  RETURN\n END\n f(n/2)\n f(n/2)\n WORK(n)\nEND",
     "O(n log n)", "f")
case("T(n)=T(n/2)+n  -> n",
     "FUNCTION f(n)\n IF n <= 1\n  RETURN\n END\n f(n/2)\n FOR i = 1 TO n\n  x = 1\n END\nEND",
     "O(n)", "f")
case("T(n)=4T(n/2)+n^2  (Master equality case)",
     "FUNCTION f(n)\n IF n <= 1\n  RETURN\n END\n f(n/2)\n f(n/2)\n f(n/2)\n f(n/2)\n WORK(n^2)\nEND",
     "O(n^2 log n)", "f")
case("T(n)=3T(n/2)+n  -> n^1.585",
     "FUNCTION f(n)\n IF n <= 1\n  RETURN\n END\n f(n/2)\n f(n/2)\n f(n/2)\n WORK(n)\nEND",
     "O(n^1.585)", "f")
case("T(n)=8T(n/2)+n^2  -> n^3",
     "FUNCTION f(n)\n IF n <= 1\n  RETURN\n END\n FOR i = 1 TO 8\n  f(n/2)\n END\n WORK(n^2)\nEND",
     "O(n^3)", "f")
case("T(n)=T(n-1)+n  (loop work) -> n^2",
     "FUNCTION f(n)\n IF n <= 1\n  RETURN\n END\n FOR i = 1 TO n\n  x = 1\n END\n f(n-1)\nEND",
     "O(n^2)", "f")
case("T(n)=T(n-1)+log n -> n log n",
     "FUNCTION f(n)\n IF n <= 1\n  RETURN\n END\n WORK(log(n))\n f(n-1)\nEND",
     "O(n log n)", "f")
case("T(n)=T(n/2)+T(n/4)+n  (unequal sizes) -> n",
     "FUNCTION f(n)\n IF n <= 1\n  RETURN\n END\n f(n/2)\n f(n/4)\n WORK(n)\nEND",
     "O(n)", "f")
case("T(n)=T(2n/3)+1 -> log n",
     "FUNCTION f(n)\n IF n <= 1\n  RETURN\n END\n f(2*n/3)\nEND", "O(log n)", "f")
case("floor / div in the argument",
     "FUNCTION f(n)\n IF n <= 1\n  RETURN\n END\n f(floor(n/2))\n f(n DIV 2)\nEND",
     "O(n)", "f")
case("Tower of Hanoi",
     "FUNCTION hanoi(n, a, b, c)\n IF n == 0\n  RETURN\n END\n hanoi(n-1, a, c, b)\n move(a, c)\n hanoi(n-1, b, a, c)\nEND",
     "O(2^n)", "hanoi")
case("merge sort with lo/hi and a helper",
     "FUNCTION merge(A, lo, mid, hi)\n FOR i = lo TO hi\n  x = 1\n END\nEND\nFUNCTION msort(A, lo, hi)\n IF lo >= hi\n  RETURN\n END\n mid = floor((lo + hi) / 2)\n msort(A, lo, mid)\n msort(A, mid + 1, hi)\n merge(A, lo, mid, hi)\nEND",
     "O(n log n)", "msort")
case("recursive binary search (lo/hi)",
     "FUNCTION bs(A, x, lo, hi)\n IF lo > hi\n  RETURN -1\n END\n mid = (lo + hi) / 2\n IF A[mid] == x\n  RETURN mid\n ELSE IF A[mid] < x\n  RETURN bs(A, x, mid + 1, hi)\n ELSE\n  RETURN bs(A, x, lo, mid - 1)\n END\nEND",
     "O(log n)", "bs")
case("recursion with decreasing second parameter",
     "FUNCTION f(a, k)\n IF k <= 0\n  RETURN a\n END\n RETURN f(a, k - 1)\nEND", "O(k)", None)
case("permutations: call inside FOR 1..n -> n!",
     "FUNCTION perm(n)\n IF n <= 1\n  RETURN\n END\n FOR i = 1 TO n\n  perm(n - 1)\n END\nEND",
     "O(n!)", "perm")
case("recursive function called from another function",
     "FUNCTION g(n)\n IF n <= 1\n  RETURN\n END\n g(n/2)\nEND\nFUNCTION h(n)\n FOR i = 1 TO n\n  g(n)\n END\nEND",
     "O(n log n)", "h")
case("top-level code calling a recursive function",
     "FUNCTION g(n)\n IF n <= 1\n  RETURN\n END\n g(n-1)\nEND\ng(n)", "O(n)", "<main program>")

# ---------------------------------------------------- unsupported -> clear error
case("quicksort: data-dependent pivot gives the worst case",
     "FUNCTION qs(A, lo, hi)\n IF lo >= hi\n  RETURN\n END\n p = partition(A, lo, hi)\n qs(A, lo, p - 1)\n qs(A, p + 1, hi)\n WORK(hi - lo)\nEND",
     "O(n^2)", "qs")
case("mutual recursion is reported",
     "FUNCTION a(n)\n IF n <= 0\n  RETURN\n END\n b(n-1)\nEND\nFUNCTION b(n)\n a(n-1)\nEND",
     "ERROR:mutual recursion", "a")
case("non-shrinking recursion is reported",
     "FUNCTION f(n)\n f(n)\nEND", "ERROR:strictly shrinks", "f")
case("T(n)=T(n-1)+T(n/2) mixed is reported",
     "FUNCTION f(n)\n IF n <= 1\n  RETURN\n END\n f(n-1)\n f(n/2)\nEND", "ERROR:mix", "f")


# ------------------------------------------------- examples folder (files)
import os
HERE = os.path.dirname(os.path.abspath(__file__))
FILE_EXPECTED = {
    "graph_bfs.txt": {"BFS": "O(V + E)"},
    "graph_dfs_recursive.txt": {"DFS_VISIT": "O(V + E)", "DFS": "O(V + E)"},
    "graph_dfs_iterative.txt": {"DFS_ITER": "O(V + E)"},
    "graph_dijkstra.txt": {"DIJKSTRA": "O(V log V + E log V)"},
    "graph_prim.txt": {"PRIM": "O(V log V + E log V)"},
    "graph_bellman_ford.txt": {"BELLMAN_FORD": "O(V * E)"},
    "graph_floyd_warshall.txt": {"FLOYD_WARSHALL": "O(V^3)"},
    "graph_kruskal.txt": {"KRUSKAL": "O(E log E + V)"},
    "graph_topological_kahn.txt": {"TOPO_SORT": "O(V + E)"},
    "graph_components.txt": {"EXPLORE": "O(V + E)", "COUNT_COMPONENTS": "O(V + E)"},
    "graph_adjacency_matrix.txt": {"MATRIX_BFS": "O(V^2)"},
    "tree_traversals.txt": {"INORDER": "O(n)", "HEIGHT": "O(n)", "BST_SEARCH": "O(n)",
                            "COUNT_NODES": "O(n)", "LIST_SEARCH": "O(n)"},
    "goto_loops.txt": {"COUNT_UP": "O(n)", "SHRINK": "O(log n)",
                       "NESTED_GOTO": "O(n^2)", "SKIP": "O(n^2)",
                       "DOUBLING": "O(log n)"},
    "nested_repeat_until.txt": {"REPEAT_NEST": "O(n log n)", "REPEAT_WITH_FOR": "O(n)",
                                "REPEAT_GOTO": "O(n^2)", "DO_NEST": "O(n log n)"},
    "recursion_mix.txt": {"MERGE_SORT": "O(n log n)", "FIB": "O(1.618^n)",
                          "POWER": "O(log n)", "SUBSETS": "O(2^n)", "SELECT": "O(n)"},
}
for _file, _expected in FILE_EXPECTED.items():
    _path = os.path.join(HERE, "examples", _file)
    if os.path.exists(_path):
        _code = open(_path, encoding="utf-8").read()
        for _name, _want in _expected.items():
            case(f"{_file}: {_name}", _code, _want, _name)

# ------------------------------------------------- graph / tree / goto probes
case("union-find find: pointer chasing", "FUNCTION FIND(x)\n WHILE parent[x] != x\n  x <- parent[x]\n END WHILE\n RETURN x\nEND", "O(n)", "FIND")
case("heap sift-down: i doubles up to n", "FUNCTION SIFT(A, n)\n i <- 1\n WHILE 2 * i <= n\n  i <- 2 * i\n END WHILE\nEND", "O(log n)", "SIFT")
case("DFS with explicit tuple stack",
     "FUNCTION DFS(G, s)\n PUSH(S, (s, NIL))\n WHILE S is not empty\n  (u, p) <- POP(S)\n  IF NOT visited[u]\n   visited[u] <- TRUE\n   FOR EACH (v, w) IN adj[u]\n    PUSH(S, (v, u))\n   END FOR\n  END IF\n END WHILE\nEND",
     "O(V + E)", "DFS")
case("cycle detection with colours (recursive)",
     "FUNCTION VISIT(u)\n color[u] <- GRAY\n FOR EACH v IN adj[u]\n  IF color[v] = WHITE\n   VISIT(v)\n  ELSE IF color[v] = GRAY\n   cycle <- TRUE\n  END IF\n END FOR\n color[u] <- BLACK\nEND",
     "O(V + E)", "VISIT")
case("bipartite check by BFS",
     "FUNCTION BIP(G, s)\n color[s] <- 0\n ENQUEUE(Q, s)\n WHILE NOT EMPTY(Q)\n  u <- DEQUEUE(Q)\n  FOR EACH v IN adj[u]\n   IF color[v] = NIL\n    color[v] <- 1 - color[u]\n    ENQUEUE(Q, v)\n   ELSE IF color[v] = color[u]\n    RETURN FALSE\n   END IF\n  END FOR\n END WHILE\n RETURN TRUE\nEND",
     "O(V + E)", "BIP")
case("BFS from every unvisited vertex, no function (visited shared)",
     "FOR EACH v IN V\n visited[v] <- FALSE\nEND FOR\nFOR EACH v IN V\n IF NOT visited[v]\n  ENQUEUE(Q, v)\n  visited[v] <- TRUE\n  WHILE Q is not empty\n   u <- DEQUEUE(Q)\n   FOR EACH w IN adj[u]\n    IF NOT visited[w]\n     visited[w] <- TRUE\n     ENQUEUE(Q, w)\n    END IF\n   END FOR\n  END WHILE\n END IF\nEND FOR",
     "O(V + E)")
case("BFS from every vertex with reset (V runs)",
     "FUNCTION ALL(G)\n FOR EACH s IN V\n  FOR EACH v IN V\n   dist[v] <- INF\n  END FOR\n  ENQUEUE(Q, s)\n  WHILE Q is not empty\n   u <- DEQUEUE(Q)\n   FOR EACH w IN adj[u]\n    IF dist[w] = INF\n     dist[w] <- dist[u] + 1\n     ENQUEUE(Q, w)\n    END IF\n   END FOR\n  END WHILE\n END FOR\nEND",
     "O(V^2 + V * E)", "ALL")
case("edge list of tuples", "FOR EACH edge IN E\n (u, v, w) <- edge\n total <- total + w\nEND FOR", "O(E)")
case("vertex loop with neighbour loop is V+E, not V*deg",
     "FOR EACH u IN V\n FOR EACH (v, w) IN adj[u]\n  total <- total + w\n END FOR\nEND FOR", "O(V + E)")
case("tree level order (no visited needed)",
     "FUNCTION LEVEL(root)\n ENQUEUE(Q, root)\n WHILE Q is not empty\n  node <- DEQUEUE(Q)\n  IF node.left != NIL THEN ENQUEUE(Q, node.left)\n  IF node.right != NIL THEN ENQUEUE(Q, node.right)\n END WHILE\nEND",
     "O(n)", "LEVEL")
case("graph recursion without visited check is rejected",
     "FUNCTION WALK(v)\n FOR EACH u IN adj[v]\n  WALK(u)\n END FOR\nEND", "ERROR:visited", "WALK")
case("GOTO out of an inner loop acts like BREAK (j > 5)",
     "FUNCTION F(n)\n i <- 0\n REPEAT\n  FOR j <- 1 TO n\n   IF j > 5 GOTO skip\n   x <- x + 1\n  END FOR\n  skip:\n  i <- i + 1\n UNTIL i >= n\nEND", "O(n)", "F")
case("GOTO restarting a whole scan (unknown count)",
     "FUNCTION G(n)\n start:\n FOR i <- 1 TO n\n  IF A[i] < 0 GOTO start\n END FOR\nEND", "O(n^2)", "G")
case("GOTO loop whose exit is RETURN",
     "FUNCTION H(n)\n i <- 1\n top:\n IF i > n THEN RETURN\n j <- 1\n WHILE j < n\n  j <- j * 2\n END WHILE\n i <- i + 1\n GOTO top\nEND", "O(n log n)", "H")
case("two GOTO loops in sequence",
     "FUNCTION K(n)\n a:\n i <- i + 1\n IF i < n GOTO a\n b:\n j <- j + 1\n IF j < n GOTO b\nEND", "O(n)", "K")
case("code after an unconditional GOTO is dead",
     "FUNCTION D(n)\n GOTO fin\n FOR i <- 1 TO n\n  FOR j <- 1 TO n\n   x <- 1\n  END FOR\n END FOR\n fin:\n RETURN\nEND", "O(1)", "D")
case("main program with GOTO loop",
     "i <- 0\nloop:\nIF i >= n GOTO out\ni <- i + 1\nGOTO loop\nout:", "O(n)")
case("quicksort with PARTITION helper (worst case)",
     "FUNCTION QS(A, lo, hi)\n IF lo < hi\n  p <- PARTITION(A, lo, hi)\n  QS(A, lo, p - 1)\n  QS(A, p + 1, hi)\n END IF\nEND\nFUNCTION PARTITION(A, lo, hi)\n FOR j <- lo TO hi - 1\n  x <- x + 1\n END FOR\nEND",
     "O(n^2)", "QS")
case("recursion counter growing to a bound",
     "FUNCTION F(i, n)\n IF i > n THEN RETURN\n F(i + 1, n)\n F(i + 1, n)\nEND", "O(2^n)", "F")
case("heap operations cost log V",
     "FUNCTION F(G)\n FOR EACH v IN V\n  INSERT(PQ, v)\n END FOR\nEND", "O(V log V)", "F")

# --------------------------------------------- textbook algorithms & extensions
case("CLRS insertion sort (indentation)",
     "INSERTION-SORT(A)\n    for j = 2 to A.length\n        key = A[j]\n        i = j - 1\n        while i > 0 and A[i] > key\n            A[i + 1] = A[i]\n            i = i - 1\n        A[i + 1] = key",
     "O(n^2)", "INSERTION_SORT")

case("CLRS merge sort (indentation)",
     "MERGE-SORT(A, p, r)\n    if p < r\n        q = floor((p + r) / 2)\n        MERGE-SORT(A, p, q)\n        MERGE-SORT(A, q + 1, r)\n        WORK(r - p)",
     "O(n log n)", "MERGE_SORT")

case("C-style nested for with braces",
     "for (int i = 0; i < n; i++) {\n    for (int j = 0; j < n; j++) {\n        x++;\n    }\n}",
     "O(n^2)")

case("Python def with range",
     "def f(n):\n    for i in range(n):\n        x = x + 1",
     "O(n)", "f")

case("Line-numbered pseudocode",
     "1. FOR i = 1 TO n\n2.   x = x + 1\n3. END",
     "O(n)")

case("CLRS triangle comment and math unicode",
     "FOR i <- 1 TO ⌊n / 2⌋ ▷ iterate half\n    x[i, 1] <- 1\nEND FOR",
     "O(n)")

case("Monotonic stack next greater element",
     "FUNCTION next_greater(A, n)\n    FOR i = 1 TO n\n        WHILE NOT EMPTY(S) AND TOP(S) < A[i]\n            POP(S)\n        END WHILE\n        PUSH(S, A[i])\n    END FOR\nEND",
     "O(n)", "next_greater")

case("Two-pointer sliding window",
     "l <- 1\nFOR r <- 1 TO n\n    WHILE sum > k AND l < r\n        sum <- sum - A[l]\n        l <- l + 1\n    END WHILE\nEND FOR",
     "O(n)")

case("Dijkstra with RELAX",
     "FUNCTION DIJKSTRA(G, w, s)\n    INITIALIZE-SINGLE-SOURCE(G, s)\n    PQ <- G.V\n    WHILE PQ is not empty\n        u <- EXTRACT-MIN(PQ)\n        FOR EACH v IN G.Adj[u]\n            RELAX(u, v, w)\n        END FOR\n    END WHILE\nEND",
     "O(V log V + E log V)", "DIJKSTRA")

case("Bellman-Ford with RELAX",
     "FUNCTION BELLMAN_FORD(G, w, s)\n    INITIALIZE-SINGLE-SOURCE(G, s)\n    FOR i <- 1 TO V - 1\n        FOR EACH (u, v) IN E\n            RELAX(u, v, w)\n        END FOR\n    END FOR\nEND",
     "O(V * E)", "BELLMAN_FORD")

case("CLRS Tree Insert (pointer chase in IF)",
     "FUNCTION TREE_INSERT(T, z)\n    x <- T.root\n    WHILE x != NIL\n        y <- x\n        IF z.key < x.key\n            x <- x.left\n        ELSE\n            x <- x.right\n        END IF\n    END WHILE\nEND",
     "O(n)", "TREE_INSERT")

case("Master Theorem Case 1 (4T(n/2)+n -> n^2)",
     "FUNCTION f(n)\n    IF n <= 1\n        RETURN\n    END\n    f(n/2)\n    f(n/2)\n    f(n/2)\n    f(n/2)\n    WORK(n)\nEND",
     "O(n^2)", "f")

case("Master Theorem Case 2 with log (2T(n/2)+n log n -> n log^2 n)",
     "FUNCTION f(n)\n    IF n <= 1\n        RETURN\n    END\n    f(n/2)\n    f(n/2)\n    WORK(n * log(n))\nEND",
     "O(n log^2 n)", "f")

case("Extended Master Theorem Case 2b (2T(n/2)+n/log n -> n log(log n))",
     "FUNCTION f(n)\n    IF n <= 2\n        RETURN\n    END\n    f(n/2)\n    f(n/2)\n    WORK(n / log(n))\nEND",
     "O(n log(log n))", "f")

case("Master Theorem Case 3 (2T(n/2)+n^2 -> n^2)",
     "FUNCTION f(n)\n    IF n <= 1\n        RETURN\n    END\n    f(n/2)\n    f(n/2)\n    WORK(n^2)\nEND",
     "O(n^2)", "f")

case("Akra-Bazzi unequal subproblems (T(n/3)+T(2n/3)+n -> n log n)",
     "FUNCTION f(n)\n    IF n <= 1\n        RETURN\n    END\n    f(n/3)\n    f(2*n/3)\n    WORK(n)\nEND",
     "O(n log n)", "f")

case("Akra-Bazzi unequal subproblems (T(n/2)+T(n/4)+n -> n)",
     "FUNCTION f(n)\n    IF n <= 1\n        RETURN\n    END\n    f(n/2)\n    f(n/4)\n    WORK(n)\nEND",
     "O(n)", "f")

case("Recurrence with sqrt(n) (2T(sqrt(n)) + log n -> log n log(log n))",
     "FUNCTION f(n)\n    IF n <= 2\n        RETURN\n    END\n    f(sqrt(n))\n    f(sqrt(n))\n    WORK(log(n))\nEND",
     "O(log n log(log n))", "f")

case("Recurrence with sqrt(n) (T(sqrt(n)) + 1 -> log(log n))",
     "FUNCTION f(n)\n    IF n <= 2\n        RETURN\n    END\n    f(sqrt(n))\nEND",
     "O(log(log n))", "f")

case("Recursive Euclid GCD",
     "FUNCTION gcd(a, b)\n    IF b == 0\n        RETURN a\n    END\n    RETURN gcd(b, a % b)\nEND",
     "O(log a)", "gcd")

SYNTAX_ERRORS = [
    ("missing END for FOR", "FOR i = 1 TO n\n x = 1", "missing its END"),
    ("missing END for IF", "IF x > 0\n y = 1", "missing its END"),
    ("wrong END keyword", "FOR i = 1 TO n\n x = 1\nEND WHILE", "expected END FOR"),
    ("stray END", "x = 1\nEND", "unexpected"),
    ("REPEAT without UNTIL", "REPEAT\n x = 1", "UNTIL"),
    ("DO without END DO WHILE", "DO\n x = 1\nEND", "END DO WHILE"),
    ("bad FOR header", "FOR i TO n\n x = 1\nEND", "invalid FOR"),
]

PARSE_SHAPES = [
    ("node types survive parsing",
     "FUNCTION t(n)\n FOR i <- 1 TO n\n  IF i > 5\n   BREAK\n  OTHERWISE\n   CONTINUE\n  END IF\n END FOR\n RETURN n\nEND FUNCTION\nDONE",
     {"FUNCTION", "FOR", "IF", "BREAK", "CONTINUE", "RETURN"}),
    ("repeat/do-while node types",
     "REPEAT\n n = n - 1\nUNTIL n <= 1\nDO\n n = n / 2\nEND DO WHILE n > 1",
     {"REPEAT_UNTIL", "DO_WHILE", "OPERATION"}),
    ("goto/label node types", "GOTO done\ndone:\nRETURN", {"GOTO", "LABEL", "RETURN"}),
    ("call statement", "CALL work(n, 2)\nf(n-1)", {"FUNCTION_CALL"}),
    ("assignment with call is an OPERATION", "x = f(n - 1) + 1", {"OPERATION"}),
]


def node_types(nodes):
    found = set()
    for node in nodes:
        found.add(node["type"])
        for key in ("body", "true_body", "false_body"):
            found |= node_types(node.get(key, []))
    return found


def run():
    passed = failed = 0

    def report(ok, title, detail=""):
        nonlocal passed, failed
        if ok:
            passed += 1
        else:
            failed += 1
            print(f"FAIL  {title}\n      {detail}")

    for title, code, expected, name in CASES:
        try:
            result = result_for(code, name)
            actual = result.text
            if expected.startswith("ERROR:"):
                needle = expected[6:]
                ok = result.complexity is None and needle in (result.error or "")
                report(ok, title, f"expected an error containing {needle!r}, got: {actual}")
            else:
                report(actual == expected, title, f"expected {expected}, got {actual}")
        except Exception as exc:
            report(False, title, f"raised {type(exc).__name__}: {exc}")
            traceback.print_exc(limit=2)

    for title, code, needle in SYNTAX_ERRORS:
        try:
            Parser(code).parse()
            report(False, f"syntax: {title}", "no SyntaxError raised")
        except SyntaxError as exc:
            report(needle.lower() in str(exc).lower(), f"syntax: {title}",
                   f"message {str(exc)!r} lacks {needle!r}")

    for title, code, expected_types in PARSE_SHAPES:
        try:
            found = node_types(Parser(code).parse())
            report(expected_types <= found, f"parse: {title}",
                   f"missing {expected_types - found}")
        except Exception as exc:
            report(False, f"parse: {title}", f"{type(exc).__name__}: {exc}")

    total = passed + failed
    print(f"\nRESULT: {passed} passed, {failed} failed, {total} total")
    return failed == 0


if __name__ == "__main__":
    sys.exit(0 if run() else 1)
