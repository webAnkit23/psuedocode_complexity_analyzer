"""
expressions.py
--------------
Small utilities shared by the analyzers:

* a tokenizer and parser for arithmetic expressions (n/2, n*n, 2^n, log(n) ...)
* a parser for loop conditions (a < b AND NOT c ...)
* linear forms (used to understand arguments such as  mid + 1  or  (lo+hi)/2)
* assignment parsing (x <- x * 2, x += 1, x++ ...)
* extraction of function calls from statement text
"""

import re
from fractions import Fraction
from functools import lru_cache
from typing import NamedTuple, Optional

CONST = "#"  # key used for the constant term of a linear form


class ExprError(ValueError):
    """Raised when text cannot be understood as an expression."""


# ----------------------------------------------------------------------
# Tokenizer
# ----------------------------------------------------------------------

_TOKEN_RE = re.compile(
    r"""\s*(?:
        (?P<num>\d+\.\d+|\d+|\.\d+)
      | (?P<id>[A-Za-z_]\w*)
      | (?P<op>\*\*|//|<=|>=|==|!=|<>|<-|:=|&&|\|\||<<|>>
              |[-+*/%^()\[\],<>=!|.]|[≤≥≠←])
    )""",
    re.VERBOSE,
)

_UNICODE_OPS = {"≤": "<=", "≥": ">=", "≠": "!=", "←": "<-", "<>": "!="}
_WORD_OPS = {"and", "or", "not", "mod", "div"}


def strip_strings(text):
    """Blank out quoted strings so their contents are never analysed."""
    return re.sub(
        r"'[^']*'|\"[^\"]*\"", lambda m: " " * len(m.group()), text
    )


def tokenize(text):
    text = strip_strings(text).strip()
    tokens = []
    pos = 0
    while pos < len(text):
        match = _TOKEN_RE.match(text, pos)
        if not match or match.end() == pos:
            if text[pos:].strip() == "":
                break
            raise ExprError(f"Cannot read expression: {text!r}")
        pos = match.end()
        if match.group("num") is not None:
            tokens.append(("num", match.group("num")))
        elif match.group("id") is not None:
            word = match.group("id")
            if word.lower() in _WORD_OPS:
                tokens.append(("op", word.lower()))
            else:
                tokens.append(("id", word))
        else:
            op = match.group("op")
            tokens.append(("op", _UNICODE_OPS.get(op, op)))
    return tokens


# ----------------------------------------------------------------------
# Expression parser   (AST = nested tuples)
#   ('num', Fraction) ('var', name) ('neg', x) ('bin', op, l, r)
#   ('pow', base, exp) ('call', name, [args]) ('index', base, idx)
#   ('fact', x) ('unk',)
# ----------------------------------------------------------------------

_CMP_OPS = {"<", "<=", ">", ">=", "==", "=", "!="}
_LEN_ATTRS = {"length", "size", "count", "len", "heap_size", "heapsize"}


class _Parser:
    def __init__(self, tokens):
        self.tokens = tokens
        self.pos = 0

    def peek(self):
        if self.pos < len(self.tokens):
            return self.tokens[self.pos]
        return (None, None)

    def accept(self, *ops):
        kind, value = self.peek()
        if kind == "op" and value in ops:
            self.pos += 1
            return value
        return None

    def expect(self, op):
        if not self.accept(op):
            raise ExprError(f"Expected {op!r}")

    def at_end(self):
        return self.pos >= len(self.tokens)

    # ---- arithmetic ----
    def expression(self):
        left = self.term()
        while True:
            op = self.accept("+", "-")
            if not op:
                return left
            left = ("bin", op, left, self.term())

    def term(self):
        left = self.unary()
        while True:
            op = self.accept("*", "/", "//", "%", "mod", "div", ">>", "<<")
            if not op:
                return left
            right = self.unary()
            if op in (">>", "<<"):
                if right[0] != "num" or right[1].denominator != 1:
                    raise ExprError("Shift amount must be a number")
                factor = ("num", Fraction(2) ** int(right[1]))
                left = ("bin", "/" if op == ">>" else "*", left, factor)
                continue
            op = {"//": "/", "div": "/", "mod": "%"}.get(op, op)
            left = ("bin", op, left, right)

    def unary(self):
        if self.accept("-"):
            return ("neg", self.unary())
        if self.accept("+"):
            return self.unary()
        return self.power()

    def power(self):
        base = self.postfix()
        if self.accept("^", "**"):
            return ("pow", base, self.unary())
        return base

    def postfix(self):
        node = self.atom()
        while True:
            if self.accept("["):
                index = self.expression()
                while self.accept(","):
                    index = self.expression()
                self.expect("]")
                node = ("index", node, index)
            elif self.accept("."):
                kind, value = self.peek()
                if kind != "id":
                    raise ExprError("Expected attribute name")
                self.pos += 1
                if value.lower() in _LEN_ATTRS:
                    node = ("call", "len", [node])
                else:
                    node = ("unk",)
            elif self.accept("!"):
                node = ("fact", node)
            else:
                return node

    def atom(self):
        kind, value = self.peek()
        if kind == "num":
            self.pos += 1
            return ("num", Fraction(value))
        if kind == "id":
            self.pos += 1
            if self.accept("("):
                args = []
                if not self.accept(")"):
                    while True:
                        args.append(self.expression())
                        if self.accept(")"):
                            break
                        self.expect(",")
                return ("call", value, args)
            return ("var", value)
        if self.accept("("):
            inner = self.expression()
            self.expect(")")
            return inner
        if self.accept("|"):
            inner = self.expression()
            self.expect("|")
            return ("call", "len", [inner])
        raise ExprError("Unexpected token in expression")

    # ---- conditions ----
    def cond_or(self):
        items = [self.cond_and()]
        while self.accept("or", "||"):
            items.append(self.cond_and())
        return items[0] if len(items) == 1 else ("or", items)

    def cond_and(self):
        items = [self.cond_not()]
        while self.accept("and", "&&"):
            items.append(self.cond_not())
        return items[0] if len(items) == 1 else ("and", items)

    def cond_not(self):
        if self.accept("not", "!"):
            return ("not", self.cond_not())
        kind, value = self.peek()
        if kind == "op" and value == "(":
            saved = self.pos
            try:
                self.pos += 1
                inner = self.cond_or()
                self.expect(")")
                nxt_kind, nxt_value = self.peek()
                if nxt_kind is None or (
                    nxt_kind == "op" and nxt_value in ("and", "or", "&&", "||", ")")
                ):
                    return inner
            except ExprError:
                pass
            self.pos = saved
        return self.cond_cmp()

    def cond_cmp(self):
        left = self.expression()
        op = self.accept(*_CMP_OPS)
        if op:
            if op == "=":
                op = "=="
            return ("cmp", op, left, self.expression())
        return ("truth", left)


@lru_cache(maxsize=4096)
def parse_expr(text):
    parser = _Parser(tokenize(text))
    tree = parser.expression()
    if not parser.at_end():
        raise ExprError(f"Cannot read expression: {text!r}")
    return tree


@lru_cache(maxsize=1024)
def parse_condition(text):
    """Return a condition tree. Unreadable conditions become ('opaque', text)."""
    try:
        parser = _Parser(tokenize(text))
        tree = parser.cond_or()
        if not parser.at_end():
            raise ExprError("trailing tokens")
        return tree
    except ExprError:
        return ("opaque", text)


_FLIP = {"<": ">=", "<=": ">", ">": "<=", ">=": "<", "==": "!=", "!=": "=="}


def negate_condition(tree):
    kind = tree[0]
    if kind == "cmp":
        return ("cmp", _FLIP[tree[1]], tree[2], tree[3])
    if kind == "and":
        return ("or", [negate_condition(t) for t in tree[1]])
    if kind == "or":
        return ("and", [negate_condition(t) for t in tree[1]])
    if kind == "not":
        return tree[1]
    return ("opaque", "NOT (...)")


# ----------------------------------------------------------------------
# Numeric / linear helpers
# ----------------------------------------------------------------------

_ROUNDING_CALLS = {"floor", "ceil", "ceiling", "int", "trunc", "round"}


def numeric_value(tree):
    """Exact value of a constant expression, or None."""
    kind = tree[0]
    if kind == "num":
        return tree[1]
    if kind == "neg":
        value = numeric_value(tree[1])
        return None if value is None else -value
    if kind == "bin":
        left, right = numeric_value(tree[2]), numeric_value(tree[3])
        if left is None or right is None:
            return None
        op = tree[1]
        if op == "+":
            return left + right
        if op == "-":
            return left - right
        if op == "*":
            return left * right
        if op == "/":
            return left / right if right != 0 else None
        return None
    if kind == "pow":
        base, exp = numeric_value(tree[1]), numeric_value(tree[2])
        if base is None or exp is None or exp.denominator != 1 or abs(exp) > 64:
            return None
        return base ** int(exp)
    if kind == "call" and tree[1].lower() in _ROUNDING_CALLS and len(tree[2]) == 1:
        return numeric_value(tree[2][0])
    return None


def linear_form(tree, defs=None, _stack=()):
    """
    Express a tree as {var: coefficient, CONST: constant}, or return None if it
    is not linear. 'defs' maps local variable names to trees so that, e.g.,
    mid = (lo + hi) / 2 can be expanded.
    """
    kind = tree[0]
    if kind == "num":
        return {CONST: tree[1]}
    if kind == "var":
        name = tree[1]
        if defs and name in defs and name not in _stack:
            return linear_form(defs[name], defs, _stack + (name,))
        return {name: Fraction(1)}
    if kind == "neg":
        inner = linear_form(tree[1], defs, _stack)
        return None if inner is None else {k: -v for k, v in inner.items()}
    if kind == "bin":
        op = tree[1]
        left = linear_form(tree[2], defs, _stack)
        right = linear_form(tree[3], defs, _stack)
        if left is None or right is None:
            return None
        if op in "+-":
            sign = 1 if op == "+" else -1
            out = dict(left)
            for key, value in right.items():
                out[key] = out.get(key, 0) + sign * value
            return {k: v for k, v in out.items() if v != 0 or k == CONST}
        if op == "*":
            if _is_constant(left):
                factor, other = left.get(CONST, Fraction(0)), right
            elif _is_constant(right):
                factor, other = right.get(CONST, Fraction(0)), left
            else:
                return None
            return {k: v * factor for k, v in other.items()}
        if op == "/":
            if not _is_constant(right) or right.get(CONST, 0) == 0:
                return None
            return {k: v / right[CONST] for k, v in left.items()}
        return None
    if kind == "call" and tree[1].lower() in _ROUNDING_CALLS and len(tree[2]) == 1:
        return linear_form(tree[2][0], defs, _stack)
    if kind == "pow":
        exp = numeric_value(tree[2])
        if exp == 1:
            return linear_form(tree[1], defs, _stack)
    return None


def _is_constant(form):
    return all(key == CONST for key, value in form.items() if value != 0)


def variables_of(form):
    return {k: v for k, v in form.items() if k != CONST and v != 0}


# ----------------------------------------------------------------------
# Assignments
# ----------------------------------------------------------------------

class Assignment(NamedTuple):
    targets: tuple
    op: str      # '=', '+=', '-=', '*=', '/=', '//=', '%=', '**='
    rhs: str


_ASSIGN_RE = re.compile(
    r"^\s*\(?\s*([A-Za-z_]\w*(?:\s*,\s*[A-Za-z_]\w*)*)\s*\)?\s*"
    r"(<-|←|:=|\*\*=|//=|\+=|-=|\*=|/=|%=|=(?!=))\s*(.+?)\s*;?\s*$"
)
_INCDEC_RE = re.compile(
    r"^\s*(?:(\+\+|--)\s*([A-Za-z_]\w*)|([A-Za-z_]\w*)\s*(\+\+|--))\s*;?\s*$"
)


def parse_assignment(code):
    match = _INCDEC_RE.match(code)
    if match:
        name = match.group(2) or match.group(3)
        sign = match.group(1) or match.group(4)
        return Assignment((name,), "+=" if sign == "++" else "-=", "1")
    match = _ASSIGN_RE.match(code)
    if not match:
        return None
    targets = tuple(t.strip() for t in match.group(1).split(","))
    op = match.group(2)
    if op in ("<-", "←", ":="):
        op = "="
    return Assignment(targets, op, match.group(3))


def new_value_tree(assignment):
    """Tree describing the value stored by an assignment (None if unreadable)."""
    if len(assignment.targets) != 1:
        return None
    try:
        rhs = parse_expr(assignment.rhs)
    except ExprError:
        return None
    target = ("var", assignment.targets[0])
    op = assignment.op
    if op == "=":
        return rhs
    symbol = {"+=": "+", "-=": "-", "*=": "*", "/=": "/", "//=": "/", "%=": "%"}
    if op in symbol:
        return ("bin", symbol[op], target, rhs)
    if op == "**=":
        return ("pow", target, rhs)
    return None


# ----------------------------------------------------------------------
# Calls
# ----------------------------------------------------------------------

_NOT_CALLS = {
    "if", "while", "for", "return", "until", "and", "or", "not", "then",
    "else", "do", "repeat", "function", "to", "downto", "step", "in", "goto",
}


def split_arguments(text):
    """Split 'a, f(b, c), d' into ['a', 'f(b, c)', 'd']."""
    if not text.strip():
        return []
    parts, current, depth, quote = [], [], 0, None
    for char in text:
        if quote is not None:
            current.append(char)
            if char == quote:
                quote = None
            continue
        if char in ("'", '"'):
            quote = char
            current.append(char)
        elif char in "([":
            depth += 1
            current.append(char)
        elif char in ")]":
            depth -= 1
            current.append(char)
        elif char == "," and depth == 0:
            parts.append("".join(current).strip())
            current = []
        else:
            current.append(char)
    parts.append("".join(current).strip())
    return [part for part in parts if part]


_CALL_FIND = re.compile(
    r"(?:(?P<recv>[A-Za-z_]\w*)\s*\.\s*)?\b"
    r"(?P<name>[A-Z][A-Z0-9_]*(?:-[A-Z][A-Z0-9_]*)+|[A-Za-z_]\w*)\s*\("
)


def norm_name(name):
    """EXTRACT-MIN -> EXTRACT_MIN (hyphenated pseudocode names)."""
    return name.replace("-", "_")


def extract_calls_full(text):
    """All calls as (name, args, receiver); nested calls included."""
    clean = strip_strings(text or "")
    calls = []
    for match in _CALL_FIND.finditer(clean):
        name = match.group("name")
        if name.lower() in _NOT_CALLS:
            continue
        depth, end = 0, None
        for index in range(match.end() - 1, len(clean)):
            if clean[index] == "(":
                depth += 1
            elif clean[index] == ")":
                depth -= 1
                if depth == 0:
                    end = index
                    break
        if end is None:
            continue
        calls.append((norm_name(name),
                      split_arguments(clean[match.end():end]),
                      match.group("recv")))
    return calls


def extract_calls(text):
    """All calls  name(arg, ...)  in the text, including nested ones."""
    return [(n, a) for n, a, _ in extract_calls_full(text)]


# ----------------------------------------------------------------------
# Graph / tree vocabulary
# ----------------------------------------------------------------------

_ADJ_INDEXED = re.compile(
    r"^(?:(?:g|graph|self)\.)?(?:adj\w*|neighbou?rs?\w*|successors?\w*|succ\w*"
    r"|out(?:going)?_?(?:edges|neighbou?rs|nodes|adj\w*)?|incident\w*"
    r"|edges_?(?:of|from)\w*|edges|nbrs?|graph|g)[\[(]"
)
_ADJ_SUFFIX = re.compile(
    r"\.(?:adj\w*|adjacent|neighbou?rs?|successors?|succ|incident\w*)(?:\(\))?$"
)
_CHILDREN = re.compile(r"(?:^|\.)(?:children|kids|child\w*|subtrees)(?:[\[(]|$|\.)")


def classify_collection(text):
    """
    'adj' (neighbours of one vertex), 'children' (children of one tree node),
    'vertices', 'edges' (the whole graph's lists) or None.
    """
    low = re.sub(r"\s+", "", text or "").lower()
    if not low:
        return None
    if _CHILDREN.search(low):
        return "children"
    if _ADJ_INDEXED.match(low) or _ADJ_SUFFIX.search(low):
        return "adj"
    if re.search(r"\w\.edges(?:\(\))?$", low) and not low.startswith(("g.", "graph.")):
        return "adj"
    if re.search(r"(?:neighbors?|neighbours?|adjacent)of\w+", low):
        return "adj"
    base = re.sub(r"^(?:g|graph)\.", "", low).strip("|")
    if base in ("adj", "adjacent", "adjacency", "neighbors", "neighbours"):
        return "adj"
    if base in ("e", "e(g)", "e[g]", "edges", "edge_set") or re.fullmatch(r"(?:g\.)?e(?:\[\w+\]|\(\w+\))?", base) or re.fullmatch(r"\w*edge\w*", base):
        return "edges"
    if base in ("v", "v(g)", "v[g]", "vertices", "vertex_set", "nodes", "node_set") or re.fullmatch(r"(?:g\.)?v(?:\[\w+\]|\(\w+\))?", base) or re.fullmatch(r"\w*(?:vert|node)\w*", base):
        return "vertices"
    return None


def classify_tree(tree):
    """classify_collection for an expression tree such as adj[v] or neighbors(v)."""
    kind = tree[0]
    if kind == "var":
        return classify_collection(tree[1])
    if kind == "index" and tree[1][0] == "var":
        return classify_collection(tree[1][1] + "[x]")
    if kind == "call":
        if tree[1].lower() in ("len", "size", "length", "count") and tree[2]:
            return classify_tree(tree[2][0])
        return classify_collection(tree[1] + "(x)")
    return None


_GUARD_RE = re.compile(
    r"visited|seen|marked?|colou?r|discovered|explored|processed|state|status"
    r"|dist(?:ance)?|\bkey\b|in_?deg(?:ree)?|settled|closed|finali[sz]ed|reached"
    r"|\bused\b|\bvis\b|parent|pred(?:ecessor)?|\bdone\b|\bin_?(?:queue|set|stack)\b",
    re.I,
)


def has_guard_text(text):
    return bool(_GUARD_RE.search(text or ""))


_WL = [
    # (regex, name group, means "queue is NOT empty")
    (r"(?:\bNOT\s+|!\s*)(?:IS[_\s]*)?EMPTY\s*\(\s*(\w+)\s*\)", True),
    (r"(?:\bNOT\s+|!\s*)(\w+)\s*\.\s*(?:is_?empty|empty)\s*\(\s*\)", True),
    (r"\bNOT\s+EMPTY\s+(\w+)", True),
    (r"(\w+)\s+(?:IS\s+)?(?:NOT\s+EMPTY|NON[-\s]?EMPTY)\b", True),
    (r"(\w+)\s*(?:≠|!=|<>)\s*(?:∅|\{\s*\}|\[\s*\]|EMPTY\b)", True),
    (r"\|\s*(\w+)\s*\|\s*>\s*0", True),
    (r"\b(?:len|size|length|count)\s*\(\s*(\w+)\s*\)\s*(?:>|!=|<>|≠)\s*0", True),
    (r"(\w+)\s*\.\s*(?:size|length|len|count)\s*(?:\(\s*\))?\s*(?:>|!=)\s*0", True),
    (r"\bEMPTY\s*\(\s*(\w+)\s*\)", False),
    (r"(\w+)\s+IS\s+EMPTY\b", False),
    (r"(\w+)\s*(?:=|==)\s*(?:∅|\{\s*\}|\[\s*\]|EMPTY\b)", False),
    (r"(\w+)\s*\.\s*(?:is_?empty|empty)\s*\(\s*\)", False),
    (r"\|\s*(\w+)\s*\|\s*(?:=|==)\s*0", False),
    (r"\b(?:len|size|length|count)\s*\(\s*(\w+)\s*\)\s*(?:=|==)\s*0", False),
]


def worklist_condition(text):
    """
    Recognise 'queue is (not) empty' tests. Returns (name, nonempty) where
    nonempty is True when the text says the queue is NOT empty.
    """
    for pattern, nonempty in _WL:
        match = re.search(pattern, text or "", re.IGNORECASE)
        if match and match.group(1).upper() not in ("IS", "NOT"):
            return match.group(1), nonempty
    return None


# ----------------------------------------------------------------------
# AST walking helpers
# ----------------------------------------------------------------------

def child_blocks(node):
    kind = node.get("type")
    if kind == "IF":
        return [node.get("true_body", []), node.get("false_body", [])]
    if kind in ("FUNCTION", "FOR", "WHILE", "REPEAT_UNTIL", "DO_WHILE"):
        return [node.get("body", [])]
    return []


def walk(nodes):
    for node in nodes:
        yield node
        for block in child_blocks(node):
            yield from walk(block)


def node_texts(node):
    """Statement text(s) belonging directly to a node (not its children)."""
    kind = node.get("type")
    if kind == "OPERATION":
        return [node.get("code", "")]
    if kind == "RETURN":
        return [node.get("value") or ""]
    if kind == "FUNCTION_CALL":
        return [f"{node['name']}({', '.join(node.get('arguments', []))})"]
    if kind == "IF":
        return [node.get("condition", "")]
    if kind in ("WHILE", "REPEAT_UNTIL", "DO_WHILE"):
        return [node.get("condition", "")]
    if kind == "FOR":
        return [str(node.get(k) or "") for k in ("start", "end", "step", "collection")]
    return []


def assigned_variables(nodes):
    """Names assigned anywhere inside the given nodes (including FOR variables)."""
    names = set()
    for node in walk(nodes):
        kind = node.get("type")
        if kind == "OPERATION":
            assignment = parse_assignment(node.get("code", ""))
            if assignment:
                names.update(assignment.targets)
        elif kind == "FOR" and node.get("variable"):
            names.add(node["variable"])
    return names


RANGE_NAME_PAIRS = [
    ("lo", "hi"), ("low", "high"), ("l", "r"), ("left", "right"),
    ("start", "end"), ("first", "last"), ("begin", "end"), ("p", "r"),
    ("s", "e"), ("from", "to"), ("lower", "upper"),
]


def find_range_pair(params):
    """Return (lo, hi) if two parameters look like the bounds of a range."""
    lowered = {p.lower(): p for p in params}
    for lo, hi in RANGE_NAME_PAIRS:
        if lo in lowered and hi in lowered:
            return lowered[lo], lowered[hi]
    return None
