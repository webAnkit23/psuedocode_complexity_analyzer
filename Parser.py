"""
Parser.py
---------
Parser for algorithm pseudocode. Produces an AST made of plain dictionaries.

Supported statements (keywords are case-insensitive)
    FUNCTION name(a, b) ... END [FUNCTION]        (also PROCEDURE / ALGORITHM)
    FOR i = a TO b [STEP s] [DO] ... END [FOR]    (also  <-  :=  and DOWNTO, NEXT i)
    FOR EACH x IN collection ... END FOR
    WHILE cond [DO] ... END [WHILE]
    REPEAT ... UNTIL cond
    DO ... END DO WHILE cond
    IF cond [THEN] ... [ELSE IF cond ...] [ELSE ...] END [IF]
    IF cond THEN statement                        (one-line form, no END)
    RETURN [value], BREAK, CONTINUE, GOTO label, label:
    f(args)  /  CALL f(args)                      (function-call statement)
    anything else                                 (assignment etc. -> OPERATION)

Comments start with  //  or  #  and run to the end of the line.
"""

import re

from expressions import split_arguments

_FUNC_RE = re.compile(
    r"^(?:FUNCTION|PROCEDURE|ALGORITHM|DEF)\s+([A-Za-z_][\w-]*)\s*"
    r"(?:\((.*)\))?\s*(?:RETURNS\b.*|->.*|:)?\s*$",
    re.IGNORECASE,
)
_FOR_RE = re.compile(
    r"^FOR\s+(\w+)\s*(?:<-|←|:=|=)\s*(.+?)\s+(TO|DOWNTO)\s+(.+?)"
    r"(?:\s+STEP\s+(.+?))?(?:\s+DO)?\s*:?\s*$",
    re.IGNORECASE,
)
_FOREACH_RE = re.compile(
    r"^FOR\s+(?:EACH\s+|ALL\s+)?(?:(?:VERTEX|NODE|EDGE|NEIGHBOU?R|ITEM|ELEMENT|PAIR)\s+)?"
    r"(\w+|\([^)]*\))\s+IN\s+(.+?)(?:\s+DO)?\s*:?\s*$",
    re.IGNORECASE,
)
_WHILE_RE = re.compile(r"^WHILE\s+(.+?)(?:\s+DO)?\s*:?\s*$", re.IGNORECASE)
_IF_THEN_RE = re.compile(r"^IF\s+(.+?)\s+THEN\b\s*(.*)$", re.IGNORECASE)
_IF_JUMP_RE = re.compile(
    r"^IF\s+(.+?)\s+((?:GO\s*TO|JUMP)\s+[A-Za-z_]\w*|RETURN\b.*|BREAK|CONTINUE)\s*$",
    re.IGNORECASE,
)
_IF_RE = re.compile(r"^IF\s+(.+?)\s*:?\s*$", re.IGNORECASE)
_ELSEIF_RE = re.compile(
    r"^(?:ELSE\s*IF|ELIF|OTHERWISE\s+IF)\s+(.+?)(?:\s+THEN)?\s*:?\s*$",
    re.IGNORECASE,
)
_ELSE_RE = re.compile(r"^(?:ELSE|OTHERWISE)\s*:?\s*$", re.IGNORECASE)
_UNTIL_RE = re.compile(r"^UNTIL\s+(.+?)\s*$", re.IGNORECASE)
_DOWHILE_END_RE = re.compile(
    r"^(?:END\s*DO|ENDDO|LOOP)\s+WHILE\s+(.+?)\s*$", re.IGNORECASE
)
_END_RE = re.compile(
    r"^(?:(END)\s*(IF|FOR|WHILE|FUNCTION|PROCEDURE|ALGORITHM)?"
    r"|(ENDIF|ENDFOR|ENDWHILE|ENDFUNCTION|ENDPROCEDURE)"
    r"|(NEXT)(?:\s+\w+)?)\s*$",
    re.IGNORECASE,
)
_GOTO_RE = re.compile(r"^(?:GO\s*TO|JUMP)\s+([A-Za-z_]\w*)\s*$", re.IGNORECASE)
_LABEL_COLON_RE = re.compile(r"^([A-Za-z_]\w*):$")
_CALL_RE = re.compile(
    r"^(?:CALL\s+)?((?:[A-Z][A-Z0-9_]*(?:-[A-Z][A-Z0-9_]*)+)|[A-Za-z_]\w*)\s*\((.*)\)\s*$",
    re.IGNORECASE,
)

_KEYWORD_LABELS = {"else", "otherwise", "repeat", "do", "then", "begin"}

_C_FOR_RE = re.compile(
    r"^\s*FOR\s*\(\s*(?:(?:INT|LET|VAR)\s+)?(\w+)\s*=\s*(.+?)\s*;\s*\1\s*(<=|>=|<|>|!=)\s*(.+?)\s*;\s*(.+?)\s*\)\s*\{?\s*$",
    re.IGNORECASE,
)
_C_FOREACH_RE = re.compile(
    r"^\s*FOR\s*\(\s*(?:(?:AUTO|INT|VAR|LET|[A-Za-z_]\w*)\s+)?(\w+)\s*:\s*(.+?)\s*\)\s*\{?\s*$",
    re.IGNORECASE,
)

_OPENERS = re.compile(
    r"^(?:(?:DEF|FUNCTION|PROCEDURE|ALGORITHM)\b|FOR\b|WHILE\b|IF\b|REPEAT\b|DO\b)",
    re.IGNORECASE,
)
_CONTINUERS = re.compile(
    r"^(?:ELSE\s*IF|ELIF|OTHERWISE\s+IF|ELSE|OTHERWISE)\b",
    re.IGNORECASE,
)
_CLOSERS = re.compile(
    r"^(?:END|NEXT|UNTIL|ENDDO|END\s*DO)\b|\}",
    re.IGNORECASE,
)
_ONE_LINE_IF = re.compile(
    r"^IF\s+.+?\s+(?:THEN\s+\S+|(?:GO\s*TO|JUMP)\s+\w+|RETURN\b|BREAK|CONTINUE)",
    re.IGNORECASE,
)


def _strip_comment(line):
    quote = None
    i = 0
    while i < len(line):
        char = line[i]
        if quote:
            if char == quote:
                quote = None
            i += 1
        elif char in ("'", '"'):
            quote = char
            i += 1
        elif (char == "#" or line.startswith("//", i) or line.startswith("--", i)
              or char in ("\u25b7", "\u25b6") or line.startswith("\\triangleright", i)):
            return line[:i]
        elif line.startswith("/*", i):
            end = line.find("*/", i + 2)
            if end != -1:
                line = line[:i] + " " + line[end + 2:]
            else:
                return line[:i]
        else:
            i += 1
    return line


def _convert_c_for(line):
    m = _C_FOR_RE.match(line)
    if m:
        var, start, op, end, step = m.groups()
        step_clean = step.replace(" ", "")
        if step_clean in (f"{var}++", f"++{var}", f"{var}+=1"):
            if op == "<":
                return f"FOR {var} = {start} TO ({end}) - 1"
            elif op == "<=":
                return f"FOR {var} = {start} TO {end}"
        elif step_clean in (f"{var}--", f"--{var}", f"{var}-=1"):
            if op == ">":
                return f"FOR {var} = {start} DOWNTO ({end}) + 1"
            elif op == ">=":
                return f"FOR {var} = {start} DOWNTO {end}"
        elif step_clean.startswith(f"{var}*="):
            factor = step_clean[len(var) + 2:]
            return f"FOR {var} = {start} TO {end} STEP *{factor}"
        elif step_clean.startswith(f"{var}+="):
            inc = step_clean[len(var) + 2:]
            return f"FOR {var} = {start} TO {end} STEP {inc}"
        return f"FOR {var} = {start} TO {end}"
    m_each = _C_FOREACH_RE.match(line)
    if m_each:
        var, coll = m_each.groups()
        return f"FOR EACH {var} IN {coll}"
    return line


def _split_semicolons(line):
    parts = []
    current = []
    depth = 0
    quote = None
    for char in line:
        if quote:
            current.append(char)
            if char == quote:
                quote = None
        elif char in ("'", '"'):
            quote = char
            current.append(char)
        elif char in "([":
            depth += 1
            current.append(char)
        elif char in ")]":
            depth -= 1
            current.append(char)
        elif char == ";" and depth == 0:
            stmt = "".join(current).strip()
            if stmt:
                parts.append(stmt)
            current = []
        else:
            current.append(char)
    stmt = "".join(current).strip()
    if stmt:
        parts.append(stmt)
    return parts or [line]


def _balanced_call(text):
    """True if the first '(' in text is closed by the final ')'."""
    start = text.find("(")
    depth = 0
    for index in range(start, len(text)):
        if text[index] == "(":
            depth += 1
        elif text[index] == ")":
            depth -= 1
            if depth == 0:
                return index == len(text.rstrip()) - 1
    return False


class Parser:
    def __init__(self, code, _lines=None):
        if _lines is not None:
            self.lines = _lines
        else:
            self.lines = self._preprocess_source(code)
        self.index = 0

    @classmethod
    def _preprocess_source(cls, code):
        clean_code = code.replace("∞", "INF").replace("∈", " IN ").replace("∉", " NOT IN ")
        clean_code = clean_code.replace("⟵", "<-").replace("←", "<-")
        clean_code = clean_code.replace("≠", "!=").replace("≤", "<=").replace("≥", ">=")
        clean_code = clean_code.replace("∅", "EMPTY")
        clean_code = re.sub(r"⌊(.*?)⌋", r"floor(\1)", clean_code)
        clean_code = re.sub(r"⌈(.*?)⌉", r"ceil(\1)", clean_code)
        clean_code = re.sub(r"\blg\b", "log", clean_code)

        raw_lines = clean_code.splitlines()
        first_pass = []
        for line_num, raw in enumerate(raw_lines, 1):
            comment_stripped = _strip_comment(raw)
            indent = len(comment_stripped) - len(comment_stripped.lstrip())
            text = comment_stripped.strip()
            if not text:
                continue
            text = re.sub(r"^(?:\d+[\.:\)]|\(\d+\)|\[\d+\])\s+", "", text)
            text = re.sub(r"^\d+\s+(?=[A-Za-z_])", "", text)
            if text.endswith("{"):
                text = text[:-1].strip()
            if text == "}":
                text = "END"
            elif text.startswith("}") and re.search(r"\}\s*else", text, re.I):
                text = text[1:].strip()
                first_pass.append((line_num, indent, "END IF"))
            text = _convert_c_for(text)
            if text:
                first_pass.append((line_num, indent, text))

        if not first_pass:
            return []

        # Check for bare function header at line 0 or top level:
        # e.g. MERGE-SORT(A, p, r) at indent 0, followed by indented lines
        for idx in range(len(first_pass)):
            num, ind, txt = first_pass[idx]
            if ind == 0 and re.match(r"^[A-Za-z_][\w-]*\s*\([^\)]*\)\s*:?$", txt):
                if not re.match(r"^(?:FUNCTION|PROCEDURE|ALGORITHM|DEF|CALL|RETURN)\b", txt, re.I):
                    if idx + 1 < len(first_pass) and first_pass[idx + 1][1] > ind:
                        first_pass[idx] = (num, ind, "FUNCTION " + txt.rstrip(":"))

        texts = [t for _, _, t in first_pass]
        has_def = any(re.match(r"^(?:DEF)\s+\w+", t, re.I) for t in texts)
        has_colon_opener = any(re.match(r"^(?:if|for|while|elif|else)\b.*:\s*$", t, re.I) for t in texts)
        has_range = any(re.search(r"\brange\s*\(", t, re.I) for t in texts)
        has_bare_func = any(txt.startswith("FUNCTION ") and not raw_lines[idx].lstrip().upper().startswith(("FUNCTION", "PROCEDURE", "ALGORITHM", "DEF"))
                            for idx, (_, _, txt) in enumerate(first_pass) if idx < len(raw_lines))

        num_openers = sum(1 for _, _, t in first_pass if _OPENERS.match(t) and not _ONE_LINE_IF.match(t))
        num_closers = sum(1 for _, _, t in first_pass if _CLOSERS.match(t))

        is_indent_mode = (num_closers < num_openers) and (has_def or has_colon_opener or has_range or has_bare_func or any(t.endswith(":") for t in texts))

        if is_indent_mode:
            expanded = []
            stack = []
            last_num = 1
            for num, ind, txt in first_pass:
                clean_txt = re.sub(r":\s*$", "", txt).strip()
                if clean_txt.upper().startswith("ELIF "):
                    clean_txt = "ELSE IF " + clean_txt[5:].strip()

                is_cont = bool(_CONTINUERS.match(clean_txt))
                is_close = bool(_CLOSERS.match(clean_txt))

                # Detect compact explicit terminators like ENDWHILE / ENDFOR / ENDIF
                # that have already caused a stack pop — don't re-emit them.
                _COMPACT_END_RE = re.compile(
                    r"^(ENDIF|ENDFOR|ENDWHILE|ENDFUNCTION|ENDPROCEDURE|ENDDO)\b",
                    re.IGNORECASE,
                )
                is_compact_explicit = bool(_COMPACT_END_RE.match(clean_txt))

                while stack:
                    top_ind, top_kind = stack[-1]
                    if is_cont and ind == top_ind and top_kind == "IF":
                        break
                    if is_close and (ind <= top_ind or len(stack) == 1):
                        stack.pop()
                        # For compact explicit terminators (ENDWHILE etc.) the pop
                        # is the whole action — don't also emit "END X" since the
                        # compact form IS the terminator the parser expects.
                        if not is_compact_explicit:
                            expanded.append((num, f"END {top_kind}"))
                        break
                    if ind <= top_ind:
                        stack.pop()
                        expanded.append((num, f"END {top_kind}"))
                    else:
                        break

                # In indent mode, skip re-emitting compact explicit terminators;
                # they have already closed the scope via the stack pop above.
                if not is_compact_explicit:
                    expanded.append((num, clean_txt))
                last_num = num

                if _OPENERS.match(clean_txt) and not _ONE_LINE_IF.match(clean_txt):
                    kind = _OPENERS.match(clean_txt).group(0).upper()
                    if kind in ("DEF", "PROCEDURE", "ALGORITHM"):
                        kind = "FUNCTION"
                    stack.append((ind, kind))

            while stack:
                _, top_kind = stack.pop()
                expanded.append((last_num, f"END {top_kind}"))
            final_lines = expanded
        else:
            final_lines = [(num, txt) for num, _, txt in first_pass]

        split_result = []
        for num, txt in final_lines:
            for piece in _split_semicolons(txt):
                piece_clean = piece.strip().rstrip(";").strip()
                if piece_clean:
                    split_result.append((num, piece_clean))
        return split_result

    # ------------------------------------------------------------------
    # helpers
    # ------------------------------------------------------------------
    def _peek(self):
        if self.index < len(self.lines):
            return self.lines[self.index]
        return None

    def _is_terminator(self, text):
        return bool(
            _END_RE.match(text) or _ELSE_RE.match(text) or _ELSEIF_RE.match(text)
            or _UNTIL_RE.match(text) or _DOWHILE_END_RE.match(text)
            or text.upper() == "DONE"
        )

    @staticmethod
    def _end_kind(text):
        """'ANY', 'IF', 'FOR', ... for an END line; None if not an END line."""
        match = _END_RE.match(text)
        if not match:
            return None
        if match.group(4):
            return "FOR"
        word = (match.group(2) or "").upper()
        if match.group(3):
            word = match.group(3).upper()[3:]
        if word in ("PROCEDURE", "ALGORITHM"):
            word = "FUNCTION"
        return word or "ANY"

    def _close(self, kind, opened_at, description):
        """Consume the END line that closes a block of the given kind."""
        current = self._peek()
        if current is None:
            raise SyntaxError(
                f"{description} starting at line {opened_at} is missing its END."
            )
        number, text = current
        found = self._end_kind(text)
        if found in ("ANY", kind):
            self.index += 1
            return
        raise SyntaxError(
            f"Line {number}: found '{text}' but expected END"
            f"{'' if kind == 'ANY' else ' ' + kind} to close the {description} "
            f"starting at line {opened_at}."
        )

    # ------------------------------------------------------------------
    # top level
    # ------------------------------------------------------------------
    def parse(self):
        nodes = self.parse_block()
        while self.index < len(self.lines):
            number, text = self.lines[self.index]
            if text.upper() == "DONE":
                self.index += 1
                continue
            raise SyntaxError(
                f"Line {number}: unexpected '{text}' (no open block to close)."
            )
        return nodes

    def parse_block(self):
        nodes = []
        while self.index < len(self.lines):
            number, text = self.lines[self.index]
            if self._is_terminator(text):
                break
            node = self._statement(number, text)
            node["line"] = number
            nodes.append(node)
        return nodes

    # ------------------------------------------------------------------
    # statements
    # ------------------------------------------------------------------
    def _statement(self, number, text):
        upper = text.upper()

        if re.match(r"^(?:FUNCTION|PROCEDURE|ALGORITHM|DEF)\s", text, re.I):
            return self._function(number, text)
        if re.match(r"^FOR\s", text, re.I):
            return self._for(number, text)
        if re.match(r"^WHILE\s", text, re.I):
            return self._while(number, text)
        if re.match(r"^IF\s", text, re.I):
            return self._if(number, text)
        if re.fullmatch(r"REPEAT\s*:?", text, re.I):
            return self._repeat(number)
        if re.fullmatch(r"DO\s*:?", text, re.I):
            return self._do_while(number)

        self.index += 1
        if upper == "BREAK":
            return {"type": "BREAK"}
        if upper == "CONTINUE":
            return {"type": "CONTINUE"}
        match = _GOTO_RE.match(text)
        if match:
            return {"type": "GOTO", "label": match.group(1)}
        match = _LABEL_COLON_RE.match(text) or re.match(
            r"^LABEL\s+([A-Za-z_]\w*)\s*:?$", text, re.IGNORECASE)
        if match and match.group(1).lower() not in _KEYWORD_LABELS:
            return {"type": "LABEL", "name": match.group(1)}
        if upper == "RETURN" or re.match(r"^RETURN[\s(]", text, re.I):
            return {"type": "RETURN", "value": text[6:].strip() or None}
        match = _CALL_RE.match(text)
        if match and _balanced_call(text.split(None, 1)[-1] if
                                    text.upper().startswith("CALL ") else text):
            return {
                "type": "FUNCTION_CALL",
                "name": match.group(1).replace("-", "_"),
                "arguments": split_arguments(match.group(2)),
            }
        return {"type": "OPERATION", "code": text}

    def _function(self, number, text):
        match = _FUNC_RE.match(text)
        if not match:
            raise SyntaxError(f"Line {number}: invalid FUNCTION header: {text}")
        self.index += 1
        body = self.parse_block()
        self._close("FUNCTION", number, "FUNCTION")
        return {
            "type": "FUNCTION",
            "name": match.group(1).replace("-", "_"),
            "parameters": split_arguments(match.group(2) or ""),
            "body": body,
        }

    def _for(self, number, text):
        match = _FOR_RE.match(text)
        if match:
            node = {
                "type": "FOR",
                "variable": match.group(1),
                "start": match.group(2).strip(),
                "end": match.group(4).strip(),
                "step": (match.group(5) or "").strip() or None,
                "direction": "DOWN" if match.group(3).upper() == "DOWNTO" else "UP",
            }
        else:
            each = _FOREACH_RE.match(text)
            if not each:
                raise SyntaxError(f"Line {number}: invalid FOR loop: {text}")
            collection = each.group(2).strip()
            names = [v.strip() for v in each.group(1).strip("()").split(",")
                     if v.strip()]
            node = {
                "type": "FOR",
                "variable": names[0] if names else "_",
                "variables": names,
                "start": "1",
                "end": "n",
                "step": None,
                "direction": "UP",
                "collection": collection,
            }
            ranged = re.fullmatch(r"(.+?)\s*\.\.\.?\s*(.+)", collection)
            to_range = re.fullmatch(r"(.+?)\s+TO\s+(.+)", collection, re.IGNORECASE)
            range_call = re.fullmatch(r"range\s*\((.*?)\)", collection, re.IGNORECASE)
            if ranged:
                node["start"], node["end"] = ranged.group(1), ranged.group(2)
                del node["collection"]
            elif to_range:
                node["start"], node["end"] = to_range.group(1).strip(), to_range.group(2).strip()
                del node["collection"]
            elif range_call:
                r_args = split_arguments(range_call.group(1))
                if len(r_args) == 1:
                    node["start"] = "0"
                    node["end"] = f"({r_args[0]}) - 1"
                elif len(r_args) == 2:
                    node["start"] = r_args[0]
                    node["end"] = f"({r_args[1]}) - 1"
                elif len(r_args) >= 3:
                    node["start"] = r_args[0]
                    node["end"] = f"({r_args[1]}) - 1"
                    node["step"] = r_args[2]
                del node["collection"]
        self.index += 1
        node["body"] = self.parse_block()
        self._close("FOR", number, "FOR loop")
        return node

    def _while(self, number, text):
        match = _WHILE_RE.match(text)
        if not match:
            raise SyntaxError(f"Line {number}: invalid WHILE loop: {text}")
        self.index += 1
        body = self.parse_block()
        self._close("WHILE", number, "WHILE loop")
        return {"type": "WHILE", "condition": match.group(1).strip(), "body": body}

    def _if(self, number, text):
        jump = _IF_JUMP_RE.match(text)
        if jump and not _IF_THEN_RE.match(text):
            self.index += 1
            inner = Parser("", _lines=[(number, jump.group(2).strip())])
            return {
                "type": "IF",
                "condition": jump.group(1).strip(),
                "true_body": inner.parse_block(),
                "false_body": [],
            }
        one_line = _IF_THEN_RE.match(text)
        if one_line and one_line.group(2).strip():
            self.index += 1
            inner = Parser("", _lines=[(number, one_line.group(2).strip())])
            return {
                "type": "IF",
                "condition": one_line.group(1).strip(),
                "true_body": inner.parse_block(),
                "false_body": [],
            }
        if one_line:
            condition = one_line.group(1).strip()
        else:
            match = _IF_RE.match(text)
            if not match:
                raise SyntaxError(f"Line {number}: invalid IF statement: {text}")
            condition = re.sub(r"\s+THEN$", "", match.group(1), flags=re.I).strip()
        self.index += 1
        return self._if_rest(condition, number)

    def _if_rest(self, condition, number):
        true_body = self.parse_block()
        false_body = []
        current = self._peek()
        if current is not None:
            _, text = current
            elseif = _ELSEIF_RE.match(text)
            if elseif:
                self.index += 1
                nested = self._if_rest(elseif.group(1).strip(), current[0])
                nested["line"] = current[0]
                return {
                    "type": "IF", "condition": condition,
                    "true_body": true_body, "false_body": [nested],
                }
            if _ELSE_RE.match(text):
                self.index += 1
                false_body = self.parse_block()
        self._close("IF", number, "IF statement")
        return {
            "type": "IF", "condition": condition,
            "true_body": true_body, "false_body": false_body,
        }

    def _repeat(self, number):
        self.index += 1
        body = self.parse_block()
        current = self._peek()
        match = _UNTIL_RE.match(current[1]) if current else None
        if not match:
            raise SyntaxError(
                f"REPEAT starting at line {number} is missing its UNTIL condition."
            )
        self.index += 1
        return {"type": "REPEAT_UNTIL", "condition": match.group(1).strip(),
                "body": body}

    def _do_while(self, number):
        self.index += 1
        body = self.parse_block()
        current = self._peek()
        match = _DOWHILE_END_RE.match(current[1]) if current else None
        if not match:
            raise SyntaxError(
                f"DO starting at line {number} must end with "
                "'END DO WHILE condition'."
            )
        self.index += 1
        return {"type": "DO_WHILE", "condition": match.group(1).strip(),
                "body": body}
