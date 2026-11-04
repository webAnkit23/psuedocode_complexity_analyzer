"""
goto_resolver.py
----------------
Rewrites GOTO / label control flow into structured loops *before* analysis,
so a jump is costed at the label it really targets.

Within one block (a function body, loop body, IF branch ...), labels split the
statements into segments. Then:

 1. Dead code is removed: after an unconditional GOTO/RETURN nothing runs
    until a label that is the target of reachable jump.
 2. Backward jumps become loops
       label: ... IF c GOTO label            ->  DO ... WHILE c
       label: ... [IF c GOTO exit] ... GOTO label
                                             ->  WHILE NOT c ...
       label: ... (jump buried inside another statement)
                                             ->  loop with unknown count (O(n))
 3. Forward jumps only ever skip work, so they are dropped (the worst case is
    the same as not jumping).

Jumps that cannot be matched to a label are reported as warnings.
"""

import copy

from expressions import walk


def _is_goto_only(body):
    return len(body) == 1 and body[0].get("type") == "GOTO"


class GotoResolver:
    def __init__(self):
        self.notes = []
        self.warnings = []

    def resolve(self, nodes):
        nodes = copy.deepcopy(nodes)
        return self._block(nodes)

    # ------------------------------------------------------------------
    def _note(self, text):
        if text not in self.notes:
            self.notes.append(text)

    def _warn(self, text):
        if text not in self.warnings:
            self.warnings.append(text)

    @staticmethod
    def _gotos(node):
        """Every GOTO inside a statement (including the statement itself)."""
        return [n for n in walk([node]) if n.get("type") == "GOTO"]

    def _block(self, nodes):
        has_label = any(n.get("type") == "LABEL" for n in nodes)
        has_goto = any(self._gotos(n) for n in nodes)
        if has_label or has_goto:
            nodes = self._resolve_level(nodes)
        for node in nodes:
            self._recurse(node)
        return nodes

    def _recurse(self, node):
        kind = node.get("type")
        if kind == "IF":
            node["true_body"] = self._block(node.get("true_body", []))
            node["false_body"] = self._block(node.get("false_body", []))
        elif kind in ("FUNCTION", "FOR", "WHILE", "REPEAT_UNTIL", "DO_WHILE"):
            node["body"] = self._block(node.get("body", []))

    # ------------------------------------------------------------------
    def _labels(self, nodes):
        labels = {}
        for index, node in enumerate(nodes):
            if node.get("type") == "LABEL":
                labels.setdefault(node["name"], index)
        return labels

    def _resolve_level(self, nodes):
        labels = self._labels(nodes)
        nodes = self._prune_dead_code(nodes, labels)
        labels = self._labels(nodes)

        changed = True
        while changed:
            changed = False
            for j, node in enumerate(nodes):
                back = [g for g in self._gotos(node)
                        if g["label"] in labels and labels[g["label"]] < j]
                if not back:
                    continue
                target = back[0]["label"]
                i = labels[target]
                all_back = [(jj, g) for jj, n in enumerate(nodes)
                            for g in self._gotos(n)
                            if g["label"] == target and labels[target] < jj]
                last = max(jj for jj, _ in all_back)
                nodes = self._make_loop(nodes, i, last, target, len(all_back))
                labels = self._labels(nodes)
                changed = True
                break

        # Remaining jumps are forward jumps (or jumps to unknown labels).
        for node in nodes:
            self._strip_forward_gotos(node, labels, False)
        result = []
        for node in nodes:
            if node.get("type") == "LABEL":
                continue
            if node.get("type") == "GOTO" and node["label"] in labels:
                self._note(
                    f"GOTO {node['label']} (line {node.get('line', '?')}) jumps "
                    "forward; code it skips is never counted twice."
                )
                continue
            result.append(node)
        return result

    # ---- dead code -----------------------------------------------------
    def _prune_dead_code(self, nodes, labels):
        live_labels = set()
        while True:
            reachable, found = True, set()
            for node in nodes:
                if node.get("type") == "LABEL" and node["name"] in live_labels:
                    reachable = True
                if not reachable:
                    continue
                for goto in self._gotos(node):
                    if goto["label"] in labels:
                        found.add(goto["label"])
                if node.get("type") in ("GOTO", "RETURN"):
                    reachable = False
            if found <= live_labels:
                break
            live_labels |= found

        kept, reachable = [], True
        for node in nodes:
            if node.get("type") == "LABEL" and node["name"] in live_labels:
                reachable = True
            if reachable:
                kept.append(node)
            elif node.get("type") != "LABEL":
                self._note(
                    f"Line {node.get('line', '?')}: unreachable code after a "
                    "GOTO/RETURN is ignored."
                )
            if reachable and node.get("type") in ("GOTO", "RETURN"):
                reachable = False
        return kept

    # ---- backward jumps -> loops --------------------------------------
    def _make_loop(self, nodes, i, j, label, jump_count):
        region = nodes[i + 1:j]
        tail = nodes[j]
        line = nodes[i].get("line")

        def finish(loop, text):
            loop["line"] = line
            self._note(text)
            return nodes[:i] + [loop] + nodes[j + 1:]

        if jump_count == 1 and tail.get("type") == "IF" \
                and _is_goto_only(tail.get("true_body", [])) \
                and not tail.get("false_body") \
                and tail["true_body"][0]["label"] == label:
            loop = {"type": "DO_WHILE", "condition": tail["condition"],
                    "body": region}
            return finish(loop, (
                f"GOTO {label} (line {tail.get('line', '?')}) jumps back to "
                f"'{label}:' -> treated as DO ... WHILE {tail['condition']}."
            ))

        if jump_count == 1 and tail.get("type") == "GOTO":
            exits, body = [], []
            for stmt in region:
                if self._is_exit_test(stmt, nodes, i, j):
                    exits.append(stmt)
                else:
                    body.append(stmt)
            if exits:
                cond = " AND ".join(f"NOT ({e['condition']})" for e in exits)
                loop = {"type": "WHILE", "condition": cond, "body": body}
                return finish(loop, (
                    f"GOTO {label} (line {tail.get('line', '?')}) with an exit "
                    f"test -> treated as WHILE {cond}."
                ))
            loop = {"type": "WHILE", "condition": "TRUE", "body": region}
            self._warn(
                f"GOTO {label}: backward jump without a recognisable exit "
                "test; the loop count is unknown (assumed O(n))."
            )
            return finish(loop, f"GOTO {label} treated as an unbounded loop.")

        # A jump buried inside another statement, or several jumps.
        for goto in self._gotos(tail):
            goto.clear()
            goto["type"] = "CONTINUE"
        for stmt in region:
            for goto in self._gotos(stmt):
                if goto["label"] == label:
                    goto.clear()
                    goto["type"] = "CONTINUE"
        loop = {"type": "WHILE", "condition": "TRUE", "body": region + [tail]}
        self._warn(
            f"GOTO {label}: the backward jump is nested or repeated, so the "
            "number of repetitions is unknown (assumed O(n))."
        )
        return finish(loop, f"GOTO {label} treated as a repeat-loop of unknown length.")

    def _is_exit_test(self, stmt, nodes, i, j):
        """IF cond GOTO exit / RETURN / BREAK, with `exit` outside [i, j]."""
        if stmt.get("type") != "IF" or stmt.get("false_body"):
            return False
        body = stmt.get("true_body", [])
        if len(body) != 1:
            return False
        only = body[0]
        if only.get("type") in ("RETURN", "BREAK"):
            return True
        if only.get("type") == "GOTO":
            labels = self._labels(nodes)
            index = labels.get(only["label"])
            return index is not None and not (i <= index <= j)
        return False

    # ---- forward jumps -------------------------------------------------
    def _strip_forward_gotos(self, node, labels, in_loop):
        kind = node.get("type")
        in_loop = in_loop or kind in ("FOR", "WHILE", "REPEAT_UNTIL", "DO_WHILE")
        for key in ("body", "true_body", "false_body"):
            block = node.get(key)
            if not block:
                continue
            kept = []
            for child in block:
                if child.get("type") == "GOTO":
                    if child["label"] in labels:
                        if in_loop:
                            self._note(
                                f"GOTO {child['label']} (line {child.get('line', '?')}) "
                                "jumps out of a loop to a later label -> treated as BREAK."
                            )
                            kept.append({"type": "BREAK", "line": child.get("line")})
                        else:
                            self._note(
                                f"GOTO {child['label']} (line {child.get('line', '?')}) "
                                "jumps forward; it can only skip work, so the "
                                "worst case ignores the jump."
                            )
                        continue
                    kept.append(child)     # target is in an enclosing block
                else:
                    self._strip_forward_gotos(child, labels, in_loop)
                    kept.append(child)
            node[key] = kept
