"""
recurrence_solver.py
--------------------
Solves recurrences produced by recursion.py.

    Divide type        T(n) = sum_i  m_i * T(c_i * n) + f(n)      (0 < c_i < 1)
        Solved with the Akra-Bazzi theorem, which contains the Master theorem
        as a special case and also handles unequal sub-problem sizes.

    Subtract type      T(n) = sum_i  m_i * T(n - k_i) + f(n)       (k_i > 0)
        one call      -> n * f(n)  (or f(n) if f is exponential)
        several calls -> r^n  where r solves  sum m_i * r^(-k_i) = 1

f(n) is the non-recursive work, a Complexity that may contain n^d log^e n.
Other variables inside f(n) are treated as constants multiplying the answer.
"""

import math
from fractions import Fraction

from fractions import Fraction
from complexity import SIZE_VAR, Complexity, Term, Unsupported, _fmt_base

TOL = 1e-6


class SolveResult:
    def __init__(self, complexity=None, notes=None, error=None):
        self.complexity = complexity
        self.notes = notes or []
        self.error = error

    def __str__(self):
        return str(self.complexity) if self.complexity else f"Unable to solve: {self.error}"


def _n_term(power=0, log=0, exp=1.0, fact=0, loglog=0):
    return Term.make({SIZE_VAR: (fact, exp, power, log, loglog)})


def _as_fraction(value):
    if abs(value - round(value)) < TOL:
        return Fraction(int(round(value)))
    return Fraction(value).limit_denominator(1000)


class RecurrenceSolver:
    def solve(self, recurrence):
        notes = []
        try:
            result = recurrence.work
            for alternative in recurrence.alternatives:
                if not alternative:
                    continue
                result = result.add(
                    self._solve_alternative(alternative, recurrence.work, notes)
                )
        except Unsupported as error:
            return SolveResult(error=str(error), notes=notes)
        return SolveResult(result, notes)

    # ------------------------------------------------------------------
    def _solve_alternative(self, calls, work, notes):
        kinds = {c.kind for c in calls}
        if kinds == {"SPLIT"}:
            return self._solve_split(calls, work, notes)
        if kinds == {"SQRT"}:
            return self._solve_sqrt(calls, work, notes)
        if kinds == {"MOD"}:
            return self._solve_mod(calls, work, notes)
        if len(kinds) > 1:
            raise Unsupported(
                "recursive calls mix different reduction styles ('n - k', 'n / b', 'sqrt(n)')"
            )
        symbolic = [c for c in calls if isinstance(c.mult, Complexity)]
        if symbolic:
            return self._solve_symbolic(calls, work, notes)
        if kinds == {"DEC"}:
            return self._solve_subtract(calls, work, notes)
        return self._solve_divide(calls, work, notes)

    def _solve_split(self, calls, work, notes):
        """Sub-problem sizes depend on data (e.g. a quicksort pivot)."""
        from recursion import RecCall
        scratch = []
        worst = self._solve_subtract([RecCall("DEC", 1, 1)], work, scratch)
        halves = [RecCall("DIV", Fraction(1, 2), 1) for _ in calls]
        best = self._solve_divide(halves, work, scratch)
        notes.append(
            "The split point is data-dependent. Worst case (one part gets "
            f"almost everything): T(n) = T(n-1) + f(n) -> {worst}. "
            f"A balanced split would give {best}."
        )
        return worst

    def _solve_sqrt(self, calls, work, notes):
        a = sum(c.mult for c in calls)
        # T(n) = a T(sqrt(n)) + f(n). Let n = 2^m => S(m) = a S(m/2) + f(2^m)
        has_log = any(t.key(SIZE_VAR)[3] > 0 or t.key(SIZE_VAR)[2] > 0 for t in work.terms)
        if not has_log or work.is_const:
            if a == 1:
                res = Complexity([_n_term(loglog=1)])
            elif a == 2:
                res = Complexity.log(SIZE_VAR)
            else:
                p = math.log2(float(a))
                p_exact = _as_fraction(p)
                res = Complexity([Term.make({SIZE_VAR: (0, 1.0, 0, p_exact, 0)})])
        else:
            if a == 1:
                res = Complexity.log(SIZE_VAR)
            elif a == 2:
                res = Complexity([Term.make({SIZE_VAR: (0, 1.0, 0, 1, 1)})])
            else:
                p = math.log2(float(a))
                p_exact = _as_fraction(p)
                res = Complexity([Term.make({SIZE_VAR: (0, 1.0, 0, p_exact, 0)})])
        notes.append(
            f"Substitution method on T(n) = {a}*T(sqrt(n)) + {work}: setting n = 2^m (m = log n) transforms the recurrence into S(m) = {a}*S(m/2) + g(m). Solving S(m) and substituting back m = log n yields {res}."
        )
        return res

    def _solve_mod(self, calls, work, notes):
        notes.append(
            "Euclidean algorithm recurrence: each recursive step replaces (a, b) with (b, a mod b), reducing the argument by at least a factor of 2 every two steps, giving O(log n) time."
        )
        return Complexity.log(SIZE_VAR)

    def _solve_symbolic(self, calls, work, notes):
        only = calls[0]
        if (len(calls) == 1 and only.kind == "DEC"
                and only.mult == Complexity.var(SIZE_VAR)):
            notes.append(
                "A recursive call inside a loop that runs n times gives "
                "T(n) = n * T(n - k) + ..., which grows like n!."
            )
            return Complexity.fact(SIZE_VAR)
        raise Unsupported(
            "a recursive call sits inside a loop with a non-constant number "
            "of iterations (only the n * T(n-1) = n! pattern is supported)"
        )

    # ---- T(n) = a T(n-k) + f(n) ---------------------------------------
    def _solve_subtract(self, calls, work, notes):
        total = sum(c.mult for c in calls)
        if total == 1:
            notes.append(
                "One recursive call on n-k: the work f(n) is repeated about "
                "n/k times, so T(n) = n * f(n)."
            )
            out = []
            for term in work.terms:
                key, _ = term.split(SIZE_VAR)
                if key[0] or key[1] != 1.0:        # factorial / exponential f(n)
                    out.append(term)
                else:
                    out.append(term.mul(Term.make({SIZE_VAR: (0, 1.0, 1, 0, 0)})))
            return Complexity(out)

        root = self._subtract_root(calls)
        notes.append(
            f"{total} recursive calls on n-k: the recursion tree grows by a "
            f"factor of about {_fmt_base(root)} per level, so T(n) = O({_fmt_base(root)}^n)."
        )
        out = [_n_term(exp=root)]
        for term in work.terms:
            (fact, base, power, log, *extra), rest = term.split(SIZE_VAR)
            if fact or base > root + TOL:
                out.append(term)                       # f(n) dominates
            elif abs(base - root) <= TOL:
                out.append(term.mul(_n_term(power=1)))
            else:
                out.append(rest.mul(_n_term(exp=root)))
        return Complexity(out)

    @staticmethod
    def _subtract_root(calls):
        def g(r):
            return sum(c.mult * r ** (-float(c.amount)) for c in calls) - 1.0
        smallest = min(float(c.amount) for c in calls)
        total = sum(c.mult for c in calls)
        low, high = 1.0 + 1e-12, total ** (1.0 / smallest) + 1.0
        for _ in range(200):
            mid = (low + high) / 2
            if g(mid) > 0:
                low = mid
            else:
                high = mid
        return round((low + high) / 2, 9)

    # ---- T(n) = sum m_i T(c_i n) + f(n) -------------------------------
    def _solve_divide(self, calls, work, notes):
        total = sum(c.mult for c in calls)
        if total == 1:
            p = 0.0
        else:
            def g(x):
                return sum(c.mult * float(c.amount) ** x for c in calls) - 1.0
            if g(0.0) < 0:
                low, high = -1.0, 0.0
                while g(low) < 0 and low > -64:
                    low *= 2
            else:
                low, high = 0.0, 1.0
                while g(high) > 0 and high < 64:
                    high *= 2
            for _ in range(200):
                mid = (low + high) / 2
                if g(mid) > 0:
                    low = mid
                else:
                    high = mid
            p = (low + high) / 2
        p_exact = _as_fraction(p)

        amounts = {c.amount for c in calls}
        is_master = len(amounts) == 1
        description = " + ".join(str(c) for c in calls)

        if is_master:
            c_val = next(iter(amounts))
            b_val = 1 / c_val
            b_str = str(b_val.numerator) if b_val.denominator == 1 else f"{float(b_val):g}"
            a_val = total
            notes.append(
                f"Master Theorem on T(n) = {description} + {work}: standard form T(n) = {a_val}*T(n/{b_str}) + f(n) with critical exponent log_{b_str}({a_val}) = {float(p_exact):.3f}."
            )
        else:
            notes.append(
                f"Akra-Bazzi on unequal divide recurrence: T(n) = {description} + {work}. The characteristic equation sum(m_i * c_i^p) = 1 yields critical exponent p = {float(p_exact):.3f}."
            )

        out = [_n_term(power=p_exact)] if p_exact else []
        for term in work.terms:
            (fact, base, power, log, *extra), rest = term.split(SIZE_VAR)
            loglog = extra[0] if extra else Fraction(0)
            if fact or base != 1.0:
                out.append(term)
            elif float(power) < p - TOL:
                if is_master:
                    notes.append(
                        f"Master Theorem Case 1 (f(n) = O(n^c) where c = {float(power):g} < log_b(a) = {float(p_exact):.3f}): leaves of the recursion tree dominate, so T(n) = Theta(n^(log_b a))."
                    )
                else:
                    notes.append(
                        f"Akra-Bazzi integral converges (f(n) = O(n^c) with c < p): leaves dominate, so T(n) = Theta(n^p)."
                    )
                out.append(rest.mul(_n_term(power=p_exact)))
            elif abs(float(power) - p) <= TOL:
                if log >= 0:
                    if is_master:
                        notes.append(
                            f"Master Theorem Case 2 (f(n) = Theta(n^(log_b a) * log^{log} n)): work is balanced across all levels of the recursion tree, adding one extra log n factor."
                        )
                    else:
                        notes.append(
                            f"Akra-Bazzi integral evaluates to Theta(log^{log+1} n): work is balanced across levels, adding an extra log n factor."
                        )
                    out.append(rest.mul(_n_term(power=p_exact, log=log + 1)))
                elif log == -1:
                    if is_master:
                        notes.append(
                            f"Extended Master Theorem / Akra-Bazzi (f(n) = Theta(n^(log_b a) / log n)): integral of 1/(u * ln u) gives an extra log(log n) factor: T(n) = Theta(n^(log_b a) * log(log n))."
                        )
                    else:
                        notes.append(
                            f"Akra-Bazzi integral of (1 / (u * ln u)) gives an extra log(log n) factor: T(n) = Theta(n^p * log(log n))."
                        )
                    out.append(rest.mul(_n_term(power=p_exact, loglog=1)))
                else:
                    out.append(rest.mul(_n_term(power=p_exact)))
            else:
                if is_master:
                    notes.append(
                        f"Master Theorem Case 3 (f(n) = Omega(n^c) where c = {float(power):g} > log_b(a) = {float(p_exact):.3f}): top-level non-recursive work dominates, and regularity condition holds."
                    )
                else:
                    notes.append(
                        "Akra-Bazzi integral dominated by upper limit: top-level non-recursive work dominates."
                    )
                out.append(term)
        return Complexity(out or [Term()])
