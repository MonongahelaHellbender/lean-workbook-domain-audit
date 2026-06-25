#!/usr/bin/env python3
"""
REAL-domain truth oracle for the root/fractional-exponent class (trust lane, Direction B ext.).
Run with Python (has mpmath + sympy).

Motivation: ~20 closed candidates carry a FRACTIONAL exponent (`x^(1/3)` = a real root). The
rational oracle PARSE_FAILs them (a root is not rational arithmetic). But they are a real DEFECT
class: Lean's `^` wants a ℕ exponent, so `1/3` FLOORS to 0 and `x^(1/3)` silently becomes
`x^0 = 1` — a different statement from the intended real-root claim. To detect that divergence we
need the INTENDED real-number truth, computed RIGOROUSLY (not floating-point eyeballing):

  inequalities / disprovable equalities -> mpmath.iv INTERVAL arithmetic: a verdict is returned
        only when the enclosures are disjoint (rigorous); else precision is raised, then we abstain.
  provable equalities (radical identities) -> sympy `(lhs-rhs).equals(0)` (True/False/None).

The INTENDED reading uses the EXACT rational exponent (1/3 stays 1/3); a fractional power needs a
positive base (else 'INDETERMINATE'). Returns TRUE / FALSE / INDETERMINATE — never a guess.
"""
import ast
from fractions import Fraction

from mpmath import iv

from domain_oracle import _eval as exact_eval  # exact rational eval (for the exponent value)

_PREC = (50, 150, 500)


class Indet(Exception):
    pass


def _to_iv(fr):
    return iv.mpf(fr.numerator) / iv.mpf(fr.denominator)


def _eval_iv(node):
    if isinstance(node, ast.Expression):
        return _eval_iv(node.body)
    if isinstance(node, ast.Constant):
        if not isinstance(node.value, int):
            raise Indet("non-int literal")
        return iv.mpf(node.value)
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
        return -_eval_iv(node.operand)
    if isinstance(node, ast.BinOp):
        op = node.op
        if isinstance(op, ast.Pow):
            base = _eval_iv(node.left)
            e = exact_eval(node.right, "Q")               # EXACT real exponent (not floored)
            if not isinstance(e, Fraction):
                raise Indet("bad exponent")
            if e.denominator == 1:
                n = int(e)
                return base ** n if n >= 0 else iv.mpf(1) / (base ** (-n))
            if not base.a > 0:                            # fractional power needs base > 0
                raise Indet("non-positive base under fractional power")
            return iv.exp(_to_iv(e) * iv.log(base))
        a, b = _eval_iv(node.left), _eval_iv(node.right)
        if isinstance(op, ast.Add):
            return a + b
        if isinstance(op, ast.Sub):
            return a - b
        if isinstance(op, ast.Mult):
            return a * b
        if isinstance(op, ast.Div):
            if 0 in b:                                    # Lean junk value x/0 = 0
                raise Indet("division by interval containing 0")
            return a / b
        raise Indet(f"op {type(op).__name__}")
    raise Indet(f"node {type(node).__name__}")


def _parse(expr):
    return ast.parse(expr.replace("^", "**"), mode="eval")


def _ineq(L, R, rel):
    """Rigorous from disjoint enclosures; None if intervals overlap."""
    if rel in ("<", "≤"):
        if L.b < R.a:
            return "TRUE"
        if L.a > R.b:
            return "FALSE"
    if rel in (">", "≥"):
        if L.a > R.b:
            return "TRUE"
        if L.b < R.a:
            return "FALSE"
    return None


def _sympy_equal(lhs, rhs):
    import sympy
    L = sympy.sympify(lhs.replace("^", "**"), rational=True)
    R = sympy.sympify(rhs.replace("^", "**"), rational=True)
    return (L - R).equals(0)            # True / False / None


def real_truth(lhs, rel, rhs):
    """'TRUE' / 'FALSE' / 'INDETERMINATE' for the relation over ℝ (real exponents)."""
    overlap_seen = False
    for dps in _PREC:
        iv.dps = dps
        try:
            L, R = _eval_iv(_parse(lhs)), _eval_iv(_parse(rhs))
        except (Indet, ValueError, ZeroDivisionError):
            return "INDETERMINATE"
        if rel in ("<", ">", "≤", "≥"):
            v = _ineq(L, R, rel)
            if v is not None:
                return v
            continue
        disjoint = (L.b < R.a) or (R.b < L.a)             # = / ≠
        if disjoint:
            return "FALSE" if rel == "=" else "TRUE"
        overlap_seen = True
    if rel in ("=", "≠") and overlap_seen:
        try:
            eq = _sympy_equal(lhs, rhs)
        except Exception:
            return "INDETERMINATE"
        if eq is None:
            return "INDETERMINATE"
        if rel == "=":
            return "TRUE" if eq else "FALSE"
        return "FALSE" if eq else "TRUE"
    return "INDETERMINATE"


_SELFTEST = [
    ("12^(1/2)", ">", "45 / 13", "TRUE"),
    ("(2^(1/3) + 1)^3 * (2^(1/3) - 1)", "=", "3", "TRUE"),
    ("(2^100 + 3^100)^(1/100)", "=", "3", "FALSE"),
    ("(1 / (2^4))^(1 / 4)", "=", "1 / 2", "TRUE"),
    ("(5/6)^(1/3) + (6/5)^(1/3)", ">", "2", "TRUE"),
    ("(10^(11/5))", "=", "(100 * (10^(1/5)))", "TRUE"),
]

if __name__ == "__main__":
    ok = True
    for lhs, rel, rhs, ev in _SELFTEST:
        got = real_truth(lhs, rel, rhs)
        good = got == ev
        ok &= good
        print(f"{'ok ' if good else 'FAIL'} {lhs} {rel} {rhs}  -> {got} (exp {ev})")
    print("SELFTEST", "PASS" if ok else "FAIL")
