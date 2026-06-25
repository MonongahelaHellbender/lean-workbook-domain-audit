#!/usr/bin/env python3
"""
Exact dual-semantics truth oracle for CLOSED arithmetic (trust lane, Direction B / CHECK B).

The Lean probe leaves ~119 closed-arithmetic candidates "undetermined" (nested ℚ division the
closed-form tactics don't settle) and skips ~35 more for kernel blow-up (e.g. 2^4038). But closed
numeral arithmetic is DECIDABLE — so we evaluate the statement exactly in Python under two
semantics that match Lean's operational behaviour precisely:

  ℚ (the intended domain for rational/real statements): standard field arithmetic via Fraction;
     Lean junk-value convention `x / 0 = 0`.
  ℕ (what a domain-naive autoformalization silently picks): Nat.sub is TRUNCATED (a - b = 0 when
     b ≥ a), Nat.div is FLOOR (and n / 0 = 0), `^` is Monoid.npow (ℕ exponent), no negation.

A unary minus is ill-typed over ℕ (no Neg ℕ) -> ℕ truth = 'N/A' (matches Lean failing to
elaborate the ℕ ascription). Non-integer / negative exponents and unsupported nodes -> 'PARSE_FAIL'
(reported, never silently guessed).

TRUST NOTE: this is a NEW trusted component. `census_oracle.py` validates it against the Lean
kernel on every candidate the kernel can independently decide; only then is it trusted on the rest.
"""
import ast
from fractions import Fraction


class NatUntyped(Exception):
    pass


def _eval(node, mode):
    """mode 'N' -> int (ℕ semantics) or raise NatUntyped; mode 'Q' -> Fraction."""
    if isinstance(node, ast.Expression):
        return _eval(node.body, mode)
    if isinstance(node, ast.Constant):
        if not isinstance(node.value, int):
            raise ValueError(f"non-int literal {node.value!r}")
        return node.value if mode == "N" else Fraction(node.value)
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
        if mode == "N":
            raise NatUntyped()
        return -_eval(node.operand, mode)
    if isinstance(node, ast.BinOp):
        a, b, op = _eval(node.left, mode), _eval(node.right, mode), node.op
        if isinstance(op, ast.Add):
            return a + b
        if isinstance(op, ast.Mult):
            return a * b
        if isinstance(op, ast.Sub):
            return (a - b if a >= b else 0) if mode == "N" else a - b
        if isinstance(op, ast.Div):
            if mode == "N":
                return a // b if b != 0 else 0          # Nat.div, n/0 = 0
            return a / b if b != 0 else Fraction(0)      # ℚ junk value x/0 = 0
        if isinstance(op, ast.Pow):
            e = b if mode == "N" else (int(b) if b.denominator == 1 else None)
            if e is None or e < 0:
                raise ValueError(f"unsupported exponent {b}")
            return a ** e
        raise ValueError(f"op {type(op).__name__}")
    raise ValueError(f"node {type(node).__name__}")


_CMP = {"=": lambda a, b: a == b, "≠": lambda a, b: a != b,
        "<": lambda a, b: a < b, ">": lambda a, b: a > b,
        "≤": lambda a, b: a <= b, "≥": lambda a, b: a >= b}


def side_value(expr, mode):
    return _eval(ast.parse(expr.replace("^", "**"), mode="eval"), mode)


def relation_truth(lhs, rel, rhs, mode):
    """'TRUE' / 'FALSE' / 'N/A' (ℕ-untyped) / 'PARSE_FAIL'."""
    try:
        a, b = side_value(lhs, mode), side_value(rhs, mode)
    except NatUntyped:
        return "N/A"
    except (ValueError, ZeroDivisionError, SyntaxError, RecursionError):
        return "PARSE_FAIL"
    return "TRUE" if _CMP[rel](a, b) else "FALSE"


def classify(lhs, rel, rhs):
    """Return (verdict, {'ℕ':tN,'ℚ':tQ}). verdict in HAZARD/SAFE/NAT_UNTYPED/PARSE_FAIL."""
    tN = relation_truth(lhs, rel, rhs, "N")
    tQ = relation_truth(lhs, rel, rhs, "Q")
    if "PARSE_FAIL" in (tN, tQ):
        v = "PARSE_FAIL"
    elif tN == "N/A":
        v = "NAT_UNTYPED"
    elif tN != tQ:
        v = "HAZARD"
    else:
        v = "SAFE"
    return v, {"ℕ": tN, "ℚ": tQ}


_SELFTEST = [
    ("5 - 8", "=", "0", "HAZARD", {"ℕ": "TRUE", "ℚ": "FALSE"}),
    ("1 - 25/64", "=", "39/64", "HAZARD", {"ℕ": "FALSE", "ℚ": "TRUE"}),
    ("2017 - (2017 / 3)", "=", "1345", "HAZARD", {"ℕ": "TRUE", "ℚ": "FALSE"}),
    ("6 / 3", "=", "2", "SAFE", {"ℕ": "TRUE", "ℚ": "TRUE"}),
    ("2 + 3", "=", "5", "SAFE", {"ℕ": "TRUE", "ℚ": "TRUE"}),
    ("1 - (6 + 4) / 36 - (1 + 4 + 1) / 36", "=", "5 / 9", "HAZARD", {"ℕ": "FALSE", "ℚ": "TRUE"}),
]

if __name__ == "__main__":
    ok = True
    for lhs, rel, rhs, ev, et in _SELFTEST:
        v, t = classify(lhs, rel, rhs)
        good = v == ev and t == et
        ok &= good
        print(f"{'ok ' if good else 'FAIL'} {lhs} {rel} {rhs}  -> {v} {t}")
    print("SELFTEST", "PASS" if ok else "FAIL")
