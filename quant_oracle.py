#!/usr/bin/env python3
"""
Variable-aware ℕ/ℚ evaluator for the QUANTIFIED extension of the domain checker (Direction B).

domain_oracle.py decides CLOSED arithmetic. Most Lean-Workbook statements are quantified
(`∀ n : ℕ, ...`), which the closed oracle can't touch. This module evaluates an arithmetic body
under an assignment of its ℕ variables, in the two semantics that matter (Lean ℕ: truncated `-`,
floor `/`, `n/0=0`, `npow`; ℚ: exact field, `x/0=0`), so a witness search can look for an
assignment where a universally-quantified body is FALSE — a counterexample.

Kept separate from the audited `domain_oracle.py` so that the published closed-arithmetic oracle
stays pristine; the semantics here mirror it exactly, plus support for ast.Name (a bound variable).
"""
import ast
from fractions import Fraction


class NatUntyped(Exception):
    pass


class Unsupported(Exception):
    pass


def _eval(node, mode, env):
    if isinstance(node, ast.Expression):
        return _eval(node.body, mode, env)
    if isinstance(node, ast.Constant):
        if not isinstance(node.value, int):
            raise Unsupported(f"non-int literal {node.value!r}")
        return node.value if mode == "N" else Fraction(node.value)
    if isinstance(node, ast.Name):
        if node.id not in env:
            raise Unsupported(f"free name {node.id}")
        v = env[node.id]
        return v if mode == "N" else Fraction(v)
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
        if mode == "N":
            raise NatUntyped()
        return -_eval(node.operand, mode, env)
    if isinstance(node, ast.BinOp):
        a, b, op = _eval(node.left, mode, env), _eval(node.right, mode, env), node.op
        if isinstance(op, ast.Add):
            return a + b
        if isinstance(op, ast.Mult):
            return a * b
        if isinstance(op, ast.Sub):
            return (a - b if a >= b else 0) if mode == "N" else a - b
        if isinstance(op, ast.Div):
            if mode == "N":
                return a // b if b != 0 else 0
            return a / b if b != 0 else Fraction(0)
        if isinstance(op, ast.Pow):
            e = b if mode == "N" else (int(b) if b.denominator == 1 else None)
            if e is None or e < 0:
                raise Unsupported(f"bad exponent {b}")
            return a ** e
        raise Unsupported(f"op {type(op).__name__}")
    raise Unsupported(f"node {type(node).__name__}")


_CMP = {"=": lambda a, b: a == b, "≠": lambda a, b: a != b,
        "<": lambda a, b: a < b, ">": lambda a, b: a > b,
        "≤": lambda a, b: a <= b, "≥": lambda a, b: a >= b}


def value(expr, mode, env):
    return _eval(ast.parse(expr.replace("^", "**"), mode="eval"), mode, env)


def truth_at(lhs, rel, rhs, mode, env):
    """'TRUE'/'FALSE'/'N/A' (ℕ-untyped)/'SKIP' (unsupported) for the relation at this assignment."""
    try:
        a, b = value(lhs, mode, env), value(rhs, mode, env)
    except NatUntyped:
        return "N/A"
    except (Unsupported, ZeroDivisionError, SyntaxError, ValueError, RecursionError):
        return "SKIP"
    return "TRUE" if _CMP[rel](a, b) else "FALSE"
