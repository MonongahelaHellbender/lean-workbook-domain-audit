#!/usr/bin/env python3
"""
Exponent-truncation hazard census for the root/fractional-exponent class (trust lane, Direction B
extension). Run with Python (real_oracle needs mpmath + sympy).

For each fractional-exponent candidate the rational oracle PARSE_FAILed, compare:
  as-formalized truth  = Lean `native_decide` on the VERBATIM default-typed goal (Lean's `^` wants
                         a ℕ exponent, so `1/3` floors to 0 and every `x^(1/n)` becomes `x^0 = 1`).
  intended-ℝ truth     = real_oracle.real_truth (rigorous mpmath.iv intervals + sympy identities).
A definite DIFFERENCE = EXPONENT-TRUNCATION HAZARD: the formalization claims something other than
the intended real-root statement. Same = SAFE (the floor happened to preserve the verdict). Either
side indefinite = INDETERMINATE (never guessed).
"""
import json
import os
import re
import subprocess
import sys

from real_oracle import real_truth
from lane_fidelity import auto_domain_pair
from scan_domain_hazards import extract_goal

HERE = os.path.dirname(os.path.abspath(__file__))
PROJECT = os.environ.get("MATHLIB_PROJECT", "")  # abs path to a Lean 4 project with Mathlib already built
LAKE = os.environ.get("LAKE", "lake")  # `lake` on PATH, or set LAKE=/path/to/lake
CENSUS = os.path.join(HERE, "examples", "_census.json")
FULL = os.path.join(HERE, "examples", "_lw_full.json")
NATIVE = os.path.join(HERE, "examples", "_real_native.lean")


def native_truth(items):
    """items: list of (tag, goal_str). Lean native_decide on goal and its negation -> truth dict."""
    src = ["import Mathlib", ""]
    for tag, g in items:
        src.append(f"theorem f_{tag} : {g} := by native_decide")
        src.append(f"#print axioms f_{tag}")
        src.append(f"theorem fn_{tag} : ¬ ({g}) := by native_decide")
        src.append(f"#print axioms fn_{tag}")
        src.append("")
    open(NATIVE, "w").write("\n".join(src))
    r = subprocess.run([LAKE, "env", "lean", NATIVE], cwd=PROJECT,
                       capture_output=True, text=True, timeout=1800)
    out = r.stdout + "\n" + r.stderr

    def proved(name):
        # A FAILED native_decide error-recovers with `sorry`, and #print axioms still emits a
        # line — containing sorryAx. So a genuine proof = axioms line present AND no sorryAx.
        m = re.search(rf"'{name}' depends on axioms:\s*\[([^\]]*)\]", out)
        return bool(m) and "sorryAx" not in m.group(1)

    res = {}
    for tag, _ in items:
        pos, neg = proved(f"f_{tag}"), proved(f"fn_{tag}")
        res[tag] = "TRUE" if pos else "FALSE" if neg else "UNKNOWN"
    return res


def main():
    pf_ids = [c["id"] for c in json.load(open(CENSUS))["parse_fail_out_of_scope"]]
    rows = {r["row"].get("id"): r["row"] for r in json.load(open(FULL))["rows"]}

    cands, items = [], []
    for cid in pf_ids:
        goal = extract_goal((rows.get(cid, {}).get("formal_statement") or "").strip())
        ap = auto_domain_pair(goal) if goal else None
        if not ap:
            continue
        tag = cid.replace("-", "_").replace("lean_workbook_", "")
        g = f"({ap['lhs']}) {ap['rel']} ({ap['rhs']})"
        cands.append({"id": cid, "tag": tag, "lhs": ap["lhs"], "rel": ap["rel"],
                      "rhs": ap["rhs"], "goal": g})
        items.append((tag, g))

    nat = native_truth(items)
    hazards, safe, indet = [], [], []
    for c in cands:
        c["as_formalized"] = nat.get(c["tag"], "UNKNOWN")
        c["intended_R"] = real_truth(c["lhs"], c["rel"], c["rhs"])
        af, ir = c["as_formalized"], c["intended_R"]
        if af in ("TRUE", "FALSE") and ir in ("TRUE", "FALSE"):
            (hazards if af != ir else safe).append(c)
        else:
            indet.append(c)

    fmt = lambda c: {"id": c["id"], "as_formalized": c["as_formalized"],
                     "intended_ℝ": c["intended_R"], "goal": c["goal"][:95]}
    out = {
        "class": "exponent-truncation (fractional exponent floored to ℕ by Lean's npow)",
        "method": "Lean native_decide (as-formalized) vs rigorous mpmath.iv+sympy real oracle (intended ℝ)",
        "candidates": len(cands),
        "EXPONENT_TRUNCATION_HAZARDS": len(hazards),
        "safe_floor_preserved_verdict": len(safe),
        "indeterminate": len(indet),
        "hazards": [fmt(c) for c in hazards],
        "safe": [fmt(c) for c in safe],
        "indeterminate_cases": [fmt(c) for c in indet],
    }
    print(json.dumps(out, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
