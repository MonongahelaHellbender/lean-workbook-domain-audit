#!/usr/bin/env python3
"""
EXACT domain-hazard census: resolve every closed-arithmetic candidate with the Python dual-
semantics oracle (domain_oracle.py), VALIDATED against the Lean kernel on every candidate the
kernel can independently decide. Turns the earlier LOWER BOUND (8 confirmed, 119 undetermined,
35 skipped) into an exact corpus count.

Soundness discipline: the oracle is a new trusted component, so we (1) cross-check it against
Lean on the overlap — any disagreement is a hard failure to investigate, not a number to ship —
and (2) label each hazard kernel-confirmed (Lean decided it too, and agrees) vs oracle-only
(Lean couldn't/wouldn't decide; trust rests on the validated oracle).

Usage: python3 census_oracle.py [rows.json]   (default examples/_lw_full.json)
"""
import json
import os
import re
import subprocess
import sys

from lane_fidelity import auto_domain_pair, truth as lean_truth
from scan_domain_hazards import extract_goal, too_big, run_probes

from domain_oracle import classify

HERE = os.path.dirname(os.path.abspath(__file__))
DEFAULT = os.path.join(HERE, "examples", "_lw_full.json")
PROJECT = os.environ.get("MATHLIB_PROJECT", "")  # abs path to a Lean 4 project with Mathlib already built
LAKE = os.environ.get("LAKE", "lake")  # `lake` on PATH, or set LAKE=/path/to/lake
NATIVE = os.path.join(HERE, "examples", "_native_confirm.lean")


def run_native(props):
    """Confirm each prop with `native_decide` (kernel + COMPILER in TCB via Lean.ofReduceBool).
    Stronger reach than norm_num/decide on big concrete ℕ/ℚ arithmetic; the compiler-trust is a
    documented TCB expansion, so native confirmation is reported as a SEPARATE tier, not folded
    into the trusted-axiom base."""
    if not props:
        return {}
    src = ["import Mathlib", ""]
    for k, p in props.items():
        src.append(f"theorem {k} : {p} := by native_decide")
        src.append(f"#print axioms {k}")
        src.append("")
    open(NATIVE, "w").write("\n".join(src))
    r = subprocess.run([LAKE, "env", "lean", NATIVE], cwd=PROJECT,
                       capture_output=True, text=True, timeout=1800)
    out = r.stdout + "\n" + r.stderr
    res = {}
    for k in props:
        m = re.search(rf"'{re.escape(k)}' depends on axioms:\s*\[([^\]]*)\]", out)
        res[k] = bool(m) and "sorryAx" not in m.group(1)
    return res


def main():
    path = sys.argv[1] if len(sys.argv) > 1 else DEFAULT
    rows = [r["row"] for r in json.load(open(path))["rows"]]
    seen, cands = set(), []
    for r in rows:
        fs = (r.get("formal_statement") or "").strip()
        key = r.get("id") or fs
        if not fs or key in seen:
            continue
        seen.add(key)
        goal = extract_goal(fs)
        ap = auto_domain_pair(goal) if goal else None
        if not ap:
            continue
        tag = (r.get("id") or "anon").replace("-", "_")
        v, ot = classify(ap["lhs"], ap["rel"], ap["rhs"])
        cands.append({"id": r.get("id"), "tag": tag, "ap": ap,
                      "detected": f"{ap['lhs']} {ap['rel']} {ap['rhs']}",
                      "oracle_verdict": v, "oracle_truth": ot,
                      "big": too_big(ap["lhs"] + ap["rhs"])})

    # Lean cross-check on every non-too_big candidate (kernel can't safely take the huge ones).
    props = {}
    for c in cands:
        if c["big"]:
            continue
        ap, t = c["ap"], c["tag"]
        props[f"dn_{t}_P"], props[f"dn_{t}_N"] = ap["natP"], f"¬ ({ap['natP']})"
        props[f"dq_{t}_P"], props[f"dq_{t}_N"] = ap["ratP"], f"¬ ({ap['ratP']})"
    proved = run_probes(props)

    # Validation: ONLY a definite-vs-definite mismatch is a soundness CONFLICT. Oracle abstaining
    # (PARSE_FAIL / N/A) where Lean decided is coverage, not a wrong answer — counted separately.
    agree = conflict = abstain = 0
    conflicts = []
    for c in cands:
        if c["big"]:
            c["lean_truth"] = {"ℕ": "SKIPPED", "ℚ": "SKIPPED"}
            continue
        lN, lQ = lean_truth(proved, f"dn_{c['tag']}"), lean_truth(proved, f"dq_{c['tag']}")
        c["lean_truth"] = {"ℕ": lN, "ℚ": lQ}
        for dom, lt in (("ℕ", lN), ("ℚ", lQ)):
            if lt not in ("TRUE", "FALSE"):
                continue
            ot = c["oracle_truth"][dom]
            if ot in ("PARSE_FAIL", "N/A"):
                abstain += 1
            elif ot == lt:
                agree += 1
            else:
                conflict += 1
                conflicts.append({"id": c["id"], "dom": dom, "oracle": ot, "lean": lt,
                                  "detected": c["detected"]})

    by = lambda v: [c for c in cands if c["oracle_verdict"] == v]
    hazards = by("HAZARD")

    # native_decide confirmation of every hazard's predicted (ℕ,ℚ) verdict (covers big ones too).
    nprops = {}
    for h in hazards:
        ap, t, ot = h["ap"], h["tag"], h["oracle_truth"]
        nprops[f"nN_{t}"] = ap["natP"] if ot["ℕ"] == "TRUE" else f"¬ ({ap['natP']})"
        nprops[f"nQ_{t}"] = ap["ratP"] if ot["ℚ"] == "TRUE" else f"¬ ({ap['ratP']})"
    nconf = run_native(nprops)
    for h in hazards:
        t, lt = h["tag"], h["lean_truth"]
        h["native_ok"] = bool(nconf.get(f"nN_{t}") and nconf.get(f"nQ_{t}"))
        kernel = lt["ℕ"] in ("TRUE", "FALSE") and lt["ℚ"] in ("TRUE", "FALSE")
        h["support"] = ("kernel+oracle" if kernel else
                        "native+oracle" if h["native_ok"] else "oracle-only")

    tier = lambda s: sum(h["support"] == s for h in hazards)
    out = {
        "dataset": f"internlm/Lean-Workbook ({len(rows)} rows, {len(seen)} unique statements)",
        "method": "Python dual-semantics oracle, validated vs Lean kernel; hazards re-confirmed by native_decide",
        "closed_arith_candidates": len(cands),
        "oracle_breakdown": {"HAZARD": len(hazards), "SAFE": len(by("SAFE")),
                             "NAT_UNTYPED": len(by("NAT_UNTYPED")), "PARSE_FAIL": len(by("PARSE_FAIL"))},
        "validation_vs_lean": {"agree": agree, "CONFLICT": conflict, "oracle_abstained": abstain,
                               "conflicts": conflicts},
        "EXACT_hazards": len(hazards),
        "hazard_support": {"kernel+oracle": tier("kernel+oracle"),
                           "native+oracle": tier("native+oracle"), "oracle_only": tier("oracle-only")},
        "corpus_hazard_rate": round(len(hazards) / len(seen), 5),
        "hazards": [{"id": h["id"], "support": h["support"], "truth": h["oracle_truth"],
                     "detected": h["detected"][:90]} for h in hazards],
        "parse_fail_out_of_scope": [{"id": c["id"], "detected": c["detected"][:90]} for c in by("PARSE_FAIL")],
    }
    print(json.dumps(out, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
