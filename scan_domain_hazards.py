#!/usr/bin/env python3
"""
REAL-DATA application of the auto domain-hazard detector (trust lane, Direction B).

Takes the CHECK-B auto-detector from `lane_fidelity.py` (which fires on its own, without
being handed an ℕ/ℚ pair) and sweeps it across the cached internlm/Lean-Workbook
`formal_statement`s. Goal: surface ACTUAL in-the-wild ℕ-truncation hazards — formalizations
whose truth value depends on the silently-chosen domain (`-` truncates at 0, `/` is floor
division over ℕ) — rather than only demonstrating the check on hand-built cases.

Pipeline per statement:
  1. extract the goal  (strip `theorem NAME <binders> :`  and the trailing `:= proof`)
  2. auto_domain_pair(goal): is it concrete arithmetic (numerals + + - * / ^ ()) carrying a
     `-` or `/`?  If not -> not a candidate (free vars / √ / choose / ascribed ℝ are excluded —
     an ℝ-ascribed statement like `(1:ℝ) - 25/64 = 39/64` is NOT pure-numeric, so it is
     correctly NOT flagged: the hazard lives only in domain-naive formalizations).
  3. for candidates, batch-probe truth over ℕ and over ℚ.  Divergence == the domain choice
     changed the claim == REFUTED-AS-CLAIMED on the fidelity axis.

We DROP `decide` on large literals (guarded by `too_big`) so the kernel never tries to unfold
an astronomically large power; those are reported separately as `skipped_large`, not silently
dropped.

AI-trust-lane artifact. Not filed claim language.
"""
import json
import os
import re
import subprocess
import sys

from lane_fidelity import auto_domain_pair, truth  # reuse the SAME detector the checker uses

HERE = os.path.dirname(os.path.abspath(__file__))
EX = os.path.join(HERE, "examples")
PROJECT = os.environ.get("MATHLIB_PROJECT", "")  # abs path to a Lean 4 project with Mathlib already built
LAKE = os.environ.get("LAKE", "lake")  # `lake` on PATH, or set LAKE=/path/to/lake
ROWS = os.path.join(EX, "_lw_rows.json")
SCAN = os.path.join(EX, "_domain_scan.lean")


def extract_goal(formal_statement):
    """`theorem NAME <binders> : GOAL := proof` -> GOAL (first depth-0 `:` after the name)."""
    fs = formal_statement.strip()
    cut = fs.find(":=")
    head = fs[:cut] if cut != -1 else fs
    depth = 0
    for i, ch in enumerate(head):
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        elif ch == ":" and depth == 0:
            return head[i + 1:].strip()
    return None


def too_big(s):
    """Literals so large that kernel `decide`/`norm_num` could blow up — exclude from probing."""
    if any(len(d) > 9 for d in re.findall(r"\d+", s)):
        return True
    # catch both `^20` and `^(2018)` — a big exponent blows up the kernel either way
    return any(int(m.group(1)) > 20 for m in re.finditer(r"\^\s*\(?\s*(\d+)", s))


def run_probes(props):
    """props: key->prop. Returns key->bool (closed cleanly, no sorryAx). norm_num/decide/simp;
    decide is safe here because too_big candidates are filtered out before probing."""
    if not props:
        return {}
    src = ["import Mathlib", "open Real Nat Finset", ""]
    for k, p in props.items():
        src.append(f"theorem {k} : {p} := by")
        # omega decides ℕ/ℤ truncated −/÷-by-literal (e.g. 2017 - 2017/3); norm_num does ℚ.
        src.append("  first | norm_num | omega | decide | simp")
        src.append(f"#print axioms {k}")
        src.append("")
    open(SCAN, "w").write("\n".join(src))
    r = subprocess.run([LAKE, "env", "lean", SCAN], cwd=PROJECT,
                       capture_output=True, text=True, timeout=1800)
    out = r.stdout + "\n" + r.stderr
    res = {}
    for k in props:
        m = re.search(rf"'{re.escape(k)}' depends on axioms:\s*\[([^\]]*)\]", out)
        res[k] = bool(m) and "sorryAx" not in m.group(1)
    return res


def main():
    path = sys.argv[1] if len(sys.argv) > 1 else ROWS
    rows = [r["row"] for r in json.load(open(path))["rows"]]
    # dedup to unique formal statements (rows are proof STEPS; many share a statement)
    seen, stmts = set(), []
    for r in rows:
        fs = (r.get("formal_statement") or "").strip()
        key = r.get("id") or fs
        if not fs or key in seen:
            continue
        seen.add(key)
        stmts.append({"id": r.get("id"), "formal_statement": fs})

    candidates, skipped_large, props = [], [], {}
    for s in stmts:
        goal = extract_goal(s["formal_statement"])
        if not goal:
            continue
        ap = auto_domain_pair(goal)
        if not ap:
            continue
        tag = (s["id"] or "anon").replace("-", "_")
        rec = {"id": s["id"], "goal": goal, "detected": f"{ap['lhs']} {ap['rel']} {ap['rhs']}"}
        if too_big(ap["lhs"] + ap["rhs"]):
            skipped_large.append(rec)
            continue
        rec["tag"] = tag
        candidates.append(rec)
        props[f"dn_{tag}_P"] = ap["natP"]
        props[f"dn_{tag}_N"] = f"¬ ({ap['natP']})"
        props[f"dq_{tag}_P"] = ap["ratP"]
        props[f"dq_{tag}_N"] = f"¬ ({ap['ratP']})"

    proved = run_probes(props)
    hazards, agree, undetermined = [], [], []
    for c in candidates:
        tN, tQ = truth(proved, f"dn_{c['tag']}"), truth(proved, f"dq_{c['tag']}")
        c["truth"] = {"ℕ": tN, "ℚ": tQ}
        if tN in ("TRUE", "FALSE") and tQ in ("TRUE", "FALSE"):
            (hazards if tN != tQ else agree).append(c)
        else:
            undetermined.append(c)

    out = {
        "dataset": f"internlm/Lean-Workbook ({len(rows)} rows from {os.path.basename(path)})",
        "toolchain": "lean 4.31.0 + mathlib",
        "detector": "lane_fidelity.auto_domain_pair (CHECK B, auto-fire)",
        "unique_statements_scanned": len(stmts),
        "closed_arith_candidates": len(candidates) + len(skipped_large),
        "probed": len(candidates),
        "skipped_large": [{"id": s["id"], "detected": s["detected"]} for s in skipped_large],
        "DOMAIN_HAZARDS": [{"id": h["id"], "detected": h["detected"], "truth": h["truth"]}
                           for h in hazards],
        "domain_safe_agree": [{"id": a["id"], "detected": a["detected"]} for a in agree],
        "undetermined_by_probe": [{"id": u["id"], "detected": u["detected"]} for u in undetermined],
        "n_hazards": len(hazards),
    }
    print(json.dumps(out, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
