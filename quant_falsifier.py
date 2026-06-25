#!/usr/bin/env python3
"""
QUANTIFIED fidelity, first cut: counterexample search for universally-quantified arithmetic
statements that are FALSE as formalized, kernel-confirmed (trust lane, Direction B extension).

A `theorem t (n : ℕ) ... : body` is `∀ n, body`. If `body` is false at some ℕ assignment, the
theorem is FALSE — a defective formalization regardless of the author's domain intent (and if it
is `:= by sorry`-stubbed, it is mislabeled as a provable target). This is SOUND and NL-independent:
a found counterexample, once the kernel confirms `¬ body[witness]`, definitively disproves it.

To stay sound we only take statements whose binders are ALL `: ℕ` (no Prop hypotheses that could
exclude the witness) and whose goal is a single bare relation (no `→`/`∧`/…). We then split each
counterexample into ℕ-TRUNCATION-INDUCED (the body is TRUE at that point over ℚ — the floor/trunc
made it false) vs GENUINELY-FALSE (false over ℚ too).

This is a FIRST CUT of the open quantified-fidelity problem: it covers ≤2 ℕ variables and bare
relations; general claim↔formalization fidelity over ℝ with hypotheses remains open.
"""
import itertools
import json
import os
import re
import subprocess
import sys

from quant_oracle import truth_at
from lane_fidelity import split_relation
from scan_domain_hazards import extract_goal

HERE = os.path.dirname(os.path.abspath(__file__))
PROJECT = os.environ.get("MATHLIB_PROJECT", "")  # abs path to a Lean 4 + Mathlib project
LAKE = os.environ.get("LAKE", "lake")
FULL = os.path.join(HERE, "examples", "_lw_full.json")
CONF = os.path.join(HERE, "examples", "_quant_confirm.lean")

ARITH = re.compile(r"^[0-9+\-*/^()\s a-zA-Z']+$")
BAD = ("→", "↔", "∧", "∨", "¬", "∃", "∀", "↦", "=>", "%", ".")   # not a bare ℕ-arithmetic relation
NAME = re.compile(r"[A-Za-z][A-Za-z0-9']*")


def nat_binders(head):
    """All `(names : ℕ)` binder groups in `head`; None if any binder is non-ℕ (hypothesis/type)."""
    vs = []
    for grp in re.findall(r"\(([^()]*)\)", head):
        if ":" not in grp:
            return None
        names, _, ty = grp.partition(":")
        if ty.strip() != "ℕ":
            return None
        vs += names.split()
    return vs


def parse_quant(fs):
    """-> (vars, lhs, rel, rhs) for a ℕ-only, bare-relation universal; else None."""
    fs = fs.strip()
    cut = fs.find(":=")
    head_goal = fs[:cut] if cut != -1 else fs
    # split head (binders) from goal at the first depth-0 ':'
    depth = 0
    gi = -1
    for i, ch in enumerate(head_goal):
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        elif ch == ":" and depth == 0:
            gi = i
            break
    if gi == -1:
        return None
    head, goal = head_goal[:gi], head_goal[gi + 1:].strip()
    vs = nat_binders(head)
    if vs is None:
        return None
    if goal.startswith("∀"):
        pre, _, body = goal[1:].partition(",")
        if ":" in pre:
            nm, _, ty = pre.rpartition(":")
            if ty.strip() != "ℕ":
                return None
            vs = vs + nm.replace("(", " ").replace(")", " ").split()
        goal = body.strip()
    if not vs or len(vs) > 3:        # widened: up to 3 bound ℕ variables
        return None
    if any(b in goal for b in BAD):
        return None
    sr = split_relation(goal)
    if not sr:
        return None
    lhs, rel, rhs = sr
    if not (ARITH.match(lhs) and ARITH.match(rhs)):   # each side: arithmetic in the bound vars only
        return None
    body = lhs + rhs
    if "-" not in body and "/" not in body:        # need a truncation-capable op
        return None
    if not set(NAME.findall(body)) <= set(vs):     # every name must be a bound ℕ var
        return None
    return vs, lhs, rel, rhs


def _range(vs):
    return (60, 31, 15)[min(len(vs) - 1, 2)]      # 1 var:0..60, 2 vars:0..31, 3 vars:0..15


def search(vs, lhs, rel, rhs):
    """First ℕ assignment (0..R) where the body is FALSE; returns (env, q_truth) or None."""
    R = _range(vs)
    for combo in itertools.product(range(R), repeat=len(vs)):
        env = dict(zip(vs, combo))
        tN = truth_at(lhs, rel, rhs, "N", env)
        if tN == "FALSE":
            return env, truth_at(lhs, rel, rhs, "Q", env)
        if tN == "SKIP":
            return None
    return None


def recover_hypothesis(vs, lhs, rel, rhs):
    """Minimal uniform lower bound L (1..4) s.t. NO ℕ counterexample remains with every var ≥ L
    in range; None if no small hypothesis recovers it. L=1 == the classic dropped 'n ≥ 1'.
    (Search evidence over the finite window, not a proof of universal truth above L.)"""
    R = _range(vs)
    for L in range(1, 5):
        if not any(truth_at(lhs, rel, rhs, "N", dict(zip(vs, c))) == "FALSE"
                   for c in itertools.product(range(L, R), repeat=len(vs))):
            return L
    return None


def confirm(items):
    """native_decide `¬ body[witness]` over ℕ -> dict tag->bool (kernel-confirmed false)."""
    src = ["import Mathlib", ""]
    for tag, prop in items:
        src.append(f"theorem q_{tag} : {prop} := by native_decide")
        src.append(f"#print axioms q_{tag}")
        src.append("")
    open(CONF, "w").write("\n".join(src))
    r = subprocess.run([LAKE, "env", "lean", CONF], cwd=PROJECT,
                       capture_output=True, text=True, timeout=1800)
    out = r.stdout + "\n" + r.stderr
    res = {}
    for tag, _ in items:
        m = re.search(rf"'q_{tag}' depends on axioms:\s*\[([^\]]*)\]", out)
        res[tag] = bool(m) and "sorryAx" not in m.group(1)
    return res


def subst(expr, env):
    return re.sub(r"[A-Za-z][A-Za-z0-9']*", lambda m: str(env[m.group(0)]), expr)


def main():
    path = sys.argv[1] if len(sys.argv) > 1 else FULL
    rows = [r["row"] for r in json.load(open(path))["rows"]]
    seen, found, items = set(), [], []
    n_cand = 0
    for r in rows:
        fs = (r.get("formal_statement") or "").strip()
        key = r.get("id") or fs
        if not fs or key in seen:
            continue
        seen.add(key)
        pq = parse_quant(fs)
        if not pq:
            continue
        n_cand += 1
        vs, lhs, rel, rhs = pq
        hit = search(vs, lhs, rel, rhs)
        if not hit:
            continue
        env, q = hit
        tag = (r.get("id") or "anon").replace("-", "_").replace("lean_workbook_", "")
        prop = f"¬ (({subst(lhs, env)} : ℕ) {rel} ({subst(rhs, env)} : ℕ))"
        # 3-way: ℚ TRUE at the witness => the floor/trunc caused the falsity; ℚ FALSE => false in
        # the rational reading too; SKIP/N/A => can't decide ℚ (e.g. negative exponent from n-1).
        kind = ("ℕ-truncation-induced" if q == "TRUE"
                else "genuinely-false" if q == "FALSE" else "undetermined-over-ℚ")
        # MISSING-HYPOTHESIS recovery: minimal uniform lower bound L that clears all
        # counterexamples in-range. L => "false as written, but holds for all vars ≥ L"
        # (the dropped side condition); None => false throughout the window (genuinely wrong).
        L = recover_hypothesis(vs, lhs, rel, rhs)
        recov = (f"holds for {'/'.join(v + '≥' + str(L) for v in vs)}" if L
                 else "no small lower-bound hypothesis recovers it")
        found.append({"id": r.get("id"), "tag": tag, "vars": vs, "body": f"{lhs} {rel} {rhs}",
                      "witness": env, "q_truth_at_witness": q, "kind": kind,
                      "recover_L": L, "recovered": recov,
                      "sorry": ":= by sorry" in fs or ":=  by sorry" in fs})
        items.append((tag, prop))

    conf = confirm(items)
    for f in found:
        f["kernel_confirmed_false"] = conf.get(f["tag"], False)
    kc = [f for f in found if f["kernel_confirmed_false"]]
    recoverable = [f for f in kc if f["recover_L"] is not None]
    out = {
        "dataset": f"internlm/Lean-Workbook ({len(seen)} unique statements)",
        "scope": "universal, ℕ-only binders, bare arithmetic relation with −/÷, ≤3 vars",
        "candidates": n_cand,
        "counterexample_found": len(found),
        "KERNEL_CONFIRMED_FALSE": len(kc),
        "of_which_truncation_induced": sum(f["kind"] == "ℕ-truncation-induced" for f in kc),
        "of_which_genuinely_false_over_ℚ": sum(f["kind"] == "genuinely-false" for f in kc),
        "of_which_undetermined_over_ℚ": sum(f["kind"] == "undetermined-over-ℚ" for f in kc),
        "of_which_sorry_stubbed": sum(f["sorry"] for f in kc),
        "MISSING_HYPOTHESIS_recoverable": len(recoverable),
        "recover_L_distribution": {str(L): sum(f["recover_L"] == L for f in kc) for L in (1, 2, 3, 4)},
        "false_throughout_window": len(kc) - len(recoverable),
        # GENUINE missing-hypothesis = recovery on a case that is also false over ℚ (so the
        # lower bound is a real dropped side-condition, not just the ℕ floor collapsing to 1≤1).
        "genuine_missing_hypothesis": sum((f["recover_L"] is not None) and f["kind"] == "genuinely-false" for f in kc),
        "recovery_is_floor_artifact": sum((f["recover_L"] is not None) and f["kind"] == "ℕ-truncation-induced" for f in kc),
        "domain_bug_not_hypothesis": sum((f["recover_L"] is None) and f["kind"] == "ℕ-truncation-induced" for f in kc),
        "genuinely_wrong_math": sum((f["recover_L"] is None) and f["kind"] == "genuinely-false" for f in kc),
        "samples": [{"id": f["id"], "body": f["body"], "witness": f["witness"],
                     "kind": f["kind"], "recovered": f["recovered"]} for f in kc],
    }
    print(json.dumps(out, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
