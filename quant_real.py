#!/usr/bin/env python3
"""
ℝ-TYPED quantified fidelity (trust lane, Direction B extension — widening #2b).

The ℕ falsifier (`quant_falsifier.py`) can't touch real-typed statements. This scans
`theorem t (x : ℝ) ... : body` universals for genuinely-FALSE real claims: a rational witness
where the body is false is a valid counterexample to `∀ x : ℝ` (soundness: ℚ ⊂ ℝ). There is no
floor/truncation here — over ℝ the body is evaluated with exact rational arithmetic at the witness
(quant_oracle's `Q` mode equals the real value at a rational point), matching Lean's `x/0 = 0`.

Soundness discipline mirrors the ℕ case: only ℝ-ONLY binders (no Prop hypothesis that could exclude
the witness) and a bare arithmetic relation. Confirmation is by `norm_num` over ℝ (native_decide
cannot decide ℝ); a confirmed `¬ body[witness]` is a real kernel proof the universal is false.

First cut: ≤2 ℝ variables; pure +,-,*,/,^ in the bound vars (no √/trig/abs — those aren't bare
rational arithmetic). Catches wrong real inequalities / dropped side-conditions; not a full ℝ oracle.
"""
import itertools
import json
import os
import re
import subprocess
import sys
from fractions import Fraction

from quant_oracle import truth_at
from lane_fidelity import split_relation
from scan_domain_hazards import extract_goal

HERE = os.path.dirname(os.path.abspath(__file__))
PROJECT = os.environ.get("MATHLIB_PROJECT", "")
LAKE = os.environ.get("LAKE", "lake")
FULL = os.path.join(HERE, "examples", "_lw_full.json")
CONF = os.path.join(HERE, "examples", "_quant_real_confirm.lean")

ARITH = re.compile(r"^[0-9+\-*/^()\s a-zA-Z']+$")
BAD = ("→", "↔", "∧", "∨", "¬", "∃", "∀", "↦", "=>", "%", ".", "|", "√", "⌊", "⌈")
NAME = re.compile(r"[A-Za-z][A-Za-z0-9']*")
# nonzero points first, 0 last: a nonzero counterexample is more informative than a degenerate
# x/0 one (the ℝ analog of the ℕ n=0 boundary / missing `x ≠ 0` side-condition).
WITS = [Fraction(n) for n in (1, -1, 2, -2, 3, -3, 5, -5, 10)] + \
       [Fraction(1, 2), Fraction(-1, 2), Fraction(3, 2), Fraction(1, 3), Fraction(2, 3), Fraction(5, 2)] + \
       [Fraction(0)]


def real_binders(head):
    vs = []
    for grp in re.findall(r"\(([^()]*)\)", head):
        if ":" not in grp:
            return None
        names, _, ty = grp.partition(":")
        if ty.strip() != "ℝ":
            return None
        vs += names.split()
    return vs


def parse_quant_real(fs):
    fs = fs.strip()
    cut = fs.find(":=")
    head_goal = fs[:cut] if cut != -1 else fs
    depth, gi = 0, -1
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
    vs = real_binders(head)
    if vs is None:
        return None
    if goal.startswith("∀"):
        pre, _, body = goal[1:].partition(",")
        if ":" in pre:
            nm, _, ty = pre.rpartition(":")
            if ty.strip() != "ℝ":
                return None
            vs = vs + nm.replace("(", " ").replace(")", " ").split()
        goal = body.strip()
    if not vs or len(vs) > 3:           # widened to 3 ℝ vars
        return None
    if any(b in goal for b in BAD):
        return None
    sr = split_relation(goal)
    if not sr:
        return None
    lhs, rel, rhs = sr
    if not (ARITH.match(lhs) and ARITH.match(rhs)):
        return None
    if not set(NAME.findall(lhs + rhs)) <= set(vs):
        return None
    return vs, lhs, rel, rhs


POS = [w for w in WITS if w > 0]


def search_real(vs, lhs, rel, rhs):
    """First rational assignment where the body is FALSE over ℝ; (env) or None."""
    for combo in itertools.product(WITS, repeat=len(vs)):
        env = dict(zip(vs, combo))
        if truth_at(lhs, rel, rhs, "Q", env) == "FALSE":
            return env
    return None


def recovers_on_positives(vs, lhs, rel, rhs):
    """True if NO counterexample remains among all-positive witnesses — i.e. the statement holds
    for all vars > 0, so the falsity is a dropped positivity side-condition (the precise version
    of the negative-witness heuristic). False => false even on positive reals (sharper find)."""
    return not any(truth_at(lhs, rel, rhs, "Q", dict(zip(vs, c))) == "FALSE"
                   for c in itertools.product(POS, repeat=len(vs)))


def subst(expr, env):
    return re.sub(r"[A-Za-z][A-Za-z0-9']*", lambda m: f"({env[m.group(0)]})", expr)


def confirm(items):
    """norm_num `¬ body[witness]` over ℝ -> dict tag->bool (kernel-confirmed false; no sorryAx)."""
    src = ["import Mathlib", ""]
    for tag, prop in items:
        src.append(f"theorem r_{tag} : {prop} := by norm_num")
        src.append(f"#print axioms r_{tag}")
        src.append("")
    open(CONF, "w").write("\n".join(src))
    r = subprocess.run([LAKE, "env", "lean", CONF], cwd=PROJECT,
                       capture_output=True, text=True, timeout=1800)
    out = r.stdout + "\n" + r.stderr
    res = {}
    for tag, _ in items:
        m = re.search(rf"'r_{tag}' depends on axioms:\s*\[([^\]]*)\]", out)
        res[tag] = bool(m) and "sorryAx" not in m.group(1)
    return res


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
        pq = parse_quant_real(fs)
        if not pq:
            continue
        n_cand += 1
        vs, lhs, rel, rhs = pq
        env = search_real(vs, lhs, rel, rhs)
        if env is None:
            continue
        tag = (r.get("id") or "anon").replace("-", "_").replace("lean_workbook_", "")
        prop = f"¬ (({subst(lhs, env)} : ℝ) {rel} ({subst(rhs, env)} : ℝ))"
        neg = any(v < 0 for v in env.values())     # negative witness ⇒ likely dropped positivity
        pos_ok = recovers_on_positives(vs, lhs, rel, rhs)
        found.append({"id": r.get("id"), "tag": tag, "body": f"{lhs} {rel} {rhs}",
                      "witness": {k: str(v) for k, v in env.items()}, "neg_witness": neg,
                      "recovers_on_positives": pos_ok,
                      "sorry": ":= by sorry" in fs or ":=  by sorry" in fs})
        items.append((tag, prop))

    conf = confirm(items)
    for f in found:
        f["kernel_confirmed_false"] = conf.get(f["tag"], False)
    kc = [f for f in found if f["kernel_confirmed_false"]]
    out = {
        "dataset": f"internlm/Lean-Workbook ({len(seen)} unique statements)",
        "scope": "universal, ℝ-only binders, bare arithmetic relation, ≤2 vars",
        "candidates": n_cand,
        "counterexample_found": len(found),
        "KERNEL_CONFIRMED_FALSE_over_ℝ": len(kc),
        "norm_num_could_not_confirm": len(found) - len(kc),
        "of_which_sorry_stubbed": sum(f["sorry"] for f in kc),
        "RECOVERED_holds_for_vars_gt_0": sum(f["recovers_on_positives"] for f in kc),
        "false_even_on_positive_reals": sum(not f["recovers_on_positives"] for f in kc),
        "samples_false_on_positives": [{"id": f["id"], "body": f["body"], "witness": f["witness"]}
                                       for f in kc if not f["recovers_on_positives"]][:14],
    }
    print(json.dumps(out, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
