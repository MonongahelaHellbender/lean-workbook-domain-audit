#!/usr/bin/env python3
"""
ℝ universals WITH HYPOTHESES (trust lane, Direction B — frontier widening #2c).

quant_real.py only handles hypothesis-free universals. Most of the corpus has constraints —
`theorem t (x : ℝ) (h : 0 < x) : body` (== `∀ x, 0 < x → body`), or `∀ x, H → body` in the goal.
We now handle them SOUNDLY: a witness disproves `∀ x, H → body` iff it makes H TRUE and body FALSE
(then `H → body` is false there). So we (1) parse the hypotheses (from Prop binders AND from goal
antecedents split on top-level `→`), each a conjunction of arithmetic relations, (2) search rational
witnesses where every hypothesis holds and the body is false, (3) confirm in Lean with norm_num that
`H(w) ∧ ¬body(w)`.

These are SHARPER than the hypothesis-free finds: the formalization is false *even with the stated
constraint*, so it is either a genuine error or still missing a further side-condition — not just a
dropped positivity. ℝ-typed vars only, ≤2 vars, bare arithmetic; norm_num confirmation (ℝ).
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

HERE = os.path.dirname(os.path.abspath(__file__))
PROJECT = os.environ.get("MATHLIB_PROJECT", "")
LAKE = os.environ.get("LAKE", "lake")
FULL = os.path.join(HERE, "examples", "_lw_full.json")
CONF = os.path.join(HERE, "examples", "_quant_hyp_confirm.lean")

ARITH = re.compile(r"^[0-9+\-*/^()\s a-zA-Z']+$")
RELSET = ("≠", "≤", "≥", "=", "<", ">")
BADREL = ("↔", "∨", "¬", "∃", "∀", "↦", "=>", "%", ".", "|", "√", "⌊", "⌈")
NAME = re.compile(r"[A-Za-z][A-Za-z0-9']*")
WITS = [Fraction(n) for n in (1, -1, 2, -2, 3, -3, 5, -5, 10)] + \
       [Fraction(1, 2), Fraction(-1, 2), Fraction(3, 2), Fraction(1, 3), Fraction(2, 3), Fraction(5, 2),
        Fraction(0)]


def split_top(s, sep):
    """Split `s` on top-level (bracket-depth 0) occurrences of single-char `sep`."""
    out, depth, last = [], 0, 0
    for i, ch in enumerate(s):
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        elif ch == sep and depth == 0:
            out.append(s[last:i])
            last = i + 1
    out.append(s[last:])
    return out


def as_relation(seg, vs):
    """Parse `seg` into (lhs, rel, rhs) of arithmetic in vs, or None."""
    seg = seg.strip()
    if any(b in seg for b in BADREL):
        return None
    sr = split_relation(seg)
    if not sr:
        return None
    lhs, rel, rhs = sr
    if not (ARITH.match(lhs) and ARITH.match(rhs)):
        return None
    if not set(NAME.findall(lhs + rhs)) <= set(vs):
        return None
    return lhs, rel, rhs


def parse_conj(prop, vs):
    """Conjunction of arithmetic relations -> list[(lhs,rel,rhs)] or None."""
    rels = []
    for part in split_top(prop, "∧"):
        r = as_relation(part, vs)
        if r is None:
            return None
        rels.append(r)
    return rels


def parse_with_hyps(fs):
    """-> (vars, hyps, body=(lhs,rel,rhs)) for an ℝ universal WITH ≥1 hypothesis, else None."""
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
    vs, hyp_props = [], []
    for grp in re.findall(r"\(([^()]*)\)", head):           # binders
        if ":" not in grp:
            return None
        names, _, ty = grp.partition(":")
        ty = ty.strip()
        if ty == "ℝ":
            vs += names.split()
        else:
            hyp_props.append(ty)                            # a Prop hypothesis binder
    # leading ∀ in the goal
    while goal.startswith("∀"):
        pre, _, rest = goal[1:].partition(",")
        if ":" in pre:
            nm, _, ty = pre.rpartition(":")
            if ty.strip() != "ℝ":
                return None
            vs += nm.replace("(", " ").replace(")", " ").split()
        goal = rest.strip()
    # goal antecedents: H1 → H2 → ... → body
    parts = split_top(goal, "→")
    hyp_props += [p.strip() for p in parts[:-1]]
    body_seg = parts[-1]
    if not vs or len(vs) > 3 or not hyp_props:      # widened to 3 ℝ vars
        return None
    hyps = []
    for hp in hyp_props:
        rels = parse_conj(hp, vs)
        if rels is None:
            return None
        hyps += rels
    body = as_relation(body_seg, vs)
    if body is None:
        return None
    return vs, hyps, body


def hyps_hold(hyps, env):
    return all(truth_at(l, rel, r, "Q", env) == "TRUE" for (l, rel, r) in hyps)


def search(vs, hyps, body):
    """First witness satisfying all hyps where body is FALSE; or None."""
    bl, brel, br = body
    for combo in itertools.product(WITS, repeat=len(vs)):
        env = dict(zip(vs, combo))
        if hyps_hold(hyps, env) and truth_at(bl, brel, br, "Q", env) == "FALSE":
            return env
    return None


def subst(expr, env):
    return re.sub(r"[A-Za-z][A-Za-z0-9']*", lambda m: f"({env[m.group(0)]})", expr)


def confirm(items):
    """norm_num that H(w) ∧ ¬body(w) over ℝ -> tag->bool (kernel-confirmed, no sorryAx)."""
    src = ["import Mathlib", ""]
    for tag, prop in items:
        src.append(f"theorem h_{tag} : {prop} := by norm_num")
        src.append(f"#print axioms h_{tag}")
        src.append("")
    open(CONF, "w").write("\n".join(src))
    r = subprocess.run([LAKE, "env", "lean", CONF], cwd=PROJECT,
                       capture_output=True, text=True, timeout=1800)
    out = r.stdout + "\n" + r.stderr
    res = {}
    for tag, _ in items:
        m = re.search(rf"'h_{tag}' depends on axioms:\s*\[([^\]]*)\]", out)
        res[tag] = bool(m) and "sorryAx" not in m.group(1)
    return res


def rel_lean(triple, env):
    l, rel, r = triple
    return f"(({subst(l, env)} : ℝ) {rel} ({subst(r, env)} : ℝ))"


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
        pq = parse_with_hyps(fs)
        if not pq:
            continue
        n_cand += 1
        vs, hyps, body = pq
        env = search(vs, hyps, body)
        if env is None:
            continue
        tag = (r.get("id") or "anon").replace("-", "_").replace("lean_workbook_", "")
        conj = " ∧ ".join(rel_lean(h, env) for h in hyps)
        prop = f"{conj} ∧ ¬ {rel_lean(body, env)}"
        found.append({"id": r.get("id"), "tag": tag,
                      "hyps": " ∧ ".join(f"{l} {rl} {rr}" for (l, rl, rr) in hyps),
                      "body": f"{body[0]} {body[1]} {body[2]}",
                      "witness": {k: str(v) for k, v in env.items()},
                      "sorry": ":= by sorry" in fs or ":=  by sorry" in fs})
        items.append((tag, prop))

    conf = confirm(items)
    for f in found:
        f["kernel_confirmed_false"] = conf.get(f["tag"], False)
    kc = [f for f in found if f["kernel_confirmed_false"]]
    out = {
        "dataset": f"internlm/Lean-Workbook ({len(seen)} unique statements)",
        "scope": "ℝ universals WITH hypotheses (Prop binders ∨ goal antecedents), ≤2 vars",
        "candidates_with_hypotheses": n_cand,
        "counterexample_found": len(found),
        "KERNEL_CONFIRMED_FALSE_despite_hypothesis": len(kc),
        "norm_num_could_not_confirm": len(found) - len(kc),
        "of_which_sorry_stubbed": sum(f["sorry"] for f in kc),
        "samples": [{"id": f["id"], "hyps": f["hyps"], "body": f["body"], "witness": f["witness"]}
                    for f in kc[:16]],
    }
    print(json.dumps(out, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
