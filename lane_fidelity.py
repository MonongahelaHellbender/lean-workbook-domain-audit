#!/usr/bin/env python3
"""
Trust lane — STATEMENT-FIDELITY checker (Direction B), non-toy prototype.

The load-bearing insight of the whole trust lane: *the verification gap is usually in the
STATEMENT, not the proof.* A kernel-clean proof can certify a subtly weaker / restated /
vacuous / wrong-domain claim. This checker runs FOUR checks on the FORMAL statement, and is
explicit about which are SOUND (a firing is a real defect) vs HEURISTIC.

  CHECK A — VACUITY (SOUND).  Lean proves the hypotheses unsatisfiable (`∀ vars, ¬H`) -> the
            theorem is vacuously true, proves nothing.

  CHECK B — DOMAIN MISMATCH (SOUND, NEW; motivated by REAL Lean-Workbook failures plus_48 /
            plus_220 / plus_246).  Autoformalizers often render real/rational arithmetic over ℕ,
            where `-` truncates at 0 and `/` is floor division -- silently a DIFFERENT theorem.
            We mechanically evaluate the statement's truth at ℕ and at ℚ; if they DIVERGE, the
            chosen domain changed the claim.  e.g. `1 - 25/64 = 39/64` is TRUE over ℚ, FALSE over ℕ.

  CHECK C — QUANTIFIER-PREFIX STRENGTH (HEURISTIC).  Compare the ∀/∃ prefix of the proved
            statement vs a reference formalization. Dropping a leading ∀ = strict weakening.

  CHECK D — CONNECTIVE DOWNGRADE (HEURISTIC, NEW; motivated by "solve for x" cases like plus_2).
            If the claim asks to CHARACTERIZE / solve (iff intended) but the formal statement's
            principal connective is `→` not `↔`, only one direction was proved.

WHY NOT just ask Lean to prove `proved -> claim`?  When the claim is independently true,
`anything -> claim` is provable: the test always passes and measures nothing. That confounder
is why naive "does the proof imply the claim" fidelity checking is broken.

Verdicts (statement-fidelity axis only -- NOT whether the theorem is proved):
  REFUTED-AS-CLAIMED  any sound probe fires, or a structural downgrade is detected
  SUPPORTED           nothing fires and structure matches  (read: "fidelity not refuted",
                      NOT a proof of semantic equivalence)
  NEEDS-QUERY         can't classify

AI-trust-lane artifact. Not filed claim language.
"""
import json
import os
import re
import subprocess

HERE = os.path.dirname(os.path.abspath(__file__))
EX = os.path.join(HERE, "examples")
PROJECT = os.environ.get("MATHLIB_PROJECT", "")  # abs path to a Lean 4 project with Mathlib already built
LAKE = os.environ.get("LAKE", "lake")  # `lake` on PATH, or set LAKE=/path/to/lake
PROBES = os.path.join(EX, "_fidelity_probes.lean")
CHAR_WORDS = ("solve", "all solutions", "if and only if", "iff", "exactly when",
              "characteri", "necessary and sufficient", "the set of", "precisely")


# ---- batched Lean probe runner (one compile for every needed Prop) -------------------------

def run_probes(props):
    """props: dict key->lean_prop. Returns dict key->bool (closed cleanly, no sorryAx)."""
    if not props:
        return {}
    src = ["import Mathlib", "open Real Nat Finset", ""]
    for k, p in props.items():
        src.append(f"theorem {k} : {p} := by")
        src.append("  first | norm_num | decide | simp | omega | tauto")
        src.append(f"#print axioms {k}")
        src.append("")
    open(PROBES, "w").write("\n".join(src))
    r = subprocess.run([LAKE, "env", "lean", PROBES], cwd=PROJECT,
                       capture_output=True, text=True, timeout=1200)
    out = r.stdout + "\n" + r.stderr
    res = {}
    for k in props:
        m = re.search(rf"'{re.escape(k)}' depends on axioms:\s*\[([^\]]*)\]", out)
        res[k] = bool(m) and "sorryAx" not in m.group(1)
    return res


def truth(proved, key):
    if proved.get(key + "_P"):
        return "TRUE"
    if proved.get(key + "_N"):
        return "FALSE"
    return "UNKNOWN"


# ---- structural helpers --------------------------------------------------------------------

def quant_prefix(s):
    seq, i, s = [], 0, s.strip()
    while i < len(s):
        while i < len(s) and s[i].isspace():
            i += 1
        if i < len(s) and s[i] in "∀∃":
            seq.append(s[i])
            j = s.find(",", i)
            if j == -1:
                break
            i = j + 1
        else:
            break
    return "".join(seq)


def prefix_relation(proved_stmt, reference):
    pp, pr = quant_prefix(proved_stmt), quant_prefix(reference)
    if pp == pr:
        return "MATCH", f"quantifier prefix matches reference ('{pp or '∅'}')"
    if pr.endswith(pp) and set(pr[:len(pr) - len(pp)]) <= {"∀"}:
        return "WEAKER", f"proved prefix '{pp}' drops leading ∀ vs reference '{pr}' (instance, not universal)"
    if pp.endswith(pr) and set(pp[:len(pp) - len(pr)]) <= {"∀"}:
        return "STRONGER", f"proved prefix '{pp}' adds leading ∀ vs reference '{pr}' (proved more than claimed)"
    return "INCOMPARABLE", f"proved prefix '{pp}' vs reference '{pr}' — not classifiable"


def connective_issue(claim, proved_stmt):
    wants_iff = any(w in claim.lower() for w in CHAR_WORDS)
    has_iff = "↔" in proved_stmt
    has_imp = "→" in proved_stmt or "->" in proved_stmt
    if wants_iff and has_imp and not has_iff:
        return "claim asks to characterize/solve (↔ intended) but formal statement uses → only — one direction"
    return None


# ---- AUTO domain-hazard detection ----------------------------------------------------------
# Fires CHECK B without being handed the ℕ/ℚ pair: parse the statement, and if it is concrete
# arithmetic carrying a truncation-capable op (`-` or `/`), build the ℕ- and ℚ-ascribed forms
# ourselves. `-` truncates at 0 over ℕ and `/` is floor division, so the domain choice can
# silently change the claim. We only target sides built from numerals + + - * / ^ ( ) — exactly
# the things ℕ/ℚ ascription is well-defined on (this deliberately excludes `choose`, `√`, `π`,
# and free variables, which aren't simply re-ascribable).

RELS = ("≠", "≤", "≥", "=", "<", ">")          # principal relations we split on (skip →, ↔, ∈)
# No `.`: a decimal literal (e.g. 33.5) has NO ℕ interpretation, so it cannot be an ℕ-truncation
# hazard — its presence already signals a rational/real reading. Excluding it also stops the
# ℕ-probe from failing to typecheck (which previously showed up as "undetermined", not a hazard).
NUM_RE = re.compile(r"[0-9+\-*/^()\s]+")
TRUNC_OPS = ("-", "/")


def is_pure_numeric(s):
    return bool(NUM_RE.fullmatch(s)) and any(ch.isdigit() for ch in s)


def split_relation(prop):
    """First depth-0 relation in `prop` -> (lhs, rel, rhs), else None."""
    depth = 0
    for i, ch in enumerate(prop):
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        elif depth == 0 and ch in RELS:
            return prop[:i].strip(), ch, prop[i + 1:].strip()
    return None


def auto_domain_pair(prop):
    """If `prop` is concrete arithmetic with a truncation op, return the ℕ/ℚ probe pair."""
    if not prop:
        return None
    sr = split_relation(prop)
    if not sr:
        return None
    lhs, rel, rhs = sr
    if not (is_pure_numeric(lhs) and is_pure_numeric(rhs)):
        return None
    if not any(op in (lhs + rhs) for op in TRUNC_OPS):
        return None  # no `-`/`/` => no truncation hazard from this check
    return {"lhs": lhs, "rel": rel, "rhs": rhs,
            "natP": f"(({lhs}) : ℕ) {rel} (({rhs}) : ℕ)",
            "ratP": f"(({lhs}) : ℚ) {rel} (({rhs}) : ℚ)"}


def domain_pair(c):
    """ℕ/ℚ probe pair for CHECK B: explicit `domain` override, else auto from proved_stmt."""
    d = c.get("domain")
    if d:
        return {"natP": f"(({d['lhs']}) : ℕ) {d['rel']} (({d['rhs']}) : ℕ)",
                "ratP": f"(({d['lhs']}) : ℚ) {d['rel']} (({d['rhs']}) : ℚ)"}
    return auto_domain_pair(c.get("proved_stmt", ""))


# ---- per-case assessment -------------------------------------------------------------------

def collect_probes(cases):
    """Build the full Prop dict so ALL Lean checks compile in ONE pass."""
    props = {}
    for c in cases:
        if c.get("vacuity_probe"):
            props[f"vac_{c['name']}"] = c["vacuity_probe"]
        dp = domain_pair(c)
        if dp:
            props[f"dn_{c['name']}_P"] = dp["natP"]
            props[f"dn_{c['name']}_N"] = f"¬ ({dp['natP']})"
            props[f"dq_{c['name']}_P"] = dp["ratP"]
            props[f"dq_{c['name']}_N"] = f"¬ ({dp['ratP']})"
    return props


def assess(c, proved):
    res = {"name": c["name"], "claim": c["claim"]}
    findings = []
    # CHECK A — vacuity (sound)
    if c.get("vacuity_probe"):
        if proved.get(f"vac_{c['name']}"):
            findings.append(("REFUTED-AS-CLAIMED",
                             "VACUITY (sound): Lean proves the hypotheses unsatisfiable — theorem is vacuous."))
        res["vacuity"] = "hypotheses unsatisfiable" if proved.get(f"vac_{c['name']}") else "not refuted"
    # CHECK B — domain mismatch (sound; auto-fires on concrete −/÷ arithmetic)
    dp = domain_pair(c)
    if dp:
        tN, tQ = truth(proved, f"dn_{c['name']}"), truth(proved, f"dq_{c['name']}")
        res["domain_probe"] = {"detected": f"{dp['lhs']} {dp['rel']} {dp['rhs']}",
                               "truth": {"ℕ": tN, "ℚ": tQ}}
        if tN in ("TRUE", "FALSE") and tQ in ("TRUE", "FALSE") and tN != tQ:
            findings.append(("REFUTED-AS-CLAIMED",
                             f"DOMAIN MISMATCH (sound): statement is {tN} over ℕ but {tQ} over ℚ — the ℕ "
                             "encoding (truncated −/÷) changed the claim."))
    # CHECK C — quantifier-prefix strength (heuristic)
    if c.get("reference_stmt"):
        rel, why = prefix_relation(c["proved_stmt"], c["reference_stmt"])
        res["strength_relation"] = rel
        if rel == "WEAKER":
            findings.append(("REFUTED-AS-CLAIMED", f"DOWNGRADE (structural): {why}"))
        elif rel == "INCOMPARABLE":
            findings.append(("NEEDS-QUERY", why))
    # CHECK D — connective downgrade (heuristic)
    if c.get("proved_stmt"):
        ci = connective_issue(c["claim"], c["proved_stmt"])
        if ci:
            findings.append(("REFUTED-AS-CLAIMED", f"CONNECTIVE DOWNGRADE (structural): {ci}"))
    # aggregate
    if any(v == "REFUTED-AS-CLAIMED" for v, _ in findings):
        res["verdict"] = "REFUTED-AS-CLAIMED"
    elif any(v == "NEEDS-QUERY" for v, _ in findings):
        res["verdict"] = "NEEDS-QUERY"
    else:
        res["verdict"] = "SUPPORTED"
    res["why"] = [w for _, w in findings] or ["no fidelity defect detected (NB: not a proof of semantic equivalence)"]
    return res


CASES = [
    # A) VACUOUS hypothesis (n < n unsatisfiable).
    {"name": "vacuous_hyp",
     "claim": "for every n, if n < n then n = n + 1 (a 'theorem')",
     "proved_stmt": "∀ n : ℕ, n < n → n = n + 1",
     "vacuity_probe": "∀ n : ℕ, ¬ (n < n)"},

    # B1) DOMAIN MISMATCH — floor division (the plus_48 pattern). TRUE over ℚ, FALSE over ℕ.
    #     proved_stmt is the BARE statement; CHECK B auto-detects the −/÷ and builds the pair.
    {"name": "domain_floor_div",
     "claim": "1 - 25/64 = 39/64 (intended as real arithmetic)",
     "proved_stmt": "1 - 25/64 = 39/64"},

    # B2) DOMAIN MISMATCH — truncated subtraction. 5 - 8 = 0 over ℕ (TRUE), ≠ 0 over ℚ (FALSE).
    {"name": "domain_trunc_sub",
     "claim": "5 - 8 = 0 (intended over the integers/reals, where it is false)",
     "proved_stmt": "5 - 8 = 0"},

    # B3) DOMAIN OK — division that agrees across ℕ and ℚ (6/3 = 2 both ways). Auto-detector
    #     fires (there is a `/`) but finds NO divergence -> correctly not flagged.
    {"name": "domain_ok",
     "claim": "6 / 3 = 2",
     "proved_stmt": "6 / 3 = 2"},

    # B4) REAL-DATA regression fixture — internlm/Lean-Workbook lean_workbook_plus_893, VERBATIM.
    #     A probability identity (rational) formalized with no ascription, so it lives over ℕ where
    #     it is FALSE. Auto-detector must keep catching this. -> REFUTED-AS-CLAIMED (ℕ F / ℚ T).
    {"name": "real_lw893_domain",
     "claim": "Lean-Workbook plus_893: 1 - (6+4)/36 - (1+4+1)/36 = 5/9 (a probability, rational)",
     "proved_stmt": "1 - (6 + 4) / 36 - (1 + 4 + 1) / 36 = 5 / 9"},

    # B5) REAL-DATA fixture #2 — Lean-Workbook plus_26988, VERBATIM. ℕ FLOOR DIVISION makes it
    #     TRUE over ℕ (2017 - 672 = 1345) but FALSE over ℚ (2017 - 2017/3 = 4034/3). A distinct
    #     mechanism from plus_893 (here ℕ is the "true" side). -> REFUTED-AS-CLAIMED.
    {"name": "real_lw26988_domain",
     "claim": "Lean-Workbook plus_26988: 2017 - 2017/3 = 1345 (intended over ℝ/ℚ, where it is false)",
     "proved_stmt": "2017 - (2017 / 3) = 1345"},

    # C) DOWNGRADE — infinitude of primes formalized as a single existence.
    {"name": "prime_downgrade",
     "claim": "there are infinitely many primes (for every N, a prime ≥ N exists)",
     "proved_stmt": "∃ p : ℕ, Nat.Prime p",
     "reference_stmt": "∀ N : ℕ, ∃ p : ℕ, N ≤ p ∧ Nat.Prime p"},

    # D1) CONNECTIVE DOWNGRADE — "solve" wants ↔ but only → is proved (one direction).
    {"name": "solve_one_direction",
     "claim": "solve x^2 - 2x - 24 < 0 (characterize all real x)",
     "proved_stmt": "∀ x : ℝ, x^2 - 2*x - 24 < 0 → x ∈ Set.Ioo (-4) 6"},

    # D2) CONNECTIVE OK — same claim, faithful ↔ (this is what lean_workbook_plus_2 actually did).
    {"name": "solve_iff",
     "claim": "solve x^2 - 2x - 24 < 0 (characterize all real x)",
     "proved_stmt": "∀ x : ℝ, x^2 - 2*x - 24 < 0 ↔ x ∈ Set.Ioo (-4) 6"},
]


def main():
    proved = run_probes(collect_probes(CASES))
    out = {"lane": "statement-fidelity (Direction B, non-toy prototype)",
           "toolchain": "lean 4.31.0 + mathlib",
           "sound_checks": ["vacuity probe", "domain (ℕ vs ℚ) mismatch"],
           "heuristic_checks": ["quantifier-prefix strength", "connective ↔/→ downgrade"],
           "claims": [assess(c, proved) for c in CASES]}
    print(json.dumps(out, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
