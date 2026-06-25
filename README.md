# Lean-Workbook domain-fidelity audit

A reproducible, kernel-validated audit of **domain-fidelity bugs** in
[`internlm/Lean-Workbook`](https://huggingface.co/datasets/internlm/Lean-Workbook), a widely-used
autoformalized theorem-proving corpus.

**Finding:** across 13,517 unique statements, the checkers flag **167 statements that claim
something other than their evident intent**, every one independently confirmed by the Lean 4
kernel:

- **49 closed-arithmetic domain hazards** (a silent ℕ/ℚ or exponent-truncation domain choice
  flips the truth value) — see [`results/HAZARDS.md`](results/HAZARDS.md);
- **27 false universals over ℕ** + **91 false universals over ℝ** (a quantified statement that is
  false as formalized, disproved by a kernel-confirmed counterexample) — see
  [`results/QUANTIFIED.md`](results/QUANTIFIED.md).

These are defective formalizations: false (or vacuously true) as written, the great majority
`:= by sorry`-stubbed (so presented as provable targets). This is the "the verification gap is in
the *statement*, not the proof" thesis, measured on real third-party data: an autoformalizer can
hand you a perfectly checkable proof of a subtly *wrong* statement, and "did it compile?" will
never catch it.

**The recurring, honest lesson:** "false as formalized" is dominated by *dropped side-conditions*
(a missing domain ascription, or a missing `n ≥ 1` / `a,b,c ≥ 0`), not by wrong mathematics — and
the checkers *recover* those side-conditions automatically where they exist.

## The two defect classes

**1. ℕ vs ℚ divergence (42).** Real/rational arithmetic rendered over ℕ, where `-` truncates at 0
and `/` is floor division — silently a different theorem.

> `lean_workbook_plus_893 : 1 - (6 + 4) / 36 - (1 + 4 + 1) / 36 = 5 / 9`

A probability identity (true over ℚ: `20/36 = 5/9`). Over ℕ every division floors to 0, so the
left side is `1` and the right is `0`: the statement is **`1 = 0`**, false — and `sorry`-stubbed.

**2. Exponent truncation (7).** A fractional exponent (`x^(1/3)` = a real root). Lean's `^` wants a
ℕ exponent, so `1/3` floors to `0` and `x^(1/3)` becomes `x^0 = 1` — a different statement.

> `lean_workbook_plus_18325 : 12^(1 / 2) > 45 / 13`

Intended: `√12 ≈ 3.4641 > 3.4615`, true. As Lean reads it: `12^0 = 1 > 3`, **false**.

Full verified list: [`results/HAZARDS.md`](results/HAZARDS.md) ·
machine-readable: [`results/hazards.json`](results/hazards.json).

## Why you can trust the count

The hazard verdicts come from an exact Python dual-semantics evaluator, but **it is never trusted
on its own**:

- **Validated against the Lean kernel.** On every candidate the kernel can independently decide,
  the oracle's verdict is cross-checked: **91/91 agreement, 0 conflicts**.
- **The 42 ℕ/ℚ hazards are fully confirmed in Lean** — *both* the ℕ and ℚ verdicts proven: 8 by
  the standard kernel probe, 34 by `native_decide` (kernel + compiler; reported as its own trust
  tier, not folded into the trusted axiom base `{propext, Classical.choice, Quot.sound}`).
- **The 7 exponent-truncation hazards** compare two readings: the *as-formalized* verdict is proven
  by `native_decide`; the *intended-ℝ* verdict comes from the rigorous real oracle below (not the
  kernel). A hazard is a definite disagreement between the two.
- The real-domain oracle is **rigorous**: `mpmath.iv` interval arithmetic returns an inequality
  verdict only from disjoint enclosures (precision raised 50→150→500 digits, else it abstains),
  and `sympy.equals` for radical identities. It never reports a floating-point guess.

## Components

| file | role |
|---|---|
| `domain_oracle.py` | exact ℕ/ℚ dual-semantics evaluator (truncated `-`, floor `/`, `x/0=0`) |
| `real_oracle.py` | rigorous real-domain oracle (`mpmath.iv` intervals + `sympy`) |
| `lane_fidelity.py` | the statement-fidelity checker (auto-detects the hazards; demo battery) |
| `scan_domain_hazards.py` | scans a row file for closed-arithmetic candidates |
| `census_oracle.py` | exact ℕ/ℚ census, validated vs the kernel + `native_decide` |
| `census_real.py` | exponent-truncation census (as-formalized vs intended-ℝ) |
| `quant_oracle.py` | variable-aware ℕ/ℚ evaluator (for quantified statements) |
| `quant_falsifier.py` | ℕ false-universal search + missing-hypothesis recovery (native_decide) |
| `quant_real.py` | ℝ false-universal search + positivity recovery (norm_num) |
| `fetch_lw_parquet.py` | downloads the dataset (one parquet; avoids the paged-API rate limit) |

## Reproduce

Requires Python (`pip install -r requirements.txt`) and a Lean 4 + Mathlib project already built
(for the kernel cross-checks). Point the scripts at it:

```bash
export MATHLIB_PROJECT=/abs/path/to/a/lean/project/with/mathlib   # has .lake/ built
export LAKE=lake                                                  # or /abs/path/to/lake

python fetch_lw_parquet.py        # -> examples/_lw_full.json
python census_oracle.py examples/_lw_full.json   # 42 ℕ/ℚ hazards, kernel-validated
python census_real.py             # 7 exponent-truncation hazards (needs mpmath+sympy)
python lane_fidelity.py           # the fidelity checker's demo battery (incl. 2 real fixtures)
python quant_falsifier.py examples/_lw_full.json   # 27 ℕ false universals + hypothesis recovery
python quant_real.py examples/_lw_full.json        # 91 ℝ false universals + positivity recovery
```

The oracles run standalone without Lean (`python domain_oracle.py`, `python real_oracle.py` run
their self-tests); Lean is only used to *confirm* the findings.

## Honest limits

- **Scope.** The exact oracles cover *closed* arithmetic (202 of 13,517 statements). General
  claim↔formalization fidelity for quantified statements over ℝ remains open.
- **Unclassified.** 10 candidates use unary minus (`-x`), which is ill-typed over ℕ; left as a
  separate class, not counted.
- **TCB.** `native_decide` adds the Lean compiler (`Lean.ofReduceBool`) to the trusted base; it is
  reported as a distinct tier. The real oracle adds `mpmath` + `sympy`, used only for the 7
  exponent cases and bounded by rigorous intervals where possible.
- During development the harness caught a `sorryAx`-smuggling bug *in its own checker* (a failed
  `native_decide` error-recovers with `sorry`, and `#print axioms` still prints a line). It is
  fixed — and it is exactly the failure mode this audit demonstrates: an axiom audit beats "did it
  compile."

## Author / license

Melissa Ellison. MIT License (see `LICENSE`). If you build on this, a citation or link back is
appreciated.
