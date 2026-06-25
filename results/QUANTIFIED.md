# Quantified false-universals in internlm/Lean-Workbook

Beyond the 49 closed-arithmetic hazards, the quantified checkers find **universally-quantified statements that are FALSE as formalized**, each disproved by a kernel-confirmed counterexample. A `theorem t (n : ℕ) … : body` means `∀ n, body`; a witness where `body` is false disproves it (for hypotheses `∀ x, H → body`, the witness must also satisfy `H`).

## Over ℕ — 27 false universals (native_decide)

- **5 genuine missing-hypothesis** (recoverable by a lower bound, e.g. `holds for n≥3`) · **5 domain bugs** · **13 genuinely wrong** (e.g. `2016²−2015·2017=2026`).

## Over ℝ, NO hypothesis — 320 false universals (norm_num)

From 1330 candidates (≤3 vars). Split by positivity-recovery: **169 hold for all vars > 0** (dropped positivity, recoverable) · **151 false even on positive reals** (sharper — missing an upper-bound/range, or genuine errors).

## Over ℝ, WITH hypothesis — the CONTROL: 16 of 723 false

When the formalization KEEPS the constraint (`∀ x, H → body`, H from a Prop binder or a goal antecedent), a counterexample must satisfy `H` and falsify `body`; confirmed by `norm_num` that `H(w) ∧ ¬body(w)`. **Almost none are false** — e.g. `plus_46825`: `x²−7 = x−1 ⊢ x²−x−8 = 0`, false at the hypothesis's own root x=−2 (the conclusion should be `x²−x−6=0`).

### The thesis, in one comparison

| | candidates | false | rate |
|---|---|---|---|
| ℝ universals, **no** hypothesis | 1330 | 320 | **24%** |
| ℝ universals, **with** hypothesis | 723 | 16 | **2%** |

Dropping the side-condition breaks the formalization; keeping it makes it almost always faithful. **The defect family is dropped side-conditions, not wrong mathematics** — every counterexample kernel-confirmed. Combined with the 49 closed-arithmetic hazards, that's **412 kernel-confirmed fidelity findings** in this corpus.

*Honest caveat:* the with-hypothesis search is incomplete for equality / measure-zero constraints (discrete rational witnesses rarely satisfy `a+b+c=1`-type hypotheses), so the 'with hypothesis' count is a lower bound — but the inequality-constrained statements are fully searchable and hold up.

