# Quantified false-universals in internlm/Lean-Workbook

Beyond the 49 closed-arithmetic hazards, the quantified checkers find **universally-quantified statements that are FALSE as formalized**, each disproved by a kernel-confirmed counterexample. A `theorem t (n : ℕ) … : body` means `∀ n, body`; a witness where `body` is false disproves it (for hypotheses `∀ x, H → body`, the witness must also satisfy `H`).

## Over ℕ — 31 false universals (native_decide)

- **7 genuine missing-hypothesis** (recoverable by a lower bound, e.g. `holds for n≥3`) · **5 domain bugs** · **15 genuinely wrong** (e.g. `2016²−2015·2017=2026`) · the remainder ℕ-truncation-induced / undetermined-over-ℚ.

## Over ℝ, NO hypothesis — 335 false universals (norm_num)

From 1401 candidates (≤3 vars). Split by positivity-recovery: **177 hold for all vars > 0** (dropped positivity, recoverable) · **158 false even on positive reals** (sharper — missing an upper-bound/range, or genuine errors).

## Over ℝ, WITH hypothesis — the CONTROL: 119 of 2187 false

When the formalization KEEPS the constraint (`∀ x, H → body`, H from a Prop binder or a goal antecedent), a counterexample must satisfy `H` and falsify `body`; confirmed by `norm_num` that `H(w) ∧ ¬body(w)`. **Far fewer are false (5.4%)** than without the constraint (24%) — e.g. `plus_46825`: `x²−7 = x−1 ⊢ x²−x−8 = 0`, false at the hypothesis's own root x=−2 (the conclusion should be `x²−x−6=0`).

### The thesis, in one comparison

| | candidates | false | rate |
|---|---|---|---|
| ℝ universals, **no** hypothesis | 1401 | 335 | **24%** |
| ℝ universals, **with** hypothesis | 2187 | 119 | **5.4%** |

Dropping the side-condition breaks the formalization; keeping it keeps it far more faithful (~4.4× lower failure rate). **The defect family is dropped side-conditions, not wrong mathematics** — every counterexample kernel-confirmed. Combined with the 49 closed-arithmetic hazards, that's **534 kernel-confirmed fidelity findings** in this corpus.

*Honest caveat:* the with-hypothesis search is incomplete for equality / measure-zero constraints (discrete rational witnesses rarely satisfy `a+b+c=1`-type hypotheses), so the 'with hypothesis' count is a lower bound — but the inequality-constrained statements are fully searchable and hold up.

---

*Correction (2026-06-26).* An earlier release reported **412** findings (ℕ 27 / ℝ 320 / ℝ-with-hyp 16) and a **2%** with-hypothesis control. A bug in the candidate filter extracted identifiers from the two relation sides concatenated **without a separator**, forging phantom variables (e.g. `'n'` + `'n - 1'` → `'nn'`) and silently rejecting valid candidates — **false negatives only**, so no prior finding was invalid; the counts were undercounts. Fixed in all three quantified checkers; corrected to **534** total (ℕ 31 / ℝ 335 / ℝ-with-hyp 119), control **24% vs 5.4%**. The thesis is unchanged (dropping the side-condition breaks formalization ~4.4× more often); every finding remains kernel-confirmed (`native_decide` over ℕ, `norm_num` over ℝ).
