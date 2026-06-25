# Quantified false-universals in internlm/Lean-Workbook

Beyond the 49 closed-arithmetic hazards, the quantified checkers find **universally-quantified statements that are FALSE as formalized** — kernel-confirmed by a counterexample. A `theorem t (n : ℕ) … : body` is `∀ n, body`; a witness where `body` is false disproves it.

## Over ℕ — 27 false universals (native_decide-confirmed)

Partitioned by *why* they're false (missing-hypothesis recovery × ℕ/ℚ truth):

- **5 genuine missing-hypothesis** — recoverable by a lower bound (e.g. `holds for n≥3`); the autoformalizer dropped a positivity/range side-condition.
- **5 domain bugs** (ℕ truncation, no bound helps — should be ℝ).
- **13 genuinely wrong** (false over ℚ too, e.g. `2016²−2015·2017=2026`).
- 3 undetermined.

## Over ℝ — 91 false universals (norm_num-confirmed)

A rational witness disproves a `∀ x : ℝ` claim (ℚ ⊂ ℝ). Split by positivity-recovery:

- **39 hold for all vars > 0** — dropped positivity (`a,b,c ≥ 0` omitted); recoverable.
- **52 false even on positive reals** — the sharper finds (missing an upper-bound/range like `c³ ≤ 2c²` false at c=3, or genuine errors).

### Sample: false even on positive reals

| id | statement | witness |
|---|---|---|
| lean_workbook_plus_606 | `c^3 ≤ 2 * c^2` | {'c': '3'} |
| lean_workbook_plus_1727 | `(x^2 / (1 + x^2)) ≤ 3 / 4` | {'x': '2'} |
| lean_workbook_plus_3810 | `(a^3 + 1)^2 ≥ (a^2 + 1) * (a^4 + 1)` | {'a': '-1'} |
| lean_workbook_plus_4390 | `a^2 + b^2 + (3 - a - b)^2 + 3 / 2 * a * b * (3 - a - b) - 9 / 2 ≥ 0` | {'a': '-1', 'b': '2'} |
| lean_workbook_plus_5906 | `a * b * (a - b) ^ 2 + 2 * (a * b - 1) * (a ^ 2 + b ^ 2) + 4 * (a * b - 2) * (a + b - 2) ≥ 0` | {'a': '1', 'b': '-3'} |
| lean_workbook_plus_6269 | `2 * b * c + 2 * b^2 + 2 * c^2 ≤ 6 + b^3 * c + b * c^3` | {'b': '1', 'c': '-2'} |
| lean_workbook_plus_7811 | `(x^4 - 4 * x^3 + 8 * x^2 + 4 * x + 1) * (x^4 + 4 * x^3 + 8 * x^2 - 4 * x + 1) = x^8 + 8 * x^6 + 24 * x^4 + 16 * x^2 + 1` | {'x': '1'} |
| lean_workbook_plus_8036 | `(x^2 - 2 * x + 2) / (3 * x^2 - 10 * x + 6) + 3 * x / (x^2 + 2) = 1` | {'x': '1'} |
| lean_workbook_plus_9060 | `(-(27 / 392) * (a - 1 / 3) + 9 / 28) ≥ 1 / (a ^ 2 + 3)` | {'a': '5'} |
| lean_workbook_plus_9481 | `(x - 2) * (x - 1) * x * (x + 1) + (y - 2) * (y - 1) * y * (y + 1) - (x - 1) * (y - 1) * (4 * x ^ 2 - 5 * x * y + 4 * y ^ 2 - 4) = 0` | {'x': '1', 'y': '-2'} |
| lean_workbook_plus_12013 | `x^5 + 1/(x^5) - 1 = (x + 1/x - 1)*((x + 1/x - 1)*(x^3 + 2*x^2 - 2*x - 6) + 5)` | {'x': '1'} |
| lean_workbook_plus_13140 | `(a + b) / (a * b) ≥ 24 / (a ^ 2 * b ^ 2 + 4 * a * b + 4)` | {'a': '1', 'b': '1'} |
| lean_workbook_plus_14247 | `6 - 5 * x + 6 * c + 3 * x^2 - 3 * c^2 ≥ 0` | {'x': '1', 'c': '-1'} |
| lean_workbook_plus_15544 | `(4 * p + 9) * (p - 3) ≥ (t - 3) * (36 - 8 * p)` | {'p': '1', 't': '3'} |

**Honest read:** across ℕ and ℝ, *"false as formalized" is dominated by dropped side-conditions* (missing positivity/range), not wrong math — but every counterexample is kernel-confirmed, so these are genuinely unprovable-as-written `sorry`-stubbed targets.

