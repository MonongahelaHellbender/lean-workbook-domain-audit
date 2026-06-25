# Verified domain-fidelity hazards in internlm/Lean-Workbook

**49 hazards** found across 13,517 unique statements (202 closed-arithmetic candidates).  
42 ℕ/ℚ-divergence + 7 exponent-truncation. Every one independently confirmed in Lean (kernel probe or `native_decide`); oracle agreed with the kernel on 91/91 overlapping verdicts, 0 conflicts.

## ℕ/ℚ-divergence hazards

Statement is true in one of ℕ / ℚ and false in the other — the silently-chosen domain (`-` truncates at 0, `/` is floor division over ℕ) changed the claim.

| id | ℕ | ℚ | confirmed by | statement |
|---|---|---|---|---|
| lean_workbook_plus_893 | FALSE | TRUE | kernel+oracle | `1 - (6 + 4) / 36 - (1 + 4 + 1) / 36 = 5 / 9` |
| lean_workbook_plus_4042 | TRUE | FALSE | kernel+oracle | `(3 / 4)^3 * (1 / 4)^2 / (2^5 / 4^5 + 3 / 4 * (1 / 4)^2 * (3 / 4)^3) = 27 / 59` |
| lean_workbook_plus_6785 | FALSE | TRUE | kernel+oracle | `9 - 12 + 3 = 0` |
| lean_workbook_plus_7898 | FALSE | TRUE | native+oracle | `(2^(2017) * (1/4)^1008) = 2` |
| lean_workbook_plus_7986 | TRUE | FALSE | kernel+oracle | `1 / 3 * (1 / 7 + 3 / 14 + 5 / 21) = 5 / 12` |
| lean_workbook_plus_9421 | FALSE | TRUE | kernel+oracle | `1 - (1 / 6) = 5 / 6` |
| lean_workbook_plus_14609 | FALSE | TRUE | kernel+oracle | `(1 - (397 * 396 * 395 * 394 / (400 * 399 * 398 * 397))) = 15761 / 529340` |
| lean_workbook_plus_23590 | FALSE | TRUE | native+oracle | `(1 + 1 / 8)^50 > 1 + 50 / 8` |
| lean_workbook_plus_24615 | FALSE | TRUE | native+oracle | `(3 / 2)^3 = 27 / 8` |
| lean_workbook_plus_26988 | TRUE | FALSE | kernel+oracle | `2017 - (2017 / 3) = 1345` |
| lean_workbook_plus_27771 | FALSE | TRUE | kernel+oracle | `(1 / 27 + 1 / 125 + 1 / 40 - 1 / 56) < (3 / 8) ^ 3` |
| lean_workbook_plus_27887 | FALSE | TRUE | native+oracle | `(10^1965 + 1)/(10^1966 + 1) > (10^1966 + 1)/(10^1967 + 1)` |
| lean_workbook_plus_29444 | FALSE | TRUE | native+oracle | `2000^3 - 1999 * 2000^2 - 1999^2 * 2000 + 1999^3 = 3999` |
| lean_workbook_plus_29973 | FALSE | TRUE | native+oracle | `(365 / 2) * (10260 / 73 + 286900 / 73) = 742900` |
| lean_workbook_plus_30298 | FALSE | TRUE | native+oracle | `(2^100 + 3^100) ≤ (3 + 1/(3^33*50))^100` |
| lean_workbook_plus_31722 | FALSE | TRUE | native+oracle | `(3 * 5 / (9 * 11)) * (7 * 9 * 11 / (3 * 5 * 7)) = 1` |
| lean_workbook_plus_33954 | FALSE | TRUE | native+oracle | `(1 + 1 / 20)^100 > 100` |
| lean_workbook_plus_34539 | TRUE | FALSE | native+oracle | `1 / 6 + 1 / 10 + 1 / 8 ≥ 1 / 2` |
| lean_workbook_plus_35275 | FALSE | TRUE | native+oracle | `24 * (3 / 8) = 9` |
| lean_workbook_plus_36733 | FALSE | TRUE | native+oracle | `(3 * 5 / (9 * 11)) * (7 * 9 * 11) / (3 * 5 * 7) = 1` |
| lean_workbook_plus_37964 | FALSE | TRUE | native+oracle | `(1 / 2 * 3 / 4 * 5 / 6 * 7 / 8 * 9 / 10 * 11 / 12 * 13 / 14 * 15 / 16 * 17 / 18 * 19 / 20 ` |
| lean_workbook_plus_42947 | TRUE | FALSE | native+oracle | `(2^4 / 3^4) * (3^4 - 2^4) / (3^4 - 1) * 2 = 2^4 * (3^4 - 2^4) / (3^4 * (3^4 - 1))` |
| lean_workbook_plus_43119 | FALSE | TRUE | native+oracle | `1 - (1 / 6 * 1 / 2) = 11 / 12` |
| lean_workbook_plus_45222 | FALSE | TRUE | native+oracle | `(1 / 3 + 1 / 4) > 1 / 2` |
| lean_workbook_plus_46730 | FALSE | TRUE | native+oracle | `28 * (4 / 3) ^ 4 - 16 * (4 / 3) ^ 3 - 12 * (4 / 3) ^ 2 - 8 > 0` |
| lean_workbook_plus_48269 | TRUE | FALSE | native+oracle | `(9 / 10)^7 * (4 / 3)^9 * (3 / 5)^6 * (5 / 6)^11 = 1 / 125` |
| lean_workbook_plus_48770 | FALSE | TRUE | native+oracle | `(2549^3 / (2547 * 2548) - 2547^3 / (2548 * 2549)) > 8` |
| lean_workbook_plus_53499 | FALSE | TRUE | native+oracle | `(1996^1995 + 1) / (1996^1996 + 1) > (1996^1996 + 1) / (1996^1997 + 1)` |
| lean_workbook_plus_55820 | FALSE | TRUE | native+oracle | `(2013^2 / (2013 * 2014 - 3)) > (2013 / 2016)` |
| lean_workbook_plus_56142 | FALSE | TRUE | native+oracle | `(4 / 3) * (5 / 4) * (6 / 5) * (7 / 6) * (8 / 7) * (9 / 8) = 3` |
| lean_workbook_plus_56516 | FALSE | TRUE | native+oracle | `2 ≥ 3 - 2 * (1 / 2)` |
| lean_workbook_plus_59251 | FALSE | TRUE | native+oracle | `2 ≥ 3 - 3 * (1 / 3)` |
| lean_workbook_plus_60719 | FALSE | TRUE | native+oracle | `(1 / 2 * 3 / 4 * 5 / 6 * 7 / 8 * 9 / 10 * 11 / 12 * 13 / 14 * 15 / 16 * 17 / 18 * 19 / 20 ` |
| lean_workbook_plus_67014 | FALSE | TRUE | native+oracle | `(2 + 4 + 6) / (1 + 3 + 5) - (1 + 3 + 5) / (2 + 4 + 6) = 7 / 12` |
| lean_workbook_plus_69090 | FALSE | TRUE | native+oracle | `17 * (11 / 17) - 13 * (1 / 13) = 10` |
| lean_workbook_plus_70669 | FALSE | TRUE | native+oracle | `(2 + 4 + 6) / (1 + 3 + 5) - (1 + 3 + 5) / (2 + 4 + 6) = 7 / 12` |
| lean_workbook_plus_72913 | FALSE | TRUE | native+oracle | `(1 + 1 / 8)^50 > 2` |
| lean_workbook_plus_76820 | TRUE | FALSE | native+oracle | `1 / 21 + 1 / 22 = 1 / 462` |
| lean_workbook_plus_77041 | FALSE | TRUE | native+oracle | `2 * (1 / 2) + 3 * (1 / 2) = 5 / 2` |
| lean_workbook_plus_78859 | FALSE | TRUE | native+oracle | `1 / 2 * 2 * 3 / 2 = 3 / 2` |
| lean_workbook_plus_79289 | FALSE | TRUE | native+oracle | `1 - ((1/4) - (1/12) + (1/24) - (1/24)) = 5/6` |
| lean_workbook_plus_82308 | FALSE | TRUE | native+oracle | `(1 / 4033 + (2 * 2016) / (2016 ^ 2 + 2017 ^ 2) + (4 * 2016 ^ 3) / (2016 ^ 4 + 2017 ^ 4) - ` |

## Exponent-truncation hazards

Statement carries a fractional exponent (`x^(1/3)` = a real root). Lean's `^` needs a ℕ exponent, so `1/3` floors to 0 and `x^(1/3)` becomes `x^0 = 1` — a different statement from the intended real-root claim. *as-formalized* = `native_decide` on the verbatim goal; *intended-ℝ* = rigorous `mpmath.iv` intervals + `sympy`.

| id | as-formalized | intended ℝ | statement |
|---|---|---|---|
| lean_workbook_plus_3781 | FALSE | TRUE | `((5/6)^(1/3) + (6/5)^(1/3)) > (2)` |
| lean_workbook_plus_18325 | FALSE | TRUE | `(12^(1 / 2)) > (45 / 13)` |
| lean_workbook_plus_19279 | FALSE | TRUE | `((2^(1 / 3) + 1)^3 * (2^(1 / 3) - 1)) = (3)` |
| lean_workbook_plus_29600 | TRUE | FALSE | `((1 / 9) * (2^(1/3) + 20^(1/3) - 25^(1/3))^2) = (2^(2/3) / 9)` |
| lean_workbook_plus_51925 | FALSE | TRUE | `((2^(1/3) + 4^(1/3))^3) = (6 + 6 * (2^(1/3) + 4^(1/3)))` |
| lean_workbook_plus_56245 | FALSE | TRUE | `(2^(1/2)) < (2 * 3^(1/2) - 2)` |
| lean_workbook_plus_70657 | FALSE | TRUE | `((1 / (2^4))^(1 / 4)) = (1 / 2)` |
