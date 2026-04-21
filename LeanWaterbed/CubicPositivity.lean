import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Order.Field.Basic

/-!
# Waterbed — Cubic positivity sub-lemma

Source: `comment.tex`,
proof of Theorem 1 (`thm:vacuous`), used in Cases 3 and 4 (line ~620).

## Paper argument (informal)

`P(y_S) := 8 y_S³ − 22 y_S² + 11 y_S − 1 > 0` on `(1/4, 1/2)`.

Factor: `P(y_S) = (2 y_S − 1)(4 y_S² − 9 y_S + 1)`. The quadratic
factor has roots `(9 ± √65)/8 ≈ 0.117, 2.133` and opens upward, so
it is strictly negative on `(0.117, 2.133) ⊃ (1/4, 1/2)`. The linear
factor `2 y_S − 1` is also strictly negative on `(1/4, 1/2)`. Both
factors negative ⟹ product positive.

## Lean encoding

We also prove `P(y_S) ≥ 0` (the non-strict version) as a convenience
lemma for Case 3 and Case 4, which only need `≥ 0` after denominator
clearing.
-/

namespace LeanWaterbed.CubicPositivity

/-- **Cubic positivity (strict).** `P(y_S) > 0` on `(1/4, 1/2)`.

Source: `comment.tex` line ~620, used in Cases 3 and 4 of Theorem 1. -/
theorem cubic_positivity
    (yS : ℝ)
    (hyS_lo : 1/4 < yS) (hyS_hi : yS < 1/2) :
    8 * yS ^ 3 - 22 * yS ^ 2 + 11 * yS - 1 > 0 := by
  -- P(yS) = (2yS-1)(4yS²-9yS+1); both factors < 0 on (1/4, 1/2)
  have h1 : 2 * yS - 1 < 0 := by linarith
  have h2 : 4 * yS * yS < 2 * yS := by nlinarith
  -- h2 gives 4yS²-9yS+1 < 2yS-9yS+1 = 1-7yS < 1-7/4 < 0
  -- Product of two negatives is positive:
  nlinarith [sq_nonneg (2 * yS - 1), sq_nonneg (1 - 2 * yS)]

/-- **Cubic non-negativity.** Convenience lemma for Cases 3 and 4. -/
theorem cubic_nonneg
    (yS : ℝ)
    (hyS_lo : 1/4 < yS) (hyS_hi : yS < 1/2) :
    8 * yS ^ 3 - 22 * yS ^ 2 + 11 * yS - 1 ≥ 0 :=
  le_of_lt (cubic_positivity yS hyS_lo hyS_hi)

/-- **Negative control.** At `y_S = 1/2`, `P(1/2) = 0`, so
strict positivity fails when the upper bound is dropped. -/
example :
    ∃ yS : ℝ,
      1/4 < yS ∧ ¬(8 * yS ^ 3 - 22 * yS ^ 2 + 11 * yS - 1 > 0) := by
  refine ⟨1/2, ?_, ?_⟩ <;> norm_num

end LeanWaterbed.CubicPositivity
