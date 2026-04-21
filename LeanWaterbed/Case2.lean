import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Order.Field.Basic

/-!
# Waterbed — Theorem 1 Case 2: KKT candidate infeasible

Source: `comment.tex`,
proof of Theorem 1 (`thm:vacuous`), Case 2.

## Paper argument (informal)

In Case 2 (only PC_S binds, μ_L = 0), the KKT candidate satisfies
`(ξ + η)/2 = (−8 y_S² + 6 y_S + 1) / (2(4 y_S − 1))`. Showing
`(ξ + η)/2 > 1` reduces to `8 y_S² + 2 y_S − 3 < 0`. This factors
as `(2 y_S − 1)(4 y_S + 3) < 0`, which holds on `(1/4, 1/2)` because
`2 y_S − 1 < 0` and `4 y_S + 3 > 0`.
-/

namespace LeanWaterbed.Case2

/-- **Case 2: KKT candidate is infeasible.** On `(1/4, 1/2)`,
`8 y_S² + 2 y_S − 3 < 0`.

Source: `comment.tex`, Case 2 of Theorem 1. -/
theorem case2_infeasible
    (yS : ℝ)
    (hyS_lo : 1/4 < yS) (hyS_hi : yS < 1/2) :
    8 * yS ^ 2 + 2 * yS - 3 < 0 := by
  nlinarith [sq_nonneg (2 * yS - 1)]

/-- **Negative control.** At `y_S = 1`, dropping the upper bound makes
`8 y_S² + 2 y_S − 3 ≥ 0` achievable. -/
example :
    ∃ yS : ℝ,
      1/4 < yS ∧ 8 * yS ^ 2 + 2 * yS - 3 ≥ 0 := by
  refine ⟨1, ?_, ?_⟩ <;> norm_num

end LeanWaterbed.Case2
