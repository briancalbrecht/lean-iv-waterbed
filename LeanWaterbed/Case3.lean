import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Order.Field.Basic
import LeanWaterbed.CubicPositivity

/-!
# Waterbed — Theorem 1 Case 3: only PC_L binds

Source: `comment.tex`,
proof of Theorem 1 (`thm:vacuous`), Case 3.

## Paper argument (informal)

In Case 3 (only PC_L binds, μ_S = 0), the KKT conditions force
`ξ = 1/(3 − 4 y_S)` with `y_S ∈ (1/4, 1/2)`. Combining with IV
condition (12), `ξ(1 + y_S) > 2 y_S(2 − y_S)`, and clearing the
strictly positive denominator `3 − 4 y_S`, the condition becomes
`1 + y_S > 2 y_S(2 − y_S)(3 − 4 y_S)`, equivalently `P(y_S) < 0`.
But `P(y_S) > 0` on `(1/4, 1/2)`. Contradiction.
-/

namespace LeanWaterbed.Case3

open LeanWaterbed.CubicPositivity

/-- **Case 3: KKT forces ξ = 1/(3−4yS); IV condition (12) fails.**

Source: `comment.tex`, Case 3 of Theorem 1. -/
theorem case3_iv_fails
    (ξ yS : ℝ)
    (hyS_lo : 1 / 4 < yS) (hyS_hi : yS < 1 / 2)
    (hξ_pos : ξ > 0) (hξ_eq : ξ * (3 - 4 * yS) = 1) :
    ξ * (1 + yS) ≤ 2 * yS * (2 - yS) := by
  -- We show the equivalent:
  --   0 ≤ 2 * yS * (2 - yS) - ξ * (1 + yS)
  -- Multiply by (3 - 4 * yS) > 0 and use hξ_eq:
  --   [2yS(2-yS) - ξ(1+yS)] * (3-4yS)
  --   = 2yS(2-yS)(3-4yS) - ξ(3-4yS)(1+yS)
  --   = 2yS(2-yS)(3-4yS) - (1+yS)      [by hξ_eq]
  --   = P(yS) ≥ 0                        [cubic positivity]
  have hd : (0 : ℝ) < 3 - 4 * yS := by linarith
  have hcubic := cubic_nonneg yS hyS_lo hyS_hi
  -- P(yS) = 2yS(2-yS)(3-4yS) - (1+yS) ≥ 0
  -- so 2yS(2-yS)(3-4yS) ≥ 1+yS
  -- and ξ(1+yS)(3-4yS) = (1+yS) ≤ 2yS(2-yS)(3-4yS)
  -- so ξ(1+yS) ≤ 2yS(2-yS)
  rw [show ξ * (1 + yS) ≤ 2 * yS * (2 - yS) ↔
    ξ * (1 + yS) * (3 - 4 * yS) ≤ 2 * yS * (2 - yS) * (3 - 4 * yS) from
    ⟨fun h => by nlinarith, fun h => by nlinarith⟩]
  nlinarith [hξ_eq, hcubic]

/-- **Negative control.** Dropping the KKT constraint `ξ(3−4yS) = 1`
makes IV condition (12) achievable. Witness: `ξ = 1, yS = 3/8`. -/
example :
    ∃ ξ yS : ℝ,
      1 / 4 < yS ∧ yS < 1 / 2 ∧ 0 < ξ ∧
        ξ * (1 + yS) > 2 * yS * (2 - yS) := by
  refine ⟨1, 3 / 8, ?_, ?_, ?_, ?_⟩ <;> norm_num

end LeanWaterbed.Case3
