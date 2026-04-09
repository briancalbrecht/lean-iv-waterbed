import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Order.Field.Basic
import LeanWaterbed.CubicPositivity

/-!
# Waterbed — Theorem 1 Case 4: both PCs bind

Source: `/Users/brian_icle/Documents/GitHub/waterbed/comment/comment.tex`,
proof of Theorem 1 (`thm:vacuous`), Case 4 (lines 717–733).

## Paper argument (informal)

In Case 4 (both PCs bind, D > 0), the multiplier identities force
`1 − 2 y_S ≤ ξ ≤ 1/(3 − 4 y_S)` on `(1/4, 1/2)`. Combined with
IV condition (12), `ξ(1 + y_S) > 2 y_S(2 − y_S)`, the upper KKT
bound gives `2 y_S(2 − y_S)(3 − 4 y_S) < 1 + y_S`, i.e., `P(y_S) < 0`.
But `P(y_S) > 0` on `(1/4, 1/2)`. Contradiction.
-/

namespace LeanWaterbed.Case4

open LeanWaterbed.CubicPositivity

/-- **Case 4: both PCs bind; IV condition (12) fails.**

Source: `comment.tex` lines 717–733, Case 4 of Theorem 1. -/
theorem case4_iv_fails
    (ξ yS : ℝ)
    (hyS_lo : 1 / 4 < yS) (hyS_hi : yS < 1 / 2)
    (hξ_lo : 1 - 2 * yS ≤ ξ) (hξ_hi : ξ * (3 - 4 * yS) ≤ 1)
    (hξ_pos : ξ > 0) :
    ξ * (1 + yS) ≤ 2 * yS * (2 - yS) := by
  have hd : (0 : ℝ) < 3 - 4 * yS := by linarith
  have hcubic := cubic_nonneg yS hyS_lo hyS_hi
  -- Same iff-multiplication pattern as Case 3
  rw [show ξ * (1 + yS) ≤ 2 * yS * (2 - yS) ↔
    ξ * (1 + yS) * (3 - 4 * yS) ≤ 2 * yS * (2 - yS) * (3 - 4 * yS) from
    ⟨fun h => by nlinarith, fun h => by nlinarith⟩]
  -- LHS: ξ(1+yS)(3-4yS) = ξ(3-4yS) * (1+yS) ≤ 1 * (1+yS) = 1+yS
  -- RHS: 2yS(2-yS)(3-4yS) ≥ 1+yS  [cubic positivity: P(yS) ≥ 0]
  nlinarith [hξ_hi, hcubic]

/-- **Negative control.** Dropping the upper KKT bound `ξ(3−4yS) ≤ 1`
makes IV condition (12) achievable. Witness: `ξ = 1, yS = 3/8`. -/
example :
    ∃ ξ yS : ℝ,
      1 / 4 < yS ∧ yS < 1 / 2 ∧
        1 - 2 * yS ≤ ξ ∧ 0 < ξ ∧
          ξ * (1 + yS) > 2 * yS * (2 - yS) := by
  refine ⟨1, 3 / 8, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num

end LeanWaterbed.Case4
