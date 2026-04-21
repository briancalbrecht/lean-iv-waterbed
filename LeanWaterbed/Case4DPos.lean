import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Order.Field.Basic

/-!
# Waterbed — Theorem 1 Case 4 sub-claim: D > 0

Source: `comment.tex`,
proof of Theorem 1 (`thm:vacuous`), Case 4 D > 0 claim.

## Paper argument (informal)

In Case 4 (both PCs bind), `D := det M = 4 y_S y_L − ξ η`. The paper
shows `D > 0` by contradiction. The contradiction reduces to
`4(2 y_S − 1)² > 0`, which holds strictly for `y_S ≠ 1/2`, in
particular on `(1/4, 1/2)`.
-/

namespace LeanWaterbed.Case4DPos

/-- **Case 4 sub-claim: `4(2 y_S − 1)² > 0` on `(1/4, 1/2)`.**

Source: `comment.tex`. -/
theorem case4_D_pos
    (yS : ℝ)
    (hyS_lo : 1/4 < yS) (hyS_hi : yS < 1/2) :
    4 * (2 * yS - 1) ^ 2 > 0 := by
  have h : (2 * yS - 1) ≠ 0 := by linarith
  have hsq : (0 : ℝ) < (2 * yS - 1) ^ 2 := by positivity
  linarith

/-- **Negative control.** At `y_S = 1/2` the expression equals zero.
Dropping `y_S < 1/2` makes the strict positivity fail. -/
example :
    ∃ yS : ℝ,
      1/4 < yS ∧ ¬(4 * (2 * yS - 1) ^ 2 > 0) := by
  refine ⟨1/2, ?_, ?_⟩ <;> norm_num

end LeanWaterbed.Case4DPos
