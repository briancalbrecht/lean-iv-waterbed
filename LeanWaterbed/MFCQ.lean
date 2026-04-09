import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Waterbed — Corollary 1: MFCQ slackening direction d = (−1, −1)

Source: `/Users/brian_icle/Documents/GitHub/waterbed/comment/comment.tex`,
proof of Corollary 1 (`cor:local-max`), lines 740–769.

## Paper argument (informal)

At any interior feasible point in the strict waterbed regime
(`ξ > 0`, `η > 0`, `ξ > η`), the only possibly active inequality
constraints are `g_S ≥ 0` and `g_L ≥ 0`, with gradients

    ∇g_S = (−2 y_S, −ξ),   ∇g_L = (−η, −2 y_L).

The common slackening direction `d = (−1, −1)` satisfies

    ∇g_S · d = 2 y_S + ξ > 0,   ∇g_L · d = η + 2 y_L > 0,

because all four quantities `y_S, y_L, ξ, η` are strictly positive.
The Mangasarian–Fromovitz constraint qualification therefore holds,
so every interior local maximizer is a KKT point.
-/

namespace LeanWaterbed.MFCQ

/-- **MFCQ slackening direction.** In the strict waterbed regime with
shares `y_S = (1 + η − ξ)/2` and `y_L = (1 + ξ − η)/2` both in
`(0, 1)`, the direction `d = (−1, −1)` satisfies
`2 y_S + ξ > 0` and `η + 2 y_L > 0`.

Source: `comment.tex` lines 740–769, Corollary 1. -/
theorem mfcq_slackening_direction
    (ξ η : ℝ)
    (hξ_pos : ξ > 0) (hη_pos : η > 0) (hξη : ξ > η)
    (hyS_pos : (1 + η - ξ) / 2 > 0) (hyL_pos : (1 + ξ - η) / 2 > 0)
    (hyS_lt : (1 + η - ξ) / 2 < 1) (hyL_lt : (1 + ξ - η) / 2 < 1) :
    2 * ((1 + η - ξ) / 2) + ξ > 0 ∧ η + 2 * ((1 + ξ - η) / 2) > 0 := by
  constructor <;> linarith

/-- **Negative control.** Dropping `η > 0` (and the share-positivity
hypothesis it entails) lets the first conjunct fail.
Witness: `ξ = 1/2, η = −2`. -/
example :
    ∃ ξ η : ℝ,
      ξ > η ∧
        ¬(2 * ((1 + η - ξ) / 2) + ξ > 0) := by
  refine ⟨1/2, -2, ?_, ?_⟩ <;> norm_num

end LeanWaterbed.MFCQ
