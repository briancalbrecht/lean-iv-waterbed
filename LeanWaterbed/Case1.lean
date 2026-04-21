import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Waterbed — Theorem 1 Case 1: both PCs slack

Source: `comment.tex`,
proof of Theorem 1 (`thm:vacuous`), Case 1.

## Paper argument (informal)

With both participation constraints slack, complementary slackness
gives μ_S = μ_L = 0. The stationarity conditions (S_ξ) and (S_η)
collapse to ∇Φ = 0, i.e., `1/2 + η − ξ = 0` and `1/2 + ξ − η = 0`.
Adding gives `1 = 0`. Contradiction.
-/

namespace LeanWaterbed.Case1

/-- **Case 1: both PCs slack.** In the strict waterbed regime, the
gradient equations `1/2 + η − ξ = 0` and `1/2 + ξ − η = 0` are
simultaneously inconsistent.

Source: `comment.tex`, Case 1 of Theorem 1. -/
theorem case1_no_solution
    (ξ η : ℝ)
    (hξη : ξ > η) (hη : η ≥ 0) (hξ : ξ < 1) (hη' : η < 1) :
    ¬ (1/2 + η - ξ = 0 ∧ 1/2 + ξ - η = 0) := by
  intro ⟨h1, h2⟩
  linarith

/-- **Negative control.** Dropping one of the two gradient equations
makes the remaining one satisfiable in the strict waterbed regime.
Witness: `ξ = 3/4, η = 1/4`. -/
example :
    ∃ ξ η : ℝ,
      ξ > η ∧ η ≥ 0 ∧ ξ < 1 ∧ η < 1 ∧
        (1/2 + η - ξ = 0) := by
  refine ⟨3/4, 1/4, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num

end LeanWaterbed.Case1
