import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Order.Field.Basic

/-!
# Waterbed — boundary case η = 0 of Theorem 3 (thm:vacuous)

Source: `/Users/brian_icle/Documents/GitHub/waterbed/comment/comment.tex`,
proof of Theorem 3 (`thm:vacuous`), boundary case η = 0 (lines 516–539).

## Paper argument (informal)

At η = 0 the large buyer's participation constraint is slack
(g_L = F/(t·n_L) > 0), so complementary slackness gives μ_L = 0.
The share formula collapses to y_S = (1 − ξ)/2, equivalently
2·y_S = 1 − ξ.

The ξ-stationarity equation (2·y_S − 1/2) − 2·y_S · μ_S = 0 gives

    μ_S = (2·y_S − 1/2) / (2·y_S) = (1/2 − ξ) / (1 − ξ).

The η-stationarity equation (3/2 − 2·y_S) − ξ · μ_S + β = 0 gives

    β = ξ · μ_S − (1/2 + ξ).

Substituting μ_S and combining over the common denominator 1 − ξ:

    β = [ξ·(1/2 − ξ) − (1/2 + ξ)·(1 − ξ)] / (1 − ξ).

Expanding and cancelling:

    β = −1 / (2·(1 − ξ)).

Since the strict waterbed regime forces 0 < y_S, i.e. ξ < 1, the
denominator 2·(1 − ξ) is positive, so β < 0. This contradicts the
KKT dual-feasibility requirement β ≥ 0.

## Lean encoding note

The paper's argument proves that β < 0, contradicting β ≥ 0.
We formalize this as: given the hypotheses, the algebraically
determined β must satisfy β < 0. The negative control drops the
upper bound ξ < 1 and shows a witness where β ≥ 0.
-/

namespace LeanWaterbed.BoundaryEta0

/-- **Boundary case η = 0.**  At η = 0 in the strict waterbed regime
(0 < ξ < 1), the KKT conditions force `β = −1 / (2·(1 − ξ)) < 0`,
contradicting dual feasibility `β ≥ 0`.

We prove: under the hypotheses `0 < ξ`, `ξ < 1`, `y_S = (1 − ξ)/2`,
and the stationarity-derived identity `β = ξ · μ_S − (1/2 + ξ)` with
`μ_S = (1/2 − ξ) / (1 − ξ)`, the multiplier `β` is strictly negative.

Formally we show `β < 0` where
`β = ξ · ((1/2 − ξ) / (1 − ξ)) − (1/2 + ξ)`.

Source: `comment.tex` lines 516–539, boundary case of Theorem 3. -/
theorem beta_neg_at_eta_zero
    (ξ : ℝ)
    (hξpos : 0 < ξ) (hξlt : ξ < 1) :
    ξ * ((1 / 2 - ξ) / (1 - ξ)) - (1 / 2 + ξ) < 0 := by
  have hd : (0 : ℝ) < 1 - ξ := by linarith
  have hd' : (1 - ξ) ≠ 0 := ne_of_gt hd
  -- Reduce to showing (ξ * ((1/2 - ξ) / (1 - ξ)) - (1/2 + ξ)) * (1 - ξ) < 0
  -- then clear the denominator.
  suffices h : (ξ * ((1 / 2 - ξ) / (1 - ξ)) - (1 / 2 + ξ)) * (1 - ξ) < 0 from by
    rcases mul_neg_iff.mp h with ⟨_, hb⟩ | ⟨ha, _⟩
    · linarith
    · exact ha
  have : ξ * ((1 / 2 - ξ) / (1 - ξ)) * (1 - ξ) = ξ * (1 / 2 - ξ) := by
    rw [mul_div_assoc', div_mul_cancel₀ _ hd']
  nlinarith

/-- **Negative control.**  If we drop the upper bound `ξ < 1`, then
there exists a `ξ` at which the same expression for `β` is non-negative.
This shows the hypothesis `ξ < 1` is load-bearing.

Witness: `ξ = 2`, giving `1 − ξ = −1`, and
`β = 2 · ((1/2 − 2)/(−1)) − (1/2 + 2) = 2 · (3/2) − 5/2 = 1/2 > 0`. -/
example :
    ∃ ξ : ℝ,
      0 < ξ ∧
        ξ * ((1 / 2 - ξ) / (1 - ξ)) - (1 / 2 + ξ) ≥ 0 := by
  refine ⟨2, ?_, ?_⟩
  · norm_num
  · norm_num

end LeanWaterbed.BoundaryEta0
