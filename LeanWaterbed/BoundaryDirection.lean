import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Field.Basic

/-!
# Waterbed — eta = 0 improving direction for equilibrium corollary

Source: `comment.tex`,
proof of Corollary `cor:equilibrium` (vacuity at asymmetric equilibria).

At `η = 0` in the strict waterbed regime, the paper uses the direction

`d = (-1 / (1 - ξ), 1)`

to show that a feasible point on the boundary cannot be a local maximizer:

1. the directional derivative of the small-firm participation slack is positive;
2. the directional derivative of the supplier objective is positive.

The theorem below verifies those two algebraic inequalities.
-/

namespace LeanWaterbed.BoundaryDirection

theorem gS_directional_pos_at_eta_zero
    (ξ : ℝ)
    (hξ1 : ξ < 1) :
    (ξ - 1) * (-1 / (1 - ξ)) - ξ > 0 := by
  have hden : 0 < 1 - ξ := by linarith
  have hden' : 1 - ξ ≠ 0 := by linarith
  have h :
      ((ξ - 1) * (-1 / (1 - ξ)) - ξ) = 1 - ξ := by
    field_simp [hden']
    ring
  rw [h]
  linarith

theorem phi_directional_pos_at_eta_zero
    (ξ : ℝ)
    (hξ0 : 0 < ξ) (hξ1 : ξ < 1) :
    ((1 / 2 : ℝ) - ξ) * (-1 / (1 - ξ)) + ((1 / 2 : ℝ) + ξ) > 0 := by
  have hden : 0 < 1 - ξ := by linarith
  have hden' : 1 - ξ ≠ 0 := by linarith
  have h :
      (((1 / 2 : ℝ) - ξ) * (-1 / (1 - ξ)) + ((1 / 2 : ℝ) + ξ)) =
        ξ * (3 - 2 * ξ) / (2 * (1 - ξ)) := by
    field_simp [hden']
    ring
  rw [h]
  have hnum : 0 < ξ * (3 - 2 * ξ) := by
    have h32 : 0 < 3 - 2 * ξ := by linarith
    nlinarith
  have hden2 : 0 < 2 * (1 - ξ) := by linarith
  exact div_pos hnum hden2

theorem eta_zero_improving_direction
    (ξ : ℝ)
    (hξ0 : 0 < ξ) (hξ1 : ξ < 1) :
    ((ξ - 1) * (-1 / (1 - ξ)) - ξ > 0) ∧
      (((1 / 2 : ℝ) - ξ) * (-1 / (1 - ξ)) + ((1 / 2 : ℝ) + ξ) > 0) := by
  constructor
  · exact gS_directional_pos_at_eta_zero ξ hξ1
  · exact phi_directional_pos_at_eta_zero ξ hξ0 hξ1

end LeanWaterbed.BoundaryDirection
