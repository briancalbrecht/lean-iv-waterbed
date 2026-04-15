import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.Order.Field.Basic

/-!
# Waterbed comment — CS derivative equivalence with IV condition (12)

Source: `comment/comment.tex`, lines 231–266.

Along the both-binding Hotelling path, dCS/dw_L > 0 if and only if
IV condition (12) holds: ξ > 2·y_S·(2 − y_S) / (1 + y_S).

## What this file verifies

1. **Pass-through substitution**: the Hotelling pricing derivatives
   dp_S/dw_L = 1/3 − ξ/(3·yS) and dp_L/dw_L = 2/3 − ξ/(6·yS)
   follow from substituting the pass-through dw_S/dw_L = −ξ/(2·yS).

2. **Computation identity**: the dCS/dwL envelope expression, after
   substituting the Hotelling pass-through and pricing formulas,
   simplifies to −(2 − yS)/3 + (1 + yS)·ξ/(6·yS).

3. **Sign equivalence**: dCS/dwL > 0 ↔ ξ > 2·yS·(2 − yS)/(1 + yS),
   with proportionality factor (1 + yS)/(6·yS) > 0.

## What this file does NOT verify

- The implicit function theorem step yielding dw_S/dw_L = −ξ/(2·yS).
  The partial derivatives ∂g_S/∂ξ = −2yS and ∂g_S/∂η = −ξ are verified
  in the main proof's displayed-partials check; this file takes the
  resulting pass-through as given.
- The envelope argument killing the dy_S/dw_L terms in dCS/dw_L.
-/

namespace LeanWaterbed.CSDerivativeEquivalence

/-- Pass-through substitution for the small firm's retail price derivative.
dp_S/dw_L = 1/3 + (2/3)·(dw_S/dw_L) with dw_S/dw_L = −ξ/(2·yS)
gives dp_S/dw_L = 1/3 − ξ/(3·yS). -/
theorem dpS_formula (ξ yS : ℝ) (hyS : yS ≠ 0) :
    (1 : ℝ) / 3 + 2 / 3 * (-ξ / (2 * yS)) = 1 / 3 - ξ / (3 * yS) := by
  field_simp
  ring

/-- Pass-through substitution for the large firm's retail price derivative.
dp_L/dw_L = 2/3 + (1/3)·(dw_S/dw_L) with dw_S/dw_L = −ξ/(2·yS)
gives dp_L/dw_L = 2/3 − ξ/(6·yS). -/
theorem dpL_formula (ξ yS : ℝ) (hyS : yS ≠ 0) :
    (2 : ℝ) / 3 + 1 / 3 * (-ξ / (2 * yS)) = 2 / 3 - ξ / (6 * yS) := by
  field_simp
  ring

/-- The dCS/dwL computation identity.
Substituting dp_S/dw_L = 1/3 − ξ/(3·yS) and dp_L/dw_L = 2/3 − ξ/(6·yS)
into dCS/dwL = −[yS · dpS/dwL + (1−yS) · dpL/dwL] gives the closed form
−(2 − yS)/3 + (1 + yS)·ξ/(6·yS). -/
theorem dCS_dwL_identity (ξ yS : ℝ) (hyS : yS ≠ 0) :
    -(yS * ((1 : ℝ) / 3 - ξ / (3 * yS)) +
      (1 - yS) * ((2 : ℝ) / 3 - ξ / (6 * yS))) =
    -(2 - yS) / 3 + (1 + yS) * ξ / (6 * yS) := by
  field_simp
  ring

/-- Forward direction: IV condition (12) implies dCS/dwL > 0.
If ξ exceeds the threshold 2·yS·(2−yS)/(1+yS), the consumer surplus
derivative is positive (consumer surplus falls as w_L decreases). -/
theorem cs_pos_of_iv12
    (ξ yS : ℝ) (hyS0 : 0 < yS)
    (h : ξ > 2 * yS * (2 - yS) / (1 + yS)) :
    -(2 - yS) / 3 + (1 + yS) * ξ / (6 * yS) > 0 := by
  have h1yS : (0 : ℝ) < 1 + yS := by linarith
  have hyS_ne : yS ≠ 0 := ne_of_gt hyS0
  have h18 : (0 : ℝ) < 18 * yS := by positivity
  -- Rewrite as single fraction over positive denominator
  have heq : -(2 - yS) / 3 + (1 + yS) * ξ / (6 * yS) =
      (3 * (1 + yS) * ξ - 6 * yS * (2 - yS)) / (18 * yS) := by
    field_simp; ring
  rw [heq, gt_iff_lt]
  apply div_pos _ h18
  -- Goal: 0 < 3 * (1 + yS) * ξ - 6 * yS * (2 - yS)
  -- Extract polynomial from hypothesis by multiplying by 3*(1+yS) > 0
  have h_sub := sub_pos.mpr (gt_iff_lt.mp h)
  have h_prod := mul_pos h_sub (mul_pos (show (0 : ℝ) < 3 by norm_num) h1yS)
  have h_expand : (ξ - 2 * yS * (2 - yS) / (1 + yS)) * (3 * (1 + yS)) =
      3 * (1 + yS) * ξ - 6 * yS * (2 - yS) := by
    field_simp; ring
  linarith

/-- Reverse direction: dCS/dwL > 0 implies IV condition (12).
If the consumer surplus derivative is positive, then ξ exceeds
the threshold 2·yS·(2−yS)/(1+yS). -/
theorem iv12_of_cs_pos
    (ξ yS : ℝ) (hyS0 : 0 < yS)
    (h : -(2 - yS) / 3 + (1 + yS) * ξ / (6 * yS) > 0) :
    ξ > 2 * yS * (2 - yS) / (1 + yS) := by
  have h1yS : (0 : ℝ) < 1 + yS := by linarith
  have hyS_ne : yS ≠ 0 := ne_of_gt hyS0
  have h18 : (0 : ℝ) < 18 * yS := by positivity
  -- Multiply h by 18*yS > 0 to clear denominators
  have hmul := mul_pos (gt_iff_lt.mp h) h18
  have hexp : (-(2 - yS) / 3 + (1 + yS) * ξ / (6 * yS)) * (18 * yS) =
      3 * (1 + yS) * ξ - 6 * yS * (2 - yS) := by
    field_simp; ring
  rw [hexp] at hmul
  -- hmul : 0 < 3 * (1 + yS) * ξ - 6 * yS * (2 - yS)
  rw [gt_iff_lt, ← sub_pos]
  -- Goal: 0 < ξ - 2 * yS * (2 - yS) / (1 + yS)
  have hfrac : ξ - 2 * yS * (2 - yS) / (1 + yS) =
      (ξ * (1 + yS) - 2 * yS * (2 - yS)) / (1 + yS) := by
    field_simp
  rw [hfrac]
  apply div_pos _ h1yS
  -- Goal: 0 < ξ * (1 + yS) - 2 * yS * (2 - yS)
  nlinarith

/-- The full equivalence: dCS/dwL > 0 iff IV condition (12).
This is the algebraic core of the paper's equivalence derivation
(comment.tex, lines 258–264). -/
theorem cs_derivative_iff_iv12
    (ξ yS : ℝ) (hyS0 : 0 < yS) :
    -(2 - yS) / 3 + (1 + yS) * ξ / (6 * yS) > 0 ↔
    ξ > 2 * yS * (2 - yS) / (1 + yS) :=
  ⟨iv12_of_cs_pos ξ yS hyS0, cs_pos_of_iv12 ξ yS hyS0⟩

/-- Negative control: without yS > 0, the forward direction fails.
At yS = −1/2, ξ = −6: dCS/dwL > 0 but ξ < threshold, because the
proportionality factor (1+yS)/(6yS) is negative. -/
theorem cs_equivalence_needs_yS_pos :
    ¬ ∀ ξ yS : ℝ, -(2 - yS) / 3 + (1 + yS) * ξ / (6 * yS) > 0 →
      ξ > 2 * yS * (2 - yS) / (1 + yS) := by
  simp only [not_forall, not_lt]
  exact ⟨-6, -(1 : ℝ) / 2, by norm_num, by norm_num⟩

end LeanWaterbed.CSDerivativeEquivalence
