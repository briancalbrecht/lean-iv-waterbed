import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.Order.Field.Basic
import LeanWaterbed.BoundaryEta0
import LeanWaterbed.Case2
import LeanWaterbed.Case4DPos
import LeanWaterbed.Vacuity

/-!
# Waterbed — Theorem 1: end-to-end composition

Source: `comment.tex`, Theorem 1 (`thm:vacuous`).

This file composes the sub-case results from the other files into a
single theorem matching the paper's Theorem 1: no KKT point of the
supplier's Hotelling problem in the strict waterbed regime satisfies
IV condition (12).

## What this formalizes

The full KKT system — stationarity, complementary slackness, dual
feasibility, and primal feasibility — is taken as hypotheses. The
proof exhausts the boundary case η = 0 and the four active-set
configurations of {g_S, g_L}, dispatching to the sub-case results
proved in separate files.

## Hypotheses

The theorem takes all KKT conditions as explicit hypotheses:
- Model parameters F > 0, t > 0, n_L > 1
- Decision variables ξ > η ≥ 0 (strict waterbed regime)
- KKT multipliers μ_S, μ_L, β ≥ 0 (α = 0 since ξ > 0)
- Participation constraint feasibility g_S ≥ 0, g_L ≥ 0
- Stationarity conditions (S_ξ) and (S_η)
- Complementary slackness on g_S, g_L, and η
-/

namespace LeanWaterbed.Theorem1

open LeanWaterbed.BoundaryEta0
open LeanWaterbed.Case2
open LeanWaterbed.Case4DPos
open LeanWaterbed.Vacuity

/-! ### Multiplier identities from stationarity

Given the stationarity conditions (S_ξ) and (S_η) with α = β = 0,
Cramer's rule yields the multiplier identities (‡_S) and (‡_L). -/

/-- **Multiplier identity (‡_S).** From stationarity with α = β = 0,
`μ_S · D = (1 − ξ(1 + 2ξ − 2η)) / 2` where `D = det M`. -/
theorem multiplier_S_identity
    (ξ η μ_S μ_L : ℝ)
    (hSξ : (1 / 2 + η - ξ) - (1 + η - ξ) * μ_S - η * μ_L = 0)
    (hSη : (1 / 2 + ξ - η) - ξ * μ_S - (1 + ξ - η) * μ_L = 0) :
    μ_S * ((1 + η - ξ) * (1 + ξ - η) - ξ * η) =
      1 / 2 - ξ / 2 + ξ * η - ξ ^ 2 := by
  have eq1 : (1 + η - ξ) * μ_S + η * μ_L = 1 / 2 + η - ξ := by linarith
  have eq2 : ξ * μ_S + (1 + ξ - η) * μ_L = 1 / 2 + ξ - η := by linarith
  have h3a := congr_arg (· * (1 + ξ - η)) eq1
  have h3b := congr_arg (· * η) eq2
  have lhs_eq : ((1 + η - ξ) * μ_S + η * μ_L) * (1 + ξ - η) -
      (ξ * μ_S + (1 + ξ - η) * μ_L) * η =
    μ_S * ((1 + η - ξ) * (1 + ξ - η) - ξ * η) := by ring
  have rhs_eq : (1 / 2 + η - ξ) * (1 + ξ - η) - (1 / 2 + ξ - η) * η =
      1 / 2 - ξ / 2 + ξ * η - ξ ^ 2 := by ring
  linarith

/-- **Multiplier identity (‡_L).** From stationarity with α = β = 0,
`μ_L · D = (1 − η(1 + 2η − 2ξ)) / 2` where `D = det M`. -/
theorem multiplier_L_identity
    (ξ η μ_S μ_L : ℝ)
    (hSξ : (1 / 2 + η - ξ) - (1 + η - ξ) * μ_S - η * μ_L = 0)
    (hSη : (1 / 2 + ξ - η) - ξ * μ_S - (1 + ξ - η) * μ_L = 0) :
    μ_L * ((1 + η - ξ) * (1 + ξ - η) - ξ * η) =
      1 / 2 - η / 2 + ξ * η - η ^ 2 := by
  have eq1 : (1 + η - ξ) * μ_S + η * μ_L = 1 / 2 + η - ξ := by linarith
  have eq2 : ξ * μ_S + (1 + ξ - η) * μ_L = 1 / 2 + ξ - η := by linarith
  have h3a := congr_arg (· * (1 + η - ξ)) eq2
  have h3b := congr_arg (· * ξ) eq1
  have lhs_eq : (ξ * μ_S + (1 + ξ - η) * μ_L) * (1 + η - ξ) -
      ((1 + η - ξ) * μ_S + η * μ_L) * ξ =
    μ_L * ((1 + η - ξ) * (1 + ξ - η) - ξ * η) := by ring
  have rhs_eq : (1 / 2 + ξ - η) * (1 + η - ξ) - (1 / 2 + η - ξ) * ξ =
      1 / 2 - η / 2 + ξ * η - η ^ 2 := by ring
  linarith

/-- **D > 0 from ξ+η < 2.** If both multiplier identities hold,
μ_S, μ_L ≥ 0, ξ > η > 0, and ξ+η < 2, then the determinant
D = (1+η−ξ)(1+ξ−η) − ξη is positive. -/
private theorem D_pos_of_sum_lt_two
    (ξ η μ_S μ_L : ℝ)
    (hξη : ξ > η) (hη_pos : 0 < η) (hξ_pos : 0 < ξ)
    (hμS : μ_S ≥ 0) (hμL : μ_L ≥ 0)
    (h_sum_lt : ξ + η < 2)
    (hSξ : (1 / 2 + η - ξ) - (1 + η - ξ) * μ_S - η * μ_L = 0)
    (hSη : (1 / 2 + ξ - η) - ξ * μ_S - (1 + ξ - η) * μ_L = 0) :
    0 < (1 + η - ξ) * (1 + ξ - η) - ξ * η := by
  by_contra hD_le
  push Not at hD_le
  set D := (1 + η - ξ) * (1 + ξ - η) - ξ * η with hD_def
  have hmS := multiplier_S_identity ξ η μ_S μ_L hSξ hSη
  have hmL := multiplier_L_identity ξ η μ_S μ_L hSξ hSη
  have h_mSD : μ_S * D ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hμS hD_le
  have h_mLD : μ_L * D ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hμL hD_le
  have h_S_bound : 1 / 2 - ξ / 2 + ξ * η - ξ ^ 2 ≤ 0 := by linarith [hmS]
  have h_L_bound : 1 / 2 - η / 2 + ξ * η - η ^ 2 ≤ 0 := by linarith [hmL]
  have ha : ξ * (1 + 2 * ξ - 2 * η) ≥ 1 := by
    have : 2 * (1 / 2 - ξ / 2 + ξ * η - ξ ^ 2) =
      1 - ξ * (1 + 2 * ξ - 2 * η) := by ring
    linarith
  have hb : η * (1 + 2 * η - 2 * ξ) ≥ 1 := by
    have : 2 * (1 / 2 - η / 2 + ξ * η - η ^ 2) =
      1 - η * (1 + 2 * η - 2 * ξ) := by ring
    linarith
  have hp_pos : (0 : ℝ) < 1 + 2 * ξ - 2 * η := by
    by_contra h_le; push Not at h_le
    have := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hξ_pos) h_le
    linarith [ha]
  have hq_pos : (0 : ℝ) < 1 + 2 * η - 2 * ξ := by
    by_contra h_le; push Not at h_le
    have := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hη_pos) h_le
    linarith [hb]
  have h1 : ξ * (1 + 2 * ξ - 2 * η) * (1 + 2 * η - 2 * ξ) ≥
      1 * (1 + 2 * η - 2 * ξ) :=
    mul_le_mul_of_nonneg_right ha (le_of_lt hq_pos)
  have h2 : η * (1 + 2 * η - 2 * ξ) * (1 + 2 * ξ - 2 * η) ≥
      1 * (1 + 2 * ξ - 2 * η) :=
    mul_le_mul_of_nonneg_right hb (le_of_lt hp_pos)
  have h_expand : (ξ + η) * ((1 + 2 * ξ - 2 * η) * (1 + 2 * η - 2 * ξ)) =
    ξ * (1 + 2 * ξ - 2 * η) * (1 + 2 * η - 2 * ξ) +
    η * (1 + 2 * η - 2 * ξ) * (1 + 2 * ξ - 2 * η) := by ring
  have h_pq_sum : (1 + 2 * ξ - 2 * η) + (1 + 2 * η - 2 * ξ) = 2 := by ring
  have h_prod :
    (ξ + η) * ((1 + 2 * ξ - 2 * η) * (1 + 2 * η - 2 * ξ)) ≥ 2 := by linarith
  have h_pq_lt : (1 + 2 * ξ - 2 * η) * (1 + 2 * η - 2 * ξ) < 1 := by
    have h_ring : (1 + 2 * ξ - 2 * η) * (1 + 2 * η - 2 * ξ) =
      1 - 4 * ((ξ - η) * (ξ - η)) := by ring
    have h_sq : (0 : ℝ) < (ξ - η) * (ξ - η) := mul_pos (by linarith) (by linarith)
    linarith
  have h_sum_ge : ξ + η > 2 := by
    by_contra h_le; push Not at h_le
    have h_strict : (0 : ℝ) < (ξ + η) *
        (1 - (1 + 2 * ξ - 2 * η) * (1 + 2 * η - 2 * ξ)) :=
      mul_pos (by linarith) (by linarith)
    have h_ident : (ξ + η) * ((1 + 2 * ξ - 2 * η) * (1 + 2 * η - 2 * ξ)) +
        (ξ + η) * (1 - (1 + 2 * ξ - 2 * η) * (1 + 2 * η - 2 * ξ)) =
      ξ + η := by ring
    linarith
  linarith

/-! ### Theorem 1: IV condition (12) is vacuous at KKT points -/

set_option maxHeartbeats 400000 in
/-- **Theorem 1 (end-to-end).** For any `F > 0`, `t > 0`, `n_L > 1`,
no KKT point of the supplier's Hotelling problem in the strict
waterbed regime `ξ > η ≥ 0` satisfies IV condition (12).

The conclusion `ξ(1 + y_S) ≤ 2 y_S(2 − y_S)` is the negation of
IV (12), with `y_S = (1 + η − ξ)/2` inlined. -/
theorem theorem1_vacuous
    (F t n_L : ℝ)
    (hF : F > 0) (ht : t > 0) (hn_L : n_L > 1)
    (ξ η μ_S μ_L β : ℝ)
    -- Strict waterbed regime
    (hξη : ξ > η) (hη : η ≥ 0)
    -- Interior market share
    (hyS_pos : 0 < (1 + η - ξ) / 2)
    -- KKT multiplier non-negativity (α = 0 since ξ > 0)
    (hμS : μ_S ≥ 0) (hμL : μ_L ≥ 0) (hβ : β ≥ 0)
    -- Participation constraint feasibility
    (hgS : F / t - ξ - ξ * η + ξ ^ 2 / 2 ≥ 0)
    (hgL : F / (t * n_L) - η - ξ * η + η ^ 2 / 2 ≥ 0)
    -- Stationarity (with α = 0)
    (hSξ : (1 / 2 + η - ξ) - (1 + η - ξ) * μ_S - η * μ_L = 0)
    (hSη : (1 / 2 + ξ - η) - ξ * μ_S - (1 + ξ - η) * μ_L + β = 0)
    -- Complementary slackness
    (hcsS : μ_S * (F / t - ξ - ξ * η + ξ ^ 2 / 2) = 0)
    (hcsL : μ_L * (F / (t * n_L) - η - ξ * η + η ^ 2 / 2) = 0)
    (hcsη : β * η = 0) :
    ξ * (1 + (1 + η - ξ) / 2) ≤
      2 * ((1 + η - ξ) / 2) * (2 - (1 + η - ξ) / 2) := by
  -- Abbreviate y_S
  set yS := (1 + η - ξ) / 2 with hyS_def
  -- yS < 1/2 from strict waterbed
  have hyS_hi : yS < 1 / 2 := by simp only [hyS_def]; linarith
  -- ξ > 0 from strict waterbed
  have hξ_pos : ξ > 0 := by linarith
  -- ξ < 1 + η from yS > 0
  have hξ_bound : ξ < 1 + η := by linarith [hyS_pos]
  -- ═══════════════════════════════════════════════════════════════
  -- Boundary case: η = 0
  -- ═══════════════════════════════════════════════════════════════
  by_cases hη0 : η = 0
  · -- At η = 0: g_L = F/(t·n_L) > 0, so μ_L = 0 by CS.
    -- Stationarity then forces β < 0, contradicting β ≥ 0.
    exfalso
    subst hη0
    -- Normalize hypotheses after η := 0 substitution
    simp only [mul_zero, zero_mul, sub_zero,
               add_zero] at hSξ hSη hcsS hcsL hgS hgL hyS_pos
    -- g_L = F/(t*n_L) > 0
    have hgL_pos : F / (t * n_L) > 0 :=
      div_pos hF (mul_pos ht (by linarith : (0 : ℝ) < n_L))
    -- μ_L = 0 from CS: μ_L * (F/(t*n_L)) = 0 and F/(t*n_L) > 0
    have hμL0 : μ_L = 0 := by
      rcases mul_eq_zero.mp hcsL with h | h
      · exact h
      · linarith
    -- ξ < 1 from yS > 0 at η = 0
    have hξ_lt : ξ < 1 := by linarith
    have hd : (1 : ℝ) - ξ ≠ 0 := by linarith
    -- From S_ξ at η = 0, μ_L = 0: (1-ξ)*μ_S = 1/2-ξ
    have h_muS_rel : (1 - ξ) * μ_S = 1 / 2 - ξ := by linarith [hμL0]
    -- μ_S = (1/2-ξ)/(1-ξ)
    have h_muS : μ_S = (1 / 2 - ξ) / (1 - ξ) := by
      rw [eq_div_iff hd]; linarith
    -- From S_η at η = 0, μ_L = 0: β = ξ*μ_S - (1/2+ξ)
    have h_beta : β = ξ * μ_S - (1 / 2 + ξ) := by
      rw [hμL0] at hSη; linarith
    -- Substitute μ_S:
    have h_beta_eq : β = ξ * ((1 / 2 - ξ) / (1 - ξ)) - (1 / 2 + ξ) := by
      rw [h_beta, h_muS]
    -- beta_neg_at_eta_zero: this expression < 0
    have h_neg := beta_neg_at_eta_zero ξ hξ_pos hξ_lt
    linarith
  -- ═══════════════════════════════════════════════════════════════
  -- Interior case: η > 0
  -- ═══════════════════════════════════════════════════════════════
  · have hη_pos : η > 0 := lt_of_le_of_ne hη (Ne.symm hη0)
    -- β = 0 from CS: β*η = 0 and η > 0
    have hβ0 : β = 0 := by
      rcases mul_eq_zero.mp hcsη with h | h
      · exact h
      · linarith
    -- Stationarity with β = 0
    have hSη' : (1 / 2 + ξ - η) - ξ * μ_S - (1 + ξ - η) * μ_L = 0 := by linarith
    -- The goal (using iv12_fails_at_kkt_upper_bound) needs:
    --   hyS_lo : 1/4 < yS
    --   hyS_hi : yS < 1/2
    --   hξ_hi  : ξ * (3 - 4 * yS) ≤ 1
    -- Case split on which participation constraints bind
    by_cases hgS0 : F / t - ξ - ξ * η + ξ ^ 2 / 2 = 0
    · -- g_S binds
      by_cases hgL0 : F / (t * n_L) - η - ξ * η + η ^ 2 / 2 = 0
      · -- ═════════════════════════════════════════════════════════
        -- Case 4: both PCs bind
        -- ═════════════════════════════════════════════════════════
        -- Step 1: ξ + η < 2 from constraint-difference identity
        have h_sum_lt : ξ + η < 2 := by
          -- F/t - F/(t*n_L) > 0
          have ht_ne : t ≠ 0 := ne_of_gt ht
          have hn_pos : (0 : ℝ) < n_L := by linarith
          have htn_pos : (0 : ℝ) < t * n_L := mul_pos ht hn_pos
          have hFdiff : F / t - F / (t * n_L) > 0 := by
            rw [div_sub_div _ _ ht_ne (ne_of_gt htn_pos)]
            apply div_pos
            · have : F * (t * n_L) - t * F = F * t * (n_L - 1) := by ring
              rw [this]; exact mul_pos (mul_pos hF ht) (by linarith)
            · exact mul_pos ht htn_pos
          -- From gS = gL = 0: F/t - F/(t*n_L) = (ξ-η) - (ξ²-η²)/2
          have h_eq : F / t - F / (t * n_L) + η - ξ + (ξ ^ 2 - η ^ 2) / 2 = 0 := by
            linarith
          -- If ξ+η ≥ 2: (ξ-η)(ξ+η-2) ≥ 0, so (ξ²-η²)/2 ≥ ξ-η, so F/t-F/(t*n_L) ≤ 0
          by_contra h_ge
          push Not at h_ge
          have h_nonneg : (0 : ℝ) ≤ (ξ - η) * (ξ + η - 2) :=
            mul_nonneg (by linarith) (by linarith)
          have h_expand : (ξ - η) * (ξ + η - 2) =
            ξ ^ 2 - η ^ 2 - 2 * ξ + 2 * η := by ring
          have h_half : (ξ ^ 2 - η ^ 2) / 2 ≥ ξ - η := by
            linarith [h_nonneg, h_expand]
          linarith [h_eq, hFdiff]
        -- Step 2: D > 0 by contradiction
        -- D = (1+η-ξ)(1+ξ-η) - ξη
        set D := (1 + η - ξ) * (1 + ξ - η) - ξ * η with hD_def
        have hD_pos : 0 < D :=
          D_pos_of_sum_lt_two ξ η μ_S μ_L hξη hη_pos hξ_pos hμS hμL h_sum_lt hSξ hSη'
        -- Step 3: ξ(3-4yS) ≤ 1 from (‡_S) + D > 0 + μ_S ≥ 0
        have hmS := multiplier_S_identity ξ η μ_S μ_L hSξ hSη'
        -- μ_S * D ≥ 0 (nonneg * pos)
        have h_mSD_nn : 0 ≤ μ_S * D := mul_nonneg hμS (le_of_lt hD_pos)
        -- So 1/2 - ξ/2 + ξη - ξ² ≥ 0, i.e., ξ(1+2ξ-2η) ≤ 1
        have h_xi_bound : ξ * (1 + 2 * ξ - 2 * η) ≤ 1 := by
          have : 2 * (1 / 2 - ξ / 2 + ξ * η - ξ ^ 2) =
            1 - ξ * (1 + 2 * ξ - 2 * η) := by ring
          linarith [hmS, h_mSD_nn]
        -- 3 - 4*yS = 1 + 2ξ - 2η
        have h_34yS : 3 - 4 * yS = 1 + 2 * ξ - 2 * η := by
          simp only [hyS_def]; ring
        -- yS > 1/4 (needed for iv12_fails_at_kkt_upper_bound)
        -- From (‡_L) + D > 0: μ_L ≥ 0 gives η(4yS-1) ≤ 1, so 4yS-1 could be anything.
        -- Instead derive from the interval being non-empty.
        -- From h_xi_bound and ξ ≥ 1-2yS (= ξ-η+η-... hmm):
        -- Actually, from η > 0 and the L-multiplier identity:
        have hmL := multiplier_L_identity ξ η μ_S μ_L hSξ hSη'
        have h_mLD_nn : 0 ≤ μ_L * D := mul_nonneg hμL (le_of_lt hD_pos)
        have h_eta_bound : η * (1 + 2 * η - 2 * ξ) ≤ 1 := by
          have : 2 * (1 / 2 - η / 2 + ξ * η - η ^ 2) =
            1 - η * (1 + 2 * η - 2 * ξ) := by ring
          linarith [hmL, h_mLD_nn]
        -- Need 1 + 2η - 2ξ > 0 for yS > 1/4. Use: if 1+2η-2ξ ≤ 0 then
        -- η*(1+2η-2ξ) ≤ 0 < 1, which is consistent. But we need another route.
        -- From h_sum_lt (ξ+η < 2) and h_xi_bound: ξ*(1+2ξ-2η) ≤ 1.
        -- Since 1+2ξ-2η > 0 (from yS < 1/2: 1+2ξ-2η = 3-4yS > 1):
        have h_p_pos : (0 : ℝ) < 1 + 2 * ξ - 2 * η := by
          have h2yS : 2 * yS = 1 + η - ξ := by rw [hyS_def]; ring
          linarith [hyS_hi]
        -- ξ ≤ 1/(1+2ξ-2η). Combined with ξ > 0 and 1+2ξ-2η > 1:
        -- ξ < 1. Then from ξ+η < 2: η < 2.
        -- From constraint-difference with gS=gL=0:
        -- (ξ-η)(2-ξ-η)/2 = F/t(1-1/n_L) > 0
        -- Need yS > 1/4, i.e., 1+η-ξ > 1/2, i.e., η > ξ-1/2.
        -- From ξ*(1+2ξ-2η) ≤ 1 and 1+2ξ-2η > 0: ξ ≤ 1/(1+2ξ-2η).
        -- And η = ξ-(1-2yS). So yS > 1/4 iff 1-2yS < 1/2 iff ξ-η < 1/2.
        -- From ξ ≤ 1/(1+2ξ-2η): set p = 1+2ξ-2η. ξ ≤ 1/p.
        -- η = ξ-1+2yS. And h_sum_lt: ξ+η < 2.
        -- From gS=gL=0 and ξ+η < 2, and ξ > η > 0.
        -- Let me derive yS > 1/4 from the multiplier identities + D > 0 + ξ+η < 2.
        -- If yS ≤ 1/4 then 1+2η-2ξ = 4yS-1 ≤ 0.
        -- η*(1+2η-2ξ) ≤ 0 (η > 0, factor ≤ 0). From h_eta_bound: this ≤ 1. OK.
        -- But from (‡_L): μ_L*D = 1/2 - η/2 + ξη - η² ≥ 0.
        -- So 1 - η + 2ξη - 2η² ≥ 0, i.e., η(1+2η-2ξ) ≤ 1.
        -- With 1+2η-2ξ ≤ 0 and η > 0: η(1+2η-2ξ) ≤ 0.
        -- μ_L*D = (1 - η(1+2η-2ξ))/2 ≥ 1/2 > 0. So μ_L > 0 (since D > 0).
        -- From CS: μ_L * gL = 0 and μ_L > 0: gL = 0. ✓ (consistent)
        -- Similarly, from (‡_S): μ_S*D ≥ 0 and ξ(1+2ξ-2η) ≤ 1.
        -- With 1+2ξ-2η = 3-4yS ≥ 2 (since yS ≤ 1/4): ξ ≤ 1/2.
        -- And η ≤ ξ - (1-2yS) with 1-2yS ≥ 1/2: η ≤ ξ-1/2 ≤ 0. Contradiction with η > 0!
        have hyS_lo : 1 / 4 < yS := by
          by_contra h_le
          push Not at h_le -- yS ≤ 1/4
          -- 1+2ξ-2η = 3-4yS ≥ 2
          have hp_ge : 1 + 2 * ξ - 2 * η ≥ 2 := by
            have h2yS : 2 * yS = 1 + η - ξ := by rw [hyS_def]; ring
            linarith
          -- ξ*(1+2ξ-2η) ≤ 1 and (1+2ξ-2η) ≥ 2: ξ ≤ 1/2
          have hξ_le : ξ ≤ 1 / 2 := by nlinarith [h_xi_bound]
          -- ξ-η = 1-2yS ≥ 1/2 (since yS ≤ 1/4)
          have h_diff : ξ - η ≥ 1 / 2 := by
            have h2yS : 2 * yS = 1 + η - ξ := by rw [hyS_def]; ring
            linarith
          -- η ≤ ξ - 1/2 ≤ 0
          linarith
        -- Apply iv12_fails_at_kkt_upper_bound
        have hξ_hi : ξ * (3 - 4 * yS) ≤ 1 := by rw [h_34yS]; exact h_xi_bound
        exact iv12_fails_at_kkt_upper_bound ξ yS hyS_lo hyS_hi hξ_hi
      · -- ═════════════════════════════════════════════════════════
        -- Case 2: g_S binds, g_L slack → μ_L = 0
        -- ═════════════════════════════════════════════════════════
        exfalso
        -- g_L > 0
        have hgL_pos : F / (t * n_L) - η - ξ * η + η ^ 2 / 2 > 0 :=
          lt_of_le_of_ne hgL (Ne.symm hgL0)
        -- μ_L = 0 from CS
        have hμL0 : μ_L = 0 := by
          by_contra h
          have hμL_pos : μ_L > 0 := lt_of_le_of_ne hμL (Ne.symm h)
          have := mul_pos hμL_pos hgL_pos
          linarith [hcsL]
        -- From stationarity with μ_L = 0, β = 0:
        -- S_ξ: (1+η-ξ)*μ_S = 1/2+η-ξ
        -- S_η: ξ*μ_S = 1/2+ξ-η
        have h_eq1 : (1 + η - ξ) * μ_S = 1 / 2 + η - ξ := by
          have : η * μ_L = 0 := by rw [hμL0]; ring
          linarith [hSξ]
        have h_eq2 : ξ * μ_S = 1 / 2 + ξ - η := by
          have : (1 + ξ - η) * μ_L = 0 := by rw [hμL0]; ring
          linarith [hSη']
        -- Cross-multiply to eliminate μ_S:
        -- ξ*(1/2+η-ξ) = (1+η-ξ)*(1/2+ξ-η)
        have h_cross : ξ * (1 / 2 + η - ξ) = (1 + η - ξ) * (1 / 2 + ξ - η) := by
          have h3 : ξ * ((1 + η - ξ) * μ_S) = ξ * (1 / 2 + η - ξ) := by rw [h_eq1]
          have h4 : (1 + η - ξ) * (ξ * μ_S) = (1 + η - ξ) * (1 / 2 + ξ - η) := by rw [h_eq2]
          have : ξ * ((1 + η - ξ) * μ_S) = (1 + η - ξ) * (ξ * μ_S) := by ring
          linarith
        have h_star : η * (1 + 2 * η - 2 * ξ) = 1 := by
          have : 2 * (ξ * (1 / 2 + η - ξ)) - 2 * ((1 + η - ξ) * (1 / 2 + ξ - η)) =
            η * (1 + 2 * η - 2 * ξ) - 1 := by ring
          linarith [h_cross]
        -- q := 1+2η-2ξ must be positive (since η > 0 and η*q = 1 > 0)
        have hq_pos : (0 : ℝ) < 1 + 2 * η - 2 * ξ := by
          by_contra h_le
          push Not at h_le
          have := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hη_pos) h_le
          linarith
        -- q < 1 (since ξ > η means 2ξ > 2η means 1+2η-2ξ < 1)
        have hq_lt : 1 + 2 * η - 2 * ξ < 1 := by linarith
        -- η > 1 (from η*q = 1, q ∈ (0,1): η > 1)
        have hη_gt_1 : η > 1 := by
          by_contra h_le; push Not at h_le
          have := mul_lt_mul_of_pos_left hq_lt hη_pos
          linarith [h_star]
        -- ξ + η > 2 (since ξ > η > 1)
        have h_sum_gt : ξ + η > 2 := by linarith
        -- Now show g_L < 0 from constraint-difference + g_S = 0.
        -- g_S - g_L = (F/t - F/(t*n_L)) + (η-ξ) + (ξ²-η²)/2
        -- With g_S = 0: g_L = -(F/t-F/(t*n_L)) - (η-ξ) - (ξ²-η²)/2
        --                   = -(F/t-F/(t*n_L)) + (ξ-η) - (ξ²-η²)/2
        --                   = -(F/t-F/(t*n_L)) - (ξ-η)((ξ+η)/2-1)
        -- Both terms are negative, so g_L < 0.
        -- F/t - F/(t*n_L) > 0:
        have ht_ne : t ≠ 0 := ne_of_gt ht
        have hn_pos : (0 : ℝ) < n_L := by linarith
        have htn_pos : (0 : ℝ) < t * n_L := mul_pos ht hn_pos
        have hFdiff : F / t - F / (t * n_L) > 0 := by
          rw [div_sub_div _ _ ht_ne (ne_of_gt htn_pos)]
          apply div_pos
          · have : F * (t * n_L) - t * F = F * t * (n_L - 1) := by ring
            rw [this]; exact mul_pos (mul_pos hF ht) (by linarith)
          · exact mul_pos ht htn_pos
        -- From gS = 0: F/t - F/(t*n_L) + (η-ξ) + (ξ²-η²)/2 = -gL
        have h_gL_eq : F / t - F / (t * n_L) + (η - ξ) + (ξ ^ 2 - η ^ 2) / 2 =
            -(F / (t * n_L) - η - ξ * η + η ^ 2 / 2) := by linarith
        -- (η-ξ) + (ξ²-η²)/2 = (ξ-η)((ξ+η)/2-1) > 0 (see below, both factors > 0... wait)
        -- Actually (η-ξ) + (ξ²-η²)/2 = -(ξ-η) + (ξ-η)(ξ+η)/2 = (ξ-η)((ξ+η)/2-1)
        -- Since ξ > η and ξ+η > 2: this is > 0.
        have h_poly_pos : (η - ξ) + (ξ ^ 2 - η ^ 2) / 2 > 0 := by
          have : (η - ξ) + (ξ ^ 2 - η ^ 2) / 2 = (ξ - η) * ((ξ + η) / 2 - 1) := by ring
          rw [this]
          exact mul_pos (by linarith) (by linarith)
        -- So -gL = F/t - F/(t*n_L) + (positive) > 0, hence gL < 0
        linarith
    · -- g_S slack → μ_S = 0
      have hgS_pos : F / t - ξ - ξ * η + ξ ^ 2 / 2 > 0 :=
        lt_of_le_of_ne hgS (Ne.symm hgS0)
      have hμS0 : μ_S = 0 := by
        by_contra h
        have hμS_pos : μ_S > 0 := lt_of_le_of_ne hμS (Ne.symm h)
        have := mul_pos hμS_pos hgS_pos
        linarith [hcsS]
      by_cases hgL0 : F / (t * n_L) - η - ξ * η + η ^ 2 / 2 = 0
      · -- ═════════════════════════════════════════════════════════
        -- Case 3: g_L binds, g_S slack → μ_S = 0
        -- ═════════════════════════════════════════════════════════
        -- From stationarity with μ_S = 0, β = 0, derive ξ(3-4yS) = 1
        have h_eq1 : η * μ_L = 1 / 2 + η - ξ := by
          have : (1 + η - ξ) * μ_S = 0 := by rw [hμS0]; ring
          linarith [hSξ]
        have h_eq2 : (1 + ξ - η) * μ_L = 1 / 2 + ξ - η := by
          have : ξ * μ_S = 0 := by rw [hμS0]; ring
          linarith [hSη']
        -- Cross-multiply to eliminate μ_L:
        have h_cross : η * (1 / 2 + ξ - η) = (1 + ξ - η) * (1 / 2 + η - ξ) := by
          have h3 : (1 + ξ - η) * (η * μ_L) = (1 + ξ - η) * (1 / 2 + η - ξ) := by rw [h_eq1]
          have h4 : η * ((1 + ξ - η) * μ_L) = η * (1 / 2 + ξ - η) := by rw [h_eq2]
          have : (1 + ξ - η) * (η * μ_L) = η * ((1 + ξ - η) * μ_L) := by ring
          linarith
        have hξ_eq : ξ * (1 + 2 * ξ - 2 * η) = 1 := by
          have : 2 * (η * (1 / 2 + ξ - η)) - 2 * ((1 + ξ - η) * (1 / 2 + η - ξ)) =
            ξ * (1 + 2 * ξ - 2 * η) - 1 := by ring
          linarith [h_cross]
        -- 3 - 4*yS = 1+2ξ-2η
        have h_34yS : 3 - 4 * yS = 1 + 2 * ξ - 2 * η := by
          simp only [hyS_def]; ring
        -- ξ*(3-4yS) = 1 ≤ 1
        have hξ_hi : ξ * (3 - 4 * yS) ≤ 1 := by rw [h_34yS]; linarith [hξ_eq]
        -- yS > 1/4: from η*μ_L = 2yS-1/2 and η > 0 and μ_L > 0
        have h_2yL_pos : (0 : ℝ) < 1 + ξ - η := by linarith
        have h_rhs_pos : (0 : ℝ) < 1 / 2 + ξ - η := by linarith
        have hμL_pos : μ_L > 0 := by
          by_contra h
          push Not at h
          have := mul_nonpos_of_nonneg_of_nonpos (le_of_lt h_2yL_pos) h
          linarith [h_eq2]
        have hyS_lo : 1 / 4 < yS := by
          have h_prod := mul_pos hη_pos hμL_pos
          have h2yS : 2 * yS = 1 + η - ξ := by rw [hyS_def]; ring
          linarith [h_eq1]
        exact iv12_fails_at_kkt_upper_bound ξ yS hyS_lo hyS_hi hξ_hi
      · -- ═════════════════════════════════════════════════════════
        -- Case 1: both PCs slack → μ_S = μ_L = 0
        -- ═════════════════════════════════════════════════════════
        exfalso
        have hgL_pos : F / (t * n_L) - η - ξ * η + η ^ 2 / 2 > 0 :=
          lt_of_le_of_ne hgL (Ne.symm hgL0)
        have hμL0 : μ_L = 0 := by
          by_contra h
          have hμL_pos : μ_L > 0 := lt_of_le_of_ne hμL (Ne.symm h)
          have := mul_pos hμL_pos hgL_pos
          linarith [hcsL]
        -- Substitute μ_S = μ_L = 0 into stationarity: 1/2+η-ξ = 0 and 1/2+ξ-η = 0
        rw [hμS0, hμL0] at hSξ hSη'
        simp only [mul_zero] at hSξ hSη'
        linarith

end LeanWaterbed.Theorem1
