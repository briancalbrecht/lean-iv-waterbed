import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.Order.Field.Basic

/-!
# Waterbed — Lemma 1: IV Proposition 5 closed form

Source: `comment.tex`,
Lemma 1 (`lem:limit-closed-form`).

## Paper argument (informal)

In the `n_L → ∞` limit, the large buyer's participation constraint
degenerates: η → 0. The small firm's binding constraint becomes the
quadratic `ξ² − 2ξ + 2F/t = 0`, with roots `ξ = 1 ± √(1 − 2F/t)`.
The larger root exceeds 1 and is infeasible (it forces `y_S ≤ 0`).
The smaller root `ξ = 1 − √(1 − 2F/t)` is real for `F/t ≤ 1/2`,
strictly positive for `F/t > 0`, and satisfies `ξ < 1/2` iff
`F/t < 3/8`. At `F/t = 3/8`, `ξ = 1/2` exactly.

## Lean encoding

The paper writes the closed form using `√`, but the mathematical
content is entirely about the quadratic `ξ² − 2ξ + 2r = 0` (where
`r = F/t`). We encode three polynomial claims that capture the root
selection without naming the root explicitly:

(a) **Feasibility**: the smaller root lies in `(0, 1/2)` when
    `0 < r < 3/8`.
(b) **Boundary**: at `r = 3/8`, the unique root below 1 is `ξ = 1/2`.
(c) **Infeasibility of the larger root**: any root `ξ ≥ 1` forces
    `y_S = (1 − ξ)/2 ≤ 0`.
-/

namespace LeanWaterbed.LimitClosedForm

/-- **Feasibility of the smaller root.** If `ξ` satisfies the
quadratic `ξ² − 2ξ + 2r = 0` with `0 < r < 3/8` and `ξ < 1`,
then `0 < ξ < 1/2`.

Source: `comment.tex`, Lemma 1. -/
theorem smaller_root_feasibility
    (ξ r : ℝ)
    (hr_pos : 0 < r) (hr_hi : r < 3 / 8)
    (hξ_lt1 : ξ < 1)
    (hquad : ξ ^ 2 - 2 * ξ + 2 * r = 0) :
    0 < ξ ∧ ξ < 1 / 2 := by
  constructor
  · -- ξ > 0: from the quadratic, ξ(ξ-2) = -2r, so ξ(2-ξ) = 2r > 0.
    -- Since ξ < 1 < 2, we have 2-ξ > 0, so ξ > 0.
    nlinarith [sq_nonneg ξ]
  · -- ξ < 1/2: from the quadratic, ξ² - 2ξ + 2r = 0, so ξ = 1 ± √(1-2r).
    -- For the smaller root (ξ < 1), ξ < 1/2 iff 2r < 3/4 iff r < 3/8.
    -- Algebraically: ξ < 1/2 iff ξ² > ξ (since ξ² - 2ξ + 2r = 0 gives
    -- ξ² = 2ξ - 2r, so ξ² > ξ iff 2ξ - 2r > ξ iff ξ > 2r).
    -- We need ξ > 2r AND ξ < 1/2. From the quadratic: ξ(2-ξ) = 2r,
    -- so if ξ ≥ 1/2 then 2r = ξ(2-ξ) ≥ (1/2)(3/2) = 3/4, i.e., r ≥ 3/8.
    -- Contrapositive: r < 3/8 implies ξ < 1/2.
    by_contra h
    push_neg at h
    -- h : 1/2 ≤ ξ, and hξ_lt1 : ξ < 1
    -- From quadratic: 2r = ξ(2-ξ) = 2ξ - ξ²
    -- With ξ ∈ [1/2, 1): ξ(2-ξ) is minimized at ξ=1/2 giving 3/4
    -- so 2r ≥ 3/4, r ≥ 3/8, contradicting hr_hi
    nlinarith [sq_nonneg (ξ - 1)]

/-- **Boundary value.** At `r = 3/8`, the quadratic has `ξ = 1/2` as
a root.

Source: `comment.tex` line 389, Lemma 1. -/
theorem boundary_root :
    (1 / 2 : ℝ) ^ 2 - 2 * (1 / 2) + 2 * (3 / 8) = 0 := by norm_num

/-- **Uniqueness at boundary.** At `r = 3/8`, `ξ = 1/2` is the only
root of the quadratic with `ξ < 1`.

Source: `comment.tex` line 389. -/
theorem boundary_unique
    (ξ : ℝ)
    (hξ_lt1 : ξ < 1)
    (hquad : ξ ^ 2 - 2 * ξ + 2 * (3 / 8) = 0) :
    ξ = 1 / 2 := by
  -- Quadratic: ξ² - 2ξ + 3/4 = 0, i.e., (ξ - 1/2)(ξ - 3/2) = 0.
  -- Roots: ξ = 1/2 or ξ = 3/2. Since ξ < 1, ξ = 1/2.
  have hfact : (ξ - 1 / 2) * (ξ - 3 / 2) = 0 := by nlinarith
  rcases mul_eq_zero.mp hfact with h | h
  · linarith
  · linarith

/-- **Infeasibility of the larger root.** Any root `ξ ≥ 1` of the
quadratic with `r > 0` forces `y_S = (1 − ξ)/2 ≤ 0`, which is
economically infeasible.

Source: `comment.tex`, Lemma 1. -/
theorem larger_root_infeasible
    (ξ r : ℝ)
    (hr_pos : 0 < r)
    (hξ_ge1 : ξ ≥ 1)
    (hquad : ξ ^ 2 - 2 * ξ + 2 * r = 0) :
    (1 - ξ) / 2 ≤ 0 := by
  -- ξ ≥ 1 implies 1 - ξ ≤ 0
  linarith

/-- **η = 0 in the limit.** From the binding constraint
`η(2 + 2ξ − η) = 0` with `2 + 2ξ − η > 0` (economically relevant
range), we conclude `η = 0`.

Source: `comment.tex`, Lemma 1. -/
theorem eta_zero_in_limit
    (η ξ : ℝ)
    (hfactor : η * (2 + 2 * ξ - η) = 0)
    (hdom : 2 + 2 * ξ - η > 0) :
    η = 0 := by
  rcases mul_eq_zero.mp hfactor with h | h
  · exact h
  · linarith

/-- **Negative control for feasibility.** Dropping `r < 3/8` (allowing
`r = 3/8`) makes `ξ < 1/2` fail. Witness: `ξ = 1/2, r = 3/8`. -/
example :
    ∃ ξ r : ℝ,
      0 < r ∧ ξ < 1 ∧ ξ ^ 2 - 2 * ξ + 2 * r = 0 ∧
        ¬(ξ < 1 / 2) := by
  refine ⟨1 / 2, 3 / 8, ?_, ?_, ?_, ?_⟩ <;> norm_num

/-- **Negative control for infeasibility.** Dropping `ξ ≥ 1` (allowing
the smaller root) makes `(1 − ξ)/2 > 0` achievable.
Witness: `ξ = 1/4, r = 7/32`. -/
example :
    ∃ ξ r : ℝ,
      0 < r ∧ ξ ^ 2 - 2 * ξ + 2 * r = 0 ∧
        (1 - ξ) / 2 > 0 := by
  refine ⟨1 / 4, 7 / 32, ?_, ?_, ?_⟩ <;> norm_num

end LeanWaterbed.LimitClosedForm
