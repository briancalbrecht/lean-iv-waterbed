import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Order.Field.Basic

/-!
# Waterbed — impossibility of IV condition (12) in the `n_L → ∞` limit

Source: `comment.tex`,
proof of Proposition 6 in the `n_L → ∞` limit.

## Paper argument (informal)

In IV's equilibrium family in the `n_L → ∞` limit, the large buyer's
participation constraint degenerates (`η = 0`), so
`y_S = (1 - ξ) / 2` and the strict waterbed regime forces
`0 < ξ < 1/2`.

IV's condition (12) reads

    ξ > 2 · y_S · (2 - y_S) / (1 + y_S).

Substituting `y_S = (1 - ξ) / 2` and clearing the strictly positive
denominator `1 + y_S = (3 - ξ) / 2`, the condition becomes

    ξ · (3 - ξ) > (1 - ξ) · (3 + ξ),

equivalently `5 ξ > 3`, i.e. `ξ > 3/5`. Combined with `ξ < 1/2`, this
is a contradiction: IV's condition (12) cannot hold anywhere in the
limit equilibrium family.

## Lean formalization

We state the result as a non-strict inequality
`ξ ≤ 2 · y_S · (2 - y_S) / (1 + y_S)`, which is equivalent to the
negation of IV condition (12) and is the form `nlinarith` handles most
cleanly. A counterexample witness shows that dropping the upper bound
`ξ < 1/2` makes the IV condition feasible, mirroring the
`runNegativeControl` pattern from the Mathematica QE workflow.
-/

namespace LeanWaterbed.Limit

/-- **Waterbed limit lemma.** In the `n_L → ∞` limit of IV's Hotelling
model, the strict waterbed regime forces `0 < ξ < 1/2` and
`y_S = (1 - ξ) / 2`. Under these bindings, IV condition (12),
`ξ > 2 · y_S · (2 - y_S) / (1 + y_S)`, cannot hold.

Formally, we prove the negation of IV (12) as the inequality
`ξ ≤ 2 · y_S · (2 - y_S) / (1 + y_S)`.

Source: `comment.tex`, `n_L → ∞` case of Proposition 6. -/
theorem iv_condition_12_fails_in_limit
    (ξ y_S : ℝ)
    (hξpos : 0 < ξ) (hξlt : ξ < 1 / 2)
    (hy_eq : y_S = (1 - ξ) / 2) :
    ξ ≤ 2 * y_S * (2 - y_S) / (1 + y_S) := by
  subst hy_eq
  have hd : (0 : ℝ) < 1 + (1 - ξ) / 2 := by linarith
  rw [le_div_iff₀ hd]
  nlinarith [sq_nonneg ξ, sq_nonneg (1 - ξ)]

/-- **Negative control.** If we drop the upper bound `ξ < 1/2` but keep
the bindings `0 < ξ` and `y_S = (1 - ξ) / 2`, then IV condition (12)
becomes achievable. This mirrors the Mathematica `runNegativeControl`
witness pattern: the upper bound is load-bearing.

Witness: `ξ = 3/4`, so `y_S = 1/8`, and

    2 · (1/8) · (2 - 1/8) / (1 + 1/8) = (15/32) / (9/8) = 5/12 < 3/4. -/
example :
    ∃ ξ y_S : ℝ,
      0 < ξ ∧ y_S = (1 - ξ) / 2 ∧
        ξ > 2 * y_S * (2 - y_S) / (1 + y_S) := by
  refine ⟨3 / 4, 1 / 8, ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · norm_num

end LeanWaterbed.Limit
