# lean-iv-waterbed

Lean 4 formalization of the proofs in "Consumer Harm from the Waterbed
Effect: A Comment on Inderst and Valletti (2011)" by Brian C. Albrecht.

Every formal claim in the paper has been encoded as a Lean theorem and
verified with no `sorry` axioms. Each theorem depends only on Lean's
three standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

The main result is `theorem1_vacuous`: an end-to-end theorem that takes
the full KKT system as hypotheses and proves IV condition (12) fails at
every KKT point in the strict waterbed regime.

## Build

Requires [elan](https://github.com/leanprover/elan) (Lean version
manager). Mathlib is fetched automatically.

```bash
lake build
```

## Verification output

Every `#check` prints the theorem's type signature — the formal claim
itself, readable as mathematics. Every `#print axioms` confirms the
proof depends only on Lean's three foundational axioms (no `sorry`).

<details>
<summary><b>Type signatures (click to expand)</b></summary>

```
eta_zero_in_limit :
  ∀ (η ξ : ℝ), η * (2 + 2 * ξ - η) = 0 → 2 + 2 * ξ - η > 0 → η = 0

smaller_root_feasibility :
  ∀ (ξ r : ℝ), 0 < r → r < 3 / 8 → ξ < 1 → ξ ^ 2 - 2 * ξ + 2 * r = 0 → 0 < ξ ∧ ξ < 1 / 2

boundary_root :
  (1 / 2) ^ 2 - 2 * (1 / 2) + 2 * (3 / 8) = 0

boundary_unique :
  ∀ ξ < 1, ξ ^ 2 - 2 * ξ + 2 * (3 / 8) = 0 → ξ = 1 / 2

larger_root_infeasible :
  ∀ (ξ r : ℝ), 0 < r → ξ ≥ 1 → ξ ^ 2 - 2 * ξ + 2 * r = 0 → (1 - ξ) / 2 ≤ 0

iv_condition_12_fails_in_limit :
  ∀ (ξ y_S : ℝ), 0 < ξ → ξ < 1 / 2 → y_S = (1 - ξ) / 2 → ξ ≤ 2 * y_S * (2 - y_S) / (1 + y_S)

beta_neg_at_eta_zero :
  ∀ (ξ : ℝ), 0 < ξ → ξ < 1 → ξ * ((1 / 2 - ξ) / (1 - ξ)) - (1 / 2 + ξ) < 0

case1_no_solution :
  ∀ (ξ η : ℝ), ξ > η → η ≥ 0 → ξ < 1 → η < 1 → ¬(1 / 2 + η - ξ = 0 ∧ 1 / 2 + ξ - η = 0)

case2_infeasible :
  ∀ (yS : ℝ), 1 / 4 < yS → yS < 1 / 2 → 8 * yS ^ 2 + 2 * yS - 3 < 0

cubic_positivity :
  ∀ (yS : ℝ), 1 / 4 < yS → yS < 1 / 2 → 8 * yS ^ 3 - 22 * yS ^ 2 + 11 * yS - 1 > 0

cubic_nonneg :
  ∀ (yS : ℝ), 1 / 4 < yS → yS < 1 / 2 → 8 * yS ^ 3 - 22 * yS ^ 2 + 11 * yS - 1 ≥ 0

case3_iv_fails :
  ∀ (ξ yS : ℝ), 1 / 4 < yS → yS < 1 / 2 → ξ > 0 → ξ * (3 - 4 * yS) = 1 →
    ξ * (1 + yS) ≤ 2 * yS * (2 - yS)

case4_iv_fails :
  ∀ (ξ yS : ℝ), 1 / 4 < yS → yS < 1 / 2 → 1 - 2 * yS ≤ ξ → ξ * (3 - 4 * yS) ≤ 1 →
    ξ > 0 → ξ * (1 + yS) ≤ 2 * yS * (2 - yS)

case4_D_pos :
  ∀ (yS : ℝ), 1 / 4 < yS → yS < 1 / 2 → 4 * (2 * yS - 1) ^ 2 > 0

mfcq_slackening_direction :
  ∀ (ξ η : ℝ), ξ > 0 → η > 0 → ξ > η →
    (1 + η - ξ) / 2 > 0 → (1 + ξ - η) / 2 > 0 →
    (1 + η - ξ) / 2 < 1 → (1 + ξ - η) / 2 < 1 →
      2 * ((1 + η - ξ) / 2) + ξ > 0 ∧ η + 2 * ((1 + ξ - η) / 2) > 0

active_set_exhaustion :
  ∀ (P Q : Prop), P ∧ Q ∨ P ∧ ¬Q ∨ ¬P ∧ Q ∨ ¬P ∧ ¬Q

iv12_fails_at_kkt_upper_bound :
  ∀ (ξ yS : ℝ), 1 / 4 < yS → yS < 1 / 2 → ξ * (3 - 4 * yS) ≤ 1 →
    ξ * (1 + yS) ≤ 2 * yS * (2 - yS)

gS_directional_pos_at_eta_zero :
  ∀ (ξ : ℝ), ξ < 1 → (ξ - 1) * (-1 / (1 - ξ)) - ξ > 0

phi_directional_pos_at_eta_zero :
  ∀ (ξ : ℝ), 0 < ξ → ξ < 1 → (1 / 2 - ξ) * (-1 / (1 - ξ)) + (1 / 2 + ξ) > 0

eta_zero_improving_direction :
  ∀ (ξ : ℝ), 0 < ξ → ξ < 1 →
    ((ξ - 1) * (-1 / (1 - ξ)) - ξ > 0) ∧
      ((1 / 2 - ξ) * (-1 / (1 - ξ)) + (1 / 2 + ξ) > 0)

dpS_formula :
  ∀ (ξ yS : ℝ), yS ≠ 0 → 1 / 3 + 2 / 3 * (-ξ / (2 * yS)) = 1 / 3 - ξ / (3 * yS)

dpL_formula :
  ∀ (ξ yS : ℝ), yS ≠ 0 → 2 / 3 + 1 / 3 * (-ξ / (2 * yS)) = 2 / 3 - ξ / (6 * yS)

dCS_dwL_identity :
  ∀ (ξ yS : ℝ), yS ≠ 0 →
    -(yS * (1 / 3 - ξ / (3 * yS)) + (1 - yS) * (2 / 3 - ξ / (6 * yS))) =
    -(2 - yS) / 3 + (1 + yS) * ξ / (6 * yS)

cs_pos_of_iv12 :
  ∀ (ξ yS : ℝ), 0 < yS → ξ > 2 * yS * (2 - yS) / (1 + yS) →
    -(2 - yS) / 3 + (1 + yS) * ξ / (6 * yS) > 0

iv12_of_cs_pos :
  ∀ (ξ yS : ℝ), 0 < yS → -(2 - yS) / 3 + (1 + yS) * ξ / (6 * yS) > 0 →
    ξ > 2 * yS * (2 - yS) / (1 + yS)

cs_derivative_iff_iv12 :
  ∀ (ξ yS : ℝ), 0 < yS →
    (-(2 - yS) / 3 + (1 + yS) * ξ / (6 * yS) > 0 ↔
     ξ > 2 * yS * (2 - yS) / (1 + yS))

cs_equivalence_needs_yS_pos :
  ¬∀ (ξ yS : ℝ), -(2 - yS) / 3 + (1 + yS) * ξ / (6 * yS) > 0 →
    ξ > 2 * yS * (2 - yS) / (1 + yS)

multiplier_S_identity :
  ∀ (ξ η μ_S μ_L : ℝ),
    1 / 2 + η - ξ - (1 + η - ξ) * μ_S - η * μ_L = 0 →
      1 / 2 + ξ - η - ξ * μ_S - (1 + ξ - η) * μ_L = 0 →
        μ_S * ((1 + η - ξ) * (1 + ξ - η) - ξ * η) = 1 / 2 - ξ / 2 + ξ * η - ξ ^ 2

multiplier_L_identity :
  ∀ (ξ η μ_S μ_L : ℝ),
    1 / 2 + η - ξ - (1 + η - ξ) * μ_S - η * μ_L = 0 →
      1 / 2 + ξ - η - ξ * μ_S - (1 + ξ - η) * μ_L = 0 →
        μ_L * ((1 + η - ξ) * (1 + ξ - η) - ξ * η) = 1 / 2 - η / 2 + ξ * η - η ^ 2

theorem1_vacuous :
  ∀ (F t n_L : ℝ), F > 0 → t > 0 → n_L > 1 →
    ∀ (ξ η μ_S μ_L β : ℝ), ξ > η → η ≥ 0 → 0 < (1 + η - ξ) / 2 →
      μ_S ≥ 0 → μ_L ≥ 0 → β ≥ 0 →
        F / t - ξ - ξ * η + ξ ^ 2 / 2 ≥ 0 →
          F / (t * n_L) - η - ξ * η + η ^ 2 / 2 ≥ 0 →
            1 / 2 + η - ξ - (1 + η - ξ) * μ_S - η * μ_L = 0 →
              1 / 2 + ξ - η - ξ * μ_S - (1 + ξ - η) * μ_L + β = 0 →
                μ_S * (F / t - ξ - ξ * η + ξ ^ 2 / 2) = 0 →
                  μ_L * (F / (t * n_L) - η - ξ * η + η ^ 2 / 2) = 0 →
                    β * η = 0 →
                      ξ * (1 + (1 + η - ξ) / 2) ≤
                        2 * ((1 + η - ξ) / 2) * (2 - (1 + η - ξ) / 2)
```

</details>

<details>
<summary><b>Axiom dependencies (click to expand)</b></summary>

```
eta_zero_in_limit              [propext, Classical.choice, Quot.sound]
smaller_root_feasibility       [propext, Classical.choice, Quot.sound]
boundary_root                  [propext, Classical.choice, Quot.sound]
boundary_unique                [propext, Classical.choice, Quot.sound]
larger_root_infeasible         [propext, Classical.choice, Quot.sound]
iv_condition_12_fails_in_limit [propext, Classical.choice, Quot.sound]
beta_neg_at_eta_zero           [propext, Classical.choice, Quot.sound]
case1_no_solution              [propext, Classical.choice, Quot.sound]
case2_infeasible               [propext, Classical.choice, Quot.sound]
cubic_positivity               [propext, Classical.choice, Quot.sound]
cubic_nonneg                   [propext, Classical.choice, Quot.sound]
case3_iv_fails                 [propext, Classical.choice, Quot.sound]
case4_iv_fails                 [propext, Classical.choice, Quot.sound]
case4_D_pos                    [propext, Classical.choice, Quot.sound]
mfcq_slackening_direction      [propext, Classical.choice, Quot.sound]
active_set_exhaustion           [propext, Classical.choice, Quot.sound]
iv12_fails_at_kkt_upper_bound  [propext, Classical.choice, Quot.sound]
gS_directional_pos_at_eta_zero [propext, Classical.choice, Quot.sound]
phi_directional_pos_at_eta_zero [propext, Classical.choice, Quot.sound]
eta_zero_improving_direction   [propext, Classical.choice, Quot.sound]
dpS_formula                    [propext, Classical.choice, Quot.sound]
dpL_formula                    [propext, Classical.choice, Quot.sound]
dCS_dwL_identity               [propext, Classical.choice, Quot.sound]
cs_pos_of_iv12                 [propext, Classical.choice, Quot.sound]
iv12_of_cs_pos                 [propext, Classical.choice, Quot.sound]
cs_derivative_iff_iv12         [propext, Classical.choice, Quot.sound]
cs_equivalence_needs_yS_pos    [propext, Classical.choice, Quot.sound]
multiplier_S_identity          [propext, Classical.choice, Quot.sound]
multiplier_L_identity          [propext, Classical.choice, Quot.sound]
theorem1_vacuous               [propext, Classical.choice, Quot.sound]
```

No `sorryAx` anywhere. Every proof is complete.

</details>

To reproduce locally:

```bash
lake build    # builds everything; all 30 theorems must compile
```

## Coverage

Paper source: `comment.tex` in the companion paper "Consumer Harm from
the Waterbed Effect: A Comment on Inderst and Valletti (2011)."

| Paper claim | Label | Lean file | Theorem |
|---|---|---|---|
| Lemma 1: η = 0 in the limit | `lem:limit-closed-form` | `LimitClosedForm.lean` | `eta_zero_in_limit` |
| Lemma 1: smaller root feasibility | `lem:limit-closed-form` | `LimitClosedForm.lean` | `smaller_root_feasibility` |
| Lemma 1: boundary ξ = 1/2 at r = 3/8 | `lem:limit-closed-form` | `LimitClosedForm.lean` | `boundary_unique`, `boundary_root` |
| Lemma 1: larger root infeasible | `lem:limit-closed-form` | `LimitClosedForm.lean` | `larger_root_infeasible` |
| Proposition: IV (12) fails in limit | `prop:limit` | `Limit.lean` | `iv_condition_12_fails_in_limit` |
| Theorem 1: boundary η = 0 | `thm:vacuous` | `BoundaryEta0.lean` | `beta_neg_at_eta_zero` |
| Theorem 1: Case 1 (both slack) | `thm:vacuous` | `Case1.lean` | `case1_no_solution` |
| Theorem 1: Case 2 (g_S binds) | `thm:vacuous` | `Case2.lean` | `case2_infeasible` |
| Cubic sub-lemma: P(y_S) > 0 | `thm:vacuous` | `CubicPositivity.lean` | `cubic_positivity`, `cubic_nonneg` |
| Theorem 1: Case 3 (g_L binds) | `thm:vacuous` | `Case3.lean` | `case3_iv_fails` |
| Theorem 1: Case 4 sub-claim D > 0 | `thm:vacuous` | `Case4DPos.lean` | `case4_D_pos` |
| Theorem 1: Case 4 (both bind) | `thm:vacuous` | `Case4.lean` | `case4_iv_fails` |
| Corollary 1: MFCQ direction | `cor:local-max` | `MFCQ.lean` | `mfcq_slackening_direction` |
| Corollary 2: constraint slack direction | `cor:equilibrium` | `BoundaryDirection.lean` | `gS_directional_pos_at_eta_zero` |
| Corollary 2: objective improving direction | `cor:equilibrium` | `BoundaryDirection.lean` | `phi_directional_pos_at_eta_zero` |
| Corollary 2: η = 0 is improvable | `cor:equilibrium` | `BoundaryDirection.lean` | `eta_zero_improving_direction` |
| CS pass-through: dp_S/dw_L | setup derivation | `CSDerivativeEquivalence.lean` | `dpS_formula` |
| CS pass-through: dp_L/dw_L | setup derivation | `CSDerivativeEquivalence.lean` | `dpL_formula` |
| CS computation identity | setup derivation | `CSDerivativeEquivalence.lean` | `dCS_dwL_identity` |
| CS derivative: forward direction | setup derivation | `CSDerivativeEquivalence.lean` | `cs_pos_of_iv12` |
| CS derivative: reverse direction | setup derivation | `CSDerivativeEquivalence.lean` | `iv12_of_cs_pos` |
| CS derivative ≡ IV (12) | setup derivation | `CSDerivativeEquivalence.lean` | `cs_derivative_iff_iv12` |
| CS equivalence: yS > 0 needed | setup derivation | `CSDerivativeEquivalence.lean` | `cs_equivalence_needs_yS_pos` |
| Case exhaustion + unifier | `thm:vacuous` | `Vacuity.lean` | `active_set_exhaustion`, `iv12_fails_at_kkt_upper_bound` |
| Multiplier identity (‡_S) | `thm:vacuous` | `Theorem1.lean` | `multiplier_S_identity` |
| Multiplier identity (‡_L) | `thm:vacuous` | `Theorem1.lean` | `multiplier_L_identity` |
| **Theorem 1 (end-to-end)** | `thm:vacuous` | `Theorem1.lean` | `theorem1_vacuous` |

Each file also contains a **negative control** — an existential witness
showing that dropping one hypothesis makes the conclusion fail. This
confirms that the hypotheses are load-bearing, not decorative.

`Theorem1.lean` contains the end-to-end theorem: `theorem1_vacuous`
takes the full KKT system (stationarity, complementary slackness,
dual feasibility, primal feasibility) as hypotheses and proves IV
condition (12) fails, composing all sub-case results. `Vacuity.lean`
provides the intermediate `iv12_fails_at_kkt_upper_bound` that
unifies Cases 3 and 4 under their shared KKT upper bound.

## What is not formalized

- **MFCQ inference.** The Lean file verifies the slackening-direction
  computation. The inference from MFCQ to "every interior local
  maximizer is a KKT point" cites Bertsekas (1999) Proposition 3.3.8
  and is not formalized.

## License

MIT
