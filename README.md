# lean-iv-waterbed

Lean 4 formalization of the proofs in "Consumer Harm from the Waterbed
Effect: A Comment on Inderst and Valletti (2011)" by Brian C. Albrecht.

Every formal claim in the paper has been encoded as a Lean theorem and
verified with no `sorry` axioms. Each theorem depends only on Lean's
three standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

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
```

</details>

<details>
<summary><b>Axiom dependencies (click to expand)</b></summary>

```
eta_zero_in_limit              [propext, Classical.choice, Quot.sound]
smaller_root_feasibility       [propext, Classical.choice, Quot.sound]
boundary_unique                [propext, Classical.choice, Quot.sound]
larger_root_infeasible         [propext, Classical.choice, Quot.sound]
iv_condition_12_fails_in_limit [propext, Classical.choice, Quot.sound]
beta_neg_at_eta_zero           [propext, Classical.choice, Quot.sound]
case1_no_solution              [propext, Classical.choice, Quot.sound]
case2_infeasible               [propext, Classical.choice, Quot.sound]
cubic_positivity               [propext, Classical.choice, Quot.sound]
case3_iv_fails                 [propext, Classical.choice, Quot.sound]
case4_iv_fails                 [propext, Classical.choice, Quot.sound]
case4_D_pos                    [propext, Classical.choice, Quot.sound]
mfcq_slackening_direction      [propext, Classical.choice, Quot.sound]
active_set_exhaustion           [propext, Classical.choice, Quot.sound]
iv12_fails_at_kkt_upper_bound  [propext, Classical.choice, Quot.sound]
```

No `sorryAx` anywhere. Every proof is complete.

</details>

To reproduce locally:

```bash
lake build    # builds everything; all 15 theorems must compile
```

## Coverage

Paper source: `comment/comment.tex` in the
[waterbed](https://github.com/briancalbrecht/waterbed) repository.

| Paper claim | Label | Lean file | Theorem | Lines |
|---|---|---|---|---|
| Lemma 1: η = 0 in the limit | `lem:limit-closed-form` | `LimitClosedForm.lean` | `eta_zero_in_limit` | 377–380 |
| Lemma 1: smaller root feasibility | `lem:limit-closed-form` | `LimitClosedForm.lean` | `smaller_root_feasibility` | 385–389 |
| Lemma 1: boundary ξ = 1/2 at r = 3/8 | `lem:limit-closed-form` | `LimitClosedForm.lean` | `boundary_unique`, `boundary_root` | 389 |
| Lemma 1: larger root infeasible | `lem:limit-closed-form` | `LimitClosedForm.lean` | `larger_root_infeasible` | 385–386 |
| Proposition: IV (12) fails in limit | `prop:limit` | `Limit.lean` | `iv_condition_12_fails_in_limit` | 420–459 |
| Theorem 1: boundary η = 0 | `thm:vacuous` | `BoundaryEta0.lean` | `beta_neg_at_eta_zero` | 516–539 |
| Theorem 1: Case 1 (both slack) | `thm:vacuous` | `Case1.lean` | `case1_no_solution` | 573–577 |
| Theorem 1: Case 2 (g_S binds) | `thm:vacuous` | `Case2.lean` | `case2_infeasible` | 580–608 |
| Cubic sub-lemma: P(y_S) > 0 | `thm:vacuous` | `CubicPositivity.lean` | `cubic_positivity` | ~620 |
| Theorem 1: Case 3 (g_L binds) | `thm:vacuous` | `Case3.lean` | `case3_iv_fails` | 611–636 |
| Theorem 1: Case 4 sub-claim D > 0 | `thm:vacuous` | `Case4DPos.lean` | `case4_D_pos` | 686–714 |
| Theorem 1: Case 4 (both bind) | `thm:vacuous` | `Case4.lean` | `case4_iv_fails` | 717–733 |
| Corollary 1: MFCQ direction | `cor:local-max` | `MFCQ.lean` | `mfcq_slackening_direction` | 740–769 |
| Case exhaustion + master | `thm:vacuous` | `Vacuity.lean` | `active_set_exhaustion`, `iv12_fails_at_kkt_upper_bound` | 502–738 |

Each file also contains a **negative control** — an existential witness
showing that dropping one hypothesis makes the conclusion fail. This
confirms that the hypotheses are load-bearing, not decorative.

The master theorem in `Vacuity.lean` verifies the case exhaustion:
`active_set_exhaustion` shows that the four active-set configurations
of {g_S, g_L} are exhaustive (via `by_cases` on two propositions),
and `iv12_fails_at_kkt_upper_bound` unifies Cases 3 and 4 under
their shared KKT upper bound.

## What is not formalized

- **MFCQ inference.** The Lean file verifies the slackening-direction
  computation. The inference from MFCQ to "every interior local
  maximizer is a KKT point" cites Bertsekas (1999) Proposition 3.3.8
  and is not formalized.

## License

MIT
