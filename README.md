# lean-waterbed

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

## Verify axioms

```bash
cat > /tmp/verify.lean <<'EOF'
import LeanWaterbed
#print axioms LeanWaterbed.Limit.iv_condition_12_fails_in_limit
#print axioms LeanWaterbed.Case3.case3_iv_fails
EOF
lake env lean /tmp/verify.lean
```

Expected output: `[propext, Classical.choice, Quot.sound]` for every
theorem. If `sorryAx` appears, a proof is incomplete.

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

Each file also contains a **negative control** — an existential witness
showing that dropping one hypothesis makes the conclusion fail. This
confirms that the hypotheses are load-bearing, not decorative.

## What is not formalized

- **Case exhaustion.** The claim that boundary + Cases 1–4 exhaust all
  active sets of {g_S, g_L} is a combinatorial argument, verified by
  inspection.
- **MFCQ inference.** The Lean file verifies the slackening-direction
  computation. The inference from MFCQ to "every interior local
  maximizer is a KKT point" cites Bertsekas (1999) Proposition 3.3.8
  and is not formalized.

## License

MIT
