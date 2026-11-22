# MWGPrincipalAgent

Formalization of Mas-Colell, Whinston and Green, *Microeconomic Theory*, Chapter 14, "The
Principal-Agent Problem", pp. 477-510, with Appendices A and B. It covers hidden actions (14.B):
the observable-effort benchmark (Proposition 14.B.1), a risk-neutral manager and selling the
project (Proposition 14.B.2), a risk-averse manager with two efforts (the Kuhn-Tucker condition
(14.B.10), Lemma 14.B.1, footnote 8, the likelihood-ratio form of the optimal scheme and the
monotone likelihood ratio property, Figure 14.B.1, Proposition 14.B.3), and an extra signal
(14.B.11). It covers hidden information (14.C): the observable-state contract (Proposition
14.C.1), the revelation principle (Proposition 14.C.2), the infinitely risk-averse manager
(footnote 15), Lemmas 14.C.1-14.C.4, (14.C.9) and Proposition 14.C.3, and monopolistic screening
(14.C.10) with the Maskin-Riley and Baron-Myerson models. It covers hybrid models (14.D),
Appendix A (multiple efforts, the first-order approach) and Appendix B (the Kuhn-Tucker analysis),
and the end-of-chapter exercises. Profits in Section 14.B have a density with respect to an
arbitrary measure, so the continuum model and the discrete version of footnote 6 are both
covered. The Kuhn-Tucker conditions of footnote 7, (14.B.10), Exercise 14.B.2 and (14.AA.3) are
proved necessary as well as sufficient: the programs are convex-like in utility levels, and a
separation argument in the finite-dimensional space of constraint values (`KuhnTucker`) gives the
multipliers with no topology on the set of schemes. The audit passed **331 theorems and 510
declarations across 34 modules**. Coverage is in the [source map](docs/source-map.md); no item is
OPEN. Departures from the printed text are in [corrections](docs/corrections.md); among them are
an inconsistency in the assumptions on `g` (p. 489), a misprinted example (footnote 21), the tie
case of Proposition 14.B.3, the claim of Appendix A that `e_H` can always be induced, and the
strict reading of Exercise 14.AA.1.

This is a Lake project pinned to Lean and Mathlib `v4.34.0`. It imports (Lake requirement, no
copies) MWG Chapter 13 (`MWGAdverseSelection`: the productive-task screening model and
`exercise_13_D_1`, used in Exercise 14.C.6) and, through that requirement, MWG Chapter 3
(`MWGClassicalDemand`: `exercise_3_C_6c`, the CES limit used in footnote 15). Jensen's
inequality and the facts on risk aversion that MWG takes from Chapter 6 are proved here
(`Basic`). See [third-party notices](THIRD_PARTY_NOTICES.md).

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Basic](MWGPrincipalAgent/Basic.lean) | 10 | Tangent lines of concave and convex functions; Jensen for densities (weak and strict); two-point Jensen |
| [KuhnTucker](MWGPrincipalAgent/KuhnTucker.lean) | 4 | Necessity of the Kuhn-Tucker conditions for convex-like programs (inequality constraints with Slater; an added equality constraint), by separation in `ℝ × ℝᵏ` |
| [HiddenAction](MWGPrincipalAgent/HiddenAction.lean) | 19 | The hidden-action model; observable effort (14.B.1)-(14.B.5), Proposition 14.B.1; Proposition 14.B.2 (selling the project) |
| [RiskAverse](MWGPrincipalAgent/RiskAverse.lean) | 21 | Two efforts with a risk-averse manager: (14.B.9)-(14.B.10), footnote 7 (sufficiency), Lemma 14.B.1, footnote 8, likelihood ratios and MLRP, Proposition 14.B.3, footnote 9 |
| [Discrete](MWGPrincipalAgent/Discrete.lean) | 4 | Finitely many profit levels (footnote 6): counting measures |
| [ExampleHA](MWGPrincipalAgent/ExampleHA.lean) | 25 | Concrete hidden-action models: Figure 14.B.1, instances of Lemma 14.B.1 and Propositions 14.B.1-14.B.3, the tie counterexample |
| [Signal](MWGPrincipalAgent/Signal.lean) | 7 | An extra signal of effort: (14.B.11), sufficient statistics, the Jensen improvement |
| [AppendixA](MWGPrincipalAgent/AppendixA.lean) | 6 | Appendix A: (14.AA.1)-(14.AA.3), Figure 14.AA.1, implementability (corrected), the first-order approach and its failure |
| [Screen](MWGPrincipalAgent/Screen.lean) | 17 | The two-type screening program (14.C.8)/(14.C.10)/(14.BB.1): Lemmas 14.C.1-14.C.3, characterization of the optimum, Exercise 14.BB.1 |
| [HiddenInfo](MWGPrincipalAgent/HiddenInfo.lean) | 31 | The hidden-information model: Propositions 14.C.1 and 14.C.3, Lemma 14.C.4, (14.C.9), footnote 17, Appendix B Steps 1-5 |
| [ExampleHI](MWGPrincipalAgent/ExampleHI.lean) | 13 | A concrete hidden-information model with its optimal contract |
| [InfRiskAversion](MWGPrincipalAgent/InfRiskAversion.lean) | 6 | Infinite risk aversion and footnote 15 (via Chapter 3, Exercise 3.C.6) |
| [Revelation](MWGPrincipalAgent/Revelation.lean) | 6 | Proposition 14.C.2 (revelation principle); Section 14.D hybrid models |
| [Monopolistic](MWGPrincipalAgent/Monopolistic.lean) | 5 | Monopolistic screening (14.C.10): footnote 21 (correction), Maskin-Riley, Baron-Myerson |
| [ExercisesC](MWGPrincipalAgent/ExercisesC.lean) | 10 | Exercises 14.C.2, 14.C.3, 14.C.5, 14.C.6 (with Chapter 13, Exercise 13.D.1) |
| [ExercisesAA](MWGPrincipalAgent/ExercisesAA.lean) | 9 | Exercises 14.AA.1 (with correction) and 14.AA.2 |
| [ExerciseB4](MWGPrincipalAgent/ExerciseB4.lean) | 9 | Exercise 14.B.4: three efforts, upward distortion |
| [ExercisesB](MWGPrincipalAgent/ExercisesB.lean) | 6 | Exercises 14.B.2 (risk-averse owner) and 14.B.3 (linear schemes, normal profits) |
| [HANecessity](MWGPrincipalAgent/HANecessity.lean) | 16 | Necessity of (14.B.10) (footnote 7), Lemma 14.B.1 for every solution, Exercise 14.B.2 and (14.AA.3): utility mixtures, Slater, pointwise minimization; instances |
| [ExercisesB56](MWGPrincipalAgent/ExercisesB56.lean) | 11 | Exercises 14.B.5 (free disposal) and 14.B.6 (revenues and costs) |
| [ExerciseB6Opt](MWGPrincipalAgent/ExerciseB6Opt.lean) | 2 | Exercise 14.B.6(b): with revenue reduction the optimal scheme depends on costs only |
| [ExerciseC8](MWGPrincipalAgent/ExerciseC8.lean) | 7 | Exercise 14.C.8 (Air Shangri-la) |
| [ExerciseC9](MWGPrincipalAgent/ExerciseC9.lean) | 5 | Exercise 14.C.9 (monopoly insurance) |
| [ExerciseC9KT](MWGPrincipalAgent/ExerciseC9KT.lean) | 4 | Exercise 14.C.9(b): the shape of every optimal menu (necessity of the Kuhn-Tucker conditions) |
| [ExerciseC7](MWGPrincipalAgent/ExerciseC7.lean) | 11 | Exercise 14.C.7 (Tirole): linear, discriminating, two-part and nonlinear pricing |
| [ExerciseB1](MWGPrincipalAgent/ExerciseB1.lean) | 12 | Exercise 14.B.1: the participation constraint need not bind |
| [ExerciseC1](MWGPrincipalAgent/ExerciseC1.lean) | 5 | Exercise 14.C.1: finitely many states, local incentive constraints (footnote 16) |
| [ExerciseC1Opt](MWGPrincipalAgent/ExerciseC1Opt.lean) | 11 | Exercise 14.C.1: the optimal contract with `N` states (binding constraints, virtual surplus, no distortion at the top, downward distortion) |
| [ExerciseC4](MWGPrincipalAgent/ExerciseC4.lean) | 11 | Exercise 14.C.4: a finitely risk-averse manager (characterization, strict distortion, instance) |
| [ExerciseC1Strict](MWGPrincipalAgent/ExerciseC1Strict.lean) | 3 | Exercise 14.C.1: strict downward distortion below the top |
| [ExerciseB7](MWGPrincipalAgent/ExerciseB7.lean) | 5 | Exercise 14.B.7: two periods; inverse Euler condition; period-2 wages depend on period-1 profits |
| [ExerciseB8](MWGPrincipalAgent/ExerciseB8.lean) | 8 | Exercise 14.B.8: costly investigation (perspective convexity, Kuhn-Tucker characterization) |
| [ExerciseC3N](MWGPrincipalAgent/ExerciseC3N.lean) | 3 | Exercise 14.C.3(a): necessity of the first-order conditions |
| [Instances](MWGPrincipalAgent/Instances.lean) | 9 | Proved instances of hypotheses of the main results |

## Build and verify

From this chapter directory:

```sh
lake build
python3 -m unittest discover -s scripts -p 'test_*.py' -v
python3 scripts/verify.py
```

The verifier builds the library, recompiles all sources in a fresh file, and audits every
declaration's axioms (only `propext`, `Classical.choice` and `Quot.sound` are allowed).
