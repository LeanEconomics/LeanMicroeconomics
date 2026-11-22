# MWGChoiceUnderUncertainty

Formalization of Mas-Colell, Whinston and Green, *Microeconomic Theory*, Chapter 6, "Choice
Under Uncertainty", pp. 167-216: expected utility and the independence axiom (6.B), money
lotteries, risk aversion and the Arrow-Pratt measures with comparisons across individuals and
wealth levels (6.C), first- and second-order stochastic dominance (6.D), state-dependent utility
(6.E) and subjective probability (6.F), with all in-text and end-of-chapter exercises. The
chapter has no appendix. The audit passed **352 theorems and 442 declarations across
28 modules**. Coverage is in the [source map](docs/source-map.md); no item is OPEN.
Proposition 6.D.2 is proved in full for general distributions (the (i) ⇒ (ii) direction by
discretization, Kreps's finite coupling theorem, Prokhorov compactness and disintegration),
and Proposition 6.E.2 is proved with the correction "three *essential* states", the printed
version being refuted by a counterexample (correction 16). Departures from the printed text are in
[corrections](docs/corrections.md).

This is a Lake project pinned to Lean and Mathlib `v4.34.0`. It imports (Lake `path`
requirements) Kreps Chapter 5 (`ChoiceUnderUncertainty`: simple lotteries, mixture spaces,
Propositions 5.3, 5.4, 5.12 and the uniqueness theorems, through the bridge
`mixtureAxioms_of_mwg` from MWG's continuity and independence axioms), Kreps Chapter 6
(`UtilityForMoney`: absolute and relative risk aversion, Propositions 6.7-6.8 and 6.16(c),
constant absolute risk aversion, the local risk premium, the generalized quantile, the
finite coupling theorem `supermartingaleCoupling_of_dominance`), MWG Chapter 1
(`MWGPreferenceChoice`: rationality) and MWG Chapter 3 (`MWGClassicalDemand`: Exercise
3.G.4(c), used for Exercise 6.E.2(c), and Definition 3.C.1 with its bridge to Kreps's
continuity). Kreps Chapter 2 (`PreferenceProperties`, reached transitively through
`MWGClassicalDemand`) supplies Debreu's additive representation theorem
(`proposition_2_14_exists`) for Proposition 6.E.2. See [third-party notices](THIRD_PARTY_NOTICES.md).

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Lotteries](MWGChoiceUnderUncertainty/Lotteries.lean) | 11 | Section 6.B: simple and compound lotteries, Definitions 6.B.1-6.B.2, footnotes 2 and 4, Figures 6.B.2-6.B.3 |
| [ExpectedUtilityTheorem](MWGChoiceUnderUncertainty/ExpectedUtilityTheorem.lean) | 24 | Definitions 6.B.3-6.B.5, Exercises 6.B.1-6.B.3, Propositions 6.B.1-6.B.3 with Steps 1-3, footnotes 6-7; bridge to Kreps's mixture axioms |
| [ExpectedUtilityDiscussion](MWGChoiceUnderUncertainty/ExpectedUtilityDiscussion.lean) | 31 | Utility differences, Figure 6.B.5, Examples 6.B.1-6.B.4 (Allais, Machina), Dutch books, footnote 9, Exercises 6.B.4-6.B.7 |
| [MoneyLotteries](MWGChoiceUnderUncertainty/MoneyLotteries.lean) | 23 | Money lotteries, linearity of distribution functions, Figure 6.C.1, St. Petersburg, footnote 14, counterexample to (6.C.1) (correction 2) |
| [RiskAversion](MWGChoiceUnderUncertainty/RiskAversion.lean) | 20 | Definitions 6.C.1-6.C.2, (6.C.2), Proposition 6.C.1, strict risk aversion and neutrality, Figures 6.C.2-6.C.3, footnote 16, Exercise 6.C.3 |
| [InsuranceAssets](MWGChoiceUnderUncertainty/InsuranceAssets.lean) | 14 | Examples 6.C.1-6.C.3, footnote 17, Exercises 6.C.1 and 6.C.4 |
| [ArrowPratt](MWGChoiceUnderUncertainty/ArrowPratt.lean) | 7 | Definition 6.C.3, invariance, `r_A = 4π'(0)`, recovery of `u`, Example 6.C.4 |
| [MoreRiskAverse](MWGChoiceUnderUncertainty/MoreRiskAverse.lean) | 12 | Proposition 6.C.2 (all five equivalences), Exercises 6.C.6-6.C.7 |
| [WealthEffects](MWGChoiceUnderUncertainty/WealthEffects.lean) | 15 | Definitions 6.C.4-6.C.5, Propositions 6.C.3-6.C.4, Exercise 6.C.10 |
| [AssetComparative](MWGChoiceUnderUncertainty/AssetComparative.lean) | 11 | Partial ordering, Example 6.C.2 continued, Exercises 6.C.8 and 6.C.11 |
| [ExercisesC](MWGChoiceUnderUncertainty/ExercisesC.lean) | 8 | Exercises 6.C.2 and 6.C.5 |
| [ExercisesC2](MWGChoiceUnderUncertainty/ExercisesC2.lean) | 9 | Exercise 6.C.12 (corrections 6-7) |
| [ExercisesC3](MWGChoiceUnderUncertainty/ExercisesC3.lean) | 14 | Exercises 6.C.13, 6.C.14, 6.C.16, 6.C.18 |
| [ExercisesC4](MWGChoiceUnderUncertainty/ExercisesC4.lean) | 11 | Exercises 6.C.9 and 6.C.20 (corrections 8-9) |
| [ExercisesC5](MWGChoiceUnderUncertainty/ExercisesC5.lean) | 7 | Exercise 6.C.15 |
| [ExercisesC6](MWGChoiceUnderUncertainty/ExercisesC6.lean) | 15 | Exercises 6.C.17 and 6.C.19 |
| [FirstOrderDominance](MWGChoiceUnderUncertainty/FirstOrderDominance.lean) | 13 | Definition 6.D.1, Proposition 6.D.1 (general distributions), Example 6.D.1, Figure 6.D.2, Exercise 6.D.2 |
| [UpwardShift](MWGChoiceUnderUncertainty/UpwardShift.lean) | 1 | Example 6.D.1, converse: first-order dominance as an upward shift |
| [SecondOrderDominance](MWGChoiceUnderUncertainty/SecondOrderDominance.lean) | 6 | Definition 6.D.2, mean-preserving spreads, (6.D.1)-(6.D.2), Proposition 6.D.2 (ii) ⇒ (i) and (i) ⇒ (iii) |
| [SOSDApprox](MWGChoiceUnderUncertainty/SOSDApprox.lean) | 8 | Proposition 6.D.2 (iii) ⇒ (i) for all nondecreasing concave `u`, single crossing |
| [DominanceExamples](MWGChoiceUnderUncertainty/DominanceExamples.lean) | 15 | Examples 6.D.2-6.D.3, Exercises 6.D.1, 6.D.3, 6.D.4 |
| [StrassenGrid](MWGChoiceUnderUncertainty/StrassenGrid.lean) | 21 | Proposition 6.D.2 (i) ⇒ (ii), grid step: hat functions, dilation and contraction of a distribution |
| [StrassenFinite](MWGChoiceUnderUncertainty/StrassenFinite.lean) | 4 | Proposition 6.D.2 (i) ⇒ (ii), finite step: martingale coupling of the discretizations (Kreps's finite coupling) |
| [StrassenLimit](MWGChoiceUnderUncertainty/StrassenLimit.lean) | 6 | Proposition 6.D.2 (i) ⇒ (ii), limit step: Prokhorov cluster point with marginals `F`, `G` and the martingale identity |
| [Strassen](MWGChoiceUnderUncertainty/Strassen.lean) | 6 | Proposition 6.D.2 (i) ⇒ (ii) and in full, converse of Example 6.D.2, Exercise 6.D.4(c) both inclusions |
| [StateDependent](MWGChoiceUnderUncertainty/StateDependent.lean) | 16 | Section 6.E: Definitions 6.E.1-6.E.4, Example 6.E.1, Proposition 6.E.1, sure-thing axiom, Exercises 6.E.1-6.E.3 |
| [DebreuAdditive](MWGChoiceUnderUncertainty/DebreuAdditive.lean) | 15 | Proposition 6.E.2 corrected (three essential states, via Kreps 2.14) and its counterexample as printed (correction 16) |
| [SubjectiveProbability](MWGChoiceUnderUncertainty/SubjectiveProbability.lean) | 9 | Section 6.F: state uniformity, Proposition 6.F.1, Example 6.F.1, Exercises 6.F.1-6.F.2 |

## Build and verify

From this chapter directory:

```sh
lake build
python3 -m unittest discover -s scripts -p 'test_*.py' -v
python3 scripts/verify.py
```

The verifier builds the library, recompiles all sources in a fresh file, and audits every
declaration's axioms (only `propext`, `Classical.choice` and `Quot.sound` are allowed).
