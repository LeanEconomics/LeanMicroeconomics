# MWGMechanismDesign

Formalization of Mas-Colell, Whinston and Green, *Microeconomic Theory*, Chapter 23,
"Incentives and Mechanism Design", pp. 857-925: Sections 23.A-23.F, Appendix A (strong
implementation), Appendix B (implementation with complete information), footnotes 1-62 and
Exercises 23.B.1-23.BB.3, every subpart. The fresh-source audit passes **649 theorems and 971
audited declarations across 36 modules**. Highlights: the revelation
principles for dominant strategies and Bayesian Nash equilibrium (Propositions 23.C.1,
23.D.1); the Gibbard-Satterthwaite theorem (Proposition 23.C.3) by the book's three steps,
reduced to Proposition 21.E.1, with Corollaries 23.C.1-23.C.2; Groves, Clarke and the
Green-Laffont theorems (Propositions 23.C.4-23.C.6), the latter with its omitted proof, and the
differentiable case through Mathlib's implicit function theorem; the expected externality
mechanism; Proposition 23.D.2 without differentiability of `U`; revenue equivalence
(Proposition 23.D.3) without densities; the Myerson-Satterthwaite theorem (Proposition 23.E.1)
both by MWG's own two-step proof, every display checked, and by a second route for general type
distributions, with one non-vacuity instance per hypothesis; Myerson's optimal auction
(Example 23.F.2), completed for general densities by envelope transfers (the sufficiency half of
Proposition 23.D.2), as is the Dana-Spier auction of production rights (Exercise 23.F.7); the
hidden-information principal-agent problem (Example 23.F.1) with the interiority of footnote 48
and the complete interim and ex ante incentive efficient sets of Example 23.F.3; Maskin's theorems
(Propositions 23.BB.1-23.BB.3), the last with Maskin's integer mechanism and full
implementation of correspondences; and the Moore-Repullo example and the manipulable Walrasian
social choice function of Example 23.B.2 made concrete. The
[source map](docs/source-map.md) records exact coverage; one item is OPEN, the Barberà-Peleg
theorem cited in footnote 19.
[Corrections](docs/corrections.md) lists 30 departures, including false printed claims refuted
by counterexample theorems: the converses of Corollaries 23.C.1-23.C.2 with indifference, the
Clarke "negative tax", Proposition 23.C.6 with one agent or one project, `Uᵢ' = v̄ᵢ` in the proof
of Proposition 23.D.2, Proposition 23.F.1 with null types, Exercises 23.E.2 and 23.F.6(b) as
printed, Definitions 23.AA.1 and 23.BB.1 without existence, the strict-dominance claim of
Appendix A, the second equilibrium of Example 23.AA.1, the monotonicity of the Pareto
correspondence and nondictatoriality of majority voting with two agents. Generated proof checks and source hashes are in
[verification](verification/verification.json).

This is an independent Lake project pinned to Lean and Mathlib `v4.34.0`. It depends, through
Lake `path` requirements, on MWG Chapter 22
([`MWGWelfareBargaining`](../22_WelfareBargaining/README.md)), which brings MWG Chapter 21
([`MWGSocialChoice`](../21_SocialChoice/README.md)) and through it MWG Chapter 1 and Kreps
Chapter 1. The modules import `MWGSocialChoice` directly: profiles, `𝓟` (`StrictPrefs`),
`topProfile` and Proposition 21.E.1 are used in the Gibbard-Satterthwaite proof, and the
single-peaked and median voter results (Proposition 21.D.1) in Exercise 23.C.5; Kreps's
`Rational` is the rationality of induced preferences. No module imports `MWGWelfareBargaining`
itself; it is required only for the path to Chapter 21. All declarations are in
`MWG.MechanismDesign`.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Mechanisms](MWGMechanismDesign/Mechanisms.lean) | 9 | Definitions 23.B.1-23.B.6, 23.C.1-23.C.3, Propositions 23.C.1-23.C.2, Exercise 23.C.1 |
| [Bayesian](MWGMechanismDesign/Bayesian.lean) | 8 | (23.C.1)-(23.C.2), footnote 16, Definitions 23.D.1-23.D.3, Proposition 23.D.1, dominant strategy implies Bayesian |
| [GibbardSatterthwaite](MWGMechanismDesign/GibbardSatterthwaite.lean) | 17 | Definitions 23.C.4-23.C.5, Proposition 23.C.3 Steps 1-3, footnote 19 |
| [RankUtility](MWGMechanismDesign/RankUtility.lean) | 8 | Rank utilities, non-vacuity of Proposition 23.C.3, Exercises 23.C.3-23.C.4 |
| [GSCorollaries](MWGMechanismDesign/GSCorollaries.lean) | 8 | Corollaries 23.C.1-23.C.2, Definition 23.C.6, false converses |
| [Quasilinear](MWGMechanismDesign/Quasilinear.lean) | 12 | (23.C.7), Proposition 23.C.4 (Groves), Clarke mechanism, footnotes 20 and 23, Proposition 23.C.5, outside agent, Exercise 23.C.11 |
| [BudgetBalance](MWGMechanismDesign/BudgetBalance.lean) | 11 | (23.C.12), Proposition 23.C.6 and its corrections, Exercise 23.C.10(a)-(b) |
| [Independent](MWGMechanismDesign/Independent.lean) | 4 | Independent types, iterated expectations |
| [ExpectedExternality](MWGMechanismDesign/ExpectedExternality.lean) | 5 | (23.D.8)-(23.D.9), the expected externality mechanism |
| [MultipleEquilibria](MWGMechanismDesign/MultipleEquilibria.lean) | 10 | Example 23.AA.1 with its correction |
| [LinearBIC](MWGMechanismDesign/LinearBIC.lean) | 7 | (23.D.10), Proposition 23.D.2, expected transfer formula |
| [NashImplementation](MWGMechanismDesign/NashImplementation.lean) | 57 | Appendix B: Definition 23.BB.1, Propositions 23.BB.1-23.BB.3, Maskin's mechanism, correspondences, Pareto correspondence, Exercises 23.BB.2-23.BB.3 |
| [SubgamePerfect](MWGMechanismDesign/SubgamePerfect.lean) | 10 | Example 23.BB.1 (Moore-Repullo), Exercise 23.BB.1 |
| [TypeDensity](MWGMechanismDesign/TypeDensity.lean) | 17 | Type distributions with densities, the Fubini form of the integration by parts, uniform distributions |
| [RevenueEquivalence](MWGMechanismDesign/RevenueEquivalence.lean) | 38 | Proposition 23.D.3, (23.D.14)-(23.D.16), Exercises 23.D.2-23.D.3 |
| [MyersonSatterthwaite](MWGMechanismDesign/MyersonSatterthwaite.lean) | 38 | Proposition 23.E.1 (general and with densities), footnote 41, non-vacuity, Exercises 23.E.1-23.E.3, 23.E.7 |
| [BilateralAdverseSelection](MWGMechanismDesign/BilateralAdverseSelection.lean) | 30 | Example 23.F.3, Figures 23.F.1-23.F.3, footnote 54, Exercises 23.F.8-23.F.10 |
| [Participation](MWGMechanismDesign/Participation.lean) | 13 | Example 23.E.1, (23.E.1)-(23.E.3) and their implications |
| [WelfareCriteria](MWGMechanismDesign/WelfareCriteria.lean) | 11 | (23.F.1)-(23.F.2), Definitions 23.F.1-23.F.3, Proposition 23.F.1 (false; corrected), Exercise 23.F.1 |
| [OptimalAuction](MWGMechanismDesign/OptimalAuction.lean) | 18 | Example 23.F.2, (23.F.7)-(23.F.9), remarks (1)-(3), Exercises 23.F.3-23.F.4 |
| [OptimalContract](MWGMechanismDesign/OptimalContract.lean) | 21 | Example 23.F.1, (23.F.3)-(23.F.6) |
| [Examples23B](MWGMechanismDesign/Examples23B.lean) | 16 | Examples 23.B.1, 23.B.3, 23.B.4 (efficiency), Exercise 23.B.1 |
| [Auctions23B](MWGMechanismDesign/Auctions23B.lean) | 43 | Examples 23.B.4-23.B.7 (auctions), auction outcome functions, Exercises 23.B.2-23.B.4 |
| [DSExercises](MWGMechanismDesign/DSExercises.lean) | 20 | Exercises 23.C.2, 23.C.5-23.C.8 |
| [StrongImplementation](MWGMechanismDesign/StrongImplementation.lean) | 21 | Appendix A: Definition 23.AA.1, strict dominance, Exercises 23.AA.1-23.AA.2 |
| [DifferentiableCase](MWGMechanismDesign/DifferentiableCase.lean) | 42 | (23.C.13)-(23.C.15), implicit function theorem, Groves form, footnote 26, `I = 2` impossibility, Exercises 23.C.9, 23.C.10(c)-(d) |
| [TradeExercises](MWGMechanismDesign/TradeExercises.lean) | 22 | Exercises 23.D.1, 23.D.4-23.D.6, 23.E.4-23.E.6 |
| [RegulationExercises](MWGMechanismDesign/RegulationExercises.lean) | 19 | Exercises 23.F.2, 23.F.5, 23.F.6, 23.F.7 (Cournot outcomes, virtual welfare) |
| [MyersonSatterthwaiteSteps](MWGMechanismDesign/MyersonSatterthwaiteSteps.lean) | 51 | MWG's proof of Proposition 23.E.1, (23.E.4)-(23.E.7) and every display of Step 2; Exercise 23.E.6(b) uniqueness |
| [DanaSpier](MWGMechanismDesign/DanaSpier.lean) | 11 | Exercise 23.F.7: reduction to virtual welfare, optimality, instance |
| [EnvelopeCompletion](MWGMechanismDesign/EnvelopeCompletion.lean) | 20 | Proposition 23.D.2 sufficiency by envelope transfers; Example 23.F.2 and Exercise 23.F.7 completed for general densities |
| [ContractInteriority](MWGMechanismDesign/ContractInteriority.lean) | 5 | Footnote 48 (interiority); Exercise 23.F.1's claim about Example 23.F.1 (first best incentive feasible) |
| [WelfareGeneral](MWGMechanismDesign/WelfareGeneral.lean) | 3 | Exercise 23.F.1, ex ante part for general type spaces |
| [ClearingPrice](MWGMechanismDesign/ClearingPrice.lean) | 7 | Exercise 23.E.5: existence of a market-clearing price, competitive mechanism |
| [MajorityTwo](MWGMechanismDesign/MajorityTwo.lean) | 7 | p. 875: majority voting with two alternatives is nondictatorial and strategy-proof; two-agent counterexample |
| [WalrasManipulation](MWGMechanismDesign/WalrasManipulation.lean) | 10 | Example 23.B.2, Figure 23.B.1: concrete manipulable Walrasian social choice function, first welfare theorem |

## Build and verify

```sh
export PATH="$HOME/.elan/bin:$PATH"
lake build MWGMechanismDesign
python3 -m unittest discover -s scripts -p 'test_*.py' -v
python3 scripts/verify.py
```
