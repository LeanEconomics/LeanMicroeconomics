# MWGClassicalDemand

Formalization of Mas-Colell, Whinston and Green, *Microeconomic Theory*, Chapter 3,
"Classical Demand Theory", pp. 40-104: preference properties and utility (3.B-3.C), the
utility maximization problem (3.D), the expenditure minimization problem (3.E), duality
(3.F), the relations between demand, indirect utility and expenditure functions with
Shephard's lemma, the Slutsky equation and Roy's identity (3.G), integrability (3.H),
welfare evaluation (3.I), the strong axiom (3.J), Appendix 3.A on continuity and
differentiability of Walrasian demand, the end-of-chapter exercises, and Mathematical
Appendix Sections M.C, M.E, M.F, M.G, M.H, M.J, M.K and M.L. The audit passed
**949 theorems and 1152 declarations across 78 modules**. Coverage is in the
[source map](docs/source-map.md); its first section lists the items still OPEN.
Departures from the printed text are in [corrections](docs/corrections.md).

The chapter was built in parts. Part A (3.A-3.D, M.C, M.F, M.J, M.K) laid the shared
definitions in `Basic`; part B added 3.E-3.G and M.E, M.G, M.L; part C added 3.J,
Appendix 3.A and M.H; part D added 3.H-3.I; parts E, F1, F2, F3 and G closed open items across the chapter, including
Frobenius integrability for every number of goods, Halkin's Lagrange theorem, the
transversality theorem M.E.2 and Debreu's representation theorem for any consumption set.
The source map and corrections keep these parts as sections.

This is a Lake project pinned to Lean and Mathlib `v4.34.0`. It imports (Lake `path`
requirements) MWG Chapters 1-2 (`MWGPreferenceChoice`: choice structures and the weak axiom;
`MWGConsumerChoice`: budgets, demand properties, the Slutsky matrix, Appendix M.A/M.B/M.D) and
Kreps Chapters 1-4 (`ChoicePreferenceUtility`, `PreferenceProperties`: Debreu's continuous
representation; `ConsumerDemand`: Berge's theorem, Cobb-Douglas and CES demand;
`RevealedPreference`: GARP), with bridge theorems, and LeanEconomics (Lake `git` requirement,
pinned to `04deccaf63`) for Brouwer's theorem in Halkin's proof. See
[third-party notices](THIRD_PARTY_NOTICES.md).

`Basic` is the shared foundation: preferences on a consumption set (`RationalOn`,
`PrefMonotone`, `PrefStronglyMonotone`, `LocallyNonsatiated`, `PrefConvex`,
`PrefStrictlyConvex`, `Homothetic`, `QuasilinearWrt`, `PrefContinuous`), `RepresentsOn`, the
Walrasian demand correspondence `walrasianDemand` and the indirect utility `indirectUtility`.

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Basic](MWGClassicalDemand/Basic.lean) | 18 | Definitions 3.B.1-3.B.7, 3.C.1; UMP, `x(p, w)`, `v(p, w)`; Euclidean distance |
| [PrefProperties](MWGClassicalDemand/PrefProperties.lean) | 16 | Section 3.B; Exercises 3.B.1-3.B.3; Figure 3.B.4 |
| [AppendixMC](MWGClassicalDemand/AppendixMC.lean) | 29 | Section M.C: Definitions M.C.1, M.C.3, Theorems M.C.1, M.C.3 |
| [AppendixMF](MWGClassicalDemand/AppendixMF.lean) | 9 | Section M.F: Definitions M.F.1-M.F.4, Theorems M.F.1(iii)-M.F.3 |
| [UtilityRepresentation](MWGClassicalDemand/UtilityRepresentation.lean) | 25 | Section 3.C: Example 3.C.1, Proposition 3.C.1; Exercises 3.C.1-3.C.4 |
| [UMPBasic](MWGClassicalDemand/UMPBasic.lean) | 34 | Propositions 3.D.1-3.D.3, Kuhn-Tucker conditions (3.D.1)-(3.D.5) |
| [UMPExamples](MWGClassicalDemand/UMPExamples.lean) | 14 | Examples 3.D.1-3.D.2; Exercises 3.D.1-3.D.2 |
| [UMPExercises](MWGClassicalDemand/UMPExercises.lean) | 12 | Exercises 3.D.3, 3.D.4(a)-(b), 3.D.8 |
| [UtilityExercises](MWGClassicalDemand/UtilityExercises.lean) | 7 | Exercises 3.C.5, 3.C.6(a) |
| [AppendixMJ](MWGClassicalDemand/AppendixMJ.lean) | 16 | Section M.J: Theorems M.J.1-M.J.3 |
| [AppendixMK](MWGClassicalDemand/AppendixMK.lean) | 11 | Section M.K: Theorems M.K.1-M.K.2 (Lagrange, Kuhn-Tucker) |
| [AppendixMKSufficiency](MWGClassicalDemand/AppendixMKSufficiency.lean) | 14 | Section M.K: (M.K.8), Theorems M.K.3-M.K.6 |
| [AppendixMCHessian](MWGClassicalDemand/AppendixMCHessian.lean) | 8 | Theorems M.C.2 and M.C.4 (with the counterexample to the printed converse) |
| [UtilityMore](MWGClassicalDemand/UtilityMore.lean) | 7 | Figure 3.C.3 (Leontief, no differentiable utility); Exercise 3.C.6(b)-(c) |
| [UMPMore](MWGClassicalDemand/UMPMore.lean) | 10 | KT sufficiency (p. 55); Exercises 3.D.3(b), 3.D.4(c) |
| [DualitySupport](MWGClassicalDemand/DualitySupport.lean) | 35 | Section 3.F: half-spaces, support function (Definition 3.F.1), duality theorem (Proposition 3.F.1, correction B1), Exercises 3.F.1-3.F.2 |
| [ExpBasic](MWGClassicalDemand/ExpBasic.lean) | 34 | Section 3.E: EMP, `h(p, ū)`, `e(p, ū)`; Propositions 3.E.1-3.E.4, (3.E.1), (3.E.4); Exercises 3.E.1, 3.E.3, 3.E.4 |
| [ExpContinuity](MWGClassicalDemand/ExpContinuity.lean) | 5 | Proposition 3.E.2(iv): joint continuity of `e` |
| [ExpExercises](MWGClassicalDemand/ExpExercises.lean) | 10 | Exercises 3.E.5, 3.E.7, 3.E.9, 3.E.10 |
| [ExpCobbDouglas](MWGClassicalDemand/ExpCobbDouglas.lean) | 10 | Example 3.E.1; Exercises 3.E.2, 3.E.8 |
| [RelationsBasic](MWGClassicalDemand/RelationsBasic.lean) | 23 | Section 3.G: Shephard's lemma (3.G.1), Proposition 3.G.2, Slutsky equation (3.G.3), Roy's identity (3.G.4, correction B4); Exercise 3.G.1 |
| [RelationsExercises](MWGClassicalDemand/RelationsExercises.lean) | 15 | Exercises 3.G.4(a)-(b), 3.G.6(a)-(b), 3.G.7, 3.G.8, 3.G.11, 3.G.13, 3.G.14, 3.G.17 |
| [AppendixML](MWGClassicalDemand/AppendixML.lean) | 4 | Section M.L: (M.L.3), Theorem M.L.1 |
| [AppendixME](MWGClassicalDemand/AppendixME.lean) | 6 | Section M.E: Definitions M.E.1-M.E.2, Theorem M.E.1, inverse function theorem |
| [AppendixMG](MWGClassicalDemand/AppendixMG.lean) | 20 | Section M.G: Definitions M.G.1-M.G.4, Theorems M.G.1 (partial), M.G.2, M.G.3 (corrections B5-B6) |
| [SARPBasic](MWGClassicalDemand/SARPBasic.lean) | 22 | Definition 3.J.1 (corrected), Proposition 3.J.1 and converse, abstract (Chapter 1) version, SA ⇒ WA, Example 2.F.1; bridges to Kreps SGARP/Prop. 1.23 and Kreps Ch. 4 GARP |
| [SARPTwoGoods](MWGClassicalDemand/SARPTwoGoods.lean) | 11 | Exercise 3.J.1 (Rose: WA ⟺ SA for `L = 2`), minimal revealed cycles; SA strictly stronger than WA for `L = 3` |
| [AppendixMH](MWGClassicalDemand/AppendixMH.lean) | 19 | Section M.H: Definitions M.H.1-M.H.4, Theorem M.H.1, footnotes 17-19, Figures M.H.1-M.H.3; bridges to Kreps and Mathlib hemicontinuity |
| [AppendixAContinuity](MWGClassicalDemand/AppendixAContinuity.lean) | 22 | Definition 3.AA.1, footnote 32, Proposition 3.AA.1, locally cheaper test, Figure 3.AA.3, Exercise 3.AA.1 |
| [AppendixABordered](MWGClassicalDemand/AppendixABordered.lean) | 11 | FOC Jacobian and bordered Hessian determinants, `-x⁴` and `x₂ - x₁⁴` remarks, footnote 33 (Leontief) |
| [AppendixADifferentiability](MWGClassicalDemand/AppendixADifferentiability.lean) | 13 | Implicit function step, differentiability ⟺ bordered Hessian determinant ≠ 0, rank `S = L - 1` |
| [IntegrabilityBasic](MWGClassicalDemand/IntegrabilityBasic.lean) | 17 | Section 3.H: `V_u`, Proposition 3.H.1 (differentiable and general), Euler's formula, the properties of `V_u` (p. 77), `V_u` generates `e` (p. 78) |
| [IntegrabilityUtility](MWGClassicalDemand/IntegrabilityUtility.lean) | 8 | Exercise 3.H.1 (EReal recovered utility; correction D1), the integrability theorem given a solution of (3.H.2) |
| [IntegrabilityPDE](MWGClassicalDemand/IntegrabilityPDE.lean) | 9 | Equation (3.H.2): Hessian = Slutsky matrix, symmetry necessary, concavity/HD1/monotonicity of solutions, integrability from (3.H.2) |
| [IntegrabilityTwoGoods](MWGClassicalDemand/IntegrabilityTwoGoods.lean) | 6 | Equation (3.H.1), footnote 18: local existence, monotonicity, concavity; lift to (3.H.2); `L = 2` integrability given global solutions |
| [IntegrabilityUnique](MWGClassicalDemand/IntegrabilityUnique.lean) | 4 | Uniqueness of solutions of (3.H.2) for `C¹` demand; the expenditure function solves (3.H.2) and is recovered uniquely |
| [IntegrabilityCobbDouglas](MWGClassicalDemand/IntegrabilityCobbDouglas.lean) | 9 | Exercise 3.H.6: Cobb-Douglas expenditure function, AM-GM, rationalization, recovered utility |
| [WelfareBasic](MWGClassicalDemand/WelfareBasic.lean) | 22 | Section 3.I: money metric (footnote 21), EV and CV (3.I.1)-(3.I.2), footnotes 22 and 24, rankings, Propositions 3.I.1-3.I.2 (correction D3), (3.I.7); Exercises 3.I.6, 3.I.11, 3.I.12 |
| [IntegrabilityExercises](MWGClassicalDemand/IntegrabilityExercises.lean) | 9 | Exercises 3.H.2 (partial), 3.H.3, 3.H.4, 3.H.5, 3.H.7; closed convex hull (p. 78, correction D2); no solution of (3.H.2) for the demand of Exercise 2.F.15 |
| [WelfareIntegrals](MWGClassicalDemand/WelfareIntegrals.lean) | 15 | (3.I.3)-(3.I.6), (3.I.8), normal/inferior comparisons, Marshallian surplus, Example 3.I.1, Exercises 3.I.1-3.I.2 (corrections D4-D6) |
| [WelfareExercises](MWGClassicalDemand/WelfareExercises.lean) | 11 | Exercises 3.I.3 (correction D5), 3.I.4, 3.I.5, 3.I.10 |
| [WelfareLinearDemand](MWGClassicalDemand/WelfareLinearDemand.lean) | 15 | Exercises 3.I.7(a)-(e), 3.I.8(a)-(d) (correction D7) |
| [WelfareTax](MWGClassicalDemand/WelfareTax.lean) | 3 | Exercise 3.I.9 (weak and strict) |
| [WelfareApprox](MWGClassicalDemand/WelfareApprox.lean) | 5 | Figure 3.I.5 budget line, equal-revenue taxes (p. 86), footnote 28 (EV, AV), (3.I.9) |
| [CloserAppendixMG](MWGClassicalDemand/CloserAppendixMG.lean) | 8 | Theorem M.G.1 exactly: Minkowski's theorem `B = Co(ext B)`, at most `N + 1` extreme points |
| [CloserCES](MWGClassicalDemand/CloserCES.lean) | 43 | Exercises 3.D.5(a)-(d) and 3.E.6: CES demand, indirect utility, linear/Leontief limits, elasticity of substitution, Hicksian demand and expenditure |
| [CloserLES](MWGClassicalDemand/CloserLES.lean) | 17 | Exercises 3.D.6(a)-(c) and 3.G.3(a): the linear expenditure system |
| [CloserLESSlutsky](MWGClassicalDemand/CloserLESSlutsky.lean) | 15 | Exercise 3.G.3(b)-(e): Shephard's lemma, Slutsky equation, symmetry, negative semidefiniteness and rank of `S` |
| [CloserRelations](MWGClassicalDemand/CloserRelations.lean) | 14 | Exercises 3.G.6(c)(e), 3.G.9, 3.G.10, 3.G.12, 3.G.18 |
| [CloserSeparable](MWGClassicalDemand/CloserSeparable.lean) | 5 | Exercise 3.G.4(a) "only linear", (c) no inferior goods, (d) gross substitutes |
| [CloserAppendixMK](MWGClassicalDemand/CloserAppendixMK.lean) | 9 | Theorem M.K.5 with inequality constraints; second-order sufficient conditions (p. 958); the example on p. 964 |
| [CloserSqrtUtility](MWGClassicalDemand/CloserSqrtUtility.lean) | 11 | Exercise 3.G.15(a)-(d): `u = 2x₁^{1/2} + 4x₂^{1/2}` |
| [CloserQuasilinear](MWGClassicalDemand/CloserQuasilinear.lean) | 5 | Exercise 3.C.5(b) "only if": quasilinear representations |
| [CloserDuality](MWGClassicalDemand/CloserDuality.lean) | 4 | Small type pp. 66-67: one-sided derivatives of the support function (Danskin) |
| [CloserDemandContinuity](MWGClassicalDemand/CloserDemandContinuity.lean) | 5 | Exercise 3.AA.2: `h` upper hemicontinuous, `e` continuous (also on `ℝ^L_+` with the infimum), differentiability of `h` |
| [CloserGivenExpenditure](MWGClassicalDemand/CloserGivenExpenditure.lean) | 8 | Exercise 3.G.16(a)-(b) and Roy's identity in (c) |
| [CloserComposite](MWGClassicalDemand/CloserComposite.lean) | 1 | Exercise 3.G.5(a): Hicksian composite commodities |
| [CloserCobbDouglas](MWGClassicalDemand/CloserCobbDouglas.lean) | 4 | Exercise 3.G.2: Cobb-Douglas satisfies Propositions 3.G.1-3.G.4; Roy's identity for the LES |
| [HardIntegrability](MWGClassicalDemand/HardIntegrability.lean) | 15 | Footnote 18: global solution of (3.H.1) for L = 2; integrability for two goods from primitive hypotheses |
| [HardHalkin](MWGClassicalDemand/HardHalkin.lean) | 6 | Theorems M.K.1-M.K.2 for merely differentiable functions (Halkin, via Brouwer) |
| [HardSecondOrder](MWGClassicalDemand/HardSecondOrder.lean) | 3 | Second-order necessary conditions, p. 958 |
| [HardEnvelope](MWGClassicalDemand/HardEnvelope.lean) | 3 | Theorem M.L.1 with only v differentiable; the constraint qualification is needed |
| [HardSard](MWGClassicalDemand/HardSard.lean) | 6 | Theorem M.E.2, the transversality theorem |
| [FrobeniusDependence](MWGClassicalDemand/FrobeniusDependence.lean) | 2 | Uniform first-order Taylor remainder on compact convex sets; differentiable dependence of an ODE solution on a parameter, given a solution of the variational equation (two Gronwall estimates) |
| [FrobeniusTheorem](MWGClassicalDemand/FrobeniusTheorem.lean) | 8 | Frobenius' theorem (sufficiency) for `∂Z/∂q = f(q, Z)` on `ℝ^L × ℝ` by integration along rays: global existence, uniqueness, differentiability via the variational equation and the integrability condition; family strictly increasing, onto and continuous in the initial value |
| [FrobeniusIntegrability](MWGClassicalDemand/FrobeniusIntegrability.lean) | 12 | (3.H.2) in logarithmic coordinates; symmetry of `S` as the integrability condition; existence of solutions of (3.H.2) for any `L` (`frob_3_H_2_exists`, `frob_expenditure_family`); the integrability theorem from primitive hypotheses (`integrability_general`) |
| [FrobeniusOnePrice](MWGClassicalDemand/FrobeniusOnePrice.lean) | 15 | Small type p. 80: the one-price subproblems (global existence without symmetry, uniqueness) and the one-price-at-a-time construction ends at `E(p̄)` (`frob_one_price_at_a_time`, `frob_one_price_at_a_time_exists`) |
| [EconDebreu](MWGClassicalDemand/EconDebreu.lean) | 11 | Proposition 3.C.1 for every `X ⊆ ℝ^L`; Debreu's theorem on second-countable spaces; open-gap lemma |
| [EconIntegrability](MWGClassicalDemand/EconIntegrability.lean) | 7 | Exercise 3.H.2 and p. 78: differentiable `e` ⇒ `K = V_ū` convex, generating preferences convex |
| [EconGivenExpenditure](MWGClassicalDemand/EconGivenExpenditure.lean) | 5 | Exercise 3.G.16(c): Hicksian and Walrasian demands, Slutsky equation |
| [EconBoundary](MWGClassicalDemand/EconBoundary.lean) | 4 | Exercise 3.AA.2: `e` not jointly continuous at boundary prices (counterexample) |
| [EconWelfare](MWGClassicalDemand/EconWelfare.lean) | 7 | Footnote 28 (CV); relative errors of AV and EV (p. 89); (3.I.9) second-order accuracy; Peano second-order Taylor lemma |
| [EconRevealed](MWGClassicalDemand/EconRevealed.lean) | 10 | Exercise 3.D.7(a)-(e): regions of permissible choices and rationalizing utilities |
| [LastRevealed](MWGClassicalDemand/LastRevealed.lean) | 12 | Exercise 3.D.7(d): iff `t ≤ 11/2`; normal demand function for `x₂ + min(x₁, 3 + x₁/4, 3 + x¹₁/4)` on `ℝ²_+`; the earlier hypothesis is unsatisfiable |
| [LastWelfare](MWGClassicalDemand/LastWelfare.lean) | 23 | Figure 3.I.8: Cobb-Douglas closed forms of (3.I.5), (3.I.6) and the AV deadweight loss, second-order expansions, relative error `→ α/(1-α)`; footnote 29 computation (`-α/(α+1)`, mixed measure) |
| [LastQuasilinear](MWGClassicalDemand/LastQuasilinear.lean) | 5 | Exercise 3.I.8(a) "only if": `x_k + inf_p(p·x - x_k - E(p))` represents `u` on demanded bundles; constancy lemma; consistent instance |
| [LastComposite](MWGClassicalDemand/LastComposite.lean) | 14 | Bridge `(x, z) ↦ Fin.snoc x z`; `ũ` attained, budget exhausted, continuous (Berge), locally nonsatiated, strictly quasiconcave |
| [LastCompositeApps](MWGClassicalDemand/LastCompositeApps.lean) | 9 | Exercise 3.G.5(b)-(c): Propositions 3.D.2, 3.G.4, 3.E.3, 3.G.1-3.G.3 for the composite problem; consistent instance |

From this directory, run:

```sh
export PATH="$HOME/.elan/bin:$PATH"
lake build
python3 -m unittest discover -s scripts -p 'test_*.py' -v
python3 scripts/verify.py
```

The verifier builds the project, freshly recompiles the contributed modules and audits every
named declaration; only `propext`, `Classical.choice` and `Quot.sound` occur.
