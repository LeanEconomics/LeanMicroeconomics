# MWGPositiveEquilibriumTheory

Formalization of Mas-Colell, Whinston and Green, *Microeconomic Theory*, Chapter 17, "The
Positive Theory of Equilibrium", pp. 578-651, with Appendix A (characterizing equilibrium
through welfare equations), Appendix B (a general approach to existence) and every
end-of-chapter exercise: excess demand and its properties (17.B, Proposition 17.B.2 derived
from preferences), existence by Kakutani and Brouwer (17.C), regular economies, local
uniqueness, the index theorem for two goods and generic regularity through the transversality
theorem (17.D), the Sonnenschein-Mantel-Debreu theorem for every number of goods (17.E),
uniqueness under the weak axiom and gross substitutes (17.F), comparative statics (17.G),
tatonnement stability with existence of trajectories, Scarf's unstable economy and the
quantity adjustment process (17.H), large economies, the Shapley-Folkman theorem and
convexified existence (17.I), the Negishi approach (Appendix A) and existence of a
quasiequilibrium in a general production economy by Kakutani (Proposition 17.BB.2). The audit
passed **983 theorems and 1344 declarations across 78 modules**. Coverage is in the
[source map](docs/source-map.md), which lists the OPEN items (chiefly the index theorem for
`L ≥ 3`, which needs Brouwer degree theory, the transversality theorem with fewer equations than
unknowns, Proposition 17.E.4, strict convexity in the SMD construction, and four existence
exercises). Departures from the printed text, including refutations of Exercise 17.D.1,
Proposition 17.H.2, the general case of Exercise 17.F.6, Exercise 17.F.14(b), and the
eigenvalue characterization of local stability, are in [corrections](docs/corrections.md).

This is a Lake project pinned to Lean and Mathlib `v4.34.0`. It imports (Lake `path`
requirement) MWG Chapter 16 (`MWGWelfareTheorems`: `PrivPrefEconomy`, Walrasian equilibrium,
the second welfare theorem) and, through it, Chapter 15 (`MWGGeneralEquilibriumExamples`:
`ExchangeEconomy`, Examples 15.B.2 and Figures 15.B.10), Chapter 10, Chapter 5 (`supply`),
Chapter 3 (`MWGClassicalDemand`: preferences, Walrasian demand, Proposition 3.AA.1, the
implicit function theorem M.E.1 and the transversality theorem M.E.2), Chapter 2 (the weak
axiom, the Slutsky matrix), the Kreps chapters (Cobb-Douglas and CES demand) and LeanEconomics
(pinned `04deccaf63`: Brouwer's and Kakutani's theorems). See
[third-party notices](THIRD_PARTY_NOTICES.md).

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Basic](MWGPositiveEquilibriumTheory/Basic.lean) | 9 | Shared definitions: price domains, properties (i)-(v) of Proposition 17.B.2, Definition 17.B.2, (17.B.2), `ẑ` |
| [ExcessDemand](MWGPositiveEquilibriumTheory/ExcessDemand.lean) | 11 | Proposition 17.B.1, conditions (i')-(iii'), Exercise 17.B.1, (17.B.1'), pure exchange as a Chapter 16 economy |
| [DemandContinuity](MWGPositiveEquilibriumTheory/DemandContinuity.lean) | 11 | Continuity of demand up to `w = 0`; the boundary lemma behind Exercise 17.B.2 |
| [StandardProperties](MWGPositiveEquilibriumTheory/StandardProperties.lean) | 21 | Proposition 17.B.2 from primitives, Exercise 17.B.2, footnote 3, the `√` instance |
| [Existence](MWGPositiveEquilibriumTheory/Existence.lean) | 29 | `L = 2` existence (Figure 17.C.1, footnote 8), Proposition 17.C.1 by Kakutani, footnotes 9-10, Exercise 17.C.1 |
| [ExistenceBrouwer](MWGPositiveEquilibriumTheory/ExistenceBrouwer.lean) | 11 | Proposition 17.C.2 by Brouwer, Figures 15.B.10(a)-(b), second welfare theorem via existence |
| [Production](MWGPositiveEquilibriumTheory/Production.lean) | 17 | (17.B.3), Exercise 17.B.4 (correction 2), footnote 4, existence with production |
| [LinearActivities](MWGPositiveEquilibriumTheory/LinearActivities.lean) | 12 | (17.B.4)-(17.B.5), Exercises 17.B.5-17.B.6 |
| [Exercise17B3](MWGPositiveEquilibriumTheory/Exercise17B3.lean) | 5 | Exercise 17.B.3(a)-(b) |
| [Exercise17C2](MWGPositiveEquilibriumTheory/Exercise17C2.lean) | 7 | Exercise 17.C.2: existence for convex-valued uhc excess demand correspondences |
| [Exercises17C](MWGPositiveEquilibriumTheory/Exercises17C.lean) | 9 | Exercises 17.C.3(a),(c),(d), 17.C.4, 17.C.5 |
| [Exercise17C6](MWGPositiveEquilibriumTheory/Exercise17C6.lean) | 8 | Exercise 17.C.6 |
| [Regularity](MWGPositiveEquilibriumTheory/Regularity.lean) | 25 | Definitions 17.D.1-17.D.2, Proposition 17.D.1, footnotes 14-15 |
| [CobbDouglasEconomy](MWGPositiveEquilibriumTheory/CobbDouglasEconomy.lean) | 18 | Cobb-Douglas economies: (i)-(v), `C¹`, Exercise 17.D.8 (index +1 for every `L`) |
| [IndexTwoGoods](MWGPositiveEquilibriumTheory/IndexTwoGoods.lean) | 22 | Proposition 17.D.2 for `L = 2`, odd number of equilibria |
| [Exercise17D1](MWGPositiveEquilibriumTheory/Exercise17D1.lean) | 10 | Exercise 17.D.1 (false as printed; corrected) |
| [Exercises17D](MWGPositiveEquilibriumTheory/Exercises17D.lean) | 6 | Figures 17.D.2-17.D.3, Exercise 17.D.7 |
| [GenericRegularity](MWGPositiveEquilibriumTheory/GenericRegularity.lean) | 16 | Definition 17.D.3, Propositions 17.D.3-17.D.5, Exercises 17.D.2-17.D.3 |
| [Exercises17DRank](MWGPositiveEquilibriumTheory/Exercises17DRank.lean) | 18 | Exercises 17.D.5-17.D.6 |
| [Exercise17D4](MWGPositiveEquilibriumTheory/Exercise17D4.lean) | 9 | Exercise 17.D.4 |
| [PriceEffects](MWGPositiveEquilibriumTheory/PriceEffects.lean) | 15 | (17.E.1)-(17.E.3), Proposition 17.E.1, footnote 27 |
| [PriceEffectsEconomy](MWGPositiveEquilibriumTheory/PriceEffectsEconomy.lean) | 7 | Proposition 17.E.2, Exercise 17.E.3, footnote 24 |
| [SMDRationalization](MWGPositiveEquilibriumTheory/SMDRationalization.lean) | 30 | Rationalizing offer points by continuous convex strongly monotone utilities |
| [SMDTwoGoods](MWGPositiveEquilibriumTheory/SMDTwoGoods.lean) | 11 | `P_ε`, Proposition 17.E.3 for `L = 2` (the book's decomposition) |
| [SMDDebreuBasic](MWGPositiveEquilibriumTheory/SMDDebreuBasic.lean) | 11 | (17.E.4)-(17.E.4'), strong axiom, Debreu's decomposition, Exercises 17.E.6-17.E.7 |
| [SMDDebreu](MWGPositiveEquilibriumTheory/SMDDebreu.lean) | 14 | Debreu's consumers |
| [SMDTheorem](MWGPositiveEquilibriumTheory/SMDTheorem.lean) | 2 | Proposition 17.E.3 (Sonnenschein-Mantel-Debreu) for every `L`, footnote 30 |
| [Exercises17E](MWGPositiveEquilibriumTheory/Exercises17E.lean) | 5 | Exercises 17.E.4-17.E.5, footnote 31 |
| [WeakAxiomED](MWGPositiveEquilibriumTheory/WeakAxiomED.lean) | 19 | Proposition 17.F.1, Definition 17.F.1, Proposition 17.F.2, footnotes 36, 39 |
| [WeakAxiomDifferential](MWGPositiveEquilibriumTheory/WeakAxiomDifferential.lean) | 16 | (17.F.1)-(17.F.2), footnote 42, Exercise 17.F.1 |
| [GrossSubstitutes](MWGPositiveEquilibriumTheory/GrossSubstitutes.lean) | 28 | Definition 17.F.2, Propositions 17.F.3-17.F.4, (17.F.3) for every `L`, Exercises 17.F.7, 17.F.8, 17.F.10 |
| [GrossSubstitutesExamples](MWGPositiveEquilibriumTheory/GrossSubstitutesExamples.lean) | 25 | Examples 17.F.1-17.F.2, footnotes 45, 48, Exercises 17.F.2-17.F.4 |
| [UniquenessPareto](MWGPositiveEquilibriumTheory/UniquenessPareto.lean) | 10 | Proposition 17.F.5, Example 17.F.3 (index argument), Exercise 17.F.9 |
| [Exercise17F5](MWGPositiveEquilibriumTheory/Exercise17F5.lean) | 11 | Exercise 17.F.5 (separable and CES utilities) |
| [UniquenessInstances](MWGPositiveEquilibriumTheory/UniquenessInstances.lean) | 8 | Instances for the (17.F.1) hypotheses |
| [IndexSemidefinite](MWGPositiveEquilibriumTheory/IndexSemidefinite.lean) | 17 | Exercises 17.F.11-17.F.12, dominant diagonals, footnote 51 |
| [TwoCountries](MWGPositiveEquilibriumTheory/TwoCountries.lean) | 10 | Example 17.F.3 and Exercise 17.F.13 |
| [Figure17D1](MWGPositiveEquilibriumTheory/Figure17D1.lean) | 6 | Figure 17.D.1: the three equilibria of Example 15.B.2 are regular |
| [ComparativeStatics](MWGPositiveEquilibriumTheory/ComparativeStatics.lean) | 14 | (17.G.1), Propositions 17.G.2-17.G.3, footnote 53 |
| [ComparativeStaticsEconomy](MWGPositiveEquilibriumTheory/ComparativeStaticsEconomy.lean) | 21 | Proposition 17.G.1 |
| [Exercises17G](MWGPositiveEquilibriumTheory/Exercises17G.lean) | 7 | Exercises 17.G.1-17.G.2 |
| [StrongGrossSubstitutes](MWGPositiveEquilibriumTheory/StrongGrossSubstitutes.lean) | 17 | Exercise 17.F.16, Exercise 17.G.3 |
| [StrongGrossSubstitutesSmooth](MWGPositiveEquilibriumTheory/StrongGrossSubstitutesSmooth.lean) | 8 | Exercise 17.F.16(b) |
| [Exercises17FMore](MWGPositiveEquilibriumTheory/Exercises17FMore.lean) | 6 | Exercises 17.F.15, 17.F.17 |
| [Complements](MWGPositiveEquilibriumTheory/Complements.lean) | 13 | Exercise 17.F.14 (correction for (b)) |
| [Exercise17F6](MWGPositiveEquilibriumTheory/Exercise17F6.lean) | 8 | Exercise 17.F.6, homothetic case |
| [Tatonnement](MWGPositiveEquilibriumTheory/Tatonnement.lean) | 28 | Tatonnement dynamics, Proposition 17.H.1, global stability under GS and the weak axiom |
| [TatonnementExistence](MWGPositiveEquilibriumTheory/TatonnementExistence.lean) | 10 | Existence of tatonnement trajectories (Picard-Lindelöf), Cobb-Douglas instance |
| [TatonnementTwoGoods](MWGPositiveEquilibriumTheory/TatonnementTwoGoods.lean) | 17 | `L = 2`: footnote 60, property (a), footnote 62 |
| [TatonnementLocal](MWGPositiveEquilibriumTheory/TatonnementLocal.lean) | 15 | Local stability, eigenvalue claim counterexample, footnote 66 |
| [QuantityAdjustment](MWGPositiveEquilibriumTheory/QuantityAdjustment.lean) | 15 | Definition 17.H.1, Proposition 17.H.2 (false as printed; corrected) |
| [Exercise17H1](MWGPositiveEquilibriumTheory/Exercise17H1.lean) | 5 | Exercise 17.H.1 |
| [Exercises17H](MWGPositiveEquilibriumTheory/Exercises17H.lean) | 12 | Figure 17.H.2, Exercises 17.H.2-17.H.3 |
| [TatonnementNewton](MWGPositiveEquilibriumTheory/TatonnementNewton.lean) | 3 | Newton dynamics (17.H.2) |
| [ShapleyFolkman](MWGPositiveEquilibriumTheory/ShapleyFolkman.lean) | 8 | The Shapley-Folkman theorem |
| [LargeEconomies](MWGPositiveEquilibriumTheory/LargeEconomies.lean) | 28 | Replica economies, Figure 17.I.1, convexification, near equilibria, footnotes 71, 73-74 |
| [Exercises17I](MWGPositiveEquilibriumTheory/Exercises17I.lean) | 11 | Exercises 17.I.1-17.I.2 |
| [Exercise17I3](MWGPositiveEquilibriumTheory/Exercise17I3.lean) | 3 | Exercise 17.I.3 |
| [NegishiApproach](MWGPositiveEquilibriumTheory/NegishiApproach.lean) | 12 | Appendix A: welfare equations, (17.AA.1), Exercise 17.AA.1 |
| [Exercises17AA](MWGPositiveEquilibriumTheory/Exercises17AA.lean) | 15 | Exercise 17.AA.2(a)-(d) |
| [NegishiLogEconomy](MWGPositiveEquilibriumTheory/NegishiLogEconomy.lean) | 14 | Instance for Exercise 17.AA.2 |
| [Exercise17AA3](MWGPositiveEquilibriumTheory/Exercise17AA3.lean) | 2 | Exercise 17.AA.3 |
| [QuasiEquilibrium](MWGPositiveEquilibriumTheory/QuasiEquilibrium.lean) | 17 | Definitions 17.BB.1-17.BB.3, Proposition 17.BB.1, Exercises 17.BB.4-17.BB.5, footnote 80 |
| [AbstractEconomy](MWGPositiveEquilibriumTheory/AbstractEconomy.lean) | 15 | Truncation, Lemmas 17.BB.1-17.BB.2, the abstract game |
| [ExistenceGeneralLemmas](MWGPositiveEquilibriumTheory/ExistenceGeneralLemmas.lean) | 17 | Lemmas 17.BB.3-17.BB.6, Exercises 17.BB.6-17.BB.7 |
| [ExistenceGeneral](MWGPositiveEquilibriumTheory/ExistenceGeneral.lean) | 8 | Proposition 17.BB.2, footnotes 81-82, an instance with production |
| [Exercises17BB](MWGPositiveEquilibriumTheory/Exercises17BB.lean) | 9 | Exercises 17.BB.1-17.BB.3 |
| [Exercise17BB3](MWGPositiveEquilibriumTheory/Exercise17BB3.lean) | 3 | Exercise 17.BB.3: some price positive |
| [Exercise17BB8](MWGPositiveEquilibriumTheory/Exercise17BB8.lean) | 8 | Exercise 17.BB.8(a), (c)-(e) |
| [Exercise17BB9](MWGPositiveEquilibriumTheory/Exercise17BB9.lean) | 6 | Exercise 17.BB.9: the two-player game |
| [Closer17I](MWGPositiveEquilibriumTheory/Closer17I.lean) | 26 | Footnote 71: neither `E(2) ⊆ E(3)` nor `E(3) ⊆ E(2)` |
| [Closer17H](MWGPositiveEquilibriumTheory/Closer17H.lean) | 17 | Footnote 62 for `L = 3`: Scarf's economy is not globally stable |
| [Closer17E](MWGPositiveEquilibriumTheory/Closer17E.lean) | 2 | Exercise 17.E.5 with three consumers |
| [Closer17HTwo](MWGPositiveEquilibriumTheory/Closer17HTwo.lean) | 8 | Property (b) for `L = 2` with several equilibria |
| [Closer17AA](MWGPositiveEquilibriumTheory/Closer17AA.lean) | 7 | Exercise 17.AA.2, differentiable sufficient condition |
| [Closer17F](MWGPositiveEquilibriumTheory/Closer17F.lean) | 9 | Exercise 17.F.6: counterexample to the general case |
| [Closer17FTax](MWGPositiveEquilibriumTheory/Closer17FTax.lean) | 8 | Exercise 17.F.15: preferences for the demand path |
| [Closer17IExist](MWGPositiveEquilibriumTheory/Closer17IExist.lean) | 12 | Existence for the convexified economy (Section 17.I) |

From this directory, run:

```sh
export PATH="$HOME/.elan/bin:$PATH"
lake build
python3 -m unittest discover -s scripts -p 'test_*.py' -v
python3 scripts/verify.py
```
