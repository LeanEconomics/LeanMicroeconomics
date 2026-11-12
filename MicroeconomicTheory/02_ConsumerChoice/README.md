# MWGConsumerChoice

Formalization of Mas-Colell, Whinston and Green, *Microeconomic Theory*, Chapter 2,
"Consumer Choice", pp. 17-39, with Mathematical Appendix Sections M.A (pp. 926-927),
M.B (pp. 928-929) and M.D (pp. 935-940). Every definition, numbered result, small-type claim
and exercise subpart is accounted for in the [source map](docs/source-map.md); departures from
the printed text, including three false printed claims with counterexamples, are in
[corrections](docs/corrections.md). The audit passed **273 theorems and 356 declarations
across 23 modules**. OPEN (explained in the source map): the converse direction of
Exercise 2.F.3(e)-(f).

This is a Lake project pinned to Lean and Mathlib `v4.34.0`. It depends (Lake `path`
requirements) on Kreps Chapter 1 `ChoicePreferenceUtility` (rational preferences, best
elements), Kreps Chapter 3 `ConsumerDemand` (nonnegative orthant, budget sets at positive
prices) and MWG Chapter 1 `MWGPreferenceChoice` (choice structures, the weak axiom), and
bridges to them instead of copying. See
[third-party notices](THIRD_PARTY_NOTICES.md).

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Commodities](MWGConsumerChoice/Commodities.lean) | 10 | Commodity space, `ℝ^L_+` and the consumption sets of Figures 2.C.1-2.C.6 |
| [WalrasianBudget](MWGConsumerChoice/WalrasianBudget.lean) | 15 | Walrasian budget sets, budget hyperplane, convexity; Exercises 2.D.1-2.D.4 |
| [DemandBasics](MWGConsumerChoice/DemandBasics.lean) | 20 | Demand, homogeneity, Walras' law, choice-structure remarks, effect notation; Exercises 2.E.1, 2.E.7 |
| [DemandCalculus](MWGConsumerChoice/DemandCalculus.lean) | 7 | Derivatives of demand along price-wealth lines |
| [Aggregation](MWGConsumerChoice/Aggregation.lean) | 14 | Propositions 2.E.1-2.E.3, elasticities; Exercises 2.E.2-2.E.4 |
| [AggregationExercises](MWGConsumerChoice/AggregationExercises.lean) | 10 | Exercises 2.E.5, 2.E.6, 2.E.8 |
| [WeakAxiom](MWGConsumerChoice/WeakAxiom.lean) | 12 | Definition 2.F.1, Proposition 2.F.1, own-price law (corrected), Figure 2.F.4 |
| [WeakAxiomExercises](MWGConsumerChoice/WeakAxiomExercises.lean) | 12 | Exercises 2.F.1, 2.F.6, 2.F.12-2.F.14; Walrasian choice structures (MWG Ch. 1) |
| [RevealedData](MWGConsumerChoice/RevealedData.lean) | 21 | Figure 2.F.5, Example 2.F.1, Exercises 2.F.2-2.F.4 |
| [MatrixDefiniteness](MWGConsumerChoice/MatrixDefiniteness.lean) | 5 | Definition M.D.1 and Mathlib bridges |
| [Slutsky](MWGConsumerChoice/Slutsky.lean) | 16 | Slutsky matrix, Propositions 2.F.2-2.F.3; Exercises 2.F.5, 2.F.7-2.F.9(b), 2.F.11 |
| [SlutskyExamples](MWGConsumerChoice/SlutskyExamples.lean) | 28 | Exercises 2.F.10, 2.F.15, 2.F.16, 2.F.17 |
| [SamuelsonSufficiency](MWGConsumerChoice/SamuelsonSufficiency.lean) | 2 | Samuelson/KMS sufficiency (p. 35): negative definiteness off the price ray implies the weak axiom |
| [AppendixMA](MWGConsumerChoice/AppendixMA.lean) | 12 | Section M.A: derivative matrices, chain and product rules |
| [AppendixMB](MWGConsumerChoice/AppendixMB.lean) | 14 | Section M.B: homogeneous functions, Theorems M.B.1-M.B.2 |
| [AppendixMDBasic](MWGConsumerChoice/AppendixMDBasic.lean) | 20 | Theorem M.D.1, Example M.D.1, Definitions M.D.2-M.D.3, Theorem M.D.5(i)-(iv) |
| [AppendixMDDeterminants](MWGConsumerChoice/AppendixMDDeterminants.lean) | 13 | Theorem M.D.2(i), (iii) (Sylvester), footnote 8; Exercise 2.F.9(a) |
| [AppendixMDSemidef](MWGConsumerChoice/AppendixMDSemidef.lean) | 5 | Theorem M.D.2(ii) |
| [AppendixMDTangent](MWGConsumerChoice/AppendixMDTangent.lean) | 7 | Theorem M.D.4 |
| [AppendixMDNeumann](MWGConsumerChoice/AppendixMDNeumann.lean) | 2 | Theorem M.D.5(v) |
| [AppendixMDBordered](MWGConsumerChoice/AppendixMDBordered.lean) | 6 | Theorem M.D.3 counterexample, Example M.D.2 |
| [AppendixMDBorderedTests](MWGConsumerChoice/AppendixMDBorderedTests.lean) | 12 | Theorem M.D.3(i) corrected, Theorem M.D.3(ii) necessity |
| [AppendixMDBorderedSemidef](MWGConsumerChoice/AppendixMDBorderedSemidef.lean) | 10 | Theorem M.D.3(ii) sufficiency: perturbed bordered-determinant expansion |

From this directory, run:

```sh
lake build
python3 -m unittest discover -s scripts -p 'test_*.py' -v
python3 scripts/verify.py
```

The verifier builds the project, freshly recompiles the contributed modules and audits every
named declaration; only `propext`, `Classical.choice` and `Quot.sound` occur.
