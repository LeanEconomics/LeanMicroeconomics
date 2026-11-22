# MWGAggregateDemand

Formalization of Mas-Colell, Whinston and Green, *Microeconomic Theory*, Chapter 4,
"Aggregate Demand", pp. 105-126: Sections 4.A-4.D, Appendix A (regularizing effects of
aggregation) and Exercises 4.B.1-4.D.11. The audit passed **204 theorems and 274 declarations
across 20 modules**. Coverage is in the [source map](docs/source-map.md) (no item is OPEN);
departures, including false printed claims with counterexamples, are in
[corrections](docs/corrections.md).

This is a Lake project pinned to Lean and Mathlib `v4.34.0`. It imports (Lake `path`
requirements) MWG Chapter 3 `MWGClassicalDemand` (Walrasian and Hicksian demand, indirect
utility and expenditure functions, Roy's identity, Shephard's lemma, the Slutsky equation,
Theorem M.J.2), MWG Chapter 2 `MWGConsumerChoice` (weak axiom, Slutsky matrix, Samuelson's
sufficient condition, matrix definiteness); MWG Chapter 1 `MWGPreferenceChoice` is a declared
requirement used only through them, as are the Kreps chapters they require. See [third-party notices](THIRD_PARTY_NOTICES.md).

Highlights: Proposition 4.B.1 in both directions (the book proves only sufficiency); the
uncompensated law of demand for homothetic preferences without differentiability; the
Mitiushin-Polterovich theorem (Proposition 4.C.3) with corner demands; Hildenbrand's
Proposition 4.C.4 for every preference-generated demand via a Young-type inequality, with a
counterexample to its strict part, the strict part under the book's Slutsky hypothesis (by
Fubini), and the extension to nonincreasing densities; Proposition 4.D.1 without
differentiability; the `A ⊆ B` Slutsky condition of Exercise 4.D.9; the quasilinear pair of
Exercises 4.C.11 and 4.D.10 (Slutsky matrices on all four regions, the weak axiom across the
kinks, a positive but no normative representative, the latter by a finite revealed-preference
chain); a three-good Hildenbrand economy with a revealed-preference 3-cycle (Exercise 4.D.11).

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Basic](MWGAggregateDemand/Basic.lean) | 10 | Aggregate demand, invariance, distribution and share rules; continuity, homogeneity, Walras' law |
| [AggregateWealth](MWGAggregateDemand/AggregateWealth.lean) | 19 | Section 4.B: (4.B.1), footnotes 3-4, invariance iff parallel paths, Proposition 4.B.1 sufficiency; Exercises 4.B.1-4.B.2 |
| [LawOfDemand](MWGAggregateDemand/LawOfDemand.lean) | 14 | Definitions 4.C.1-4.C.2, (4.C.1)-(4.C.2), Propositions 4.C.1-4.C.2; Exercise 4.C.1 |
| [AggregateSlutsky](MWGAggregateDemand/AggregateSlutsky.lean) | 19 | (4.C.4)-(4.C.8), the covariance matrix `C`, Leontief `S = 0`; Exercises 4.C.2, 4.C.8, 4.C.9 |
| [LShaped](MWGAggregateDemand/LShaped.lean) | 26 | L-shaped preferences; Example 4.C.1; Exercises 4.C.3, 4.C.12, 4.C.13 |
| [Representative](MWGAggregateDemand/Representative.lean) | 16 | Definitions 4.D.1-4.D.3, Proposition 4.D.1, `A ⊆ B`; Exercises 4.D.1-4.D.5, 4.D.8 |
| [RepresentativeExamples](MWGAggregateDemand/RepresentativeExamples.lean) | 5 | Examples 4.D.1-4.D.2, potential compensation; Exercises 4.D.6-4.D.7 |
| [Hildenbrand](MWGAggregateDemand/Hildenbrand.lean) | 11 | Proposition 4.C.4 and its strict-part counterexample; Exercises 4.C.7 (unimodal), 4.C.10 |
| [MitiushinPolterovich](MWGAggregateDemand/MitiushinPolterovich.lean) | 9 | Proposition 4.C.3 with boundary demands and on convex sets; Exercises 4.C.5-4.C.6 |
| [GormanNecessity](MWGAggregateDemand/GormanNecessity.lean) | 4 | Proposition 4.B.1, necessity |
| [AppendixA](MWGAggregateDemand/AppendixA.lean) | 3 | Example 4.AA.1 |
| [NormativeSlutsky](MWGAggregateDemand/NormativeSlutsky.lean) | 2 | Exercise 4.D.9 |
| [StrongAxiomExamples](MWGAggregateDemand/StrongAxiomExamples.lean) | 3 | WA without invariance; identical consumers satisfy the SA (p. 115) |
| [LShapedHomothetic](MWGAggregateDemand/LShapedHomothetic.lean) | 5 | Exercise 4.C.4 |
| [RepresentativeUtility](MWGAggregateDemand/RepresentativeUtility.lean) | 9 | Exercise 4.D.4(a), continuity on all of `ℝ^L_+` |
| [HildenbrandDensity](MWGAggregateDemand/HildenbrandDensity.lean) | 2 | Exercise 4.C.7 (nonincreasing density) |
| [QuasilinearPair](MWGAggregateDemand/QuasilinearPair.lean) | 5 | Exercise 4.C.11(a), (c) |
| [QuasilinearSlutsky](MWGAggregateDemand/QuasilinearSlutsky.lean) | 24 | Exercise 4.C.11(b), (c) conclusion; Exercise 4.D.10 |
| [HildenbrandStrict](MWGAggregateDemand/HildenbrandStrict.lean) | 6 | Proposition 4.C.4, strict part; Exercise 4.C.10 (WA) |
| [HildenbrandThreeGoods](MWGAggregateDemand/HildenbrandThreeGoods.lean) | 12 | Exercise 4.D.11 |

From this directory, run:

```sh
export PATH="$HOME/.elan/bin:$PATH"
lake build
python3 -m unittest discover -s scripts -p 'test_*.py' -v
python3 scripts/verify.py
```

The verifier builds the project, freshly recompiles the contributed modules and audits every
named declaration; only `propext`, `Classical.choice` and `Quot.sound` occur.
