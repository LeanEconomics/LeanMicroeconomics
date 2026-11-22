# MWGWelfareTheorems

Formalization of Mas-Colell, Whinston and Green, *Microeconomic Theory*, Chapter 16, "Equilibrium
and Its Basic Welfare Properties", pp. 545-577, with Appendix A (technical properties of the set of
feasible allocations) and the end-of-chapter exercises 16.C.1-16.AA.3: the basic model of a
private ownership production economy (16.B), the first welfare theorem (16.C), the second welfare
theorem with quasiequilibria and the cheaper consumption argument (16.D), Pareto optimality and
social welfare optima (16.E), first-order conditions for Pareto optimality (16.F, with the Fritz
John and Kuhn-Tucker conditions proved), and applications: contingent commodities, occupational
choice, Lindahl equilibrium with both welfare theorems and marginal cost pricing (16.G). The audit passed **181 theorems and
275 declarations across 18 modules**. Coverage is in the [source map](docs/source-map.md); one
item is OPEN (footnote 13: Kannai's concavifiability theorem). Departures from the printed text
are in [corrections](docs/corrections.md), among them counterexamples to the claim that every
price equilibrium with transfers is a quasiequilibrium (p. 552, `p = 0`), to Proposition 16.D.3
without local nonsatiation, to Proposition 16.AA.1 and the closedness claim of p. 574 (aggregate
production set not closed), to footnote 18's constraint qualification claim, to Exercise 16.G.4
without an optimum, and to the wealth condition of Definition 16.G.1 as printed.

The general economy (`PrefEconomy`, with preference relations, consumption sets, production sets
and total endowment), the private ownership economy (`PrivPrefEconomy`, with endowments and
shares), Walrasian equilibrium, price equilibrium and quasiequilibrium with transfers, Pareto
optimality, the utility possibility set and the marginal cost price equilibrium are written as
reusable definitions for Chapters 17 and 18.

This is a Lake project pinned to Lean and Mathlib `v4.34.0`. It imports (Lake `path` requirement)
MWG Chapter 15 (`MWGGeneralEquilibriumExamples`: the exchange economy, bridged by
`exchangeToPrefEconomy`) and, through it, Chapter 10 (`MWGCompetitiveMarkets`: allocations and
Definition 10.B.3, bridged by `isWalrasEqm_iff_competitiveEqm`), Chapter 5 (`MWGProduction`:
`supply`), Chapter 3 (`MWGClassicalDemand`: preference properties, Proposition 3.C.1, Theorems
M.G.2 and M.C.3, the line-derivative lemmas of M.C and M.K) and Chapter 2 (`MWGConsumerChoice`).
It has no other dependency. See [third-party notices](THIRD_PARTY_NOTICES.md).

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Basic](MWGWelfareTheorems/Basic.lean) | 24 | Definitions 16.B.1-16.B.4, 16.C.1, 16.D.1, pure exchange, footnotes 3-4, correction 1, bridges to Chapters 10 and 15 |
| [FirstWelfare](MWGWelfareTheorems/FirstWelfare.lean) | 17 | Proposition 16.C.1, Figure 16.C.1, Exercises 16.C.1-16.C.4 |
| [SecondWelfare](MWGWelfareTheorems/SecondWelfare.lean) | 10 | Proposition 16.D.1 (Steps 1-9), Exercises 16.D.1-16.D.2 |
| [CheaperPoint](MWGWelfareTheorems/CheaperPoint.lean) | 11 | Propositions 16.D.2-16.D.3, footnotes 6-9, correction 2, Exercise 16.D.3 |
| [QuasiExample](MWGWelfareTheorems/QuasiExample.lean) | 7 | Figure 16.D.2, the strongly monotone pure exchange claim of p. 556 |
| [Replica](MWGWelfareTheorems/Replica.lean) | 9 | Figures 16.D.4-16.D.5, Exercise 16.D.4 |
| [SocialWelfare](MWGWelfareTheorems/SocialWelfare.lean) | 12 | `U`, `UP`, Propositions 16.E.1-16.E.2, footnote 12, Figure 16.E.1, (16.E.2), Exercise 16.E.2 |
| [UtilityFrontier](MWGWelfareTheorems/UtilityFrontier.lean) | 5 | Exercise 16.E.1(b)-(c) |
| [Appendix](MWGWelfareTheorems/Appendix.lean) | 15 | Propositions 16.AA.1 (correction 3) and 16.AA.2, Exercises 16.AA.1-16.AA.3 |
| [FritzJohn](MWGWelfareTheorems/FritzJohn.lean) | 2 | Fritz John conditions via Gordan's alternative (geometric Hahn-Banach) |
| [FirstOrder](MWGWelfareTheorems/FirstOrder.lean) | 9 | Problem (16.F.1), Exercises 16.F.1-16.F.2 |
| [FirstOrderWelfare](MWGWelfareTheorems/FirstOrderWelfare.lean) | 12 | Binding constraints, Exercise 16.F.3, (16.F.10)-(16.F.14), Pareto optimum iff equilibrium, Proposition 16.F.1, footnote 18 (correction 4) |
| [RatioConditions](MWGWelfareTheorems/RatioConditions.lean) | 8 | Exercise 16.F.4: (16.F.4)-(16.F.6) |
| [MarginalCost](MWGWelfareTheorems/MarginalCost.lean) | 3 | Marginal cost price equilibrium, Proposition 16.G.1, Exercises 16.G.1-16.G.2 |
| [MCExamples](MWGWelfareTheorems/MCExamples.lean) | 7 | Figures 16.G.1-16.G.2, Exercises 16.G.3-16.G.4 (correction 5) |
| [Applications](MWGWelfareTheorems/Applications.lean) | 9 | Examples 16.G.1-16.G.3, Definition 16.G.1 (correction 6), footnotes 20 and 23 |
| [Exercise16G5](MWGWelfareTheorems/Exercise16G5.lean) | 9 | Exercise 16.G.5(a)-(e) |
| [LindahlSecond](MWGWelfareTheorems/LindahlSecond.lean) | 12 | Second welfare theorem for Lindahl equilibria via the artificial economy, with an instance |

From this directory, run:

```sh
export PATH="$HOME/.elan/bin:$PATH"
lake build
python3 -m unittest discover -s scripts -p 'test_*.py' -v
python3 scripts/verify.py
```
