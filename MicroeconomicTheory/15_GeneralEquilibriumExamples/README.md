# MWGGeneralEquilibriumExamples

Formalization of Mas-Colell, Whinston and Green, *Microeconomic Theory*, Chapter 15, "General
Equilibrium Theory: Some Examples", pp. 515-544, with the Part Four introduction (pp. 511-514):
pure exchange and the Edgeworth box (15.B: allocations, budget sets, offer curves, Walrasian
equilibrium, Pareto optimality, the contract curve, multiple equilibria and nonexistence, the
first and second welfare theorems and their failures), the one-consumer, one-producer economy
(15.C), the 2 × 2 production model (15.D: factor price equalization, Stolper-Samuelson, Rybczynski,
the diversification cone, the small open economy) and general versus partial equilibrium (15.E), and
the end-of-chapter exercises 15.B.1-15.D.9. The audit passed **424 theorems and 573 declarations
across 22 modules**. Coverage is in the [source map](docs/source-map.md); no item is OPEN. Departures from the printed text are in
[corrections](docs/corrections.md), among them counterexamples to the claim that every offer curve
passes through the endowment (p. 517), to Exercise 15.B.10(b) as printed, to the
Heckscher-Ohlin theorem of Exercise 15.D.9 as printed, and to Exercises 15.D.1(b) and 15.D.6(c) as
printed for the 2 × 2 model as formalized (both are proved for technologies differentiable along
rays).

The pure exchange economy (`ExchangeEconomy`, with the Edgeworth box `EdgeworthEconomy`), the
welfare theorems for it (any number of consumers and goods), the one-consumer economy
(`RCEconomy`), the factor-market model (`IsFactorEqm`) and the 2 × 2 model (`TwoByTwo`) are
written as reusable structures for Chapters 16 and 17, as are the Pareto curve of the box
(`ExchangeEconomy.paretoCurve`), the Cobb-Douglas 2 × 2 model (`cdtModel`) and the two-consumer
production economy (`TCEconomy`).

This is a Lake project pinned to Lean and Mathlib `v4.34.0`. It imports (Lake `path` requirement)
MWG Chapter 10 (`MWGCompetitiveMarkets`: Definitions 10.B.1-10.B.3, to which the exchange economy
is bridged by `isDemandEqm_iff_competitiveEqm` and `isParetoOptimal_iff_economy`, and the
derivative sandwich criterion) and, through it, MWG Chapter 3 (`MWGClassicalDemand`: Walrasian
demand, local nonsatiation, strong monotonicity and convexity of preferences, the Cobb-Douglas
demand of Example 3.D.1, Exercise 3.B.1) and Chapter 2 (`MWGConsumerChoice`: budget sets,
`nonnegOrthant`). It has no other dependency. See [third-party notices](THIRD_PARTY_NOTICES.md).

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Exchange](MWGGeneralEquilibriumExamples/Exchange.lean) | 21 | Exchange economies, (15.B.1), budget sets, offer curves, Definitions 15.B.1-15.B.3, bridges to Chapter 10, Exercise 15.B.1 |
| [Tools](MWGGeneralEquilibriumExamples/Tools.lean) | 9 | Continuity and derivative lemmas, quasiconcavity from convex preferences, tangent lines of concave functions |
| [Welfare](MWGGeneralEquilibriumExamples/Welfare.lean) | 15 | First and second welfare theorems, tangency at interior optima, endowment transfers, footnote 4 |
| [CobbDouglasBox](MWGGeneralEquilibriumExamples/CobbDouglasBox.lean) | 12 | Example 15.B.1, Exercise 15.B.2 with comparative statics |
| [MultipleEquilibria](MWGGeneralEquilibriumExamples/MultipleEquilibria.lean) | 15 | Example 15.B.2 and Exercise 15.B.5 |
| [Blair](MWGGeneralEquilibriumExamples/Blair.lean) | 12 | CES demand with exponent `-2`, Exercise 15.B.6 |
| [OfferCurves](MWGGeneralEquilibriumExamples/OfferCurves.lean) | 8 | Offer curves through the endowment, Exercise 15.B.4 |
| [Nonexistence](MWGGeneralEquilibriumExamples/Nonexistence.lean) | 27 | Figures 15.B.10 and 15.B.14, Exercise 15.B.9 |
| [QuasilinearBox](MWGGeneralEquilibriumExamples/QuasilinearBox.lean) | 13 | Exercises 15.B.8 and 15.B.10(a)-(b) (correction 9) |
| [RobinsonCrusoe](MWGGeneralEquilibriumExamples/RobinsonCrusoe.lean) | 13 | Section 15.C: equilibrium, welfare theorems, footnote 7, Figure 15.C.3(a), Exercise 15.C.1(a) |
| [RobinsonExercises](MWGGeneralEquilibriumExamples/RobinsonExercises.lean) | 10 | Exercises 15.C.1(b) and 15.C.2, footnote 8 |
| [FactorMarkets](MWGGeneralEquilibriumExamples/FactorMarkets.lean) | 7 | Factor market equilibrium, (15.D.1)-(15.D.6), Exercise 15.D.2 |
| [TwoByTwo](MWGGeneralEquilibriumExamples/TwoByTwo.lean) | 32 | The 2 × 2 model: unit costs, factor intensity, factor price equalization, Propositions 15.D.1-15.D.2, Exercises 15.D.3, 15.D.5, 15.D.6(a)-(b), the Leontief instance |
| [ProductionExercises](MWGGeneralEquilibriumExamples/ProductionExercises.lean) | 13 | Exercises 15.D.7 and 15.D.9 (correction 11) |
| [ClosedEconomy](MWGGeneralEquilibriumExamples/ClosedEconomy.lean) | 6 | Exercise 15.D.4 |
| [GeneralVersusPartial](MWGGeneralEquilibriumExamples/GeneralVersusPartial.lean) | 7 | Section 15.E: the tax incidence example |
| [TwoConsumerProduction](MWGGeneralEquilibriumExamples/TwoConsumerProduction.lean) | 29 | Two consumers with labor endowments and one firm: Exercise 15.C.1(c), multiplicity and the constant-returns case |
| [OfferCurveExamples](MWGGeneralEquilibriumExamples/OfferCurveExamples.lean) | 12 | Exercise 15.B.4(d) (a non-normal offer curve), Figure 15.B.10(b) (disconnected offer curve) |
| [CobbDouglasTwoByTwo](MWGGeneralEquilibriumExamples/CobbDouglasTwoByTwo.lean) | 68 | The Cobb-Douglas 2 × 2 model, Exercises 15.D.6(c)-(d) (correction 15) and 15.D.8 |
| [FactorParetoSet](MWGGeneralEquilibriumExamples/FactorParetoSet.lean) | 32 | Pareto set of factor allocations (p. 533), Exercise 15.D.1 (correction 17), footnote 16 |
| [ClosedEconomyGeneral](MWGGeneralEquilibriumExamples/ClosedEconomyGeneral.lean) | 4 | Exercise 15.D.4(b) for a general model |
| [ParetoCurve](MWGGeneralEquilibriumExamples/ParetoCurve.lean) | 59 | Exercises 15.B.7 and 15.B.10(d): the Pareto curve, homothetic preferences, the transfer paradox |

From this directory, run:

```sh
export PATH="$HOME/.elan/bin:$PATH"
lake build
python3 -m unittest discover -s scripts -p 'test_*.py' -v
python3 scripts/verify.py
```
