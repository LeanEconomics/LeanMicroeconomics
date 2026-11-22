# MWGExternalitiesPublicGoods

Formalization of Mas-Colell, Whinston and Green, *Microeconomic Theory*, Chapter 11,
"Externalities and Public Goods", pp. 350-382: the bilateral externality (11.B: inefficiency of
equilibrium, quotas, Pigouvian taxes, bargaining and the Coase theorem, the market for rights),
public goods (11.C: the Samuelson condition, private provision and free riding, corrective
subsidies, Lindahl equilibrium), multilateral externalities (11.D: depletable externalities with
necessary and sufficient multiplier conditions and an efficient market, nondepletable ones with
quotas, taxes and tradable permits), private information (11.E: inefficient bargaining, quotas
versus taxes, the Groves-Clarke mechanism and its budget problem), Appendix A (nonconvexities),
and every exercise (11.B.1-11.E.7). The audit passed **235 theorems and 349 declarations across
15 modules**. Coverage is in the [source map](docs/source-map.md); no item is OPEN (two results
cited from Chapter 23 are left to that chapter). Departures from the printed text are in
[corrections](docs/corrections.md), among them counterexamples to the existence of a solution of
(11.E.1), Exercise 11.B.2(c) as printed, Exercise 11.D.6(a) at `I = 2` and Exercise 11.E.7's
tax schedule.

This is a Lake project pinned to Lean and Mathlib `v4.34.0`. It imports (Lake `path`
requirements) MWG Chapter 10 (`MWGCompetitiveMarkets`: the Kuhn-Tucker tools `IsFOCSol`,
`isFOCSol_unique`, `foc_max_iff`, `foc_max_necessary`, `foc_local_necessary`, `foc_tangent_le`)
and MWG Chapter 8 (`MWGSimultaneousMoveGames`: `WeaklyDominant`, `IsNashEquilibrium`, with
Chapter 7's `NormalForm`), and through them Chapters 2, 3, 5 and 7. See
[third-party notices](THIRD_PARTY_NOTICES.md).

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Tools](MWGExternalitiesPublicGoods/Tools.lean) | 10 | Quasilinear Pareto optimality iff surplus maximization (footnote 4), take-it-or-leave-it offers, Kuhn-Tucker on `ℝ₊` |
| [Concavity](MWGExternalitiesPublicGoods/Concavity.lean) | 6 | Tangent inequalities for convex/concave functions of several variables, Kuhn-Tucker on the orthant |
| [Bilateral](MWGExternalitiesPublicGoods/Bilateral.lean) | 34 | Section 11.B: Definition 11.B.1, footnotes 2-5, (11.B.1)-(11.B.7), quotas, Pigouvian taxes, the Coase theorem, Figure 11.B.3, the rights market |
| [PublicGoods](MWGExternalitiesPublicGoods/PublicGoods.lean) | 27 | Section 11.C: Definition 11.C.1, (11.C.1)-(11.C.8), free riding, subsidies (Exercises 11.C.1-11.C.2), Lindahl equilibrium, footnotes 9-11 |
| [Multilateral](MWGExternalitiesPublicGoods/Multilateral.lean) | 20 | Section 11.D: (11.D.1)-(11.D.6), footnotes 13 and 15, depletable markets, quotas, the uniform tax, tradable permits |
| [PrivateInfo](MWGExternalitiesPublicGoods/PrivateInfo.lean) | 15 | Section 11.E, pp. 368-372: (11.E.1) and its correction, quotas and taxes, Figures 11.E.2-11.E.4, footnotes 22-23, permits |
| [GrovesClarke](MWGExternalitiesPublicGoods/GrovesClarke.lean) | 19 | Section 11.E, pp. 373-374: the Groves-Clarke mechanism, budget imbalance, Exercises 11.E.3-11.E.6 |
| [AppendixA](MWGExternalitiesPublicGoods/AppendixA.lean) | 12 | Examples 11.AA.1-11.AA.3 |
| [ExercisesB](MWGExternalitiesPublicGoods/ExercisesB.lean) | 26 | Exercises 11.B.1-11.B.5 |
| [ExercisesC](MWGExternalitiesPublicGoods/ExercisesC.lean) | 4 | Exercise 11.C.3 (Lagrange multipliers) |
| [ExercisesD1](MWGExternalitiesPublicGoods/ExercisesD1.lean) | 11 | Exercises 11.D.1 (a Chapter 7 normal form) and 11.D.2 |
| [ExercisesD2](MWGExternalitiesPublicGoods/ExercisesD2.lean) | 11 | Exercises 11.D.3-11.D.4 |
| [ExercisesD3](MWGExternalitiesPublicGoods/ExercisesD3.lean) | 21 | Exercises 11.D.5-11.D.7 |
| [ExercisesE](MWGExternalitiesPublicGoods/ExercisesE.lean) | 11 | Exercises 11.E.1, 11.E.2 (expectations against a probability measure) and 11.E.7 |
| [Instances](MWGExternalitiesPublicGoods/Instances.lean) | 8 | Concrete instances of hypotheses not instantiated in their own modules |

From this directory, run:

```sh
export PATH="$HOME/.elan/bin:$PATH"
lake build
python3 -m unittest discover -s scripts -p 'test_*.py' -v
python3 scripts/verify.py
```
