# MWGCompetitiveMarkets

Formalization of Mas-Colell, Whinston and Green, *Microeconomic Theory*, Chapter 10,
"Competitive Markets", pp. 311-349: Pareto optimality and competitive (Walrasian) equilibrium
(10.B), partial equilibrium analysis with quasilinear utility (10.C: equilibrium as an instance of
Definition 10.B.3, existence and uniqueness, demand and supply, comparative statics and tax
incidence), the fundamental welfare theorems in the partial equilibrium model (10.D), welfare
analysis with Marshallian surplus and deadweight loss (10.E), free entry and long-run equilibria
(10.F), the concluding remarks on groups of goods (10.G), and every end-of-chapter exercise
(10.B.1-10.G.5). The chapter has no appendix. The audit passed **365 theorems and 471
declarations across 17 modules**. Coverage is in the [source map](docs/source-map.md); no item is
OPEN. Departures from the printed text are in [corrections](docs/corrections.md) (among them
counterexamples for the supply derivative on p. 319, Exercise 10.F.3 as printed and the kink claim
of Exercise 10.F.7).

This is a Lake project pinned to Lean and Mathlib `v4.34.0`. It imports (Lake `path`
requirement) MWG Chapter 5 (`MWGProduction`: the supply correspondence used in Definition
10.B.3, Exercise 5.B.4's nonclosed additive closure, Exercise 5.D.1's average-cost condition,
Exercise 5.D.3's Le Chatelier principle and Example 5.C.1's Cobb-Douglas cost) and, through it,
MWG Chapter 3 (`MWGClassicalDemand`: `walrasianDemandOn`, strong monotonicity) and Chapter 2
(`MWGConsumerChoice`: budget sets, `nonnegOrthant`); it has no other dependency. See [third-party notices](THIRD_PARTY_NOTICES.md).

| Module | Theorems | Contents |
| --- | ---: | --- |
| [FOCTools](MWGCompetitiveMarkets/FOCTools.lean) | 23 | Kuhn-Tucker conditions on `ℝ₊`, the solution `focSol` of `d(x) ≤ r` and its continuity and derivative, a sandwich criterion for derivatives |
| [ParetoEquilibrium](MWGCompetitiveMarkets/ParetoEquilibrium.lean) | 13 | Definitions 10.B.1-10.B.3, the utility possibility set, Lemma 10.B.1, Exercises 10.B.1-10.B.2 |
| [QuasilinearModel](MWGCompetitiveMarkets/QuasilinearModel.lean) | 61 | Quasilinear consumers and firms, demand and supply functions and aggregates (p. 319), concrete instances, correction 1 |
| [QuasilinearEquilibrium](MWGCompetitiveMarkets/QuasilinearEquilibrium.lean) | 15 | (10.C.1)-(10.C.3) as a characterization of Definition 10.B.3, independence of endowments, existence and uniqueness, constant returns, Figure 10.C.8 |
| [WelfareTheorems](MWGCompetitiveMarkets/WelfareTheorems.lean) | 26 | (10.D.1), Pareto optimality via aggregate surplus, (10.D.2)-(10.D.5), Propositions 10.D.1-10.D.2, footnote 15, (10.D.6), Exercises 10.D.1, 10.D.3, 10.D.4 |
| [ConvexExistence](MWGCompetitiveMarkets/ConvexExistence.lean) | 7 | Existence (surplus maximization) and uniqueness of equilibrium with convex costs; Proposition 10.D.2 without a presupposed equilibrium |
| [CentralAuthority](MWGCompetitiveMarkets/CentralAuthority.lean) | 49 | Exercises 10.C.3-10.C.4, inverse demand `P = x⁻¹`, industry marginal cost `C' = q⁻¹` |
| [Surplus](MWGCompetitiveMarkets/Surplus.lean) | 31 | Section 10.E: welfare and surplus, (10.E.2)-(10.E.12), footnotes 17 and 19, deadweight loss, Exercise 10.E.2 |
| [TaxIncidence](MWGCompetitiveMarkets/TaxIncidence.lean) | 25 | Example 10.C.1 ((10.C.7)-(10.C.8)), Example 10.E.1, Exercises 10.C.5-10.C.7 |
| [FreeEntry](MWGCompetitiveMarkets/FreeEntry.lean) | 21 | Section 10.F: Definition 10.F.1, long-run supply, constant returns, strictly convex costs (Exercise 10.F.1), efficient scale, footnotes 25-29, efficiency, Example 10.F.1 |
| [ExercisesF](MWGCompetitiveMarkets/ExercisesF.lean) | 14 | Exercises 10.F.2-10.F.4 (correction 7) |
| [ExercisesF2](MWGCompetitiveMarkets/ExercisesF2.lean) | 13 | Exercises 10.F.5-10.F.7 (correction 8), an instance of Example 10.F.1 |
| [ExercisesC](MWGCompetitiveMarkets/ExercisesC.lean) | 18 | Exercises 10.C.1, 10.C.2, 10.C.8-10.C.11, 10.D.2 |
| [ExercisesE](MWGCompetitiveMarkets/ExercisesE.lean) | 13 | Quasilinear CV = EV (small type, p. 334), Exercises 10.E.1 and 10.E.3 |
| [DerivedPaths](MWGCompetitiveMarkets/DerivedPaths.lean) | 9 | One-variable implicit function theorem; derived equilibrium paths for Exercises 10.C.5 and 10.E.1(a); Lagrange multiplier for Exercise 10.E.3(b) |
| [GroupMarkets](MWGCompetitiveMarkets/GroupMarkets.lean) | 20 | Section 10.G: groups of goods, Exercises 10.G.1-10.G.5, footnote 32 |
| [Instances](MWGCompetitiveMarkets/Instances.lean) | 7 | A concrete economy with an equilibrium, Propositions 10.D.1-10.D.2 applied, further instances |

From this directory, run:

```sh
export PATH="$HOME/.elan/bin:$PATH"
lake build
python3 -m unittest discover -s scripts -p 'test_*.py' -v
python3 scripts/verify.py
```
