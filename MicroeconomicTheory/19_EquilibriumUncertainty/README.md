# MWGEquilibriumUncertainty

Formalization of Mas-Colell, Whinston and Green, *Microeconomic Theory*, Chapter 19, "General
Equilibrium Under Uncertainty", pp. 687-731, with its end-of-chapter exercises: contingent
commodities and information structures (19.B), Arrow-Debreu equilibrium and risk sharing (19.C),
sequential trade and Radner equilibrium (19.D, Proposition 19.D.1), asset markets, arbitrage and
complete asset structures (19.E, Propositions 19.E.1-19.E.3 with both proofs of 19.E.1),
incomplete markets, sunspots and constrained efficiency (19.F, Proposition 19.F.1), firm behavior
(19.G) and imperfect information and rational expectations equilibrium (19.H, Proposition 19.H.1).
The audit passed **278 theorems and 436 declarations across 20 modules**. Coverage is in the
[source map](docs/source-map.md); nothing is OPEN: Exercise 19.F.3 (more assets, everybody worse
off) and Hart's nonexistence example of Exercise 19.F.4 are constructed and proved, and the
equilibria of Exercise 19.H.6(b)-(e) are computed. Departures from the printed text are in [corrections](docs/corrections.md),
among them counterexamples to Proposition 19.D.1(ii) without monotonicity, to the state
independence of Pareto optima with a zero-probability state (Example 19.F.1), to the dispersion
argument of Example 19.E.6, the impossibility of the example requested in Exercise 19.G.2, an
arbitrage in Exercise 19.E.6(d), and the corrected prices of Example 19.H.4.

Arrow-Debreu equilibrium is shown to be Walrasian equilibrium (Definition 16.B.3) of the economy
with `LS` commodities, so the welfare theorems of Chapter 16 apply directly. Lemma 19.E.1 is
proved as in the book with the separating hyperplane theorem M.G.2 of Chapter 3.

This is a Lake project pinned to Lean and Mathlib `v4.34.0`. It imports (Lake `path`
requirements) MWG Chapter 16 (`MWGWelfareTheorems`: private ownership economies, Walrasian
equilibrium, Pareto optimality, Propositions 16.C.1 and 16.D.1) and, through it, Chapters 15, 10,
5, 3 and 2 (in particular Chapter 3's preference properties and Theorem M.G.2), and MWG Chapter 6
(`MWGChoiceUnderUncertainty`: Definition 6.E.2). It has no other dependency. See
[third-party notices](THIRD_PARTY_NOTICES.md).

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Basic](MWGEquilibriumUncertainty/Basic.lean) | 10 | Definition 19.B.1, Examples 19.B.1-19.B.3, footnotes 2-3, shares (correction 1), information structures, strong monotonicity |
| [ArrowDebreu](MWGEquilibriumUncertainty/ArrowDebreu.lean) | 18 | Definition 19.C.1, bridge to Chapter 16, welfare theorems, Exercise 19.C.1, exchange economies |
| [Calculus](MWGEquilibriumUncertainty/Calculus.lean) | 10 | One-sided derivative tests, the Lagrange alternative, directional first-order conditions, quasilinear demand |
| [Exchange](MWGEquilibriumUncertainty/Exchange.lean) | 21 | Pareto optimality, first welfare theorem for exchange, state independence of Pareto optima, one-good first-order conditions, Pareto tangency |
| [RiskSharing](MWGEquilibriumUncertainty/RiskSharing.lean) | 12 | Examples 19.C.1-19.C.2, Exercises 19.C.2-19.C.5 |
| [Sequential](MWGEquilibriumUncertainty/Sequential.lean) | 14 | Definitions 19.D.1 and 19.E.2, Proposition 19.D.1 (correction 2), footnotes 5 and 7, Exercise 19.D.1 |
| [SequentialExamples](MWGEquilibriumUncertainty/SequentialExamples.lean) | 8 | Example 19.D.1, Exercises 19.D.2-19.D.4 |
| [Assets](MWGEquilibriumUncertainty/Assets.lean) | 20 | Definition 19.E.1, Examples 19.E.1-19.E.5, Lemma 19.E.1, Proposition 19.E.1 (Proof 1), Definition 19.E.3, Exercise 19.E.2 |
| [AssetsFOC](MWGEquilibriumUncertainty/AssetsFOC.lean) | 6 | Proposition 19.E.1 (Proof 2), Exercise 19.E.1 |
| [Complete](MWGEquilibriumUncertainty/Complete.lean) | 22 | Propositions 19.E.2-19.E.3, redundancy, Exercises 19.E.3-19.E.4, Example 19.E.6 (correction 3), Exercise 19.E.6 |
| [LongLived](MWGEquilibriumUncertainty/LongLived.lean) | 3 | Example 19.E.7, Exercise 19.E.5, footnote 21 |
| [Incomplete](MWGEquilibriumUncertainty/Incomplete.lean) | 15 | Example 19.F.1 (sunspots), Definition 19.F.1, Proposition 19.F.1, Example 19.F.2, Exercises 19.F.1-19.F.2 |
| [Firms](MWGEquilibriumUncertainty/Firms.lean) | 7 | Definition 19.G.1, (19.G.1), unanimity, Exercises 19.G.1-19.G.4 |
| [Information](MWGEquilibriumUncertainty/Information.lean) | 22 | Signals, Definition 19.H.1, Proposition 19.H.1, Exercises 19.H.1-19.H.3, Example 19.H.1 |
| [RationalExpectations](MWGEquilibriumUncertainty/RationalExpectations.lean) | 20 | Definition 19.H.2, pooled information price functions, Examples 19.H.2-19.H.3 |
| [REExamples](MWGEquilibriumUncertainty/REExamples.lean) | 29 | Examples 19.H.4-19.H.6, Exercises 19.H.4, 19.H.5, 19.H.7 |
| [ExercisesFH](MWGEquilibriumUncertainty/ExercisesFH.lean) | 8 | Exercises 19.F.5 and 19.H.6(a), surplus and Pareto optimality |
| [Closer19F3](MWGEquilibriumUncertainty/Closer19F3.lean) | 14 | Exercise 19.F.3(a)-(c): spot and Arrow-Debreu equilibria, the four-state economy, one versus three assets |
| [Closer19H6](MWGEquilibriumUncertainty/Closer19H6.lean) | 8 | Exercise 19.H.6(b)-(e): non-contingent and contingent equilibria within events, ex ante utilities, closed-form instance |
| [Closer19F4](MWGEquilibriumUncertainty/Closer19F4.lean) | 11 | Exercise 19.F.4: real assets, demand for `∑ cⱼ√yⱼ`, Hart's example with no Radner equilibrium |

From this directory, run:

```sh
export PATH="$HOME/.elan/bin:$PATH"
lake build
python3 -m unittest discover -s scripts -p 'test_*.py' -v
python3 scripts/verify.py
```

The full build, fresh recompilation and unchanged verifier's transitive-axiom audit passed on
2026-11-23. Only `propext`, `Classical.choice` and `Quot.sound` occur. Dependency declarations are
trusted from their own audited projects.
