# MWGSimultaneousMoveGames

Formalization of Mas-Colell, Whinston and Green, *Microeconomic Theory*, Chapter 8,
"Simultaneous-Move Games", pp. 235-266: dominant and dominated strategies and iterated
deletion (8.B), rationalizable strategies (8.C), Nash equilibrium in pure and mixed strategies
and its existence (8.D, Appendix A), Bayesian Nash equilibrium (8.E) and trembling-hand
perfection (8.F), together with Mathematical Appendix Section M.I (Brouwer, Kakutani and Tarski
fixed-point theorems). The hard results are proved: Nash existence via Kakutani for finite
mixed games (Proposition 8.D.2) and for continuous quasiconcave games (Proposition 8.D.3),
existence of a trembling-hand perfect equilibrium (Exercise 8.F.3, Selten), Proposition 8.F.1,
and the two-player equivalence of never-best responses and strict domination by a separating
hyperplane (Exercise 8.C.3); the two-player converses on pp. 245 and 259 (from Farkas' lemma
and Stiemke's alternative of Chapter 5); and every end-of-chapter exercise, including the
infinite-round Cournot deletion process (8.B.5) and the Bayesian games 8.E.1-8.E.3. The audit
passed **347 theorems and 504 declarations across 24 modules**. Coverage is in the
[source map](docs/source-map.md); nothing is left OPEN. Departures from the printed text are in [corrections](docs/corrections.md).

This is a Lake project pinned to Lean and Mathlib `v4.34.0`. It imports (Lake requirements, no
copies) MWG Chapter 7 (`MWGNoncooperativeGames`: `NormalForm`, `mixedPayoff`,
`mixedExtensionGame`, `IsMixedStrategy`, `matchingPennies`), MWG Chapter 3
(`MWGClassicalDemand`: Appendix M.H upper hemicontinuity) and LeanEconomics (pinned `04decca`:
`FixedPoint.Brouwer`, `FixedPoint.Kakutani`) and MWG Chapter 5 (`MWGProduction`: Appendix M.M,
`farkas`, `exists_pos_of_cone_inter_nonneg`, `isClosed_coneOf`). See [third-party notices](THIRD_PARTY_NOTICES.md).

Normal-form games are Chapter 7's `NormalForm I S`; `u_i(s_i, s_{-i})` is the payoff at
`Function.update s i s_i` (the `i`-th coordinate of `s` is ignored), and mixed strategies are
probability vectors with `u_i(σ) = N.mixedPayoff σ i`.

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Dominance](MWGSimultaneousMoveGames/Dominance.lean) | 16 | Definitions 8.B.1-8.B.3, 8.D.1, best-response correspondence, iterated strict dominance, Exercises 8.B.4 (with infinite counterexample) and 8.D.2 |
| [MixedPayoff](MWGSimultaneousMoveGames/MixedPayoff.lean) | 18 | Algebra of mixed payoffs: linearity in own strategy, the p. 240 expansion, pure tests, compound beliefs |
| [MixedStrategies](MWGSimultaneousMoveGames/MixedStrategies.lean) | 21 | Definition 8.B.4, Proposition 8.B.1, Exercises 8.B.6-8.B.7, Definition 8.C.1, footnote 1, Definition 8.D.2, Proposition 8.D.1, Corollary 8.D.1 |
| [AppendixMI](MWGSimultaneousMoveGames/AppendixMI.lean) | 12 | Section M.I: Theorems M.I.1-M.I.3, Figures M.I.1-M.I.3, the circle rotation |
| [Existence](MWGSimultaneousMoveGames/Existence.lean) | 14 | Appendix A: Lemma 8.AA.1, Propositions 8.D.3 and 8.D.2 via Kakutani; footnote 5 |
| [Rationalizable](MWGSimultaneousMoveGames/Rationalizable.lean) | 17 | Definition 8.C.2, Exercises 8.C.1-8.C.2, rationalizable ⊆ ISD survivors, NE strategies rationalizable, footnote 3 |
| [TwoPlayer](MWGSimultaneousMoveGames/TwoPlayer.lean) | 5 | Separating-hyperplane argument; correlated beliefs; Exercise 8.C.3 |
| [TremblingHand](MWGSimultaneousMoveGames/TremblingHand.lean) | 20 | Perturbed games, Definition 8.F.1, Propositions 8.F.1-8.F.2, Exercise 8.F.3 (existence) |
| [Bimatrix](MWGSimultaneousMoveGames/Bimatrix.lean) | 38 | Two-player payoff tables: Nash, domination, deletion and mixed payoffs in terms of the table |
| [Examples8B](MWGSimultaneousMoveGames/Examples8B.lean) | 11 | Figure 8.B.1, Examples 8.B.1-8.B.3, weak-deletion order dependence, Figure 8.B.5 |
| [Examples8CD](MWGSimultaneousMoveGames/Examples8CD.lean) | 16 | Example 8.C.1, Figure 8.C.2, Examples 8.D.1-8.D.5, Exercise 8.D.1, correlated signal |
| [Bayesian](MWGSimultaneousMoveGames/Bayesian.lean) | 10 | Bayesian games, (8.E.1), Definition 8.E.1, Proposition 8.E.1, Example 8.E.1 |
| [Zigger](MWGSimultaneousMoveGames/Zigger.lean) | 10 | Example 8.E.2 and (8.E.3) |
| [ExercisesBD](MWGSimultaneousMoveGames/ExercisesBD.lean) | 24 | Exercises 8.B.1, 8.B.2, 8.D.6, 8.D.7 (minimax), 8.D.8 |
| [ExercisesCF](MWGSimultaneousMoveGames/ExercisesCF.lean) | 10 | Figure 8.F.1, Exercises 8.C.4 and 8.F.2 |
| [Bargaining](MWGSimultaneousMoveGames/Bargaining.lean) | 4 | Exercise 8.D.4 |
| [TwoPlayerConverse](MWGSimultaneousMoveGames/TwoPlayerConverse.lean) | 18 | Gordan and Stiemke alternatives from Farkas; two-player converse of Proposition 8.F.2 (p. 259); rationalizability with probabilistic conjectures = iterated strict dominance (p. 245) |
| [Converses](MWGSimultaneousMoveGames/Converses.lean) | 5 | Counterexample to p. 245 under Definition 8.C.2 read literally; `(U, L)` of Figure 8.F.1 is THP |
| [Auctions](MWGSimultaneousMoveGames/Auctions.lean) | 20 | Exercises 8.B.3 (Vickrey) and 8.D.3 (first price, dollar bids) |
| [Cournot](MWGSimultaneousMoveGames/Cournot.lean) | 21 | Maximal deletion process; Exercises 8.B.5 (limit of deletion) and 8.E.3 (Bayesian Cournot) |
| [IceCream](MWGSimultaneousMoveGames/IceCream.lean) | 14 | Exercise 8.D.5 |
| [Kreps](MWGSimultaneousMoveGames/Kreps.lean) | 7 | Exercise 8.D.9 |
| [Armies](MWGSimultaneousMoveGames/Armies.lean) | 7 | Exercise 8.E.1 |
| [FirstPriceUniform](MWGSimultaneousMoveGames/FirstPriceUniform.lean) | 9 | Exercise 8.E.2 |

## Build and verify

From this chapter directory:

```sh
lake build
python3 -m unittest discover -s scripts -p 'test_*.py' -v
python3 scripts/verify.py
```

The verifier builds the library, recompiles all sources in a fresh file, and audits every
declaration's axioms (only `propext`, `Classical.choice` and `Quot.sound` are allowed).
