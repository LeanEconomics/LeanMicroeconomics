# MWGMarketPower

Formalization of Mas-Colell, Whinston and Green, *Microeconomic Theory*, Chapter 12, "Market
Power", pp. 383-435: monopoly pricing, its deadweight loss and perfect discrimination (12.B); the
Bertrand and Cournot models, the competitive limit of Cournot competition and the linear city
(12.C); repeated Bertrand interaction with Nash reversion (12.D); entry and welfare (12.E);
strategic precommitment (12.G); Appendix A on infinitely repeated games, including Nash
reversion, Friedman's theorem, severer (stick-and-carrot) punishments and the folk theorem with
exact average payoffs in pure strategies; and Appendix B on entry deterrence and accommodation.
The audit passed **661 theorems and 866 declarations across 43 modules**. Everything in the chapter is formalized except the Kreps-Scheinkman theorem
(p. 395), which MWG cites without proof; verbal and graphical items are listed as such in the
[source map](docs/source-map.md). Departures from the printed text are in
[corrections](docs/corrections.md): among them counterexamples to Lemma 12.AA.1's "only if",
Propositions 12.AA.1, 12.AA.2 and 12.AA.4 as printed, Exercise 12.AA.1, Proposition 12.D.2's first
part and Exercise 12.D.2, the existence claim of footnote 5, Exercises 12.C.8(d), 12.C.11(b),
12.C.14(c), 12.D.3(b), 12.E.7 and 12.F.1, Example 12.E.4, and MWG's tie rule in Appendix B.

This is a Lake project pinned to Lean and Mathlib `v4.34.0`. It imports (Lake `path`
requirements, no copies) MWG Chapter 10 (`MWGCompetitiveMarkets`: the Kuhn-Tucker tools
`foc_max_necessary`, `foc_max_iff`, `foc_continuousOn`, `foc_hasDerivWithin_interior`,
`foc_le_tangent_convex`) and MWG Chapter 9 (`MWGDynamicGames`: the multi-stage game with observed
actions `OSHist`, `OSProfile`, `osValue`, `osValue_succ`, `osValue_abs_le`, `osPlay_update`,
`osPath_length`, and the discounted one-shot deviation principle
`oneShot_deviation_principle_discounted_iff`), and through Chapter 9 MWG Chapters 7-8
(`NormalForm`, `IsNashEquilibrium`; from Chapter 8 the modules `Dominance`, `Existence`
(`nash_exists_of_quasiconcave`, Proposition 8.D.3) and `Cournot` (Exercise 8.B.5, re-exported as
Exercise 12.C.19)). See [third-party notices](THIRD_PARTY_NOTICES.md).

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Monopoly](MWGMarketPower/Monopoly.lean) | 16 | (12.B.2)-(12.B.4), footnotes 5-6 (correction 1), deadweight loss, flat demand, Example 12.B.1, perfect discrimination (12.B.5) |
| [MonopolyExercises](MWGMarketPower/MonopolyExercises.lean) | 16 | Exercises 12.B.1-12.B.4, 12.B.6, 12.B.7(a)-(b) |
| [MonopolyExercises2](MWGMarketPower/MonopolyExercises2.lean) | 11 | Exercises 12.B.7(c)-(d), 12.B.8-12.B.10 |
| [MonopolyExercises3](MWGMarketPower/MonopolyExercises3.lean) | 23 | Exercises 12.B.2(c) (deadweight loss in the elasticity), 12.B.5(a)-(b) (menus, resale) |
| [Bertrand](MWGMarketPower/Bertrand.lean) | 13 | Bertrand model, Proposition 12.C.1, Exercises 12.C.1 and 12.C.3 |
| [Cournot](MWGMarketPower/Cournot.lean) | 15 | (12.C.1)-(12.C.6), footnote 12, Proposition 12.C.2, competitive limit, Example 12.C.1, Exercises 12.C.6-12.C.7 |
| [LinearCity](MWGMarketPower/LinearCity.lean) | 9 | Example 12.C.2: demand (12.C.7)-(12.C.9), best responses (12.C.12), unique equilibrium |
| [RepeatedGames](MWGMarketPower/RepeatedGames.lean) | 21 | Appendix A model, values from recursions, Definition 12.AA.1, Lemma 12.AA.1 (corrected), (12.AA.2)-(12.AA.3) |
| [NashReversion](MWGMarketPower/NashReversion.lean) | 10 | Counterexample to Lemma 12.AA.1/Proposition 12.AA.2/Exercise 12.AA.1, Proposition 12.AA.2 (corrected), Proposition 12.AA.3, minimax payoffs |
| [Schedule](MWGMarketPower/Schedule.lean) | 5 | Exact average payoffs from pure action sequences (for the folk theorem) |
| [FolkTheorem](MWGMarketPower/FolkTheorem.lean) | 9 | Proposition 12.AA.5 (folk theorem), minimax version, Prisoner's Dilemma instance |
| [StickCarrot](MWGMarketPower/StickCarrot.lean) | 12 | Stick-and-carrot automaton, Propositions 12.AA.1 and 12.AA.4 under the envelope property (12.AA.6) |
| [StickCarrotInstances](MWGMarketPower/StickCarrotInstances.lean) | 10 | A game satisfying the hypotheses of Propositions 12.AA.1 and 12.AA.4 |
| [StickCarrotLiteral](MWGMarketPower/StickCarrotLiteral.lean) | 36 | Counterexample to the literal Propositions 12.AA.1 and 12.AA.4; corrected versions under a one-sided bound equivalent to (12.AA.6) |
| [CournotFolk](MWGMarketPower/CournotFolk.lean) | 5 | Example 12.AA.1 (average payoff zero), existence of the stick, linear instance |
| [RepeatedBertrand](MWGMarketPower/RepeatedBertrand.lean) | 9 | Section 12.D: Nash reversion, Proposition 12.D.1, Proposition 12.D.2 (first part, corrected), Exercise 12.D.2, counterexample |
| [RepeatedBertrand2](MWGMarketPower/RepeatedBertrand2.lean) | 5 | Proposition 12.D.2 (second part) |
| [RepeatedCournot](MWGMarketPower/RepeatedCournot.lean) | 5 | Exercise 12.D.3 (correction 9) |
| [MiscExercises](MWGMarketPower/MiscExercises.lean) | 4 | Exercises 12.C.9(c), 12.D.1 |
| [Entry](MWGMarketPower/Entry.lean) | 13 | Section 12.E: (12.E.1)-(12.E.8), Examples 12.E.1-12.E.3, Proposition 12.E.1, Exercise 12.E.2 |
| [Precommitment](MWGMarketPower/Precommitment.lean) | 7 | Section 12.G: (12.G.1)-(12.G.2), Figure 12.G.1, Example 12.G.1, Exercise 12.G.1 |
| [CournotBestResponse](MWGMarketPower/CournotBestResponse.lean) | 20 | Exercise 12.C.8(a)-(f): best responses, b(Q)+Q nondecreasing, symmetric equilibrium existence (corrected), multiplicity, uniqueness |
| [CompetitiveLimit](MWGMarketPower/CompetitiveLimit.lean) | 26 | Section 12.F: explicit two-stage entry SPNE, Proposition 12.F.1, footnote 29, Exercise 12.F.1 (counterexample and corrected version) |
| [CompetitiveLimitExercises](MWGMarketPower/CompetitiveLimitExercises.lean) | 12 | Exercises 12.F.2-12.F.4 |
| [EntryDeterrence](MWGMarketPower/EntryDeterrence.lean) | 51 | Appendix B: Dixit capacity game, Figures 12.BB.1-12.BB.8, blockaded/deterred/accommodated entry, Exercises 12.BB.1-12.BB.2 |
| [EntryDeterrenceExercises](MWGMarketPower/EntryDeterrenceExercises.lean) | 26 | Exercise 12.BB.3 (plant location in the linear city) |
| [CournotExistence](MWGMarketPower/CournotExistence.lean) | 7 | Small type p. 393: Cournot existence via Proposition 8.D.3, nonexistence example |
| [DifferentiatedProducts](MWGMarketPower/DifferentiatedProducts.lean) | 6 | Differentiated-products Bertrand (pp. 395-396), footnote 13 |
| [CapacityConstraints](MWGMarketPower/CapacityConstraints.lean) | 28 | Capacity constraints and rationing (pp. 394-395), Exercise 12.C.11 |
| [CityModels](MWGMarketPower/CityModels.lean) | 29 | Linear city with nonpurchase, small type p. 398, Exercises 12.C.13-12.C.14 |
| [CityExercises](MWGMarketPower/CityExercises.lean) | 9 | Exercise 12.C.15 (quadratic travel cost) |
| [CircularCity](MWGMarketPower/CircularCity.lean) | 12 | Circular city (p. 399), Exercise 12.C.16 |
| [RepresentativeConsumer](MWGMarketPower/RepresentativeConsumer.lean) | 12 | Representative consumer (12.C.13), monopolistic competition (p. 400) |
| [MixedBertrand](MWGMarketPower/MixedBertrand.lean) | 27 | Exercise 12.C.2: (c, c) is the unique mixed-strategy equilibrium |
| [BertrandCosts](MWGMarketPower/BertrandCosts.lean) | 21 | Exercise 12.C.4(a)-(b): Bertrand with different costs, continuous and grid prices |
| [UnitBids](MWGMarketPower/UnitBids.lean) | 13 | Exercise 12.C.5: bidding for units |
| [CournotCosts](MWGMarketPower/CournotCosts.lean) | 21 | Exercises 12.C.9(a)-(b), 12.C.10, 12.C.19 (alias of Exercise 8.B.5), 12.C.20 |
| [Stackelberg](MWGMarketPower/Stackelberg.lean) | 16 | Exercises 12.C.12 and 12.C.18(a) |
| [LinearCityCosts](MWGMarketPower/LinearCityCosts.lean) | 5 | Exercise 12.C.17: linear city with c1 <= c2, all cases |
| [FiniteRepeatedBertrand](MWGMarketPower/FiniteRepeatedBertrand.lean) | 7 | Finitely repeated Bertrand: unique SPNE (p. 401) |
| [RepeatedBertrandExercises](MWGMarketPower/RepeatedBertrandExercises.lean) | 22 | Exercises 12.D.4-12.D.5 (cost changes, Rotemberg-Saloner) |
| [OneStageEntry](MWGMarketPower/OneStageEntry.lean) | 22 | One-stage entry (pp. 410-411), Example 12.E.4 (corrected), footnotes 24, 26-27 |
| [EntryExercises](MWGMarketPower/EntryExercises.lean) | 15 | Exercises 12.E.1, 12.E.3-12.E.7 |

From this directory, run:

```sh
export PATH="$HOME/.elan/bin:$PATH"
lake build
python3 -m unittest discover -s scripts -p 'test_*.py' -v
python3 scripts/verify.py
```
