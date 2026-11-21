# MWGDynamicGames

Formalization of Mas-Colell, Whinston and Green, *Microeconomic Theory*, Chapter 9, "Dynamic
Games", pp. 267-306: sequential rationality and backward induction (Zermelo's theorem,
Propositions 9.B.1-9.B.2), subgames and subgame perfection (Definitions 9.B.1-9.B.2), the
generalized backward-induction procedure (Proposition 9.B.3), beliefs, weak perfect Bayesian
and sequential equilibrium (Definitions 9.C.1-9.C.4, Propositions 9.C.1-9.C.2), forward
induction (9.D), finite and infinite horizon bargaining (Appendix A: unique SPNE, Stahl and
Rubinstein, also with different discount factors) and extensive form trembling-hand
perfection (Appendix B). The hard results are proved: the one-shot deviation principle on
finite trees and, for consistent assessments, with perfect recall; every extensive form
trembling-hand perfect equilibrium is a sequential equilibrium; existence of sequential
equilibrium and of subgame perfect equilibrium (Kreps-Wilson, Selten). The audit passed
**653 theorems and 953 declarations across 37 modules**. Coverage, including the items left
OPEN, is in the [source map](docs/source-map.md); departures from the printed text are in
[corrections](docs/corrections.md).

This is a Lake project pinned to Lean and Mathlib `v4.34.0`. It imports (Lake requirement, no
copies) MWG Chapter 8 (`MWGSimultaneousMoveGames`: `IsNashEquilibrium`, `IsTHP`,
`exercise_8_F_3`, `perturbedNash_eq_of_not_best`) and through it MWG Chapter 7
(`MWGNoncooperativeGames`: `ExtensiveForm`, `reach`, `assemble`, `IsBehaviorStrategy`,
`toNormalForm`, `mixedPayoff_toNormalForm`, `mixedOutcome_factor`,
`mixedWeight_mixedOfBehavior`, `matchingPenniesB`). See
[third-party notices](THIRD_PARTY_NOTICES.md).

Games are Chapter 7's `ExtensiveForm` (nodes are histories); a strategy profile is a
behaviour profile `F : I → H → A → ℝ` and `cont G f x i` is player `i`'s continuation payoff
from node `x`.

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Basic](MWGDynamicGames/Basic.lean) | 34 | Continuation payoffs and the backward-induction recursion, behaviour profiles, Nash equilibrium of `Γ_E`, Definitions 9.B.1-9.B.2, Exercise 9.B.2, the entry-node decomposition |
| [Zermelo](MWGDynamicGames/Zermelo.lean) | 19 | One-shot deviation principle (finite trees), backward induction, Propositions 9.B.1-9.B.2, Exercise 9.B.4 |
| [Generalized](MWGDynamicGames/Generalized.lean) | 8 | Reduced games, Proposition 9.B.3 |
| [Beliefs](MWGDynamicGames/Beliefs.lean) | 18 | Definitions 9.C.1-9.C.4, Propositions 9.C.1-9.C.2, SE ⇒ weak PBE |
| [Bargaining](MWGDynamicGames/Bargaining.lean) | 34 | The alternating-offer game, subgame perfection, Shaked-Sutton bounds, discounted one-stage deviation bound |
| [Rubinstein](MWGDynamicGames/Rubinstein.lean) | 18 | Examples 9.AA.1-9.AA.2, Exercise 9.B.12 |
| [AgentForm](MWGDynamicGames/AgentForm.lean) | 11 | Agent normal form, Definition 9.BB.1, existence of EFTHP |
| [OneShot](MWGDynamicGames/OneShot.lean) | 7 | One-shot deviation principle for consistent assessments |
| [Sequential](MWGDynamicGames/Sequential.lean) | 9 | EFTHP ⇒ SE (p. 300), existence of SE, Exercise 9.B.8 |
| [Entry](MWGDynamicGames/Entry.lean) | 15 | Example 9.B.1, Figures 9.B.1-9.B.2 |
| [EntryTwo](MWGDynamicGames/EntryTwo.lean) | 24 | Examples 9.C.1, 9.C.3, Exercise 9.C.2, Figure 9.D.1(a) |
| [EntrySim](MWGDynamicGames/EntrySim.lean) | 15 | Examples 9.B.3, 9.B.4, 9.C.5, Exercise 9.B.6, Figure 9.D.3 |
| [ThreePlayer](MWGDynamicGames/ThreePlayer.lean) | 10 | Example 9.B.2, Exercises 9.B.1, 9.B.3 |
| [Further](MWGDynamicGames/Further.lean) | 7 | Instances of Proposition 9.B.3, Exercise 9.B.4 and Appendix A; Bayes numbers p. 285; Figure 9.D.1(b); Exercise 9.B.5(b) |
| [Counterexamples](MWGDynamicGames/Counterexamples.lean) | 11 | Corrections 1 and 6: uniqueness in Propositions 9.B.1-9.B.2 fails with nature; three-player Exercise 9.B.4 |
| [Centipede](MWGDynamicGames/Centipede.lean) | 18 | Example 9.B.5, Figure 9.B.8: unique SPNE and its outcome |
| [JointVenture](MWGDynamicGames/JointVenture.lean) | 12 | Example 9.C.2: unique weak PBE, another SPNE |
| [NatureBeliefs](MWGDynamicGames/NatureBeliefs.lean) | 14 | Example 9.C.4: weak PBE with inconsistent beliefs, unique sequential equilibrium |
| [Trembling](MWGDynamicGames/Trembling.lean) | 16 | Figures 9.BB.1-9.BB.2: normal form vs extensive form THP, SE that is not EFTHP |
| [ForwardInduction](MWGDynamicGames/ForwardInduction.lean) | 8 | Figure 9.D.2 (equilibrium domination), footnote 15 (SE) |
| [Repeated](MWGDynamicGames/Repeated.lean) | 7 | Proposition 9.B.4 (history-based model), repeated Prisoner's Dilemma |
| [Maskin](MWGDynamicGames/Maskin.lean) | 10 | Exercise 9.B.5(c)-(e) |
| [TwicePlayed](MWGDynamicGames/TwicePlayed.lean) | 13 | Two-period backward induction, Exercise 9.B.9, footnote 10 |
| [DominanceBI](MWGDynamicGames/DominanceBI.lean) | 22 | Exercise 9.D.1: iterated weak dominance and backward induction |
| [EntryCoordination](MWGDynamicGames/EntryCoordination.lean) | 16 | Exercise 9.B.10 |
| [StrictBI](MWGDynamicGames/StrictBI.lean) | 4 | Uniqueness of SPNE from strict preferences on the backward-induction path |
| [EntryDeterrence](MWGDynamicGames/EntryDeterrence.lean) | 17 | Exercise 9.B.14(a)-(b) |
| [OfferCosts](MWGDynamicGames/OfferCosts.lean) | 54 | Bargaining with offer costs: Exercises 9.B.7, 9.B.13 |
| [Attrition](MWGDynamicGames/Attrition.lean) | 39 | Exercise 9.B.11: war of attrition in a declining market |
| [Bagwell](MWGDynamicGames/Bagwell.lean) | 46 | Exercise 9.C.7(a)-(c) |
| [SellerBuyer](MWGDynamicGames/SellerBuyer.lean) | 35 | Exercise 9.C.3(a)-(b) (`v̲ = 0`), 9.C.6 for 9.C.3 |
| [Settlement](MWGDynamicGames/Settlement.lean) | 23 | Exercise 9.C.4(a)-(c) |
| [Informed](MWGDynamicGames/Informed.lean) | 11 | Exercise 9.C.5, 9.C.6 for 9.C.4(c)-9.C.5 |
| [PerfectForward](MWGDynamicGames/PerfectForward.lean) | 7 | Sufficient condition for EFTHP; footnote 15 (EFTHP) |
| [SellerBuyerGeneral](MWGDynamicGames/SellerBuyerGeneral.lean) | 27 | Exercise 9.C.3(b) for `0 ≤ v̲ < v̄` |
| [OneShotDeviation](MWGDynamicGames/OneShotDeviation.lean) | 12 | One-shot deviation principle for discounted infinite-horizon games; grim trigger |
| [SignalBeliefs](MWGDynamicGames/SignalBeliefs.lean) | 2 | Consistency of off-path beliefs with finitely many types |

## Build and verify

From this chapter directory:

```sh
lake build
python3 -m unittest discover -s scripts -p 'test_*.py' -v
python3 scripts/verify.py
```

The verifier builds the library, recompiles all sources in a fresh file, and audits every
declaration's axioms (only `propext`, `Classical.choice` and `Quot.sound` are allowed).
