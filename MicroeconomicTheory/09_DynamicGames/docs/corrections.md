# Corrections

Departures from the printed text of MWG Chapter 9, checked against the page images. Items 1
and 17 are printed claims that are false as stated (with corrected statements); item 21 reads a
misprint; the other items are implicit assumptions, encodings or precise statements of
open-ended exercises made explicit.

1. **Propositions 9.B.1 and 9.B.2: uniqueness needs no moves of nature.** The uniqueness clause
   ("if no player has the same payoffs at any two terminal nodes, there is a unique ...") fails
   when nature moves: distinct terminal payoffs do not prevent ties between lotteries. Example:
   one player chooses `L` (payoff `1`) or `R`, after which nature picks payoffs `0` or `2` with
   probability `1/2` each; payoffs at the three terminal nodes are distinct, `L` and `R` are both
   optimal, and both pure profiles are SPNE. `proposition_9_B_1` and `proposition_9_B_2` prove
   uniqueness under the additional hypothesis that nature does not move
   (`∀ k, G.player k ≠ none`), which is the setting of the chapter's examples. The counterexample
   is the game `natureGame`: `proposition_9_B_2_nature_counterexample` (two SPNE with different
   moves although payoffs at distinct terminal nodes are distinct) and
   `proposition_9_B_1_nature_counterexample` (no unique backward-induction profile).
2. **Mixed versus behaviour strategies.** MWG states the solution concepts for strategy profiles
   `σ` (mixed strategies). The formalization uses behaviour strategies throughout (`IsNashB`,
   `IsSPNE`, `IsWeakPBE`, `IsSequentialEq`), which is equivalent under perfect recall by Kuhn's
   theorem (Chapter 7, `kuhn_theorem`). For pure profiles, `IsNashB.isNashEquilibrium_pure`
   connects to the normal-form Nash equilibrium of Chapter 8.
3. **Propositions 9.C.1 and 9.C.2 assume perfect recall.** The proofs (and the decompositions
   of a deviation into first nodes of an information set) use perfect recall, which MWG does not
   state; `proposition_9_C_1` and `proposition_9_C_2` take `G.PerfectRecall` as a hypothesis.
4. **Sequential equilibrium: beliefs and nature.** `IsSequentialEq` includes that `μ` is a system
   of beliefs. This is automatic from consistency when nature's moves have full support; the
   results of Appendix B (`isSequentialEq_of_isEFTHP`, `exists_isSequentialEq`,
   `oneShot_consistent`) assume `NatureFullSupport` (Kreps and Wilson's standing assumption).
5. **Exercise 9.B.8 is proved for games with perfect recall and full-support moves of nature**
   (`exercise_9_B_8`), as a corollary of existence of sequential equilibrium. MWG states it for
   every finite game; the generalized backward-induction proof for games without perfect recall
   is not formalized.
6. **Exercise 9.B.4: two players.** "Zero-sum" is read as a two-player game with
   `u₂ = −u₁` (`exercise_9_B_4`). With three or more players and payoffs summing to zero the
   claim fails (a mover indifferent between `(0, 1, −1)` and `(0, −1, 1)` gives two SPNE with
   different payoffs): `zeroSum3Game`, `exercise_9_B_4_three_player_counterexample` (payoffs sum
   to zero at every node; both pure profiles are SPNE; player 2 gets `1` in one and `−1` in the
   other).
7. **Bargaining model.** Offers are amounts `y ∈ [0, v]` given to the responder; strategies are
   defined at every history and subgame perfection is required at every history of feasible
   offers within the horizon (`BargainingGame.IsSPNE`). With `δ₁ = δ₂ = δ` the SPNE is unique on
   these histories (`example_9_AA_2`); the responder's acceptance at indifference is forced, as
   MWG's footnote 16 explains for the finite game.
8. **Proposition 9.B.4: a history-based model.** The successive play of `Γ¹_N, …, Γᵀ_N` is
   modelled directly by its histories (`RHist`, the lists of pure profiles played so far), with
   behaviour strategies assigning a mixed strategy of `Γⁿ_N` to every history of length `n`,
   payoffs `rval` summed over periods, and subgame perfection `IsRSPNE` required at every
   history (every history starts a subgame of `Γ_E`). It is not built as a Chapter 7
   `ExtensiveForm` tree, and no bridge to such a tree is proved. Periods are numbered from `0`.
   The statement is proved as printed, including uniqueness (`proposition_9_B_4`).
9. **Exercise 9.B.5: the sequential game by its backward-induction characterisation.** Game (b)
   (player 1 moves first, player 2 observes `m₁`) is not built as a Chapter 7 `ExtensiveForm`.
   Its pure strategy profiles are pairs `(m₁, s₂)` with `s₂ : M₁ → M₂`; an SPNE is a profile in
   which `s₂ m₁'` is a best reply of player 2 after every `m₁'` and `m₁` is a best reply of
   player 1 against `s₂` (`IsMaskinSPNE`; the subgames of (b) are the whole game and the
   subgames after each `m₁'`, so this is the backward-induction characterisation of
   Proposition 9.B.2 / `isSPNE_iff_oneShotOptimal`). A Nash equilibrium of (b) only requires no
   profitable deviation in the normal form (`IsMaskinNash`), i.e. player 2's reply is optimal
   on the path only. Only pure SPNE are considered in (c) and (d). Parts (c)-(e) are true as
   printed (`exercise_9_B_5c`, `exercise_9_B_5d`, `exercise_9_B_5d_nash`, `exercise_9_B_5e_ties`,
   `exercise_9_B_5e_mixed`).
10. **Exercise 9.B.9: history model, pure strategies.** The twice-played game uses the
   history model of item 8 with `T = 2`. A pure strategy profile assigns a pure profile to
   every history (`rpure p`); it is an SPNE if no player gains by any deviation in behaviour
   strategies after any history (`IsRSPNE`). Actions `aₖ`, `bₖ` are numbered `k − 1`.
11. **Exercise 9.B.10: what is proved.** The book asks for "the SPNEs" for `x ≥ 0` and `x < 0`.
   Proved: (i) for every `x`, the complete set of pure strategy SPNE
   (`exercise_9_B_10_pure`): ((in, accommodate, `U`), (accommodate, `ℓ`)) always, and
   ((in, accommodate, `D`), (accommodate, `r`)) exactly when `x ≥ 1`. The relevant threshold for
   pure SPNE is `x = 1`, not `x = 0`: for `0 ≤ x < 1`, `(D, r)` is an equilibrium of the
   coordination game, but with `(x, 3)` after (accommodate, accommodate) the post-entry game has
   no pure equilibrium (E prefers to fight an accommodating I). (ii) For `x < 0` the SPNE is
   unique among all behaviour profiles (`exercise_9_B_10_neg`). (iii) For `x ≥ 0` mixed
   equilibria matter: for `x = 3` the mixed coordination equilibrium (`U` with probability
   `3/4`, `ℓ` with probability `1/2`) is part of a further SPNE in which E enters, with payoff
   `3/2` (`exercise_9_B_10_mixed`). The complete set of mixed SPNE for `x ≥ 0` (which also
   involves mixed equilibria of the post-entry game; by an unformalized computation, when the
   coordination game ends in `(D, r)` with `0 ≤ x < 1`, E enters iff `x > 2/3`) is not formalized.
12. **Exercise 9.B.14: model and assumptions.** E's entry decision (cost `K`, paid at time 0,
   undiscounted) is followed by production periods `t = 0, 1, 2` with payoffs discounted by
   `δ^t`; in each period E first stays or exits, then I fights or accommodates; once out, E earns
   `0` and I earns `x` in each remaining period. In (b) a fight ends the game (E is forced out,
   I earns `x` in the remaining periods). The discount factor is assumed positive (`0 < δ`),
   which MWG leaves implicit; `δ ≤ 1` is not needed. Only parts of (A.1)-(A.3) are used:
   (a) needs `z > y` and (A.3); (b) needs `z > y` and (A.2). The parenthetical "(unique)" in
   (b) fails at `K = 1`, where E is indifferent about entry and both the entering and the
   non-entering profile are SPNE (`exercise_9_B_14b`, last conjunct); the post-entry strategies
   are unique for every `K`. Answer to (b): E enters iff `K < 1`, stays in period 0, exits in
   period 1 (and would stay in period 2); I accommodates in periods 0 and 2 and fights in
   period 1. Uniqueness is among all behaviour profiles (`eq_dirac_of_strict_bi`), which needs
   only strict preferences along the backward-induction solution, not Proposition 9.B.2's
   no-ties condition (which can fail here, e.g. at `δ = 1`).
13. **Exercise 9.D.1: formulation.** Iterated deletion of weakly dominated strategies is
   formalized for any normal form (`IsWDominatedIn`, `WDDeletionStep`; Chapter 8 has it only for
   two-player tables): one step may remove several strategies of several players, each weakly
   dominated within the current sets, as in Chapter 8's `SDStep`. The game is the normal form of
   Chapter 7's `toNormalForm` (non-reduced: strategies specify moves at nodes they exclude).
   "Same outcome" is: the same path from the initial node (`OnPath`) and the same payoffs for
   every player. The deletion order processes decision nodes by decreasing length and removes
   strategies that deviate from backward induction at a node they do not exclude by their own
   moves; strategies that differ from the SPNE only at nodes they exclude survive (they are
   payoff-equivalent duplicates and cannot be removed by weak dominance). The stronger remark
   that any order of deletion works (Moulin, 1981) is not formalized.
14. **Exercise 9.B.7: model.** The game of Example 9.AA.1 (pure strategies at every history of
   rejected offers, as in `MWGDynamicGames/Bargaining.lean`) with `δ = 1` and an offer cost
   `c ∈ (0, v)`: in every period the proposer must make an offer (as in Example 9.AA.1; if she
   could decline to offer, she would be indifferent with two periods left and uniqueness would
   fail; this remark is not formalized) and pays `c` for it, accepted or not. A player's payoff is her share of the agreement
   (or `0`) minus her total offer costs; payoffs are in `WithBot ℝ` so that the same model
   (`OfferCostGame`, horizon `T : ℕ∞`) covers Exercise 9.B.13. The printed claim of a unique
   SPNE is true (`exercise_9_B_7`), with the responder accepting at indifference (MWG's
   footnote 16 argument). Answer: with `m` periods left the proposer offers `W (m − 1)` where
   `W k = v − c` (odd `k`) or `0` (even `k`), so player 1 gets `v − c` and player 2 `0` when `T`
   is odd, and `0` and `v − c` when `T` is even; as `T → ∞` the outcome alternates and has no
   limit (`exercise_9_B_7_limit`), unlike the discounted game.
15. **Exercise 9.B.13: what is proved.** The book asks for "the subgame perfect Nash equilibria"
   of the infinite-horizon game with offer costs. Perpetual disagreement means infinitely many
   offers and payoff `⊥` (`−∞`). Proved: every SPNE gives payoffs `a, b ≥ 0` with
   `a + b ≤ v − c` in every subgame (`spne_bounds`); every split `(a, v − c − a)` with
   `a ∈ [0, v − c]` is the payoff of a stationary SPNE with immediate agreement
   (`splitProfile_isSPNE`), so the SPNE is far from unique and each player's set of SPNE payoffs
   is exactly `[0, v − c]` (`exercise_9_B_13_payoffs`); if `v < 2c` agreement is immediate in
   every SPNE, and if `v ≥ 2c` there is an SPNE with the first offer rejected (payoffs
   `(v − 2c, 0)`, `delayProfile_isSPNE`). Not formalized: the complete set of SPNE payoff pairs
   (with delays), and mixed strategies.
16. **Exercise 9.B.11: model.** An infinite-horizon game with pure strategies: a firm's move at
   date `t` may depend on the date and on the rival's status, "in" or "exited at the start of
   period `u < t`" (`AttritionProfile`); this is the full history of moves. If the rival exits at
   the start of period `u` and the firm stays, the firm is a monopolist in period `u`. A firm
   that never exits has payoff `⊥` (its profits tend to `−∞`). Subgame perfection is imposed at
   every node (both in at `t`; alone at `t` after the rival's exit at `u`). The truncation
   argument is proved in the model, not assumed: from date 26 on staying is strictly dominated
   for both firms (`monopoly_spne`, `exercise_9_B_11_unique`), and backward induction covers
   dates 25 down to 0. The SPNE is unique (among pure-strategy profiles; mixed strategies are
   not considered); in it A exits at the start of period 11, after which B is a monopolist until
   it exits at the start of period 26; A earns `605` and B `285.5`.
17. **Exercise 9.C.7(c): the weak PBE is unique only for `1/3 < p < 2/3`.** The book asks to
   "show that there is a unique weak perfect Bayesian equilibrium". True for pure strategies:
   for every `p ∈ (0, 1)`, `(T; U after both signals)` with beliefs on `T` is a weak PBE
   (`exercise_9_C_7c`) and the only weak PBE in which player 1 plays a pure strategy
   (`exercise_9_C_7c_pure_unique`). With behaviour (mixed) strategies, which Definition 9.C.3
   allows, it is false for `p ≥ 2/3` and for `p ≤ 1/3`: player 1's gain from `T` over `B` is
   `1 + 3 (qT − qB)(2p − 1)` (`qB`, `qT`: player 2's probabilities of `D` after the signals),
   which can vanish when `|2p − 1| ≥ 1/3`. Counterexamples: for `2/3 ≤ p < 1`, player 1 plays
   `T` with probability `p`, player 2 plays `D` with probability `1/(3(2p − 1))` after signal `B`
   (belief `1/2`) and `U` after signal `T` (`exercise_9_C_7c_mixed_high`); for `0 < p ≤ 1/3`
   the mirror image (`exercise_9_C_7c_mixed_low`). Corrected statement: the weak PBE is unique
   iff `1/3 < p < 2/3` (`exercise_9_C_7c_unique`, `exercise_9_C_7c_unique_iff`). Model: nature
   moves after player 1 and draws the signal (information sets `1`, `2` of nature, `3`, `4` of
   player 2), `bagC`.
18. **Exercise 9.C.3: model.** A direct model of the pure strategies of the two-period game
   (`SBProfile`, `IsSBWeakPBE`): the buyer's period-1 rule at every price, the seller's
   period-2 price and belief after every rejected price. The period-2 buyer rule (accept iff
   `q ≤ v`) is built in: it is the only sequentially rational move given that she accepts when
   indifferent (`sb_period2`). The seller's optimality at her first information set is against
   every change of her whole strategy (first price and the second price after it), with the
   prior as belief (Definition 9.C.2). Prices are arbitrary reals.
19. **Exercise 9.C.3(b): reduced model, `v̲ = 0`, `v̄ = 1`.** The buyer's sequential rationality
   is proved to give a cutoff rule at every price for every expected second price
   (`exercise_9_C_3b_cutoff`); the uniform case is then stated in reduced form
   (`IsSBUWeakPBE`): the seller's strategy is the first price and the second price `r p` after
   each rejected `p`, the buyer uses the cutoff, the uniform prior enters through its
   distribution function (mass of `[k, 1]` is `1 − k`), Bayes' posterior after rejection of a
   cutoff `k > 0` is uniform on `[0, k)` (`sbURev`), and an off-path second price may be any
   `r ∈ [0, 1]` (each is optimal for the belief concentrated on `v = r`,
   `sb_point_mass_opt`). The values are normalised to `[0, 1]` (rescaling all money amounts
   covers any `[0, v̄]`); the case `v̲ > 0` (where the second-period price can be the corner
   `v̲`) is treated in item 25. Result: the standard answer (linear cutoff `2p/(2 − δ)`, first
   price `(2 − δ)²/(2 (4 − 3δ))`) is a weak PBE and the unique weak PBE with consistent beliefs
   (`exercise_9_C_3b`), but weak PBE are not unique: off-path beliefs of the seller after her own
   deviations can support other first prices (`exercise_9_C_3b_not_unique`). For two types
   (part (a)) the weak PBE outcome is determined by the three benchmarks
   (`sb_weakPBE_outcome`).
20. **Exercise 9.C.4: model and prior.** The prior is a probability measure `μ` on `ℝ`
   concentrated on `[0, 1]`; parts (a)-(b) assume it has no atoms (`NullSingletonClass μ`), which
   covers the book's density `f` (Mathlib's `nullSingletonClass_withDensity`); part (c) needs no
   such assumption. D's information sets are singletons and P moves once, so a weak PBE of (a)
   is D best responding everywhere plus P's optimality (`IsSetWeakPBE`; D may break ties either
   way, which matters only on a null set). `π` is written `dmg` (the identifier `π` is
   reserved in this project). Part (b) is answered by monotone comparative statics valid for
   every atomless prior (trial probability and P's payoff); the direction of the settlement
   offer itself is not determined without further assumptions on the prior and is not
   formalized.
21. **Exercise 9.C.4(c): "Ms. D" read as "Ms. P".** The book says "allow Ms. D, after having her
   offer rejected, to decide not to go to court"; offers are made by Ms. P, so the agent who may
   drop the case is Ms. P (`SetCProfile.court`). Results: with `E[λ] π < c_p` no weak PBE has
   trials (`exercise_9_C_4c_no_trial`: the rejecting types are the low ones, so the posterior
   mean after a rejection is at most `E[λ]`); the no-settlement profile is a weak PBE iff
   `E[λ] π ≤ c_p` (`exercise_9_C_4c_drop`); when `E[λ] π ≤ c_p ≤ π` every offer in `(0, c_d]`
   accepted by all types is a weak PBE (`exercise_9_C_4c_settle`). Effects of changes: a higher
   `c_p` or a lower `π` enlarges the region `E[λ] π < c_p` where court is not credible. The
   complete set of weak PBE of (c) is not characterised.
22. **Exercise 9.C.5: model and scope.** P's offer is a function of her type; D's belief after
   each offer is a probability measure on `[0, 1]`; Bayes' rule applies to offers made with
   positive prior probability (`IsSet5WeakPBE`). Proved: the structure of every weak PBE
   (`exercise_9_C_5`), existence for every prior (`exercise_9_C_5_semi`), and the pooling
   equilibria (`exercise_9_C_5_pooling`, `exercise_9_C_5_passive`). Partial-pooling equilibria
   with a settlement amount above `c_d` (which require `s ≤ E[λ | settle] π + c_d`) are not
   characterised.
23. **Exercise 9.C.6: reading of "sequential equilibrium".** Definition 9.C.4 is stated for
   finite games; these games have a continuum of moves (prices, offers) or types. It is read
   through its consequence for these games, structural consistency: after every move of an
   uninformed player that some types of the informed player respond to by rejecting with
   positive probability, the uninformed player's belief is the prior conditioned on those types
   (the uninformed player's own trembles do not depend on the type, so they cancel in Bayes'
   rule; `sbPost_tendsto` proves the limit statement for two types). Definitions:
   `IsSBConsistent` (9.C.3(a)), `IsSBUConsistent` (9.C.3(b)), `IsSetCConsistent` (9.C.4(c)).
   Results: 9.C.3(a) has no pure sequential equilibrium when `λ vH > vL`
   (`exercise_9_C_6_two_types_none`; mixed strategies would be needed after first prices in
   `(p̂, vH]`) and otherwise exactly the weak PBE outcomes (i)-(ii)
   (`exercise_9_C_6_two_types`); 9.C.3(b) has a unique one (`exercise_9_C_3b`); in 9.C.4(a)
   the only beliefs are at singleton information sets, so sequential equilibria are the weak PBE
   of `exercise_9_C_4a`; in 9.C.4(c) the multiple weak PBE above are consistent
   (`exercise_9_C_6_settlement`); in 9.C.5 the passive-belief pooling equilibrium is consistent
   (`exercise_9_C_5_passive`), and a full characterisation (with type-dependent trembles over a
   continuum of types) is not formalized.
24. **Footnote 15: extensive form trembling-hand perfection.** Proved through a sufficient
   condition (`isEFTHP_pureMoves_of`, games without absent-mindedness): a pure profile is EFTHP
   if some totally mixed behaviour profiles converging to it make every agent's sure move a best
   reply. The trembles used (`ε = 1/(n + 5)`; E plays the entry strategy favoured by I's belief
   with probability `ε` and the other with `ε²`, each agent of I its other action with `ε`) need
   `ε ≤ 1/5` for Figure 9.D.2 (Out gives `−10ε`, the small niche `−1 − 5ε`); the footnote's claim
   holds as stated (`footnote_15_D_1a_EFTHP`, `footnote_15_D_1b_EFTHP`, `footnote_15_D_2_EFTHP`).
25. **Exercise 9.C.3(b) with `v̲ > 0`: normalisation and answer.** Payoffs are multiplied by
   `v̄ − v̲` and period-2 revenues by `k − v̲` (positive constants; no comparison changes); the
   reduced model is otherwise that of item 19 (`isSBGWeakPBE_zero_one_iff` recovers it at
   `v̲ = 0`, `v̄ = 1`). The book's question has a three-case answer
   (`exercise_9_C_3b_general`): when `v̄ ≤ 2v̲` the seller sells to every type at `v̲` at once;
   otherwise the first price is `(2 − δ)² v̄/(2 (4 − 3δ))` (interior second price `k*/2`) when
   `G_I ≥ G_C`, and `(1 − δ) v̄/2 + δ v̲` with the corner second price `v̲` (cutoff `v̄/2`) when
   `G_C ≥ G_I`, where `4 (4 − 3δ)(G_I − G_C) = δ (4 (4 − 3δ)(v̲² − v̲ v̄) + (3 − 2δ) v̄²)`
   (`sbgGI_sub_sbgGC`); at equality both prices are equilibrium prices, so the consistent weak
   PBE is unique except on that boundary. In terms of `v̲/v̄` the interior case holds iff
   `v̲/v̄ ≤ (1 − √((1 − δ)/(4 − 3δ)))/2` (a root of the quadratic; the closed form is not
   formalized, the polynomial condition is). Instance with a corner: `v̄ = 1`, `δ = 1/2`,
   `v̲ = 3/10` (first price `2/5`, cutoff `1/2`, second price `3/10`).
26. **One-shot deviation principle: scope.** Stated for multi-stage games with observed actions,
   pure strategies, per-period payoffs depending on the history and the current action profile,
   uniformly bounded, and a common discount factor `δ ∈ [0, 1)` (`oneShot_deviation_principle_discounted`,
   `oneShot_deviation_principle_discounted_iff`). Behaviour strategies and moves of nature are not covered.
   The bargaining game's bound `value_le_of_bound` is not re-derived from it (the bargaining
   model has a continuum of offers and a horizon `T ≤ ⊤`); the concrete instance is grim
   trigger in the repeated prisoners' dilemma (`grim_trigger_spe_iff`).
27. **Exercise 9.C.6 for 9.C.5: finite types only.** `signal_belief_consistent` proves that with
   finitely many types of full support, every belief after an off-path move of the informed
   player is a limit of Bayes posteriors under type-dependent trembles; the continuum-of-types
   model of `Informed.lean` has no formal notion of consistency, so the full characterisation of
   its sequential equilibria remains OPEN (see the source map).
