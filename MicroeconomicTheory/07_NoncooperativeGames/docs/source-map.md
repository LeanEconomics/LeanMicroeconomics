# Source map

Mas-Colell, Whinston and Green, *Microeconomic Theory*, Chapter 7, "Basic Elements of
Noncooperative Games", pp. 219-234 (text pp. 219-233, exercises pp. 233-234). No
Mathematical Appendix section is assigned to this chapter. Printed pages; Lean names relative
to `MWG.NoncooperativeGames` (dot-notation names live in `ExtensiveForm`, `NormalForm` or
`GameTree`). Every definition, numbered example, precise claim of the text, footnote with
mathematical content and exercise subpart is listed, with verbal items marked as such.
Statements were checked against the page images. Departures are numbered as in
[corrections](corrections.md). No dependency module is imported (Mathlib only). The Prisoner's
Dilemma does not appear in Chapter 7 (it is introduced in Chapter 8).

Encoding conventions: players `Fin 2` with `0` = player 1; Matching Pennies actions `0` = H,
`1` = T; histories list the most recent action first.

## Section 7.A-7.B: what a game is

| Source | Claim | Lean |
| --- | --- | --- |
| Section 7.A, p. 219 | Overview of the chapter | Verbal |
| Section 7.B, items (i)-(iv), pp. 219-220 | Players, rules, outcomes, payoffs; payoffs of expected-utility form | Verbal; formal counterparts `ExtensiveForm`, `NormalForm`, `NormalForm.mixedPayoff` |
| Example 7.B.1, p. 220 | Matching Pennies | `mpPay`, `matchingPennies` |
| Example 7.B.1, p. 221 | Best action depends on the opponent's | `example_7_B_1_best_action` |
| Section 7.B, p. 221 | Zero-sum games; Matching Pennies and Tick-Tack-Toe are zero-sum | `NormalForm.IsZeroSum`, `example_7_B_1_zero_sum`, `example_7_B_1_isZeroSum`, `example_7_B_2_zero_sum` |
| Example 7.B.2, Figure 7.B.1, p. 220 | Tick-Tack-Toe: players, board, alternating moves, outcomes | `tttLines`, `tttMarks`, `tttWins`, `tttPayoff`, `tickTackToe`, `example_7_B_2_alternate`, `ttt_not_both_win` |
| Example 7.B.3, p. 221 | Meeting in New York | `meetingNY` |
| Example 7.B.3, p. 221 | Interests completely aligned | `example_7_B_3_aligned`, `example_7_B_3_not_zeroSum` |
| Example 7.B.3, p. 221 | Optimal action depends on beliefs about the other | `example_7_B_3_best_reply`, `example_7_B_3_two_places` |

## Section 7.C: the extensive form

| Source | Claim | Lean |
| --- | --- | --- |
| Example 7.C.1, Figure 7.C.1, pp. 221-222 | Matching Pennies Version B and its tree | `matchingPenniesB`, `matchingPenniesB_terminals` |
| Example 7.C.1, p. 222 | Unique path from the root to each node (tree structure) | `suffix_unique`, `extensive_initial_node`, `GameTree.hist_injective` |
| Example 7.C.2, Figure 7.C.2, pp. 222-223 | Tick-Tack-Toe in extensive form; nodes record how a position was reached | `tickTackToe`, `example_7_C_2_paths` |
| Section 7.C, p. 222 | Version B and Tick-Tack-Toe have perfect information | `example_7_C_1`, `example_7_C_2_perfectInformation` |
| Example 7.C.3, Figure 7.C.3, pp. 223-224 | Version C; one information set for player 2; same actions at its nodes | `matchingPenniesC`, `example_7_C_3` |
| Section 7.C, p. 224 | Information sets list a player's distinguishable circumstances (two for player 2 in Version B, one in Version C) | `example_7_D_1`, `example_7_D_2` (strategy counts) and verbal |
| Section 7.C, p. 224 | Same choices at all nodes of an information set | field `avail_spec`, `choices_eq_of_info_eq` |
| Footnote 1, p. 224 | Perfect recall, conditions (i) and (ii) | `NoAbsentMindedness`, `RecallFor`, `PerfectRecall`, `info_ne_of_cons_suffix` |
| Figure 7.C.4(a), p. 225 | Player 2 forgets player 1's move: no perfect recall | `figure7C4a`, `figure_7_C_4a` |
| Figure 7.C.4(b), p. 225 | Player 1 forgets her own move: no perfect recall | `figure7C4b`, `figure_7_C_4b` |
| Section 7.C, p. 224 | All games in the book have perfect recall | Verbal (a standing assumption) |
| Example 7.C.4, p. 225 | Standard Matching Pennies drawn with Figure 7.C.3, or with the players reversed | `matchingPenniesC`, `matchingPenniesReversed`, `exercise_7_D_2`, `example_7_C_4` |
| Definition 7.C.1, p. 226 | Perfect and imperfect information | `PerfectInformation`; perfect information implies perfect recall: `noAbsentMindedness_of_perfectInformation`, `recallFor_of_perfectInformation`, `perfectRecall_of_perfectInformation` |
| Example 7.C.5, Figure 7.C.5, p. 226 | Version D: a move of nature with probabilities `1/2` | `matchingPenniesD`, `example_7_C_5`, `example_7_C_5_random_outcome` |
| Section 7.C, p. 226 | Common knowledge of the structure | Verbal |
| Items (i)-(vii), p. 227 | Formal extensive form `Γ_E` | `ExtensiveForm` (fields), `IsDecision`, `IsTerminal`, `IsPred`, `decisionNodes`, `terminals`, `successors`, `mem_successors`, `isDecision_or_isTerminal` |
| Item (ii), p. 227 | Tree: one initial node, predecessors and successors disjoint | `extensive_initial_node`, `extensive_tree_disjoint`, `mem_of_suffix`, `exists_cons_suffix`; abstract trees `GameTree`, `GameTree.exists_iterate_eq_root`, `GameTree.iterate_eq_root_unique` (correction 3) |
| Item (iii), p. 227 | Distinct successors have distinct actions; choice sets `c(x)` | `extensive_successor_actions_distinct`, `GameTree.act_inj`, `mem_avail_of_cons_mem`, `cons_mem_of_mem_avail` (correction 2) |
| Item (iv), p. 227 | Information sets partition the decision nodes; `C(H)` | `infoSet`, `infoSet_partition`, `avail_nonempty` (correction 1) |
| Items (v)-(vii), p. 227 | Player function, nature's probabilities, Bernoulli payoffs | fields `player`, `natureProb`, `nature_nonneg`, `nature_zero`, `nature_sum`, `payoff` |
| Section 7.C, p. 227 | Abstract trees and history trees are interchangeable | `GameTree.hist`, `hist_root`, `hist_of_pred`, `hist_eq_nil_iff`, `hist_injective`, `historyNodes`, `nil_mem_historyNodes`, `historyNodes_tail_mem`, `cons_mem_historyNodes_iff`, `toGameTree`, `gameTree_of_history` |
| Footnote 2, p. 226 | Game form versus game | Verbal (items (i)-(vi) are the fields other than `payoff`) |
| Small type, pp. 227-228 | Three implicit finiteness assumptions; infinite games | Verbal (finite games only, as MWG assume in Part II) |

## Section 7.D: strategies and the normal form

| Source | Claim | Lean |
| --- | --- | --- |
| Definition 7.D.1, p. 228 | Pure strategy `s_i : ℋ_i → 𝒜`, `s_i(H) ∈ C(H)` | `InfoSetOf`, `PureStrategy`, `pureOfFun`, `pureOfFun_apply` |
| Section 7.D, pp. 228-229 | A strategy is a complete contingent plan | Verbal (the type `PureStrategy` assigns an action at every information set) |
| Example 7.D.1, p. 229 | Version B: two strategies for player 1, four for player 2 | `example_7_D_1`, `mpBResponse`, `mpBProfile` |
| Example 7.D.2, p. 229 | Version C: two strategies each | `example_7_D_2` |
| Section 7.D, p. 229 | Profiles `s = (s_i, s_{-i})` | Functions `(i : I) → PureStrategy i`; `Function.update` |
| Section 7.D, p. 229 | A profile induces a distribution over terminal nodes (a single path without nature) | `reach`, `assemble`, `pureBeh`, `pureProfile`, `pureProfile_apply`, `sum_reach_terminals_below`, `sum_reach_terminals`, `pureProfile_outcome_distribution`, `reach_pureProfile_zero_or_one`, `pureProfile_outcome_degenerate` |
| Definition 7.D.2, p. 230 | Normal form `Γ_N = [I, {S_i}, {u_i}]` | `NormalForm`, `toNormalForm`, `toNormalForm_payoff_of_reach`, `toNormalForm_payoff_eq_of_reach` |
| Example 7.D.3, Figure 7.D.1, p. 230 | Normal form of Version B | `matchingPenniesB_payoff`, `example_7_D_3` |
| Exercise 7.D.2 (in text), p. 230 | Normal forms of Version C and of standard Matching Pennies | `exercise_7_D_2`, `example_7_C_4` |
| Section 7.D, p. 230 | Players choose strategies simultaneously (referee) | Verbal |
| Small type, pp. 230-231 | Unique normal form of an extensive form | `toNormalForm` is a function of the extensive form |
| Small type, p. 231, Figure 7.D.2 | Different extensive forms with the same normal form | `figure_7_D_2`, `figure_7_D_2_payoff`, `figure_7_D_2_same_normal_form` |
| Small type, p. 231 | Normal form and dynamic games; simultaneous-move games | Verbal |

## Section 7.E: randomized choices

| Source | Claim | Lean |
| --- | --- | --- |
| Definition 7.E.1, p. 232 | Mixed strategy | `IsMixedStrategy` |
| Section 7.E, p. 232 | Mixed extension `Δ(S_i)` as a simplex in `ℝ^M` | `mixedExtension`, `mixedExtension_fin` |
| Section 7.E, p. 232 | Pure strategy as a degenerate mixed strategy | `pureMixed`, `isMixedStrategy_pureMixed`, `NormalForm.mixedPayoff_pure` |
| Section 7.E, p. 232 | `u_i(σ) = ∑_s σ₁(s₁)⋯σ_I(s_I) u_i(s)`, independent randomization | `NormalForm.mixedPayoff`, `NormalForm.sum_prod_mixed` |
| Section 7.E, p. 232 | Payoff of a mixed profile is expected utility over terminal nodes | `mixedOutcome`, `mixedOutcome_factor`, `mixedOutcome_distribution`, `mixedPayoff_toNormalForm` |
| Section 7.E, p. 232 | Mixed extension `Γ_N = [I, {Δ(S_i)}, {u_i}]` | `NormalForm.mixedExtensionGame`, `NormalForm.mixedExtensionGame_pure` |
| Small type, p. 232 | Mixed strategy as a plan contingent on a uniform private signal | `signalCut`, `mixedStrategy_signal`, `mixedStrategy_signal_pure` (correction 7) |
| Footnote 3, p. 232 | Correlated randomization deferred to Chapter 8 | Verbal |
| Definition 7.E.2, p. 233 | Behaviour strategy | `IsBehaviorStrategy`, `isBehaviorStrategy_pureBeh` (correction 4) |
| Section 7.E, p. 233 (Kuhn 1953) | Realization equivalence | `RealizationEquivalent`, `weight`, `weight_congr`, `reach_assemble_factor`, `reach_update_factor`, `realizationEquivalent_of_weight` (correction 6) |
| Section 7.E, p. 233 (Kuhn 1953) | Behaviour strategy has a realization-equivalent mixed strategy | `mixedOfBehavior`, `isMixedStrategy_mixedOfBehavior`, `mixedWeight_mixedOfBehavior`, `kuhn_behavior_to_mixed` (correction 5) |
| Section 7.E, p. 233 (Kuhn 1953) | Mixed strategy has a realization-equivalent behaviour strategy | `behaviorOfMixed`, `isBehaviorStrategy_behaviorOfMixed`, `mixedWeight_eq_weight_behaviorOfMixed`, `kuhn_mixed_to_behavior` (correction 5) |
| Section 7.E, p. 233 | The equivalence under perfect recall, against mixed or behaviour rivals | `kuhn_theorem`, `realizationEquivalent_mixed_rivals`, `kuhn_mixed_rivals` |
| Section 7.E, p. 233 | Analytical convenience; all randomized strategies called "mixed" | Verbal |
| Supporting lemmas | Weights of pure and mixed strategies | `Consistent`, `weight_pureBeh_of_consistent`, `weight_pureBeh_of_not_consistent`, `mixedWeight`, `consistent_iff_of_recall`, `weight_pureBeh_eq_of_recall`, `mixedWeight_eq_of_recall`, `PathAllows`, `pathFactor`, `weight_pureBeh_eq_prod` |

## Exercises

| Source | Claim | Lean |
| --- | --- | --- |
| Exercise 7.C.1, p. 233 | Tree of Meeting in New York with two places | `exercise7C1`, `exercise_7_C_1` (also its normal form; correction 9) |
| Exercise 7.D.1, p. 233 | `∏_n M_n` pure strategies | `card_pureStrategy`, `exercise_7_D_1` |
| Exercise 7.D.2, p. 233 | In text (see Section 7.D) | `exercise_7_D_2`, `example_7_C_4` |
| Exercise 7.E.1(a), p. 233 | Strategies in Figure 7.Ex.1: 12 for player 1, 2 for player 2 | `exercise7E1`, `exercise_7_E_1a` |
| Exercise 7.E.1(b), p. 233 | Behaviour to realization-equivalent mixed | `exercise7E1_perfectRecall`, `exercise_7_E_1b` |
| Exercise 7.E.1(c), p. 234 | Mixed to realization-equivalent behaviour | `exercise_7_E_1c`, `exercise_7_E_1c_mixed_rivals` |
| Exercise 7.E.1(d), p. 234 | Merged game: not perfect recall; (b) holds, (c) fails | `exercise7E1Merged`, `ex7E1Sigma`, `isMixedStrategy_ex7E1Sigma`, `exercise_7_E_1d` |
