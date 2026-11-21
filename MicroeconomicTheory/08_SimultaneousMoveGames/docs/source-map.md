# Source map

Mas-Colell, Whinston and Green, *Microeconomic Theory*, Chapter 8, "Simultaneous-Move Games",
pp. 235-266 (text pp. 235-261, exercises pp. 262-266), with Appendix A of the chapter
(pp. 260-261) and Mathematical Appendix Section M.I, "Fixed Point Theorems" (pp. 952-953).
Printed pages; Lean names relative to `MWG.SimultaneousMoveGames`. Every definition, numbered
result and example, precise claim of the text, footnote with mathematical content and
exercise subpart is listed; verbal items are marked as such, and items not formalized are
marked OPEN with the reason. Statements were checked against the page images. Departures are
numbered as in [corrections](corrections.md).

Dependencies (Lake requirements, imported, not copied): `MWGNoncooperativeGames` (Chapter 7:
`NormalForm`, `mixedPayoff`, `mixedExtensionGame`, `IsMixedStrategy`, `pureMixed`,
`matchingPennies`); `MWGClassicalDemand` (Chapter 3, Appendix M.H: `UpperHemicontinuousMWG`,
`HasClosedGraph`, `CorrMapsInto`, `hasClosedGraph_of_isClosed`,
`uhc_iff_hasClosedGraph_of_isCompact`); `LeanEconomics` (pinned `04decca`:
`LeanEconomics.FixedPoint.brouwer`, `LeanEconomics.FixedPoint.kakutani`); `MWGProduction` (Chapter 5, Appendix M.M: `farkas`, `exists_pos_of_cone_inter_nonneg`, `coneOf`, `isClosed_coneOf`).

Encoding conventions. Normal forms are Chapter 7's `NormalForm I S`; a rivals' profile `s_{-i}`
is a full profile whose `i`-th coordinate is ignored, and `(s_i, s_{-i})` is
`Function.update s i s_i`. Mixed strategies are probability vectors `S_i → ℝ`; `u_i(σ)` is
`N.mixedPayoff σ i`. Payoff tables are `bimatrix u₁ u₂` with rows and columns numbered from `0`
in printed order (player 1 = `0`). Iterated deletion processes are finite chains
`Relation.ReflTransGen` of deletion steps from the full game.

## Section 8.A-8.B: dominant and dominated strategies

| Source | Claim | Lean |
| --- | --- | --- |
| Section 8.A, p. 235; p. 236 | Overview; notation `Γ_N`, `s_{-i}`, `S_{-i}` | Verbal; encoding above |
| Figure 8.B.1, pp. 236-237 | Prisoner's Dilemma: confess strictly dominant for both; (C, C) Nash; both prefer (DC, DC); one year gained, eight imposed | `pdU₁`, `pdU₂`, `figure_8_B_1_confess_dominant`, `figure_8_B_1_dilemma` |
| Definition 8.B.1, p. 237 | Strictly dominant strategy | `StrictlyDominant` |
| Definition 8.B.2, p. 237 | Strictly dominates, strictly dominated | `StrictlyDominates`, `StrictlyDominated`, `StrictlyDominates.trans` |
| Section 8.B, p. 237 | Restatement of 8.B.1 via 8.B.2 | `strictlyDominant_iff_dominates` |
| Example 8.B.1, Figure 8.B.2, p. 237 | No strictly dominant strategy; D dominated by M and U | `fig8B2U₁`, `fig8B2U₂`, `example_8_B_1` |
| Definition 8.B.3, p. 238 | Weakly dominates/dominated, weakly dominant | `WeaklyDominates`, `WeaklyDominated`, `WeaklyDominant`, `StrictlyDominates.weaklyDominates` |
| Example 8.B.2, Figure 8.B.3, p. 238 | U and M weakly dominated by D | `fig8B3U₁`, `fig8B3U₂`, `example_8_B_2` |
| Section 8.B, p. 238 | Weakly dominated strategies cannot be ruled out by rationality alone; caution | Verbal |
| Example 8.B.3, Figure 8.B.4, pp. 238-239 | DA's Brother: no dominance for prisoner 1; DC strictly dominated for prisoner 2; iterated deletion gives (C, C) | `daU₁`, `daU₂`, `example_8_B_3_dominance`, `example_8_B_3` |
| Section 8.B, pp. 239-240 | Iterated deletion of strictly dominated strategies; several at once | `SDominatedIn`, `SDStep`, `SDTerminal`, `fullSets`, `sdChain_subset`, `sdStep_nonempty`, `sdChain_nonempty`, `sdChain_dominated_by_survivor`, `sdTerminal_subset_chain` |
| Section 8.B, pp. 239-240 | Order of deletion does not matter (see Exercise 8.B.4) | `exercise_8_B_4` (finite games; correction 1) |
| Small type, p. 240 | Iterated weak deletion depends on the order (Figure 8.B.3) | `RowWeaklyDominatedIn`, `ColWeaklyDominatedIn`, `WDStep2`, `WDTerminal2`, `wdTerminal2_singleton`, `figure_8_B_3_order_dependence` |
| Definition 8.B.4, p. 240 | Strict domination in `[I, {Δ(S_i)}, {u_i}]`; strictly dominant mixed strategy | `MixedStrictlyDominates`, `MixedStrictlyDominated`, `MixedStrictlyDominant` |
| Small type, p. 240 | Test against pure `s_{-i}`; the expansion formula | `mixedStrictlyDominates_iff_pure`, `mixedPayoff_update_eq_expect`, `mixedPayoff_lt_of_pure`, `mixedPayoff_le_of_pure`, `mixedPayoff_update`, `prod_update_eq` |
| Proposition 8.B.1, p. 241 | Pure strategy dominated iff some mixed strategy beats it against all `s_{-i}` | `proposition_8_B_1` |
| Small type, Figure 8.B.5, p. 241 | No pure strategy dominates M, but ½U + ½D does | `fig8B5U₁`, `fig8B5U₂`, `halfUD`, `figure_8_B_5` |
| Exercise 8.B.6, p. 241 (in text) | Mixed strategies using a dominated pure strategy are dominated | `exercise_8_B_6` (`mixedPayoff_shift`, `isMixedStrategy_shift`) |
| Small type, p. 242 | With M paying 6, U and D undominated but ½U + ½D dominated by M | `fig8B5U₁'`, `figure_8_B_5_variant` |
| Small type, p. 242 | Two-stage procedure for iterated mixed dominance | `MSDStep` (stage-wise test of Proposition 8.B.1 over remaining pure strategies), `sdStep_msdStep`; the second stage is Definition 8.B.4 applied to `Δ(S_i^∞)` (listed) |

## Section 8.C: rationalizable strategies

| Source | Claim | Lean |
| --- | --- | --- |
| Definition 8.C.1, p. 242 | Best response; never a best response | `IsBestResponse`, `NeverBestResponse`, `isBestResponse_update` |
| Footnote 1, p. 243 | Optimal against an independent probabilistic conjecture ⇒ best response to the compound profile | `footnote_8_1` (`mixedPayoff_compound`) |
| Section 8.C, p. 243 | A strictly dominated strategy is never a best response | `neverBestResponse_of_mixedStrictlyDominated` |
| Section 8.C, p. 243 | Iterated removal of never-best responses | `BRToSome`, `ratStep`, `ratIter`, `NBRStep`, `NBRTerminal`, `nbrStep_ratStep` |
| Definition 8.C.2, p. 243 | Rationalizable strategies | `Rationalizable`, `Rationalizable.isMixedStrategy`, `subset_ratIter_of_bestResponseSet`, `rationalizable_of_bestResponseSet` |
| Section 8.C, p. 243 | Rationalizable ⊆ survivors of iterated strict dominance | `exists_ratIter_support_subset`, `rationalizable_support_subset`, `msd_dominated_lt`, `msdChain_of_sdChain` |
| Section 8.C, p. 243 | Order of removal does not matter (Exercise 8.C.2) | `exercise_8_C_2`, `nbrTerminal_eq_rationalizable`, `exists_ratIter_subset_of_chain`, `nbrChain_subset` |
| Example 8.C.1, Figure 8.C.1, p. 244 | b₄ dominated by ½b₁ + ½b₃; a₄ by a₂ after deleting b₄; a₁-a₃, b₁-b₃ rationalizable; a₄, b₄ not | `fig8C1U₁`, `fig8C1U₂`, `bernheim`, `halfB13`, `example_8_C_1_dominance`, `bernheimSet`, `example_8_C_1_rationalizable`, `bernheim_bestResponse_b4`, `example_8_C_1_not_rationalizable` |
| Example 8.C.1 and footnote 2, p. 244 | Chains of justification | Verbal (the best-response set `bernheimSet` is the chain) |
| Footnote 3, p. 245 | A rationalizable strategy exists when a Nash equilibrium does | `footnote_8_3` |
| Small type, p. 245 | Two players: not strictly dominated ⇒ best response (Figure 8.C.2) | `exercise_8_C_3`, `figure_8_C_2` |
| Small type, p. 245 | Two players: rationalizable = survivors of iterated strict dominance | False under Definition 8.C.2 read literally: `rationalizable_two_counterexample` (`ratGap`, `halfLR`, `ratGap_bestResponse`, `msdTerminal_full_of_bestResponse`; correction 9). True with footnote 1's probabilistic conjectures, both directions: `rationalizableConv_iff_two` (`RationalizableConv`, `BRToSomeConv`, `ratStepConv`, `ratIterConv`, `ratIterConv_subset`, `rationalizableConv_of_bestResponseSet`, `MSDTerminal`; ⊆: `exists_ratIterConv_support_subset`, `eq_zero_of_mem_convexHull`; ⊇: `rationalizableConv_of_msdTerminal_two`, `exists_belief_of_msdTerminal`, `exists_max_mem_of_msdChain`, `gordan_alternative` from Chapter 5's `farkas`) |
| Small type, p. 245 | With correlated randomizations the equivalence holds for any number of players | `bestResponse_correlated_of_not_dominated`, `correlated_iff_not_dominated` (`IsBelief`, `beliefPayoff`) |

## Section 8.D: Nash equilibrium

| Source | Claim | Lean |
| --- | --- | --- |
| Definition 8.D.1, p. 246 | Nash equilibrium | `IsNashEquilibrium`, `IsNashEquilibrium.not_strictlyDominated` |
| Example 8.D.1, Figure 8.D.1, p. 246 | (M, m) the only pure Nash equilibrium | `fig8D1U₁`, `fig8D1U₂`, `example_8_D_1` |
| Example 8.D.2, p. 246 | (a₂, b₂) the only pure Nash equilibrium of Figure 8.C.1 | `example_8_D_2` |
| Section 8.D, p. 247 | Every strategy in a Nash equilibrium is rationalizable | `rationalizable_of_isMixedNash` |
| Example 8.D.3, Figure 8.D.2, p. 247 | Meeting in New York: two pure equilibria | `meetNY`, `example_8_D_3`, `example_8_D_3_figure` |
| Section 8.D, p. 247 | Best-response correspondence; NE iff `s_i ∈ b_i(s_{-i})` | `bestResponse`, `bestResponse_update`, `isNashEquilibrium_iff_mem_bestResponse` |
| Section 8.D, pp. 248-250 | Arguments (i)-(v) for Nash equilibrium | Verbal; focal-point payoffs (1000, 1000): `example_8_D_3` (any positive payoffs) |
| Definition 8.D.2, p. 250 | Mixed strategy Nash equilibrium; = Definition 8.D.1 for the mixed extension | `IsMixedNash`, `isMixedNash_iff_bestResponse`, `isMixedNash_iff_mixedExtensionGame` |
| Example 8.D.4, Figure 8.D.3, p. 250 | Matching Pennies: no pure equilibrium; ½-½ mixed equilibrium | `example_8_D_4_no_pure`, `example_8_D_4` (Chapter 7's `matchingPennies`) |
| Proposition 8.D.1, pp. 250-251 | Indifference on the support, no better pure strategy off it | `proposition_8_D_1`, `isBestResponse_iff_support`, `mixedPayoff_update_eq_sum_pure`, `mixedPayoff_le_of_pure_le` |
| Section 8.D, p. 251 | Only pure deviations need be checked | `isMixedNash_iff_pure_deviations`, `isBestResponse_pureMixed_of_max`, `exists_pure_bestResponse` |
| Corollary 8.D.1, p. 251 | Pure NE iff degenerate mixed NE | `corollary_8_D_1` |
| Example 8.D.5, p. 251 | Indifference iff σ = 1/11; each goes to Grand Central with probability 1/11 | `example_8_D_5_indifference`, `example_8_D_5` |
| Section 8.D, p. 252 | Mixed strategies as private signals; stability concerns | Verbal |
| Small type, p. 252 | Public signal: following it is a correlated equilibrium | `meetNY_correlated` |
| Proposition 8.D.2, p. 252 | Finite games have a mixed Nash equilibrium | `proposition_8_D_2` (nonempty `S_i`; `no_mixedProfile_of_isEmpty`, correction 2) |
| Section 8.D, p. 253 | Randomization essential (Matching Pennies) | `example_8_D_4_no_pure` |
| Proposition 8.D.3, p. 253 | Pure NE with compact convex strategy sets, continuous payoffs quasiconcave in own strategy | `proposition_8_D_3` (`ℝ^{M_i}`), `nash_exists_of_quasiconcave` (normed spaces), `restrictGame`, `isNashEquilibrium_restrictGame`, `proposition_8_D_3_instance` |
| Footnote 5, p. 253 | A finite strategy set cannot be convex | `footnote_8_5`, `footnote_8_5_singleton` (correction 3) |
| Section 8.D, p. 253 | Existence without quasiconcavity / continuity (Dasgupta-Maskin) | Verbal citation; not stated precisely in the text |

## Section 8.E: Bayesian Nash equilibrium

| Source | Claim | Lean |
| --- | --- | --- |
| Section 8.E, pp. 253-254 | Incomplete information; Harsanyi's approach | Verbal |
| Section 8.E, p. 255 | Bayesian game `[I, {S_i}, {u_i}, Θ, F]`; decision rules | `BayesianGame` (payoffs may depend on all types; correction 4), `BayesianGame.IsPrior`, `BayesianGame.play` |
| (8.E.1), p. 255 | Expected payoff `ũ_i` | `BayesianGame.expectedPayoff`, `BayesianGame.toNormalForm` |
| Definition 8.E.1, p. 255 | Bayesian Nash equilibrium | `BayesianGame.IsBNE`, `BayesianGame.isBNE_iff` |
| Footnote 7, p. 255 | Mixed strategies over `𝒮_i`; finite or infinite `Θ_i` | Listed; finite-type mixed BNE exists: `BayesianGame.exists_mixed_BNE` |
| Proposition 8.E.1, (8.E.2), pp. 255-256 | BNE iff each type with positive probability best-responds to the conditional distribution | `BayesianGame.proposition_8_E_1` (`typeProb`, `typeGain`, `condPayoff`, `play_update`, `expectedPayoff_update_eq`, `expectedPayoff_eq`, `typeGain_eq_zero`) |
| Footnote 8, p. 256 | Infinite types: almost every type | Listed (the continuum case is used type-by-type in Example 8.E.2) |
| Example 8.E.1, Figure 8.E.1, pp. 254-256 | DA's Brother with incomplete information: four strategies of prisoner 2; BNE characterized by μ vs 1/6 | `daDims`, `DAΘ`, `daBayes`, `daθ`, `daΘEquiv`, `sum_daΘ`, `daBayes_isPrior`, `example_8_E_1` |
| Example 8.E.2, (8.E.3), pp. 256-257 | Zigger: cutoff rule, cutoff ≥ √c, cutoffs in (0, 1), θ̂₁²θ̂₂ = c = θ̂₂²θ̂₁, θ* = c^{1/3}, outcome probabilities | `zProb`, `ZiggerBNE`, `zigger_cutoff`, `zigger_cutoff_ge_sqrt`, `zigger_prob_response`, `example_8_E_2`, `example_8_E_2_exists`, `example_8_E_2_outcomes` (`zProb_mem`, `volume_sq_ge`, `volume_sq_ge_of_one_lt`) |
| Section 8.E, p. 257 | Purification (Harsanyi 1973); correlated equilibria as BNE | Verbal |

## Section 8.F: trembling-hand perfection

| Source | Claim | Lean |
| --- | --- | --- |
| Figure 8.F.1, pp. 258-259 | (D, R) a Nash equilibrium in weakly dominated strategies (not THP) | `fig8F1U₁`, `fig8F1U₂`, `figure_8_F_1`, `mixedWeaklyDominates_pureMixed` |
| Section 8.F, p. 258 | Perturbed games `Γ_ε`, `Δ_ε(S_i)` | `IsPerturbation`, `perturbedSet`, `IsPerturbedNash`, `convex_perturbedSet`, `isCompact_perturbedSet`, `perturbedSet_nonempty` |
| Definition 8.F.1, p. 258 | (Normal form) trembling-hand perfect NE | `IsTHP` |
| Footnote 9, p. 258; p. 259 | Dynamic-game version; stronger robustness test | Verbal |
| Proposition 8.F.1, p. 259 (Exercise 8.F.1) | THP iff best response to a sequence of totally mixed profiles converging to σ | `proposition_8_F_1` (`IsTotallyMixed`, `perturbedNash_eq_of_not_best`, `isTotallyMixed_of_perturbedNash`) |
| Proposition 8.F.2, p. 259 | THP strategies not weakly dominated; no weakly dominated pure strategy played | `proposition_8_F_2`, `proposition_8_F_2_pure` (`MixedWeaklyDominates`, `MixedWeaklyDominated`, `mixedWeaklyDominates_iff_pure`, `MixedWeaklyDominates.lt_of_totallyMixed`, `mixedWeaklyDominated_of_pure`) |
| Small type, p. 259 | Converse true for two players | `isTHP_of_not_weaklyDominated_two` (`exists_totallyMixed_bestResponse` via `stiemke_alternative` from Chapter 5's `exists_pos_of_cone_inter_nonneg`; `isBestResponse_two_mix`, `two_mixedPayoff_eq`, `two_mixedPayoff_pure`, `two_profile_ext`, `two_other`, `two_nonempty`); instance `figure_8_F_1_UL_isTHP` |
| Small type, p. 259 | Converse false for three players (Exercise 8.F.2) | `exercise_8_F_2` |
| Small type, p. 259 | Correlated trembles restore the converse | Verbal (no correlated-tremble notion is defined in the text) |
| Section 8.F, p. 259 | Selten: THP equilibrium exists in finite games | `exercise_8_F_3` |
| Section 8.F, pp. 259-260 | Hence a NE with no weakly dominated strategy exists; footnote 10 (Bertrand) | `exists_nash_no_weakly_dominated`; footnote 10 verbal (Chapter 12) |
| Small type, p. 260 | Proper equilibrium (Myerson) | Verbal citation |

## Appendix A: existence of Nash equilibrium

| Source | Claim | Lean |
| --- | --- | --- |
| Lemma 8.AA.1, p. 260 | Best responses nonempty, convex-valued, uhc (footnote 11: Section M.H) | `lemma_8_AA_1`, `bestResp`, `update_mem_pi` |
| Proposition 8.D.3, proof, p. 261 | Kakutani applied to `b = b_1 × ⋯ × b_I` | `nash_exists_of_quasiconcave` (via `kakutani_mwg`) |
| Proposition 8.D.2, proof, p. 261 | 8.D.3 for strategy sets `Δ(S_i)` | `proposition_8_D_2` (`continuous_mixedPayoff`, `concaveOn_mixedPayoff_update`, `convex_mixedExtension`, `isCompact_mixedExtension`) |

## Mathematical Appendix M.I: fixed point theorems

| Source | Claim | Lean |
| --- | --- | --- |
| Section M.I, p. 952 | Fixed point of a function/correspondence | Definitions inline (`x = f x`, `x ∈ f x`) |
| Theorem M.I.1, p. 952 | Brouwer | `theorem_M_I_1` (from `LeanEconomics.FixedPoint.brouwer`), `theorem_M_I_1_instance` |
| Figure M.I.1(a), pp. 952-953 | N = 1 by the intermediate value theorem | `brouwer_unitInterval_ivt` |
| Figure M.I.1(b), p. 953 | Continuity indispensable | `figure_M_I_1b` |
| Section M.I, p. 953 | Rotation of the circle: continuous, no fixed point, circle not convex | `unitCircle`, `rotateClockwise`, `circle_rotation_no_fixedPoint`, `circle_not_convex` |
| Theorem M.I.2, p. 953 | Kakutani (uhc in the sense of Definition M.H.3) | `theorem_M_I_2`, `kakutani_mwg` (from `LeanEconomics.FixedPoint.kakutani`), `theorem_M_I_2_instance` |
| Figure M.I.2(a)-(b), p. 953 | Convex values indispensable | `figM12b`, `figure_M_I_2b`; (a) is the theorem |
| Theorem M.I.3, p. 953 | Tarski on `[0, 1]^N` | `theorem_M_I_3` (Knaster-Tarski in Mathlib) |
| Figure M.I.3, p. 953 | Nondecreasing discontinuous map with fixed points | `figure_M_I_3` |

## Exercises

| Source | Claim | Lean |
| --- | --- | --- |
| Exercise 8.B.1, p. 262 | Strictly dominant strategy iff β = 0; its value | `lobbyGame`, `exercise_8_B_1_dominant`, `exercise_8_B_1_only_if`, `exercise_8_B_1_one_firm`, `exercise_8_B_1_nonpositive` (`quad_max`, `lobbyGame_update`, `eq_of_strictlyDominant_of_max`; correction 5) |
| Exercise 8.B.2(a), p. 262 | Two weakly dominant strategies give equal payoffs | `weaklyDominant_unique` (vacuous under 8.B.3), `exercise_8_B_2a` (correction 6) |
| Exercise 8.B.2(b), p. 262 | Example: opponent prefers one of two weakly dominant strategies | `AtLeastAsGoodAsAll`, `exercise_8_B_2b` (correction 6) |
| Exercise 8.B.3, p. 262 | Vickrey auction: truthful bidding weakly dominant and unique | `vickrey`, `exercise_8_B_3` (two or more bidders), `exercise_8_B_3_instance`, `exercise_8_B_3_one_bidder` (correction 10); `vickrey_update`, `vickrey_truthful`, `vickrey_le_truthful`, `vickrey_sup_const` |
| Exercise 8.B.4, p. 262 | Order independence of iterated strict dominance | `exercise_8_B_4`; infinite counterexample `countingGame`, `countingGame_step`, `countingGame_terminal`, `exercise_8_B_4_infinite_counterexample` (correction 1) |
| Exercise 8.B.5(a), p. 262 | Cournot duopoly: unique prediction | `exercise_8_B_5a`: every finite round of the maximal process (`sdRound`, `sdIter`, `sdStep_sdRound`, `sdIter_chain`) leaves an interval of quantities, and `⋂ₙ sdIter n i = {q*}`, `q* = (a - c)/(3b)` (`cournotStar`, `cournotBounds`, `cournotBounds_inv`, `cournot_two_sdIter`, `cournot_round`, `cournot_round_zero`, `cournot_not_dominated`, `cournot_update`, `cournot_gap`, `rivalsTotal`, `rivalsTotal_const`, `rivalsTotal_mem`, `qIval`, `cbr`, `cournot`) |
| Exercise 8.B.5(b), p. 262 | Three firms: not unique | `exercise_8_B_5b`: the process stops at `[0, (a - c)/(2b)]` (`SDTerminal`), a nontrivial limit |
| Exercise 8.B.6, p. 241 | See Section 8.B | `exercise_8_B_6` |
| Exercise 8.B.7, p. 262 | A strictly dominant strategy is pure | `exercise_8_B_7` (`uniformMixed`, `isMixedStrategy_uniformMixed`, `uniformMixed_pos`, `isMixedProfile_uniform`) |
| Exercise 8.C.1, p. 262 | Unique ISD prediction is the NBR prediction | `exercise_8_C_1` |
| Exercise 8.C.2, p. 262 | Order independence for never-best responses | `exercise_8_C_2` |
| Exercise 8.C.3, p. 262 | Two players: never a best response ⇒ strictly dominated (separating hyperplane) | `exercise_8_C_3` (`marginal`, `isMixedProfile_marginal`, `expect_eq_mixedPayoff_marginals`, `bestResponse_correlated_of_not_dominated`) |
| Exercise 8.C.4(a), p. 263 | M never a best response to independent randomizations | `exercise_8_C_4a` (symmetric entry), `exercise_8_C_4a_printed_false` (correction 8); `c4U`, `c4E` |
| Exercise 8.C.4(b), p. 263 | M not strictly dominated | `exercise_8_C_4b` |
| Exercise 8.C.4(c), p. 263 | M a best response to a correlated belief | `exercise_8_C_4c` |
| Exercise 8.D.1, p. 263 | (a₂, b₂) the unique mixed NE of Figure 8.C.1 | `exercise_8_D_1` |
| Exercise 8.D.2, p. 263 | A unique ISD survivor is a NE | `exercise_8_D_2` |
| Exercise 8.D.3(a), p. 263 | First-price auction, dollar bids: strictly dominated strategies | `exercise_8_D_3a` (none) (`firstPrice`, `fpPay`, `fpInt`, `fpPay_eq`, `fpPay_le_iff`, `fpPay_lt_iff`, `one_sub_ne`, `firstPrice_update`) |
| Exercise 8.D.3(b), p. 263 | Weakly dominated strategies | `exercise_8_D_3b`: `b ≥ max(v_i, 1)`, or `b = 0` and `v_i ≥ 2` (`firstPrice_weaklyDominates_iff`) |
| Exercise 8.D.3(c), p. 263 | Nash equilibria; existence; uniqueness | `exercise_8_D_3c` (all pure NE), `exercise_8_D_3c_exists`, `exercise_8_D_3c_not_unique` (`fpInt_bound_iff`, `firstPrice_isNash_iff`) |
| Exercise 8.D.4(a), p. 263 | No strictly dominated demand | `demandGame`, `demand_update`, `eff`, `exercise_8_D_4a` |
| Exercise 8.D.4(b), p. 263 | Weakly dominated demands: 0 and above 100 | `exercise_8_D_4b` |
| Exercise 8.D.4(c), p. 263 | Pure NE: sum 100, or both at least 100 | `exercise_8_D_4c` |
| Exercise 8.D.5(a), pp. 263-264 | Two vendors: unique NE at the midpoint | `exercise_8_D_5a` (`icShare2`, `iceCream2`, `iceCream2_update`, `icShare2_lt`, `icShare2_self`, `icShare2_gt`, `icShare2_le_half`, `uiMid`) |
| Exercise 8.D.5(b), p. 264 | Three vendors: no pure NE | `exercise_8_D_5b` (`icShare3`, `iceCream3`, `iceCream3_update`, `icShare3_left`, `icShare3_right`, `icShare3_self`, `icShare3_leftmost`, `icShare3_rightmost`, `icShare3_together`) |
| Exercise 8.D.6, p. 264 | Every 2 × 2 game has a mixed NE; the hint's parametrization | `exercise_8_D_6`, `exercise_8_D_6_param` |
| Exercise 8.D.7(a), p. 264 | `v_i ≥ w_i` | `exercise_8_D_7a` (`iSup_iInf_le_iInf_iSup_of_bdd`, `mprof`, `Δ₁`, `Δ₂`, `pay2`, `maximin₁`, `minimax₁`, `maximin₂`, `minimax₂`) |
| Exercise 8.D.7(b), p. 264 | Zero-sum NE: `u_i* = v_i = w_i` | `exercise_8_D_7b` (`IsZeroSum2`, `pay2_zeroSum`, `isMixedNash_mprof_iff`) |
| Exercise 8.D.7(c), p. 264 | Interchangeability of equilibria | `exercise_8_D_7c` |
| Exercise 8.D.8, p. 264 | Strictly quasiconvex payoffs ⇒ degenerate equilibria | `exercise_8_D_8_counterexample` (false as printed), `exercise_8_D_8` (strictly concave; correction 7) |
| Exercise 8.D.9(a), p. 265 | Player 2's choice (verbal) | Mathematical content: `M` is player 2's unique strategy guaranteeing `0`, `exercise_8_D_9a` (`krepsU₁`, `krepsU₂`, `kreps`, `kreps_rows`, `kreps_cols`) |
| Exercise 8.D.9(b), p. 265 | All Nash equilibria | `exercise_8_D_9b`: `(U, LL)`, `(D, R)`, `((51/52)U + (1/52)D, ½LL + ½L)` (`krepsX`, `krepsY`) |
| Exercise 8.D.9(c), p. 265 | `M` in no NE; `M` rationalizable | `exercise_8_D_9c_not_nash`, `exercise_8_D_9c_rationalizable` |
| Exercise 8.D.9(d), p. 265 | Preplay communication (verbal) | Mathematical content: both pure NE give `(100, 2)`, strictly better for both than any outcome with `M`, `exercise_8_D_9d` |
| Exercise 8.E.1, p. 265 | Armies: all pure BNE | `exercise_8_E_1` (with `0 < s < w`, `M > 0`), `exercise_8_E_1_instance` (`armyPay`, `armies`, `sum_fin2_bool`, `armies_isPrior`, `armies_typeProb`, `armies_typeGain`, `armies_isBNE_iff`, `stratAA`, `stratNN`, `stratAN`) |
| Exercise 8.E.2(a), p. 265 | Two bidders: linear BNE `s(v) = v/2` | `exercise_8_E_2a` (type by type, as Example 8.E.2; `fpBelow`, `fpExp`, `fpTie_zero`, `fpBelow_eq`, `fpBelow_nonpos`, `fp_bernoulli`, `fp_core`) |
| Exercise 8.E.2(b), p. 265 | `I` bidders: `s(v) = ((I - 1)/I) v`; limit as `I → ∞` | `exercise_8_E_2b`, `exercise_8_E_2b_limit` (bids tend to `v`), `exercise_8_E_2b_mono` |
| Exercise 8.E.3, p. 265 | Bayesian Cournot: the BNE | `exercise_8_E_3` (unique BNE `q_t = (2a - 3c_t + c̄)/(6b)`, assuming `3c_H ≤ 2a + c̄`; correction 11), `exercise_8_E_3_instance` (`typeP`, `tcost`, `bayesCournot`, `expQ`, `sum_fin2_fin2`, `bayesCournot_isPrior`, `bayesCournot_typeProb`, `bayesCournot_typeGain`, `quad_argmax`, `bayesCournot_isBNE_iff`, `bcq`) |
| Exercise 8.F.1, p. 265 | Prove Proposition 8.F.1 | `proposition_8_F_1` |
| Exercise 8.F.2, p. 265 | (D, L, B₁) not THP; none of D, L, B₁ weakly dominated | `vdU₁`, `vanDamme`, `p3`, `mixedPayoff_three`, `exercise_8_F_2_nash`, `exercise_8_F_2_undominated`, `exercise_8_F_2` |
| Exercise 8.F.3, p. 266 | Existence of THP equilibrium | `exercise_8_F_3` (`exists_perturbedNash`, `uniformTremble`, `isPerturbation_uniformTremble`, `tendsto_uniformTremble`, `tendsto_mixedPayoff_update`) |

## Supporting infrastructure

| Lean | Role |
| --- | --- |
| `IsMixedProfile`, `pureProfile`, `isMixedProfile_pureProfile`, `pureProfile_update`, `mixedPayoff_update_update`, `mixedPayoff_update_add_smul`, `mixedPayoff_update_sum_smul`, `mixedPayoff_pureProfile_update`, `mixedPayoff_pureProfile`, `mixedPayoff_pureProfile_update_mixed`, `prod_mixed_nonneg`, `sum_prod_mixed_eq_one`, `abs_mixedPayoff_le` | Algebra of mixed payoffs (module `MixedPayoff`) |
| `S2`, `bimatrix`, `pp`, `eq_pp`, `mp`, `eq_mp`, `ps`, `isMixedProfile_mp`, `fullSets_eq_ps`, `mixedPayoff_fin_two`, `sum_pureMixed_mul` and the `bimatrix_*` lemmas | Two-player payoff tables (module `Bimatrix`) |
| `mixed_le_one`, `mixed_exists_pos`, `isMixedStrategy_of_mem_perturbedSet` | Elementary facts on mixed strategies |
