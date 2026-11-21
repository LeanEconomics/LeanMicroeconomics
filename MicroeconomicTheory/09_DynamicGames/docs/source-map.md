# Source map

Mas-Colell, Whinston and Green, *Microeconomic Theory*, Chapter 9, "Dynamic Games",
pp. 267-306. Printed pages; Lean names relative to `MWG.DynamicGames`. Games are Chapter 7's
`ExtensiveForm` (histories as nodes) and strategies are behaviour strategies (Kuhn's theorem,
Chapter 7). All numbered definitions and Propositions 9.B.1-9.B.3, 9.C.1-9.C.2 are formalized,
with the hard results (Zermelo, uniqueness of the Rubinstein SPNE, the one-shot deviation
principles, extensive form trembling-hand perfection implies sequential equilibrium, and
existence of sequential and subgame perfect equilibria). Items marked **OPEN** were not
formalized in this session; the reason is given. Departures are in
[corrections](corrections.md).

## Section 9.B: backward induction and subgame perfection

| Source | Claim | Lean |
| --- | --- | --- |
| Section 9.A, pp. 267-268 | Introduction (credibility) | verbal |
| Section 9.B, pp. 270-272 | Continuation payoffs and the backward-induction recursion | `reachFrom`, `cont`, `cont_decision`, `cont_terminal`, `cont_eq`, `cont_unfold`, `cont_nil`, `reach_mul_cont`, `cont_congr`, `le_cont` |
| Footnote 3, p. 272 | `u_i(·)` is the normal-form payoff | `toNormalForm_payoff_eq_cont`, `IsNashB.isNashEquilibrium_pure` |
| Example 9.B.1, Figure 9.B.1, pp. 268-269 | Entry game; the two pure NE; (out, fight) not sequentially rational | `entryGame`, `example_9_B_1_perfectInformation`, `example_9_B_1_nash`, `example_9_B_1_not_spne` |
| Figure 9.B.2, p. 270 | Reduced game, backward induction gives (in, accommodate) | `example_9_B_1_spne` |
| Principle of sequential rationality, p. 269 | Optimal move at each decision node | `OneShotOptimalAt` |
| Backward induction, pp. 270-271 | The procedure is well defined in finite PI games | `IsBackwardInduction`, `exists_backwardInduction`, `pureOfChoice`, `cont_pureOfChoice` |
| Footnote 2, p. 270 | Finiteness matters | verbal (Appendix A shows an infinite case) |
| Example 9.B.2, Figure 9.B.3, pp. 271-272 | Three-player PI game; BI profile; unique SPNE | `threeGame`, `threeBI`, `example_9_B_2` |
| Proposition 9.B.1, pp. 272-273 | Zermelo: BI profile exists and is a NE; unique without ties (and without nature) | `proposition_9_B_1`, `oneShot_deviation_principle`, `oneShotOptimal_unique`, `pure_eq_of_assemble_eq`; with nature uniqueness fails: `proposition_9_B_1_nature_counterexample`, `natureGame` (corrections, item 1) |
| (9.B.1), distance-`n` induction, pp. 272-273 | The proof's induction | `oneShot_deviation_principle` |
| Note p. 273 | Finite PI games have a pure NE | `exists_pure_nash_of_perfectInformation` |
| Example 9.B.3, Figure 9.B.4, pp. 273-274 | Entry followed by a simultaneous game; three pure NE; unique SPNE | `entrySim`, `fig9B4`, `example_9_B_3_nash`, `example_9_B_3_spne` |
| Footnotes 4-5, p. 273 | Complete contingent plans; mutual expectations | verbal (footnote 5's dominance remark is the strict-dominance step of `example_9_B_3_spne`) |
| Definition 9.B.1, p. 274 | Subgame | `IsSubgameRoot`, `isSubgameRoot_nil` |
| Figure 9.B.5, footnote 6, pp. 275-276 | Parts that are not subgames; the two subgames of 9.B.4 | `entrySim_subgames`, `example_9_B_1_subgames` |
| p. 275 | In PI games every decision node starts a subgame | `isSubgameRoot_of_perfectInformation` |
| Definition 9.B.2, p. 275 | SPNE | `InducesNashAt`, `IsSPNE`; NE in behaviour strategies `IsBehaviorProfile`, `IsNashB` |
| p. 275 | Every SPNE is a NE | `isNashB_of_isSPNE` |
| Exercise 9.B.2(a), p. 275 | Only subgame the whole game ⇒ NE = SPNE | `exercise_9_B_2a` |
| Exercise 9.B.2(b), p. 275 | SPNE induces SPNE in every subgame | `exercise_9_B_2b`, `IsSubgameRootWithin`, `isSubgameRootWithin_iff` |
| pp. 275-276 | In finite PI games SPNE = backward induction | `isSPNE_iff_oneShotOptimal`, `oneShotOptimal_of_isSPNE`, `isSPNE_of_oneShotOptimal` |
| Proposition 9.B.2, footnote 7, p. 276 | Pure SPNE exists; unique without ties (and without nature) | `proposition_9_B_2`; counterexample with nature `proposition_9_B_2_nature_counterexample`, `natureGame_payoff_injective`, `natureGame_oneShot`, `assemble_pureB_pureOfChoice` |
| Generalized BI procedure, p. 277 | Steps 1-4 | `splice`, `IsSPNEIn`, `IsSPNEReduced`, `cont_splice_root` |
| Proposition 9.B.3(i), p. 277 | SPNE restricted to the reduced game | `proposition_9_B_3_i`, `isSPNEIn_of_isSPNE` |
| Proposition 9.B.3(ii), p. 277 | Splicing a reduced-game SPNE with a subgame SPNE | `proposition_9_B_3_ii`, `entryNodes_inSub`, `assemble_splice`, `assemble_update_splice`, `proposition_9_B_3_instance` |
| p. 278 | Final subgames: NE = SPNE; Example 9.B.3 solved by generalized BI | `exercise_9_B_2a`, `proposition_9_B_3_instance`, `example_9_B_3_spne` |
| Example 9.B.4, Figures 9.B.6-9.B.7, footnotes 8-9, pp. 278-279 | Niche Choice: two pure SPNE | `nicheGame`, `example_9_B_4` |
| Proposition 9.B.4, pp. 279-280 | Unique SPNE of repeated play of games with unique NE | `proposition_9_B_4` (existence and uniqueness of the history-independent SPNE, with its payoffs), in the history-based model `RHist`, `rsnoc`, `rval`, `IsRBehavior`, `IsRSPNE`; `rval_congr`, `rstage`, `rstage_update`, `rval_succ_of_const`, `isMixedNash_rstage_of_isRSPNE` (the backward-induction step); instance `pd_unique_nash`, `proposition_9_B_4_instance` (repeated Prisoner's Dilemma) |
| Footnote 10, p. 280 | History dependence with multiple equilibria | `footnote_10` (in the game of Exercise 9.B.9, (a₁, b₁) then (a₂, b₂) after (a₁, b₁) and (a₃, b₃) otherwise is a pure SPNE, though (a₁, b₁) is not a stage equilibrium) |
| pp. 280-281 | Infinite horizon games | Appendix A (`exercise_9_B_12`) |
| Example 9.B.5, Figure 9.B.8, pp. 281-282 | Centipede: unique SPNE, stop everywhere | `centipede` (`n + 1` decision nodes; MWG's game is `centipede 197`), `centPile`, `centPile_even`, `centPile_odd`, `example_9_B_5_payoffs`, `example_9_B_5` (perfect information; stop everywhere is an SPNE; every SPNE stops everywhere; payoffs `(1, 1)`; unique backward-induction profile), `example_9_B_5_ties` (Proposition 9.B.2's hypothesis fails), `centipede_step`, `centipede_cont_stopAll` |

## Section 9.C: beliefs and sequential rationality

| Source | Claim | Lean |
| --- | --- | --- |
| Example 9.C.1, Figure 9.C.1, p. 282 | Two pure NE, both SPNE | `entryTwo`, `fig9C1`, `example_9_C_1_nash`, `entryTwo_subgames`, `example_9_C_1_spne` |
| Definition 9.C.1, p. 283 | System of beliefs | `IsBeliefSystem` |
| p. 284 | `E[u_i | H, μ, σ]` | `condPayoff` |
| Definition 9.C.2, p. 284 | Sequential rationality | `SeqRationalAt`, `SeqRational` |
| pp. 284-285, footnotes 12-13 | Completely mixed strategies; Bayes' rule; the numbers `3/4`, `2/3`, `1/3` | `IsTotallyMixedB`, `bayesBelief`, `probInfo`, `example_9_C_1_bayes` |
| Definition 9.C.3, p. 285 | Weak PBE | `BayesConsistent`, `IsWeakPBE` |
| Proposition 9.C.1 and Exercise 9.C.1, pp. 285-286, 304 | NE iff sequential rationality on the path with Bayes beliefs | `proposition_9_C_1` (perfect recall), `nash_gap_eq`, `entry_closed`, `bayesOrUniform_spec` |
| p. 286 | Weak PBE is NE | `isNashB_of_isWeakPBE` |
| Example 9.C.1 continued, p. 286 | Unique weak PBE (in₁, accommodate), `μ = 1` | `example_9_C_1_weakPBE`, `leftBelief` |
| Example 9.C.2, Figure 9.C.2, pp. 286-287 | Joint venture: unique weak PBE; another SPNE | `jvGame`, `example_9_C_2_weakPBE` (the weak PBE and its uniqueness), `example_9_C_2_spne` (((out, out), decline, fight) is an SPNE), `jvGame_subgames`, `jvBelief` |
| Example 9.C.3, Figure 9.C.3, pp. 287-288 | Unique weak PBE for `γ > 0` | `fig9C3`, `example_9_C_3_unique`, `example_9_C_3_exists`, `entryTwo_weakPBE_facts`, `entryTwo_weakPBE_of`, `fig9C3_scalar`, `fig9C3_acc`, `fig9C3_fight`, `fig9C3_best` |
| Strengthenings, pp. 288-290 | Discussion; perfect Bayesian equilibrium | verbal |
| Example 9.C.4, Figure 9.C.4, pp. 289 and 291 | Weak PBE with unreasonable beliefs; unique SE `(y, r)` | `ncGame`, `example_9_C_4_weakPBE`, `example_9_C_4_consistent_beliefs`, `example_9_C_4_not_consistent`, `example_9_C_4_sequential` (unique SE `(y, r)` with beliefs `1/2`), `ncGame_bayes_half` |
| Example 9.C.5, Figure 9.C.5, pp. 289-291 | Weak PBE not SPNE; SE = unique SPNE | `example_9_C_5`, `fightBelief` |
| Definition 9.C.4, p. 290 | Sequential equilibrium | `IsConsistent`, `IsSequentialEq` |
| p. 290 | Every SE is a weak PBE | `isWeakPBE_of_isSequentialEq`, `tendsto_assemble`, `tendsto_reachFrom`, `tendsto_reach` |
| Proposition 9.C.2, p. 291 | SE strategies are an SPNE | `proposition_9_C_2` (perfect recall), `reachFrom_prop_of_consistent`, `isSequentialEq_strengthens` |
| Small type p. 291 | Players with the same information share beliefs | verbal |

## Section 9.D: forward induction

| Source | Claim | Lean |
| --- | --- | --- |
| Figure 9.D.1(a), pp. 292-293 | Weak PBE with beliefs on the dominated In₁ | `fig9D1a`, `figure_9_D_1a` |
| Figure 9.D.1(b), pp. 292-293 | Weak PBE with beliefs on the dominated small niche | `fig9D1b`, `figure_9_D_1b` |
| Footnote 15, p. 292 | The depicted equilibria are also SE and EFTHP | SE: `footnote_15_D_1a`, `footnote_15_D_1b`, `figure_9_D_2` (second conjunct), `entryTwo_consistent_leftBelief_zero`, `entryTwo_consistent_leftBelief_one`; EFTHP: `footnote_15_D_1a_EFTHP`, `footnote_15_D_1b_EFTHP`, `footnote_15_D_2_EFTHP` (trembles `fwdTremble` = `1/(n + 5)`, `fwdTremble_pos`, `fwdTremble_le`, `tendsto_fwdTremble`), via the sufficient condition `isEFTHP_pureMoves_of` (totally mixed behaviour profiles converging to a pure profile against which every agent's sure move is a best reply) |
| Figure 9.D.2, pp. 293-294 | Weak PBE (and SE); small niche not strictly dominated by out but equilibrium dominated | `fig9D2`, `figure_9_D_2` |
| Figure 9.D.3, pp. 294-295 | (in, small niche) strictly dominated by out | `figure_9_D_3` |
| Small type pp. 295-296 | Normal-form arguments, Kohlberg-Mertens | verbal |

## Appendix A: bilateral bargaining

| Source | Claim | Lean |
| --- | --- | --- |
| Figure 9.AA.1, p. 297 | The alternating-offer game | `BargainingGame`, `BargainingProfile`, `path`, `Agrees`, `value`, `respValue`, `IsDeviation`, `IsSPNE` (namespace `BargainingGame`), `value_eq_respValue`, `value_congr`, `value_bounds` |
| Example 9.AA.1, pp. 296-297 | Finite horizon: unique SPNE; `v₁*(T)` for odd and even `T` | `BargainingGame.example_9_AA_1`, `finP`, `finP_eq`, `example_9_AA_1_odd`, `example_9_AA_1_even`, `example_9_AA_1_instance` |
| Footnote 16, p. 296 | If offers of zero are refused, no optimal offer | the threshold `≥` is forced by `strategies_determined`; the footnote's own claim is verbal |
| Example 9.AA.1, p. 297 | Limit `v/(1+δ)`, `δv/(1+δ)` | `example_9_AA_1_limit` |
| Example 9.AA.2, pp. 298-299 | Rubinstein: unique SPNE, immediate agreement | `example_9_AA_2`, `rubinstein_value`, `rubinstein_isSPNE`, `threshold_isSPNE`, `value_ge_of_isSPNE`, `value_le_of_isSPNE`, `strategies_determined`, `example_9_AA_2_instance` |
| Footnote 17, p. 298 | The largest SPNE payoff is well defined | `spnePayoffs` (bounded, nonempty; `sSup`/`sInf` in `rubinstein_value`) |
| p. 299 | Infinite-horizon outcome is the finite-horizon limit | `example_9_AA_1_limit`, `example_9_AA_2` |
| One-stage deviation (infinite horizon, discounting) | Used to verify SPNE in the bargaining game | `value_le_of_bound`, `threshold_isSPNE` |
| One-shot deviation principle, general (infinite horizon, bounded payoffs, `δ ∈ [0, 1)`) | In a multi-stage game with observed actions (pure strategies), no profitable one-shot deviation at any history implies no profitable deviation (finite or infinite) at any history; hence SPE iff no profitable one-shot deviation | `OSHist`, `OSProfile`, `osPlay`, `osPath`, `osValue`, `osPath_length`, `osValue_summable`, `osValue_abs_le`, `osValue_succ`, `osPlay_update`, `osValue_congr`, `oneShot_deviation_principle_discounted`, `oneShot_deviation_principle_discounted_iff`; instance: grim trigger in the repeated prisoners' dilemma is subgame perfect iff `δ ≥ 1/2` (`grim_trigger_spe_iff`, `pdStage`, `pdClean`, `grimTrigger`, `pdU`, `pdU_bound`, `grim_value_clean`, `grim_value_dirty`) |

## Appendix B: extensive form trembling-hand perfection

| Source | Claim | Lean |
| --- | --- | --- |
| Agent normal form, p. 299 | Selten's agent form and its normal form | `Agent`, `owner`, `agentForm`, `agentNF`, `agentPure`, `agentEquiv`, `agentBeh`, `agentProfile`, `agentNF_mixedPayoff` |
| Definition 9.BB.1, p. 299 | EFTHP | `IsEFTHP`; existence `exists_isEFTHP` |
| Figure 9.BB.1, pp. 299-300 | van Damme's example: unique SPNE ((NR, L), ℓ); ((R, L), r) and ((R, M), r) normal form THP; unique EFTHP ((NR, L), ℓ) | `bb1Game`, `figure_9_BB_1_spne`, `bb1Game_subgames`, `bb1_normalForm` (the normal form as a bimatrix), `figure_9_BB_1_normalTHP`, `figure_9_BB_1_efthp` |
| p. 300 | Every EFTHP is a sequential equilibrium, hence subgame perfect | `isSequentialEq_of_isEFTHP`, `isSPNE_of_isEFTHP` (perfect recall, nature with full support) |
| One-shot deviation principle with consistent beliefs | Behind the p. 300 claim | `oneShot_consistent`, `propagate_consistent`, `entry_cons_closed`, `entry_cons_unique`, `propW`, `NatureFullSupport`, `reach_pos_of_totallyMixed`, `probInfo_pos`, `cont_update_dirac_sub` |
| Existence of sequential equilibrium (Kreps-Wilson) | Finite games with perfect recall | `exists_isSequentialEq` |
| Figure 9.BB.2, p. 301 | SE that is not EFTHP | `fig9BB2`, `figure_9_BB_2`; general fact: an agent never plays an action worse against every totally mixed profile, `isEFTHP_eq_zero_of_worse` |

## Exercises

| Source | Claim | Lean |
| --- | --- | --- |
| Exercise 9.B.1, p. 301 | Five subgames | `exercise_9_B_1` |
| Exercise 9.B.2(a)-(b) | In text | `exercise_9_B_2a`, `exercise_9_B_2b` |
| Exercise 9.B.3, p. 301 | BI profile is NE; all six pure NE; the others are not sequentially rational | `exercise_9_B_3_nash`, `exercise_9_B_3`, `IsPureNash3`, `threeGame_cont_pure` |
| Exercise 9.B.4, p. 302 | Zero-sum PI: unique SPNE payoffs | `exercise_9_B_4` (two players), `cont_zeroSum`, `exercise_9_B_4_instance` |
| Exercise 9.B.5(a), p. 302 | Simultaneous moves: `m₁` and `m₂` strategies | definitional (a strategy is an action) |
| Exercise 9.B.5(b) | Sequential: `m₁` and `m₂^{m₁}` strategies | `exercise_9_B_5b` |
| Exercise 9.B.5(c) | Multiple SPNE of (b) imply a tie for player 1 or player 2 | `exercise_9_B_5c`; instance `exercise_9_B_5c_instance`; model `IsMaskinSPNE` (backward-induction characterisation, see corrections), `IsMaskinNash`, `IsMaskinSimNash`, `IsMaskinSPNE.isMaskinNash` |
| Exercise 9.B.5(d) | No ties for player 2 and a pure NE of (a) with payoff `π₁`: every SPNE of (b) gives player 1 at least `π₁`; not so for every NE of (b) | `exercise_9_B_5d`; instance `exercise_9_B_5d_instance`, `maskinD₁`, `maskinD₂`, `maskinD₂_noTies`; counterexample for Nash equilibria `exercise_9_B_5d_nash` |
| Exercise 9.B.5(e) | The bound fails with ties for player 2, or for a mixed NE of (a) | `exercise_9_B_5e_ties` (`maskinTie₁`), `exercise_9_B_5e_mixed` (`maskinMix₁`, `maskinMix₂`, `maskinMix_spne_iff`; Chapter 8's `bimatrix`, `mp`) |
| Exercise 9.B.6 | Mixed post-entry equilibrium `2/9`; SPNE with E out | `exercise_9_B_6`, `nicheMixed` |
| Exercise 9.B.7, p. 302 | Finite horizon `T`, offer cost `c < v`, no discounting: the unique SPNE (proposer with `m` periods left offers `W (m − 1)`, responder accepts exactly `y ≥ W (m − 1)`, indifference included; `W k = v − c` for odd `k`, `0` for even `k`); payoffs `(v − c, 0)` for odd `T`, `(0, v − c)` for even `T`; no limit as `T → ∞` | `exercise_9_B_7`, `exercise_9_B_7_values`, `exercise_9_B_7_parity`, `exercise_9_B_7_limit`, `exercise_9_B_7_instance`, `W`, `W_succ`; model `OfferCostGame`, `OfferCostGame.value`, `OfferCostGame.respValue`, `OfferCostGame.IsSPNE`, `offerCost`, `share`, `firstStop`, `firstStop_eq`, `firstStop_le`, `value_eq_respValue`, `value_le_of_bound`, `threshold`, `threshold_isSPNE`, `strategies_determined` (see corrections) |
| Exercise 9.B.8 | Mixed SPNE exists in finite games | `exercise_9_B_8` (perfect recall, nature with full support; see corrections) |
| Exercise 9.B.9 | Twice-played 3×3 game: pure SPNE | `exercise_9_B_9` (pure SPNE iff (a₂, b₂) or (a₃, b₃) after every first-period outcome and no profitable first-period deviation), `exercise_9_B_9_first` (a first-period profile is played in some pure SPNE iff it is not (a₂, b₃) or (a₃, b₂)), `twProfile_isRSPNE`, `tw_nash_iff`, `tw_nash_iff'` (stage pure NE), `twU₁`, `twU₂`, `twS`, `twProfile`; general two-period backward induction `augGame`, `isRSPNE_two_iff`, `rpure`, `isRSPNE_two_pure_iff`, `rval_one`, `rval_two`, `pp_inj`, `rsnoc_zero`, `tw_payoff_cont` |
| Exercise 9.B.10 | Entry with a coordination post-game: SPNE for `x ≥ 0` and `x < 0` | `ecGame`, `ecInfo`, `ecPay`, `ec_subgames`; `exercise_9_B_10_pure` (for every `x`: pure SPNE are ((in, A, U), (A, ℓ)) and, iff `x ≥ 1`, ((in, A, D), (A, r))), `exercise_9_B_10_neg` (`x < 0`: unique SPNE among all behaviour profiles), `exercise_9_B_10_mixed` (`x = 3`: a further SPNE with the mixed coordination equilibrium); `ec_spne_U`, `ec_spne_D`, `ec_cont`, `ec_cont0`, `ec_cont1`, `ec_cont3`, `ec_beh`, `ec_assemble`, `ec_noNature`, `ec_decisionNodes`, `ecMixed`; general `IsSPNE.pure_dev`, `assemble_pureMoves`. The complete set of mixed SPNE for `x ≥ 0` is not characterised (see corrections) |
| Exercise 9.B.11, p. 303 | Declining market war of attrition: SPNE outcome and strategies | `exercise_9_B_11` (unique SPNE `attritionSPNE`: both in, A stays iff `t ≤ 10`, B iff `t ≤ 25`; alone, A stays iff `t ≤ 20`, B iff `t ≤ 25`; outcome: A exits at the start of period 11, B at the start of period 26; payoffs 605 and 285.5), `exercise_9_B_11_unique`, `exercise_9_B_11_monopoly`, `attritionSPNE_isSPNE`, `attritionSPNE_values`, `declining`, `decVA`, `decVB`, `decM`, `decL`; model `AttritionGame`, `AttritionProfile`, `AttritionGame.IsSPNE`, `jointValue`, `monoValue`, `jointValue_eq`, `monoValue_eq`, `stay_of_pos`, `exit_of_neg`, `monopoly_spne` (truncation: staying dominated after the last profitable date, then backward induction), `jointValue_le`, `monoValue_le` (see corrections) |
| Exercise 9.B.12 | Rubinstein with `δ₁ ≠ δ₂` | `exercise_9_B_12`, `xstar`, `xstar_add`, `rubOffer` |
| Exercise 9.B.13, p. 303 | SPNE of the infinite horizon game with offer costs | `exercise_9_B_13` (every SPNE: payoffs `a, b ≥ 0`, `a + b ≤ v − c`; every `(a, v − c − a)`, `a ∈ [0, v − c]`, is an SPNE payoff with immediate agreement), `exercise_9_B_13_payoffs` (each player's SPNE payoff set is `[0, v − c]`), `exercise_9_B_13_not_unique`, `exercise_9_B_13_delay` (`v < 2c`: agreement immediate at every node in every SPNE; `v ≥ 2c`: an SPNE with the first offer rejected), `exercise_9_B_13_instance`, `exercise_9_B_13_delay_instance`; `spne_bounds`, `value_le_feasible`, `value_add_le`, `splitProfile`, `splitProfile_isSPNE`, `spne_immediate`, `delayProfile`, `delayProfile_isSPNE`, `isSPNE_of_oneStage`. The full set of SPNE payoff pairs with delay is not characterized (see corrections) |
| Exercise 9.B.14(a) | Unique SPNE: enter, always stay, always accommodate | `exercise_9_B_14a`, `deterA`, `cA`, `dtA_strict`; data `dtNodesA`, `dtInfoA`, `dtPayA`, `dtStepA`, `dtA_cont`, `dtA_step`, `dtA_decisionNodes`, `dtA_noNature`, `dtA_perfectInformation` |
| Exercise 9.B.14(b) | With the financial constraint: unique post-entry SPNE strategies (stay, exit, stay; accommodate, fight, accommodate); E enters iff `K < 1`, two SPNE at `K = 1` | `exercise_9_B_14b`, `deterB`, `cB`, `dtB_strict`, `dtB_root`, `dtB_after_root`; data `dtNodesB`, `dtInfoB`, `dtPayB`, `dtStepB`, `dtB_cont`, `dtB_step`, `dtB_decisionNodes`, `dtB_noNature`, `dtB_perfectInformation`; instance `exercise_9_B_14_instance`; strict backward induction `bstep`, `cont_dirac_play`, `isPureMoves_dirac`, `isSPNE_of_weak_bi`, `eq_dirac_of_strict_bi` |
| Exercise 9.C.1 | Prove Proposition 9.C.1 | `proposition_9_C_1` |
| Exercise 9.C.2 | Weak PBE for `γ ∈ (−1, 0)` | `exercise_9_C_2`, `exercise_9_C_2_exists` |
| Exercise 9.C.3(a), p. 304 | Two types: characterise the pure weak PBE | Model `SBProfile`, `IsSBWeakPBE`, `sbVal`, `sbPrior`, `sbCont`, `sbRev`, `sbPay`, `sbPost`, `sbHat` (`p̂ = (1 − δ) vH + δ vL`), `sb_period2` (period-2 buyer rule). Necessity `sb_weakPBE_outcome`: every weak PBE has (i) `p1 = vL`, both buy at once (needs `vL ≥ λ p̂ + (1 − λ) δ vL`, `vL ≥ δ λ vH`), (ii) `p1 = p̂`, high type buys at once, low type at `vL` in period 2, or (iii) `p1 > vH`, no period-1 sale and `p2 = vH`; seller's payoff = the largest of the three benchmarks. Sufficiency `exercise_9_C_3a` (each outcome is a weak PBE outcome exactly when its benchmark is largest), existence `exercise_9_C_3a_exists`, instances `exercise_9_C_3a_examples`. Cutoff structure `sb_acc_mono`, `sb_buyer`; period-2 prices `sb_p2_mem` (always `vL` or `vH`), `sb_p2_of_lt`, `sbRev_le`, `sbRev_le_vL`, `sbRev_vL`, `sbRev_vH`; `sb_weakPBE_p2`, `sbPay_le`, `sbHat_mem`, `sbBuild`, `sbBuild_acc`, `sbBuild_acc_vL`, `sbBuild_isWeakPBE`, `bool_false_of_not` |
| Exercise 9.C.3(b), p. 304 | `v` uniform: characterise the weak PBE | Cutoff structure for every expected second price: `exercise_9_C_3b_cutoff` (`sbKappa`). Reduced model for `v` uniform on `[0, 1]` (see corrections): `IsSBUWeakPBE`, `sbCut`, `sbUPay`, `sbURev`, `sb_point_mass_opt`, `sb_rev_bound`; second price for the uniform posterior on `[0, k)` is `k/2` (`sbURev_opt_iff`); linear cutoff `κ = 2p/(2 − δ)` (`sb_consistent_r`, `sbRStar_cut`); `exercise_9_C_3b`: the profile with `p1 = p* = (2 − δ)²/(2 (4 − 3δ))`, cutoff `(2 − δ)/(4 − 3δ)`, second price `(2 − δ)/(2 (4 − 3δ))` (`sbPStar`, `sbRStar`) is a weak PBE and the unique one with consistent beliefs; `sbG_le`, `sbUPay_value`, `sbUPay_nonpos`. Weak PBE not unique: `exercise_9_C_3b_not_unique` (`δ = 1/2`, `p1 = 3/10 ≠ 9/20`). General `0 ≤ v̲ < v̄` (module `SellerBuyerGeneral`): model `sbgCut`, `sbgPay`, `sbgRev`, `IsSBGWeakPBE`, `IsSBGConsistent` (bridge `isSBGWeakPBE_zero_one_iff` to the `v̲ = 0`, `v̄ = 1` model); second price `max (v̲, k/2)`, the corner `v̲` when `k ≤ 2v̲` (`sbgRev_opt_iff`, `sbgRev_le`, `sbgRev_opt_val`, `sbgMaxRev`); consistent cutoff `K(p) = min ((p − δv̲)/(1 − δ), 2p/(2 − δ), v̄)` (`sbg_consistent`, `sbgK`, `sbgR`, `sbgCut_R`, `sbgK_mem`, `sbgCut_gt`, `sbgCut_of_le`, `sbgPhi`, `sbgK_phi`, `sbgPhi_K`); values `sbgVal`, `sbgGIk`, `sbgGCk`, `sbgGI`, `sbgGC`, `sbgKI`, `sbgOpt`, `sbgVal_corner`, `sbgVal_interior`, `sbgGC_sub`, `sbgGI_sub`, `sbgGIk_sub_sbgGCk`, `sbgGI_sub_sbgGC`, `sbgVal_le_opt`, `sbgPay_low`, `sbgPay_cons`, `sbgPhi_cand`, `sbg_cand_valid`, `sbgKI_mem`. Characterisation `exercise_9_C_3b_general` (iff): (i) `v̄ ≤ 2v̲`: `p1 = v̲`, all buy at once; (ii) `2v̲ < v̄`, `G_C ≤ G_I`: `p1 = sbgPI = (2 − δ)² v̄/(2 (4 − 3δ))`, cutoff `k*`, second price `k*/2`; (iii) `2v̲ < v̄`, `G_I ≤ G_C`: `p1 = sbgPC = (1 − δ) v̄/2 + δ v̲`, cutoff `v̄/2`, second price the corner `v̲`; `exercise_9_C_3b_general_outcomes`, `exercise_9_C_3b_general_exists`, instances `exercise_9_C_3b_general_examples` (`v̄ = 1`, `δ = 1/2`, `v̲ = 0, 3/10, 3/5`) |
| Exercise 9.C.4(a), p. 304 | Pure weak PBE of the settlement game | Model `SetBR`, `setPay`, `IsSetWeakPBE`, `setV`, `setM`; `exercise_9_C_4a` (atomless prior, e.g. any density: weak PBE iff D best responds and `s` maximises `V`), `setPay_eq_setV`, reduced form `setV_eq` (`V = π E[min(λ, t)] + c_d − (c_p + c_d) Prob(λ < t)`, `t = (s − c_d)/π`), `setV_thr`, `setV_of_le`, `setOffer_ge` (`s ≥ c_d`), `setTrial_eq` (trial probability `Prob(λ < t)`), `setM_facts`, `setG_zero`, `integrable_min`; example `exercise_9_C_4_uniform` (`unifPrior`, `unifPrior_isProbabilityMeasure`, `unifPrior_supp`, `setAccBR`, `setAccBR_BR`) |
| Exercise 9.C.4(b), p. 304 | Effects of `c_p`, `c_d`, `π` | `setTrial_anti` (trial probability weakly decreasing in `(c_p + c_d)/π`, any atomless prior), `exercise_9_C_4b` (weakly falls with `c_p` and with `c_d`, weakly rises with `π`), `exercise_9_C_4b_payoff` (P's payoff weakly falls with `c_p`, weakly rises with `c_d` and `π`) |
| Exercise 9.C.4(c), p. 304 | P may drop the case after a rejection | Model `SetCProfile`, `setCPay`, `IsSetCWeakPBE`; `exercise_9_C_4c_no_trial` (`E[λ] π < c_p`: no trials in any weak PBE; `setIntegral_lower_le`, `integrable_id_of_supp`, `integral_trial`), `exercise_9_C_4c_drop` (no-settlement weak PBE iff `E[λ] π ≤ c_p`; `setDrop`), `exercise_9_C_4c_settle` (`E[λ] π ≤ c_p ≤ π`: every `s ∈ (0, c_d]` is an all-settle weak PBE offer; `setSettle`), examples `exercise_9_C_4c_5_examples`. Printed "Ms. D" read as Ms. P (see corrections) |
| Exercise 9.C.5, p. 304 | P knows `λ` | Model `Set5Profile`, `set5Pay`, `IsSet5WeakPBE`, `set5Pay_acc`, `set5Pay_rej`, `mean_mem_Icc`, `set5_acc_facts`; `exercise_9_C_5` (one settlement amount, payoffs at least `max (c_d, λπ − c_p)`, the types going to trial are the high ones), `exercise_9_C_5_semi` (always a weak PBE: types with `λπ − c_p ≤ c_d` settle at `c_d`, others go to trial; `set5Semi`, `condOrZero`, `condOrZero_facts`), `exercise_9_C_5_pooling` (pooling at any `s ∈ [max (c_d, π − c_p), E[λ] π + c_d]`; `set5Pool`), `exercise_9_C_5_passive` (pooling at `E[λ] π + c_d` with prior beliefs everywhere; `set5Passive`), example in `exercise_9_C_4c_5_examples` |
| Exercise 9.C.6, p. 304 | Sequential equilibria of 9.C.3-9.C.5 | Read through structural consistency (see corrections). 9.C.3(a): `IsSBConsistent`, `sbPost_tendsto` (limits of trembles give Bayes' posterior), `sbPost_eq`, `exercise_9_C_6_two_types_none` (`λ vH > vL`: no pure SE), `exercise_9_C_6_two_types` (`λ vH ≤ vL`: outcomes (i)-(ii) only, and they exist). 9.C.3(b): `IsSBUConsistent`, `exercise_9_C_3b` (unique). 9.C.4(a): no off-path beliefs, SE = weak PBE (`exercise_9_C_4a`). 9.C.4(c): `IsSetCConsistent`, `exercise_9_C_6_settlement` (the multiple weak PBE are consistent). 9.C.5: `exercise_9_C_5_passive` (prior beliefs everywhere, limits of type-independent trembles); with finitely many types, type-dependent trembles generate every off-path belief (`signal_belief_consistent`, instance `signal_belief_consistent_instance`), so consistency adds nothing to the weak PBE conditions when the informed player moves once. A full characterisation of the SE of 9.C.5 with its continuum of types is **OPEN**: Definition 9.C.4 is not defined for a continuum of types (no notion of totally mixed trembles over `[0, 1]` and of limits of Bayes beliefs is formalized), and even the weak PBE of 9.C.5 are not fully characterised (partial pooling above `c_d`, corrections item 22) |
| Exercise 9.C.7(a), pp. 304-305 | Figure 9.Ex.2: SPNE, uniqueness, other NE | `bagA`, `bagPay`, `bagPayAB`; `exercise_9_C_7a` (unique SPNE `(B; D, U)`; NE iff `B` with `D` after `B`, `Prob(D after T) ≤ 2/3`, or `T` with `U` after `T`, `Prob(D after B) ≤ 1/3`; `(T; U, U)` is a non-subgame-perfect NE), `bagA_isSPNE`, `bagA_isSPNE_unique`, `bagA_isNashB_iff`, `bagA_nash_cases`, `bagA_cont`, `bagA_payoffs`, `bagA_assemble_eq`, `bagA_behavior`, `bagA_beh`, `bagA_beh_update`, `bagA_perfectInformation` |
| Exercise 9.C.7(b), p. 304 | Player 2 does not observe: new extensive form and NE | `bagB` (one information set for player 2), `exercise_9_C_7b` (unique NE `(T, U)`, mixed included), `bagB_cont`, `bagB_payoffs`, `bagB_assemble_eq`, `bagB_beh`, `bagB_beh_update` |
| Exercise 9.C.7(c), p. 305 | Noisy observation: extensive form; "unique weak PBE" | `bagC` (nature draws the signal after player 1's move; `bagCNodes`, `bagInfoC`, `bagNature`, `bagPayC`); `exercise_9_C_7c` (`(T; U, U)` with beliefs on `T` is a weak PBE for every `p`), `exercise_9_C_7c_pure_unique` (unique among weak PBE with player 1 pure), `exercise_9_C_7c_unique` (unique for `1/3 < p < 2/3`), counterexamples `exercise_9_C_7c_mixed_high` (`p ≥ 2/3`), `exercise_9_C_7c_mixed_low` (`p ≤ 1/3`), `exercise_9_C_7c_unique_iff` (corrected statement); `bagC_weakPBE_facts`, `bagC_weakPBE_of_T`, `bagC_isWeakPBE_of`, `bagC_seq0`, `bagC_seq3`, `bagC_seq4`, `bagC_bayes`, `bagProfile`, `bagBelief`, `bagProfile_values`, `bagBelief_values`, `bagC_probInfo_pos`, `bagC_cont`, `bagC_infoSet`, `bagC_assemble`, `bagC_assemble_eq`, `bagC_payoff0`, `bagC_condPayoff`, `bagC_cond3`, `bagC_cond4`, `bagC_reach`, `bagC_beh`, `bagC_beh_update`, `dirac_fin2` (see corrections) |
| Exercise 9.D.1 | PI, no nature, no ties: an order of iterated removal of weakly dominated strategies leaves only profiles with the SPNE path and payoffs | `exercise_9_D_1`, instance `exercise_9_D_1_instance` (entry game); `IsWDominatedIn`, `WDDeletionStep`, `biSets`, `biSets_step`, `biSets_mono`, `biSets_top`, `biSets_agree`, `cont_biSets`, `onPath_biSets_iff`, `Permits`, `permits_of_onPath`, `towards`, `towards_on_path`, `towards_mem`, `bi_strict`, `inSub_iff_of_pi`, `OnPath`, `onPath_self`, `OnPath.mono`, `OnPath.cons`, `OnPath.trans`, `IsPureMoves`, `isPureMoves_pureProfile`, `pureProfile_eq_one_iff`, `cont_step`, `cont_onPath`, `cont_agree`. The any-order claim (Moulin 1981) is not formalized |
