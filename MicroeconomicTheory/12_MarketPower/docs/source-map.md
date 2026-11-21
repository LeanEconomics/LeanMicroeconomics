# Source map

Mas-Colell, Whinston and Green, *Microeconomic Theory*, Chapter 12, "Market Power", pp. 383-435.
Printed pages; Lean names relative to `MWG.MarketPower`.
Covered: monopoly pricing and its welfare loss, perfect discrimination, the Bertrand and Cournot
models (including the competitive limit of Cournot and existence via Proposition 8.D.3), capacity
constraints, product differentiation, the linear city with and without nonpurchase, the circular
city, the representative-consumer and monopolistic competition models, repeated Bertrand
interaction with Nash reversion, entry and welfare, strategic precommitment, and Appendix A
(Nash reversion, Friedman's theorem, severer punishments, the folk theorem with exact payoffs and
pure strategies, Example 12.AA.1), and Appendix B (strategic entry deterrence and accommodation). Items marked **not formalized** or **OPEN** are listed with
the reason; corrections are in [corrections](corrections.md).

## 12.B Monopoly pricing

| Source | Claim | Lean |
| --- | --- | --- |
| (12.B.1), p. 384; fn 2-4 | Price formulation; partial equilibrium; inverse demand | quantity formulation used (as MWG does); fn 2-4 verbal; fn 3 see Ex. 12.B.2 |
| (12.B.2), p. 385 | Monopolist's problem | `monopolyProfit`, `IsMonopolyOptimum`, `hasDerivWithinAt_monopolyProfit` |
| (12.B.3)-(12.B.4), p. 385 | First-order conditions; interior optimum | `eq_12_B_3`, `eq_12_B_4` |
| p. 385 | `p(qᵐ) > c'(qᵐ)` and `qᵐ < q°` | `monopoly_price_gt_mc`, `monopoly_quantity_lt` (correction 1) |
| Existence claim and fn 5, p. 385 | Existence of an optimum | `footnote_12_5`; counterexample `footnote_12_5_counterexample` (correction 1) |
| fn 6, p. 385 | FOC sufficient under concavity; convex demand can break concavity | `footnote_12_6`, `footnote_12_6_not_concave` |
| p. 386 | Deadweight loss `∫(p − c') > 0` | `deadweight_loss_pos` |
| Fig. 12.B.1-12.B.2, p. 386 | Graphical | listed only |
| p. 386; fn 7 | `p' = 0`: no distortion | `flat_demand_no_distortion`; fn 7 verbal |
| Example 12.B.1, p. 386 | Linear demand, constant returns | `example_12_B_1` |
| (12.B.5), pp. 386-387 | Perfect discrimination solves the surplus problem | `perfect_discrimination`, `perfect_discrimination_optimal` |

## 12.C Static models of oligopoly

| Source | Claim | Lean |
| --- | --- | --- |
| p. 388 | Bertrand model, sales function | `IsBertrandDemand`, `bertrandSales`, `bertrandSales_duopoly`, `bertrandProfit`, `bertrandGame` |
| Proposition 12.C.1, p. 388 | Unique NE `p₁ = p₂ = c` | `proposition_12_C_1` (proof departure, correction 2) |
| fn 8-9 | Fourth variation; mixed strategies | fn 8 verbal; fn 9 is Ex. 12.C.2: `exercise_12_C_2` (below) |
| p. 389; Exercise 12.C.1 | `J̄` firms at the lowest price share `x(p̄)`; with `J > 2` all sales at cost | `bertrandSales`, `exercise_12_C_1` |
| (12.C.1)-(12.C.4), p. 390 | Cournot problem and first-order conditions | `cournotProfit`, `IsCournotNE`, `cournot_foc` |
| fn 11-12, p. 390 | Method remark; interior equilibrium | fn 11 verbal; `footnote_12_12` (any number of firms) |
| (12.C.5), p. 390 | Summed FOC | `eq_12_C_5` |
| Proposition 12.C.2, p. 390 | `c < p(Q*) < p(qᵐ)` | `proposition_12_C_2` |
| Example 12.C.1, pp. 391-393; Exercise 12.C.6 | Best responses, unique NE, price, joint monopoly point | `example_12_C_1_br`, `example_12_C_1`, `example_12_C_1_joint`, `exercise_12_C_6` |
| Fig. 12.C.1-12.C.3 | Graphical | listed only |
| Small type, p. 393 | Quasiconcavity and Proposition 8.D.3: a pure NE exists | `cournotGenProfit`, `smallType_12_C_393` (strategy sets `[0, B]`, via Chapter 8's `nash_exists_of_quasiconcave`), `smallType_12_C_393_unbounded` (on `[0, ∞)` when `p(Q) ≤ c` for `Q ≥ B`), `smallType_12_C_393_linear` (correction 25) |
| Small type, p. 393; Fig. 12.C.3 | Without quasiconcavity a pure NE may not exist; firms must differ (Ex. 12.C.8) | `IsCournotGenNE`, `cnxP`, `cnxC`, `cnxP_rev`, `cournotGenProfit_fin0`, `cournotGenProfit_fin1`, `smallType_12_C_393_nonexistence`; identical firms: Ex. 12.C.8(d) below; figure graphical |
| (12.C.6), p. 393 | `J`-firm condition; `J = 1`; `p(Q_J) → c` | `eq_12_C_6`, `eq_12_C_6_one`, `cournot_competitive_limit` |
| Exercise 12.C.7, p. 393 | Linear `J`-firm model | `exercise_12_C_7`, `exercise_12_C_7_limits` |
| p. 394 | With `q̄ = ¾x(c)` (or any `0 < q̄ < x(c)`), `p₁ = p₂ = c` is not an equilibrium | `capSales`, `capProfit`, `IsCapNE`, `capSales_lt`, `capSales_gt`, `capSales_eq`, `capSales_nonneg`, `capacity_bertrand_not_eqm`, `capacity_bertrand_not_eqm_three_quarters` |
| pp. 394-395; Fig. 12.C.4 | A price in `(c, p(q̄))` assures positive sales `x(p₁) − q̄` at a positive margin | `capacity_assured_sales` (sales are `min{q̄, x(p₁) − q̄}`, correction 23); figure graphical |
| Small type, p. 395 | Rationing rules; high-valuation rule | the high-valuation rule is `capSales`; comparisons with other rules verbal |
| p. 395 | Kreps-Scheinkman (1983): Cournot outcome is the unique SPNE | cited by MWG without proof; **not formalized** (needs mixed-strategy equilibria of the pricing subgames) |
| p. 395 | For a wide range of capacities the unique pricing equilibrium is `p(q̄₁ + q̄₂)` | `capacity_unique` (the range of Ex. 12.C.11(a), positive capacities, continuous demand) |
| pp. 395-396 | Differentiated demand: a best response to `p̄₋ⱼ` with `x_j(c, p̄₋ⱼ) > 0` is above cost; equilibrium prices above cost | `diffProducts_profitable`, `diffProducts_br_above_cost`, `diffProducts_eqm_above_cost`, `diffProducts_instance` (nonnegative demand) |
| fn 13, p. 395 | Bertrand demand is discontinuous at `p_j = min_{k≠j} p_k` | `footnote_12_13`, `footnote_12_13_instance` |
| Example 12.C.2, pp. 396-398 | Linear city: (12.C.7)-(12.C.12), unique NE `c + t`, no asymmetric equilibria | `lcHat_spec`, `linearCity_prefers`, `lcDemand`, `lcProfit`, `lcBR_mid`, `lcBR_high`, `lcBR_low`, `IsLCNash`, `example_12_C_2` |
| Fig. 12.C.6, pp. 396-397 | Purchase decisions with nonpurchase; demand | `lcv_buys_iff`, `volume_unit_inter_Iio`, `lcvShare`, `lcvShare_spec`, `lcHat_symm`, `lcvShare_nonneg`, `lcvShare_eq_of`, `lcvShare_eq_zero`, `lcvProfit`, `IsLCVNash`; figure graphical |
| Small type, p. 398 | Best responses for all `v` | `IsLCVUniqueBR`, `lcv_le_zero_of_lt`, `lcv_mul_le`, `lcv_le_of_share`, `lcv_le_one`, `lcv_le_A`, `lcv_le_B`, `lcv_uniqueBR_of`, `lcv_eq_of_uniqueBR`, `lcv_max_of_uniqueBR`, `lcvNash_of_BR`, `lcvBR_low`, `lcvBR_duo`, `lcvBR_kink`, `lcvBR_mono`, `lcvBR_cover`, `lcvBR_capture`, `lcvBRLow`, `lcvBRMid`, `lcvBRHigh`, `lcvBRLow_spec`, `lcvBRMid_spec`, `lcvBRHigh_spec`, `lcv_rival_low`, `lcvNash_ge_c`, `lcvShare_symm_half` |
| Small type, p. 398 | Equilibrium `c + t` valid for `v ≥ c + 3t/2`; `v < c + t` local monopolists; kink for `v ∈ [c + t, c + 3t/2]` with zero surplus at `ẑ` | `smallType_12_C_398` (also unique), `exercise_12_C_14c` (market areas do not touch), `smallType_12_C_398_kink` |
| p. 399; Fig. 12.C.8 | Circular city (Salop): `J` firms equally spaced on a circle | `circLin_prefers`, `circLin_beyond`, `circDemand`, `circ_symmetric_eqm`, `circ_symmetric_unique`, `circularCity_linear` (price `c + t/J`; MWG derives no equilibrium here; deviation demand modelling in correction 28) |
| fn 15; p. 399 | Symmetric positions only on the circle; spatial models | verbal |
| p. 399; (12.C.13) | Representative consumer `G(∑ f(x_j)) + m`; first-order conditions; inversion to demand | `repWelfare`, `repUtility_budget`, `repWelfare_update`, `eq_12_C_13`, `repTangent`, `repTangent_strict`, `eq_12_C_13_sufficient`, `eq_12_C_13_unique`, `eq_12_C_13_instance` (correction 27) |
| fn 16, 17 | More general utility; quantity games | verbal |
| p. 400 | Monopolistic competition: demand `ψ(p_j/G'(x̄))`, index unaffected by one firm, equilibrium `x̄*` | `monComp_demand`, `monComp_index_update`, `monComp_no_interaction`, `IsMonCompEqm`, `monComp_example` |
| fn 18 | Spatial models keep strategic interaction | verbal |

## 12.D Repeated interaction

| Source | Claim | Lean |
| --- | --- | --- |
| p. 401 | Finitely repeated Bertrand: unique SPNE `p = c` | `fhValue`, `IsFiniteRepeatedSPNE`, `finiteNashValue`, `fhValue_congr`, `finite_repeated_step`, `finite_repeated_unique_spne` (any `δ`), `finite_repeated_spne_iff` (`δ ≥ 0`), `bertrandStage_nash_iff`, `finite_repeated_bertrand`, `finite_repeated_bertrand_instance` (correction 39) |
| (12.D.1), p. 401 | Nash reversion strategies | `nashReversion`, `constPrice`, `bertrandStage` |
| Proposition 12.D.1, pp. 401-402; (12.D.2) | SPNE iff `δ ≥ 1/2` | `proposition_12_D_1`, `bertrand_nashReversion_iff` |
| Small type, p. 403 | Interpretations of `δ` | see Ex. 12.D.1 |
| Proposition 12.D.2, first part, p. 403 | Prices in `[c, pᵐ]` sustained for `δ ≥ 1/2` | `proposition_12_D_2_part1_corrected`; counterexample `proposition_12_D_2_counterexample` (correction 7) |
| Proposition 12.D.2, second part, pp. 403-404; (12.D.3)-(12.D.5) | `δ < 1/2`: all sales at `c` | `proposition_12_D_2_part2` (correction 8) |
| fn 19-20, p. 404 | Remarks | verbal |
| pp. 404-405 | Folk theorem remark; imperfect observability | see Appendix A; small type verbal |
| Exercise 12.D.2, p. 405 | `J` firms: `δ ≥ (J − 1)/J` | `exercise_12_D_2_corrected` (correction 7) |

## 12.E Entry

| Source | Claim | Lean |
| --- | --- | --- |
| (12.E.1)-(12.E.2), p. 406 | Equilibrium number of entrants; uniqueness with decreasing `π_J` | `IsEntryEquilibrium`, `entry_equilibrium_unique`, `entry_equilibrium_exists`, `entry_equilibrium_iff` |
| fn 21-22, p. 406 | Many equilibria by identity; weak inequalities | fn 21 verbal; `footnote_12_22` |
| Example 12.E.1, p. 407; (12.E.3)-(12.E.4) | Cournot entry: `q_J`, `π_J`, `J*` = integer part of `J̃`, statics | `cournotEntryProfit`, `example_12_E_1`, `example_12_E_1_number`, `example_12_E_1_statics` |
| Example 12.E.2, p. 407 | Bertrand entry: `J* = 1` | `example_12_E_2` |
| (12.E.5), p. 408 | Welfare | `entryWelfare`, `entryWelfare_linear` |
| Example 12.E.3, p. 408; (12.E.6)-(12.E.7) | `J° = 2, 3, 8` give `J* = 4, 7, 26` | `example_12_E_3`, `example_12_E_3_aux` |
| (A1)-(A3), Proposition 12.E.1, p. 409; (12.E.8); fn 23 | `J* ≥ J° − 1` | `proposition_12_E_1` (every maximizer, so fn 23) |
| Exercise 12.E.2 | `π_J` decreasing under (A1)-(A3) | `exercise_12_E_2` |
| fn 24 | Strict version | `footnote_12_24`, `footnote_12_24_instance` (correction 42) |
| Fig. 12.E.1-12.E.3, pp. 410-411 | Graphical | listed only |
| p. 410 | One-stage entry game with price competition; demand to one lowest-price firm | `IsLowestPriceRule`, `exists_lowestPriceRule`, `oneStageProfit`, `IsOneStageEq`, `lowestRule_update_lt`, `lowestRule_update_gt`, `oneStageProfit_of_win`, `oneStageProfit_of_lose`, `oneStageProfit_le` |
| Example 12.E.4, pp. 410-411 | All sales at `p* = min{p : p ≥ [K + cx(p)]/x(p)}`, one firm, zero profits | `oneStagePrice`, `example_12_E_4_set`, `oneStagePrice_spec`, `example_12_E_4` (single peakedness added), `example_12_E_4_exists`, `example_12_E_4_instance`; false as printed: `osCexDemand`, `osCexDemand_mid`, `osCexDemand_isBertrand`, `example_12_E_4_counterexample` (correction 43) |
| Example 12.E.4, p. 411 | Strictly better welfare than Example 12.E.2 | `oneStageWelfare`, `example_12_E_4_welfare` |
| fn 25 | References | verbal |
| fn 26, p. 411 | Giving demand to one firm is the only division compatible with equilibrium | equal sharing has no equilibrium: `shareProfit`, `IsShareEq`, `shareProfit_of_lowest`, `shareProfit_of_gt`, `footnote_12_26` (correction 44) |
| fn 27, p. 411 | Outcome solves the planner's problem with nonnegative profits | `footnote_12_27`, `footnote_12_27_instance` (correction 45) |
| p. 411 | One-stage vs two-stage; hit-and-run entry; contestable markets | verbal (formal content: Example 12.E.4 and Ex. 12.E.6) |

## 12.F The competitive limit

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 411-412 | Market size `α`, `p_α(q) = p(q/α)`, `c̄`, `q̄`, two-stage Cournot entry SPNE | `sizedDemand`, `sizedDemand_strictAntiOn`, `entryNetProfit`, `IsCournotEntrySPNE` (explicit SPNE, potential firms `ℕ`), `BRDecreasing`; nonempty: `entry_spne_instance` (correction 16) |
| Proposition 12.F.1, p. 412 | SPNE prices converge to `c̄` | `proposition_12_F_1`; general form `competitive_limit`; with step (i) from Ex. 12.F.1: `proposition_12_F_1_of_exercise_12_F_1`; instance `proposition_12_F_1_instance` (correction 16) |
| Proof step (i), p. 412 | `b` decreasing for large `α` | Ex. 12.F.1 below (false as printed; corrected condition used) |
| Proof step (ii), p. 412 | `Q_α ≥ αx(c̄) − q̄` | `entry_step_ii` |
| Small type, pp. 412-413 | Incumbents' output cannot rise after entry (via Ex. 12.C.8(c)) | `entry_incumbents_no_expand` |
| Proof step (iii), p. 413 | `Δp_α → 0`; price `≥ c̄` | `competitive_limit`, `entry_price_ge` |
| p. 413 | Two forces; Bertrand has no limit result; differentiated products | verbal (Bertrand: `example_12_E_2`; differentiation: Ex. 12.F.4) |
| fn 28, p. 413 | Welfare loss per consumer `→ 0` | verbal; for the linear model see Ex. 12.F.2(b) (`exercise_12_F_2b`) |
| fn 29, p. 413 | Proposition valid with constant marginal cost, `c̄` = limit of average cost | `footnote_12_29`, `footnote_12_29_instance` |

## 12.G Strategic precommitments

| Source | Claim | Lean |
| --- | --- | --- |
| (12.G.1), p. 414 | `ds₂*/dk` | `eq_12_G_1` |
| Fig. 12.G.1, p. 415 | Sign table | `figure_12_G_1` |
| (12.G.2), p. 416 | Direct and strategic effects | `eq_12_G_2` |
| Example 12.G.1, pp. 415-416; fn 30 | Cost reduction: Cournot vs price competition | `example_12_G_1`, `cournot_two_costs`, `linearCity_two_costs`; fn 30 verbal |
| p. 417 | Entry deterrence (stage 1.5): firm 2 stays out if its anticipated stage-3 profit is below `F`; credible deterrence through `k` | made precise in Appendix B: `EDEntryOptimal`, `appendixB_stage2`, `IsEDSPNE`; predatory-pricing threat and "many mechanisms" verbal |

## Appendix A: infinitely repeated games and the folk theorem

| Source | Claim | Lean |
| --- | --- | --- |
| Model, pp. 417-418; fn 31 | Repeated game, strategies, outcome paths, `v_i(Q, t)` | `stageU`, `IsRepeatedSPNE`, `pathValue`, `pathHist`, `osValue_eq_of_rec` (Chapter 9's `osValue`, `oneShot_deviation_principle_discounted_iff` imported) |
| p. 418 | Stage NE every period is an SPNE | `stage_nash_spne` |
| Definition 12.AA.1 | Nash reversion | `nashReversion`, `IsStageNash` |
| Lemma 12.AA.1, p. 418; (12.AA.1) | Characterization | `nashReversion_spne_iff` (corrected), `lemma_12_AA_1_if`, counterexample `counterexample_12_AA` (correction 3) |
| (12.AA.2)-(12.AA.3), p. 419 | Rewritten conditions | `eq_12_AA_2`, `eq_12_AA_3` |
| Proposition 12.AA.1, p. 419; (12.AA.4)-(12.AA.6) | Pareto improvement by Nash reversion | false as printed: `proposition_12_AA_1_false`, `sclG_hypotheses`, `counterexample_12_AA_1_4`; corrected `proposition_12_AA_1_upper` (instance `scl_upper_instance_1`) and envelope version `proposition_12_AA_1`, `LocalGameData`, `stage_local_pos`, instance `proposition_12_AA_1_instance`; (12.AA.4) `scl_own_partial_zero`; (12.AA.6) `scl_env_of_upper`, `scl_upper_of_hasDerivAt` (correction 6) |
| Proposition 12.AA.2, p. 420 | Monotone in `δ` | `proposition_12_AA_2_corrected`; counterexample `counterexample_12_AA` (correction 4) |
| Proposition 12.AA.3, p. 420 | Friedman's theorem | `proposition_12_AA_3` |
| fn 32 | Convexification by alternating | covered by `proposition_12_AA_5` and `Schedule` |
| Exercise 12.AA.1, p. 420 | Payoffs below Nash not sustainable | `exercise_12_AA_1_corrected`, `exercise_12_AA_1_printed_condition` (correction 5) |
| p. 421; fn 33 | Minimax payoffs, individual rationality | `minimaxValue`, `bestReplyValue`, `minimax_le_nash`, `minimax_le_spne_value`; fn 33 verbal |
| Proposition 12.AA.4, p. 421; Exercise 12.AA.2 | Severer punishments | false as printed: `proposition_12_AA_4_false`, `sclG_spne_value_nonneg`, `counterexample_12_AA_1_4`; corrected `proposition_12_AA_4_upper` (instance `scl_upper_instance_4`) and envelope version `proposition_12_AA_4`, `scProfile`, `scProfile_spne`, `stage_local_neg`, instance `proposition_12_AA_4_instance` (correction 6) |
| Proposition 12.AA.5, p. 422; fn 34-35 | Folk theorem | `proposition_12_AA_5`, `folk_theorem`, `folk_theorem_instance`, `Schedule` (`sched_invariant`, `schedCont_rec`, `schedCont_close`); fn 34-35 verbal |
| Example 12.AA.1, pp. 422-423; (12.AA.7); fn 36-37 | Average payoff zero in repeated Cournot | `example_12_AA_1`, `example_12_AA_1_qbar`, `example_12_AA_1_instance`, `cfG`; fn 36 is the compact action set; fn 37 is Chapter 9's one-shot deviation principle |

## Appendix B: strategic entry deterrence and accommodation

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 423-424 | Three-stage game (capacity `k_I` at `r`; entry at `F`; quantities, I at cost `w` up to capacity, E at `w + r`) | linear model `p(Q) = a − Q`, `r > 0`, `a − w − 2r > 0` (correction 20): `edProfit`, `edQI`, `edQE`, `edQM`, `edProfE`, `IsStage3Nash`, `edPayI`, `EDEntryOptimal`, `IsEDSPNE` |
| p. 424 | Profits strictly concave in own output; concave `p` sufficient | `appendixB_profit_strictConcave` (general `p`) |
| p. 424 | Concave `p` makes best responses downward sloping | `appendixB_br_antitone` (general `p`), `appendixB_concave_increment` |
| p. 424; Fig. 12.BB.1 | E's best response `b(q_I \| w + r)`; E's profits fall moving right; point `Z` where they equal `F` | general: `figure_12_BB_1`; linear: `figure_12_BB_1_linear`, `edKZ` |
| p. 424 display; Fig. 12.BB.2 | `b_I(q_E \| k_I) = min{b(q_E \| w), k_I}` | general: `figure_12_BB_2`; linear: `figure_12_BB_2_linear` |
| p. 425; Fig. 12.BB.3 | Stage-3 equilibrium after entry; points `A`, `B`; I can reach E's best response up to `B` but not beyond | `figure_12_BB_3` (existence, uniqueness, point `A`, `k_B > u/3`), `figure_12_BB_3_range`, `edKB` |
| p. 425; Fig. 12.BB.4 | `k_I > k_B`: capacity not fully used; threat not credible | `figure_12_BB_4` |
| p. 425 | No entry: monopoly output `b_I(0 \| k_I)` | `appendixB_stage3_noEntry` |
| p. 426 | Stage 2: enter iff nonnegative net profit, i.e. iff left of `Z` | `appendixB_stage2`, `edBookRule`, `edBookRule_optimal`, `edStayOutRule`, `edStayOutRule_optimal` |
| p. 426; Fig. 12.BB.5 | Blockaded entry: capacity `b(0 \| w + r)`, no entry, best possible outcome | `figure_12_BB_5`, `edPayI_false_le`, `figure_12_BB_5_instance` |
| p. 426; Fig. 12.BB.6 | Entry inevitable: Stackelberg point `S`; first-mover advantage; `S` right of `B` gives `k_I = k_B`, worse than `S` | `figure_12_BB_6`, `edPayI_true_le`, `figure_12_BB_6_firstMover`, `figure_12_BB_6_rightOfB`, `figure_12_BB_6_instance`, `figure_12_BB_6_rightOfB_instance` |
| p. 427; Fig. 12.BB.7 | Deterrence possible but not inevitable: capacity `≥ k_Z` deters | `appendixB_deter_region`, `appendixB_deter_entry`, `appendixB_deter_noEntry`; tie at `k_Z`: correction 21, `appendixB_bookRule_no_spne` |
| p. 427; Fig. 12.BB.8 | `k_π` (monopoly output earning the profit at `S`); `k_π > k_Z` ⇒ deter, `k_π < k_Z` ⇒ accommodate | `edKPi`, `figure_12_BB_8`, `figure_12_BB_7_deter`, `figure_12_BB_7_accommodate`, `figure_12_BB_7_deter_instance`, `figure_12_BB_7_accommodate_instance` |
| p. 427 | Deterrence threat raises output and welfare relative to no possible entry | `appendixB_deterrence_raises_output`, `edSurplus`, `edSurplus_eq_integral` |
| Fig. 12.BB.1-12.BB.8 | Curves, isoprofit tangency at `S` | mathematical content as above; drawing listed only |
| Exercise 12.BB.1, p. 427 | `S` right of `Z` ⇒ deterrence better | `exercise_12_BB_1` (general `p`), `exercise_12_BB_1_instance`; in the linear model `S` is never strictly right of `Z` unless entry is blockaded: `appendixB_linear_S_le_Z` |

## Exercises

| Source | Claim | Lean |
| --- | --- | --- |
| 12.B.1(a)-(b) | Lerner index; elastic demand | `priceElasticity`, `priceElasticity_eq_demand`, `exercise_12_B_1a`, `exercise_12_B_1b` (correction 12) |
| 12.B.2(a) | `ε ≤ 1`: no optimal price | `exercise_12_B_2a` |
| 12.B.2(b) | `pᵐ = εc/(ε − 1)`, margin `1/ε`, deadweight loss | `ceProfit`, `ceProfit_eq`, `exercise_12_B_2b`, `exercise_12_B_2b_dwl` |
| 12.B.2(c) | Deadweight loss as `ε` varies (`x(c)` fixed) | closed form `ceDWL`, `ceDWLShape`, `ceDWL_eq`, `exercise_12_B_2c_derivation`; positive, strictly decreasing, `→ ∞` as `ε → 1⁺`, `→ 0` as `ε → ∞`, `(ε − 1)DWL → Xc(1 − 2/e)`: `exercise_12_B_2c`, `ceDWLShape_pos`, `ceDWLShape_strictAntiOn`, `ceDWLShape_tendsto_one`, `ceDWLShape_tendsto_atTop`, `ceDWLShape_scaled_tendsto` (with `ceDWL_y_bounds`, `ceDWL_rpow_eq`, `ceDWL_exp_mul`, `ceDWLShape_hasDerivAt`, `ceDWLShape_scaled_eq`); computed values `exercise_12_B_2c_eps2`, `exercise_12_B_2c_eps3` |
| 12.B.3 | Comparative statics | `implicit_slope`, `exercise_12_B_3_cost`, `exercise_12_B_3_demand` |
| 12.B.4 | Revealed preference | `exercise_12_B_4_cost`, `exercise_12_B_4_param` (correction 11) |
| 12.B.5(a) | Unit demand, no discernment: single price optimal | `unitUtility`, `unitMenu_highPrice`, `unitMenu_core`, `exercise_12_B_5a`, `exercise_12_B_5a_instance` (menu model, correction 52) |
| 12.B.5(b) | Multiple units, costless competitive resale: single price optimal | `IsResaleEquilibrium`, `isResaleEquilibrium_iff`, `exercise_12_B_5b`, `exercise_12_B_5b_instance`; resale needed: `exercise_12_B_5b_needs_resale` (correction 52) |
| 12.B.6 | Efficient subsidy `−p'(q°)q°` | `exercise_12_B_6` |
| 12.B.7(a)-(d) | Men and women | `groupBenefit`, `widgetWelfare`, `exercise_12_B_7a`, `exercise_12_B_7b`, `exercise_12_B_7c`, `exercise_12_B_7d`, `exercise_12_B_7d_one_served` |
| 12.B.8(a)-(c) | Learning by doing | `lbdProfit`, `lbdWelfare`, `exercise_12_B_8a`, `exercise_12_B_8b`, `exercise_12_B_8c` |
| 12.B.9(a)-(c) | Investment in cost reduction | `exercise_12_B_9a`, `exercise_12_B_9b`, `exercise_12_B_9c` |
| 12.B.10 | Quality given price | `exercise_12_B_10`, `consumerSurplus_strictMono` |
| 12.C.1 | In text | `exercise_12_C_1` |
| 12.C.2 | `(c, c)` with certainty is the unique NE in mixed strategies | `mbProfit`, `mbProfit_fst`, `mbProfit_snd`, `mbWin`, `mbProfit_integral`, `IsMixedPrice`, `mbPayoff`, `IsMixedBertrandNE`, `exercise_12_C_2` (lemmas `mb_ae_eq`, `mb_gap`, `mb_rival_pos`, `mb_ae_Ici_ne_zero`, `mb_top_atom`, `mb_undercut`, `mb_above_null`, `mb_below_null`, `mb_eq_dirac`; correction 30) |
| 12.C.3(a)-(b) | Discrete prices | `gridPrice`, `gridBertrandGame`, `exercise_12_C_3a`, `exercise_12_C_3b` |
| 12.C.4(a) | Pure NE with `c₁ < c₂` | `bcGame`, `bcGame_nash_iff`, `exercise_12_C_4a` (characterization, ties split), `exercise_12_C_4a_none` (no NE when firm 1's monopoly price exceeds `c₂`), `bcLinDemand`, `bcLinDemand_isBertrand`, `exercise_12_C_4a_none_instance`, `exercise_12_C_4a_drastic_instance`; ties to the low-cost firm: `bcTieProfit₁`, `bcTieProfit₂`, `exercise_12_C_4a_tieRule` (NE are `p₁ = p₂ ∈ [c₁, c₂]`, incl. `(c₂, c₂)`, firm 2 weakly dominated) (correction 31) |
| 12.C.4(b) | Grid prices: NE, undominated NE, limit | `bcGridGame`, `exercise_12_C_4b` (all NE), `exercise_12_C_4b_eqm`, `exercise_12_C_4b_dominated`, `exercise_12_C_4b_undominated`, `exercise_12_C_4b_limit` (both prices → `c₂`), `exercise_12_C_4b_instance` (correction 32) |
| 12.C.5 | All bid `v_{q+1}` is a NE and a competitive price; in every pure NE buyers `1..q` win | `ubAbove`, `ubPayoff`, `IsUBNash`, `ub_card_winners`, `exercise_12_C_5a`, `exercise_12_C_5_competitive`, `exercise_12_C_5b` (tie-breaking reading, correction 33) |
| 12.C.6, 12.C.7 | In text | `exercise_12_C_6`, `exercise_12_C_7`, `exercise_12_C_7_limits` |
| 12.C.8(a) | Best response depends only on `Q₋ⱼ` | `cbrProfit`, `IsBROn`, `cgProfit`, `IsCournotGameNE`, `IsCournotEqm`, `cgProfit_update`, `exercise_12_C_8a` |
| 12.C.8(b) | `b` need not be unique | `cbrDemandB`, `exercise_12_C_8b` |
| 12.C.8(c) | `q̂ + Q̂₋ⱼ ≥ q + Q₋ⱼ`; jumps only upward; `b' ≥ −1` | `cbr_convex_pair`, `exercise_12_C_8c`, `exercise_12_C_8c_monotone`, `exercise_12_C_8c_jump`, `exercise_12_C_8c_deriv`; instance `cbrSelLinear`, `exercise_12_C_8c_instance` |
| 12.C.8(d) | Symmetric pure NE exists | false as printed: `exercise_12_C_8d_counterexample`; corrected (compact `[0, B]`, continuity): `cbr_exists_Icc`, `cbr_symmetric_fixed_point`, `exercise_12_C_8d`, `exercise_12_C_8d_instance` (correction 14) |
| 12.C.8(e) | Multiple equilibria | `cbrDemandE`, `cbrDemandE_br`, `exercise_12_C_8e` (continuum `(t, 2 − t)`) |
| 12.C.8(f) | Conditions for uniqueness | `cbr_foc`, `cournotEqm_foc`, `exercise_12_C_8f` (differentiable `P`, `P' < 0`, convex differentiable `c`: all equilibria symmetric; plus marginal revenue nonincreasing in `Q`: unique), `exercise_12_C_8f_instance` |
| 12.C.9(a) | NE with `c₁ > c₂`; when only one firm produces | `ccLinCost`, `ccLin_ne_iff`, `exercise_12_C_9a` (unique NE: interior iff `a + c₂ > 2c₁`, else only firm 2 produces `(a − c₂)/(2b)`); also `cournot_two_costs` |
| 12.C.9(b) | Comparative statics in `c₁` | `exercise_12_C_9b` (outputs and profits `bqⱼ²`), `example_12_G_1` |
| 12.C.9(c) | Profit/revenue `= H/ε` | `exercise_12_C_9c` |
| 12.C.10(a) | Two producers ⇒ `Q*` produced inefficiently | `cc_sum_update_two`, `cc_foc`, `cc_move`, `exercise_12_C_10a` (correction 34) |
| 12.C.10(b) | Correct measure of welfare loss | `efficientCost`, `allocWelfare`, `efficientSurplus`, `efficientCost_le`, `exercise_12_C_10b` (loss `S(Q°) − W(q*)` = output loss + production inefficiency), `exercise_12_C_10b_strict`, `exercise_12_C_10_instance` |
| 12.C.10(c) | Welfare falls when `α₁` falls | `cc_lin_integral`, `exercise_12_C_10c` (`dW/dc₁ = (11c₁ − 4a − 7c₂)/(9b)`; `a = 10`, `b = 1`, `c₂ = 1`, `c₁: 5 → 9/2`); "why" verbal |
| 12.C.11(a) | `q₁ < b_c(q₂)`, `q₂ < b_c(q₁)` ⇒ `p₁ = p₂ = p(q₁ + q₂)` is a NE | `IsCournotBRc`, `cap_P_x`, `cap_P_anti`, `cap_P_concave`, `cap_pi_three`, `cap_pi_pos`, `cap_eqm_side`, `exercise_12_C_11a`, `exercise_12_C_11a_instance`; uniqueness `capacity_unique` (correction 24) |
| 12.C.11(b) | `q₁ > b_c(q₂)` or `q₂ > b_c(q₁)` ⇒ no pure NE | false as printed: `exercise_12_C_11b_counterexample_zero_capacity`, `exercise_12_C_11b_counterexample_zero_br`, `capDemandEx` (+ `_cont`, `_nonneg`, `_anti`, `_concave`, `_inv`); corrected (`q₁, q₂ > 0`, `b_c > 0`, continuous demand): `cap_undercut`, `capNE_eq`, `cap_no_eqm_side`, `exercise_12_C_11b`, `exercise_12_C_11b_instance` (correction 24) |
| 12.C.12(a) | Cross-partial sign ⇒ best responses increasing/decreasing | `sc_strictMonoOn_diff`, `sc_topkis`, `sc_foc_interior`, `exercise_12_C_12a`, `exercise_12_C_12a_unique` (correction 35) |
| 12.C.12(b) | Cournot: decreasing is the normal case | `exercise_12_C_12b`, `exercise_12_C_12b_normal`, `exercise_12_C_12b_instance`; "normal" argued verbally plus the lemma |
| 12.C.13 | `v > c + 3t`: every best response leaves all consumers buying | `exercise_12_C_13` (shares sum to one, correction 29) |
| 12.C.14(a) | `v ∈ (c + 2t, c + 3t)`: best responses, unique NE `c + t` | `exercise_12_C_14a` (`lcvBRMid`) |
| 12.C.14(b) | `v ∈ (c + 3t/2, c + 2t)`: same | `exercise_12_C_14b` (`lcvBRLow`) |
| 12.C.14(c) | `v < c + t`: unique NE `(v + c)/2`, some consumers do not buy | `exercise_12_C_14c` (with `v > c`); `exercise_12_C_14c_counterexample` (correction 26) |
| 12.C.14(d) | `v ∈ (c + t, c + 3t/2)`: unique symmetric NE `v − t/2`; asymmetric equilibria? | `exercise_12_C_14d`: all equilibria are `p₁ + p₂ = 2v − t` with `p₁, p₂ ∈ [L, U]`; asymmetric ones exist |
| 12.C.14(e) | Effect of a fall in `t` in (d) vs (a), (b) | `exercise_12_C_14e` (raises price and profit in (d), lowers them in (a), (b)) |
| 12.C.15 | Quadratic travel cost, linear city | `quadCity_prefers`, `lcDemand_eq_share`, `exercise_12_C_15` (NE `c + t`, same demand as (12.C.8)) |
| 12.C.16 | Circular city with quadratic cost; `J → ∞`; `t` falls | `circQuad_prefers`, `circQuad_beyond`, `exercise_12_C_16` (price `c + t/J²`, profit `tM/J³`), `exercise_12_C_16_limits` (correction 28) |
| 12.C.17 | Linear city with `c₁ ≤ c₂`: all equilibria, no-sales threshold `c₂ − c₁ ≥ 3t`, local statics | `IsLCNash2`, `lc2_br_mid`, `lc2_br_high`, `lc2_br`, `exercise_12_C_17`, `exercise_12_C_17_statics`; also `linearCity_two_costs`, `example_12_G_1` (correction 36) |
| 12.C.18(a) | Leader output and profit larger, total output larger, follower profit smaller | `sb_hasDerivAt`, `sb_anti_own`, `sb_anti_rival`, `sb_br_unique`, `sb_br_of_foc`, `sb_br_anti`, `exercise_12_C_18a`, `exercise_12_C_18a_instance` (correction 37) |
| 12.C.18(b) | Picture with best responses and isoprofits | graphical; its content (leader's optimum on the follower's best-response curve, to the right of Cournot) is (a) |
| 12.C.19 | Exercise 8.B.5 | `exercise_12_C_19a`, `exercise_12_C_19b` (re-exports of Chapter 8's `MWG.SimultaneousMoveGames.exercise_8_B_5a`, `exercise_8_B_5b`) |
| 12.C.20 | Proposition 12.C.2 with convex costs | `cc_convex_increment`, `exercise_12_C_20` (`c'(qⱼ*) < p(Q*) < p(qᵐ)`), `exercise_12_C_20_instance` (correction 38) |
| 12.D.1(a)-(c) | Growth, ending market, response lag | `exercise_12_D_1a`, `exercise_12_D_1b`, `exercise_12_D_1c` (correction 13) |
| 12.D.2 | In text | `exercise_12_D_2_corrected` (correction 7) |
| 12.D.3(a)-(b) | Repeated linear Cournot | `CournotNR`, `cournot_gain`, `exercise_12_D_3a`, `exercise_12_D_3b_corrected`, `exercise_12_D_3b_printed_false`, `exercise_12_D_3b_threshold` (correction 9) |
| 12.D.4(a) | Cost change: most profitable sustainable price | `rbx_le_of_below`, `rbx_update`, `rbx_lin_facts`, `exercise_12_D_4a`, `exercise_12_D_4a_monotone`, `exercise_12_D_4a_instance` (correction 40) |
| 12.D.4(b) | Cost rises from period 2: maximal period-1 price | `costChangeU`, `costChangePath`, `costChangeProfile`, `CostChangeSustains`, `costChangeValue`, `costChangeValue_on`, `costChangeValue_off`, `osValue_costChange`, `costChange_spne_iff`, `exercise_12_D_4b`, `exercise_12_D_4b_compare`, `exercise_12_D_4b_instance` (correction 40) |
| 12.D.5(a) | `δ` high: `p_H = p_L = pᵐ` | `rsValue`, `IsRSNashReversion`, `rs_state_iff`, `rbx_scaled_isBertrand`, `exercise_12_D_5a` (correction 41) |
| 12.D.5(b) | `δ̂ > 1/2`; highest `p_H` on `[1/2, δ̂)`; countercyclical prices | `rs_threshold`, `rs_high_nec`, `exercise_12_D_5b`; "what drives this" verbal (correction 41) |
| 12.D.5(c) | `δ < 1/2`: `p_H = p_L = c` | `rbx_price_eq_c`, `exercise_12_D_5c`; instance `exercise_12_D_5_instance` (correction 41) |
| 12.E.1 | Differing efficiency: need the most efficient firm be active? | No: `e1Profit`, `IsEntryStageEq`, `exercise_12_E_1` (correction 46) |
| 12.E.3 | Welfare loss of free entry in Examples 12.E.1-12.E.2; `K → 0` | `exercise_12_E_3_cournot`, `bertrandEntryOutput`, `exercise_12_E_3_bertrand` (correction 47) |
| 12.E.4 | Perfect cartel: optimal number, welfare of free entry | `exercise_12_E_4` (correction 48) |
| 12.E.5 | Circular city entry vs planner (a) entry and pricing (b) entry only | `circTravelCost`, `circTravelCost_eq`, `circWelfare`, `exercise_12_E_5`, `exercise_12_E_5_instance` (correction 49) |
| 12.E.6 | One- vs two-stage Cournot entry | `IsOneStageCournotEntryGen`, `exercise_12_E_6_two_to_one`, `exercise_12_E_6_fewer`, `exercise_12_E_6_linear`, `exercise_12_E_6_converse_fails` (correction 50) |
| 12.E.7 | One-stage price entry with `AC(q)`: competitive and efficient | `IsPriceEntryConfig`, `exercise_12_E_7` (`J* ≥ 2`), `exercise_12_E_7_efficient`, `exercise_12_E_7_instance`; false for `J* = 1`: `e7CexAC`, `exercise_12_E_7_counterexample` (correction 51) |
| 12.E.2 | In text | `exercise_12_E_2` |
| 12.F.1 | `b` weakly decreasing for large `α` | false as printed: `gaussDemand`, `gaussDemand_model`, `gaussDemand_bounds`, `gaussFOC`, `gauss_br_foc`, `gaussFOC_anti`, `gaussFOC_mono`, `exercise_12_F_1_counterexample`, `exercise_12_F_1_false`; corrected: `exercise_12_F_1_core`, `sized_br_le`, `exercise_12_F_1`, `exercise_12_F_1_instance`, `linear_br_unique`, `linear_brDecreasing` (correction 15) |
| 12.F.2(a) | Market inverse demand of `I` consumers | `exercise_12_F_2a` |
| 12.F.2(b) | One- and two-stage Cournot entry as `I → ∞`: prices, outputs, consumer surplus | `fqJ`, `linCS`, `linCS_eq`, `IsOneStageCournotEntry`, `cournot_entry_profit_bounds`, `exercise_12_F_2b`, `exercise_12_F_2b_instance` (correction 17) |
| 12.F.3 | Welfare loss `→ 0` as `K → 0` | linear model: `firstBestWelfare`, `entryWelfare_linear_general`, `exercise_12_F_3` (correction 18) |
| 12.F.4 | Differentiated products, welfare in `α`, `β` | ill-posed as printed: `dpProfit`, `IsDPBR`, `exercise_12_F_4_br`, `exercise_12_F_4_root`, `exercise_12_F_4_no_br`, `exercise_12_F_4_symmetric`, `exercise_12_F_4_indeterminate` (correction 19) |
| 12.G.1 | Cost derivatives | `exercise_12_G_1` |
| 12.AA.1 | In text | `exercise_12_AA_1_corrected` (correction 5) |
| 12.AA.2 | Prove Proposition 12.AA.4 | false as printed: `proposition_12_AA_4_false`; corrected `proposition_12_AA_4_upper`, `proposition_12_AA_4` (correction 6) |
| 12.BB.1 | In text | `exercise_12_BB_1`, `exercise_12_BB_1_instance` |
| 12.BB.2 | Indifference ⇒ welfare strictly higher under deterrence | `exercise_12_BB_2`, `exercise_12_BB_2_instance` (linear model, correction 20); "discuss generally" verbal |
| 12.BB.3 | Linear city, one or two plants, entry, price competition: equilibrium | subgames: `exercise_12_BB_3_monopoly_one`, `exercise_12_BB_3_monopoly_two`, `exercise_12_BB_3_duopoly`, `exercise_12_BB_3_coloc_two`, `exercise_12_BB_3_coloc_one`, `bb3_coloc_zero`, `bb3D`, `bb3ShareE`; equilibrium `exercise_12_BB_3`, `bb3PayOne`, `bb3PayTwo`, `exercise_12_BB_3_instance` (correction 22) |
| 12.BB.3 | Parameter dependence; welfare vs no entrant and vs one-plant restriction | threshold `F ≷ tM/2` in `exercise_12_BB_3`; `exercise_12_BB_3_welfare`, `bb3Welfare`, `bb3_transport_one`, `bb3_transport_two` |
