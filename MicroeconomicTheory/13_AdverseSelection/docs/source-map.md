# Source map

Mas-Colell, Whinston and Green, *Microeconomic Theory*, Chapter 13, "Adverse Selection,
Signaling, and Screening", pp. 436-476, with Appendix A. Printed pages; Lean names relative to
`MWG.AdverseSelection` (signaling and screening names in `SigModel`, Appendix A names in
`SignalingGame`). Types follow a probability measure `μ` on `ℝ` concentrated on `[θ̲, θ̄]`.
The games of 13.C, 13.D and Appendix A are bespoke models; their equilibrium conditions use
Chapter 8's `IsNashEquilibrium` for the firms' or responders' stage (corrections, item 5).
No item is **OPEN**. Departures are
in [corrections](corrections.md).

## Section 13.A and 13.B: adverse selection

| Source | Claim | Lean |
| --- | --- | --- |
| 13.A, pp. 436-437 | Introduction | verbal |
| p. 438, footnotes 1-3 | The model: types on `[θ̲, θ̄]`, `F` nondegenerate, home earnings `r(θ)`; random productivity; quasilinear disutility | `TypeDist`, `acceptSet`, `TypeDist.meanType_mem`, `TypeDist.integrable_id`; footnotes 1-3 verbal |
| p. 438, footnote 4 | Full-information competitive equilibrium `w*(θ) = θ`; other equilibria `w*(θ) ≥ θ` for non-employed types | `typeMarketClears`, `typeMarket_clears_iff` (the wage must also be `< r(θ)`), `fullInfo_eq` |
| (13.B.1), p. 438, footnote 5 | Aggregate surplus; maximized by employing `{θ : r(θ) ≤ θ}` | `aggSurplus`, `optEmployment`, `optEmployment_eq`, `employment_le`, `integrable_employment`, `aggSurplus_le_opt`, `aggSurplus_lt_opt`; footnote 5 verbal |
| (13.B.2), p. 439 | `Θ(w)` | `acceptSet`, `measurableSet_acceptSet` |
| (13.B.3), p. 439 | Labor demand | `laborDemand`, `laborDemand_unbounded`, `laborDemand_profit` |
| Definition 13.B.1, p. 439 | Competitive equilibrium; `E[θ]` when `Θ* = ∅` | `IsCompEq`, `eqWages`, `condMean`, `meanType`, `mem_eqWages_iff` (correction 3) |
| pp. 439, 444 | Profit `M(E[θ | Θ(w)] - w)` | `firmProfit`, `firmProfit_eq_setIntegral`, `firmProfit_eq`, `mem_eqWages_iff_profit`, `firmProfit_of_null` |
| p. 440 | `r(θ) = r`: `w* = E[θ]`, all or nobody employed, not Pareto optimal | `condMean_const`, `eqWages_const`, `acceptSet_const`, `const_inefficient`; counterexample with an atom `const_atom_counterexample`, `atomMeas`, `integral_atomMeas`, `atomMeas_typeDist` (correction 1) |
| Footnote 6, p. 440 | Missing markets, externality | verbal |
| p. 441 | Adverse selection model: `r ≤ θ`, `r` strictly increasing, density `f > 0`; continuity of `E[θ | r(θ) ≤ w]` | `HasPosDensity`, `RegularModel` (with continuity of `r`, correction 2), `continuous_firmProfit`, `RegularModel.continuous`, `measure_acceptSet_pos`, `measure_acceptSet_inter`, `condMean_of_superset` |
| (13.B.6), Figure 13.B.1, p. 441 | `w* = E[θ | r(θ) ≤ w*]` | `mem_eqWages_iff`, `RegularModel.mem_eqWages_iff`; figure graphical |
| p. 441 | `E[θ | r(θ) ≤ w]` increases in `w` on `[r(θ̲), r(θ̄)]`, minimum `θ̲`, maximum `E[θ]` | `condMean_of_superset` (maximum); nondecreasing for `r` monotone: `condMean_acceptSet_mono`, `condMean_mono_of_sep`, `condMean_ge`; strictly increasing on `[r(θ̲), r(θ̄)]` in the regular model: `RegularModel.condMean_acceptSet_strictMono`, `condMean_lt_of_sep` |
| Footnote 7, p. 441 | No wage below `r(θ̲)` is an equilibrium | `not_mem_eqWages_of_lt`, `acceptSet_inter_eq_empty`, `firmProfit_of_lt` |
| Footnote 8 | Other diagram | Exercise 13.B.1 |
| Figure 13.B.2, p. 442 | `r(θ̲) = θ̲`: `w* = θ̲`, only type `θ̲` employed | `acceptSet_inter_eq_singleton`, `mem_eqWages_rl_iff`, `firmProfit_rl` |
| Example 13.B.1, p. 442 | `E[θ | αθ ≤ w] = w/(2α)`; `α > 1/2`: `E[θ | r ≤ 0] = 0`, `E[θ | r ≤ w] < w` | `akerlofR`, `acceptSet_akerlofR`, `akerlof_regular`, `example_13_B_1`, `example_13_B_1_zero`, `example_13_B_1_high`, `example_13_B_1_lt`, `example_13_B_1_unravel`; uniform measure `unifMeas`, `unifMeas_apply`, `unifMeas_isProb`, `unifMeas_compl`, `unifMeas_typeDist`, `unifMeas_density`, `unifMeas_Iic`, `unifMeas_setIntegral_Iic`, `unifMeas_mean`, `Iic_inter_Icc_of_le` |
| Footnote 9 | Payoffs equal to no market | `proposition_13_B_1_ii_payoffs` |
| Footnote 10 | Akerlof's `α = 2/3` | `example_13_B_1_akerlof` |
| Figure 13.B.3, p. 442 | Multiple equilibria | `example_13_B_1_lowα` (`W* = {0, 1}`); figure graphical |
| p. 443 | Equilibria are Pareto ranked | `pareto_ranked` |
| p. 443, footnote 11 | Two-firm wage game; single type is Bertrand | `wageShare`, `wageGame`, `WageBestReply`, `isNash_wageGame_iff`, `wageShare_*`, `worker_best`; footnote 11 is `wageGame_unique` with one type |
| Proposition 13.B.1(i), pp. 443-444 | Unique pure SPNE `(w*, w*)` | `proposition_13_B_1_i` (with `r` continuous), `proposition_13_B_1_i_outcome`, `wageGame_unique`, `WageBestReply.profit_nonpos`, `WageBestReply.nonneg`, `RegularModel.firmProfit_neg_of_gt_max`, `firmProfit_zero_nonneg`, `firmProfit_nonpos_of_gt`, `firmProfit_neg_of_gt`, `firmProfit_neg_of_ae_lt`, `setIntegral_pos_of_ae_pos`; instance `proposition_13_B_1_i_instance`; counterexample without continuity `counterexample_13_B_1_i`, `jumpR`, `jumpR_*` (correction 2) |
| p. 443 | `w* = Max W*` exists | `RegularModel.exists_isGreatest_eqWages`, `RegularModel.firmProfit_pos_of_lt_θl` |
| Proposition 13.B.1(ii), pp. 444-445 | SPNEs are `{wⱼ ≤ w*}`, several, payoffs as in the highest-wage equilibrium | `proposition_13_B_1_ii`, `proposition_13_B_1_ii_multiple`, `proposition_13_B_1_ii_payoffs`, `wageGame_flat`; instance `example_13_B_1_spne` |
| Footnote 12, Figure 13.B.4 | Acceptance when indifferent; pathological case | `acceptSet` convention; the hypothesis `hgap` of `proposition_13_B_1_i` |
| p. 445, footnote 13 | Firms' sophistication | verbal; footnote 13 is Exercise 13.B.6 (`WilsonEconomy.exercise_13_B_6d_i`) |
| pp. 445-446 | Constrained Pareto optimum; full PO is constrained PO | `IsParetoImprovement`, `IsConstrainedPO`, `BudgetOK`, `budget_wu_le`, `scheme_payoff`; the second claim is immediate (verbal) |
| p. 446, footnote 14 | Authority implements the highest-wage equilibrium; dominated equilibria are not constrained PO | `highest_wage_implementable`, `dominated_not_constrainedPO`; footnote 14 verbal |
| Proposition 13.B.2, pp. 447-448 | Highest-wage equilibrium is a constrained PO | `proposition_13_B_2`, `MonoModel`, `RegularModel.toMono`, `MonoModel.isConstrainedPO`, `MonoModel.profit_add_lt`, `MonoModel.firmProfit_neg_of_gt_max`, `firmProfit_of_full`, `mean_mem_eqWages`; instance `proposition_13_B_2_instance` |
| (13.B.7)-(13.B.12), p. 447 | The scheme `w_u(θ̂)`, `w_e(θ̂)` and its value at `θ*` | `schemeWu`, `schemeWe`, `scheme_13_B_7_8`, `scheme_13_B_11_12`, `scheme_at_θstar` |
| Footnote 15 | No budget surplus | `footnote_15` |
| Footnote 16 | `r(θ) > θ` for some `θ` | `exercise_13_B_10` |
| (13.B.13), pp. 448-449, footnotes 17-18 | Weighted welfare; mandated employment raises surplus but hurts `θ̄` | `weightedWelfare`, `weightedWelfare_const`, `mandate_all`; footnotes verbal |
| p. 449, footnote 19 | Ex ante constrained optimum | verbal |
| (13.B.14)-(13.B.17), pp. 449-450 | Revelation mechanisms reduce to `(w_e, w_u)` schemes | `MechIR`, `MechBB`, `MechIC`, `MechBudget`, `mechanism_17_of_14_15`, `mechanism_exists_t`, `mechanism_two_outcome`, `mechanism_scheme` |

## Section 13.C: signaling

| Source | Claim | Lean |
| --- | --- | --- |
| p. 450 | Costless test | Exercise 13.C.1 (`exercise_13_C_1`) |
| p. 450 | Model: two types, `λ`, cost `c(e, θ)` | `SigModel`, `SigModel.Valid`, `θ`, `Eθ`, `expProd`, `Valid.c_lt_of_pos`, `Valid.c_le`, `Valid.c_pos`, `Valid.c_nonneg`, `Valid.Eθ_mem`, `Valid.expProd_mem`, `expProd_one`, `expProd_zero`, `expProd_lam` (corrections 6-7) |
| p. 451, Figure 13.C.1 | The game tree | `workerPay`, `offerProfit`, `IsPBE` |
| p. 452, footnote 20 | PBE conditions (i)-(iii) | `IsPBE`, `BayesOnPath`; equivalence with sequential equilibrium not formalized (stated without proof in the book) |
| p. 452 | Bertrand wages `μ(e)θ_H + (1 - μ(e))θ_L` | `bertrand_iff`, `bertrand_wage`, `offerProfit_rc`, `bertrandOffer`, `bertrandOffer_nash`, `bertrandOffer_max`, `IsPBERed`, `redPay`, `Valid.isPBERed_of_isPBE`, `Valid.isPBE_of_isPBERed`, `Valid.exists_isPBE_iff` |
| p. 453, Figures 13.C.2-13.C.3 | Single crossing; `w(e) ∈ [θ_L, θ_H]` | `Valid.sc`, `Valid.wage_mem`; figures graphical |
| Lemma 13.C.1, p. 453 | Wages `θ_H`, `θ_L` | `lemma_13_C_1`, `lemma_13_C_1_r0` |
| Lemma 13.C.2, p. 454 | `e*(θ_L) = 0` | `lemma_13_C_2`, `Valid.low_payoff` |
| pp. 454-455, Figures 13.C.4-13.C.7 | Separating PBE with `e*(θ_H) ∈ [ẽ, e₁]` and the supporting beliefs | `sepBelief`, `separating_sep`, `separating_sepBelief`, `separating_iff`, `separating_interval` |
| p. 455 | Pareto ranking of separating equilibria | `separating_pareto_ranked`, `separating_payoffs` |
| p. 456, Figure 13.C.8 | Comparison with no signaling; dependence on `λ` | `separating_vs_nosignal`, `high_type_worse_as_lam_to_one`; independence of `λ` is visible in `separating_iff` |
| pp. 456-457, Figures 13.C.9-13.C.10 | Pooling PBE at `e ∈ [0, e']`; Pareto dominated by no signaling | `poolBelief`, `pooling_iff`, `pooling_interval`, `pooling_dominated` |
| pp. 457-458 | Reasonable beliefs select `ẽ`; Cho-Kreps | `low_never_above`, `refined_separating`; Appendix A below |
| pp. 458-459, Figure 13.C.11 | Banning signaling; cross-subsidization | `exercise_13_C_3`, `crossWage`, `crossModel`, `crossModel_valid`, `crossModel_cL`, `crossModel_cH`, `crossModel_cH_lt`, `crossModel_separating`, `crossModel_pooling` (correction 11) |
| Exercise 13.C.3, p. 459 | Example: cross-subsidy improves, banning does not | `exercise_13_C_3` |
| Small type, pp. 459-460, Figure 13.C.12 | `r ∈ (θ_L, θ_H)`, `E[θ] < r`: pooling at `0` with no employment, separating range `[ẽ, e₂]`, Pareto dominance | `smalltype_pooling`, `smalltype_separating`, `smalltype_pareto` |

## Section 13.D: screening

| Source | Claim | Lean |
| --- | --- | --- |
| p. 460, footnotes 21-22 | Model | `SigModel` with `r = 0`; footnote 21 verbal; footnote 22 is Exercise 13.D.1 (`exercise_13_D_1`) |
| p. 461, footnotes 23-24 | Two-stage game, tie-breaking rules | `util`, `ValidMenu`, `Chooses`, `share`, `typeProfit`, `screenProfit`, `IsScreenEq`, `chooses_unique`, `exists_chooses`, `chooses_of_strict`, `typeProfit_of_chooses`, `typeProfit_of_not`, `typeProfit_empty`, `typeProfit_capture`, `typeProfit_add`, `share_add`, `share_nonneg`, `share_le_one`, `screenProfit_empty`; footnote 23 (SPNE = PBE = SE) not formalized; footnote 24 is Exercise 13.D.4 (`exercise_13_D_4`) |
| Proposition 13.D.1, pp. 461-462, Figure 13.D.1 | Observable types: `(θ_i, 0)`, zero profits | `IsTypeEq`, `IsTypeEq.symm`, `proposition_13_D_1`, `proposition_13_D_1_exists` |
| p. 462, Figure 13.D.2 | The full-information outcome cannot arise; break-even lines | verbal |
| p. 462 | Both types accept some contract in any equilibrium | `IsScreenEq.exists_bothEmployed` (`BothEmployed` now only names the chosen contracts) |
| Lemma 13.D.1, pp. 462-463 | Zero profits | `lemma_13_D_1`, `zero_profits_of_employed`, `screenProfit_add`, `IsScreenEq.nonneg`, `IsScreenEq.symm`, `BothEmployed.symm`, `chosen_valid` |
| Lemma 13.D.2, p. 463, Figure 13.D.3 | No pooling equilibrium | `lemma_13_D_2`, `exists_high_dev`, `screenProfit_capture_high` |
| Lemma 13.D.3, pp. 463-464, Figure 13.D.4 | `w_L = θ_L`, `w_H = θ_H` | `lemma_13_D_3`, `no_low_capture`, `screenProfit_capture_low_pos` |
| Lemma 13.D.4, p. 464, Figure 13.D.5 | Low type gets `(θ_L, 0)` | `lemma_13_D_4` |
| Lemma 13.D.5, pp. 464-465, Figure 13.D.6 | High type gets `(θ_H, t̂_H)` | `lemma_13_D_5` |
| Proposition 13.D.2, p. 465 | Both together | `proposition_13_D_2` |
| pp. 465-466, Figures 13.D.7-13.D.8 | Nonexistence via a pooling contract or a pair of contracts | `no_eq_of_pooling_deviation`, `no_eq_of_pair_deviation`, `screenModel`, `screenModel_valid`, `nonexistence_pooling_instance`, `nonexistence_pair_instance` |
| Figure 13.D.7(a), p. 465 | Existence when no deviation is profitable | Existence criterion `sepMenu`, `NoProfitableDeviation`, `isScreenEq_sepMenu`; concrete SPNE `figure_13_D_7a` (`screenModel (1/5)`), `screenModel_cL`, `screenModel_cH`; instance of Proposition 13.D.2 and Lemma 13.D.1 `proposition_13_D_2_instance` |
| p. 466, footnote 25 | Welfare; constrained optimality when an equilibrium exists | Pareto inefficiency `screening_inefficient`; low type worse `screening_low_worse`; high type at least as well off when an SPNE exists `screening_high_better`; constrained optimality in the true form `screening_no_strict_improvement`, `ScreenFeasible`; footnote 25 and correction 13: `footnote_25_counterexample`, `linModel`, `linModel_cL`, `linModel_cH`, `linModel_valid` |
| Small type, pp. 466-467 | Wilson equilibria, Riley, Maskin-Tirole | verbal |

## Appendix A: reasonable-beliefs refinements

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 467-468 | Signaling games; PBE (i)-(iii) | `SignalingGame`, `IsBeliefOn`, `responseGame`, `IsPBE`, `IsPBE.mem_eqResponses`, `eqPayoff` |
| (13.AA.1), p. 468, footnotes 26-27 | Strict dominance, `Θ(a)`, reasonable beliefs | `DominatedFor`, `typesUndominated`, `ReasonableBeliefs`; footnotes verbal |
| p. 469 | In the education model `Θ(e) = {θ_L, θ_H}` | `education_Theta_all` |
| (13.AA.2), p. 469, footnotes 28-29 | `S*(Θ̂, a)`, `Θ*(a)` | `eqResponses`, `typesUndominatedStar`; footnotes verbal |
| pp. 469-470 | `S*(Θ, e) = [θ_L, θ_H]`; `e > ẽ` dominated for `θ_L`; only `ẽ` survives; pooling eliminated (Figure 13.AA.1) | `education_Sstar`, `low_never_above`, `refined_separating`, `pooling_eliminated` |
| (13.AA.3), p. 471 | Equilibrium dominance, `Θ**(a)`; (13.AA.2) implies (13.AA.3) | `EqDominated`, `typesNotEqDominated`, `eqDominated_of_dominated`, `typesNotEqDominated_subset` |
| p. 471, Figure 13.AA.2 | Equilibrium dominance gives the best separating equilibrium | `EqDomEd`, `notEqDomEd`, `AdmissibleOn`, `icSetEd`, `ViolatesICEd`, `eqPay`, `violates_of_high`, `education_IC_unique`, `education_IC_exists`, `education_IC_instance` |
| (13.AA.4), p. 471 | Intuitive criterion; reasonable beliefs imply passing it | `icTypes`, `ViolatesIC`, `passesIC_of_reasonable` (correction 8) |
| Example 13.AA.1, pp. 471-472 | Passes the intuitive criterion without reasonable beliefs | `exGame`, `exG`, `exPrior`, `exGame_payoff`, `exGame_nash_iff`, `pointMass`, `pointMass_belief`, `pointMass_resp`, `exGame_eqResponses`, `example_13_AA_1_eqdom`, `exResp`, `exBelief`, `exPrior_belief`, `exGame_eqPayoff`, `example_13_AA_1_pbe`, `example_13_AA_1_ic`, `example_13_AA_1_no_reasonable` (correction 10) |
| p. 472 | Two types: the notions coincide | `two_types_singleton`, `two_types_reasonable` (correction 9); instance `twoTypes_instance` (`twoGame`, `twoG`, `twoGame_payoff`, `twoGame_nash_iff`, `boolPoint`, `boolPoint_belief`, `twoGame_one_mem`, `twoResp`, `twoBelief`) |
| p. 472 | Three or more types: no unique prediction; divinity, D1, stability | Exercise 13.AA.1 (`exercise_13_AA_1`); divinity, D1, stability verbal |

## Exercises

| Source | Claim | Lean |
| --- | --- | --- |
| Exercise 13.B.1, p. 473 | Equilibria read off the diagram `r(θ̂)`, `E[θ \| θ ≤ θ̂]`, `θ̂`: `W*` is the no-employment wage `E[θ] < r(θ̲)`, or `r(θ̲) = θ̲`, or `r(θ̂)` with `θ̂ ∈ (θ̲, θ̄)` and `r(θ̂) = E[θ \| θ ≤ θ̂]`, or the all-employed wage `E[θ] ≥ r(θ̄)` | `exercise_13_B_1`, `exercise_13_B_1_cutoff`, `MonoModel.acceptSet_cutoff`, `exB_condMean_congr`, `exB_ae_eq_of_inter`, `exB_condMean_empty` (correction 14) |
| Exercise 13.B.1, p. 473 | All-employed equilibrium iff `r(θ̄) ≤ E[θ]`, wage `E[θ]` | `exercise_13_B_1_full` |
| Exercise 13.B.1, p. 473 | Pareto optimal allocation employs `{θ : r(θ) ≤ θ}` | `exercise_13_B_1_po` |
| Exercise 13.B.1, p. 473 | Non-monotone `r`: a crossing need not be an equilibrium | `exercise_13_B_1_nonmono`, `exB_le_condMean` |
| Exercise 13.B.1, p. 473 | Diagrams for Figures 13.B.1-13.B.3 | graphical (the equilibria shown are covered by `exercise_13_B_1`) |
| Exercise 13.B.2, p. 473 | Every competitive equilibrium is Pareto inefficient (aggregate surplus strictly below the optimum) | `exercise_13_B_2`, `exB_eq_zero_of_cross`, `exB_lt_near`, `exB_gt_near`, `exB_integrable`; instance `exercise_13_B_2_instance`, `exB_unif_condMean_Iic` |
| Exercise 13.B.3, p. 473 | Positive selection model | `AntiModel`, `AntiModel.measure_acceptSet_pos` |
| Exercise 13.B.3(a), p. 473 | The more capable workers are the ones who work | `exercise_13_B_3a` |
| Exercise 13.B.3(b), p. 473 | `r(θ) > θ` for all `θ`: the equilibrium is Pareto efficient (unique, `w* = E[θ]`, no employment) | `exercise_13_B_3b`, instance `exercise_13_B_3b_instance`; reading `r(θ) < θ`: `exercise_13_B_3b_lt`, `exercise_13_B_3b_lt_instance` |
| Exercise 13.B.3(c), p. 473 | An equilibrium with positive employment has too much employment | `exercise_13_B_3c` (with `θ̂ ∈ (θ̲, θ̄)`), instance `exercise_13_B_3c_instance`; counterexample `exercise_13_B_3c_counterexample` (correction 15) |
| 13.B.4 | No-trade theorem | `exercise_13_B_4`, `sum_pos_of_fibers` (finite probability space) |
| 13.B.5(a) | Equilibria with `E[θ | ∅] = θ̲` | `eqWagesB5`, `exercise_13_B_5a` |
| 13.B.5(b) | Pareto dominance of full employment | `exercise_13_B_5b` |
| 13.B.5(c) | SPNE of the wage game | `exercise_13_B_5c` |
| 13.B.5(d) | Highest-wage equilibrium constrained PO | `exercise_13_B_5d` |
| 13.B.10 | Proposition 13.B.2 with `r(θ) > θ` | `exercise_13_B_10` |
| 13.C.3 | In text | `exercise_13_C_3` |
| 13.C.5(a) | When the consumer buys | `exercise_13_C_5a` |
| 13.C.5(b) | No separating PBE with advertising | `exercise_13_C_5b` |
| 13.C.6(a) | Pooling loan rate and comparative statics | `exercise_13_C_6a` |
| Exercise 13.B.6(a), p. 474 | Firm `γ` hires iff `γμ ≥ w`; `z(w, μ) = N∫_{w/μ}^∞ g` | `FirmDensity`, `wilHireSet`, `wilDemand`, `wil_hire_best`, `exercise_13_B_6a`, `expDensity` |
| Exercise 13.B.6(b), p. 474 | `z*` increasing at `w̃` iff the elasticity of `μ` exceeds 1 | `exercise_13_B_6b`, `exercise_13_B_6b_instance` (correction 17) |
| Exercise 13.B.6(c), p. 474 | `s(w) = F(r⁻¹(w))`, `z*(w*) = s(w*)`; the highest-wage equilibrium Pareto dominates the others | `WilsonEconomy`, `WilsonEconomy.mu`, `WilsonEconomy.zstar`, `WilsonEconomy.supply`, `WilsonEconomy.IsCE`, `WilsonEconomy.Valid`, `WilsonEconomy.exercise_13_B_6c`, `exercise_13_B_6_instance` |
| Exercise 13.B.6(d)(i), p. 474 | Only the highest-wage equilibrium can be an SPNE outcome | `WilsonEconomy.offerPay`, `WilsonEconomy.IsSPNE`, `WilsonEconomy.exercise_13_B_6d_i`, `exercise_13_B_6_instance` |
| Exercise 13.B.6(d)(ii), p. 474 | It is an SPNE iff `z*(w) ≤ z*(w*)` for all `w > w*` | "only if" `WilsonEconomy.exercise_13_B_6d_ii_necessary`; "if" false: `exercise_13_B_6d_ii_counterexample`; corrected `WilsonEconomy.exercise_13_B_6d_ii_corrected`, `WilsonEconomy.exercise_13_B_6d_ii_full_employment` (correction 18) |
| Exercise 13.B.7, p. 474 | Interventions reducing / increasing employment; budget | `ReducesEmployment`, `IncreasesEmployment`, `budgetOK_iff`, `exB7_reduces_exists`, `exB7_reduces_of`, `exB7_increases_exists`, `exB7_increases_of`, `exB7_pay_emp`, `exB7_pay_unemp`, `exB7_profit_of_empty` |
| Exercise 13.B.7, p. 474 | A Pareto-improving reduction exists iff one of the form `(w*, ŵ_u)`, `ŵ_u > 0`, does | `exercise_13_B_7_reduce` (instance: `exercise_13_B_9`) |
| Exercise 13.B.7, p. 474 | A Pareto-improving increase exists iff one of the form `(ŵ_e, 0)`, `ŵ_e > w*`, does | `exercise_13_B_7_increase`, `MonoModel.levelNull`; instance `exercise_13_B_7_instance` (correction 16) |
| Exercise 13.B.7, p. 474 | Simple proof of Proposition 13.B.2 | `exercise_13_B_7_proposition_13_B_2`, `exB7_profit_congr`, `MonoModel.measureReal_acceptSet_lt_one` |
| Exercise 13.B.8, p. 474 | Interventions conditioned on observed purchases `x(θ)` | `xNetRev`, `XBudgetOK`, `IsXParetoImprovement`, `xNetRev_const`, `xBudgetOK_const_iff`, `exB8_integral_lt` |
| Exercise 13.B.8, p. 474 | A Pareto-improving intervention exists even at the highest-wage equilibrium | false in the model of p. 446: `exercise_13_B_8_false`; corrected `exercise_13_B_8`, instance `exercise_13_B_8_instance`; constant `x`: `exercise_13_B_8_const_x` (correction 19) |
| Exercise 13.B.9, p. 474 | Two-type positive selection model | `twoPt`, `integral_twoPt`, `twoPt_typeDist`, `meanType_twoPt`, `firmProfit_twoPt` |
| Exercise 13.B.9, p. 474 | The highest-wage equilibrium need not be constrained Pareto optimal | `exercise_13_B_9` |
| Exercise 13.B.9, p. 474 | Exact condition for a full-employment equilibrium to be constrained Pareto optimal: `r(θ_L) ≤ θ_L` | `exercise_13_B_9_exact`, instance `exercise_13_B_9_cpo_instance` |
| Exercise 13.C.1, p. 474 | In any SPNE all types test and non-testers are offered at most `θ̲` | `testNonTakers`, `IsTestEq`, `exercise_13_C_1`, `exercise_13_C_1_instance` (correction 20) |
| Exercise 13.C.2, p. 475 | Separating and pooling PBE with productivity `θ(1 + μe)`; relation to full information | `SigModel.prodWage`, `SigModel.IsPBEProd`, `SigModel.IsPBEProdRed`, `SigModel.Valid.exists_isPBEProd_iff`, `SigModel.fullPay`, `SigModel.IsFullInfoChoice`, `SigModel.exercise_13_C_2_separating`, `SigModel.exercise_13_C_2_full_info`, `SigModel.exercise_13_C_2_distorted`, `SigModel.exercise_13_C_2_pooling`, `SigModel.exercise_13_C_2_pooling_low`, `SigModel.exercise_13_C_2_instance`, `SigModel.exercise_13_C_2_full_info_instance` |
| Exercise 13.C.4, p. 475 | Continuum of types, `c = e²/θ`: "the (unique) PBE" | false: separating PBE `exercise_13_C_4_separating` (`sepEduc`, `sepWage`, `sepEduc_sq`, `sepWage_sepEduc`, `sepEduc_injOn`) and pooling PBE `exercise_13_C_4_pooling` (`poolWage`) both exist, `exercise_13_C_4_not_unique`, instance `exercise_13_C_4_instance`; corrected: the separating PBE is unique, `exercise_13_C_4_unique_separating`, `eq_of_sq_bound`; model `IsPBEC4` (correction 26) |
| Exercise 13.C.6(b)(i), p. 475 | Payoff `p_t(Π - R) - (1 + ρ)x` | `LoanModel`, `LoanModel.Valid`, `LoanModel.entPay`, `LoanModel.exercise_13_C_6b_i`, `LoanModel.exercise_13_C_6b_bank_zero_profit` |
| Exercise 13.C.6(b)(ii), p. 475 | Best separating PBE: `x* = p_B(p_GΠ - (1 + r))/(p_G(1 + ρ) - p_B(1 + r))`; rises with `p_B`, `p_G`, `Π`, falls with `r`, independent of `λ` | `LoanModel.repay`, `LoanModel.gamePay`, `LoanModel.IsLoanPBE`, `LoanModel.xStar`, `LoanModel.exercise_13_C_6b_ii_separating`, `LoanModel.exercise_13_C_6b_ii_best`, `LoanModel.exercise_13_C_6b_ii_statics`, `LoanModel.exercise_13_C_6b_ii_statics_instance` |
| Exercise 13.C.6(b)(iii), p. 476 | Both types' payoffs compared with (a) | `LoanModel.poolPay`, `LoanModel.exercise_13_C_6b_iii`, `LoanModel.exercise_13_C_6b_iii_instance` |
| Exercise 13.D.1, p. 476 | Model: output `θ(1 + μt)`; general two-type screening game | `prodGame`, `surplus`, `prodGame_inj`, `prodGame_P`, `prodGame_zero`, `θ_pos`; `ScrGame`, `ScrGame.Menu`, `ScrGame.Chooses`, `ScrGame.Inj`, `ScrGame.typeProfit`, `ScrGame.profit`, `ScrGame.IsEq`, `ScrGame.IsEq.zero`, `ScrGame.typeProfit_capture`, `ScrGame.profit_add` and the other `ScrGame.*` lemmas |
| Exercise 13.D.1, p. 476 | SPNE characterization: zero profits, low type gets her full-information contract, high type's task maximizes surplus among tasks the low type strictly dislikes, no pooling | `exercise_13_D_1` |
| Exercise 13.D.1, p. 476 | Observable types; comparison | `obsGame`, `obsGame_inj`, `exercise_13_D_1_observable`, `exercise_13_D_1_observable_exists`, `exercise_13_D_1_observable_instance`, `exercise_13_D_1_compare` |
| Exercise 13.D.1, p. 476 | Existence criterion; instances; nonexistence | `prod_isEq`, `quadModel`, `quadModel_cL`, `quadModel_cH`, `quadModel_valid`, `exercise_13_D_1_fullinfo`, `exercise_13_D_1_distorted`, `linModel9`, `linModel9_valid`, `exercise_13_D_1_nonexistence` (correction 21) |
| Exercise 13.D.2(a), p. 476 | Policies `(M, R)` are wealth levels in the two states | `policyWealth`, `exercise_13_D_2a`, `exercise_13_D_2a_log` |
| Exercise 13.D.2(b), p. 476 | SPNE outcomes: high risk fully insured at fair price, low risk partially insured on the high type's indifference curve | `RSModel`, `RSModel.q`, `RSModel.V`, `RSModel.Pr`, `RSModel.abar`, `RSModel.game`, `RSModel.Valid`, `RSModel.rs_characterization`, `RSModel.rs_point_lt`, `RSModel.rs_point_unique`, `RSModel.insModel`, `RSModel.ins_participation`, `RSModel.exercise_13_D_2b`, `RSModel.exercise_13_D_2b_outcome` (correction 22) |
| Exercise 13.D.2(b), p. 476 | Does an equilibrium necessarily exist? No | `RSModel.rs_isEq`, `RSModel.rs_no_eq`, `RSModel.log_valid`, `RSModel.log_isEq`, `RSModel.log_no_eq`, `RSModel.exercise_13_D_2b_exists`, `RSModel.exercise_13_D_2b_nonexistence` |
| Exercise 13.D.3(a), p. 476 | Deterministic observable output: each type paid her output | `exercise_13_D_3a`, `exercise_13_D_3a_exists` |
| Exercise 13.D.3(b), p. 476 | Random output, risk neutral: full-information outcome | `rnProb`, `rnMean`, `rnGame`, `RnGame.inj`, `RnGame.P_eq`, `RnGame.zero`, `exercise_13_D_3b`, `exercise_13_D_3b_exists` |
| Exercise 13.D.3(c), p. 476 | Strictly risk averse: Rothschild-Stiglitz contracts; existence and nonexistence | `RSModel.labModel`, `RSModel.lab_participation`, `RSModel.exercise_13_D_3c`, `RSModel.exercise_13_D_3c_exists`, `RSModel.exercise_13_D_3c_nonexistence` (correction 23) |
| Exercise 13.D.4, p. 476 | Free entry, single contracts: equilibrium notion | `offered`, `ChoosesS`, `gross`, `feProfit`, `IsFreeEntryEq`, `choosesS_unique`, `exists_choosesS`, `choosesS_of_strict`, `offered_finite`, `offered_update_none`, `ncard_pos_of`, `update_finite`, `IsFreeEntryEq.no_entry`, `IsFreeEntryEq.active_nonneg` |
| Exercise 13.D.4, p. 476 | Characterization: `(θ_L, 0)`, `(θ_H, t̂_H)`, no pooling; existence; nonexistence | `exercise_13_D_4`, `feProfile`, `fe_exists`, `fe_no_eq_of_pooling`, `exercise_13_D_4_lin`, `exercise_13_D_4_pair`, `exercise_13_D_4_nonexistence` (correction 24) |
| Exercise 13.AA.1, p. 476 | Three types, `r = 0`: two PBE with different outcomes pass the intuitive criterion | `aaGame`, `aa_payoff`, `aa_nash_iff`, `aa_eqResponses`, `aa_passes_ic`, `aa_pbe1`, `aa_pbe2`, `exercise_13_AA_1` and the `aa*` definitions (correction 25) |
