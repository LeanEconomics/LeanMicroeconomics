# Source map

Andreu Mas-Colell, Michael D. Whinston and Jerry R. Green, *Microeconomic Theory*, Chapter 11,
"Externalities and Public Goods", pp. 350-382. Printed pages; Lean names relative to
`MWG.ExternalitiesPublicGoods`. All definitions, examples, mathematical claims of the text (small
type and footnotes included), Appendix A and every end-of-chapter exercise subpart (11.B.1-11.E.7;
the only in-text exercise is 11.E.4) are covered. Purely verbal discussion and figures are
identified below. No item is OPEN; two cited results of Chapter 23 (Myerson-Satterthwaite in
footnote 18, the Green-Laffont characterization behind p. 374) are left to that chapter
(correction 18). Departures are numbered as in [corrections](corrections.md). Results imported
from Chapter 10 (`MWGCompetitiveMarkets`: `IsFOCSol`, `isFOCSol_unique`, `foc_max_iff`,
`foc_max_necessary`, `foc_local_necessary`, `foc_tangent_le`) and Chapter 8
(`MWGSimultaneousMoveGames`: `WeaklyDominant`, `WeaklyDominates`, `IsNashEquilibrium`, with
Chapter 7's `NormalForm`) are named with their package, at the worktree's current commit.

## Tools

| Source | Claim | Lean |
| --- | --- | --- |
| Footnote 4, p. 353; pp. 360, 366 (via Section 10.D) | Quasilinear economy with a common level: Pareto optimal iff aggregate surplus maximized | `QLAlloc`, `QLFeasible`, `QLPareto`, `qlSurplus'`, `ql_pareto_iff`, `ql_pareto_exists` |
| pp. 356-357 | Take-it-or-leave-it offers: proposer maximizes joint surplus, responder at reservation | `IsTIOLIOffer`, `tioli_iff` |
| (11.B.1)-(11.B.4) and analogues | Kuhn-Tucker on `ℝ₊` (from Chapter 10's `foc_max_iff`); uniqueness; monotone up to the maximizer; `φ'' < 0` gives decreasing `φ'` | `kt_max_iff`, `kt_isMax_iff`, `kt_max_unique`, `kt_strict_max`, `strictMonoOn_Icc_of_deriv_pos`, `kt_strictMonoOn`, `strictAntiOn_of_second_deriv_neg` (correction 12) |
| Exercises 11.B.5, 11.D.2, 11.D.4 | Tangent inequalities for convex/concave functions of several variables; Kuhn-Tucker on the orthant | `convex_tangent`, `concave_tangent`, `orthant`, `convex_orthant`, `hasDerivAt_update`, `clm_apply_eq_sum`, `orthant_kt_iff` |

## Sections 11.A and 11.B: a simple bilateral externality

| Source | Claim | Lean |
| --- | --- | --- |
| Section 11.A, pp. 350-351, footnote 1 | Introduction | Verbal |
| Definition 11.B.1, p. 352 | Externality | `HasExternality`, `definition_11_B_1`; `∂u₂/∂h ≠ 0` gives one: `hasExternality_of_deriv_ne` |
| p. 352 | Pecuniary externalities create no inefficiency | Verbal (Chapter 10's welfare theorems) |
| Footnote 2, p. 352 | Positive and negative externalities | `PositiveExternality`, `NegativeExternality`, `PositiveExternality.hasExternality`, `NegativeExternality.hasExternality` |
| p. 352 | Derived utility `vᵢ(p, wᵢ, h)` | `footnote_3` (the maximization) |
| Footnote 3, p. 353 | Quasilinear utility gives `φᵢ(p, h) + wᵢ` | `footnote_3` (correction 13) |
| p. 353 | The model: `φᵢ` twice differentiable, `φᵢ'' < 0`; firms likewise | `Bilateral`, `strictAntiOn_of_second_deriv_neg`; instance `Bilateral.ex`, `Bilateral.ex_values` |
| (11.B.1), p. 353 | Equilibrium level `h*` | `Bilateral.IsEqLevel`, `Bilateral.eq_11_B_1` |
| Footnote 4, p. 353 | Pareto optimality iff joint surplus maximized | `Bilateral.footnote_4` |
| (11.B.2), p. 353 | Optimal level `h°` | `Bilateral.IsOptLevel`, `Bilateral.eq_11_B_2` |
| p. 353 | Equilibrium not optimal unless `h° = h* = 0` | `Bilateral.eq_ne_opt` |
| p. 354, Figure 11.B.1 | Negative externality `h* > h°`; positive `h* < h°` | `Bilateral.negative_externality_excess`, `Bilateral.positive_externality_shortfall` |
| p. 354 | Optimality does not eliminate a negative externality | `Bilateral.ex_values` (`h° = 3/2 > 0`) |
| Small type, p. 354 | Optimal level independent of wealth (quasilinear) | `Bilateral.opt_indep_wealth`; non-quasilinear case: Exercise 11.B.2 |
| p. 354 | Quota `h ≤ h°` yields `h°` | `Bilateral.quota_implements` |
| (11.B.3)-(11.B.4), p. 355, Figure 11.B.2 | Pigouvian tax `t_h = -φ₂'(h°)` implements `h°` uniquely; sign for positive externality | `Bilateral.IsTaxChoice`, `Bilateral.eq_11_B_4`, `Bilateral.pigou_tax`, `Bilateral.pigou_tax_unique`, `Bilateral.pigou_tax_sign` |
| Footnote 5, p. 355 | If `h° = 0`, any larger tax works | `Bilateral.footnote_5` |
| p. 355 | Subsidy for reduction = tax + lump sum | `Bilateral.subsidy_equiv_tax` |
| p. 356 | Taxing the activity directly; taxes and quotas equally effective under full information | `Bilateral.tax_quota_equivalent`; taxing output: Exercise 11.B.5 |
| pp. 356-357, (11.B.5), footnote 6 | Bargaining with rights to consumer 2 gives `h°` | `Bilateral.IsOffer2Free`, `Bilateral.eq_11_B_5` |
| p. 357 | Rights to consumer 1; the Coase theorem; the payments' signs | `Bilateral.IsOffer2Right`, `Bilateral.coase_theorem`, `Bilateral.coase_payments` |
| Figure 11.B.3, p. 357 | Points `a, b, c, d, e, f`; other procedures give the segments `[f, d]`, `[e, c]` | `Bilateral.offer1_iff`, `Bilateral.figure_11_B_3` (any disagreement point) |
| p. 357 | Well-defined and enforceable rights needed | Verbal |
| p. 358 | Government needs less information | Verbal |
| Small type, p. 358, footnote 7 | Merger internalizes; measurement costs | `Bilateral.merger_internalizes`; rest verbal |
| (11.B.6)-(11.B.7), pp. 358-359 | Rights market demand and supply | `Bilateral.eq_11_B_6`, `Bilateral.IsRightsSupply`, `Bilateral.eq_11_B_7` |
| p. 359 | Equilibrium `h** = h°`, `p_h* = φ₁'(h°) = -φ₂'(h°)`; utilities (point `g`) | `Bilateral.IsRightsEquilibrium`, `Bilateral.rights_equilibrium_optimal`, `Bilateral.rights_equilibrium_exists` |
| p. 359, footnote 8 | Missing markets; thin markets | Verbal |

## Section 11.C: public goods

| Source | Claim | Lean |
| --- | --- | --- |
| Definition 11.C.1, p. 359 | Public good: use by one does not preclude use by others | `NondepletableFeasible`, `definition_11_C_1`, `nondepletable_not_preclude`; private: `DepletableFeasible`, `depletable_precludes` |
| Footnote 9, p. 360 | Congestion; pure public goods | `depletable_imp_nondepletable`; rest verbal |
| p. 360 | Exclusion; public bads | Verbal (exclusion: footnote 11) |
| p. 360 | The model: `φᵢ'' < 0`, `c'' > 0` | `PublicGood`; instance `pgEx`, `pgEx_values` |
| p. 360 | Pareto optimality via aggregate surplus | `PublicGood.pareto_iff_optimal`, `PublicGood.IsOptimal` |
| (11.C.1), pp. 360-361 | Samuelson condition | `PublicGood.eq_11_C_1`, `PublicGood.optimal_unique` |
| (11.C.2), p. 361 | Private provision: consumer's problem | `PublicGood.IsConsumerChoice`, `PublicGood.IsPrivateEq` |
| (11.C.3)-(11.C.4), p. 361 | First-order conditions of consumers and firm | `PublicGood.consumer_foc`, `PublicGood.firm_foc`, `PublicGood.subsidyEq_iff`, `PublicGood.eq_11_C_3_4` |
| (11.C.5), p. 361 | `∑ φᵢ'(q*) > c'(q*)` when `I > 1`, `q* > 0` | `PublicGood.eq_11_C_5` |
| p. 362, footnote 10, Figure 11.C.1 | `q* < q°`; public bad reverses | `PublicGood.underprovision`, `PublicGood.public_bad_excess` (correction 10) |
| p. 362 | Stark free rider: only consumer `I` buys, `φ_I'(q*) = c'(q*)` | `PublicGood.stark_free_rider` |
| p. 362 | Vertical summation | Graphical |
| pp. 362-363 | Subsidies `sᵢ = φ'₋ᵢ(q°)` restore optimality | `PublicGood.IsSubsidyEq`, `PublicGood.exercise_11_C_1`, `PublicGood.exercise_11_C_1_exists` (any `I`) |
| p. 363 | Government needs to know benefits | Verbal |
| (11.C.6)-(11.C.8), pp. 363-364 | Lindahl equilibrium, `q** = q°`; existence | `PublicGood.IsLindahlEq`, `PublicGood.eq_11_C_6`, `PublicGood.lindahl_optimal`, `PublicGood.lindahl_exists` |
| p. 364, footnote 11 | Exclusion needed for Lindahl; Pareto optima involve no exclusion | `PublicGood.footnote_11`; rest verbal |

## Section 11.D: multilateral externalities

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 364-365, footnote 12 | Depletable vs nondepletable; allocability | Verbal |
| p. 365 | The model: `J` firms, `I` consumers, `πⱼ'' < 0`, `φᵢ'' < 0` | `Multilateral`; instance `mlEx`, `mlEx_values`, `mlEx_depl` |
| (11.D.1), p. 365 | Unfettered equilibrium | `Multilateral.IsUnfetteredEq`, `Multilateral.eq_11_D_1` (correction 1) |
| Footnote 13, p. 365 | Indeterminate distribution across consumers | `Multilateral.footnote_13` |
| (11.D.2), p. 366, footnote 14 | Pareto problem for a depletable externality | `Multilateral.DeplFeas`, `Multilateral.deplObj`, `Multilateral.IsDeplOpt` |
| (11.D.3)-(11.D.4), p. 366 | Necessary and sufficient first-order conditions with multiplier `μ` | `Multilateral.DeplKKT`, `Multilateral.deplKKT_sufficient`, `Multilateral.deplKKT_necessary`, `Multilateral.eq_11_D_3_4` |
| p. 366 | A market for a depletable externality is efficient (and supports every optimum) | `Multilateral.IsDeplMarketEq`, `Multilateral.consumer_sell_iff`, `Multilateral.firm_buy_iff`, `Multilateral.deplMarket_optimal`, `Multilateral.deplMarket_exists` |
| (11.D.5)-(11.D.6), p. 366 | Nondepletable: problem and first-order conditions | `Multilateral.nondeplObj`, `Multilateral.IsNondeplOpt`, `Multilateral.NondeplFOC`, `Multilateral.eq_11_D_6` |
| p. 367, footnote 15 | Analogy with (11.C.1); `J` firms producing a public good | `Multilateral.footnote_15` |
| p. 367, footnote 16 | Market fails; free riding in bargaining | `Multilateral.nondepl_excess` (correction 2); bargaining: Exercise 11.D.6 |
| p. 367 | Quotas and the uniform tax `t_h = -∑ᵢ φᵢ'(∑ⱼ hⱼ°)` | `Multilateral.nondepl_quota`, `Multilateral.IsFirmTaxChoice`, `Multilateral.nondepl_tax` |
| Small type, p. 367 | Tradable permits: price `-∑ φᵢ'(h°)`, firms use `hⱼ°`; every permit equilibrium is optimal | `Multilateral.IsPermitEq`, `Multilateral.permit_demand_iff`, `Multilateral.permits_equilibrium`, `Multilateral.permits_unique` |

## Section 11.E: private information and second-best solutions

| Source | Claim | Lean |
| --- | --- | --- |
| p. 368 | Types `η`, `θ`; `b(θ)`, `c(η)`; `h̄` optimal iff `b > c` | `twoLevel_optimal_iff` |
| (11.E.1), p. 369 | Consumer's demand `T_c* > c`; inefficiency with positive probability | `bargObj`, `eq_11_E_1_gt`, `eq_11_E_1_inefficient`, `heavyG`, `eq_11_E_1_no_solution`, `expG`, `eq_11_E_1_exponential` (correction 3) |
| Footnotes 17-19, p. 369 | Monopoly analogy; Myerson-Satterthwaite; organizations | Verbal; footnote 18 cites Chapter 23 (correction 18) |
| p. 369, Figure 11.E.1 | `h°(θ, η)` | Graphical; definitions in the theorems below |
| pp. 369-370 | Quota choice `h^q(ĥ, θ)`; insensitive to `η`; `h^q = ĥ` if `∂π(ĥ, θ)/∂h > 0` | `IsQuotaChoice`, `quota_binds`, instance `quota_binds_instance` |
| p. 370, Figures 11.E.2-11.E.3 | Surplus loss under quota and tax as integrals | `surplus_loss_integral` |
| p. 370 | Tax choice `h^t(t, θ)` | `IsTaxChoice'`, `lq_tax_choice`, `lq_quota_choice` |
| p. 371, Figure 11.E.4(a) | A quota is optimal for every `θ`; no tax is | `figure_11_E_4a` |
| p. 371, Figure 11.E.4(b) | A tax is optimal for every `θ`; no quota is | `figure_11_E_4b` |
| p. 371, footnotes 20-21 | Expected surplus criterion; continuum bargaining | Verbal |
| Footnote 22, p. 371 | Firm's take-it-or-leave-it offer is efficient when the consumer's type is known | `footnote_22` |
| Small type, p. 372 | Uniform tax distributes efficiently across firms | `uniform_tax_efficient` |
| Small type, p. 372 | Tradable permits never worse than the quota; statistical knowledge | `permits_ge_quota`; last sentence verbal |
| Footnote 23, p. 372 | Non-substitutable sources: trade can lower surplus | `footnote_23` |
| p. 373 | Revelation mechanism; truth-telling weakly dominant for both (Section 8.B sense) | `gcGame`, `gc_payoff_consumer`, `gc_payoff_firm`, `gc_consumer_truth`, `gc_firm_truth` (`MWGSimultaneousMoveGames.WeaklyDominant`) |
| p. 373 | Optimal outcome for every `(b, c)` | `gc_optimal` |
| Exercise 11.E.4 (in text), p. 374 | Arbitrary payments depending on the other's announcement | `exercise_11_E_4` (built into `gcGame`) |
| Small type, p. 374 | Deficit `b - c`; no budget balance; eliminating deficits creates surpluses | `gcRevenue`, `gc_deficit`, `gc_no_budget_balance`, `gc_surplus_somewhere` (correction 18) |

## Appendix A: nonconvexities and the theory of externalities

| Source | Claim | Lean |
| --- | --- | --- |
| p. 374, footnote 24 | Concave `π₁`; `π₁` may be negative | Verbal |
| Example 11.AA.1, p. 375, Figure 11.AA.1, footnote 25 | `π₂(h) = γ h^{β/(1-α)}`, `γ > 0`; problem concave in `z`; convex in `h` when `α + β > 1` | `aa1Gamma`, `example_11_AA_1`, `example_11_AA_1_concave_in_z`, `example_11_AA_1_convex`, `example_11_AA_1_alpha_zero`, `example_11_AA_1_alpha_one` (correction 4) |
| Example 11.AA.2, pp. 375-376, Figure 11.AA.2, footnote 26 | Shutdown plus a decreasing profit rules out concavity | `example_11_AA_2`, `example_11_AA_2_instance`; footnote 26 verbal |
| p. 376 | Market existence problems; taxes and quotas still work | Verbal |
| Example 11.AA.3, pp. 376-377, Figure 11.AA.3 | Optimum `h = 0` (surplus `2`), tax `t > 1`; local optimum `h = 1`; surplus higher only for `h < 1/2` | `aa3π₁`, `aa3π₂`, `aa3_surplus_le`, `aa3_surplus_ge`, `example_11_AA_3_optimum`, `example_11_AA_3_local`, `example_11_AA_3_kink` (correction 5) |

## Exercises

| Source | Claim | Lean |
| --- | --- | --- |
| Exercise 11.B.1 | Inefficiency condition; dependence on parameters | `exercise_11_B_1`, `exercise_11_B_1_bees_efficient` |
| Exercise 11.B.1 | Smith's bribe; merged owner; government | `exercise_11_B_1_bribe`, `exercise_11_B_1_subsidy`; intuition verbal |
| Exercise 11.B.2(a) | Pareto problem and first-order condition | `exercise_11_B_2a_reduction`, `compensated_iff`, `exercise_11_B_2a_convex`, `exercise_11_B_2a_slope`, `exercise_11_B_2a`, `exercise_11_B_2a_instance` |
| Exercise 11.B.2(b) | Wealth effect of the demand for `h` | `exercise_11_B_2b`, `exercise_11_B_2b_instance` |
| Exercise 11.B.2(c) | Comparative statics of `h°` in `w₂` | `exercise_11_B_2c_invariant`, `exercise_11_B_2c_counterexample`, `exercise_11_B_2c_corrected`, `exercise_11_B_2c_sign`, `exercise_11_B_2c_instance` (correction 6) |
| Exercise 11.B.3 | Bargaining after the Pigouvian tax (inefficient) and after the quota (efficient) | `Bilateral.exercise_11_B_3_tax`, `Bilateral.exercise_11_B_3_quota` |
| Exercise 11.B.4 | `e` neither taxed nor subsidized | `exercise_11_B_4`, `exercise_11_B_4_no_tax_e`, `exercise_11_B_4_instance` |
| Exercise 11.B.5(a) | Firm's first-order conditions | `quadrant`, `convex_quadrant`, `lines_deriv`, `exercise_11_B_5_firm` (`τ = t = 0`) |
| Exercise 11.B.5(b) | Pareto first-order conditions | `exercise_11_B_5b` |
| Exercise 11.B.5(c) | Output tax fails; tax on `h` restores efficiency | `exercise_11_B_5c` |
| Exercise 11.B.5(d) | Fixed proportions: output tax `-αφ'(αq°)` | `exercise_11_B_5d` |
| Exercise 11.B.5 | Instance | `exercise_11_B_5_instance` |
| Exercise 11.C.1 | Subsidies for `I` consumers | `PublicGood.exercise_11_C_1`, `PublicGood.exercise_11_C_1_exists` |
| Exercise 11.C.2 | Output subsidy | `PublicGood.exercise_11_C_2`, `PublicGood.exercise_11_C_2_exists` |
| Exercise 11.C.3 | Ramsey taxation with a public good; interpretation | `taxPGForm`, `taxPGForm_single`, `taxPGForm_snd`, `exercise_11_C_3`, `exercise_11_C_3_instance` (correction 17); interpretation in the module docstring |
| Exercise 11.D.1 | Symmetric Nash equilibrium; comparison with Pareto | `studentGame`, `student_dev`, `exercise_11_D_1`, `exercise_11_D_1_pareto`, `exercise_11_D_1_instance` (correction 11) |
| Exercise 11.D.2 | Optimal levels, equilibrium, tax/subsidy scheme | `d2Obj`, `d2Obj_concave`, `d2Obj_hasFDerivAt`, `exercise_11_D_2_opt`, `concave1_kt_iff`, `d2_own`, `IsD2Eq`, `exercise_11_D_2_eq`, `exercise_11_D_2_tax`, `exercise_11_D_2_instance` |
| Exercise 11.D.3 | Learning by doing: `Q* < Q°`; subsidy | `clm2_apply`, `exercise_11_D_3_msc`, `exercise_11_D_3_msc_deriv`, `exercise_11_D_3`, `exercise_11_D_3_subsidy`, `exercise_11_D_3_optimal`, `exercise_11_D_3_instance` (correction 16) |
| Exercise 11.D.4 | Nonhomogeneous externalities; firm-specific taxes; when uniform | `d4Obj`, `d4Obj_concave`, `exercise_11_D_4_opt`, `firm_tax_iff`, `exercise_11_D_4_tax`, `exercise_11_D_4_uniform`, `exercise_11_D_4_instance` |
| Exercise 11.D.5(a) | Free-entry equilibrium | `IsCommonsEq`, `avg_gt_marginal`, `avg_strictAnti` |
| Exercise 11.D.5(b) | Optimum; comparison `b° < b*` | `exercise_11_D_5b`, `exercise_11_D_5_compare` (correction 15) |
| Exercise 11.D.5(c) | Per-boat tax | `exercise_11_D_5c` |
| Exercise 11.D.5(d) | Single owner | `exercise_11_D_5d` |
| Exercise 11.D.5 | Instance | `exercise_11_D_5_instance` |
| Exercise 11.D.6(a) | Coalition offer; membership equilibria; `I = 1` optimal; `θ < 1` for `I ≥ 3` | `LandModel`, `LandModel.prof`, `LandModel.yld`, `LandModel.hθ`, `LandModel.pay`, `LandModel.exercise_11_D_6_offer`, `LandModel.memberPay`, `LandModel.outPay`, `LandModel.exercise_11_D_6_stay`, `LandModel.exercise_11_D_6_join`, `LandModel.IsMembershipEq`, `LandModel.membershipEq_iff`, `LandModel.exercise_11_D_6a`, `landEx` (correction 7) |
| Exercise 11.D.6(b) | `θ` declines, `→ 0` | `LandModel.exercise_11_D_6b`, `LandModel.exercise_11_D_6b_limit` |
| Exercise 11.D.7(a) | Both neighborhoods occupied | `nbUtil`, `exercise_11_D_7a_allA`, `exercise_11_D_7a_allB`, `exercise_11_D_7a_counterexample` (correction 8) |
| Exercise 11.D.7(b) | Cutoff structure; the cutoff | `exercise_11_D_7b`, `avg_interval`, `exercise_11_D_7b_cutoff` |
| Exercise 11.D.7(c) | Pareto improvement by raising the cutoff | `exercise_11_D_7c` |
| Exercise 11.E.1(a) | Best quota | `quad_integral`, `lqπ`, `lqφ`, `exercise_11_E_1a` |
| Exercise 11.E.1(b) | Best tax | `lq_tax_response`, `exercise_11_E_1_tax_value`, `exercise_11_E_1b` |
| Exercise 11.E.1(c) | Comparison: tax better iff `b > c` | `exercise_11_E_1c`, moments instance `exercise_11_E_moments_instance` (correction 14) |
| Exercise 11.E.2 | Two producers: optimal uniform quota and tax; dependence on `σ₁₂` | `exercise_11_E_2`, `exercise_11_E_2_compare` |
| Exercise 11.E.3 | Truth is the consumer's only weakly dominant strategy | `weaklyDominant_unique`, `exercise_11_E_3` |
| Exercise 11.E.4 | In text | `exercise_11_E_4` |
| Exercise 11.E.5 | Groves-Clarke for a public project; expected budget balance | `projGame`, `proj_payoff`, `exercise_11_E_5_truth`, `exercise_11_E_5_strict`, `exercise_11_E_5_efficient`, `projBudget`, `exercise_11_E_5_balance`, `exercise_11_E_5_balance_instance` |
| Exercise 11.E.6 | `N` projects | `exercise_11_E_6`, `exercise_11_E_6_selector` |
| Exercise 11.E.7 | Nonlinear tax `-φ(h, η̄)` | `exercise_11_E_7`, `exercise_11_E_7_printed` (correction 9) |
