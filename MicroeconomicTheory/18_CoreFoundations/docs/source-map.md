# Source map

Mas-Colell, Whinston and Green, *Microeconomic Theory*, Chapter 18, "Some Foundations for
Competitive Equilibria", pp. 652-686 (Sections 18.A-18.E, Appendix A, Exercises 18.B.1-18.AA.10).
Printed pages; Lean names relative to `MWG.CoreFoundations`. Every statement was checked against
the page images. The core and Debreu-Scarf core convergence (18.B), the abstract trading model and
its three examples (18.C), self-selective allocations (18.D), the no-surplus characterization of
Walrasian equilibria (18.E) and cooperative game theory with the core, balancedness and the
Shapley value (Appendix A) are covered. Rows marked *verbal* or *graphical* have no precise
mathematical content beyond what the neighbouring rows formalise. OPEN items are listed at the
end. Departures from the printed text are numbered in [corrections](corrections.md).
Dependencies used (Lake `path` requirements): `MWGWelfareTheorems` (Ch. 16: `IsMaximalFor`,
`PrefEconomy`, `PrivPrefEconomy.IsWalrasEqm`, `proposition_16_C_1_walras`, `exercise_16_C_2`,
`concaveOn_le_tangent`, the Replica/CheaperPoint lemmas `exists_strict_of_tendsto`,
`exists_strict_sub_single`, `rationalOn_utilityPref`, `prefContinuous_utilityPref`; through it
Ch. 2-3 `nonnegOrthant`, `budgetSetOn`, `RationalOn`, `PrefStronglyMonotone`,
`PrefStrictlyConvex`, `PrefContinuous`, `utilityPref`, `duality_exists_dot_of_clm`, and Ch. 5
`farkas`), and `MWGWelfareBargaining` (Ch. 22: `Game`, `shapley`, `margContrib`,
`sum_margContrib`, `shapley_pareto`, `exercise_22_F_2`, `exercise_22_F_3a`, `exercise_22_F_4a`,
`unanimity`, `dividend`, `sum_dividend`, `eq_sum_unanimity`, `value_eq_dividendValue`).

## 18.A-18.B Core and equilibria (Basic, CoreWalras, EqualTreatment, DebreuScarf, DebreuScarfSpecial)

| Source | Claim | Lean |
| --- | --- | --- |
| 18.A, p. 652 | Introduction | verbal |
| p. 653 | Economy, CRS technology, standing assumptions, feasibility; instance | `CoreEconomy`, `IsCRSTechnology`, `CoreEconomy.Standing`, `CoreEconomy.IsFeasible`, `isCRSTechnology_nonposOrthant`, `sqrtU`, `sqrtEconomy`, `sqrtEconomy_standing`, `continuous_sqrtU`, `sqrtU_lt_of_le_of_ne`, `sqrtU_strict_concave` |
| Footnote 1, p. 653 | Constant returns and ownership shares | verbal |
| Def. 18.B.1, p. 653 | Blocking coalition | `CoreEconomy.Blocks`, `definition_18_B_1` |
| Def. 18.B.2, p. 654 | Core property, core | `CoreEconomy.HasCoreProperty`, `CoreEconomy.core`, `definition_18_B_2` |
| pp. 654-655 | Walrasian equilibrium of the CRS economy; bridge to Def. 16.B.3 | `CoreEconomy.IsWalrasEqm`, `CoreEconomy.IsWalrasAlloc`, `profit_eq_zero_of_max`, `CoreEconomy.toPriv`, `isWalrasEqm_iff_toPriv` |
| p. 654 | Core allocations are Pareto optimal (and individually rational) | `CoreEconomy.ParetoDominates`, `CoreEconomy.IsParetoOptimal`, `CoreEconomy.IsIndividuallyRational`, `isParetoOptimal_iff_toPriv`, `core_not_strictly_dominated`, `core_isParetoOptimal`, `core_isIndividuallyRational`, `isIndividuallyRational_iff_exchange` |
| Footnote 2, p. 654 | Weak Pareto domination gives strict domination for all | `footnote_18_2`, `exists_strict_all_of_weak` |
| Fig. 18.B.1, p. 654 | Two consumers: core = Pareto optimal and individually rational | `figure_18_B_1` |
| Footnote 3, p. 654 | | verbal |
| Prop. 18.B.1, pp. 654-655 | Walrasian allocations have the core property (exchange proof; general CRS) | `proposition_18_B_1_exchange`, `proposition_18_B_1` |
| p. 655 | The converse is false | `converse_18_B_1_false`, `exampleAlloc_mem_core`, `exampleAlloc_not_walras`, `sqrtEconomy_diag_isParetoOptimal`, `exampleAlloc_ir`, `two_mul_sqrt_le`, `sqrtU_two`, `sqrtU_vec`, `exampleAlloc`, `exampleEndow`, `exampleShare`, `two_sqrt_third_lt`, `two_sqrt_two_thirds_lt` |
| Fig. 18.B.2, p. 655 | A contract-curve allocation blocked in the 2-replica; `-2(x'₂-ω₂) = x'₁-ω₁` | `figure_18_B_2`, `figure_18_B_2_identity`, `figure_18_B_2_identity_instance`, `fig18B2Bundle`, `fig18B2Coalition` (correction 6) |
| Footnote 4, p. 655 | Bertrand analogy | verbal |
| p. 656 | Types, `N`-replica, equal treatment | `CoreEconomy.replica`, `typeAlloc`, `EqualTreatment`, `equalTreatment_typeAlloc` |
| Prop. 18.B.2, p. 656 | Core of the replica has equal treatment; (18.B.1) | `proposition_18_B_2`, `exists_worst`, `avg_pref`, `avg_strict`, `convex_upper_of_strictlyConvex` |
| Footnote 5, p. 656 | Weakly better for all, strictly for one, gives strictly better for all | `footnote_18_5` |
| p. 657 | Type allocations, feasibility `N y ∈ Y`, `C_N`, `C_{N+1} ⊆ C_N`, Walrasian type allocations in every `C_N` and independent of `N` | `CoreEconomy.CN`, `replica_isFeasible_typeAlloc`, `core_replica_eq_typeAlloc`, `CN_succ_subset`, `walras_mem_CN`, `isWalrasEqm_typeAlloc_iff`, `walrasTypeAllocs_eq` |
| Prop. 18.B.3, p. 657 | Debreu-Scarf: as printed false; corrected with `ωₕ ≫ 0`, any CRS `Y`, proof by convex hull of improving trades, rounding and separation | `proposition_18_B_3_false`, `dsEconomy`, `oneZero_mem_core`, `not_maximal_one_zero`, `proposition_18_B_3`, `convex_strictUpper`, `exists_type_combination`, `exists_rounding`, `sum_replica_filter`, `disjoint_improving_trades` (correction 1) |
| pp. 657-659 | The book's special-case proof: favoured type, coalition identity, nonnegativity for large `N`, blocking | `exists_favoured_type`, `grad_dot_pos_of_proportional`, `special_coalition_identity`, `special_nonneg_eventually`, `special_coalition_blocks`, `proposition_18_B_3_special_case` |
| Fig. 18.B.3, p. 658 | | graphical |
| Footnote 6, p. 659 | | verbal |
| p. 659 | `Vᵢ`, `V`; `∑ωᵢ ∈ V`; core ⇒ `∑ωᵢ` not interior; supporting price is Walrasian; `V` need not be convex | `coreVset`, `coreV`, `sum_endow_mem_coreV`, `core_not_mem_interior_coreV`, `supporting_price_isWalrasEqm`, `supporting_price_needs_positive_endowment`, `coreVset_not_convex` (corrections 2-3) |
| pp. 659-660 | Almost-convexity of sums; Aumann-Vind continuum | verbal |

## 18.C Noncooperative foundations (TradingGames)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 660 | Abstract trading model | `TradingModel`, `TradingModel.IsValid`, `TradingModel.payoff` |
| Def. 18.C.1, p. 660; footnote 7 | Trading equilibrium | `TradingModel.IsTradingEqm`, `definition_18_C_1`, `footnote_18_7` |
| p. 661 | Effective budget set | `TradingModel.effBudget`, `TradingModel.isTradingEqm_maximal_effBudget` |
| Footnote 8, p. 661 | Price independent of own action: net trades in the hyperplane, budget in the Walrasian budget | `footnote_18_8` (correction 10) |
| p. 661 (1) | Insensitivity of prices to own actions as `r → ∞` | `price_insensitivity` |
| p. 661 (2), Fig. 18.C.1; footnote 9 | Individual spanning | verbal, graphical |
| Ex. 18.C.1, pp. 661-663; footnote 10 | Cournot model as a trading model | `cournotModel`, `cournotModel_isValid`, `cournotModel_payoff`, `cournot_sum_update` |
| Ex. 18.C.1 | Walrasian equilibrium at capacity | `example_18_C_1_walras` |
| Ex. 18.C.1; footnote 12 | Every firm producing `rb'/J` is a Cournot equilibrium; it is not Walrasian; an instance | `example_18_C_1`, `example_18_C_1_not_walrasian`, `cournotStepSel`, `example_18_C_1_instance` (correction 9) |
| p. 662, footnote 11, Figs. 18.C.2-18.C.3 | Quasilinear case, Giffen money | verbal, graphical |
| Ex. 18.C.2, p. 663 | Complements: null production is an equilibrium | `partialOne`, `partialTwo`, `complementsPrice`, `complementsModel`, `complementsModel_isValid`, `complements_sum_update_zero`, `partialOne_axis_eq_zero`, `partialTwo_axis_eq_zero`, `example_18_C_2` (correction 8) |
| Footnote 13, p. 663 | Homothetic nonlinear `ψ`, discontinuous prices at the origin, `ψ` not differentiable | `fn13GeomMean`, `footnote_18_13_psi`, `footnote_18_13_psi_concave`, `footnote_18_13_prices`, `footnote_18_13_discontinuous`, `footnote_18_13_not_differentiable` |
| Ex. 18.C.3, p. 664; (18.C.1) | Trading posts, trading rule and prices | `tpPrice`, `tpGood`, `tpMoney`, `example_18_C_3_rule` (correction 11) |
| p. 664 | Prices continuous except without offers | `example_18_C_3_continuous`, `tp_continuous_sum_fst`, `tp_continuous_sum_snd`, `example_18_C_3_no_continuous_price`, `tpLoneBid`, `tp_continuous_loneBid`, `tpPrice_loneBid` |
| Footnote 14, p. 664 | Price of money zero | `footnote_18_14` |
| p. 665 | An inactive post remains an equilibrium; no money, no purchases | `TradingPostEconomy`, `TradingPostEconomy.FeasibleBid`, `TradingPostEconomy.goodsOut`, `TradingPostEconomy.moneyOut`, `TradingPostEconomy.IsEqm`, `tp_lone_bidder`, `tp_all_zero`, `example_18_C_3_inactive_post`, `example_18_C_3_no_money` |
| Fig. 18.C.4, p. 664-665 | Thick and thin markets, cash in advance | graphical, verbal |
| Exercise 18.C.1, p. 685 | Effective budget sets (`L = 2`) convex, upper boundary without straight segments | `tpBudget`, `tp_update_sums`, `tp_outcome`, `exercise_18_C_1_one_sided`, `tpFrontier`, `tp_outcome_on_frontier`, `tpFrontier_eq`, `tpFrontier_strictConcaveOn`, `tpFrontier_antitoneOn`, `tpMaxBuy`, `tp_reachable`, `exercise_18_C_1_eq`, `exercise_18_C_1_convex`, `exercise_18_C_1_boundary` |

## 18.D The limits to redistribution (Redistribution, Closer18D)

| Source | Claim | Lean |
| --- | --- | --- |
| Def. 18.D.1, p. 666 | Self-selective allocation, generalized budget set | `CoreEconomy.IsSelfSelectiveWith`, `CoreEconomy.IsSelfSelective`, `definition_18_D_1` |
| p. 666 | "It is enough to take `B = {x*ᵢ}`" (misprint: net trades) | `selfSelective_iff_netTrades`, `CoreEconomy.NoEnvyNetTrades`, `misprintEconomy`, `selfSelective_consumptions_misprint` (correction 4) |
| Footnote 15, Fig. 18.D.1 | | verbal, graphical |
| p. 667 | Walrasian ⇒ Pareto optimal and self-selective with `B = {p·z = 0}` | `walras_isParetoOptimal_selfSelective` |
| Figs. 18.D.2-18.D.3, p. 667 | Pareto optimal, self-selective, not Walrasian | `fig18D2Endow`, `fig18D2Alloc`, `fig18D2_sqrt_sq`, `figure_18_D_2` |
| Fig. 18.D.4, pp. 667-668; footnotes 16-18 | Continuum example with kinked preferences; smoothness discussion | graphical, verbal (finite counterpart `figure_18_D_2`) |
| Prop. 18.D.1, p. 669 | Equal treatment step; single net trade is zero; main claim under explicit smoothness of `z(t)`; instance | `proposition_18_D_1_supported_eq`, `proposition_18_D_1_equal_treatment`, `proposition_18_D_1_single_net_trade`, `proposition_18_D_1_smooth`, `proposition_18_D_1_walrasian`, `prop18D1D`, `proposition_18_D_1_instance`; continuum form (types `t ∈ [0, 1]`, population measure `ν`, `L = 2`): `c18_planar_flat_const`, `c18_flat_of_noEnvy`, `c18_continuousOn_of_noEnvy` (continuity of `z(t)` derived), `proposition_18_D_1_continuum`, instance `proposition_18_D_1_continuum_instance` (`c18InstU`, `c18InstOmega`, `c18InstZ`, `c18InstD`, `c18InstD_apply`, `c18InstU_mid`); definitions `c18IsSelfSelective`, `c18_isSelfSelective_iff_noEnvy`, `c18IsMeasureFeasible`, `c18IsMeasurePareto`, `c18_integral_dot_eq_zero`, `c18_isMeasurePareto_of_supported`; helpers `c18_abs_coord_le`, `c18_dot_two`, `c18_abs_sub_le_of_mem_uIcc`, `c18_mem_uIcc_affine` (correction 25; supporting price and `L ≥ 3` OPEN) |
| Footnote 19, Figs. 18.D.5-18.D.6 | | verbal, graphical |
| Exercise 18.D.1, p. 685 | Individually rational Edgeworth allocations are self-selective | `pref_add_of_pref_endow`, `exercise_18_D_1` |

## 18.E Marginal productivity (MarginalProduct, MarginalProductExamples, Closer18Value)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 670 | Quasilinear economy with `H` types | `QLEconomy`, `QLEconomy.u`, `qlPrice`, `qlPrice_sum`, `qlPrice_sub`, `qlPrice_mono` |
| (18.E.1)-(18.E.2), pp. 670-671 | Maximal social utility `v(μ)` (a supremum) and its finiteness | `QLEconomy.IsFeasible`, `QLEconomy.welfare`, `QLEconomy.valueSet`, `QLEconomy.v`, `QLEconomy.IsOptimal`, `QLEconomy.isOptimal_iff`, `QLEconomy.valueSet_nonempty`, `QLEconomy.welfare_le_of_majorant`, `QLEconomy.v_le_of_majorant`, `QLEconomy.bddAbove_of_majorant`, `QLEconomy.exists_majorant`, `ql_fderiv_single_nonneg`, `ql_clm_apply_eq_sum`, `ql_hasDerivAt_line` (correction 16) |
| p. 670 | `v(rμ) = r v(μ)`, `v(I/I) = v(I)/I` | `QLEconomy.valueSet_smul`, `QLEconomy.v_zero`, `QLEconomy.v_smul`, `QLEconomy.v_div` |
| Footnote 20, p. 670 | Equal treatment within types is without loss | `QLEconomy.IsFeasibleFinite`, `qlTypeCount`, `ql_sum_fiber`, `footnote_18_20`, `footnote_18_20_sSup` |
| Exercise 18.E.1, p. 671 | `v` concave and homogeneous of degree one | `ql_convex_bundles`, `QLEconomy.u_concaveOn`, `QLEconomy.v_superadditive`, `exercise_18_E_1`, `sqrtQL_v_concave` |
| p. 671, footnote 21 | Continuum limit; differentiability of `v` | verbal; instance `sqrtQL_v`, `sqrtQL_v_differentiableAt` |
| Def. 18.E.1, p. 671; footnote 22 | Marginal product (no-surplus) allocation | `QLEconomy.IsMarginalProduct`, `definition_18_E_1_instance` |
| Prop. 18.E.1, pp. 671-672 | Marginal product iff Walrasian (`μ ≫ 0`); Euler; (18.E.4) | `QLEconomy.IsWalrasEqm`, `QLEconomy.walras_price_nonneg`, `QLEconomy.walras_budget_eq`, `QLEconomy.walras_majorant`, `QLEconomy.v_le_linear`, `ql_euler`, `proposition_18_E_1`, `proposition_18_E_1_of_walras`, `QLEconomy.partial_v_of_walras`, `QLEconomy.walras_of_optimal_of_partial`, `ql_partial_eq_of_le_linear`, `QLEconomy.foc_of_optimal`, `QLEconomy.supporting_prices`, `ql_eventually_nonneg_line`, `ql_sum_perturb`, `ql_eventually_nonneg_of_pos`, `proposition_18_E_1_instance`, `sqrtQLEconomy`, `sqrtQL_concave`, `sqrtQL_mono`, `sqrtQL_differentiableAt`, `sqrtQL_omega_nonneg`, `sqrtQL_welfare_le`, `qlOnes`, `sqrtQLStar`, `ql_sqrt_half`, `ql_sqrt_tangent`, `sqrtQL_walras`, `sqrtQL_optimal` (correction 15) |
| (18.E.5); Exercise 18.E.2, pp. 672, 685 | `∂v/∂μₕ = uₕ(x*ₕ) + p·(ωₕ - x*ₕ)` | `exercise_18_E_2`, `sqrtQL_partial` |
| p. 672 | Interpretation of (18.E.5) | verbal |
| p. 672 | Finite economies: `Δₕv ≥ ∂v/∂μₕ`, `∑ Iₕ Δₕv ≥ v(I)`, full marginal contributions infeasible, Walrasian iff `uₕ = ∂v/∂μₕ(I)`, instances | `QLEconomy.deltaV`, `claim_18_E_deltaV_ge_partial`, `claim_18_E_sum_deltaV_ge`, `claim_18_E_no_full_marginal`, `claim_18_E_no_full_marginal_finite`, `claim_18_E_finite_walras_iff`, `sqrtQL_deltaV`, `example_18_E_finite_strict`, `example_18_E_no_full_marginal`, `example_18_E_walras_below_delta`, `example_18_E_finite_claims` |
| p. 673 | Shapley value of the finite economy sums to `v(I)` | `qlShapleyGame`, `claim_18_E_shapley_sum` |
| p. 673 | Hypergeometric-average formula for the Shapley value of an economy with types: exact form; weights form a probability distribution; the printed form is not exact | `c18Profile`, `c18TypeGame`, `c18Box`, `c18_card_profile_fiber`, `c18_profile_mono`, `c18_sum_powerset_profile`, `c18_profile_insert`, `c18_card_eq_sum_profile`, `c18_profile_erase`, `c18_shapley_sub_const`, `c18_shapley_types`, `c18_shapley_hypergeometric`, `c18_hypergeometric_weights_sum`, `c18BookFormula`, `c18_book_formula_counterexample` (correction 27) |
| p. 673 | Value equivalence theorem ("too advanced to be given here") | OPEN (see below) |
| Exercise 18.E.3, p. 685 | Leontief preferences: Walrasian traders get less than their marginal contribution | `leontiefQLEconomy`, `leontief_concave`, `leontief_mono`, `leontief_welfare_le`, `leontief_v`, `leontief_line`, `exercise_18_E_3_left_deriv`, `exercise_18_E_3_right_deriv`, `exercise_18_E_3_not_differentiable`, `exercise_18_E_3_delta`, `exercise_18_E_3`, `exercise_18_E_3_eqm`, `exercise_18_E_3_boundary`, `exercise_18_E_3_hypotheses` (corrections 13-14) |

## Appendix A Cooperative game theory (CoopGames, Balanced, ShapleyValue, ShapleyExamples, ShapleyExercises, Closer18AA)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 673-674; footnotes 23-24 | Introduction | verbal |
| p. 674 | Outcomes and projections `u^S` (`ℝ^S` as sets of outcomes depending only on `S`) | `projS`, `extS`, `projS_extS`, `continuous_projS`, `continuous_extS` |
| Def. 18.AA.1, p. 674; footnote 25 | Utility possibility set | `IsUtilityPossibilitySet`, `isUtilityPossibilitySet_iff` |
| Def. 18.AA.2, p. 675 | Game in characteristic form | `NTUGame`, `IsCharacteristicForm` |
| Ex. 18.AA.1, p. 675 | Economies: comprehensive, convex, superadditive; closedness | `econGame`, `econGame_comprehensive`, `econGame_nonempty`, `example_18_AA_1_convex`, `example_18_AA_1_superadditive`, `openConeTech`, `openConeTech_isCRS`, `example_18_AA_1_not_closed`, `example_18_AA_1_closed`, `c18NegSum`, `c18NegSum_continuous`, `c18NegSum_smul`, `c18_cone_bounded`, `example_18_AA_1_closed_cone`, `example_18_AA_1_closed_crs`, `c18HalfPlane`, `c18HalfPlane_hyp`, `example_18_AA_1_closed_halfPlane`, `example_18_AA_1_free_production` (correction 17) |
| Ex. 18.AA.2, pp. 675-676; Fig. 18.AA.4 | Majority voting; `V` need not be convex | `votingGame`, `votingGame_isCharacteristicForm`, `votingGame_superadditive`, `votingPayoffs`, `example_18_AA_2_not_convex` |
| Def. 18.AA.3, p. 676 | Superadditivity; satisfied by Exs. 18.AA.1-18.AA.2 | `IsSuperadditive`, `example_18_AA_1_superadditive`, `votingGame_superadditive` |
| Def. 18.AA.4, p. 676; footnote 26 | TU games (Ch. 22 `Game`); TU sets | `tuSet`, `tuSet_isCharacteristicForm`, `tuSet_superadditive_iff`; footnote 26 verbal |
| Ex. 18.AA.3, p. 677; Figs. 18.AA.5-18.AA.6 | TU majority voting; normalisation `v({i}) = 0` | `tuMajority`, `example_18_AA_3`; graphical, verbal |
| Defs. 18.AA.5-18.AA.6, p. 678; TU forms | Blocking, core, TU blocking and TU core | `ntuBlocks`, `tu_blocks_iff`, `ntuCore`, `tuCore`, `ntuCore_tuSet` |
| Fig. 18.AA.7 | | graphical |
| Exercise 18.AA.2, p. 678 | Nonempty core ⇒ `v(S) + v(T) ≤ v(I)` | `exercise_18_AA_2` |
| Ex. 18.AA.4, p. 678 | Both majority games have empty cores | `example_18_AA_4_tu`, `example_18_AA_4_ntu`; Condorcet remark verbal |
| Ex. 18.AA.5, pp. 678-679; footnote 27 | Economy core = game core; Walrasian ⇒ nonempty | `example_18_AA_5`, `example_18_AA_5_game_core`, `example_18_AA_5_walras` (correction 20) |
| Ex. 18.AA.6, p. 679 | Proportional allocation in the core; convex `f` ⇒ nondecreasing average product | `prodGame`, `propAlloc`, `propAlloc_sum`, `example_18_AA_6`, `example_18_AA_6_convex`; "larger returns, larger core" verbal (correction 19) |
| Footnote 28, p. 679 | Strictly decreasing returns ⇒ empty core | `footnote_18_28`, `footnote_18_28_core_empty` (correction 18) |
| Exercise 18.AA.3, p. 685 | Constant average product ⇒ proportional allocation is the only core allocation | `exercise_18_AA_3` |
| Exercise 18.AA.1, p. 685 | Generalized partitions and examples; balancedness; nonempty core iff balanced (Bondareva-Shapley, via Farkas) | `IsGeneralizedPartition`, `exercise_18_AA_1_singletons`, `exercise_18_AA_1_pairs`, `IsBalanced`, `isBalanced_of_core`, `core_nonempty_of_isBalanced`, `exercise_18_AA_1`, `bsGen`, `dotProduct_snoc`, `snoc_apply_castSucc`, `snoc_apply_last` |
| pp. 679-680; footnotes 29-30, Fig. 18.AA.8 | The value as egalitarian division | verbal, graphical |
| (18.AA.1), p. 680 | Two-player egalitarian solution | `formula_18_AA_1`, `egalitarian_pair` |
| (18.AA.2), p. 681 | Preservation of differences: uniqueness by induction, the displayed `Sh₁(I, v)` formula, existence | `subgame`, `IsEgalitarianSolution`, `isEgalitarianSolution_congr`, `egalitarian_unique`, `egalitarian_recursion`, `shapleyFamily`, `shapleyFamily_isEgalitarian`, `powerset_filter_not_mem` |
| Def. 18.AA.7, p. 681 | Shapley value | `shapleyMWG`, `definition_18_AA_7` |
| (18.AA.3), p. 681; footnote 31 | Average marginal contribution (= Ch. 22 `shapley`); `∑ᵢ m(S(π,i), i) = v(I)` | `formula_18_AA_3`, `shapley_subgame`, `dividend_subgame`, `footnote_18_31`, `sum_marginal_contributions` |
| (18.AA.4), p. 682; footnote 32 | Subset formula | `subsetFormula`, `subsetFormula_eq_shapleyFamily`, `formula_18_AA_4`, `hockey_stick`, `shapley_weight_sum_nat`, `shapley_weight_sum`, `sub_erase_eq_sum_dividend`; probability interpretation verbal |
| Exercise 18.AA.4, p. 685 | (18.AA.4) and (18.AA.3) satisfy (18.AA.2) | `exercise_18_AA_4` |
| Ex. 18.AA.7, pp. 681-683 | Glove market: orderings, `Sh = (1/6, 1/6, 2/3)`, the (18.AA.2) check, core `{(0,0,1)}`, Shapley not in the core | `gloveInt`, `gloveGame`, `example_18_AA_7_values`, `gloveMarg`, `example_18_AA_7_orderings`, `gloveGame_empty`, `gloveGame_swap`, `example_18_AA_7`, `example_18_AA_7_check`, `sum_glove_core`, `example_18_AA_7_core`, `example_18_AA_7_block`, `example_18_AA_7_shapley_not_core` |
| (a)-(d), p. 682; footnote 33 | Efficiency, symmetry, linearity, dummy | `shapley_efficiency`, `RolesPermuted`, `rolesPermuted_iff`, `map_swap_of_iff`, `map_swap_of_mem_notMem`, `shapley_symmetry_footnote_33`, `MWGSymmetric`, `shapley_mwgSymmetric`, `shapley_linearity`, `shapley_dummy_axiom` |
| p. 682 | The four properties characterize the Shapley value | `shapley_characterization` |
| pp. 682-683 | The Shapley value need not be in the core | `shapley_not_core_majority`, `example_18_AA_7_shapley_not_core` |
| Def. 18.AA.8, p. 683 | Convex games | `IsConvexGame` |
| Prop. 18.AA.1, p. 683 | Convex ⇒ Shapley value in the core | `marginal_vector_mem_core`, `proposition_18_AA_1` (correction 23) |
| Ex. 18.AA.8, p. 683; Exercise 18.AA.7, p. 686 | Complementary inputs: the production game is convex; `N = 1`; `N > 1` neither necessary nor sufficient | `IncreasingDifferences`, `inputGame`, `exercise_18_AA_7`, `convexOn_increasing_differences`, `example_18_AA_8_one_input`, `example_18_AA_8_one_input_deriv`, `example_18_AA_8_not_sufficient`, `example_18_AA_8_not_necessary`; with the printed hypothesis `∂²f/∂z_h∂z_k ≥ 0` for every `N`: `c18Partial`, `c18_eq_sum_single`, `c18_clm_apply_eq_sum`, `c18_partial_differentiableAt`, `c18_hasDerivAt_line`, `c18_line_mem`, `c18_partial_mono`, `c18_fderiv_mono`, `example_18_AA_8_increasingDifferences`, `exercise_18_AA_7_crossPartials`, instance `c18_product_crossPartials`, `exercise_18_AA_7_product` (corrections 21-22) |
| Exercise 18.AA.5, p. 686 | Unanimity games: equal split | `IsUnanimityGame`, `isUnanimityGame_unanimity`, `exercise_18_AA_5` |
| Exercise 18.AA.6, p. 686 | Unanimity decomposition; uniqueness; the Shapley value | `exercise_18_AA_6_decomposition`, `exercise_18_AA_6_unique`, `exercise_18_AA_6` |
| Exercise 18.AA.8, p. 686 | Convex production function, empty core | `maxTech`, `maxGame`, `exercise_18_AA_8` |
| Exercise 18.AA.9 | The four-player game | `v9Int`, `game9`, `game9_empty`, `exercise_18_AA_9_table` |
| Exercise 18.AA.9(a) | `Min{z₁, z₂}` technology | `omega9`, `exercise_18_AA_9a` |
| Exercise 18.AA.9(b) | Core = `{(α, α, 1-α, 1-α)}` | `sum_alpha_alloc`, `alpha_alloc_mem_core`, `exercise_18_AA_9b` |
| Exercise 18.AA.9(c) | Unique core point `(0,0,1,1)`; player 1 compared | `game9mod`, `exercise_18_AA_9c`, `exercise_18_AA_9c_compare` |
| Exercise 18.AA.9(d) | Shapley value `(1/2, 1/2, 1/2, 1/2)` by symmetry | `game9_perm_invariant`, `exercise_18_AA_9d` |
| Exercise 18.AA.9(e) | Modified Shapley value `(7/12, 1/4, 7/12, 7/12)`; comparison | `exercise_18_AA_9e`, `exercise_18_AA_9e_compare`; discussion verbal |
| Exercise 18.AA.10(a) | Shapley cost allocation | `costGame`, `psi1`, `psi2`, `exercise_18_AA_10a` |
| Exercise 18.AA.10(b) | Marginal costs | `exercise_18_AA_10b` |
| Exercise 18.AA.10(c) | Efficiency | `exercise_18_AA_10c_unbounded`, `exercise_18_AA_10c_no_max`, `exercise_18_AA_10c_foc` (correction 24) |
| Exercise 18.AA.10(d) | No rule charges each division the full marginal cost | `const_of_hasDerivAt_zero_Ioi`, `exercise_18_AA_10d` (correction 24) |

## Section 18.B exercises (CoreWalras, EqualTreatment, DebreuScarfSpecial, ShoeMarket)

| Source | Claim | Lean |
| --- | --- | --- |
| Exercise 18.B.1, p. 684 | Walrasian allocations are in the core with CRS | `exercise_18_B_1` |
| Exercise 18.B.2, p. 685 | Three-consumer non-equal-treatment core allocation; impossible with two consumers | `ex18B2Economy_standing`, `ex18B2_tu_bound`, `exercise_18_B_2a`, `exercise_18_B_2b`, `ex18B2Economy`, `ex18B2Alloc`, `ex18B2U`, `ex18B2U_lt_of_le_of_ne`, `ex18B2U_vec`, `ex18B2_util` |
| Exercise 18.B.3, p. 685 | Walrasian allocations have equal treatment | `exercise_18_B_3`, `replica_walras_equalTreatment` |
| Exercise 18.B.4, p. 685 | Taylor step of Prop. 18.B.3 | `exercise_18_B_4`, `exercise_18_B_4_grad` |
| Exercise 18.B.5, p. 685 | Shoe market model | `shoeU`, `shoeFeasible`, `shoeParetoOptimal`, `shoeMatched`, `shoeBlocks`, `shoeCore`, `shoeWalras`, `shoeEndow`, `shoeExample`, `shoePairs`, `shoeWealth`, `shoe_card_left`, `shoe_card_right`, `shoe_eq_one_of_sum_le`, `shoe_sum_ite_left`, `shoe_sum_ite_right`, `shoe_sum_u_le` |
| Exercise 18.B.5(a) | Matched allocations and Pareto optima | `shoe_paretoOptimal_iff`, `exercise_18_B_5a`, `shoe_matched_not_paretoOptimal`, `exercise_18_B_5a_converse`, `shoe_paretoOptimal_not_matched` (correction 5) |
| Exercise 18.B.5(b) | Core with weak blocking | `exercise_18_B_5b` |
| Exercise 18.B.5(c) | Walrasian equilibria | `exercise_18_B_5c`, `shoeWalras_pR_pos`, `shoeWalras_pairs`, `shoeWalras_endowment` |
| Exercise 18.B.5(d) | Core and Walrasian equilibria compared | `exercise_18_B_5d` |

## OPEN

1. Proposition 18.D.1, two steps of the general statement (p. 669). What is proved
   (`proposition_18_D_1_continuum`, `L = 2`, types `t ∈ [0, 1]` with a population measure `ν`
   finite on compacts, `∫_{[0,1]} z dν = 0`): with no envy (self-selectivity,
   `c18_isSelfSelective_iff_noEnvy`), a common supporting price `p` with first-order conditions
   `Du(x(t); t) = λ(t) p`, interior bundles and the regularity listed in correction 25, the
   net-trade path is continuous (derived, `c18_continuousOn_of_noEnvy`) and the allocation is
   Walrasian. Missing: (a) the second welfare theorem for the continuum, i.e. that a
   measure-theoretic Pareto optimum (`c18IsMeasurePareto`) of interior bundles with
   differentiable utilities is supported by such a `p` (only the converse,
   `c18_isMeasurePareto_of_supported`, is proved); the book takes this step for granted ("Let `p`
   be the price vector supporting `x*`"); (b) `L ≥ 3`. The book's proof is limited to `L = 2`,
   and so is ours: the flatness step `c18_planar_flat_const` uses that the orthogonal complement
   of `p` is one-dimensional. For `L ≥ 3` the analogous step is false for non-rectifiable paths
   (a Koch-type curve `γ` in `p^⊥` with `|γ(s) - γ(t)| ≥ c|s - t|^α`, `α < 1`, gives
   `p·z(t) = t - 1/2` with no envy for the utilities `p·x - φ(|P x - γ(t)|)`,
   `φ(d) = (d/c)^{1/α}`); this suggested counterexample to the proposition for `L ≥ 3` is not
   formalised.
2. The value equivalence theorem (p. 673; Aumann 1975, "too advanced to be given here"): for
   replica economies the Shapley values converge to the Walrasian utilities
   `∂v/∂μ_h(I)`. The exact finite formula it starts from is proved
   (`c18_shapley_hypergeometric`, `c18_hypergeometric_weights_sum`); the limit needs a law of
   large numbers for hypergeometric samples (concentration of `I'/|I'|` around `I/I`) and the
   continuity of the supergradients of the concave, homogeneous `v` at `μ`, which are not
   formalised.
