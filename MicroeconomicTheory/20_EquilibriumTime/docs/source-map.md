# Source map

Mas-Colell, Whinston and Green, *Microeconomic Theory*, Chapter 20, "Equilibrium and Time",
pp. 732-786, and Mathematical Appendix Section M.N, "Dynamic Programming", pp. 968-970.
Printed pages; Lean names relative to `MWG.EquilibriumTime`.
The chapter's sections are 20.A-20.I (20.H is overlapping generations, 20.I nonequilibrium
dynamics). Every numbered definition, proposition and example, the precise unnumbered claims,
footnotes and every exercise subpart are listed. "Verbal" marks discussion without a precise
mathematical claim; "OPEN" marks a claim not formalised, with the reason. Departures are in
[corrections](corrections.md). Dependency uses: Chapter 15's `concave_le_fderiv` and
`concave_le_tangent` (gradient inequalities), Chapter 5's `NoFreeLunch`, `FreeDisposal`,
`Efficient` and `proposition_5_F_2` (second fundamental theorem), and LeanEconomics'
`DynamicProgram` (Bellman operator, `valueFunction`, `isGreatest_planValue`,
`eq_valueFunction`, `tendsto_iterate_valueFunction`), all through the Chapter 17 requirement.

## 20.A Introduction (p. 732)

| Source | Claim | Lean |
| --- | --- | --- |
| Section 20.A, pp. 732-733 | Overview; deterministic setting; `∑_t` means `∑_{t=0}^∞` | Verbal |

## 20.B Intertemporal utility (pp. 733-736)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 733 | Bounded nonnegative consumption streams | `BoundedStream`, `NonnegStream` |
| (20.B.1), p. 733 | `V(c) = ∑ δ^t u(c_t)` and its convergence | `discountedUtility`, `summable_discounted`, `summable_discounted_of_monotoneOn`, `abs_utility_le_of_monotoneOn` |
| Footnote 1, p. 733 | Terminology | Verbal |
| Comment (1), Exercise 20.B.1, pp. 733, 782 | Time impatience | `forwardShift`, `discountedUtility_forwardShift`, `exercise_20_B_1`; `impatience_fails_at_zero_discount` (correction 1) |
| Footnote 2, p. 734 | Completeness of the induced preference | `footnote_20_2` |
| Footnote 3, p. 734 | Ramsey's remark | Verbal |
| Comment (1), p. 734 | Survival-probability interpretation | `survival_interpretation` |
| (20.B.2), p. 734 | Time-dependent additive form; (20.B.1) as a special case | `timeAdditiveUtility`, `discountedUtility_eq_timeAdditive` |
| Comment (2), Exercise 20.B.2, pp. 734, 782 | (20.B.1) is stationary; violation with time-dependent discounting | `backShift`, `discountedUtility_split`, `exercise_20_B_2_stationary`, `quasiHyperbolic`, `exercise_20_B_2_violation`; `stationarity_fails_at_zero_discount` |
| Footnote 4, p. 734 | Time consistency is tautological | `footnote_20_4` |
| Comment (3), Exercise 20.B.3, pp. 735, 783 | Separability of future and past | `splice`, `discountedUtility_splice`, `exercise_20_B_3_future`, `exercise_20_B_3_past` |
| Comment (3), p. 735 | Separability implies additivity (Blackorby-Primont-Russell) | OPEN: cited representation theorem, not proved in MWG; needs the Debreu-Gorman additive representation theorem (separability of all subsets of periods plus continuity give additivity, via the hexagon/Thomsen condition), not in Mathlib or LeanEconomics |
| Comment (3), p. 735 | Habits via household production | Verbal |
| Comment (4), p. 735 | Length of the period | Verbal |
| Comment (5), p. 735 | `V(c) = u(c₀) + δ V(c¹)` | `discountedUtility_recursive` |
| Comment (5), (20.B.3), p. 736 | Recursive utility with `G(u, V) = u^α + δV^α` | `powAggregator`, `recursiveTrunc`, `recursiveUtility`, `recursive_aggregator_two_solutions` (correction 2) |
| Exercise 20.B.4, p. 783 | Well-defined recursive utility | `exercise_20_B_4_bounded`, `recursiveTrunc_mono`, `exercise_20_B_4_limit`, `exercise_20_B_4_aggregator` |
| Comment (6), p. 736 | Altruism: the dynasty's utility is (20.B.1) | `altruism_dynasty` |
| Exercise 20.B.5, p. 783 | Concavity of `V` | `exercise_20_B_5_concave` |
| Exercise 20.B.5, p. 783 | Additive form is cardinal: affine transformations preserve it, ordinal ones need not, and it is unique up to positive affine maps | `exercise_20_B_5_affine`, `exercise_20_B_5_ordinal_not_additive`; uniqueness: `twoDateStream`, `twoDate_value`, `twoDate_props`, `SameRanking` (instance `sameRanking_affine`), `additive_jensen`, `affine_of_weighted_jensen`, `exercise_20_B_5_unique` (correction 22) |

## 20.C Intertemporal production and efficiency (pp. 736-743)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 737 | Plans `y = (y_b, y_a)` | `ProdPlan` |
| (i)-(iv), p. 737 | Assumptions on `Y`; bridge to Chapter 5 | `TechAssumptions`, `noFreeLunch_iff_stack`, `freeDisposal_iff_stack`, `stackPlan` and lemmas |
| p. 737 | `y_a ≥ 0` makes (iv) follow from (iii) | `truncation_of_nonneg_after` |
| Example 20.C.1, footnote 5, p. 737 | Ramsey-Solow technology; labor primary; (i)-(iv) | `ramseySolowSet`, `ramseySolowSet_eq`, `ramseySolow_labor_primary`, `example_20_C_1` |
| Example 20.C.2, p. 737 | Cost-of-adjustment technology | `costAdjustmentSet` |
| Example 20.C.3, p. 738 | Two-sector technology; special cases | `twoSectorSet`, `example_20_C_3_costAdjustment`, `mergeGoods`, `example_20_C_3_ramseySolow` |
| Example 20.C.4, p. 738 | `(N+1)`-sector technology | `multiSectorSet` |
| Definition 20.C.1, footnote 6, p. 738 | Production paths; net input-output vectors | `IsProdPath`, `netOutput` |
| Definition 20.C.2, p. 739 | Efficiency | `ProdEfficient` |
| Definition 20.C.3, p. 739 | Myopic profit maximization; Malinvaud prices | `periodProfit`, `planValue`, `MyopicProfitMax` |
| Footnote 7, p. 739 | Infinite present value possible | Verbal (see Exercises 20.C.2-20.C.5) |
| Example 20.C.5, p. 740 | Storage: myopic but inefficient, TC fails | `storageSet`, `storageSet_eq`, `storageSet_techAssumptions`, `storagePath`, `example_20_C_5` |
| p. 740 | Transversality condition | `Transversality` |
| Proposition 20.C.1, p. 740 | Myopic + `p ≫ 0` + TC ⇒ efficient | `proposition_20_C_1`, `sum_value_netOutput`, `sum_value_netOutput'`, `sum_value_le_of_myopic`, `no_value_improvement` |
| p. 741 | (ii): TC not necessary for Malinvaud prices | golden rule: `golden_rule_efficient` with constant prices `rs_steady_prices` (footnote 22) |
| Example 20.C.6, p. 741 | First-order conditions necessary and sufficient | `example_20_C_6`, `rs_profitMax_of_foc`, `rs_foc_of_profitMax` |
| (20.C.1)-(20.C.2), p. 741 | Sufficient conditions for efficiency | `efficient_of_20_C_1_20_C_2` (correction 13) |
| p. 741 | (20.C.1) not sufficient; (20.C.2) not necessary | `inefficient_above_golden` with `rs_steady_prices`; `golden_rule_efficient` |
| (20.C.2'), footnote 8, p. 742 | Cass's criterion `∑ 1/q_t = ∞` | OPEN: cited theorem (Cass 1972); neither direction formalised: both need Cass's curvature bounds on `F` and a comparison of the price sequence with the deviation of a dominating path |
| Example 20.C.7, p. 742 | (i)-(ii), (20.C.3); reduces to (20.C.1) | `example_20_C_7`, `example_20_C_7_no_adjustment` |
| Small type, p. 742 | Efficient plans are on the boundary | `prodEfficient_not_mem_interior` |
| Small type, pp. 742-743 | Efficiency forces `q_{a,t-1} = β q_{bt}` (smooth case) | `SupportsAt`, `SmoothAt`, `proportional_normals_of_twoEfficient`, `efficient_twoDateSet`, `convex_twoDateSet` |
| Small type, p. 743 | Inductive construction of Malinvaud prices; only short-run efficiency used | `normalScale`, `normalPrices`, `malinvaud_of_proportional_normals`, `malinvaud_of_twoEfficient` |
| Small type, p. 743 | Nonsmooth existence (separation plus limit, nontightness) | OPEN: separation of each finite truncation is available (geometric Hahn-Banach), but the limit step (normalized truncation prices, diagonal extraction, and the nontightness condition keeping the limit nonzero) is not formalised |
| Figures 20.C.1-20.C.2 | Smooth sets; inefficiency at `t` | Graphical (content as above) |
| Exercise 20.C.1, p. 783 | Own rates of interest | `ownRate`, `exercise_20_C_1` |
| Exercise 20.C.2, p. 783 | Finite-horizon profit maximization | `exercise_20_C_2` |
| Exercise 20.C.3, p. 783 | Weak efficiency with `p ≥ 0`, `p ≠ 0` | `ProdWeaklyEfficient`, `exercise_20_C_3` |
| Exercise 20.C.4(a), p. 783 | Overall profit maximization ⇒ efficiency | `BoundedPath`, `OverallProfitMax`, `splicePath`, `exercise_20_C_4a` (correction 14) |
| Exercise 20.C.4(b), p. 783 | Myopic ⇒ overall | `tendsto_value_of_bounded`, `exercise_20_C_4b` |
| Exercise 20.C.5(a), p. 783 | Myopic ⇒ `T`-efficient | `TEfficient`, `not_finite_change_of_myopic`, `exercise_20_C_5a` |
| Exercise 20.C.5(b), p. 783 | Smooth: 2-efficient ⇒ `T`-efficient | `exercise_20_C_5b` |
| Exercise 20.C.5(c), p. 783 | Failure for linear activities (chain of intermediate goods) | `chainPlan`, `chainSet`, `chainSetNoReturn`, `chainStoragePath`, `chain_value_zero`, `chain_storage_myopic`, `exercise_20_C_5c_twoEfficient`, `chainDetourPath`, `exercise_20_C_5c_not_threeEfficient` |
| Exercise 20.C.6, pp. 783-784 | Wages supporting any capital path | `exercise_20_C_6` |

## 20.D Equilibrium: the one-consumer case (pp. 743-754)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 744, footnote 9 | Consumption of a path; feasibility; bounded paths | `consumption`, `FeasiblePath` |
| (20.D.1), p. 744 | The accounting identity | `identity_20_D_1` |
| Definition 20.D.1, p. 744 | Walrasian equilibrium | `InBudget`, `UtilityMax`, `WalrasEq` (correction 3); instance `example_20_D_1_ii` |
| p. 745 | Monotonicity ⇒ finite wealth, binding budget | `budget_binds` |
| Proposition 20.D.1, p. 745 | Equilibrium satisfies TC | `proposition_20_D_1` |
| (ii'), Exercise 20.D.2, pp. 745, 784 | (ii') ⇔ (ii) with `w < ∞` | `TotalProfitMax`, `exercise_20_D_2_to`, `exercise_20_D_2_of` |
| Definition 20.D.2, p. 745 | Myopic utility maximization | `MyopicUtilityMax` |
| Exercise 20.D.3, (20.D.5), p. 745 | Characterization by first-order conditions | `Foc20D5`, `exercise_20_D_3` |
| (20.D.6), pp. 745-746 | (20.D.5) ⇔ (20.D.6) | `Foc20D6`, `foc_20_D_5_iff_20_D_6` |
| Proposition 20.D.2, p. 746 | (20.D.6) and `∑ p c = w` ⇒ optimal | `proposition_20_D_2` |
| Example 20.D.1, pp. 746-747 | Log utility: `p_t c_t = δ^t (1 - δ) w` | `example_20_D_1_foc` |
| Exercise 20.D.4, p. 784 | Constant savings rate | `exercise_20_D_4` |
| Example 20.D.1(i) | Exchange: prices `δ^t (1 - δ)/ω_t` | `example_20_D_1_i` |
| Example 20.D.1(ii) | Linear technology: full equilibrium | `linearTech`, `posOrthant1`, `logUtil`, `logUtil_concaveOn`, `logUtil_hasFDerivAt`, `example_20_D_1_ii` |
| Example 20.D.1(iii) | General `F` | `example_20_D_1_iii_false`, `example_20_D_1_iii_corrected` (correction 4) |
| Footnote 10, p. 746 | Log utility violates continuity at 0 | Handled by the consumption set `posOrthant1` |
| Exercise 20.D.1, p. 784 | Sequence of budget constraints | `exercise_20_D_1` |
| (20.D.7), Proposition 20.D.3, p. 747 | Equilibria solve the planning problem | `PlanOptimal`, `boundedStream_consumption`, `proposition_20_D_3` |
| Proposition 20.D.4, footnote 11, p. 748 | Planning solutions are equilibria | `proposition_20_D_4`, `partial_bounds`, `eventually_pos_of_hasDerivAt`, `BoundedPath.update` |
| Proposition 20.D.5, p. 749 | Existence of a planning optimum | `proposition_20_D_5`, `continuous_consumption`, `consumption_zero`, `summable_of_continuousOn` (correction 7) |
| Proposition 20.D.6, p. 749 | Uniqueness of the consumption solution | `proposition_20_D_6`, `consumption_mix` |
| (20.D.8), footnote 12, p. 750 | Reduced planning problem | `Admissible`, `reducedObjective`, `objective_20_D_8`, `OptimalFrom` |
| p. 750 | Strict concavity ⇒ unique solution | `optimal_unique` |
| (20.D.9), footnote 13, p. 750 | Euler equations, necessary at interior optima | `EulerEq`, `euler_of_shortRun`, `euler_of_optimal` |
| Example 20.D.2, p. 750 | Ramsey-Solow Euler equations | `example_20_D_2_deriv`, `example_20_D_2`, `example_20_D_2_ratio` |
| Example 20.D.3, footnotes 14-15, p. 751 | Cost of adjustment; iterated form (q-theory) | `example_20_D_3_deriv`, `example_20_D_3`, `hasSum_of_recursion`, `example_20_D_3_iterated`; footnotes verbal |
| Exercise 20.D.5, p. 784 | `F = k^α`, `γ = (k' - k)^β` | `powCost`, `exercise_20_D_5_gamma_deriv_zero`, `exercise_20_D_5_gamma_deriv_pos`, `exercise_20_D_5_gamma_deriv_neg`, `exercise_20_D_5_F_deriv`, `exercise_20_D_5_steady_state`; "say as much as you can" verbal |
| Exercise 20.D.6, p. 784 | Euler ⇔ short-run optimality | `euler_telescope`, `exercise_20_D_6` |
| p. 751, footnote 16 | Strictly interior paths | Hypothesis of `proposition_20_D_7` |
| Proposition 20.D.7, p. 751 | Euler + bounded + strictly interior ⇒ optimal | `proposition_20_D_7`, `abs_fderiv_le_of_concave`, `concave_le_fderiv_normed` (correction 8) |
| (20.D.10), p. 752 | Tails of optimal paths; policy function | `reducedObjective_succ`, `consPath`, `reducedObjective_consPath`, `optimal_tail`, `policy_20_D_10` |
| p. 752 | Euler shooting: at most one `k₁` gives a bounded interior path | `optimal_unique` with `proposition_20_D_7` |
| Example 20.D.4, Exercise 20.D.7, p. 753 | `k_{t+1} = 3k_t - 2k_{t-1}` and its solutions | `exercise_20_D_7_euler`, `example_20_D_4_deriv`, `exercise_20_D_7_solution`, `exercise_20_D_7_unique`, `example_20_D_4_consumption`, `example_20_D_4_negative`, `example_20_D_4_unbounded`, `example_20_D_4_bounded_iff`, `example_20_D_4_not_optimal`, `example_20_D_4_infeasible` (correction 6), `logRegion`, `example_20_D_4_optimal` |
| Footnote 17, p. 753 | Euler prices violate TC | `footnote_20_17` |
| (20.D.11), p. 753 | Bellman equation; uniqueness of its bounded solution | `IsValueFn`, `bellman_20_D_11`, `bellman_20_D_11_printed_false` (correction 5); uniqueness: `theorem_M_N_1` |
| Exercise 20.D.8(i)-(ii), (20.D.12) | Concavity; single-period perturbations | `exercise_20_D_8_i` (correction 9), `exercise_20_D_8_ii` |
| Exercise 20.D.9, footnote 18 | `V' = ∇₁u`, `V'' ≥ ∇²₁₁u` | `exercise_20_D_9_first`, `second_deriv_nonneg_of_isLocalMin`, `exercise_20_D_9_second` |
| Figure 20.D.1 | Value function majorized | Graphical (`exercise_20_D_8_ii`) |

## 20.E Stationary paths, interest rates and golden rules (pp. 754-759)

| Source | Claim | Lean |
| --- | --- | --- |
| Definition 20.E.1, p. 754 | Stationary paths | `IsStationary` |
| Proposition 20.E.1, footnote 19, p. 754 | Efficient stationary paths have proportional prices (smooth case) | `proposition_20_E_1`, `supporting_prices_proportional`, `propPrices`; nonsmooth OPEN (MWG: "too delicate") |
| p. 755, Exercise 20.E.1 | Interest rate `r = (1 - α)/α` | `exercise_20_E_1` |
| Proposition 20.E.2, footnote 20, p. 755 | Efficient if `r > 0`, inefficient if `r < 0` (smooth case) | `proposition_20_E_2_pos`, `proposition_20_E_2_neg`, `exists_mem_of_smooth_neg`, `clm_prod_eq_planValue` (correction 15) |
| p. 755 | Stationary equilibria are modified golden rules | `stationary_equilibrium_modified_golden_rule` |
| Definition 20.E.2, p. 755 | Modified golden rule; golden rule | `IsModifiedGoldenRule`, `IsGoldenRule` |
| p. 756 | Candidates independent of `u` | `stationary_equilibrium_modified_golden_rule` |
| p. 756 | `r_t` is the net marginal productivity of capital | `rs_interest_rate`, `hasDerivAt_capital` |
| p. 756, footnote 21 | Steady-state surplus, interest, supporting prices and wage | `rs_steady_prices` |
| p. 756 | Golden rule `r(k̂) = 0` maximizes surplus; modified golden rule | `golden_rule_iff`, `modified_golden_rule_iff`, `modified_golden_rule_below` |
| p. 756 | `k < k̂ ⇒ r > 0`; `k > k̂ ⇒ r < 0`, inefficient | `rate_pos_below_golden`, `rate_neg_above_golden`, `inefficient_above_golden` |
| p. 756, footnote 22, Figure 20.E.2 | The golden rule is efficient | `golden_rule_capital`, `golden_rule_efficient` (correction 12); supporting prices constant (`rs_steady_prices`) |
| Exercise 20.E.4, p. 784 | Three neoclassical properties | `exercise_20_E_4_i_mono`, `exercise_20_E_4_i_anti`, `exercise_20_E_4_ii`, `euler_homogeneous`, `exercise_20_E_4_iii_wage`, `exercise_20_E_4_iii`, with `chord_right_le`, `strict_tangent_below`, `strictMonoOn_left_of_max`, `strictAntiOn_right_of_max` |
| (20.E.1), Exercise 20.E.5, p. 758 | Multisector first-order conditions; `∇Ĝ = (r/s) q`; golden rule iff `r = 0` | `eq_20_E_1`, `golden_rule_multisector` |
| p. 758 | Golden rule efficient in the multisector model | `golden_rule_multisector_efficient` (correction 25), instance `golden_rule_quadratic_instance`; strict concavity needed: `golden_rule_linear_inefficient` |
| Figure 20.E.3, Exercise 20.E.6, p. 759 | Slope of the level curve is `1 + r` | `exercise_20_E_6`; several modified golden rules: graphical, not formalised |
| Exercise 20.E.7, p. 785 | Perfect substitutes ⇒ distinct interest rates | `exercise_20_E_7` |
| Exercise 20.E.2(a)-(b), p. 784 | Proportional paths under constant returns | `IsConeTech`, `smoothAt_smul_of_cone`, `malinvaud_prop_of_common_normal`, `exercise_20_E_2a`, `exercise_20_E_2b_pos`, `exercise_20_E_2b_neg` |
| Exercise 20.E.3, p. 784 | `k_t ≤ k̂ - ε` ⇒ efficient | `exercise_20_E_3` |
| Exercise 20.E.8, p. 785 | Growth golden rule `r = n` | `exercise_20_E_8_surplus`, `exercise_20_E_8` |
| Exercise 20.E.9, p. 785 | Golden rule is not an equilibrium | `exercise_20_E_9` |

## 20.F Dynamics (pp. 759-765)

| Source | Claim | Lean |
| --- | --- | --- |
| (20.F.1), p. 759 | Dynamics by iterating the policy function | `policy_20_D_10` |
| p. 760 | Steady state ⇔ `k = ψ(k)` | `steady_state_iff_fixed` |
| Figures 20.F.1-20.F.2 | Increasing `ψ`: convergence to a (the) steady state | `monotone_policy_converges`, `monotone_policy_converges_unique` |
| Figure 20.F.3 | Cycle of period 2 | `two_cycle_example` |
| Figure 20.F.4 | Cycle of period 3; chaos | `three_cycle_example`; "period three ⇒ chaos": OPEN (cited, Grandmont); Li-Yorke needs the interval-covering lemma (`f(I) ⊇ J` ⇒ a subinterval mapped onto `J`), itineraries for every period and an uncountable scrambled set; not formalised |
| p. 761, footnote 24, (20.F.2), Figure 20.F.5 | Boldrin-Montrucchio; complete impatience | OPEN (not stated precisely; continuity argument heuristic) |
| Exercise 20.F.1, p. 785 | Engel curves of a concave utility | `exercise_20_F_1_engel`; monotonicity and concavity for small `ε` OPEN: the choice of `ε` needs bounds on `γ_i'` and `γ_i''` on `(0, α]`, which the exercise does not give (the `γ_i` are `C²` only on `w > 0`, and the terms `(x_i - γ_i(w)) γ_i''(w)` of the Hessian need not be dominated by `-w^{-3/2}/4` as `w → 0`); with such bounds the Hessian computation was not formalised |
| p. 762, footnote 25, (20.F.3) | `ψ' = -∇²₂₁u/(∇²₂₂u + δV'')` | `policy_deriv` |
| p. 762 | Bound on `|ψ'|` | `policy_deriv_bound_printed_false`, `policy_deriv_lower_bound` (correction 10) |
| p. 763, footnote 26, Exercise 20.F.2 | Contraction ⇒ unique, globally stable steady state; cyclical convergence | `exercise_20_F_2`, `exercise_20_F_2_false` (correction 11), `footnote_20_26` |
| p. 763, footnote 27 | Turnpike theorem | `cycle_beaten_by_mean` (strict-concavity step); theorem OPEN (cited, McKenzie): needs the value-loss argument with uniform strict concavity near the steady state and compactness of feasible paths, not formalised |
| pp. 763-764, (20.F.4), Figure 20.F.6 | Positive cross derivative ⇒ increasing policy | `StrictIncDiff`, `increasing_differences_of_cross_pos`, `policy_mono_of_increasing_differences` |
| p. 764 | Uniqueness of the modified golden rule `F'(k) = 1/δ`; convergence | `modified_golden_rule_below`, `exercise_20_E_4_ii`, `monotone_policy_converges_unique` |
| p. 764 | Negative cross derivative ⇒ decreasing policy | `policy_anti_of_decreasing_differences` |
| Exercise 20.F.3, p. 785 | Cross-derivative sign in both models | `exercise_20_F_3_rs`, `exercise_20_F_3_adjustment` |
| p. 764 | Transitory and permanent shocks | Verbal (Exercises 20.F.4-20.F.5) |
| Example 20.F.1, Figure 20.F.7, p. 765 | Separable utility: constant policy | `example_20_F_1` |
| Exercise 20.F.4, p. 785 | Transitory shock | `exercise_20_F_4` |
| Exercise 20.F.5, p. 785 | Permanent shock: `k₁ᴾ ≥ k₁ᵀ` | `exercise_20_F_5` |

## 20.G Equilibrium: several consumers (pp. 765-769)

| Source | Claim | Lean |
| --- | --- | --- |
| Definition 20.G.1, footnote 28, p. 765 | Walrasian equilibrium with `I` consumers | `WalrasEqI`, `wealthI`, `walrasEqI_example` |
| Proposition 20.G.1, footnote 29, p. 766 | First welfare theorem | `FeasibleAlloc`, `sum_wealthI`, `exists_better_of_slack`, `proposition_20_G_1` |
| Proposition 20.G.2, footnote 30, p. 767 | Representative consumer with Negishi weights | `negishiUtility`, `weighted_supergradient`, `negishiUtility_props`, `proposition_20_G_2` (correction 18) |
| pp. 767-768 | Internal and external properties | Verbal |
| p. 768, footnote 31 | Negishi equations, generic finiteness | OPEN (Kehoe-Levine; infinite-horizon transversality theorem) |
| Footnote 32, Exercise 20.G.4 | Equilibria are repetitions of static equilibria, `p_t = δ^t p̄` | `StaticWalrasEq` (instance `staticWalrasEq_noTrade`), `static_foc`, `exercise_20_G_4_repetition`, `strictConcave_lt_fderiv`, `exercise_20_G_4_static` (correction 19) |
| (20.G.5)-(20.G.6), p. 769 | Externalities; implicit derivative | `eq_20_G_6` |
| p. 769 | `|dk_{t+1}/dk_t|, |dk_{t+1}/dk_{t-1}| < 1/2` ⇒ perturbations dampen | `dampening_of_small_coefficients` |
| p. 769 | Robust continua with externalities | OPEN (no explicit example given) |
| Exercise 20.G.1, p. 785 | Two consumers, one good | `exercise_20_G_1` |
| Exercise 20.G.2, p. 785 | Marginal utilities of wealth constant across periods | `ParetoOptimalExchange` (instance `paretoOptimalExchange_linear`), `discountedUtility_finite_change`, `pareto_ratio_core`, `exercise_20_G_2`, `exercise_20_G_2_ratio`; interpretation verbal |
| Exercise 20.G.3(a), p. 786 | Pareto frontier parametrized by the ratio of marginal utilities of wealth | `exercise_20_G_3a` |
| Exercise 20.G.3(b), p. 786 | Negishi equation: one equation in the ratio `r`, zeros = equilibria | `negishiPrice`, `exercise_20_G_3b` |
| Exercise 20.G.3(c), p. 786 | Generic finiteness of equilibria ("argue ... as precise as you can") | OPEN: needs the transversality (Sard) theorem of Section 17.D applied to the Negishi map; not available |
| Exercise 20.G.5, p. 786 | (20.G.6) exceeds one without externalities | `exercise_20_G_5` |

## 20.H Overlapping generations (pp. 769-777)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 770, footnote 33 | Generations, endowments, the asset | `olgWealth` |
| (20.H.1)-(20.H.2), Definition 20.H.1, p. 771 | Budgets; equilibrium | `OLGEq` (correction 16); instance `olg_autarky_linear` |
| p. 771, footnote 34 | Fundamental value bounds the asset price; `M ≥ 0` | `fundamental_value_bound` |
| p. 771 | No bubbles with finitely many consumers; Exercise 20.H.1 | `exercise_20_H_1` |
| Figures 20.H.1-20.H.2, p. 772 | Construction of equilibria; steady state `α = (1 - ε - γ)/(1 - γ)` | `olg_steady_alpha`; constructions graphical |
| p. 772 | Existence (Wilson 1981) | OPEN (cited): Brouwer/Kakutani (LeanEconomics.FixedPoint) would give equilibria of the `T`-truncated economies, but the truncation with a terminal generation, uniform price and consumption bounds, the diagonal limit and the preservation of optimality in the limit are not formalised |
| p. 773, footnote 35 | `ε > 0` ⇒ `∑ p_t < ∞` | Field `assetFinite` of `OLGEq` |
| Proposition 20.H.1, p. 773 | `∑ p_t < ∞` ⇒ Pareto optimal | `olg_budget_binds`, `olg_cost_ge`, `olg_cost_gt`, `olg_total_wealth`, `proposition_20_H_1` |
| p. 773 | Autarky equilibrium with `p_t/p_{t+1} = β` | `olg_autarky_equilibrium` |
| p. 773 | Autarky dominated when `β < 1` | `olg_autarky_dominated` |
| p. 774 | `p_{t+1} c_{at} = M`; `M = 0` only without trade | `olg_consumption_value`, `olg_nominal_identity`, `olg_bubble_zero_iff_autarky` |
| p. 774, Figure 20.H.3 | Monetary steady state; its optimality | `monetary_steady_state_prices_log` (correction 17); `monetaryCb`, `monetary_steady_state_optimal` (correction 20), instance `sqrt_utility_unique_max`, `monetary_steady_state_optimal_sqrt` |
| p. 774 | Optimal nominal equilibria ⇔ bubble bounded away from 0 | Stationary economy `√b + √a`: `OLGParetoOptimal` (instance `olgParetoOptimal_monetary`), `sqrtU`, `sqrt_demand`, `olg_sqrt_demand`, `olg_sqrt_classification`, `olg_sqrt_optimal_iff_bubble` (correction 24); general utilities OPEN (needs a Balasko-Shell/Okuno-Zilcha optimality criterion with curvature bounds) |
| Proposition 20.H.2, p. 775 | `∑ p_t < ∞` ⇒ `M = 0` | `proposition_20_H_2` |
| pp. 775-776, footnotes 36-37, Figure 20.H.4, (20.H.3) | Indeterminacy; determinacy condition | Nominal indeterminacy (continuum indexed by `r_0 ≥ 1`) in the `√b + √a` economy: `olg_sqrt_classification`; (20.H.3) holds there: `sqrt_determinacy_condition`; the general claim (uniqueness in the real-asset case under (20.H.3), continuum under its reverse) OPEN: needs a formal theory of offer-curve dynamics for general excess demand functions |
| Exercise 20.H.2(a), p. 786 | (20.H.3) ⇒ the steady state is the only real-asset equilibrium | OPEN: offer-curve dynamics for general excess demands not formalised |
| Exercise 20.H.2(b), p. 786 | (20.H.3) ⇒ monetary steady state is the only Pareto optimal nominal equilibrium | For the `√b + √a` economy (which satisfies (20.H.3)): `exercise_20_H_2b_sqrt`, `sqrt_determinacy_condition`; general excess demands OPEN (as (a)) |
| Exercise 20.H.2(c), p. 786 | (20.H.3) violated strictly at `p_b = p_a` ⇒ several Pareto optimal nominal equilibria | OPEN: needs local stable-manifold analysis of the offer-curve map at the steady state |
| Exercise 20.H.2(d), p. 786 | Conditions on `v`, `δ` for (20.H.3) with `u = v(c_b) + δ v(c_a)` | OPEN (open-ended; Example 17.F.2's computation not formalised) |
| p. 777 | Backward shift: onto linear map with nonzero kernel | `backward_shift` |
| Figures 20.H.5-20.H.6, footnote 38 | Cycles of period 2 and 3 (no inferior goods) | `cycleU`, `cycleCa`, `cycleCb`, `cyclePrice`, `figure_20_H_5_period_two`, `cycle3U`, `cycle3Ca`, `cycle3Cb`, `cycle3Price`, `figure_20_H_6_period_three` (correction 21) |

## 20.I Remarks on nonequilibrium dynamics (pp. 778-781)

| Source | Claim | Lean |
| --- | --- | --- |
| (20.I.1), footnote 39, p. 778 | First-order conditions with marginal utilities of wealth | `foc_20_D_5_iff_20_D_6` |
| p. 778 | Short-run price effects `λ_i (D²u_i)⁻¹` negative definite, also in aggregate | `shortRun_demand_derivative`, `shortRun_negDef`, `shortRun_aggregate_negDef` |
| p. 778 | Unique and globally tâtonnement stable short-run equilibrium | `unique_zero_of_negDef`; `sq_le_dotProduct_self`, `tatonnement_global_stable`, `tatonnement_global_stable_negDef` (correction 23), instance `tatonnement_linear_instance` |
| p. 779 | Patience makes changes in `λ_i` small | Verbal |
| Exercise 20.I.1, footnote 40, p. 779 | Law-of-demand identity | `exercise_20_I_1` |
| p. 779, footnote 41 | Stability ⇔ determinacy | Verbal (borderline cases neglected) |
| (20.I.2)-(20.I.3), footnotes 42-43, p. 780 | Temporary equilibrium; Walras' law | `learning_walras` |
| Footnote 44, Figure 20.I.1, p. 781 | Learning reverses equilibrium dynamics | `learning_reverses` |

## M.N Dynamic programming (pp. 968-970)

| Source | Claim | Lean |
| --- | --- | --- |
| (M.N.1), footnote 32, p. 968 | The problem; maximizer exists; value function | `mnReward`, `mnProgram`, `mnObjective`, `mnPlan`, `mnPlan_value`, `plan_value_eq`, `value_attained_M_N`, `summable_mnObjective` |
| p. 968 | `v` continuous; concave if `A` convex, `u` concave | `value_continuous_M_N`, `value_concave_M_N` |
| p. 969 | Bellman equation | `bellman_M_N` |
| Theorem M.N.1, (M.N.2), p. 969 | Continuous solutions of the Bellman equation equal `v` | `theorem_M_N_1` |
| p. 969 | Value function iteration converges | `value_iteration_M_N`, `value_iteration_pointwise_M_N` |
| (M.N.3)-(M.N.4), footnote 33, pp. 969-970 | Euler equations | `euler_M_N_4` |
