# Source map

Andreu Mas-Colell, Michael D. Whinston and Jerry R. Green, *Microeconomic Theory*, Chapter 10,
"Competitive Markets", pp. 311-349. Printed pages; Lean names relative to
`MWG.CompetitiveMarkets`. All definitions, the lemma, both propositions, all examples, the
mathematical claims of the text, small type and footnotes, and every end-of-chapter exercise
subpart (10.B.1-10.G.5; the chapter has no in-text exercises other than references to these
and no appendix) are covered. Purely verbal discussion is identified below. No item is OPEN.
Departures are numbered as in [corrections](corrections.md). Results imported from earlier
chapters are named with their package: `MWGProduction` (Chapter 5), `MWGClassicalDemand`
(Chapter 3) and `MWGConsumerChoice` (Chapter 2), at the worktree's current commit.

## Section 10.A and 10.B: Pareto optimality and competitive equilibria

| Source | Claim | Lean |
| --- | --- | --- |
| Section 10.A, pp. 311-312 | Introduction | Verbal |
| p. 312 | Economy: `Xᵢ`, `uᵢ`, `ω`, `Yⱼ` | `Economy`, `Allocation` |
| Definition 10.B.1, p. 312 | Allocation, feasibility | `Economy.IsAllocation`, `Economy.IsFeasible`, `definition_10_B_1` |
| Definition 10.B.2, p. 313 | Pareto optimality | `Economy.IsParetoOptimal`, `definition_10_B_2` |
| p. 313, Figure 10.B.1 | Utility possibility set; Pareto optimal = undominated boundary points | `Economy.utilityPossibilitySet`, `mem_utilityPossibilitySet`, `isParetoOptimal_iff_undominated` (any number of consumers) |
| p. 313 | Pareto optimality and equity | Verbal |
| p. 314 | Private ownership economy, shares, wealth | `PrivEconomy`, `PrivEconomy.toEconomy`, `PrivEconomy.wealth` |
| Definition 10.B.3, p. 314 | Competitive equilibrium (10.B.1)-(10.B.3); profit maximization is Chapter 5's `supply`, utility maximization Chapter 3's `walrasianDemandOn` | `PrivEconomy.IsCompetitiveEqm`, `definition_10_B_3`, `PrivEconomy.IsCompetitiveEqm.isFeasible` (via `MWGProduction` `supply`, `MWGClassicalDemand` `walrasianDemandOn`, `MWGConsumerChoice` `budgetSetOn`) |
| pp. 314-315, footnotes 1-2, small type | Price taking; why markets clear; zero prices | Verbal |
| p. 316; Exercise 10.B.2 | Scaling prices by `α > 0` | `exercise_10_B_2` (correction 4) |
| Lemma 10.B.1 and proof, p. 316 | Clearing of `L - 1` markets implies the last | `lemma_10_B_1`, `lemma_10_B_1_strictlyPositive` (correction 5) |

## Section 10.C: partial equilibrium competitive analysis

| Source | Claim | Lean |
| --- | --- | --- |
| p. 316, footnotes 3-4 | Motivation of partial equilibrium | Verbal (Exercise 10.C.1 below) |
| p. 317 | Quasilinear consumers: `φ` bounded, `φ' > 0`, `φ'' < 0`, `φ(0) = 0` on `x ≥ 0` | `QLConsumer` (derivatives within `[0, ∞)`) |
| p. 317, footnote 5 | Firms: `cⱼ' > 0`, `cⱼ'' ≥ 0`; `Yⱼ = {(-z, q)}` | `QLFirm`, `qlEconomy`, `qlEconomyOf`, `qlPrice`, `qlPrice_dot` |
| p. 317 | Firm's problem, FOC necessary and sufficient | `ql_supply_iff`, `QLFirm.max_iff`, `foc_max_iff`, `foc_max_necessary` |
| p. 318 | Consumer's problem, budget binds, FOC necessary and sufficient | `ql_demand_iff`, `QLConsumer.max_iff`, `ql_wealth` |
| p. 318, (10.C.1)-(10.C.3) | Characterization of equilibria; allocation from levels of good `ℓ` | `IsQLEqm`, `qlAllocation`, `ql_isCompetitiveEqm_iff` |
| p. 318, footnote 6 | `p* > 0` | `ql_eqm_price_pos`, `IsQLEqm.price_pos` |
| p. 318 | Positive aggregate if `maxᵢ φᵢ'(0) > minⱼ cⱼ'(0)` | `IsQLEqm.aggregate_pos` |
| pp. 318-319, footnote 7 | Independence of endowments and shares | `ql_isCompetitiveEqm_of_isQLEqm` |
| p. 319, Figure 10.C.1 | `φ'` strictly decreasing onto `(0, φ'(0)]`; demand `xᵢ(p)`: zero iff `p ≥ φᵢ'(0)`, continuous, nonincreasing, strictly decreasing below `φᵢ'(0)`, `xᵢ' = 1/φᵢ''` | `QLConsumer.dφ_strictAnti`, `QLConsumer.exists_dφ_lt`, `QLConsumer.dφ_surj`, `QLConsumer.demand`, `QLConsumer.demand_spec`, `QLConsumer.demand_eq`, `QLConsumer.demand_eq_zero_iff`, `QLConsumer.demand_continuousAt`, `QLConsumer.demand_antitoneOn`, `QLConsumer.demand_strictAnti`, `QLConsumer.demand_hasDerivAt`, `QLConsumer.demand_deriv_neg` (via `focSol`, `focSol_continuousAt`, `focSol_hasDerivAt`) |
| p. 319 | Aggregate demand: continuous, nonincreasing, strictly decreasing below `maxᵢ φᵢ'(0)`, zero above | `aggDemand`, `aggDemand_continuousOn`, `aggDemand_antitoneOn`, `aggDemand_strictAnti`, `aggDemand_eq_zero_iff` |
| p. 319, footnote 8, Figure 10.C.2 | Supply `qⱼ(p)` for strictly convex costs with `c' → ∞`; `qⱼ' = 1/cⱼ''` | `QLFirmStrict`, `QLFirmStrict.supply`, `QLFirmStrict.supply_foc`, `QLFirmStrict.supply_eq`, `QLFirmStrict.supply_eq_zero_iff`, `QLFirmStrict.supply_continuous`, `QLFirmStrict.supply_monotone`, `QLFirmStrict.supply_strictMono`, `QLFirmStrict.supply_hasDerivAt`; `cubicFirm`, `supply_not_differentiable_example` (correction 1) |
| pp. 319-320 | Aggregate supply | `aggSupply`, `aggSupply_continuous`, `aggSupply_monotone`, `aggSupply_strictMono`, `aggSupply_eq_zero_iff` |
| p. 320, Figure 10.C.3, footnote 9 | Existence and uniqueness of `p* ∈ (minⱼ cⱼ'(0), maxᵢ φᵢ'(0))` and of the allocation | `ql_eqm_exists`, `ql_eqm_unique`; footnote 9 verbal |
| pp. 320-321 | Merely convex costs: existence (via surplus maximization) and uniqueness of price and consumptions | `optimalLevels_exist`, `ql_eqm_exists_convex`, `ql_competitiveEqm_exists_convex`, `ql_eqm_unique_convex`, `inst_convex_existence` (correction 2) |
| p. 320, footnote 10 | Linear costs: supply infinite above `c` | `footnote_10_C_10`, `linearFirm` |
| p. 321, Figure 10.C.4 | Constant returns: `p* = c`, outputs indeterminate | `figure_10_C_4_price`, `figure_10_C_4_indeterminate` |
| p. 321, Figure 10.C.5, footnotes 11-12 | `q⁻¹ = C'`, the industry marginal cost | `invSupply`, `invSupply_aggSupply`, `invSupply_hasDerivAt`, `minCost`, `exercise_10_C_3c_strict` |
| pp. 321-322, Figure 10.C.6 | Inverse demand `P = x⁻¹`; `φᵢ'(xᵢ) = P(x)` | `invDemand`, `invDemand_aggDemand`, `aggDemand_invDemand`, `invDemand_strictAntiOn`, `invDemand_continuousAt`, `exercise_10_C_4b` |
| p. 322 | Price as marginal social benefit and marginal cost | `exercise_10_C_4b`, `invSupply_hasDerivAt` |
| pp. 322-323, (10.C.4)-(10.C.6) | Comparative statics system | Instantiated in Example 10.C.1 and Exercise 10.C.5 |
| Example 10.C.1, pp. 323-324, (10.C.7)-(10.C.8), Figure 10.C.7 | Sales tax: `p*(t)`, monotone comparative statics, `p*' = -x'/(x' - q')`, `-1 ≤ p*' < 0`, `p*' = -1` when `q' = 0`, formula in `φᵢ''`, `cⱼ''` | `taxRange`, `taxPrice`, `taxPrice_spec`, `taxPrice_unique`, `taxQuantity`, `example_10_C_1_monotone`, `taxPrice_continuousAt`, `eq_10_C_8`, `example_10_C_1_bounds`, `example_10_C_1_formula`, `example_10_C_1_instance`, `invDemand_hasDerivAt` (correction 12) |
| pp. 324-325, Figure 10.C.8, footnotes 13-14 | Nonexistence with a nonconvex technology | `figure_10_C_8_cost`, `figure_10_C_8_no_equilibrium` |

## Section 10.D: the fundamental welfare theorems

| Source | Claim | Lean |
| --- | --- | --- |
| p. 325, (10.D.1), Figure 10.D.1 | Utility vectors for fixed levels of good `ℓ`: a half-space with normal `(1, …, 1)` | `eq_10_D_1` |
| p. 325 | Pareto optimal allocations maximize aggregate surplus and waste nothing | `ql_pareto_iff_le`, `ql_pareto_iff`, `ql_feasible_iff`, `ql_utility`, `ql_sum_utility_le`, `ql_reduce` |
| footnote 15, p. 325 | Uniqueness of optimal consumption and aggregate production; PO allocations differ only in the numeraire | `footnote_10_D_15`, `exercise_10_D_1`, `exercise_10_D_1_strict` |
| (10.D.2), p. 326 | Optimal levels; Marshallian aggregate surplus | `qlSurplus`, `IsOptimalLevels` |
| (10.D.3)-(10.D.5), p. 326 | FOC necessary and sufficient; same as (10.C.1)-(10.C.3) with `μ` | `optimalLevels_foc`, `IsQLEqm.isOptimalLevels`, `optimalLevels_iff_foc` |
| Proposition 10.D.1, p. 326 | First welfare theorem | `proposition_10_D_1`, `ql_eqm_sum_utility`; instance `inst_equilibrium_pareto` |
| pp. 327-328 | Prices equal shadow prices | `optimalLevels_iff_foc` (the multiplier `μ` of (10.D.2) is `p*`) |
| Proposition 10.D.2, p. 327 | Second welfare theorem | `proposition_10_D_2_convex` (convex costs, no presupposed equilibrium), `proposition_10_D_2_of_exists`, `proposition_10_D_2`, `IsOptimalLevels.surplus_eq`; instances `inst_second_welfare`, `inst_proposition_10_D_2_convex` (correction 2) |
| p. 327 | Convexity needed for the second theorem, not the first | Verbal (see `lr_maximizes_surplus`) |
| (10.D.6), small type p. 328 | Alternative characterization | `Economy.Solves10D6`, `exercise_10_D_3_pareto`, `exercise_10_D_3_of_pareto` |

## Section 10.E: welfare analysis

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 328-329, footnote 16, Figure 10.E.1 | With optimal lump-sum redistribution welfare rises iff aggregate surplus rises, for any (strictly increasing) social welfare function | `redistributionSet`, `welfare_lt_iff_surplus_lt`, `eq_10_D_1`; instance `inst_welfare_lt` |
| (10.E.1), p. 329 | Aggregate surplus | `qlSurplus` |
| footnote 17, p. 329 | Utilitarian `W`: no transfers needed | `footnote_10_E_17` |
| (10.E.2)-(10.E.4), p. 330, footnote 18 | `dS = [P(x) - C'(x)] dx` | `eq_10_E_4`; footnote 18 verbal |
| (10.E.5), p. 330, Figure 10.E.2 | `S(x) = S₀ + ∫₀ˣ [P - C']`, `S₀ = 0` if `cⱼ(0) = 0` | `aggSurplus`, `eq_10_E_5`, `aggSurplus_zero_of_cost_zero`, `aggSurplus_hasDerivAt`, `aggSurplus_continuousOn`, `grossBenefit_eq_integral`, `minCost_eq_integral` |
| p. 331, footnote 19 | `S` concave, `S' = P - C'`, maximized at the competitive aggregate | `footnote_10_E_19_concave`, `footnote_10_E_19`, `competitive_maximizes_surplus` |
| Example 10.E.1, (10.E.6), pp. 331-332, Figure 10.E.3, footnote 20 | Deadweight loss is negative; `S*'(0) = 0` | `deadweight_loss_neg`, `example_10_E_1`, `example_10_E_1_first_order` |
| (10.E.7), p. 332, footnote 21 | `CS(p̂) = ∑ φᵢ(xᵢ(p̂)) - p̂x(p̂) = ∫₀^{x(p̂)} [P - p̂]` | `consumerSurplus`, `eq_10_E_7` |
| (10.E.8), p. 333, footnote 22 | `CS(p̂) = ∫_{p̂}^∞ x` | `eq_10_E_8`, `consumerSurplus_hasDerivAt`, `QLConsumer.surplus_hasDerivAt` |
| (10.E.9), p. 333 | Change in consumer surplus | `eq_10_E_9` |
| (10.E.10)-(10.E.11), p. 333, footnote 23 | Producer surplus `Π = Π₀ + ∫₀^{q(p̂)} [p̂ - C'] = Π₀ + ∫₀^{p̂} q`, `Π₀ = -∑ cⱼ(0)` | `producerSurplus`, `eq_10_E_10`, `eq_10_E_11`, `producerSurplus_hasDerivAt`, `QLFirmStrict.profit_hasDerivAt`, `producerSurplus_eq_of_le` |
| (10.E.12), p. 333 | Change in producer surplus | `eq_10_E_12` |
| p. 333 | Tax revenue; deadweight loss = losses of CS and PS less revenue | `example_10_E_1_decomposition` |
| Small type, pp. 333-334, footnote 24 | Normative representative consumer; CV = EV = change in consumer surplus for quasilinear utility | `ql_indirect_utility`, `ql_cv_eq_ev` (cf. `MWGClassicalDemand` `exercise_3_I_5`) |
| p. 334 | Potential Pareto improvement iff surplus increases | `potential_pareto_iff` |
| p. 334 | Warning on undistorted other markets | Verbal; Exercise 10.G.3 |

## Section 10.F: free entry and long-run equilibria

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 334-335 | Free entry, `c(0) = 0`, no sunk costs | Verbal; `IsProfitMax` |
| Definition 10.F.1, p. 335 | Long-run competitive equilibrium | `IsLREqm`, `definition_10_F_1`, `IsLREqmReal` |
| footnote 25, p. 335 | At most one positive output with strictly convex costs | `footnote_10_F_25` |
| p. 335, footnote 26 | Long-run supply correspondence; additive closure (Exercise 5.B.4) | `PosProfit`, `InLRSupply`, `posProfit_unbounded`; `lr_technology_not_closed` (via `MWGProduction` `exercise_5_B_4_not_closed`) |
| footnote 27, p. 336 | `x(p*) ∈ Q(p*)` iff equilibrium price | `footnote_10_F_27` |
| p. 336, Figure 10.F.1 | Constant returns: `p* = c`, indeterminacy, `Q(p)` | `lr_crs`, `lr_crs_indeterminate`, `lrSupply_crs` |
| pp. 336-337, Figure 10.F.2 | Strictly convex costs: no equilibrium; `Q(p)` | `lr_strictConvex_nonexistence`, `lrSupply_strictConvex`, `exercise_10_F_1` |
| p. 337, Figure 10.F.3 | Nonclosed long-run technology; `c'(Q/J) → c'(0)` never reached | `lr_technology_not_closed`, `figure_10_F_3` |
| pp. 337-338, Figure 10.F.4 | Efficient scale: `p* = c̄`, `q* = q̄`, `J* = x(c̄)/q̄`, `Q(p)`; same as constant returns at `c̄` | `IsEfficientScale`, `IsEfficientScale.le_cost`, `lr_efficientScale`, `lrSupply_efficientScale`; instance `inst_lr_efficientScale` |
| footnote 28, p. 338 | `c'(q*) = p* = c(q*)/q*`; U-shaped AC gives `q* = q̄` | `footnote_10_F_28`, `footnote_10_F_28_ushaped` (via `MWGProduction` `exercise_5_D_1`) |
| p. 338 | Integer problem | `lr_integer_problem`; small-market discussion verbal |
| p. 339, footnote 29 | Range of efficient scales | `footnote_10_F_29` |
| p. 339 | Oligopoly approximation (Chapter 12) | Verbal |
| p. 339 | Long-run equilibrium maximizes surplus without convexity | `lr_maximizes_surplus` |
| pp. 339-340, (10.F.1)-(10.F.2) | Long- and short-run costs with lumpy fixed costs | `lumpyCost`; short-run cost `K + ψ` |
| Example 10.F.1, pp. 340-341, Figure 10.F.5 | Short-run price below `c̄`, losses, exit to `J₁ < J₀` | `example_10_F_1`, `example_10_F_1_instance` |
| Small type, p. 341 | Limits of the two-period dichotomy | Verbal |

## Section 10.G: concluding remarks

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 341-342 | Premises of partial equilibrium analysis | Verbal |
| p. 342, footnote 30 | Nonsubstitution theorem keeps other prices fixed | Verbal (Chapter 5, `MWGProduction` Proposition 5.AA.2) |
| p. 342 | Group of `M` goods with quasilinear utility; wealth irrelevant | `group_ump_iff`, `IsGroupEqm`, `groupSurplus` |
| p. 342 | Uniqueness and welfare theorems extend | `IsGroupEqm.maximizes`, `exercise_10_G_1_unique`, `exercise_10_G_1_unique_strict` |
| footnote 31, p. 343 | Separable good `ℓ` decouples | `exercise_10_G_2_consumer`, `exercise_10_G_2_surplus`, `dot_split` |
| p. 343 | Wealth effects matter for welfare, less for positive analysis | Verbal |
| footnote 32, p. 343 | Backward-bending demand with endowments of good `ℓ` | `footnote_10_G_32`, `footnote_10_G_32_increasing` |

## Exercises

| Source | Claim | Lean |
| --- | --- | --- |
| Exercise 10.B.1(a) | Strong ⇒ weak Pareto efficiency | `Economy.IsWeaklyParetoOptimal`, `exercise_10_B_1a` |
| Exercise 10.B.1(b) | Equivalence for continuous strongly monotone utilities on `ℝ^L_+` | `exercise_10_B_1b`, `exercise_10_B_1b_general` (no interiority); instance `inst_exercise_10_B_1b` (correction 3) |
| Exercise 10.B.1(c) | Example where they differ; role of monotonicity and interiority | `exercise_10_B_1c_economy`, `exercise_10_B_1c`, `exercise_10_B_1b_general` |
| Exercise 10.B.2 | Scaling prices | `exercise_10_B_2` |
| Exercise 10.C.1(a) | Log Cobb-Douglas demand and wealth effect | `exercise_10_C_1a`, `exercise_10_C_1a_wealth` |
| Exercise 10.C.1(b) | Wealth effect vanishes as `L` and `w` grow | `exercise_10_C_1b` |
| Exercise 10.C.2(a) | First-order conditions | `exercise_10_C_2a`, `logConsumer_max` |
| Exercise 10.C.2(b) | Equilibrium `p = σ`, `x = q = β/σ`; dependence on `α, β, σ` | `exercise_10_C_2b`, `exercise_10_C_2b_statics` |
| Exercise 10.C.3(a) | FOC of the cost minimization | `costSet`, `IsCostFOC`, `exercise_10_C_3a`, `exercise_10_C_3a_sufficient`, `foc_cost_ge`, `minCost_eq_of_foc` (correction 13) |
| Exercise 10.C.3(b) | `C'(q) = cⱼ'(qⱼ*)` | `exercise_10_C_3b` |
| Exercise 10.C.3(c) | Profit maximization at `C'(q)` gives `q`; `C' = q⁻¹` | `exercise_10_C_3c`, `exercise_10_C_3c_strict`, `invSupply_hasDerivAt` |
| Exercise 10.C.4(a) | Central authority's problem and FOC | `benefitSet`, `grossBenefit`, `exercise_10_C_4a`, `foc_benefit_le` (correction 14) |
| Exercise 10.C.4(b) | `P(x) = γ'(x) = φᵢ'(xᵢ*)` | `exercise_10_C_4b`, `hasDerivAt_of_sandwich` |
| Exercise 10.C.4(c) | `P` is the inverse of aggregate demand | `exercise_10_C_4c` |
| Exercise 10.C.5 | Implicit-function derivation of `dp*/dt` | `exercise_10_C_5`, `exercise_10_C_5_derived` (paths derived), instance `inst_exercise_10_C_5` (correction 15) |
| Exercise 10.C.6(a) | Specific tax: who pays is irrelevant | `exercise_10_C_6a` |
| Exercise 10.C.6(b) | Ad valorem: producer collection raises consumer cost; inelastic-supply special case; equivalent rates | `exercise_10_C_6b`, `exercise_10_C_6b_inelastic`, `exercise_10_C_6b_equivalent` |
| Exercise 10.C.7 | Constant-elasticity incidence, polar cases and limits | `exercise_10_C_7_price`, `exercise_10_C_7_elasticity`, `exercise_10_C_7_limits` |
| Exercise 10.C.8(a) | `dπ/dα = p*'q* - c_α` | `exercise_10_C_8a`, `price_response_cost_param`, `hasDerivAt_comp_pair` |
| Exercise 10.C.8(b) | Weakest condition `∂MC/∂α < ∂AC/∂α`; converse | `exercise_10_C_8b`, `exercise_10_C_8b_AC`, `exercise_10_C_8b_converse` (correction 6) |
| Exercise 10.C.8(c) | Factor-demand form | `exercise_10_C_8c` |
| Exercise 10.C.9 | Price falls with `w_k` iff `k` inferior | `exercise_10_C_9`, `price_response_cost_param` |
| Exercise 10.C.10 | Equilibrium and comparative statics with constant elasticities | `exercise_10_C_10`, `exercise_10_C_10_statics` |
| Exercise 10.C.11 | Profit difference `-c_α Δα` | `exercise_10_C_11` |
| Exercise 10.D.1 | Uniqueness of optimal levels | `exercise_10_D_1`, `exercise_10_D_1_strict` |
| Exercise 10.D.2 | Optimal levels for Exercise 10.C.2's economy | `exercise_10_D_2` |
| Exercise 10.D.3 | (10.D.6) solutions are Pareto optimal and conversely | `exercise_10_D_3_pareto`, `exercise_10_D_3_of_pareto` |
| Exercise 10.D.4 | FOC of (10.D.6) are (10.D.3)-(10.D.5) | `exercise_10_D_4`, `exercise_10_D_4_converse` |
| Exercise 10.E.1 | Domestic welfare derivative | `exercise_10_E_1_deriv`, `exercise_10_E_1_foreign_price`, `hasDerivAt_comp_two` |
| Exercise 10.E.1(a) | Small tariff raises welfare (strictly convex foreign costs) | `exercise_10_E_1a`, `exercise_10_E_1a_derived` (path derived via `implicit_path`, `implicit_1d`), instance `inst_exercise_10_E_1a` |
| Exercise 10.E.1(b) | Small tariff lowers welfare (constant returns abroad) | `exercise_10_E_1b` |
| Exercise 10.E.2 | `∫₀^{x(p̂)} [P - p̂] = ∫_{p̂}^∞ x` | `exercise_10_E_2` (correction 9) |
| Exercise 10.E.3(a) | Equivalent tax vectors; `t₁ = 0` | `exercise_10_E_3a`, `exercise_10_E_3a_normalize` |
| Exercise 10.E.3(b) | Ramsey inverse elasticity rule | `exercise_10_E_3b_lagrange` (multiplier from Lagrange's theorem), `ramsey_strict`, `exercise_10_E_3b_marginal`, `exercise_10_E_3b`, instance `inst_exercise_10_E_3b` (correction 16) |
| Exercise 10.E.3(c) | Equal rates, inelastic goods, taxing good 1 only | `exercise_10_E_3c`, `exercise_10_E_3c_good_one` |
| Exercise 10.F.1 | `π(p) > 0` iff `p > c'(0)` | `exercise_10_F_1`; instance `inst_exercise_10_F_1` |
| Exercise 10.F.2(a) | Long-run equilibrium with `A - Bp` and `K + αq + βq²`; dependence on `A` | `quadLumpyCost`, `quadLumpy_efficientScale`, `quadLumpy_book`, `lr_efficientScale_real`, `exercise_10_F_2a`, `exercise_10_F_2a_statics` |
| Exercise 10.F.2(b) | Short-run response, limit as `A → ∞`, explanation | `exercise_10_F_2b_supply`, `exercise_10_F_2b`, `exercise_10_F_2b_limit` (correction 10) |
| Exercise 10.F.3 | Ad valorem vs. lump-sum taxes after long-run adjustment | `exercise_10_F_3_printed`, `exercise_10_F_3_scale`, `exercise_10_F_3_prices`, `exercise_10_F_3_inelastic`, `exercise_10_F_3_counterexample` (correction 7) |
| Exercise 10.F.4 | `p*(w)` nondecreasing, HD1, concave | `exercise_10_F_4` (correction 11) |
| Exercise 10.F.5(a) | Long-run supply response exceeds short-run | `exercise_10_F_5a` (via `MWGProduction` `exercise_5_D_3`) |
| Exercise 10.F.5(b) | Smaller long-run price response, larger quantity response | `exercise_10_F_5b_deriv`, `exercise_10_F_5b` |
| Exercise 10.F.6 | Cobb-Douglas long-run price/quantity; short-run industry supply | `exercise_10_F_6_longRun` (via `MWGProduction` `example_5_C_1_cost`), `exercise_10_F_6_shortRun` |
| Exercise 10.F.7 | Kink in short-run cost; variability of prices and quantities | `srCost`, `exercise_10_F_7_leontief`, `exercise_10_F_7_leontief_kink`, `exercise_10_F_7_vertical_supply`, `exercise_10_F_7_cd_longRun`, `exercise_10_F_7_cd_shortRun`, `exercise_10_F_7_cd_smooth` (correction 8) |
| Exercise 10.G.1 | Equilibrium equations, wealth independence, uniqueness | `IsGroupEqm`, `group_ump_iff`, `group_consumer_foc`, `group_firm_foc`, `orthant_coord_foc`, `IsGroupEqm.maximizes`, `exercise_10_G_1_unique`, `exercise_10_G_1_unique_strict` (correction 17) |
| Exercise 10.G.2 | Separability; surplus of good `ℓ`; full separability | `exercise_10_G_2_consumer`, `exercise_10_G_2_surplus`, `exercise_10_G_2_full` |
| Exercise 10.G.3(a)-(b) | Single-market measure; substitutes overstate, complements understate the loss; correct measure | `exercise_10_G_3_4`, `exercise_10_G_3` |
| Exercise 10.G.4 | Welfare loss from raising both taxes | `exercise_10_G_4` |
| Exercise 10.G.5(a) | Effect on the price of good 3 | `exercise_10_G_5a` |
| Exercise 10.G.5(b) | Bias of the fixed-`p₃` formula | `exercise_10_G_5b` |

## Supporting results

| Lean | Content |
| --- | --- |
| `foc_max_iff`, `foc_max_necessary`, `foc_local_necessary`, `foc_tangent_le`, `foc_le_tangent_convex` | Kuhn-Tucker conditions on `ℝ₊` |
| `IsFOCSol`, `focSol` and lemmas | The solution of `d(x) ≤ r` (equality if `x > 0`), continuity and derivative |
| `hasDerivAt_of_sandwich`, `remainder_isLittleO` | Envelope-type differentiability |
| `expConsumer`, `expConsumer_demand`, `linearFirm`, `quadFirm`, `quadFirm_supply`, `instC`, `instF`, `inst_gap` | Concrete consumers and firms |
| `continuousAt_of_antitoneOn_of_image_mem_nhds`, `hasDerivAt_comp_pair`, `hasDerivAt_comp_two` | Calculus helpers |
| `implicit_1d`, `implicit_path` | One-variable implicit function theorem; existence and continuity of an equilibrium path |
