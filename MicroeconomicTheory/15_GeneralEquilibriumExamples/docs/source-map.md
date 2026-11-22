# Source map

Andreu Mas-Colell, Michael D. Whinston and Jerry R. Green, *Microeconomic Theory*, Chapter 15,
"General Equilibrium Theory: Some Examples", pp. 515-544, with the Part Four introduction
(pp. 511-514). Printed pages; Lean names relative to `MWG.GeneralEquilibriumExamples`. All
definitions, both propositions, both examples, the precise claims of the text, small type and
footnotes, and every exercise subpart (15.B.1-15.D.9, including the in-text Exercise 15.D.1) are
listed. The figures without formulas (15.B.10, 15.B.14, 15.C.3) are given concrete economies with
the features described. No item is OPEN.
Departures are numbered as in [corrections](corrections.md). Results imported from earlier
chapters are named with their package: `MWGCompetitiveMarkets` (Chapter 10), `MWGClassicalDemand`
(Chapter 3) and `MWGConsumerChoice` (Chapter 2).

## Part Four introduction and Section 15.A (pp. 511-515)

| Source | Claim | Lean |
| --- | --- | --- |
| Part Four introduction, pp. 511-514 | Methodology and plan of Part IV; quasilinear groups admit a representative consumer (refers to Chapters 4 and 10) | Verbal; no new mathematical claim |
| Section 15.A, p. 515 | Overview of the chapter | Verbal |

## Section 15.B: pure exchange and the Edgeworth box (pp. 515-525)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 515-516 | Pure exchange economy, Edgeworth box economy (consumption sets `ℝ²₊`), total endowment | `ExchangeEconomy`, `EdgeworthEconomy`, `ExchangeEconomy.ofOrthant`, `ExchangeEconomy.totalEndowment` (general `I`, `L`, `Xᵢ`; see correction 1) |
| (15.B.1), p. 516 | Feasible allocations; nonwasteful allocations = points of the box | `ExchangeEconomy.IsAllocation`, `ExchangeEconomy.IsFeasible`, `ExchangeEconomy.InBox`, `ExchangeEconomy.InBox.isFeasible`, `ExchangeEconomy.inBox_endowment` |
| p. 517 | Budget set `Bᵢ(p)`, demand `xᵢ(p, p·ωᵢ)` | `ExchangeEconomy.budget`, `ExchangeEconomy.demand` |
| p. 517, footnote 3 | Only allocations on the budget line are affordable to both consumers | `budget_line_of_inBox` |
| Footnote 2, p. 517 | Budget sets may extend outside the box | Graphical |
| p. 517 | Offer curve; every point weakly preferred to the endowment | `ExchangeEconomy.offerCurve`, `offerCurve_ge_endowment` |
| pp. 517-518 | The offer curve passes through the endowment, tangent to the indifference curve | `endowment_mem_offerCurve` (convex, differentiable, `∇u(ω) ≫ 0`), instance `endowment_mem_offerCurve_instance`, Cobb-Douglas `cd_endowment_mem_offerCurve`; false in general: `fig_15_B_10a_endowment_not_optimal` (correction 2) |
| Figures 15.B.1-15.B.6 | Box, budget sets, preferences, demand, excess demand | Graphical |
| Definition 15.B.1, p. 519 | Walrasian equilibrium (as printed) and demand form; equivalent under local nonsatiation; Definition 10.B.3 with no firms | `ExchangeEconomy.IsWalrasEqm`, `ExchangeEconomy.IsDemandEqm`, `ExchangeEconomy.IsDemandEqm.isWalrasEqm`, `isWalrasEqm_iff_isDemandEqm`, `ExchangeEconomy.toPrivEconomy`, `isDemandEqm_iff_competitiveEqm` |
| p. 519 | At an equilibrium the offer curves intersect; every intersection other than `ω` is an equilibrium | `offerCurve_of_isDemandEqm`, `isDemandEqm_of_offerCurves`, `proportional_of_orthogonal` |
| p. 519 | Demand is homogeneous of degree zero; `αp*` is an equilibrium price vector | `ExchangeEconomy.budget_smul`, `ExchangeEconomy.demand_smul`, `isWalrasEqm_smul`, `isDemandEqm_smul` |
| Example 15.B.1, pp. 519-520 | Offer curves; demand monotonicity in `p₁`; (15.B.2) `p₁/p₂ = α/(1-α)`; the second market clears too | `example_15_B_1_offerCurves`, `example_15_B_1_monotone`, `example_15_B_1`, `cd_demand_eq`, `cd_demand_empty` |
| p. 521 | Uniqueness in Figure 15.B.7 (refers to Exercise 15.B.2) | `exercise_15_B_2` |
| Example 15.B.2, pp. 521-522 | Quasilinear economy with three equilibria `p₁/p₂ ∈ {1/2, 1, 2}`; `r > 0`; offer curves `≫ 0`; demand for good 1 may rise with `p₁` | `ex15B2Economy`, `ex15B2r_bounds`, `exercise_15_B_5_offerCurves`, `exercise_15_B_5_printed`, `ex15B2_roots`, `ex15B2_factor`, `example_15_B_2`, `example_15_B_2_increasing` (correction 3) |
| Figure 15.B.10(a), p. 522 | Endowment on the boundary; consumer 2 keeps `ω₂`; `ω₁` never optimal; demand for good 2 unbounded at `p₂ = 0`; consumer 2 not strongly monotone; no equilibrium | `fig10aEconomy`, `fig_15_B_10a_demand1`, `fig_15_B_10a_endowment_not_optimal`, `fig_15_B_10a_no_demand0`, `fig_15_B_10a_not_stronglyMonotone`, `fig_15_B_10a_no_eqm` |
| Figure 15.B.10(b), p. 522 | Nonconvex preferences: no equilibrium; consumer 1's offer curve is disconnected | `fig10bEconomy`, `sqUtility_props`, `sqUtility_demand_corner`, `fig_15_B_10b_no_eqm`; offer curve = the two axis half-lines from 2 on: `fig_15_B_10b_offerCurve`, `fig10b_demand0`, `fig10b_corner_mem`; not preconnected: `fig_15_B_10b_offerCurve_not_preconnected` |
| Definition 15.B.2, p. 523 | Pareto optimality; bridge to Definition 10.B.2 | `ExchangeEconomy.IsParetoOptimal`, `isParetoOptimal_iff_economy` |
| p. 523, Figure 15.B.11 | Interior Pareto optimum: indifference curves tangent | `paretoOptimal_interior_tangency`; boundary case graphical |
| p. 523, Figure 15.B.12 | Pareto set, contract curve | `ExchangeEconomy.paretoSet`, `ExchangeEconomy.contractCurve` |
| p. 524 | First welfare theorem; equilibria lie on the contract curve | `first_welfare_theorem`, `walrasEqm_mem_contractCurve` |
| Definition 15.B.3, p. 524 | Equilibrium with transfers; budgets bind under local nonsatiation | `ExchangeEconomy.IsEqmWithTransfers`, `ExchangeEconomy.IsSupportable`, `ExchangeEconomy.IsEqmWithTransfers.wealth_eq` |
| p. 524 | Second welfare theorem (continuous, convex, strongly monotone) | `second_welfare_theorem` (any `I`, `L`), `second_welfare_theorem_edgeworth` |
| Figure 15.B.13(b), p. 525 | Transfers of endowments; moving endowments to `x*` gives a no-trade equilibrium | `walrasEqm_of_endowment_transfer`, `walrasEqm_at_allocation` |
| Footnote 4, p. 525 | After moving endowments to `x*`, `x*` is the unique equilibrium allocation (strict convexity needed) | `footnote_4_unique`, `footnote_4_needs_strict_convexity` |
| Figure 15.B.14, p. 525 | Nonconvex preferences: a Pareto optimum not supportable | `fig14Economy`, `fig14_u2_props`, `sqUtility_props`, `fig_15_B_14` |
| p. 525 | In Figure 15.B.10(a) `ω` is Pareto optimal but not supportable | `fig_15_B_10a_po_not_supportable` |
| Footnote 1, p. 516 | Consumer types | Verbal |

## Section 15.C: the one-consumer, one-producer economy (pp. 525-529)

| Source | Claim | Lean |
| --- | --- | --- |
| (15.C.1)-(15.C.4), pp. 526-527 | The economy, profit and utility maximization, equilibrium | `RCEconomy`, `RCEconomy.IsProfitMax`, `RCEconomy.budget`, `RCEconomy.IsConsumerOpt`, `RCEconomy.IsWalrasEqm`, `rc_budget_eq`, `rc_consumerOpt_iff` |
| p. 527, Figure 15.C.1 | Budget line = isoprofit line; intercept `π/p`, slope `-w/p` | `budgetLine_eq_isoprofit`, `budgetLine_intercept_slope` |
| p. 528, Figure 15.C.2 | Equilibrium allocations maximize utility over the feasible set (first welfare theorem) | `RCEconomy.feasible`, `RCEconomy.IsOptimal`, `rc_first_welfare`, `rc_eqm_price_pos` |
| p. 528 | The welfare optimum is an equilibrium allocation (second welfare theorem) | `rc_second_welfare` (correction 4), `rc_optimal_frontier` |
| Footnote 7, p. 528 | One consumer: Pareto optimality = utility maximization; unique optimum and equilibrium | `pareto_one_consumer_iff`, `footnote_7_unique` |
| Figure 15.C.3(a), p. 529 | Nonconvex technology: optimum not supportable; the firm does not maximize profit even locally | `fig15C3aEconomy`, `fig_15_C_3a_optimal`, `fig_15_C_3a_no_eqm`, `fig_15_C_3a_prices` |
| Figure 15.C.3(b), p. 529 | First welfare theorem with nonconvex technology | `rc_first_welfare` (no convexity assumed) |
| Footnote 8, p. 529 | Equal distribution maximizes symmetric concave social welfare | `footnote_8` |
| pp. 528-529 | Representative producer and consumer | Verbal (Sections 4.D, 5.E) |

## Section 15.D: the 2 × 2 production model (pp. 529-538)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 530 | Factor market equilibrium with fixed output prices | `IsOptimalInput`, `IsFactorEqm` |
| (15.D.1)-(15.D.2), p. 530 | First-order conditions necessary and sufficient | `factorEqm_iff_foc`, `concave_le_fderiv`; instance `exercise_15_D_7_foc` |
| (15.D.3)-(15.D.4), pp. 530-531 | Equilibrium in terms of cost functions | Constant-returns form: `interior_eqm_iff` (correction 6) |
| (15.D.5)-(15.D.6), p. 531, footnote 12 | Equilibrium allocation maximizes revenue | `factorEqm_revenue_max` |
| p. 532 | Factor prices = aggregate marginal revenue products; an endowment increase lowers the factor's price | `factorEqm_supergradient`, `factorEqm_monotone`, `factor_price_endowment_opposite` (supergradient form; correction 6) |
| p. 532, Figure 15.D.1 | Unit cost, `∇cⱼ = aⱼ`, concavity, intensity falls as `w₁` rises | `TwoByTwo`, `TwoByTwo.IsModel`, `TwoByTwo.c`, `TwoByTwo.c_le`, `TwoByTwo.c_smul`, `TwoByTwo.a_smul`, `TwoByTwo.unitCost_hasDerivAt`, `TwoByTwo.intensity_antitone` (correction 5) |
| p. 533, Figure 15.D.2 | Pareto set of factor allocations; tangency = common factor prices; Pareto set above, below or equal to the diagonal; if it cuts the diagonal it is the diagonal | `IsFactorAllocation`, `TwoByTwo.IsEfficientAllocation`, `TwoByTwo.IsSupportedBy`, `TwoByTwo.IsSupportedAllocation`, `TwoByTwo.IsInteriorSupport`, `TwoByTwo.supported_isEfficient`, `TwoByTwo.efficient_isSupported` (interior, smooth technologies; instance `efficient_isSupported_cdModel`), `TwoByTwo.diagonal_pareto_set`, `TwoByTwo.diagonal_pareto_set_efficient` (correction 16) |
| Definition 15.D.1, p. 534 | Factor intensity | `TwoByTwo.FactorIntensity`, `TwoByTwo.FactorIntensity.det_pos` |
| (15.D.7), footnotes 13-14, p. 534 | Price = unit cost at interior equilibria; curves cross at most once | `TwoByTwo.crs_profitMax_iff`, `TwoByTwo.interior_eqm_iff`, `TwoByTwo.unitCost_ratio_strictMono` |
| p. 535, Figure 15.D.5 | Equilibrium factor allocation | `TwoByTwo.interior_eqm_allocation` |
| p. 535 | Factor price equalization theorem | `TwoByTwo.factor_price_equalization` |
| Footnote 15, p. 535 | Diversification iff endowment in the cone | `TwoByTwo.exercise_15_D_6b` |
| Proposition 15.D.1, pp. 536-537 | Stolper-Samuelson (global form and the book's differential proof) | `TwoByTwo.proposition_15_D_1`, `TwoByTwo.proposition_15_D_1_differential` |
| Footnote 16, p. 536 | Stolper-Samuelson without the global factor intensity condition | `TwoByTwo.footnote_16` (intensity ranking only at the initial equilibrium), instance `footnote_16_leontief` |
| p. 537 | After `p₁` rises both firms use factor 1 less intensively | `TwoByTwo.intensity_antitone` with `TwoByTwo.proposition_15_D_1` |
| Proposition 15.D.2, p. 537 | Rybczynski | `TwoByTwo.proposition_15_D_2`, `TwoByTwo.outputs_cramer` |
| pp. 537-538 | `L × J` case | Verbal |
| Instances | Leontief model satisfies all assumptions; non-vacuity of 15.D.1-15.D.2 | `leontiefModel`, `leontiefModel_isModel`, `leontiefModel_factorIntensity`, `leontief_instances` |

## Section 15.E: general versus partial equilibrium (pp. 538-540)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 539 | Equilibrium without tax: `z = M/N`, `w̄ = f'(M/N)` | `IsTaxEqm`, `no_tax_eqm` |
| p. 539 | Partial equilibrium view: town 1's employment falls | `partial_eqm_employment_falls` |
| (15.E.1)-(15.E.5), p. 539 | `w'(0) = -1/N` (and `z'(0)`) | `general_eqm_wage_derivative`; instance `quadratic_eqm_path` (correction 7) |
| p. 540 | The wage effect vanishes as `N → ∞` | `wage_effect_vanishes` |
| p. 540, footnote 17 | Aggregate profits unchanged to first order; labor bears the burden | `aggregate_profit_derivative`, `labor_bears_burden` |
| Footnote 18, p. 540 | Budget-share justifications do not apply | Verbal |

## Exercises

| Source | Claim | Lean |
| --- | --- | --- |
| Exercise 15.B.1(a), p. 540 | Walras' law for the box | `exercise_15_B_1a` |
| Exercise 15.B.1(b), p. 540 | One market clears ⇒ both clear | `exercise_15_B_1b` |
| Exercise 15.B.2, p. 540 | Cobb-Douglas equilibrium and comparative statics in `ω₁₁` | `exercise_15_B_2`, `exercise_15_B_2_statics`, `cdEconomy` |
| Exercise 15.B.3, p. 540 | Walrasian equilibria are Pareto optimal | `exercise_15_B_3`, `first_welfare_theorem` |
| Exercise 15.B.4(a), (c), p. 541 | Shapes of offer curves | Graphical |
| Exercise 15.B.4(b), p. 541 | Gross substitute offer curves intersect once | `GrossSubstitute`, `exercise_15_B_4b`, `exercise_15_B_4b_offerCurves`; instance `cdOffer_grossSubstitute` |
| Exercise 15.B.4(d), p. 541 | Non-normal offer curves exist; they require an inferior good | `exercise_15_B_4d` (strict form, correction 8); existence: `ex15B4dUtility`, `ex15B4dDemand`, `ex15B4d_props`, `ex15B4d_opt`, `ex15B4d_demand_five`, `ex15B4d_demand_high`, `exercise_15_B_4d_exists`; good 2 inferior in the example: `ex15B4d_inferior` |
| Exercise 15.B.4(e), p. 541 | Normal + gross substitute: one intersection | `NormalOfferCurve`, `exercise_15_B_4e` |
| Exercise 15.B.4(f), p. 541 | Two normal offer curves intersecting three times | `ex15B2d`, `exercise_15_B_4f`, `example_15_B_2` |
| Exercise 15.B.5, p. 541 | Offer curves and equilibrium prices of Example 15.B.2 | `exercise_15_B_5_offerCurves`, `exercise_15_B_5_printed`, `ql8_optimal`, `example_15_B_2` |
| Exercise 15.B.6, p. 541 | Blair's economy: `p₁/p₂ ∈ {27/64, 1, 64/27}` | `blairEconomy`, `cesNeg2_optimal`, `cesNeg2_demand`, `blair_demand`, `exercise_15_B_6` (correction 1) |
| Exercise 15.B.7, p. 541 | Pareto set connected; with homothetic preferences on one side of the diagonal | `ExchangeEconomy.ParetoCurveHyp`, `exercise_15_B_7_homeomorph`, `exercise_15_B_7_connected`, `ExchangeEconomy.paretoCurve`, `pc_continuous_paretoCurve`, `pc_eq_paretoCurve`, `pc_isCompact_paretoSet`; `exercise_15_B_7_homothetic` (weak sides, correction 12), `exercise_15_B_7_diagonal`; instance `sqrtEconomy_hyp`, `sqrtEconomy_homothetic`, `sqrtEconomy_paretoSet` |
| Exercise 15.B.8, p. 541 | Interior Pareto optima share the good-2 allocation | `exercise_15_B_8`, `quasilinear_strictConcave`, instance `sqrtQLEconomy_instance`; connection to Chapter 10 verbal |
| Exercise 15.B.9, pp. 541-542 | Alphanse and Betatrix: unique equilibrium; with 5 units, Brie is free | `exercise_15_B_9`, `exercise_15_B_9_second`, `alphanse_demand`, `betatrix_demand` |
| Exercise 15.B.10(a), p. 542 | More endowment can lower utility (quasilinear) | `exercise_15_B_10a`; interpretation verbal |
| Exercise 15.B.10(b), p. 542 | A transfer cannot lower the recipient's utility (quasilinear) | `exercise_15_B_10b` (corrected), `exercise_15_B_10b_counterexample` (correction 9) |
| Exercise 15.B.10(c), p. 542 | Transfer paradox possible | Graphical; the counterexample of correction 9 exhibits a transfer paradox (with a non-small price change) |
| Exercise 15.B.10(d), p. 542 | Paradox only with multiple equilibria; hint: a no-transfer equilibrium with lower utility | `exercise_15_B_10d_lower_eqm` ("no higher", correction 13), `exercise_15_B_10d`, `ExchangeEconomy.QuasiSupports`; instance `sqrtEconomy_transfer_eqm`, `sqrtEconomy_15_B_10d`; "not more generally" verbal |
| Exercise 15.C.1(a), p. 542 | Unique equilibrium production | `exercise_15_C_1a` |
| Exercise 15.C.1(b), p. 542 | Slope of labor excess demand | `exercise_15_C_1b`, `exercise_15_C_1b_sign`, `exercise_15_C_1b_instance`, `exercise_15_C_1b_not_monotone` (correction 10) |
| Exercise 15.C.1(c), p. 542 | Multiple equilibria with two consumers endowed with labor; not under constant returns | `TCEconomy`, `TCEconomy.IsWalrasEqm`, `ex15C1cEconomy`, `ex15C1c_strictlyConvex`, `exercise_15_C_1c` (two equilibria, `w/p = 1` and `262144/531441`); constant returns: `exercise_15_C_1c_crs`, `exercise_15_C_1c_crs_wage`, `exercise_15_C_1c_crs_no_low_wage` (correction 14) |
| Exercise 15.C.2, p. 542 | `w/p = √3/2`, `x = (2/3, √3/3)`, `π = p√3/6` | `exercise_15_C_2`, `sqrt_firm_profit` (correction 1) |
| Exercise 15.D.1(a), p. 533 | One firm is more factor-1 intensive all along the Pareto set (unless diagonal) | `TwoByTwo.exercise_15_D_1a`, `TwoByTwo.factorRatio_order_preserved`, `TwoByTwo.factorRatio_eq_preserved`, `TwoByTwo.exercise_15_D_1a_pareto` (correction 16) |
| Exercise 15.D.1(b), p. 533 | A ray from an origin meets the Pareto set at most once; intensities and factor prices monotone | False as printed: `exercise_15_D_1b_counterexample` (Leontief); corrected for technologies differentiable along rays: `TwoByTwo.relRatio_strictAnti`, `TwoByTwo.exercise_15_D_1b_ratios_fall`, `TwoByTwo.exercise_15_D_1b_monotone`, `TwoByTwo.exercise_15_D_1b`, instance `exercise_15_D_1b_cdModel` (correction 17) |
| Exercise 15.D.2, p. 542 | Production possibility set convex | `productionPossibilitySet`, `exercise_15_D_2` (any `J`, `L`) |
| Exercise 15.D.3, p. 543 | Magnification; owner of the intensive factor better off | `TwoByTwo.exercise_15_D_3`, `TwoByTwo.exercise_15_D_3_welfare` |
| Exercise 15.D.4(a), p. 543 | Closed-economy equilibrium | `IsClosedEqm` |
| Exercise 15.D.4(b), p. 543 | At most one equilibrium | `exercise_15_D_4b` (Leontief, all equilibria); general model, equilibria with `w ≫ 0`: `TwoByTwo.exercise_15_D_4b_general`, instance `exercise_15_D_4b_cdModel` (correction 18) |
| Exercise 15.D.4(c), p. 543 | Multiplicity possible | `exercise_15_D_4c` |
| Exercise 15.D.5, p. 543 | Rybczynski magnification | `TwoByTwo.exercise_15_D_5` |
| Exercise 15.D.6(a), p. 543 | Equilibrium conditions with specialization | `TwoByTwo.exercise_15_D_6a` |
| Exercise 15.D.6(b), p. 543 | Diversification cone | `TwoByTwo.exercise_15_D_6b` |
| Exercise 15.D.6(c), p. 543 | Unit-dollar isoquants intersect at most once | False as printed: `exercise_15_D_6c_counterexample` (Leontief); corrected: `TwoByTwo.unitDollarIsoquant`, `TwoByTwo.RaySurjective`, `TwoByTwo.RayDifferentiable`, `TwoByTwo.exercise_15_D_6c`, `TwoByTwo.rayF_ratio_strictMono`, instance `exercise_15_D_6c_cdModel` (correction 15); graphical construction of the cone graphical |
| Exercise 15.D.6(d), p. 543 | Which good the economy specializes in, and the factor prices | Necessary direction in `TwoByTwo.exercise_15_D_6b`; sufficiency `TwoByTwo.exercise_15_D_6d_spec0`, `TwoByTwo.exercise_15_D_6d_spec1`, `TwoByTwo.exercise_15_D_6d_spec0_of_ray`, `TwoByTwo.exercise_15_D_6d_spec1_of_ray`, existence `TwoByTwo.exercise_15_D_6d_spec0_exists`, `TwoByTwo.exercise_15_D_6d_spec1_exists`, uniqueness `TwoByTwo.exercise_15_D_6d_spec0_unique`, `TwoByTwo.exercise_15_D_6d_spec1_unique`; instance via `exercise_15_D_8_spec0`, `exercise_15_D_8_spec1` (correction 15) |
| Exercise 15.D.7, p. 544 | Equilibrium via (15.D.1)-(15.D.2) and via (15.D.5) | `exercise_15_D_7`, `exercise_15_D_7_revenue`, `exercise_15_D_7_foc`, `ex15D7_optimal_iff` |
| Exercise 15.D.8, p. 544 | Cobb-Douglas equilibria for all endowments | Model: `cdtF`, `cdtA`, `cdtCost`, `cdtModel`, `cdtModel_isModel`, `cdtModel_factorIntensity`, `cdModel`, `cdModel_isModel`, `cdModel_factorIntensity`; equilibria: `exercise_15_D_8_diversified`, `exercise_15_D_8_spec0`, `exercise_15_D_8_spec1`, `exercise_15_D_8_outputs`, `exercise_15_D_8` (unique for every `z̄ ≫ 0`) |
| Exercise 15.D.9, p. 544 | Heckscher-Ohlin | `exercise_15_D_9`, `exercise_15_D_9_unique_demand`, `homogeneous_demand_scale`, `exercise_15_D_9_counterexample` (correction 11) |
