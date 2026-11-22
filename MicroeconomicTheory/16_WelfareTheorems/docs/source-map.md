# Source map

Andreu Mas-Colell, Michael D. Whinston and Jerry R. Green, *Microeconomic Theory*, Chapter 16,
"Equilibrium and Its Basic Welfare Properties", pp. 545-577, with Appendix A (pp. 573-574) and the
exercises (pp. 575-577). Printed pages; Lean names relative to `MWG.WelfareTheorems`. All
definitions, numbered propositions, examples and figures with precise content, the small-type
claims and footnotes, and every exercise subpart are formalized, except the items marked
"listed" (verbal or forward references) and one OPEN item (footnote 13, Kannai's
concavifiability theorem). Departures and corrections are in [corrections](corrections.md).
Dependencies used: Chapter 15 (`MWGGeneralEquilibriumExamples`: `ExchangeEconomy`), Chapter 10
(`MWGCompetitiveMarkets`: `Allocation`, `PrivEconomy`), Chapter 5 (`supply`), Chapter 3
(`LocallyNonsatiated`, `PrefConvex`, `PrefContinuous`, `RationalOn`, `PrefStronglyMonotone`,
`utilityPref`, Proposition 3.C.1 `proposition_3_C_1_general`, Theorem M.G.2 `theorem_M_G_2_ii`,
Theorem M.C.3 `theorem_M_C_3_necessity`, `mc_line_hasDerivAt`, `mk_eventually_gt_of_deriv_pos`,
`duality_exists_dot_of_clm`, Exercise 3.B.1), Chapter 2 (`nonnegOrthant`, `budgetSetOn`), all at
the commits of this worktree.

## 16.A-16.B: the model and definitions

| Source | Claim | Lean |
| --- | --- | --- |
| 16.A, pp. 545-546 | Introduction | listed (verbal overview) |
| 16.B, p. 546 | Economy `({(Xᵢ, ≿ᵢ)}, {Yⱼ}, ω̄)` | `PrefEconomy`, `PrefEconomy.ofUtility` |
| 16.B, p. 546 | Edgeworth box as `L = I = 2`, `J = 1`, `Y₁ = -ℝ²₊`; pure exchange economies | `nonposOrthant`, `PrefEconomy.IsPureExchange`, `exchangeToPrefEconomy`, `exchangeToPrefEconomy_isPureExchange`, `exchange_isFeasible_iff`, `exchange_isDemandEqm_isPriceEqm` |
| Definition 16.B.1, (16.B.1), pp. 546-547 | Allocations, feasibility, the set `A` | `PrefEconomy.IsAllocation`, `PrefEconomy.IsFeasible`, `PrefEconomy.feasibleSet`, `definition_16_B_1` |
| Definition 16.B.2, p. 547 | Pareto domination and optimality | `PrefEconomy.ParetoDominates`, `PrefEconomy.IsParetoOptimal`, `definition_16_B_2` |
| 16.B, p. 547 | All endowments to one strongly monotone consumer is Pareto optimal | `paretoOptimal_all_to_one` |
| 16.B, p. 547; footnote 1 | Private ownership economy, shares; unanimity of owners (Section 5.G) | `PrivPrefEconomy`, `PrivPrefEconomy.toEconomy`, `PrivPrefEconomy.SharesValid`; footnote 1 listed (reference to Ch. 5) |
| Definition 16.B.3, pp. 547-548; footnote 2 | Walrasian equilibrium; "maximal for `≿` in `B`" | `PrivPrefEconomy.wealth`, `PrivPrefEconomy.IsWalrasEqm`, `IsMaximalFor`, `definition_16_B_3`, `isWalrasEqm_iff_competitiveEqm` |
| Definition 16.B.4, p. 548 | Price equilibrium with transfers | `PrefEconomy.IsPriceEqmWithTransfers`, `definition_16_B_4`, `PrefEconomy.IsPriceEqmWithTransfers.isFeasible` |
| 16.B, p. 548 | A Walrasian equilibrium is a price equilibrium with transfers | `PrivPrefEconomy.sum_wealth`, `PrivPrefEconomy.IsWalrasEqm.isPriceEqmWithTransfers` |

## 16.C: the first fundamental theorem

| Source | Claim | Lean |
| --- | --- | --- |
| Definition 16.C.1, p. 549 | Local nonsatiation (Definition 3.B.3) | `definition_16_C_1`, `lns_exists_better_cheaper` |
| 16.C, p. 549 | Desirable commodities give LNS | listed (Exercise 3.B.1, Chapter 3) |
| 16.C, p. 549 | Continuous LNS preferences have no closed bounded consumption set | `unbounded_of_lns` |
| Proposition 16.C.1, (16.C.1)-(16.C.3), pp. 549-550 | First welfare theorem | `equation_16_C_1`, `exercise_16_C_2`, `proposition_16_C_1`, `proposition_16_C_1_walras` |
| Figure 16.C.1, p. 550 | Thick indifference: price equilibrium with transfers not Pareto optimal | `fig16C1u1`, `fig16C1u2`, `fig16C1Economy`, `fig16C1Eqm`, `figure_16_C_1` |
| 16.C, p. 550 | Market completeness, price taking; distribution | listed (verbal) |

## 16.D: the second fundamental theorem

| Source | Claim | Lean |
| --- | --- | --- |
| 16.D, p. 551 | Failures of Figures 15.C.3(a), 15.B.14, 15.B.10(a) | listed (Chapter 15); Figure 15.B.10(a) made concrete in Figure 16.D.2 below |
| Definition 16.D.1, pp. 551-552 | Price quasiequilibrium with transfers | `PrefEconomy.IsPriceQuasiEqmWithTransfers`, `definition_16_D_1`, `PrefEconomy.IsPriceQuasiEqmWithTransfers.isFeasible` |
| 16.D, p. 552 | Every price equilibrium with transfers is a quasiequilibrium (correction 1) | `PrefEconomy.IsPriceEqmWithTransfers.isPriceQuasiEqm`, `PrefEconomy.IsPriceEqmWithTransfers.isPriceQuasiEqm_of_lns`, `priceEqmCounterEconomy`, `priceEqmCounterEconomy_counterexample` |
| Footnote 3, small type, p. 552 | Under LNS `wᵢ = p·x*ᵢ`; conditions (i), (ii'), (iii) | `PrefEconomy.IsPriceQuasiEqmWithTransfers.wealth_eq`, `footnote_3` |
| Footnote 4, p. 552 | Under LNS, (ii'') characterizes equilibrium with transfers | `footnote_4` |
| Small type, p. 552; Exercise 16.D.1 | (ii') is expenditure minimization | `exercise_16_D_1` |
| Proposition 16.D.1, pp. 552-554; Steps 1-9; footnote 5 | Second welfare theorem | `preferredSet`, `PrefEconomy.aggPreferredSet`, `PrefEconomy.availableSet`, `proposition_16_D_1_step1`, `proposition_16_D_1_step2_V`, `proposition_16_D_1_step2_Y`, `proposition_16_D_1_step3`, `proposition_16_D_1_step5`, `proposition_16_D_1` (Steps 4, 6-9 inside), `strict_of_strict_of_pref`, `strict_of_pref_of_strict` |
| Figure 16.D.1, p. 553 | The separation argument | listed (illustration of `proposition_16_D_1`) |
| Figure 16.D.2 (= 15.B.10(a)), p. 554 | Quasiequilibrium that is not an equilibrium; unique price `(1, 0)`; `w₁ = 0` | `fig16D2u1`, `fig16D2u2`, `fig16D2Economy`, `fig16D2Alloc`, `fig16D2_lns`, `figure_16_D_2_quasi`, `figure_16_D_2_unique_price`, `figure_16_D_2_not_eqm`, `lns_of_strictMono_coord`, `euclidDist_add_single` |
| Proposition 16.D.2, p. 555; Figure 16.D.3 | Cheaper consumption argument | `proposition_16_D_2`, `isMaximalFor_of_strict_gt` |
| Footnotes 6, 7, 8, p. 555 | Expenditure min. vs. preference max.; locally cheaper consumption; generalizes 3.E.1(ii) | `footnote_6`, `footnote_7`, `footnote_8` |
| Proposition 16.D.3, p. 555 | Quasiequilibrium with `w ≫ 0` is an equilibrium (correction 2) | `proposition_16_D_3`, `satiatedEconomy`, `proposition_16_D_3_needs_lns` |
| Small type, p. 556; footnote 9 | Free disposal forces `p ≥ 0`; `x* ≫ 0`; strongly monotone case gives `p ≫ 0` | `footnote_9`, `dotProduct_pos_of_nonneg_ne_zero`, `pureExchange_quasiEqm_isPriceEqm_of_interior`, `pureExchange_quasiEqm_isPriceEqm_of_strongMono` |
| 16.D, pp. 556-557; footnote 10 | Practical limitations of lump-sum transfers | listed (verbal) |
| Small type, pp. 557-558; Figures 16.D.4, 16.D.5 | Nonconvex one-consumer economy; Pareto improvement in the 2-replica | `replicaEconomy`, `symmetricAlloc`, `sqNormU`, `sqNormU_stronglyMonotone`, `figure_16_D_4`, `figure_16_D_5` |
| Figure 16.D.6, p. 558 | A Pareto optimum not supportable in the replica box | listed (drawn preferences; the phenomenon is Chapter 15's `fig_15_B_14`) |
| Small type, p. 558; footnote 11 | Large replicas: Exercise 16.D.4; Chapter 17 facts | see Exercise 16.D.4; footnote 11 listed (forward reference) |

## 16.E: Pareto optimality and social welfare optima

| Source | Claim | Lean |
| --- | --- | --- |
| 16.E, p. 558; Figure 16.E.1 | Utility possibility set `U` (closed under Appendix A) | `utilityPossibilitySet`, `utilityPossibilitySet_down`; closedness `proposition_16_AA_2` |
| 16.E, p. 559 | Pareto frontier `UP` | `paretoFrontier` |
| Footnote 12, p. 559 | A boundary point of `U` need not be Pareto optimal | `fig16C1Utilities`, `footnote_12` |
| Proposition 16.E.1, p. 559 | Pareto optimal iff utility vector in `UP` | `proposition_16_E_1` |
| 16.E, p. 559; Exercise 16.E.2 | `U` convex for convex `Xᵢ`, `Yⱼ`, concave `uᵢ` | `exercise_16_E_2` |
| Footnote 13, p. 559 | Concave representations under a strengthening of strict convexity | **OPEN**. The precise result behind the footnote is Kannai's concavifiability theorem (Kannai 1977): a twice continuously differentiable preference whose indifference surfaces have everywhere positive Gaussian curvature (equivalently, the nonsingular bordered Hessian of Appendix A of Chapter 3) admits a concave utility representation on every compact convex subset of the consumption set. Formalizing it needs the curvature-based construction of a concave transform of a utility (Kannai's or Fenchel's construction), which is not in Mathlib or the dependencies; no counterexample is claimed, since the footnote does not specify the domain (global concavifiability on unbounded sets is a different and delicate question) |
| 16.E, p. 560; footnote 14; (16.E.1) | Linear social welfare functions | weighted sums `∑ λᵢvᵢ` in the statements below; footnote 14 listed (Chapter 22) |
| Proposition 16.E.2, p. 560; Figure 16.E.3 | `λ ≫ 0` maximizers are in `UP`; supporting weights `λ ≥ 0` for convex `U` | `proposition_16_E_2_i`, `proposition_16_E_2_ii`, `strongDual_apply_eq_sum` |
| 16.E, p. 560; footnote 15 | Every Pareto optimum is a welfare optimum for some `λ ≥ 0`, and conversely for `λ ≫ 0` | `pareto_isWelfareOptimum`, `welfareOptimum_isPareto`; footnote 15 listed |
| 16.E, p. 561; Figure 16.E.1 point `ū` | Nonconvex `U`: a Pareto optimum maximizing no linear welfare function | `squareUtility`, `fig16E1Economy`, `figure_16_E_1` |
| (16.E.2), p. 561; Figure 16.E.4 | Normative representative consumer | `repUtility`, `representative_consumer` |

## 16.F: first-order conditions

| Source | Claim | Lean |
| --- | --- | --- |
| 16.F, p. 562; footnote 17 | `∇u ≫ 0` gives strong monotonicity; `∇F ≫ 0` gives free disposal | `strictMono_of_grad_pos`, `mono_of_grad_pos`, `clm_apply_eq_sum_partials`, `clm_pos_of_partials_pos` |
| (16.F.1), p. 562 | The Pareto problem | `Problem16F1`, `IsSolution16F1`, `economy16F` |
| Exercise 16.F.1, p. 562 | Solutions are Pareto optimal; Pareto optima solve (16.F.1) | `exercise_16_F_1_i`, `exercise_16_F_1_ii`, `solution16F1_resources_bind` |
| 16.F, p. 563; Figure 16.F.1 | Constraints bind; parametrizing the frontier | `section_16_F_constraints_bind`; Figure 16.F.1 listed |
| (16.F.2)-(16.F.3), p. 563; Exercise 16.F.2; footnote 18 | Kuhn-Tucker conditions; constraint qualification (correction 4) | `exercise_16_F_2`, `fritz_john`, `no_improving_direction`, `projX`, `projY`, `resLin`, `footnote_18_counterexample` |
| 16.F, p. 563-564 | Multipliers as shadow prices | listed (interpretation; Section M.K) |
| (16.F.4)-(16.F.6), p. 564; Exercise 16.F.3 | Ratio conditions at interior solutions | `exercise_16_F_3` |
| Small type (i)-(iii), pp. 564-565, (16.F.7)-(16.F.9); Exercise 16.F.4 | Three efficiencies | `Problem16F7`, `exercise_16_F_4_i`, `Problem16F8`, `exercise_16_F_4_ii`, `exercise_16_F_4_iii`, `exists_sep_direction`, `eventually_gt_along`, `eventually_pos_along`, `clm_two_dir`, `single_eq_smul_single` (route via (16.F.9) not formalized: departure 13) |
| 16.F, p. 565; (16.F.10)-(16.F.11) | Correspondence with utility and profit maximization; Pareto optimal iff price equilibrium with transfers | `foc_16F2_iff_16F10`, `consumer_max_of_foc`, `firm_max_of_foc`, `convexOn_tangent_le`, `concaveOn_le_tangent`, `section_16_F_pareto_isPriceEqm`, `section_16_F_pareto_iff_priceEqm` |
| (16.F.12)-(16.F.14), p. 566; footnote 19 | Weighted welfare problem and its correspondence | `foc_16F13_iff_16F2`; sufficiency inside `proposition_16_F_1` |
| Proposition 16.F.1, p. 566 | Pareto optima maximize weighted utilities, `λᵢ = 1/αᵢ` | `proposition_16_F_1` |

## 16.G: applications

| Source | Claim | Lean |
| --- | --- | --- |
| 16.G, p. 567 | Contingent and dated commodities | listed (Chapters 19-20) |
| Example 16.G.1, p. 567; footnote 20 | `2^I` states; `2^{I-1}` contingent commodities | `footnote_20` |
| Example 16.G.2, p. 568 | Occupational choice: `Xᵢ` closed convex; LNS; convex technology; welfare theorems apply | `occupationalX`, `example_16_G_2_X`, `example_16_G_2_lns`, `example_16_G_2_Y` |
| Example 16.G.3, pp. 568-570; footnotes 21, 22 | Public goods, feasibility and Pareto optimality | `PublicFeasible`, `PublicParetoOptimal`; footnotes 21-22 listed |
| Definition 16.G.1, pp. 569-570 | Lindahl equilibrium (correction 6) | `IsLindahlEqm`, `IsLindahlEqmPrinted`, `definition_16_G_1_wealth_gap`, `definition_16_G_1_printed_forces`, `lindahlExampleU`, `definition_16_G_1_printed_counterexample` |
| Example 16.G.3, p. 570 | Every Lindahl equilibrium is Pareto optimal | `lindahl_isParetoOptimal` |
| Example 16.G.3, p. 570 | Every Pareto optimum is a Lindahl (quasi)equilibrium with transfers (reduction to the artificial economy and Proposition 16.D.1) | `lindahlEmb`, `lindahlProj`, `lindahlX`, `lindahlY`, `lindahlArtificialEconomy`, `IsLindahlQuasiEqm`, `lindahlEmb_zero`, `lindahlEmb_succ`, `lindahlProj_emb`, `dot_succ`, `dot_lindahlEmb`, `emb_proj`, `emb_mem`, `proj_mem`, `euclidDist_emb`, `lindahlAlloc`, `lindahl_pareto_artificial`, `lindahl_second_welfare`, `lindahl_second_welfare_instance` |
| Footnote 23, p. 570 | Samuelson condition `∑ MRSᵢ = MRT` | `footnote_23` |
| 16.G, pp. 570-571; Figure 16.G.1 | Loss at the only supporting prices; shutting down is better | `sqTechF`, `sqTechY`, `sqTechF_hasFDerivAt`, `fig16G1Economy`, `fig16G1Alloc`, `figure_16_G_1` |
| Proposition 16.G.1, p. 571; footnote 24; Exercise 16.G.1 | Pareto optima are marginal cost price equilibria | `PrefEconomy.IsMCPriceEqm`, `proposition_16_G_1`, `exercise_16_G_1` |
| Footnote 25, p. 571 | Terminology | listed (see Exercise 16.G.3) |
| Exercise 16.G.2, p. 572 | Input price = output price × marginal product | `exercise_16_G_2` |
| 16.G, p. 572; footnote 26 | (16.G.1) is not profit maximization; regulation | listed (verbal; Figure 16.G.1 above) |
| Small type, p. 572; Figure 16.G.2 | A marginal cost price equilibrium need not be Pareto optimal | `fig16G2Economy`, `fig16G2Alloc`, `figure_16_G_2` |

## Appendix A

| Source | Claim | Lean |
| --- | --- | --- |
| Appendix A, p. 573 | The set `A` of feasible allocations; aggregate production set | `PrefEconomy.feasiblePairs`, `aggregateProduction` |
| Proposition 16.AA.1, pp. 573-574; footnote 27 | Closed, bounded, nonempty (correction 3) | `exercise_16_AA_1`, `proposition_16_AA_1`, `proposition_16_AA_1_nonempty`, `mem_of_tendsto_inv_smul`, `isClosed_nonnegOrthant`, `isClosed_nonposOrthant`, `aaY1`, `aaCounterEconomy`, `aaCounter_agg`, `proposition_16_AA_1_counterexample`; footnote 27 listed (Section 5.B) |
| Appendix A, p. 574; Figure 16.AA.1 | The `J = 1` argument: `(Y + {ω̄}) ∩ ℝ^L₊` compact | `exercise_16_AA_2` |
| Proposition 16.AA.2, p. 574 | `U` closed and bounded above | `proposition_16_AA_2` |

## Exercises

| Source | Claim | Lean |
| --- | --- | --- |
| Exercise 16.C.1, p. 575 | Compact `X` and continuous `≿` contradict LNS | `exercise_16_C_1` |
| Exercise 16.C.2, p. 575 | (16.C.2) | `exercise_16_C_2` |
| Exercise 16.C.3(a), p. 575 | At most one satiation point; LNS elsewhere | `StrictlyConvexC3`, `strictlyConvexC3_of_prefStrictlyConvex`, `prefStrictlyConvex_of_strictlyConvexC3`, `euclidDist_segment`, `exercise_16_C_3a_unique`, `exercise_16_C_3a_lns` |
| Exercise 16.C.3(b), p. 575 | First welfare theorem with satiation | `exercise_16_C_3b` |
| Exercise 16.C.4, p. 575 | Altruism: `U`-optima are `u`-optima; converse fails; no concavity used | `PrefEconomy.IsParetoOptimalWrt`, `exercise_16_C_4`, `altruismPleasure`, `altruismW`, `exercise_16_C_4_converse_fails`; second question answered by `proposition_16_D_1` applied to the pleasure economy (verbal) |
| Exercise 16.D.1, p. 575 | Expenditure minimization | `exercise_16_D_1` |
| Exercise 16.D.2, p. 575 | LNS is needed in Proposition 16.D.1 | `ex16D2u`, `ex16D2Economy`, `exercise_16_D_2` |
| Exercise 16.D.3, p. 575 | Quasiequilibria are equilibria with `p ≫ 0` | `exercise_16_D_3` |
| Exercise 16.D.4, pp. 575-576 | Replicas and nonconvexity | `exists_strict_of_tendsto`, `exists_strict_sub_single`, `exists_nat_combination_neg`, `exercise_16_D_4` |
| Exercise 16.E.1(a), p. 576 | Boundary point of `U` in `U'` not Pareto optimal | `achievedUtilitySet`, `achievedUtilitySet_subset`, `footnote_12` |
| Exercise 16.E.1(b), p. 576 | Boundary points in `U'` are Pareto optimal; `U' = U ∩ ℝ^I₊` | `utility_mono_of_strongMono`, `exercise_16_E_1b_interior`, `exercise_16_E_1b`, `exercise_16_E_1b_hint` |
| Exercise 16.E.1(c), p. 576 | Quasiequilibrium utilities are not interior | `exercise_16_E_1c` |
| Exercise 16.E.2, p. 576 | `U` convex | `exercise_16_E_2` |
| Exercises 16.F.1-16.F.4, p. 576 | See Section 16.F | `exercise_16_F_1_i`, `exercise_16_F_1_ii`, `exercise_16_F_2`, `exercise_16_F_3`, `exercise_16_F_4_i`, `exercise_16_F_4_ii`, `exercise_16_F_4_iii` |
| Exercises 16.G.1-16.G.2, p. 576 | See Section 16.G | `exercise_16_G_1`, `exercise_16_G_2` |
| Exercise 16.G.3, p. 576 | Unique marginal cost equilibrium with cost not minimized | `ex16G3F`, `ex16G3Y`, `ex16G3Economy`, `ex16G3F_hasFDerivAt`, `exercise_16_G_3` |
| Exercise 16.G.4, p. 576 | One consumer: an optimal marginal cost equilibrium (correction 5) | `exercise_16_G_4`, `noOptimumF`, `exercise_16_G_4_needs_optimum` |
| Exercise 16.G.5(a), p. 577 | Optimal allocation of the endowments | `exercise_16_G_5a` |
| Exercise 16.G.5(b), p. 577 | Wages, cost, marginal cost `3/4`, consumer's choice | `exercise_16_G_5b_wages`, `exercise_16_G_5b_cost`, `exercise_16_G_5b_mc`, `exercise_16_G_5bc` |
| Exercise 16.G.5(c), p. 577 | Lump-sum tax `1/3` | `exercise_16_G_5bc` |
| Exercise 16.G.5(d), p. 577 | Landowner transfer `(w_L + w_T)√e/2` | `exercise_16_G_5d` |
| Exercise 16.G.5(e), p. 577 | Marginal cost equilibrium and its Pareto optimality | `exercise_16_G_5e_level`, `exercise_16_G_5e`, `sqrt_mul_add_le` |
| Exercise 16.AA.1, p. 577 | `A` closed | `exercise_16_AA_1` |
| Exercise 16.AA.2, p. 577 | Compactness; four assumptions indispensable | `exercise_16_AA_2`, `exercise_16_AA_2_needs_closed`, `exercise_16_AA_2_needs_convex`, `exercise_16_AA_2_needs_zero`, `exercise_16_AA_2_needs_no_free_lunch` |
| Exercise 16.AA.3, p. 577 | Bounded plans of firm 1 | `exercise_16_AA_3` |

## Supporting declarations

`dotProduct_finset_sum`, `abs_dotProduct_sub_le`, `dot_two`, `zero_mem_supply_nonpos`,
`rationalOn_utilityPref`, `prefContinuous_utilityPref`, `single_nonneg_add`.
