# Source map

Mas-Colell, Whinston and Green, *Microeconomic Theory*, Chapter 19, "General Equilibrium Under
Uncertainty", pp. 687-731. Printed pages; Lean names relative to `MWG.EquilibriumUncertainty`.
All numbered definitions, propositions, examples and the lemma are formalized, with the
mathematical footnotes and small-type claims, and every exercise subpart, including the
constructions of Exercise 19.F.3 (more assets, everybody worse off), Hart's nonexistence example of
Exercise 19.F.4 and the closed-form equilibria of Exercise 19.H.6(b)-(e). Nothing is OPEN.
Departures and corrections are in [corrections](corrections.md).

## Section 19.B: contingent commodities

| Source | Claim | Lean |
| --- | --- | --- |
| Section 19.A, pp. 687-688 | Introduction | verbal |
| Definition 19.B.1, p. 688 | Contingent commodities and vectors; random-variable view | `CVec`, `contingentUnit`, `definition_19_B_1`, `randomVar`, `randomVar_ext`, `cval` |
| Footnote 1, p. 688 | Negative entries are obligations | verbal (vectors in `ℝ^{LS}`) |
| p. 689 | Consumption sets and preferences on `ℝ^{LS}` | `CEconomy` |
| Example 19.B.1, p. 689 | Expected-utility preferences over contingent vectors are rational | `expUtil`, `euPref`, `example_19_B_1` |
| Footnote 2, p. 689 | Section 6.E for `L = 1` extends (Definition 6.E.2) | `footnote_19_2` |
| Example 19.B.2, p. 689 | Seeds and crops: `(-1,1,-1,0)` feasible, `(-1,1,0,0)` not | `seedsTech`, `plan2`, `example_19_B_2` |
| Footnote 3, p. 689 | Goods consumed before resolution | `ConsumedExAnte` |
| p. 689 | Shares (printed normalization corrected) | `SharesValid`, `shares_printed_normalization_fails` (correction 1) |
| p. 690, Figures 19.B.1-19.B.2 | Two-period and tree structures | verbal (graphical) |
| p. 690 (small type) | Information structures (partitions), increasingly fine families | `IsInfoStructure`, `Refines`, `IsInfoFamily` |
| Example 19.B.3, p. 691 | The three partitions of Figure 19.B.2 | `example19B3`, `example_19_B_3` |
| p. 691 (small type) | Date-events have a unique predecessor | `unique_predecessor` |
| p. 691 (small type) | Measurability and reduction to the timeless structure | `IsMeasurable`, `example_19_B_3_measurable` |

## Section 19.C: Arrow-Debreu equilibrium

| Source | Claim | Lean |
| --- | --- | --- |
| Definition 19.C.1, p. 692 | Arrow-Debreu equilibrium | `CEconomy.IsADEqm`, `CEconomy.wealth` |
| p. 691-692 | It is a Walrasian equilibrium with `LS` commodities | `flat`, `unflat`, `flat_dotProduct`, `CEconomy.toPriv`, `isADEqm_iff_isWalrasEqm` |
| p. 692 | First welfare theorem applies (Prop. 16.C.1, from `MWGWelfareTheorems`) | `CEconomy.IsParetoOptimal`, `adEqm_paretoOptimal`, `adEqm_paretoOptimal_eu`, `euPref_rational_lns` |
| p. 692 | Second welfare theorem applies (Prop. 16.D.1, from `MWGWelfareTheorems`) | `paretoOptimal_supported` |
| p. 692 | Concave Bernoulli utilities give convex preferences | `euPref_convex`, `euPref_prefConvex` |
| Footnote 4, p. 692; p. 692 | Debreu reference; profits are nonrandom | verbal |
| Exchange economies | Definition 19.C.1 with no firms and utilities | `IsADEqmU`, `exchangeCE`, `isADEqmU_iff` |
| p. 703 (also used throughout) | Strongly monotone expected utility | `StronglyMonotoneC`, `StronglyMonotoneL`, `expUtil_stronglyMonotone` |
| p. 694, p. 710 | Pareto optimality with `∑ x ≤ ∑ ω`; first welfare theorem for exchange | `IsParetoOptimalU`, `adEqmU_price_nonneg`, `adEqmU_budget_binds`, `adEqmU_paretoOptimal` |
| Example 19.C.1(a), pp. 692-693 | No aggregate risk, common probabilities: full insurance; Pareto set is the diagonal | `example_19_C_1a`, `example_19_C_1a_diagonal`, `po_stateIndependent` |
| Example 19.C.1(b), p. 693 | Different probabilities: more consumption in the state thought more likely | `example_19_C_1b` |
| Example 19.C.2, p. 693 | Aggregate risk: `p₁/p₂ < π₁/π₂`; `p₁ < p₂` with equal probabilities | `example_19_C_2`, `example_19_C_2_equal` |
| Figures 19.C.1-19.C.2 | Edgeworth boxes | graphical; content in the rows above |

## Section 19.D: sequential trade

| Source | Claim | Lean |
| --- | --- | --- |
| p. 694 | Ex ante Pareto optimality implies no ex post trade | `no_expost_trade` |
| Footnote 5, p. 694 | AD prices of state `s` are spot equilibrium prices | `footnote_19_5`, `adBudget` |
| (19.D.1), p. 695 | The Radner problem | `radnerFeasible` (with `R = I`) |
| Footnote 6, p. 695 | Expectations could differ | verbal |
| Definition 19.D.1, p. 696 | Radner equilibrium (contingent trade in one good) | `IsRadnerEqmD`, `definition_19_D_1` |
| Footnote 7, p. 696 | Initial endowments of contingent commodities | `footnote_19_7` |
| p. 696 | Budget constraints homogeneous of degree zero; normalizations | `radnerFeasible_rescale` |
| Footnote 8, p. 696 | Contingent commodities paying dollars | `dollarFeasible`, `exercise_19_D_1_dollars_goods` |
| Proposition 19.D.1(i), p. 697 | AD equilibrium gives Radner equilibrium (`q_s = p_{1s}`) | `adBudget_eq_radner`, `proposition_19_D_1_i` |
| Proposition 19.D.1(ii), p. 697 | Radner equilibrium gives AD equilibrium (multipliers `μ_s`) | `radner_eq_adBudget`, `proposition_19_D_1_ii_le`, `proposition_19_D_1_ii`, `clear_eq_of_binding`, `proposition_19_D_1_ii_counterexample` (correction 2) |
| Example 19.D.1, pp. 697-698 | Symmetric two-state economy; equal spot prices | `omega19D1`, `example_19_D_1`, `example_19_D_1_instance`, `example_19_D_1_stateIndependent` |
| pp. 698-699 (small type); footnotes 9-10 | Multi-period Radner equilibrium | `adBudgetTree`, `radnerBudgetTree`, Exercise 19.D.4 rows |

## Section 19.E: asset markets

| Source | Claim | Lean |
| --- | --- | --- |
| Definition 19.E.1, p. 699 | Assets as return vectors | `ReturnVector`, `returnMatrix` |
| Footnotes 10-14, pp. 699-700 | Real/financial assets; riskless asset | verbal |
| Example 19.E.1, p. 700 | Riskless asset, Arrow securities, `(1,2,1,2,…)` | `arrowSecurity`, `example_19_E_1_arrow`, `example19E1iii`, `example_19_E_1_iii` |
| Example 19.E.2, p. 700 | Options; `r(3.5)`, `r(2.5)`, `r(1.5)` for `r = (4,3,2,1)` | `callOption`, `primary4321`, `example_19_E_2` |
| Definition 19.E.2, p. 701 | Radner equilibrium with assets | `radnerFeasible`, `IsRadnerEqm` |
| p. 701 | Budget set `B_i(p, q, R)` with `p_{1s} = 1` | `budgetSet_normalized` |
| Proposition 19.E.1, p. 701 | Asset prices `q = μ·R`, `μ ≥ 0` | `proposition_19_E_1` |
| Footnotes 15-16, p. 701 | Assumption can be weakened; `μ_s` as implicit prices | verbal; `arrow_price` |
| Proof 1, p. 702 | Arbitrage-free prices; equilibrium prices are arbitrage free | `ArbitrageFree`, `NonnegNonzeroReturns`, `radner_arbitrageFree` |
| Lemma 19.E.1, pp. 702-703 | Arbitrage free implies `q = μ·R`, `μ ≥ 0`; positivity of `q` | `lemma_19_E_1`, `ArbitrageFree.pos`, `separation_fintype`, `eq_smul_of_ker_le` |
| Footnote 17, p. 702 | Dropping zero rows | built into `lemma_19_E_1` (correction 14) |
| Figure 19.E.1 | Construction of the weights | graphical; content in `lemma_19_E_1` |
| Proof 2, p. 703; footnote 18 | First-order conditions, `μ_s = π_s v_s'/α` | `foc_halfspace`, `portfolioObjective`, `hasDerivAt_portfolioObjective`, `proposition_19_E_1_proof2`, `proposition_19_E_1_proof2_radner` (correction 13) |
| p. 703 | Uniqueness of `μ` when `rank R = S` | `multipliers_unique` (the sufficiency direction) |
| Example 19.E.3, p. 704 | Riskless asset: `min_s r_{sk} ≤ q_k ≤ max_s r_{sk}` | `example_19_E_3` |
| Definition 19.E.3, p. 704 | Complete asset structure | `IsComplete`, `isComplete_iff_surjective` |
| Example 19.E.4, p. 704 | Identity and a triangular `3 × 3` structure are complete | `example_19_E_4_identity`, `example_19_E_4` |
| Example 19.E.5, p. 704 | Spanning through options; impossible if `r_s = r_{s'}` | `optionStructure19E5`, `example_19_E_5`, `not_complete_of_eq_rows`, `example_19_E_5_not_separating` |
| Proposition 19.E.2(i), p. 705 | Complete markets: AD equilibrium gives Radner equilibrium | `proposition_19_E_2_i`, `dot_eq_of_pricing` |
| Proposition 19.E.2(ii), p. 705 | Complete markets: Radner equilibrium gives AD equilibrium, `μ ≫ 0` | `proposition_19_E_2_ii`, `multipliers_pos_of_complete` (correction 2) |
| Proposition 19.E.3, p. 706; (19.E.1) | Same range gives same Radner allocations | `proposition_19_E_3`, `radner_date0_binds` |
| p. 706 | Redundant assets do not change the range | `appendAsset`, `redundant_range` |
| pp. 706-707 | Prices of `S` independent assets determine `μ`, Arrow prices | `multipliers_unique`, `arrow_price` |
| Example 19.E.6, p. 707; (19.E.2) | Option pricing; bounds and monotonicity | `r2_19E6`, `example_19_E_6_returns`, `example_19_E_6_price`, `example_19_E_6_bounds`, `optionPrice19E6`, `example_19_E_6_dispersion`, `example_19_E_6_identity_fails` (correction 3) |
| pp. 707-708 (small type) | Completeness node by node in a tree | `IsCompleteTree` |
| Example 19.E.7, p. 708; Figure 19.E.2 | Long-lived assets; AD prices from asset prices | `nodeMatrix19E7`, `rootMatrix19E7`, `example_19_E_7`, `adPrices19E7` |
| Footnotes 19-20, p. 708 | "Typically"; one normalization per budget | verbal |
| Footnote 21, p. 708 | Martingale property | `footnote_19_21` |

## Section 19.F: incomplete markets

| Source | Claim | Lean |
| --- | --- | --- |
| p. 709; footnotes 22-23 | Reasons for incompleteness | verbal |
| Example 19.F.1, pp. 709-710 | Pareto optima are state independent (needs `π ≫ 0`) | `example_19_F_1_po`, `example_19_F_1_needs_pos` (correction 5) |
| p. 710 | Complete markets give sunspot-free equilibria | `example_19_F_1_complete` |
| p. 710 | `K = 0`: Radner iff spot equilibria in each state | `IsSpotEqm`, `radner_noAssets_iff` |
| p. 710 | Sunspot equilibria exist from multiple spot equilibria and are inefficient | `sunspot_radnerEqm`, `sunspot_not_po`, `leontief_spot_eqm` |
| Footnote 24, p. 709 | History of "sunspots" | verbal |
| Footnote 25, p. 710 | Second-best | verbal |
| p. 711 | Induced utility `U*ᵢ` (`L = 1`) | `inducedConsumption` |
| Definition 19.F.1, p. 711 | Constrained Pareto optimality | `IsConstrainedPO` |
| Footnote 26, p. 711 | With one good, consumption is determined by the portfolio | `radner_consumption_induced` |
| Proposition 19.F.1, p. 711 | Radner equilibria are constrained Pareto optimal (`L = 1`) | `proposition_19_F_1` |
| Footnotes 27-28, p. 711 | No assets: no instruments; first-period redistribution | verbal |
| p. 712; footnotes 29-30 | No useful generalization for `L > 1` | verbal; Example 19.F.2 |
| Example 19.F.2, p. 712 | Pareto-ranked Radner equilibria (Hart) | `example_19_F_2`, `radner_noAssets_iff` |
| p. 713; footnote 31 | Existence and determinacy with incomplete markets | verbal |

## Section 19.G: firms

| Source | Claim | Lean |
| --- | --- | --- |
| p. 713; footnotes 32-33 | Firm as an asset; shares | verbal; `withFirm` |
| Figure 19.G.1 | Production choices | graphical |
| Definition 19.G.1, p. 714 | Spanned sets | `IsSpanned` |
| p. 714; footnote 34 | Market value `v(a, q)`, well defined; small redundant project | `marketValue_wellDefined`; `redundant_range`, `proposition_19_E_3` |
| (19.G.1), p. 715; footnote 35 | The budget set with shares | `firmBudget` |
| p. 715; footnote 36 | Unanimity for market value maximization | `unanimity`, `unanimity_utility` |
| p. 715; footnote 37 | Quoting and price-taking difficulties without spanning | verbal |
| pp. 715-716 (small type); footnote 38 | Shares not traded: endowments `θᵢ a` | `exercise_19_G_3`, `exercise_19_G_4` |

## Section 19.H: imperfect information

| Source | Claim | Lean |
| --- | --- | --- |
| p. 716; footnotes 39-40 | Signals; measurability of endowments | `SigmaMeas` |
| p. 717 | Symmetric information | `SymmetricInfo` |
| p. 717; footnotes 41-42 | Posterior probabilities; conditional utility; spot prices depend on the signal | `cellMass`, `posterior`, `posterior_sum`, `condEU`, `condEU_eq`, `cellMass_pos` |
| Definition 19.H.1, p. 717 | At least as / more informative | `AtLeastAsInformative`, `MoreInformative`, `SigmaMeas.mono` |
| Footnote 43, p. 717 | Refinement of partitions | `footnote_19_43` |
| p. 718 | The plan `x^σ` | `IsSignalPlan` |
| Proposition 19.H.1, p. 718 | More information helps a single consumer | `proposition_19_H_1`, `sum_eq_sum_cells`, `signalPlan_optimal_on` |
| Example 19.H.1, pp. 718-719 | Information destroys insurance (`1/2 < 1/√2`) | `example_19_H_1_noinfo`, `example_19_H_1_state1`, `example_19_H_1_state2`, `example_19_H_1` |
| Footnote 44, p. 719 | Complete markets relative to the signal | verbal (first welfare theorem, `adEqmU_paretoOptimal`) |
| p. 719 | Price aggregates information | Definition 19.H.2 rows |
| Example 19.H.2, p. 720; (19.H.1) | Naive price `(3 + 2β)/4` reveals `β`, not an REE | `QLOptimal`, `qlOptimal_iff`, `QLSpotEqm`, `qlSpotEqm_iff`, `qlSpotEqm_two`, `postCoef`, `updU`, `updU_eq`, `QLClears`, `qlClears_iff`, `qlClears_two`, `example_19_H_2` |
| Definition 19.H.2, p. 721; footnotes 45-46 | Rational expectations equilibrium price function | `reeEvent`, `IsREE` |
| p. 721 | Pooled price, fully revealing, implies REE | `pooledEvent`, `IsPooledPrice`, `FullyRevealing`, `DependsOnSignals`, `reeEvent_eq_pooled`, `pooled_fullyRevealing_isREE` |
| Example 19.H.2 continued, p. 721 | `p̂(β) = β` is an REE | `example_19_H_2_continued` |
| Example 19.H.3, p. 722 | No REE exists (Kreps) | `example_19_H_3` |
| p. 722 (small type) | Sufficient statistics | Example 19.H.4 rows |
| Example 19.H.4, pp. 722-723; footnotes 47-48 | 50 states; pooled prices by case; not revealing; REE | `bOf`, `kOf`, `sig19H4`, `case19H4`, `price19H4`, `postCoef_unif50`, `facts19H4`, `factsREE19H4`, `postCoef_pooled19H4`, `example_19_H_4`, `example_19_H_4_printed` (correction 6) |
| Example 19.H.5, p. 723 | Pooled price `β + (1/I)∑εᵢ`; separation; REE via private signals | `example_19_H_5_pooled`, `example_19_H_5_separates`, `example_19_H_5_identifies` |
| p. 723 | Grossman-Stiglitz paradox | verbal; Exercise 19.H.5 |
| Example 19.H.6, p. 724 | Lemons: admissible pairs, equivalent form, REE | `GoodSupply`, `LemonsAdmissible`, `lemons_admissible_iff`, `lemons_admissible_cases`, `example_19_H_6` |
| Footnote 49, p. 724 | `α = 1/2`, `p = 1.5`: supply 2, demand 1 | `footnote_19_49` |

## Exercises

| Source | Claim | Lean |
| --- | --- | --- |
| Exercise 19.C.1, p. 725 | Concave `u_s` give concave expected utility | `exercise_19_C_1` |
| Exercise 19.C.2, p. 725 | MRS on the Pareto set below the probability ratio | `exercise_19_C_2`, `po_tangency`, `po_no_improving_dir`, `po_exhausts` |
| Exercise 19.C.3, p. 726 | `∑_s (π_{si} p̄ - p_s) x_{si} ≥ 0`; interpretation | `exercise_19_C_3`; interpretation verbal |
| Exercise 19.C.4(a), p. 726 | Risk-averse consumer insures completely | `exercise_19_C_4a`, `halfEndow` |
| Exercise 19.C.4(b), p. 726 | Incomplete insurance, direction of bias, no gain for the risk-neutral agent | `exercise_19_C_4b` |
| Exercise 19.C.5, p. 726 | Consuming the expected endowment is an equilibrium | `exercise_19_C_5` |
| Exercise 19.D.1, p. 726 | Dollar-paying contingent commodities; normalizations | `dollarFeasible`, `exercise_19_D_1`, `exercise_19_D_1_dollars_goods` |
| Exercise 19.D.2, p. 726 | Contingent trades of Example 19.D.1 | `exercise_19_D_2` |
| Exercise 19.D.3, p. 727 | Consumption at `t = 0`: Proposition 19.D.1 remains valid | `adBudget0`, `radnerBudget0`, `exercise_19_D_3_i`, `exercise_19_D_3_ii` |
| Exercise 19.D.4(a), p. 727 | AD problem in the three-date tree | `adBudgetTree` |
| Exercise 19.D.4(b), p. 727 | Radner problem in the tree | `radnerBudgetTree` |
| Exercise 19.D.4(c), p. 727 | Proposition 19.D.1 remains valid | `exercise_19_D_4c_i`, `exercise_19_D_4c_ii` |
| Exercise 19.E.1(a), p. 727 | Consumption at `t = 0`: Proposition 19.E.1 by first-order conditions | `exercise_19_E_1a` |
| Exercise 19.E.1(b), p. 727 | `μ_s = π_s u₁'(x_{1s}) / u₀'(x₀)` | `exercise_19_E_1b` |
| Exercise 19.E.2, p. 727 | Options on a separating asset complete the market | `interpolate_by_options`, `exercise_19_E_2` |
| Exercise 19.E.3, p. 727 | Completing the proof of Proposition 19.E.2(i) | `proposition_19_E_2_i` (utility maximization step) |
| Exercise 19.E.4, p. 706 | Pricing a redundant asset by arbitrage | `exercise_19_E_4`, `exercise_19_E_4_eqm` |
| Exercise 19.E.5, p. 727 | Sequential trade equals AD trade when `q_b ≠ q_c` | `SeqReachable19E7`, `exercise_19_E_5` |
| Exercise 19.E.6(a)-(f), pp. 727-728 | Pricing derived assets | `r1_19E6x`, `r2_19E6x`, `ConsistentStatePrices`, `exercise_19_E_6a`, `exercise_19_E_6b`, `exercise_19_E_6c`, `exercise_19_E_6d` (correction 4), `exercise_19_E_6e`, `exercise_19_E_6f` |
| Exercise 19.F.1, p. 728 | Sunspot-free equilibria for any asset structure | `exercise_19_F_1`, `exercise_19_F_1_po` |
| Exercise 19.F.2, p. 728 | Continuity, concavity, monotonicity of `U*ᵢ` | `exercise_19_F_2_continuous`, `exercise_19_F_2_concave`, `exercise_19_F_2_increasing` |
| Exercise 19.F.3(a), p. 728 | Two states, two goods: sum of utilities lower with complete markets | `linU`, `coef19F3`, `U19F3`, `omega19F3`, `pSpot19F3`, `xSpot19F3`, `pAD19F3`, `xAD19F3`, `exercise_19_F_3a_spot` (no-asset Radner equilibrium), `exercise_19_F_3a_AD` (Arrow-Debreu equilibrium), `exercise_19_F_3a_complete_radner`, `exercise_19_F_3a` (sums `23/8 < 3`) (correction 21) |
| Exercise 19.F.3(b), p. 728 | Four states: (a) in states 1, 2, roles reversed in states 3, 4 | `firstHalf19F3`, `secondHalf19F3`, `double19F3`, `doubleU19F3`, `append4_zero`, `append4_one`, `append4_two`, `append4_three`, `exercise_19_F_3b`, `doubleU19F3_linU`, `doubleU19F3_double` |
| Exercise 19.F.3(c), p. 728 | One asset better for everybody than three | `R1_19F3`, `R3_19F3`, `pADspot19F3`, `z3_19F3`, `exercise_19_F_3c_one`, `exercise_19_F_3c_three`, `exercise_19_F_3c` (utilities `3/2 > 23/16` for both consumers) (correction 21) |
| Exercise 19.F.4, p. 728 | Nonexistence of Radner equilibrium (real assets, `L > 1`) | `radnerFeasibleReal`, `IsRadnerEqmReal`, `radnerFeasibleReal_single`, `isRadnerEqmReal_single`, `sqrtDemand`, `A19F4`, `c19F4`, `U19F4`, `omega19F4`, `c19F4_pos`, `ret19F4`, `exercise_19_F_4_AD` (Arrow-Debreu equilibrium; asset values collinear), `ad19F4_det`, `spot19F4_det`, `U19F4_lt_bump`, `dot_bump19F4`, `exercise_19_F_4` (no Radner equilibrium) |
| Exercise 19.F.5(a), p. 728 | Arrow-Debreu allocation with disability risk | `welfare19F5`, `strictConcave_tangent`, `exercise_19_F_5a`; infinitely many states verbal |
| Exercise 19.F.5(b), p. 728 | Unobservable disability, `c_a > c_d`: same allocation | `exercise_19_F_5b` |
| Exercise 19.F.5(c), pp. 728-729 | `c_a < c_d`: not reachable; equilibrium `c_a = c_d = k/2`, constrained optimal | `exercise_19_F_5c` |
| Exercise 19.G.1, p. 729 | Justifying (19.G.1): no need to buy shares | `exercise_19_G_1` |
| Exercise 19.G.2, p. 729 | Example of a significant loss | `exercise_19_G_2_no_one_worse_off`, `radnerFeasibleE` (correction 7) |
| Exercise 19.G.3, p. 729 | Traded or untraded shares: same budget sets | `exercise_19_G_3` |
| Exercise 19.G.4, p. 729 | Owners need not be unanimous | `exercise_19_G_4` |
| Exercise 19.H.1(a), p. 729 | Ex post optimality under full revelation; counterexample otherwise | `condEU_of_injective`, `exercise_19_H_1a`, `exercise_19_H_1a_counterexample` |
| Exercise 19.H.1(b)-(d), p. 729 | Interim optimality; conditional comparisons | `exercise_19_H_1b`, `exercise_19_H_1c`, `exercise_19_H_1d` |
| Exercise 19.H.2, p. 729 | State-dependent `p`, `w` that are `σ`-measurable | `exercise_19_H_2` |
| Exercise 19.H.3, p. 729 | The two steps of the proof of Proposition 19.H.1 | `exercise_19_H_3_max`, `exercise_19_H_3_subset` |
| Exercise 19.H.4, p. 730 | The missing step of Example 19.H.4 | `postCoef_pooled19H4`, `facts19H4` (correction 6) |
| Exercise 19.H.5, p. 730 | Verification in Example 19.H.5; `δ` independent of `I` and `p` | `example_19_H_5_identifies`, `infoGain`, `infoGain_eq`, `infoGain_nonneg`, `infoGain_pos`, `continuousOn_infoGain`, `integral_infoGain_pos`, `exercise_19_H_5` |
| Exercise 19.H.6(a), p. 730 | The Arrow-Debreu equilibrium | `U1_19H6`, `U2_19H6`, `omega19H6`, `x19H6`, `sqrt_le_add_quarter`, `exercise_19_H_6a` |
| Exercise 19.H.6(b), p. 730 | Non-contingent markets; Pareto optimality | `bern19H6`, `ncFeasible19H6`, `IsNCEqm19H6`, `ncTrade19H6`, `sqrt_le_tangent`, `ncEqm19H6` (equilibrium from consumer 2's first-order condition), `xB19H6`; not Pareto optimal when consumer 2's good-1 consumption varies: `exercise_19_H_6_not_po`, `exercise_19_H_6b_not_po`; closed form in `wInst19H6`, `wInst19H6_sqrt`, `exercise_19_H_6_instance` (correction 22) |
| Exercise 19.H.6(c), p. 730 | Information on state 1, non-contingent trade | `ncEqm19H6` with `E = {1}` (`t = 1/4 - w₁`) and `E = {2, 3}`, `xC19H6`, `exercise_19_H_6_instance` |
| Exercise 19.H.6(d), p. 730 | Contingent trade after the information | `IsCEqm19H6`, `cEqm19H6` (the allocation of (a) in each event), `exercise_19_H_6_instance`; it maximizes total surplus: `exercise_19_H_6_surplus` |
| Exercise 19.H.6(e), p. 730 | Comparing ex ante utilities; social value of information | `exAnte19H6`, `exercise_19_H_6e` (consumer 1: `ω₂₁` throughout; consumer 2: (b) ≤ (c) ≤ (a) = (d)), `exercise_19_H_6e_instance`, strict in `exercise_19_H_6_instance`; total surplus `exercise_19_H_6_surplus` |
| Exercise 19.H.7(a)-(d), pp. 730-731 | Full and asymmetric information prices; REE for `ε ≠ 0`; none for `ε = 0` | `coef19H7`, `endow19H7`, `sig19H7`, `exercise_19_H_7a`, `events19H7b`, `exercise_19_H_7b`, `exercise_19_H_7c`, `exercise_19_H_7d` |

## Supporting results

| Module | Content |
| --- | --- |
| `Calculus` | `eventually_lt_of_hasDerivAt_pos`, `hasDerivAt_nonpos_of_eventually_le`, `exists_nonneg_smul_of_dot_nonpos`, `cval_add_smul`, `foc_dir`, `hasDerivAt_lt_of_strictConcaveOn`, `eq_of_hasDerivAt_eq_of_strictConcaveOn`, `quasilinearLog_le`, `quasilinearLog_eq_iff`, `quasilinearLog_at` |
| `Exchange` | `cval_sum`, `cval_mono`, `cval_add`, `cval_sub`, `cval_smul`, `cval_unit`, `exists_larger_cheap`, `constC`, `eu1`, `eu1_eq_expUtil`, `eu1_stronglyMonotone`, `dirC`, `cval_dirC`, `hasDerivAt_eu1_dir`, `foc_eu1`, `GoodBernoulli`, `GoodBernoulli.deriv_pos`, `GoodBernoulli.deriv_lt`, `goodBernoulli_sqrt` |
| `ArrowDebreu` | `unflat_flat`, `flat_unflat`, `flat_injective`, `flat_add`, `flat_smul`, `flat_sum`, `unflat_add`, `unflat_smul`, `flatAlloc` |
| `RiskSharing` | `strictConcaveOn_fin1`, `omega19C1`, `AggregateTwoOne` |
| `Assets`, `Complete`, `Incomplete`, `RationalExpectations` | `mulVec_single`, `postCoef_singleton`, `postCoef_const`, `reeEvent_nonempty`, `pooledEvent_nonempty`, `qlOptimal_price_pos`, `beta19H`, `beta19H_pos`, `half2`, `half2_pos`, `postCoef_univ_beta`, `betaBoth`, `ones2`, `sig19H2`, `naiveEvents19H2`, `beta19H3`, `beta19H3_pos`, `coef19H7_pos`, `u0_19H7`, `u1_19H7`, `pos_19H7b`, `ne_19H7b`, `price19H4_eq_iff`, `unif50`, `betaBoth19H4`, `beta19H4` |

Dependencies used (Lake `path` requirements): `MWGWelfareTheorems` (Chapter 16: `PrivPrefEconomy`,
`IsWalrasEqm`, `IsParetoOptimal`, `IsPriceQuasiEqmWithTransfers`, Propositions 16.C.1 and 16.D.1),
through it `MWGClassicalDemand` (Chapter 3: `RationalOn`, `LocallyNonsatiated`, `PrefConvex`,
`euclidDist`, Theorem M.G.2(ii) `theorem_M_G_2_ii`) and `MWGCompetitiveMarkets` (`Allocation`);
`MWGChoiceUnderUncertainty` (Chapter 6: Definition 6.E.2 `HasExtendedEU`).
