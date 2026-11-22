# Source map

Andreu Mas-Colell, Michael D. Whinston and Jerry R. Green, *Microeconomic Theory*, Chapter 17,
"The Positive Theory of Equilibrium", pp. 578-651, with Appendix A (characterizing equilibrium
through welfare equations), Appendix B (a general approach to the existence of Walrasian
equilibrium) and the exercises (pp. 642-651). Printed pages; Lean names relative to
`MWG.PositiveEquilibriumTheory`. Departures and corrections are in [corrections](corrections.md).

All definitions, numbered propositions, lemmas, examples, displayed equations, footnotes and
small-type claims with precise content, and every exercise subpart are formalized, except
rows marked "listed" (verbal or graphical content) and the OPEN rows. The OPEN items are:
Proposition 17.D.2 and footnote 16 for `L ≥ 3` and the homotopy argument of pp. 597-598
(Brouwer degree / Poincaré-Hopf, absent from Mathlib; `L = 2` is proved); Proposition 17.D.3
with fewer equations than unknowns (Sard's theorem between different dimensions; the
application only uses `M = N`); strict convexity of the preferences in Proposition 17.E.3
(convex preferences are proved); Proposition 17.E.4 (proof omitted in the book) and footnote
28; Exercise 17.F.16(g) for `N ≥ 2` (index theorem); the general linearization claims of p. 624
(Hartman-Grobman, and "negative real parts imply local stability" beyond negative definite
`Dẑ` and `L = 2`, which needs the Lyapunov matrix equation); the production sketch of p. 630; Exercises 17.C.3(b), 17.BB.3 and
17.BB.8(b) and the state-dependent generalization of p. 639 (existence arguments not built).
Dependencies used: Chapter 16 (`MWGWelfareTheorems`), Chapter 15
(`MWGGeneralEquilibriumExamples`), Chapters 10, 5, 3 (including `theorem_M_E_1`,
`theorem_M_E_2`) and 2, Kreps `ConsumerDemand`, and LeanEconomics (`brouwer`, `kakutani`,
pinned `04deccaf63`), all at the commits of this worktree.

## 17.A-17.B: shared definitions

| Source | Claim | Lean |
| --- | --- | --- |
| 17.A, pp. 578-579 | Introduction | listed (verbal overview) |
| 17.B, p. 581 | Standing assumptions: `Xᵢ = ℝ^L_+`, continuous, strictly convex, strongly monotone preferences | `StandardUtility` |
| Definition 17.B.2, p. 581 | Individual and aggregate excess demand functions | `demandFn`, `demandFn_mem`, `demandFn_eq`, `indivExcessDemand`, `excessDemand`, `excessDemand_apply`, `excessDemand_eq` |
| (17.B.2), p. 581 | Equilibrium price vector: `z(p) = 0` | `IsEqmPrice`, `IsEqmPrice.smul`, `posOrthant`, `mem_posOrthant`, `isOpen_posOrthant`, `smul_mem_posOrthant` |
| Proposition 17.B.2(i)-(v), p. 582 | Names of the five properties | `EDContinuous`, `EDHomogeneous`, `EDWalrasLaw`, `EDBoundedBelow`, `EDBoundary`, `IsStandardExcessDemand` |
| 17.B, p. 582 | `p ≫ 0` is an equilibrium iff `ẑ(p) = 0` | `truncExcessDemand`, `eqm_iff_trunc_eq_zero` |
| 17.C, p. 586 | The unit simplex `Δ` | `priceSimplex` |

## 17.B Equilibrium: definitions and basic equations

| Source | Claim | Lean |
| --- | --- | --- |
| Definition 17.B.1, p. 579 | Walrasian equilibrium of a private ownership economy | Chapter 16 `PrivPrefEconomy.IsWalrasEqm` (imported) |
| Footnote 1, p. 579 | "maximal for `≿ᵢ` in `B`" | Chapter 16 `IsMaximalFor` (imported) |
| 17.B, p. 580 | Pure exchange economy: `J = 1`, `Y₁ = -ℝ^L₊`, `Xᵢ = ℝ^L₊` | `pureExchangeEconomy` |
| (i')-(iii'), p. 580 | Restatement of Definition 17.B.1 for pure exchange | `conditions_i'_iii'` |
| Exercise 17.B.1, p. 641 | (i') iff profit maximization on `-ℝ^L₊` | `exercise_17_B_1` |
| Proposition 17.B.1, p. 580 | `p ≥ 0` is an equilibrium price vector iff `∑ᵢ (xᵢ(p, p·ωᵢ) - ωᵢ) ≤ 0` (17.B.1) | `proposition_17_B_1` (local nonsatiation suffices) |
| Proof of 17.B.1, p. 580 | `p·xᵢ(p, p·ωᵢ) = p·ωᵢ` under local nonsatiation | `ed_budget_eq` |
| Definition 17.B.2, pp. 580-581 | Individual and aggregate excess demand | `demandFn`, `indivExcessDemand`, `excessDemand` (Basic); `uDemand`, `uDemand_mem`, `uDemand_nonneg`, `walrasianDemand_eq_singleton`, `uDemand_smul`, `demand_subsingleton` |
| 17.B, p. 581 | The domain of `z` contains all `p ≫ 0` | `demand_nonempty`, `uDemand_zero_wealth`, `eq_zero_of_dotProduct_nonpos` |
| (17.B.1'), p. 581 | `p ∈ ℝ^L₊` is an equilibrium price vector iff `z(p) ≤ 0` | `proposition_17_B_1'` |
| 17.B, p. 581 | At an equilibrium `z(p) ≤ 0`, `p·z(p) = 0`, so `z_ℓ(p) = 0` if `p_ℓ > 0` | `eqm_excess_eq_zero_of_price_pos` |
| Footnote 2, p. 581 | A "bad" has zero price and is disposed of | listed (verbal) |
| 17.B, p. 581 | With strongly monotone preferences every equilibrium has `p ≫ 0` | `walrasianDemand_eq_empty`, `eqm_price_pos` |
| (17.B.2), p. 581 | `p` is an equilibrium price vector iff `z(p) = 0` | `eqm_iff_isEqmPrice` |
| 17.B, p. 581 | Other systems of equilibrium equations (Appendix A) | listed (verbal, forward reference) |
| Proposition 17.B.2, pp. 581-582 | `z` satisfies (i)-(v) | `proposition_17_B_2`; general form `wealthExcessDemand`, `isStandard_wealthExcessDemand`, `IsStandardExcessDemand.congr`, `excessDemand_eqOn`, `isStandardExcessDemand_of_fin_zero` |
| Proposition 17.B.2(i), p. 582 | Continuity (from continuity of demand) | `wealthExcessDemand_continuous`, `continuousOn_uDemand` (Proposition 3.AA.1 extended to `w = 0`), `continuousOn_uDemand_comp`, `isOpen_pwDomainSet`, `exists_pos_le_of_strictlyPositive`, `wealthDomain` |
| Proposition 17.B.2(ii), p. 582 | Homogeneity of degree zero | `wealthExcessDemand_homogeneous` |
| Proposition 17.B.2(iii), p. 582 | Walras' law | `wealthExcessDemand_walras` |
| Proposition 17.B.2(iv), p. 582 | `z_ℓ(p) > -s`, since `Xᵢ = ℝ^L₊` bounds net supply by the endowment | `wealthExcessDemand_boundedBelow` |
| Proposition 17.B.2(v), proof, p. 582 | Some consumer's wealth tends to a positive limit (`p·∑ᵢ ωᵢ > 0`) and his demand becomes unbounded | `exchange_boundary_wealth`, `dotProduct_pos_of_ne_zero`, `nonneg_of_tendsto_pos`, `demand_bounded_near_boundary_false`, `wealthExcessDemand_boundary` |
| Footnote 3, p. 582 | (i)-(iv) hold with locally nonsatiated preferences | `footnote_17_3` |
| Instance | `u = ∑ₗ √xₗ` is a standard utility; a standard excess demand function | `sqrtUtility`, `strictlyQuasiconcaveOn_sqrtUtility`, `sqrtUtility_stronglyMonotone`, `standardUtility_sqrtUtility`, `sqrtEconomy`, `sqrtEconomy_isStandard` |
| Correction | Endowments must lie in `ℝ^L₊` (corrections 1) | `negEndowEconomy`, `negEndowEconomy_demand_empty` |
| 17.B, p. 582 | With Walras' law, `p ≫ 0` clears all markets iff it clears the first `L - 1` | `eqm_iff_trunc_eq_zero` (Basic) |
| (17.B.3), p. 582 | Production inclusive excess demand function | `ProdEconomy`, `ProdEconomy.wealth`, `ProdEconomy.supplyTotal`, `prodExcessDemand`, `ProdEconomy.toPriv`; supply `ySup`, `ySup_mem`, `ySup_smul`, `supply_nonempty`, `supply_subsingleton`, `supply_coord_lower`, `continuousOn_ySup`, `continuousOn_profit` |
| 17.B, p. 582 | `p` is an equilibrium price vector iff `z̃(p) = 0` | `prod_eqm_iff` |
| 17.B, pp. 582-583 | Without bounded production sets `z̃` may be undefined, but equilibria are still its zeros | listed (verbal) |
| 17.B, p. 583 and footnote 4 | With set-valued supply: `p` is an equilibrium price vector iff `0 ∈ z̃(p)` | `prodExcessCorr`, `footnote_17_4` |
| Small type, p. 583 | Linear activity technology | `linActTech`, `linActEconomy`, `activity_mem_linActTech`, `dotProduct_activities`, `dotProduct_le_of_le` |
| Small type, p. 583 | No free goods; zero maximum profits; equilibria have `y = ∑ⱼ αⱼ aⱼ` | `linAct_profit_zero`, `linAct_eqm_structure` |
| (17.B.4)-(17.B.5), p. 583 | `(p, α)` is an equilibrium iff `z(p) - ∑ⱼ αⱼ aⱼ = 0`, `p·aⱼ ≤ 0`, `αⱼ(p·aⱼ) = 0` | `linAct_eqm_iff` |
| Small type, p. 583 | (17.B.5) as the equations `αⱼ p·aⱼ + Max {0, p·aⱼ} = 0` | `complementarity_iff_max` |
| Small type, p. 583 | Convex technologies as constant returns with a firm-specific factor (Proposition 5.B.2); a single representative firm | listed (verbal; Chapter 5) |
| Small type, p. 584 | A single constant returns technology freely available to consumers | listed (verbal); formal content is Exercise 17.B.6 |
| Footnote 5, p. 584 | The two-stage process reduces production to exchange | listed (verbal) |

## 17.C Existence of Walrasian equilibrium

| Source | Claim | Lean |
| --- | --- | --- |
| 17.C, p. 584, footnote 6 | Existence as a consistency test | listed (verbal) |
| 17.C, p. 584 | Any `z` satisfying (i)-(v) has a zero; hence existence under Proposition 17.B.2 | `proposition_17_C_1`, `proposition_17_C_1_economy` |
| 17.C, pp. 584-585, Figure 17.C.1 | `L = 2`: normalize `p₂ = 1`, solve `z₁(p₁, 1) = 0` by continuity | `existence_two_goods`, `vec2_mem_posOrthant`, `walras_two` |
| Footnote 7, p. 585 | Axis convention (Marshall vs Walras) | listed (verbal) |
| Footnote 8, p. 585 | `z₁(p₁, 1) > 0` for small and `< 0` for large `p₁` (via (iv), (v), Walras' law, homogeneity) | `footnote_17_8_low`, `footnote_17_8_high` |
| Proposition 17.C.1, p. 585 | Statement | `proposition_17_C_1`, `proposition_17_C_1_economy` |
| Proof, p. 586 | The simplex `Δ`, its interior | `priceSimplex` (Basic), `isClosed_priceSimplex`, `priceSimplex_subset_Icc`, `isCompact_priceSimplex`, `convex_priceSimplex`, `single_mem_priceSimplex`, `dotProduct_self_pos_of_mem_priceSimplex` |
| Step 1, p. 586 | `f(p) = argmax_{q ∈ Δ} z(p)·q`; the face display; `z(p) ≠ 0 ⇒ f(p) ⊆ Boundary Δ`; `z(p) = 0 ⇒ f(p) = Δ` | `fixedPointCorr`, `fixedPointCorr_pos`, `step1_face`, `simplex_argmax_zero`, `step1_subset_boundary`, `step1_eq_simplex`, `fixedPointCorr_subset` |
| Step 2, p. 586 | `f(p) = {q ∈ Δ : p·q = 0} ≠ ∅` on the boundary; no boundary fixed point | `fixedPointCorr_not_pos`, `step2_nonempty`, `step2_not_fixed`, `fixedPointCorr_nonempty` |
| Step 3, p. 586 | A fixed point is an equilibrium | `step3_fixed_isEqm` |
| Step 4, p. 587 | Convex valued; upper hemicontinuous (closed graph) | `exercise_17_C_1`, `step4_isClosed_graph` |
| Footnote 9, p. 587 | `f(p)` is a face of `Δ` | `simplex_argmax_iff`, `footnote_17_9_boundary` |
| Footnote 10, p. 587 | Expenditure on a good is bounded by the value of excess supplies | `footnote_17_10` |
| Step 5, p. 587 | Kakutani's theorem (LeanEconomics `kakutani`) | `proposition_17_C_1` |
| 17.C, pp. 587-588 | Figure 15.B.10(a): property (v) fails (bounded excess demand as `p → (1, 0)`); consumer 2 not strongly monotone | `fig_15_B_10a_excessDemand_bounded`, `fig_15_B_10a_not_boundary`, `demandFn_mem_budget`; Chapter 15 `fig_15_B_10a_not_stronglyMonotone` |
| 17.C, p. 588 | Figure 15.B.10(b): nonconvex preferences, `z` not a function | `fig_15_B_10b_demand_not_subsingleton`; Chapter 15 `sqUtility_props` |
| Footnote 11, p. 588 | Existence for convex-valued uhc correspondences; fails in 15.B.10(b) | Exercise 17.C.2 (`exercise_17_C_2`); `fig_15_B_10b_demand_not_subsingleton` |
| 17.C, p. 588 | Locally nonsatiated preferences can give `z` defined at all nonzero `p ≥ 0`; equilibrium condition `z(p) ≤ 0` | listed (verbal); see (17.B.1') |
| Proposition 17.C.2, p. 588 | Continuous `z` on `ℝ^L₊ \ {0}` with Walras' law has `z(p*) ≤ 0` | `proposition_17_C_2`, `nonzeroNonneg`, `priceSimplex_subset_nonzeroNonneg` |
| Proof of 17.C.2, pp. 588-589, Figure 17.C.2 | `z⁺`, `α(p) ≥ 1`, `f(p) = (p + z⁺(p))/α(p)` continuous `Δ → Δ`; `z⁺·z = 0 ⇒ z ≤ 0`; Brouwer | `zPlus`, `brouwerMap`, `one_le_sum_zPlus`, `brouwerMap_mapsTo`, `brouwerMap_continuousOn`, `le_zero_of_zPlus_dotProduct_eq_zero`; Figure 17.C.2 listed (graphical) |
| 17.C, p. 589 | Proposition 17.C.1 applies to production economies (Exercise 17.B.4) | `production_existence` |
| 17.C, p. 589 | The correspondence version | `exercise_17_C_2` |
| 17.C, p. 589 | Computation of equilibria (Scarf) | listed (verbal) |
| Small type, p. 589 | The second welfare theorem as a corollary of existence | `secondWelfare_of_existence` |
| Footnote 12, p. 589 | Validity beyond these economies | listed (verbal) |

## Exercises 17.B and 17.C

| Source | Claim | Lean |
| --- | --- | --- |
| Exercise 17.B.1, p. 641 | (i') iff profit maximization on `-ℝ^L₊` | `exercise_17_B_1` |
| Exercise 17.B.2, p. 642 | Property (v) of Proposition 17.B.2 | `exercise_17_B_2`, `wealthExcessDemand_boundary`, `demand_bounded_near_boundary_false` |
| Exercise 17.B.3(a), p. 642 | The maximal excess demand is eventually at goods whose price goes to zero | `exercise_17_B_3a` |
| Exercise 17.B.3(b), p. 642 | A good whose price goes to zero may stay in excess supply | `exercise_17_B_3b`, `ex17B3z`, `ex17B3z_isStandard`, `ex17B3path`, `sum_inv_pos`, `sum_pos_of_pos` |
| Exercise 17.B.4, p. 642 | `z̃` of (17.B.3) satisfies (i)-(v) | `exercise_17_B_4` (with `0 ∈ Yⱼ`, corrections 2); instance `discTech`, `isClosed_discTech`, `discTech_bdd`, `strictConvex_discTech`, `discEconomy`, `discEconomy_isStandard` |
| Exercise 17.B.5, p. 642 | Equation system for constant returns single-output firms with differentiable unit costs | `exercise_17_B_5`, `euler_unitCost`, `gradVec`, `dotProduct_gradVec` |
| Exercise 17.B.6, p. 642 | Rader: equilibria of the two-stage exchange problem are Walrasian equilibria with production | `exercise_17_B_6`, `RaderOptimal`, `cone_sum_mem`; "Interpret" listed (verbal) |
| Exercise 17.C.1, p. 642 | `f` of Proposition 17.C.1 is convex valued | `exercise_17_C_1` |
| Exercise 17.C.2, p. 642 | Convex-valued uhc excess demand correspondences with (i)-(v) have `0 ∈ z(p)` | `exercise_17_C_2`, `CorrBoundary`, `ex17C2_uniform`, `coord_bound_of_walras`, `deltaSimplex`, `isCompact_deltaSimplex`, `convex_deltaSimplex`, `deltaArgmax`, `exercise_17_C_2_of_function` (instance), `exercise_17_C_2_needs_nonempty` (corrections 3) |
| Exercise 17.C.3, p. 643 | Budget sets and equilibrium with taxes on gross consumption | `grossTaxBudget`, `IsTaxEqm` |
| Exercise 17.C.3(a), p. 643 | Illustrate (graphical); an equilibrium with taxes need not be Pareto optimal | `exercise_17_C_3a`, `taxExampleT`, `taxExampleX`, `sqrt_tangent`; illustration listed (graphical) |
| Exercise 17.C.3(b), p. 643 | Existence of an equilibrium with taxes via Proposition 17.C.1 | OPEN: the lump-sum rebate `R` is a second unknown. At market clearing the rebate condition `R = (1/I)∑ᵢ∑ₗ t_ℓᵢp_ℓx_ℓᵢ` is implied by the budget identities, but at nonequilibrium prices the induced excess demand depends on `(p, R)`, and `R ↦ (1/I)∑ᵢ taxᵢ(p, p·ωᵢ + R)` need not have a unique or continuously selected fixed point, so Proposition 17.C.1 (a function of `p`) does not apply directly; a proof needs a fixed-point argument in `(p, R)` with the `Δ_δ` truncation and boundary limit of Proposition 17.C.2 redone for the pair (not done) |
| Exercise 17.C.3(c), p. 643 | Budget set with taxes on net trades; how it differs (kinks at `ω`); represent graphically | `netTaxBudget`, `exercise_17_C_3c` (it is the equal-rate buy/sell budget set, convex, contains `ω`); graph listed (graphical) |
| Exercise 17.C.3(d), p. 643 | Budget set with different buying and selling rates | `buySellTaxBudget`, `exercise_17_C_3d` (convex) |
| Exercise 17.C.3(e), p. 643 | How to approach existence for (c) | listed (verbal) |
| Exercise 17.C.4, p. 643 | The progressive redistribution rule | `progressiveWealth`, `progressiveWealth_eq` (each consumer gets `(wᵢ + w̄)/2`) |
| Exercise 17.C.4(a), p. 643 | After-tax wealths `(5p₁ + 7p₂)/4`, `(7p₁ + 5p₂)/4` | `exercise_17_C_4a` |
| Exercise 17.C.4(b), p. 643 | The conditions of Proposition 17.C.1 hold (so an equilibrium exists) | `exercise_17_C_4b` |
| Exercise 17.C.5, p. 643 | Induced preferences `≿*` | `inducedPref` |
| Exercise 17.C.5(a), p. 643 | `≿*` is complete and transitive | `exercise_17_C_5a` |
| Exercise 17.C.5(b), p. 643 | `Yᵢ` convex ⇒ `≿*` convex | `exercise_17_C_5b` (for a convex `≿`) |
| Exercise 17.C.5(c), p. 644 | Marketed and household goods as pure exchange of marketed goods; discuss | listed (verbal) |
| Exercise 17.C.6, p. 644 | `L = 2`: four examples, each violating exactly one of (i), (iii), (iv), (v) (all homogeneous), with no solution of `z(p) = 0` | (i): `exercise_17_C_6_i`, `ex17C6NotCont`; (iii): `exercise_17_C_6_iii`, `ex17C6NotWalras`; (iv): `exercise_17_C_6_iv`, `ex17C6NotBdd`; (v): `exercise_17_C_6_v`, `ex17C6NotBdry`; helpers `edBoundary_two`, `ex17C6_ratio_large` (printed list "(i), (iii), and (iv)": corrections 6) |
| Exercise 17.C.6, p. 644 | Why (ii) is not in the list: (i), (iii), (iv), (v) alone give an equilibrium (any `L`), so no example can violate only (ii) | `exercise_17_C_6_ii`, `homogenize`, `homogenize_isStandard` |

## 17.D Local uniqueness and the index theorem

Normalization `p_L = 1` with `L = n + 1`; `p̂ ∈ ℝ^{L-1}` is a normalized price vector. Modules
`Regularity`, `IndexTwoGoods`, `CobbDouglasEconomy`, `GenericRegularity`, `Exercises17D`.

| Source | Claim | Lean |
| --- | --- | --- |
| 17.D, p. 589 | Introduction: uniqueness or multiplicity | listed (verbal) |
| Figure 17.D.1, p. 590 | `z₁(p₁, 1)` of Example 15.B.2 with three equilibria `p₁ ∈ {1/2, 1, 2}`, all regular (p. 591) | equilibria: Chapter 15 `example_15_B_2` (imported); regularity and indices `+1, -1, +1`: `figure_17_D_1` (`z₁(q, 1) = G(q^{1/9})`, `G(t) = r/t⁹ - 1/t⁸ + 1/t - r`: `f17_excessDemand`, `f17G`, `f17G'`, `f17_hasDerivAt_G`, `f17_regular`, `f17_facts`, `f17_rpow_pow`); graph listed (graphical) |
| p. 590 | Parsimony of the Walrasian model; uniqueness only under special conditions (17.F); history selects the region | listed (verbal) |
| p. 590 | Locally unique (locally isolated) equilibrium; local uniqueness property; locally determinate theory | the property is the conclusion of `proposition_17_D_1_isolated` |
| Figures 17.D.2-17.D.3, pp. 590-591 | A continuum of equilibria is possible (Edgeworth box and excess demand) | `fig_17_D_3`, `fig17D3z`, `fig17D3g`, `fig17D3g_eq_zero`, `twoGoodED`, `twoGoodED_isStandard`; Edgeworth-box picture listed (graphical) |
| p. 590 | Debreu (1970): continua happen only by accident | Proposition 17.D.5 below |
| p. 591 | Consumers `(≿ᵢ, ωᵢ)` with `ωᵢ ≫ 0`; `z` satisfies (i)-(v) and is `C¹` | `proposition_17_B_2` (batch 1); differentiability as a hypothesis on demand functions (`proposition_17_D_5`), instance `contDiffOn_cdDemand` |
| Footnote 13, p. 591 | Appendix A to Chapter 3 discusses differentiability of demand | listed (verbal; Chapter 3 `AppendixADifferentiability`) |
| p. 591 | `ẑ(p) = (z₁(p), …, z_{L-1}(p))`; `(p₁, …, p_{L-1}, 1)` is an equilibrium iff `ẑ(p) = 0` | `normPrice`, `normPrice_castSucc`, `normPrice_last`, `normPrice_mem_posOrthant`, `normPrice_init`, `continuous_normPrice`, `normED`, `IsNormEqm`, `isNormEqm_iff`, `IsNormEqm.normED_eq_zero` |
| Footnote 14, p. 591 | If `z(p) = 0` and `Dz(p)` has rank `L - 1`, then `Dẑ(p)` has rank `L - 1` whichever good is the numeraire, and the sign of its determinant does not depend on the normalization | `footnote_17_14` (all principal `(L-1)`-minors nonzero, same sign), `ker_eq_smul_of_rank`, `euler_fderiv` (`Dz(p)p = 0`), `walras_fderiv` (`pᵀDz(p) = 0` at equilibrium), `normED_hasFDerivAt` (`Dẑ` is the minor deleting the numeraire), `truncCLM`, `inclCLM`, `inclCLM_castSucc`, `inclCLM_last`, `hasFDerivAt_normPrice`, `isRegularEqm_of_rank` (corrections 12) |
| Definition 17.D.1, p. 591 | Regular equilibrium (`Dẑ(p)` nonsingular); regular economy | `IsRegularEqm`, `IsRegularEconomy`, `isInvertible_iff_det_ne_zero` |
| p. 591 | Figure 17.D.1: every equilibrium regular (nonzero slope); Figure 17.D.3: no equilibrium regular | Figure 17.D.3: `fig_17_D_3`; Figure 17.D.1: `figure_17_D_1`; further regular multi-equilibrium instances are `exercise_17_D_1_corrected` (three equilibria, CES) and `exercise_17_D_8` |
| Proposition 17.D.1, p. 592 | A regular equilibrium is locally isolated; a regular economy has finitely many normalized equilibria | `proposition_17_D_1_isolated`, `proposition_17_D_1_finite`, `dist_init_le` |
| Proof of 17.D.1, p. 592 | Inverse function theorem; there is `r > 0` with `1/r < p_ℓ < r` at equilibria (boundary condition); the equilibrium set is closed and bounded, hence compact; compact and discrete is finite | `proposition_17_D_1_bounds`, `isCompact_normEqm`, `normEqm_eq_image`, `proposition_17_D_1_finite` |
| Instance | A regular economy satisfying (i)-(v) | `cd1_finite`, `cd1ED_isStandard`, `cd1_isRegularEconomy`, `cd1ED`, `cd1ED_eq` |
| p. 592 | `L = 2`: a regular economy has an odd number of equilibria and the slopes alternate, starting (and ending) negative | `two_goods_card_odd`, `two_goods_first_slope_neg`, `two_goods_last_slope_neg`, `two_goods_slopes_alternate`, `two_goods_local_sign`, `two_goods_pos_iff`, `two_goods_sign_right`, `two_goods_sign_left`, `two_goods_bracket`, `two_goods_data` |
| Definition 17.D.2, p. 592 | `index p = (-1)^{L-1} sign |Dẑ(p)|` | `eqmIndex`, `eqmIndex_eq_one_or`, `itgSgn`, `itgSgn_pos`, `itgSgn_neg`, `itgSgn_eq_of_pos_iff` |
| Footnote 15, p. 592 | `sign α = +1` or `-1` for `α > 0`, `α < 0` | `footnote_17_15` |
| p. 592 | `L = 2`: `|Dẑ(p)|` is the slope of `z₁(·, 1)`; index `+1` iff the slope is negative | `slope2`, `det_eq_slope2`, `eqmIndex_two`, `two_goods_hasDerivAt`, `vec1`, `normPrice_vec1`, `vec1_apply_zero`, `isNormEqm_vec1_iff` |
| p. 593 | For a regular economy the sum of indices makes sense (finitely many equilibria) | `proposition_17_D_1_finite` |
| Proposition 17.D.2, p. 593 | The index theorem: `∑ index p = +1` for every regular economy | `L = 2`: `proposition_17_D_2_two_goods` (from (i)-(v) and regularity; core `two_goods_telescope`), instance `proposition_17_D_2_two_goods_instance`; every `L`, one-consumer Cobb-Douglas economies: `exercise_17_D_8`. General `L`: OPEN: needs the Brouwer degree (or Poincaré-Hopf / the homotopy argument of pp. 597-598 with transversality of the homotopy), not in Mathlib |
| p. 593, footnote 16 | The number of equilibria of a regular economy is odd (Dierker 1972), so nonzero | `L = 2`: `two_goods_card_odd`, `odd_card_of_sum_eq_one`; general `L`: OPEN (a consequence of Proposition 17.D.2) |
| p. 593 | Index types; positive-index equilibria more fundamental; uniqueness (17.F); 17.E | listed (verbal) |
| p. 593 | Generically, economies are regular | `proposition_17_D_5` |
| Footnote 17, p. 593 | References (Balasko, Mas-Colell) | listed (verbal) |
| (17.D.1), p. 593 | A system of `M` equations in `N` unknowns `f(v) = 0` | `RegularEqSystem` (`f : ℝ^N → ℝ^M`) |
| pp. 593-594 | Over-, exactly and underdetermined systems; "not always true" | `M > N`: `regularEqSystem_iff_of_lt`, `proposition_17_D_3_over`; `M = N`: `isolated_of_isInvertible`; `M < N`: `exercise_17_D_2`; the counterexamples with linear equations listed (verbal) |
| Definition 17.D.3, p. 594 | Regular system: `rank Df(v) = M` whenever `f(v) = 0` | `RegularEqSystem` |
| p. 594 | `M < N`: solutions parametrized by `N - M` variables (Exercise 17.D.2); `M = N`: locally isolated; `M > N`: regular iff no solution | `exercise_17_D_2`; `isolated_of_isInvertible`, `proposition_17_D_1_isolated`; `regularEqSystem_iff_of_lt` |
| Figure 17.D.4, p. 594 | The regular case is typical; perturbed system | listed (graphical) |
| Footnote 18, p. 594 | Perturbations should be `C¹` | listed (verbal) |
| pp. 594-595 | Parametrized systems `f(v; q)`; "for almost every `q`" | the measure-zero form of `proposition_17_D_3`, `proposition_17_D_5` |
| Footnote 19, p. 595 | Genericity in the first (full measure), second (open, full measure) and third (open dense) senses; first sense used | listed (verbal); all results use the first sense |
| Footnote 20, p. 595 | `f` as many times differentiable as necessary | `C¹` suffices for `M ≥ N` (`proposition_17_D_3`, `proposition_17_D_3_over`) |
| Proposition 17.D.3, p. 595 | Transversality theorem | `M = N`: `proposition_17_D_3` (bridge to Chapter 3 `theorem_M_E_2_regular`), `fderiv_partial_left`; `M > N`: `proposition_17_D_3_over`. `M < N`: OPEN: needs Sard's theorem for `C^k` maps (`k > N - M`) from the `(N + S - M)`-dimensional solution manifold to `ℝ^S`; Mathlib has only the measure-zero image lemma in equal dimension (corrections 10) |
| p. 595 | If `M > N`, generically `f(v; q) = 0` has no solution | `proposition_17_D_3_over` |
| p. 596 | Endowments `ω ∈ ℝ^{LI}_{++}` as parameters; `ẑ(p; ω)` | `endowOf`, `genSystem`, `demandED` |
| Proposition 17.D.4, p. 596 | `rank D_ω ẑ(p; ω) = L - 1` (indeed already `D_{ω₁}`); a perturbation with `p·dω₁ = 0` moves `ẑ` by `-dω̂₁` | `proposition_17_D_4`, `genSystem_shift`, `endowPerturb`, `endowOf_add_smul`, `endowOf_endowPerturb`, `normPrice_dotProduct_snoc`; explicit computation `exercise_17_D_3` |
| Proposition 17.D.5, p. 596 | For almost every `(ω₁, …, ω_I) ∈ ℝ^{LI}_{++}` the economy is regular (Debreu) | `proposition_17_D_5` (`C¹` demand functions, corrections 11), `contDiffOn_genSystem`, `contDiff_normPrice`, `isRegularEconomy_congr`; instance `proposition_17_D_5_cobbDouglas`, `cdEconomy`, `cdUtility`, `excessDemand_cdEconomy`, `walrasianDemand_cobbDouglas`, `cdDemand`, `contDiffOn_cdDemand`, `dotProduct_cdDemand`, `cdDemand_smul`, `cd_wealth_nonneg`, `cdED_isStandard` |
| Footnote 21, p. 596 | The nonregular endowments form a Lebesgue-null subset of `ℝ^{LI}` (probability zero under a nondegenerate normal) | `proposition_17_D_5` (measure zero); the normal-distribution reformulation listed (verbal) |
| p. 596, Figure 17.D.5 | The equilibrium set `E = {(ω₁, ω₂, p₁) : ẑ(p₁, 1; ω) = 0}`; number of equilibria jumps from 3 to 1 | listed (graphical) |
| p. 597 | The 3-to-1 picture is typical because of the index theorem; Balasko (1988) | listed (verbal) |
| Small type, p. 597 | Generic determinacy extends to externalities, taxes (Exercise 17.D.6); "finite" need not mean "small"; sunspots (19.F) | Exercise 17.D.6 below; remainder listed (verbal) |
| pp. 597-598, "On the index theorem" | Homotopy `ẑ(p, t) = tẑ(p) + (1-t)ẑ⁰(p)` from a Cobb-Douglas `ẑ⁰` with a unique equilibrium of sign `(-1)^{L-1}` (Exercise 17.D.8); the solution set is a union of curves and loops; indices at the ends | `ẑ⁰`: `exercise_17_D_8`, `cd1_sign_det`; the topological argument: OPEN (degree theory / one-manifolds with boundary), as for Proposition 17.D.2 |
| Figure 17.D.6, p. 598 | The equilibrium set under a homotopy | listed (graphical) |
| Footnote 22, p. 597 | Arbitrary homotopies (Figures 17.G.1) | listed (verbal) |
| Footnote 23, p. 598 | `L = 2`: the path reverses direction exactly where `∂ẑ₁(p₁, t)/∂p₁ = 0` (implicit function theorem) | listed (verbal); the implicit function theorem is Chapter 3 `theorem_M_E_1` |

## Exercises 17.D

| Source | Claim | Lean |
| --- | --- | --- |
| Exercise 17.D.1, p. 644 | CES economy (`ρ = -4`, weights 2): compute excess demand; verify multiple equilibria | excess demand: `ex17D1_excessDemand`, `ex17D1_excessDemand_eq`, `ex17D1_walras`, `ex17D1_eqm_iff`, `ex17D1Economy`, `cesU`, `cesW`, `cesD`, `walrasianDemand_cesU`, `dotProduct_cesD`, `exists_fifth_root`, `ex17D1_pos`; FALSE as printed (unique equilibrium): `exercise_17_D_1_printed`; corrected (weight `(31/14)⁵`, three equilibria): `exercise_17_D_1_corrected`, `ex17D1Kappa` (corrections 7) |
| Exercise 17.D.2, p. 644 | Implicit function theorem: near a regular solution the solution set is parametrized by `N - M` parameters | `exercise_17_D_2` |
| Exercise 17.D.3, p. 644 | The computations for Proposition 17.D.4 | `exercise_17_D_3` (`D_{ω_{i₀}}ẑ = D_w x̂ pᵀ - [I | 0]`, directionally) |
| Exercise 17.D.4, p. 644 | Two goods, two consumers, fixed `ω̄ ≫ 0`: for almost every `ω₁ ≪ ω̄` finitely many equilibria (Slutsky hint) | `exercise_17_D_4` (a.e. regular, from negative own substitution effects), `exercise_17_D_4_finite` (finite under (i)-(v)), `d4_rank` (full rank: `D_{ω₁}ẑ₁ = (∂_w x₁₁ - ∂_w x₁₂)pᵀ`, else `∂ẑ₁/∂p₁ = s₁ + s₂ < 0`), `d4Sys`, `d4Sys_apply`, `d4X`, `d4Region`, `isOpen_d4Region`, `contDiffOn_d4Sys`, `normPrice_one`; instance `exercise_17_D_4_cobbDouglas`, `cd_slutsky_neg` |
| Exercise 17.D.5, p. 644 | System in `(x₁, x₂, p, λ₁, λ₂)` with endowments as parameters satisfies the full rank condition (no aggregation) | `focSystem_rank`, `focSystem`, `focX1`, `focX2`, `focDir`, `focX1_line`, `focX2_line`, `focSystem_shift_ω`; generic regularity and instance (log utilities) `exercise_17_D_5`, `logGrad`, `contDiffOn_logGrad`, `logGrad_fderiv_isInvertible`, `isInvertible_of_injective` |
| Exercise 17.D.6, p. 644 | With an externality `u₁(x₁, x₂)`, generically finitely many equilibria | `exercise_17_D_6` (a.e. regular), `exercise_17_D_6_isolated` (locally isolated), `exercise_17_D_6_finite` (finite when the equilibrium set is compact; corrections 13), `focDomain`, `isOpen_focDomain`, `contDiff_focX1`, `contDiff_focX2`, `contDiffOn_focSystem`, `isolated_of_isInvertible`, `finite_of_isCompact_isolated`; instance `exercise_17_D_6_instance`, `externalGrad` |
| Exercise 17.D.7(a), p. 644 | `N` islands without communication, three equilibria each: `3^N` equilibria | `exercise_17_D_7a` |
| Exercise 17.D.7(b), p. 644 | Identical islands with free transport: 3 equilibria | `exercise_17_D_7b` (corrections 13) |
| Exercise 17.D.8, p. 645 | The index of the equilibrium of a one-consumer Cobb-Douglas economy is `+1` | `exercise_17_D_8`, `cd1_det`, `cd1_sign_det`, `cd1Jacobian`, `cd1_hasFDerivAt`, `det_diagonal_add_vecMulVec`, `normPrice_dotProduct`, `cd1_eqm_iff` |

## 17.E Anything goes: the Sonnenschein-Mantel-Debreu theorem

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 598-599 | Introduction: no restrictions beyond Proposition 17.B.2; exchange economies suffice (aggregation is unproblematic in production) | listed (verbal) |
| (17.E.1), p. 599 | `∑ₖ (∂zₗ/∂pₖ) pₖ = 0`, i.e. `Dz(p) p = 0` (homogeneity) | `eq_17_E_1`, `pe_clm_apply_eq_sum` (with `euler_fderiv`) |
| (17.E.2), p. 599 | `∑ₖ pₖ ∂zₖ/∂pₗ = -zₗ(p)`, i.e. `p·Dz(p) = -z(p)` (Walras' law) | `eq_17_E_2` (with `walras_fderiv`) |
| (17.E.3), p. 599 | `Dz(p) = ∑ᵢ [Sᵢ(p, p·ωᵢ) - D_w xᵢ(p, p·ωᵢ) zᵢ(p)ᵀ]` | `eq_17_E_3`, `aggExcessDemand`, `pe_dotCLM`, `pe_dotCLM_apply` (Slutsky matrix: Chapter 2 `slutskyMatrix`) |
| p. 599 | Without wealth effects `Dz(p)` would inherit negative semidefiniteness | listed (verbal); made precise by Proposition 17.E.1 |
| p. 599 | The wealth-effect matrix `D_w xᵢ zᵢᵀ` has rank 1 (rows/columns proportional) | `rank_wealthEffectMatrix_le` (rank `≤ 1`), `rank_wealthEffectMatrix_eq_one` (`= 1` when both vectors are nonzero) |
| Footnote 24, p. 599 | `z(p)` can take any value (choose `ω` with `ω + z(p) ≫ 0` and a utility demanding it) | exactly the values with `p·z = 0`: `footnote_17_24`; necessity `footnote_17_24_necessary` (corrections 16) |
| p. 600, footnote 25 | The wealth effect of consumer `i` can hurt in at most one direction | listed (verbal); made precise by Proposition 17.E.1 |
| Proposition 17.E.1, p. 600 | `I < L`: at an equilibrium there is `dp ≠ 0`, `p·dp = 0`, `dp·Dz(p) dp ≤ 0` | `proposition_17_E_1` (`I ≥ 1`, demand functions with Walras' law and the weak axiom, differentiable; Chapter 2 `proposition_2_F_2` gives `Sᵢ` n.s.d.), `pe_walras_indiv`; instance `proposition_17_E_1_instance`, `pe_demandGood0`, `pe_demandGood0_walras`, `pe_demandGood0_weakAxiom` (corrections 15) |
| p. 600 | With `I ≥ L` no restriction beyond (17.E.1)-(17.E.2) is to be expected | listed (verbal); confirmed by Proposition 17.E.2 |
| Proposition 17.E.2, p. 600 | Given `p`, `z` and `A` with `p·z = 0`, `Ap = 0`, `p·A = -z`, there are `L` consumers with `z(p) = z`, `Dz(p) = A` | `proposition_17_E_2` (corrections 17) |
| Proof of 17.E.2, pp. 600-601 | `A = ∑ₗ eˡaˡ`; consumers with `zᵢ(p) = -pᵢ(aⁱ)ᵀ`, `D_w xᵢ = (1/pᵢ)eⁱ`, `Sᵢ = 0`, `xᵢ = ωᵢ - pᵢ(aⁱ)ᵀ ≫ 0`; kinked indifference sets | `kinkUtility`, `kinkUtility_continuous`, `kinkUtility_stronglyMonotone`, `kink_demand` (demand `x̄ + ((w - p'·x̄)/p'ᵢ) eⁱ` for all `p'` near `p`: wealth effect `(1/p'ᵢ)eⁱ`, null substitution); endowments `ωᵢ = R𝟙 + pᵢ aⁱ` inside `proposition_17_E_2` |
| Footnote 26, p. 600 | "Vertex" = "kink" when `L = 2` | listed (verbal) |
| Footnote 27, p. 601 | `D_w xᵢ = αᵢ eⁱ` and `p·D_w xᵢ = 1` give `αᵢ = 1/pᵢ` | `footnote_17_27` |
| Footnote 28, p. 601 | One can also prescribe symmetric n.s.d. substitution matrices `Sᵢ` with `p·Sᵢ = 0`, `Sᵢp = 0` (smooth indifference sets if rank `L - 1`) | OPEN: needs consumers with prescribed second-order behaviour at the demanded bundle (a smooth utility with given Hessian on `T_p`); not attempted |
| Figure 17.E.1, p. 601 | The construction for `L = 2` | listed (graphical); content in `proposition_17_E_2` |
| p. 602 | On `P_ε` a candidate `z` must be continuous, homogeneous of degree zero, and satisfy Walras' law | the hypotheses of `proposition_17_E_3`; necessity is Proposition 17.B.2 (`IsStandardExcessDemand`, earlier batches) |
| Proposition 17.E.3, p. 602 | SMD: continuous, homogeneous of degree zero, Walras' law on `P_ε` ⟹ aggregate excess demand of `L` consumers on `P_ε` | `proposition_17_E_3` (all `L`), `pEps`, `pEps_pos`, `pEps_smul`; the book's two-good proof `proposition_17_E_3_two`. Strict convexity of preferences: OPEN (corrections 18) |
| Footnote 29, p. 602 | History (Sonnenschein 1973, Mantel 1974/1976, Debreu 1974) | listed (verbal) |
| Footnote 30, p. 602 | Any `I ≥ L` consumers suffice (add consumers without endowments) | `footnote_17_30` (`I = L + k`) |
| Proof, `L = 2`, p. 602 | `r` with `|z₁(p)| < r` on `P_ε`; `z¹₁ = z₁/2 + r`, `z²₁ = z₁/2 - r`, `zⁱ₂ = -(p₁/p₂) zⁱ₁`; `z = z¹ + z²`; each `zⁱ` continuous, homogeneous, Walras, never `0` | `smd2_bound`, `smd2z1`, `smd2z2`, `smd2_decomposition`, `pEps2_mk`, `pEps2_decomp` |
| Proof, `L = 2`, pp. 602-603 | Endowments `ωᵢ ≫ 0` with `ωᵢ + zⁱ(p) ≫ 0`; the offer curve does not touch `ωᵢ`; "we can always fit an indifference map" | `proposition_17_E_3_two` (endowments `R𝟙`); the indifference map: `smd_curve_rationalize`, from the general lemma `smd_rationalize` (`SMDData`, `smdTerm`, `smdSigma`, `smdBox`, `smdF`, `smdClamp`, `smdFt`, `smdQ`, `smdU` and lemmas `smdTerm_continuous`, `smdTerm_continuous_d`, `smdSigma_le`, `smdSigma_eq`, `smdSigma_continuous`, `smdBox_isCompact`, `mem_smdBox`, `smdBox_nonempty`, `smdF_inner_continuous`, `smdF_continuous`, `smdF_le`, `le_smdF`, `smdF_eq`, `smdBox_sum`, `smdSigma_mono`, `smdF_mono`, `smdF_lipschitz`, `smdF_add_le`, `smdF_concave`, `smdClamp_mem`, `smdClamp_of_mem`, `smdClamp_mono`, `smdClamp_sub_mono`, `smdFt_mono`, `smdClamp_continuous`, `smdFt_continuous`, `smdQ_le_iff`, `smdFt_lipschitz`, `smdQ_le_add`); consumers from utilities on excess demands: `smd_demand_eq`, `smd_consumer_props`, `smd_sum_props` |
| Figure 17.E.2, p. 603 | The offer curve `OCᵢ` and the fitted indifference map | listed (graphical); content in `smd_curve_rationalize` |
| p. 603 | Proposition 17.E.3 is silent near the boundary; existence, finiteness, oddness, index come from boundary behaviour | listed (verbal) |
| Footnote 31, p. 603 | A candidate `z` with no zero on `P_ε` is still generated; its equilibria lie outside `P_ε` | `footnote_17_31` |
| Footnote 32, p. 603 | Reference (Mas-Colell 1977) | listed (verbal) |
| Proposition 17.E.4, p. 603 | Any finite set of normalized prices `pⁿ` and rank-`(L-1)` matrices `Aₙ` with `Aₙpⁿ = 0`, `pⁿ·Aₙ = 0` and the index formula (alternating signs if `L = 2`) are the equilibria and price effects of an `L`-consumer economy | OPEN: the book omits the proof (Mas-Colell 1977); needs global control of the equilibrium set of the constructed economy (no new equilibria), beyond Proposition 17.E.3 |
| Footnote 33, p. 603 | `Âₙ`: delete one row and the corresponding column | listed (definition; cf. `footnote_17_14`) |
| p. 604 | Interpretation: further restrictions need strong assumptions; survey reference | listed (verbal) |
| Small type, p. 604 | With endowment bounds and nonnegative consumption, `z(·)` is further restricted (Figure 17.E.3) | Exercise 17.E.5 below |
| Figure 17.E.3, p. 604 | `z(p) = (-1, a)`, `z(p') = (b, -1)` | `exercise_17_E_5` |
| p. 604, footnote 34 | SA for excess demand ⟹ generated by rational preferences (proof of Proposition 3.J.1) | not used: the preferences are constructed directly (`smd_rationalize`, `debreu_consumer`) (corrections 18) |
| (17.E.4), p. 605 | `p` directly revealed preferred to `p'`: `z(p) ≠ z(p')`, `p·z(p') ≤ 0`; indirect via chains; the strong axiom | `RevPrefDirect`, `StrongAxiomED` (`Relation.TransGen`) |
| p. 605 | Normalization `‖p‖² = p·p = 1` | `unitPEps`, `pEps_normalize`, `unitPEps_isCompact`, `unitPEps_bounds`, `unitPEps_subset` |
| (17.E.4'), p. 605 | Proportionally one-to-one `z`; then (17.E.4) ⟺ `p ≠ p'`, `p·z(p') ≤ 0` | `PropOneToOne`, `RevPrefDirect'`, `revPrefDirect_iff` |
| p. 605 | Basic observation: `αᵢ(·) zⁱ(·)` with `αᵢ > 0` has the same revealed preferences, and is proportionally one-to-one with the SA if `zⁱ` is | `propOneToOne_smul`, `revPrefDirect_smul_iff`, `strongAxiomED_smul` |
| p. 605 | `zⁱ(p) = eⁱ - pᵢ p` is the projection of `eⁱ` on `T_p`, maximizing `-‖z - eⁱ‖` on `T_p`; proportionally one-to-one and SA | `debreuZ`, `debreuZ_walras`, `debreuZ_dist`, `unit_dot_le`, `debreuZ_revPref_lt`, `exercise_17_E_6`, `exercise_17_E_7` |
| p. 605 | `r` with `z(p) + rp ≫ 0` on normalized `P_ε`; `αᵢ(p) = zᵢ(p) + rpᵢ > 0` | inside `proposition_17_E_3` (`αᵢ ≥ 1`), extended off the normalized prices by Tietze |
| p. 606 | `∑ᵢ (zᵢ(p) + rpᵢ)(eⁱ - pᵢp) = z(p)` | `debreu_decomposition` |
| p. 606 | Each `αᵢ(·)zⁱ(·)` is generated by a consumer | `debreu_consumer`, `debreuDom`, `debreuRho`, `debreuRho_apply_self`, `debreuRho_apply_ne`, `debreuDom_gap`, `debreuRho_mem`, `debreuRho_of_le`, `debreuRho_continuous`, `debreuDom_isCompact`, `debreuZ_continuous`, `dot_debreuZ`; assembled in `proposition_17_E_3` |
| Figure 17.E.4, p. 605 | Revealed preference for excess demand | listed (graphical) |
| Figure 17.E.5, p. 606 | Debreu's construction | listed (graphical); content in `debreu_decomposition` |

## Exercises 17.E

| Source | Claim | Lean |
| --- | --- | --- |
| Exercise 17.E.1, p. 645 | Derive (17.E.1) and (17.E.2) | `exercise_17_E_1` |
| Exercise 17.E.2, p. 645 | Derive (17.E.3) | `exercise_17_E_2` |
| Exercise 17.E.3, p. 645 | Explicit utility functions for the consumers of Proposition 17.E.2 | `exercise_17_E_3`, `kinkUtility` |
| Exercise 17.E.4, p. 645 | A continuous, homogeneous, Walras `z` on `P_ε` (two goods) not generated by a rational preference relation; its offer curve passes through the endowment; compare Figure 17.E.2 | `exercise_17_E_4`, `ex17E4Z`, `ex17E4Dom`, `ex17E4Z_props` (`z(1, 1) = 0`); the graphical comparison listed (graphical) (corrections 20) |
| Exercise 17.E.5, p. 645 | The choices of Figure 17.E.3 are not generated by consumers with endowments `≤ (1, 1)` and nonnegative consumption | two consumers: `exercise_17_E_5`; three consumers: `exercise_17_E_5_three` (share constraints for any number of consumers: `ex17E5_shares`); four consumers: the obstruction disappears, `exercise_17_E_5_four` (corrections 21) |
| Exercise 17.E.6, p. 645 | `zⁱ(p) = eⁱ - pᵢp` (`‖p‖ = 1`) is proportionally one-to-one | `exercise_17_E_6` (on `{‖p‖ = 1, pᵢ > 0}` ⊇ normalized `P_ε`) |
| Exercise 17.E.7, p. 645 | `zⁱ` satisfies the strong axiom | `exercise_17_E_7` |

## 17.F Uniqueness of equilibria

| Source | Claim | Lean |
| --- | --- | --- |
| p. 606, footnote 35 | Introduction; four headings; surveys (Kehoe 1985, 1991; Mas-Colell 1991) | listed (verbal) |
| p. 606 | Standing assumption: continuous, strictly convex, strongly monotone preferences | `StandardUtility` (17.B); several results need less (strict convexity only: `wa_indivExcessDemand`, `proposition_17_F_5`, `exercise_17_F_9`) |
| p. 607 | A constant returns, convex technology `Y` (convex cone); the economy formed by `z(·)` and `Y` | `IsCRConvexTech`, `crEconomy` |
| p. 607 | The Section 4.D route (wealth distributed to maximize a social welfare function) is not promising; focus on the weak axiom for aggregate excess demand | listed (verbal) |
| Proposition 17.F.1, p. 607 | `p` is a Walrasian equilibrium price vector iff (i) `p·y ≤ 0` for all `y ∈ Y` and (ii) `z(p) ∈ Y` | `proposition_17_F_1` (exchange economy `E` plus the firm `Y`, Chapter 16's `IsWalrasEqm`), `IsCREqmPrice`, `cr_profit_zero`, `wa_excessDemand_walras`, `convex_posOrthant` (corrections 30) |
| Footnote 36, p. 607 | `Y` an aggregate production set; constant returns make profits zero in equilibrium; pure exchange is `Y = -ℝ^L_+` | `cr_profit_zero`, `footnote_17_36` |
| Definition 17.F.1, p. 607 | The weak axiom for excess demand: `z(p) ≠ z(p')`, `p·z(p') ≤ 0` imply `p'·z(p) > 0` | `WeakAxiomED` |
| p. 608 | In words: `p` revealed preferred to `p'` excludes the converse; same as Sections 1.G, 2.F | listed (verbal) |
| Footnote 37, p. 608 | Revealed preference defined on budget sets (price vectors) rather than choices | listed (verbal) |
| p. 608 | The weak axiom always holds for the excess demand of a single individual | `wa_indivExcessDemand`, `wa_of_demand_eq`; instance `cd1_weakAxiom`, `cd1_demand_eq` |
| p. 608 | It is a strong condition for aggregate excess demand (Section 4.C) | listed (verbal); see Example 17.F.1 and Exercise 17.F.3 |
| p. 608, Figure 17.F.1 | The weak axiom is necessary: if it fails at `p, p'`, both are equilibria for `Y* = {y : p·y ≤ 0, p'·y ≤ 0}` | `wa_violation_two_eqm`, `starTech`, `starTech_isCR` (closed convex cone) |
| p. 608 | The weak axiom is not sufficient for uniqueness, but gives convexity; finitely many normalized equilibria then means one | Proposition 17.F.2 below |
| Footnote 38, p. 608 | The generic finiteness of Section 17.D extends to production | listed (verbal) |
| Proposition 17.F.2, p. 609 | (a) Unique normalized equilibrium for every constant returns convex `Y` ⟹ weak axiom; (b) weak axiom ⟹ equilibrium price set convex for every such `Y`; finite ⟹ at most one | (a) `proposition_17_F_2_necessity` (hypothesis only for closed `Y`), its hypothesis holds for one Cobb-Douglas consumer: `cd1_unique_cr_eqm`; (b) `proposition_17_F_2_convex` (any `Y`), `wa_combo_eq`; finite case `proposition_17_F_2_finite`, `subsingleton_of_convex_finite`; with (i)-(v) and regularity (Proposition 17.D.1): `proposition_17_F_2_regular` |
| Proof of 17.F.2, p. 609 | `p'' = αp + (1-α)p'` satisfies (i); `p·z(p'') ≤ 0` or `p'·z(p'') ≤ 0`; the weak axiom forces `z(p'') = z(p)` (or `z(p')`) | `wa_combo_eq` |
| Footnote 39, p. 609 | `z(p'') ∈ {z(p), z(p')}` and continuity give `z(p) = z(p')`: all equilibria have the same aggregate consumption and production | `footnote_17_39` (intermediate value theorem) |
| p. 609 | Proportional endowments `ωᵢ = αᵢω̄`: wealth `αᵢ` after normalizing `p·ω̄ = 1`; then the weak axiom is restrictive but not implausible (Section 4.C) | listed (verbal) |
| Footnote 40, p. 609 | References (Hildenbrand 1994) | listed (verbal) |
| pp. 609-610 | Nonproportional endowments can destroy the weak axiom even with homothetic preferences | listed (verbal); made precise by (17.F.2), Example 17.F.1, Exercise 17.F.3 |
| Footnote 41, p. 610 | With free endowments homothetic preferences impose no restriction (Mantel 1976) | listed (verbal; cf. Section 17.E) |
| (17.F.1), p. 610 | Sufficient: `dp·Dz(p) dp < 0` whenever `dp·z(p) = 0` and `dp` not proportional to `p` ("it can be shown") | `eq_17_F_1_sufficient` (homogeneity, Walras' law, differentiability on `ℝ^L_{++}`), `wad_not_proportional`, `wad_deriv_neg`, `wad_hasDerivAt_dot`; instance (one Cobb-Douglas consumer) `wadZ`, `wadZ_props`, `wadZ_differentiableAt`, `wadZ_condition`, `eq_17_F_1_instance` |
| p. 610, footnote 42 | With the weak inequality, (17.F.1) is necessary: `Δp·Δz ≤ 0`, then the differential limit | `footnote_17_42`, `wad_deriv_nonpos` |
| p. 610 | Homothetic preferences: `D_{wᵢ}xᵢ = xᵢ/(p·ωᵢ)` | `homothetic_wealthJacobian` |
| (17.F.2), p. 610 | `Dz(p) = ∑ᵢSᵢ - ∑ᵢ(1/p·ωᵢ)[xᵢ - (p·ωᵢ/p·ω̄)x̄][…]ᵀ + ∑ᵢ(1/p·ωᵢ)[xᵢ - (p·ωᵢ/p·ω̄)x̄][ωᵢ - (p·ωᵢ/p·ω̄)ω̄]ᵀ - (1/p·ω̄)x̄z(p)ᵀ` | `eq_17_F_2` (from (17.E.3), `eq_17_E_3`), `eq_17_F_2_identity`, `wadMatrix` |
| p. 610 | For `dp·z(p) = 0`: the substitution and variance terms are `≤ 0`, the fourth term is null, the third (covariance) term is ambiguous | `eq_17_F_2_terms`, `wad_quad_vecMulVec`; the ambiguity: Example 17.F.1, Exercise 17.F.3 |
| p. 610 | Interpretation: positive association of consumption and endowment per dollar | listed (verbal) |
| Footnote 43, p. 610 | The covariance term cannot be wrong if the `xᵢ` or the `ωᵢ` are collinear | Exercise 17.F.1 below |
| Example 17.F.1, p. 611 | Two consumers trading goods 1-2 and 3-4; if both excess demands are nonzero at `p'`, the weak axiom fails, via `q = (p'₁, p'₂, αp̂₃, αp̂₄)`, `q' = (αp̂₁, αp̂₂, p'₃, p'₄)` | `example_17_F_1`, `TwoBlockED`, `ex17F1_dir` (existence of `p̂`), `ex17F1_dot4`; verification: `exercise_17_F_2` |
| Example 17.F.1, p. 611 | "compatible with homotheticity and even with gross substitution" | homotheticity: instance `ex17F1Z` (two Cobb-Douglas consumers, `ex17F1Z1`, `ex17F1Z2`, `ex17F1Z1_eq_cd`, `ex17F1Z_twoBlock`, `ex17F1Z_not_weakAxiom`); weak gross substitutes `ex17F1Z_weakGS`, `ex17F1_coord_mono`; strict gross substitutes impossible: `example_17_F_1_not_GS`, `ex17F1Z_not_GS` (corrections 24) |
| Footnote 44, p. 611 | The example is a case of positive association | listed (verbal) |
| p. 611 | Motivation: gross versus compensated substitutes | listed (verbal) |
| Definition 17.F.2, p. 611 | Gross substitute property | `GrossSubstitute` |
| pp. 611-612 | With homogeneity, raising `pₗ` lowers `zₗ` (`p̄ = αp`, raising the other prices one at a time) | `gs_own_price`, `gs_path`, `gs_path_le`; needs `L ≥ 2`: `gs_own_price_one_good` (corrections 27) |
| p. 612 | Differential version: `∂zₖ/∂pₗ > 0` for `k ≠ ℓ` | necessary only weakly: `gs_partial_nonneg`; sufficient: `gs_of_partial_pos`; `> 0` can fail: `gs_partial_not_pos`, `gsCubicZ`, `gsCubicZ_props`, `gsCubic_h_strictMono`, `gsCubic_h_pos` (corrections 26) |
| p. 612 | With homogeneity, `Dz(p)p = 0` makes the diagonal of `Dz(p)` negative | `gs_diag_neg` |
| p. 612 | Weak gross substitution | `WeakGrossSubstitute`, `GrossSubstitute.weak` |
| Footnote 45, p. 612 | `c - (I - A)α` (input-output) and `g(α) - α` (`g` increasing) have the weak GS property; no homogeneity or Walras' law there | `footnote_17_45_io`, `footnote_17_45_fixed`; the remark on homogeneity/Walras listed (verbal) |
| Figure 17.F.2, p. 612 | Offer curve of a GS excess demand (`L = 2`): as `p₁` rises, `z₁` falls and `z₂` rises | `gs_own_price` and `GrossSubstitute`; picture listed (graphical) |
| p. 612 | The GS property is additive across excess demand functions | `GrossSubstitute.add`, `WeakGrossSubstitute.add`, `GrossSubstitute.sum` |
| Example 17.F.2, p. 612 | `uᵢ = ∑ₗ uₗᵢ(xₗᵢ)` with `-xu''/u' < 1` gives GS for any endowments; CES `0 < ρ < 1` satisfies it | Exercise 17.F.5 below |
| Example 17.F.2, p. 612 | Limits `ρ → 1`, `ρ → 0` are linear and Cobb-Douglas (Exercise 3.C.6) | listed; Chapter 3 `exercise_3_C_6a`, `exercise_3_C_6b`, `exercise_3_C_6c` |
| Example 17.F.2, pp. 612-613 | Cobb-Douglas is borderline: `zₗ = αₗ(p·ω)/pₗ - ωₗ` responds to `pₖ` iff `ωₖ > 0` | `example_17_F_2_cd`; GS when `ω ≫ 0`: `cd1_grossSubstitute` |
| Footnote 46, p. 613 | Grandmont (1992) | listed (verbal) |
| Proposition 17.F.3, p. 613 | GS aggregate excess demand has at most one (normalized) exchange equilibrium | `proposition_17_F_3` (`z(p) = z(p')` only for proportional `p, p'`), `proposition_17_F_3_norm` |
| Proof of 17.F.3, p. 613 | Scale so `p' ≥ p`, `pₗ = p'ₗ`; lower the other prices one at a time; "`zₗ(p) > zₗ(p')`" | `gs_path` (the inequality is `zₗ(p) < zₗ(p')`); printed sign refuted: `proposition_17_F_3_printed_sign` (corrections 25) |
| p. 613, small type | GS in production economies is limited; reduction to an exchange of factors may help | listed (verbal); Exercise 17.F.6 |
| Footnote 47, p. 613 | References | listed (verbal) |
| p. 613 | The weak axiom does not imply GS | `wa_not_gs` |
| p. 613, footnote 48 | GS does not imply the weak axiom; hence with constant returns GS consumers do not give uniqueness | `gs_not_weakAxiom`, `gsNotWAZ`, `gsNotWAZ_GS`, `gsNotWAZ_walras`, `footnote_17_48` (Example 17.F.1 itself is only weakly GS: corrections 24) |
| (17.F.3), p. 613 | GS: `z(p) = 0`, `z(p') ≠ 0` imply `p·z(p') > 0` ("we shall not prove") | `eq_17_F_3` (every `L`), `RevealedEqmProperty`, `gs_max_ratio_nonpos`, `gs_top_value_neg`, `gs_abel` |
| pp. 613-614, Figure 17.F.3 | (17.F.3) is the weak axiom restricted to an equilibrium `p`; the offer curve lies above the hyperplane with normal `p` | `RevealedEqmProperty`; picture listed (graphical) |
| p. 614 | (17.F.3) implies a convex equilibrium set (Exercise 17.F.8) | `exercise_17_F_8` |
| p. 614 | (17.F.3) holds in the weak axiom case and in the no-trade case | `wa_eq_17_F_3`; `notrade_eq_17_F_3` with instance `sqrt1_noTrade`, `sqrt1Economy`, `sqrt1_demand` |
| p. 614 | Differentiable case: `p·Dz(p) = 0`, `Dz(p)p = 0` at an equilibrium | `gs_row_col` (from `euler_fderiv`, `walras_fderiv`) |
| Proposition 17.F.4, p. 614 | `z(p) = 0` and the GS sign pattern give `dp·Dz(p) dp < 0` for `dp ≠ 0` not proportional to `p` | `proposition_17_F_4`, `gs_quad_identity` (`v·Av = -½∑ aₖₗpₖpₗ(vₖ/pₖ - vₗ/pₗ)²`), `gs_dot_apply` |
| p. 614 | "This is summarized in Proposition 12.F.4" | misprint for 17.F.4 (corrections 29) |
| p. 614 | Uniqueness from Pareto optimality; Exercise 17.F.9 allows production | listed (verbal); Exercise 17.F.9 |
| Proposition 17.F.5, pp. 614-615 | If the endowment allocation is an equilibrium allocation (no trade), it is the unique equilibrium allocation | `proposition_17_F_5` (strict convexity suffices), `up_mid_mem`, `up_mid_gt`; instance `sqrt1_eqm` (corrections 31) |
| p. 615 | Index analysis: sign uniformity of the Jacobian determinant across equilibria forces uniqueness | listed (verbal); index theorem: `proposition_17_D_2_two_goods` (`L = 2`) |
| p. 615 | In the WA and GS cases `Dz(p)` is negative semidefinite at every equilibrium | WA: `wa_nsd_at_eqm`; GS: `gs_nsd_at_eqm`; (17.F.3): `exercise_17_F_10` |
| p. 615 | If moreover `rank Dz(p) = L - 1`, the index is `+1` (Exercise 17.F.11), so regular economies have a unique equilibrium | `exercise_17_F_11_index` (with the WA: `wa_nsd_at_eqm`; with GS: `gs_nsd_at_eqm`); uniqueness itself, without the index: WA `proposition_17_F_2_regular`, GS `proposition_17_F_3_norm` |
| p. 615 | Index analysis used to establish nonuniqueness (Varian 1977) | listed (verbal) |
| Example 17.F.3, p. 615 | Two one-consumer countries, `uᵢ = x_{Hi} - x_{Fi}^ρ`, `-1 < ρ < 0`; symmetric equilibrium `p = (1, 1)`; a negative index at the symmetric equilibrium implies an asymmetric equilibrium; the index is negative if home-biased wealth effects make country 1's demand for good 1 rise with `p₁` by more than country 2's falls | the economy `tcEconomy`; demand `exercise_17_F_13_demand`; symmetric equilibrium `exercise_17_F_13_eqm`; its index is `+1` for every `-1 < ρ < 0` (country 1's demand does rise, but less than country 2's falls): `exercise_17_F_13_index` (corrections 34); the index argument for `L = 2`: `example_17_F_3_index`, with an instance having an index `-1` equilibrium `ex17F3_index`, `example_17_F_3_index_instance`, `ex17F3g`, `ex17F3Z`, `ex17F3Z_isStandard`, `ex17F3g_hasDerivAt` |
| Footnote 49, p. 615 | Excess demand is not differentiable where demand hits the boundary; generically not at equilibria | listed (verbal) |

## Exercises 17.F

| Source | Claim | Lean |
| --- | --- | --- |
| Exercise 17.F.1, p. 645 | (17.F.2) gives a negative semidefinite `Dz(p)` if endowments, or consumptions, are proportional | on `dp·z(p) = 0` (the sense of (17.F.1)): `exercise_17_F_1a` (endowments), `exercise_17_F_1b` (consumptions), `wad_nsd_of_cov_zero`; unrestricted semidefiniteness fails: `exercise_17_F_1_unrestricted` (corrections 28) |
| Exercise 17.F.2, p. 645 | The verification of Example 17.F.1 for `α` large | `exercise_17_F_2`; conclusion `example_17_F_1` |
| Exercise 17.F.3, p. 645 | Four goods; consumer 1 spends all wealth on good 3, consumer 2 on good 4; endowments violating the weak axiom | `exercise_17_F_3` (`ω₁ = (1, 0, 0, 0)`, `ω₂ = (0, 1, 0, 0)`, `p = (1, 1, 1, 1)`, `p' = (1, 3, 2, 2)`), `cornerED` |
| Exercise 17.F.4, p. 645 | Each consumer spends all wealth on one good: aggregate excess demand has the weak GS property | `exercise_17_F_4` (`ωᵢ ≥ 0`) |
| Exercise 17.F.5, p. 645 | Missing steps of Example 17.F.2: separable utilities with `-xu''/u' < 1` give GS; CES `0 < ρ < 1` | `exercise_17_F_5_foc`, `exercise_17_F_5` (interior demand), `SepFOC`, `ex17F5_demand_eq`, `ex17F5_tangent`, `ex17F5_tangent_strict`, `ex17F5_rra`; CES: `exercise_17_F_5_ces`, `ex17F5_cesU`, `ex17F5_cesDemand`, `ex17F5_cesED`, `ex17F5_ces_rra`, `ex17F5_ces_foc`, `ex17F5_ces_demand`, `ex17F5_ces_transform`; Cobb-Douglas: `example_17_F_2_cd` (corrections 32) |
| Exercise 17.F.6, p. 645 | Two goods, two factors, Cobb-Douglas constant returns, normal GS final demand: the induced factor excess demand is GS; unique equilibrium | the induced economy `fgeInduced` (`fgeCost`, Shephard requirements, `fgeInduced_eq`, `fgeCost_ratio`); proved for homothetic consumers (`fgeDemand`, `fgeDemand_gs_normal`): GS and homogeneity `exercise_17_F_6_homothetic` (`fge_term_mono`, `fge_weight`), uniqueness `exercise_17_F_6_unique`, instance `fgeShare_instance`; FALSE for general normal GS demand: `exercise_17_F_6_counter` (`fgeInducedGen`, `fgeInducedGen_homothetic`, `fgeLux`, `fgeLux_walras`, `fgeLux_hom`, `fgeLux_normal`, `fgeLux_gs`, `fgeLux_slutsky`) (corrections 33) |
| Exercise 17.F.7, p. 646 | Prove (17.F.3) for `L = 2` | `exercise_17_F_7` (instance of `eq_17_F_3`, proved for every `L`) |
| Exercise 17.F.8, p. 646 | (17.F.3) implies that `{p : z(p) = 0}` is convex | `exercise_17_F_8` (with Walras' law) |
| Exercise 17.F.9, p. 646 | Constant returns `Y`; equilibrium consumptions attainable without trade (`xᵢ - ωᵢ ∈ Y`) are the only equilibrium consumptions | `exercise_17_F_9`; instance `sqrt1_cr_eqm` |
| Exercise 17.F.10, p. 646 | (17.F.3) implies `Dz(p)` negative semidefinite at an equilibrium | `exercise_17_F_10` (with Walras' law) |
| Exercise 17.F.11, p. 646 | `z(p) = 0`, `rank Dz(p) = L - 1`, `Dz(p)` negative semidefinite: every principal `(L - 1) × (L - 1)` minor has sign `(-1)^{L-1}` (hint: nonsingular by Section M.D; consider `Dz(p) - αI`) | `exercise_17_F_11` (matrix form `isd_minor_sign`; nonsingularity `footnote_17_14`; sign by the homotopy `isd_det_sign_of_nsd`, `isd_quad_submatrix`, `isd_mat_eqm`); index `+1`: `exercise_17_F_11_index`, `isd_index_of_pos`; instance `isd_instance` |
| Exercise 17.F.12, p. 646 | `z(p) = 0` and the GS sign pattern: each principal `(L - 1) × (L - 1)` submatrix has a negative dominant diagonal and is negative definite | `exercise_17_F_12` (matrix form `isd_gs_minor`, `isd_gs_quad_neg`, `isd_not_prop`); Definition M.D.2: `NegDominantDiagonal` |
| Exercise 17.F.13, p. 646 | The missing computation of Example 17.F.3 | `exercise_17_F_13_demand` (`tc_optimal`, `tc_tangent`, `tcX`, `tcX_foc`, `tcX_pos`), `exercise_17_F_13_eqm` (`tcX_one_lt`), `exercise_17_F_13_index` (`tc_excessDemand_near`, `tc_hasDerivAt`): the index is `+1` (corrections 34) |
| Exercise 17.F.14(a), p. 646 | Cobb-Douglas `∏ vₗ^{αₗ}`, `∑ α ≤ 1`: any two inputs are complements at any `v` | `exercise_17_F_14a` (`∂²f/∂vₗ∂vₗ' = αₗαₗ'f/(vₗvₗ')`, `v ≫ 0`; any `α ≫ 0`), `secondPartial`, `InputComplements`, `cdProduction`, `cmpH`, `cmpD`, `cmp_hasFDerivAt`, `cdProduction_eq`, `cmpH_div` |
| Exercise 17.F.14(b), p. 646 | Constant returns: for every `ℓ` some `ℓ'` is a complement to `ℓ` | false as printed: `exercise_17_F_14b_counter` (`cmpLinear`); corrected (if `∂²f/∂vₗ² < 0`): `exercise_17_F_14b`, from `∑ₗ' vₗ' ∂²f/∂vₗ∂vₗ' = 0` (`cmp_fderiv_smul`, `cmp_apply_eq_sum`) (corrections 38) |
| Exercise 17.F.14(c), p. 646 | Strictly concave `f`, all inputs complements: `∂vₗ/∂p₁ > 0`, `∂vₗ/∂pₗ < 0`, `∂vₗ/∂pₗ' < 0` | `exercise_17_F_14c` (negative definite Hessian), `cmp_inv_neg`, instance `cmp_inv_neg_instance` (corrections 38) |
| Exercise 17.F.14(d), p. 646 | Implications for uniqueness theorems based on gross substitution | listed (verbal); by (c) the input demands are gross complements |
| Exercise 17.F.15, p. 646 | One consumer, ad valorem taxes, lump-sum rebate: define the equilibrium; unique with a Leontief technology and normal goods; normality is indispensable (two commodities) | definition `IsLeontiefTaxEqm` (`taxProducerPrice`, `taxConsumerPrice`, `leontiefPlan`, `taxProfit_zero`); uniqueness `exercise_17_F_15`; example `exercise_17_F_15_normality` (`taxPath`), generated by continuous, monotone, convex preferences: `exercise_17_F_15_preferences` (`fn15U`, `fn15U_demand`, `fn15U_ge_iff`, `taxPath_zero`, `taxPath_comb`, `fn15U_continuous`, `fn15U_monotone`, `fn15U_quasiconcave`) (corrections 40) |
| Exercise 17.F.16, p. 646 | `g` on `[0, r]^N`, `g(0) ≫ 0`, `g(r, …, r) ≪ 0`; no Walras' law, homogeneity or continuity | `sgsBox`, `BoxGrossSubstitute` |
| Exercise 17.F.16(a), p. 647 | SGS implies GS | `StrongGrossSubstitute`, `exercise_17_F_16a` |
| Exercise 17.F.16(b), p. 647 | GS does not imply SGS; `C¹` and GS imply SGS | `exercise_17_F_16b_counter` (`sgsStep`, `sgsCounter`); `exercise_17_F_16b` (`g` `C¹` on `ℝ^N`; `sgs_chain`, `sgsPath`, `sgs_own`, `sgs_update_eq`) (corrections 39) |
| Exercise 17.F.16(c), p. 647 | SGS: an equilibrium exists (Tarski, Section M.I); illustrate for `N = 1` | `exercise_17_F_16c`, `sgs_tarski`, `sgs_map`, `sgs_fixed_iff`, `sgs_le_iff`, `sgs_ge_iff`, `sgs_extremal`; illustration listed (graphical) |
| Exercise 17.F.16(d), p. 647 | An example with `N = 2` and several equilibria | `exercise_17_F_16d` (`sgsTwo`, `sgsPsi`, `sgsPsi_mono`; equilibria `(1, 1)`, `(2, 2)`, `(3, 3)`) |
| Exercise 17.F.16(e), p. 647 | Two equilibria have an equilibrium above both and one below both | `exercise_17_F_16e` |
| Exercise 17.F.16(f), p. 647 | Maximal and minimal equilibria | `exercise_17_F_16f` |
| Exercise 17.F.16(g), p. 647 | `Dg(p)` with a negative dominant diagonal at every equilibrium: uniqueness ("perhaps nonrigorously") | `N = 1`: `exercise_17_F_16g_one`; OPEN for `N ≥ 2` (the book's argument is the index theorem in `N` dimensions, not available) |
| Exercise 17.F.16(h), p. 647 | The first `N` excess demands of an `(N + 1)`-good GS economy: apply (g) | `exercise_17_F_16h` (`Dĝ(p̂)p̂ ≪ 0` with positive numeraire cross effects; uniqueness via Proposition 17.F.3) (corrections 39) |
| Exercise 17.F.17, p. 647 | Becker-Grandmont: random uniform choice on the budget line (`L = 2`) gives a Cobb-Douglas average excess demand | `exercise_17_F_17`, `beckerLine`, `beckerLine_props`, `beckerMean`, `beckerMean_eq` (corrections 43) |

## 17.G Comparative statics analysis

| Source | Claim | Lean |
| --- | --- | --- |
| p. 616 | Comparative statics; the system `ẑ(p; q) = 0`, `q ∈ ℝ^N`, `p_L = 1` | listed (verbal); the system is a map `(Fin n → ℝ) × (Fin N → ℝ) → (Fin n → ℝ)` throughout |
| p. 616 | Multiplicity: focus on local effects near a regular `p̄`, by the implicit function theorem (Section M.E) | Chapter 3's `theorem_M_E_1` |
| (17.G.1), p. 616 | `Dp(q̄) = -[D_p ẑ(p̄; q̄)]⁻¹ D_q ẑ(p̄; q̄)` | `eq_17_G_1` (strictly differentiable `ẑ`, regular); any differentiable local solution: `eq_17_G_1_any` |
| Footnote 50, p. 616 | `D_p ẑ` is `D_p z` without its last row and column | `normED_hasFDerivAt` (17.D) |
| p. 616 | Proposition 17.E.2 suggests "anything goes" for comparative statics | listed (verbal); made precise by Proposition 17.G.1 |
| p. 616 | `q = ω̂₁`: with strict normality of consumer 1's demand, `rank Dp(ω̂₁) = L - 1` (Exercise 17.G.1) | `exercise_17_G_1` |
| Proposition 17.G.1, p. 617 | Given `p̄`, `ω̂₁` and a nonsingular `B`, there is an economy of `L + 1` consumers with `ẑ(p̄; ω̂₁) = 0`, regular, `Dp(ω̂₁) = B` | `proposition_17_G_1` (`cseEconomy`, `cseZ`, `cse_excessDemand`, `cseG`, `cseG_eq`, `cseG_contDiffAt`, `cseG_omega`, `cseG_fderiv_inr`, `cseM`, `cseM_mulVec`, `cseM_det`, `cse_hasStrictFDerivAt_normPrice`, `cseCLM`, `cse_toMatrix'_eq`) (corrections 36) |
| Proof of 17.G.1, (17.G.2), p. 617 | First consumer with `D_{ω̂₁} ẑ₁` nonsingular; `L` consumers with aggregate `-ẑ₁(p̄; ω̂₁)` and `D_p ẑ = -D_{ω̂₁} ẑ₁ B⁻¹`; Proposition 17.E.2 restricts only the full `L × L` matrix | the bordered matrix `cseA`, `cseTop`, `cseA_mulVec`, `cseA_vecMul`, `cseA_trunc`, `cseA_castSucc`, `cseA_last`, `cseTop_castSucc`, `cseTop_last`, `cseTop_dot`; `proposition_17_E_2` (strict derivative) |
| p. 617, small type | Prior restrictions with nonnegative consumption and endowments (Brown and Matzkin 1993) | listed (verbal) |
| p. 617 | Intuitive comparative statics need strong conditions (wealth effects, substitutability) | listed (verbal) |
| Proposition 17.G.2, p. 617 | `D_q ẑ` (read `D_p ẑ`) negative definite implies `(D_q ẑ dq)·(Dp(q̄) dq) ≥ 0` (17.G.3) | `proposition_17_G_2`, with existence `proposition_17_G_2_exists`; instance `proposition_17_G_2_instance` (corrections 35) |
| Footnote 51, p. 617 | The condition does not depend on which good is labeled `L` (Section M.D) | `footnote_17_51`, `isd_nd_iff` (Theorem M.D.4(ii)-(iii)), `isd_quad_shift`, `isd_eq_insertNth` |
| Proof of 17.G.2, p. 618 | The inverse of a negative definite matrix is negative definite | `cs_inv_nd`, `cs_det_ne_zero_of_nd` |
| p. 618 | The weak axiom gives negative semidefiniteness of `D_p ẑ`; 17.G.2 is a small strengthening; shocks and price changes form an acute angle | `wa_nsd_at_eqm` (17.F); the angle is (17.G.3); rest listed (verbal) |
| p. 618, footnote 52 | A shock lowering only the excess demand of good 1 lowers its equilibrium price | `cs_single_market`; footnote 52 (Walras' law moves good `L`) listed (verbal) |
| p. 618 | This does not say that raising `ω₁₁` lowers `p₁` (Exercise 17.G.2) | `exercise_17_G_2` |
| Proposition 17.G.3, p. 618 | `D_p z` with negative diagonal and positive off-diagonal entries: `[D_p ẑ]⁻¹` has all entries negative | `proposition_17_G_3`, `cs_inv_neg`, `cs_neg_of_nonneg` (corrections 37) |
| Proof of 17.G.3, p. 618 | Homogeneity gives `D_p ẑ p̂ ≪ 0`; `A = (1/r)D_p ẑ + I` productive; `[I - A]⁻¹ ≫ 0` (Proposition 5.AA.1) | `D_p ẑ p̂ ≪ 0`: inside `proposition_17_G_3` (from `euler_fderiv`); the productive-matrix route is replaced by `cs_neg_of_nonneg` (corrections 37) |
| pp. 618-619 | With GS, `D_q ẑ dq ≪ 0` implies `Dp(q̄) dq ≪ 0`; a lower endowment of good `L` (normal demand) lowers the prices of goods `1, …, L - 1` | `cs_gs_shock`; the endowment application listed (verbal) |
| p. 619 | The assumptions of 17.G.3 are stronger than those of 17.G.2: `D_p ẑ` negative definite (Proposition 17.F.4 with `dp_L = 0`) | `exercise_17_F_12`, `isd_gs_minor` |
| Footnote 53, p. 619 | Nonlocal shocks: along the homotopy path `pₗ(q̂) - pₗ(q̄) = ∫ ∂pₗ/∂t < 0` | `footnote_17_53` |
| p. 619 | The homotopy `ẑ(·, t) = (1 - t)ẑ(·; q̄) + tẑ(·; q̂)`; follow the solution set `E` from `(0, p̄)` | `csHomotopy`, `csHomotopy_ends`; path following listed (verbal) |
| Footnotes 54-56, p. 619 | Numerical path following; small shocks give a homotopy-independent `p̂`; with multiple equilibria the result may depend on the homotopy | listed (verbal) |
| Figure 17.G.1, p. 620 | Comparative statics in the large: (a) a single path, (b), (c) turning points | listed (graphical) |
| p. 620, footnote 57 | No natural continuation; reversing `t`; the lack of a theory of equilibrium selection | listed (verbal) |

## Exercises 17.G

| Source | Claim | Lean |
| --- | --- | --- |
| Exercise 17.G.1, p. 647 | Strictly normal demand of consumer 1: `rank D_{ω̂₁} ẑ₁ = L - 1` and `rank Dp(ω̂₁) = L - 1` | derivative `exercise_17_G_1_deriv`; nonsingularity `exercise_17_G_1_det` (with `exercise_17_G_1_walras`); `rank Dp`: `exercise_17_G_1_rank`; assembled for Proposition 17.G.1's economy: `exercise_17_G_1` (corrections 42) |
| Exercise 17.G.2, p. 647 | Economies with `D_p ẑ` negative definite and `∂p₁/∂ω₁₁ > 0` | `exercise_17_G_2` (`L = 3`, `ex17G2B`, `ex17G2N`); impossible with two goods: `exercise_17_G_2_two_goods` (corrections 41) |
| Exercise 17.G.3, p. 648 | Two SGS functions, `ĝ ≥ g`: `p̂^min ≥ p^min`, `p̂^max ≥ p^max`; graph for `N = 1` | `exercise_17_G_3` (no continuity or uniqueness needed); graph listed (graphical) |

## 17.H Tâtonnement stability

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 620-621, introduction; footnote 58 | Economics centres on equilibrium; dynamics, the plethora of disequilibrium models; reference to Hahn (1982) | listed (verbal) |
| (17.H.1), p. 621 | Price tâtonnement `dpₗ/dt = cₗ zₗ(p)`, `cₗ > 0` | `tatField`, `IsTatPath` (trajectory on `t ≥ 0`, `p(t) ≫ 0`, derivative one-sided at `0`), `tat_coord`, `tat_continuousOn` |
| (17.H.1), p. 621 (taken for granted) | Trajectories exist | `tat_exists` (for `z` of class `C¹` on `ℝ^L_{++}` with Walras' law and small prices rising; Picard-Lindelöf `tex_picard`, invariance `tex_piece`, concatenation `tex_glue`, `tex_coord_le`); instance: one Cobb-Douglas consumer, any `c ≫ 0`, any `p(0) ≫ 0`: `cd1_tat_exists` (`cd1ED_contDiffOn`, `cd1ED_repel`, `cd1ED_eqm`) |
| p. 621, interpretation; footnote 59 | Who sets prices, the law of one price, fictional time; Walras, Barone, Lange | listed (verbal) |
| p. 621 | With two goods, `p₁(t)/p₂(t)` increases at `t` iff `z₁(p₁(t)/p₂(t), 1) > 0`, whatever the absolute levels | `footnote_17_60`, `tat_two_ratio_increases_iff`, `ttgFactor`, `ttgFactor_pos`, `ttg_hom`, `ttg_walras` |
| p. 622, footnote 60 | `dpₗ/dt` depends only on relative prices; the change in `p₁/p₂` depends on the ratio and on the absolute levels | `footnote_17_60` (`d(p₁/p₂)/dt = z₁(p₁/p₂, 1)(c₁p₂² + c₂p₁²)/p₂³`), `footnote_17_60_levels` (the factor scales as `1/α`) |
| Figure 17.H.1, p. 622 | Two-good trajectories: arrows by the sign of `z₁(p₁/p₂, 1)` | `tat_two_ratio_increases_iff`, `tat_two_locally_stable`, `tat_two_locally_totally_unstable`; the picture listed (graphical) |
| p. 621-622, property (a) | A regular equilibrium is locally stable or locally totally unstable according to the sign of the slope of excess demand, i.e. its index | `tat_two_locally_stable` (slope `< 0`), `tat_two_locally_totally_unstable` (slope `> 0`), via the index: `tat_two_stable_of_index`, `tat_two_unstable_of_index` (`itgSgn_neg_iff`, `itgSgn_pos_iff`, `ttg_quad_bound`, `ttg_factor_lower`) (corrections 46) |
| p. 622, property (b) | System stability with two goods: from any initial position relative prices converge to some equilibrium | unique equilibrium: `footnote_17_62_two_goods`; any number of equilibria: `section_17_H_property_b` (one-dimensional argument: `ctg_fall`, `ctg_rise`, `ctg_plateau`, `ctg_no_peak`, `ctg_monotone`, `ctg_converges`) (corrections 46) |
| p. 622 | With `L > 2` neither (a) nor (b) generalizes; any excess demand flow is possible beyond boundary behaviour (Propositions 17.E.2-17.E.3) | listed (verbal); the saddle case: `saddle2`, `figure_17_H_2_index` |
| p. 622, display | `S = {p ≫ 0 : ∑ pₗ² = 1}` is invariant for `cₗ = 1`: `d(∑ pₗ²)/dt = 2 p·z(p) = 0` | `tat_sphere_invariant`; general speeds `∑ pₗ²/cₗ` constant: `tat_wNormSq_const` (`tat_hasDeriv_wNormSq`, `tatField_hasDeriv_wNormSq`, `wNormSq`) |
| Figure 17.H.2, p. 623 | Trajectories for `L = 3`: locally stable index `+1`, locally totally unstable index `+1`, saddle index `-1`; inward near the boundary | `figure_17_H_2_index` (with `rh2`, `rh2_pos`, `saddle2`); the picture listed (graphical) |
| p. 623, footnote 61 | No comfort from convergence to a limit cycle | listed (verbal) |
| p. 623 | Global stability for the weak axiom, gross substitute and no-trade cases: `p*·z(p) > 0` for `p` not proportional to `p*` | `tat_global_stability_gs`, `tat_global_stability_wa`, common form `tat_global_stability_revealed` (no-trade input: `notrade_eq_17_F_3`); inputs `eq_17_F_3`, `wa_eq_17_F_3`, `proposition_17_F_3` |
| p. 623, footnote 62 | Uniqueness does not imply stability, except for `L = 2` | `L = 2`: `footnote_17_62_two_goods` (`ttg_sign_of_unique`); `L = 3`: Scarf's economy, `footnote_17_62_three_goods` (`scarfEconomy`, `scarf_demand_0`/`_1`/`_2`, `scarf_excessDemand`, `scarfZ_props`, `scarfZ_eqm_iff`, `scarf_prod_const`, `scarf_tat_exists`, `scarf_not_converge`; the boundary condition fails, `scarfZ_not_boundary`) (corrections 74) |
| p. 623, footnote 63 | A proof specific to gross substitutes: Exercise 17.H.1 | `exercise_17_H_1a`, `exercise_17_H_1b` |
| Proposition 17.H.1, p. 623 | `z(p*) = 0` and `p*·z(p) > 0` for `p` not proportional to `p*` ⟹ relative prices of every trajectory converge to those of `p*` | `proposition_17_H_1` (convergence to `λp*`), `proposition_17_H_1_relative`; Lyapunov core `tat_lyapunov_core`, compactness `tat_unif_pos`, `tat_g_nonneg`, `tat_monotoneOn`; instance `cd1_tat_converges` (corrections 44) |
| p. 624, proof display | `df(p(t))/dt = -p*·z(p(t)) ≤ 0`, strict iff `p(t)` not proportional to `p*` | `proposition_17_H_1_deriv` (the derivative is `-2p*·z`; corrections 44), `tat_hasDeriv_wInner` |
| p. 624, proof | `p(t)` monotonically approaches every `αp*` | `proposition_17_H_1_monotone` |
| p. 624, proof | The rate of approach goes to zero only if `p(t)` becomes nearly proportional to `p*` | `tat_unif_pos`, `tat_lyapunov_core` |
| p. 624, footnote 64 | Lyapunov functions | the function `wNormSq c (p - λp*)` of `tat_lyapunov_core`; definition listed (verbal) |
| p. 624 | Normalized dynamics `p_L = 1`, `ẑ`; local stability: `‖p(0) - p*‖ < ε ⟹ p(t) → p*` | `IsNormTatPath`, `NormLocallyStable` |
| p. 624 | Near a regular `p*` the behaviour is controlled by the linearization `CDẑ(p*)` | listed (verbal); OPEN in general (Hartman-Grobman) |
| p. 624 | `p*` locally stable iff all eigenvalues of `CDẑ(p*)` have negative real parts | "only if" FALSE: `tat_eigen_counterexample` (`cxZ`, `cxF`, `cxJ`, `cxZ_props`, `normED_cxZ`, `cxF_hasFDerivAt`, `cxZ_regular`, `cxJ_eigen`, `cxZ_converges`); "if": `n = 1` in `tat_two_locally_stable`, negative definite `Dẑ` in `tat_local_stable_of_negDef`, general: OPEN (Lyapunov matrix equation) (corrections 47) |
| p. 624 | `p*` locally stable for all speeds if `Dẑ(p*)` is negative definite | `tat_local_stable_of_negDef` (`tat_negDef_uniform`, `tat_dot_le`, `tat_exp_decay`, `tat_norm_lt_of_wNormSq`, `tat_wNormSq_le`); instance `tat_local_stable_cd1` |
| p. 624, footnote 65 | How could we know the speeds? | listed (verbal) |
| p. 624, footnote 66 | The property of Proposition 17.H.1 implies negative semidefiniteness of `Dẑ(p*)` | `footnote_17_66` |
| p. 624 | Tâtonnement constrains each price to react only to its own excess demand | listed (verbal) |
| (17.H.2), p. 624 | Newton's method `dp/dt = -λ[Dẑ(p)]⁻¹ẑ(p)`, i.e. `Dẑ(p)(dp/dt) = -λẑ(p)` | `IsNewtonPath`, `newton_exp` (`ẑ(p(t)) = e^{-λt}ẑ(p(0))`), instance `newton_instance` |
| p. 625 | If `Dẑ(p*)` is nonsingular, (17.H.2) restores equilibrium after a small disturbance | `newton_restores` (corrections 48) |
| p. 625 | Informational contrast between tâtonnement and Newton; Smale (1976), Saari-Simon (1978) | listed (verbal) |
| p. 625, quantity tâtonnement; footnotes 67-68 | Quantities out of equilibrium, prices the short-run equilibrium prices `p(y)` of `{y} - ℝ^L_+` | listed (verbal); single consumer: `p(y) = ∇u(y + ω)` (`margUtil`, `fderiv_eq_margUtil_dot`), long-run equilibrium `IsLongRunEqm` |
| Definition 17.H.1, p. 625 | Admissible trajectory: `p(y(t))·dy/dt ≥ 0`, equality only at profit maximization | `IsAdmissible` |
| p. 625, footnotes 69-70 | Real time; adaptive behaviour; Marshallian vs Walrasian dynamics | listed (verbal) |
| Proposition 17.H.2, p. 626 | One strictly convex consumer: every admissible trajectory converges to the unique equilibrium | FALSE as printed: `proposition_17_H_2_counter` (`qaU`, `qaY`, `qaω`, `qaPath`, `qaPath'`, `qaU_strictConcave`, `qaY_props`, `qa_eqm`); corrected (uniformly admissible): `proposition_17_H_2`, instance `proposition_17_H_2_instance` (`qaPathB`, `qaPathB'`); uniqueness `qa_unique` (corrections 49) |
| p. 626, proof display | `du(y(t) + ω)/dt = ∇u·dy/dt = μ p(y(t))·dy/dt > 0` except at equilibrium | `qa_hasDeriv_utility`, `proposition_17_H_2_utility`, `concave_le_fderiv` |
| Figure 17.H.3, p. 626 | Quantity tâtonnement along the frontier of `Y` | listed (graphical) |
| p. 626 | The single consumer may be a positive representative consumer | listed (verbal) |

## Exercises 17.H

| Source | Claim | Lean |
| --- | --- | --- |
| Exercise 17.H.1(a), p. 648 | Gross substitutes, `cₗ = 1`: `ψ(p(t)) = max zₗ/pₗ` decreases | `exercise_17_H_1a` (`ex17H1Psi`, `ex17H1_key`, `ex17H1_max_strict`, `ex17H1_max_anti`) (corrections 50) |
| Exercise 17.H.1(b), p. 648 | `p(t)` converges to an equilibrium | `exercise_17_H_1b` |
| Exercise 17.H.2(a), p. 648 | Walras price and Marshall quantity dynamics, formally; interpretation | `ex17H2Walras`, `ex17H2Marshall`; interpretation listed (verbal) |
| Exercise 17.H.2(b), p. 648 | Near constant returns: always Walrasian stable; Marshallian stability depends on the slope of excess demand | `exercise_17_H_2b` (corrections 51) |
| Exercise 17.H.2(c), p. 648 | Joint dynamics; phase diagram; trajectories spiral in the typical case | `exercise_17_H_2c`, `ex17H2J`; phase diagram listed (graphical) |
| Exercise 17.H.2(d), p. 648 | With the technology of (b), the joint system is locally stable iff Marshallian stable | `exercise_17_H_2d`; fails without small `ε`: `exercise_17_H_2d_small_needed` |
| Exercise 17.H.2(e), p. 648 | Constant returns and constant excess demand: phase diagram; quantities responding to excess demand are stabilizing | `exercise_17_H_2e_circles`, `exercise_17_H_2e_stabilizing`; diagram listed (graphical) |
| Exercise 17.H.3, p. 648 | Draw (`L = 3`) a unique, locally totally unstable equilibrium; could it be a saddle? | drawing listed (graphical); not a saddle: `exercise_17_H_3`, instance `exercise_17_H_3_cd`, via `figure_17_H_2_index` (a locally totally unstable equilibrium has index `+1`, a saddle `-1`) (corrections 52) |

## 17.I Large economies and nonconvexities

| Source | Claim | Lean |
| --- | --- | --- |
| p. 627, first paragraph | Price taking presumes insignificant agents; the model has finitely many consumers | listed (verbal) |
| p. 627 | `r` replicas of `I` types; `(x₁, …, x_I)` means every consumer of type `i` consumes `xᵢ` | `replica`, `replica_demand`, `replica_totalEndowment` |
| p. 627 | The analysis does not depend on `r`; any equilibrium of the earlier model is an equilibrium of the `r`-replica | `replica_isDemandEqm` |
| p. 627 | Unequal numbers per type (Exercise 17.I.1) | `exercise_17_I_1` |
| p. 627 | Independence of the number of consumers depends on convexity; with nonconvexities different bundles for consumers of one type cannot be neglected | listed (verbal); illustrated by `figure_17_I_1` |
| Figure 17.I.1, p. 627 | One consumer of each type: no equilibrium; two of each: an equilibrium (convex consumers keep their endowment, nonconvex consumers at `x₁` and `x'₁`) | `fig17I1Economy`, `cdU`, `figure_17_I_1_one_two`; all replicas: `figure_17_I_1` (`E(r) = ∅` for odd `r`, the ray `p₁ = p₂ > 0` for even `r`); demand computations `fig17I1_demand_iff`, `fig17I1_pos`, `fig17I1_cd`, `fig17I1_sq_le`, `fig17I1_sq_ge`, `fig17I1_mem_20`, `fig17I1_mem_02`, `fig17I1_mem_11`, `fig17I1_totalEndowment`, `even_of_sum_pm_one` (corrections 53) |
| p. 628 | When we replicate an economy, new equilibria may emerge | `figure_17_I_1`, `footnote_71_converse_fails` |
| Footnote 71, p. 628 | `E(1) ⊆ E(r)` | `footnote_71_one` (`eqmPriceSet`, `isDemandEqm_of_replica_one`) (corrections 55) |
| Footnote 71, p. 628 | The converse need not be true | `footnote_71_converse_fails` (`E(2) ⊄ E(1)`) |
| Footnote 71, p. 628 | For `r'' > r' > 1` no inclusion relationship need hold, except `E(r') ⊆ E(r'')` when `r'' = mr'` | `footnote_71_mul` (`replica_mul_isDemandEqm`); `footnote_71_no_inclusion` (`E(2) ⊄ E(3)`, `E(4) ⊄ E(3)`); a single pair with neither inclusion, `E(2) ⊄ E(3)` and `E(3) ⊄ E(2)`: `footnote_71_neither` (`fn71Economy`, `fn71_one_mem_two`, `fn71_one_not_mem_three`, `fn71_two_mem_three`, `fn71_two_not_mem_two`) (corrections 54) |
| p. 628 | Replication may help existence; if the economy is large, existence is assured or nearly so | `near_equilibrium` (below) |
| Footnote 72, p. 628 | Starr (1969) | the Shapley-Folkman theorem: `shapley_folkman` |
| p. 628 | For `p ≫ 0`, `zᵢ(p)` is a compact, possibly nonconvex set (consumer 1 at `p̄` in Figure 17.I.1) | `excessDemandSet`, `isCompact_demand`, `demand_subset_Icc`, `isBounded_demand`, `isBounded_excessDemandSet`; nonconvex at `p̄`: `fig17I1_mem_20`, `fig17I1_mem_02`, `fig17I1_sq_le` |
| p. 628, display | `z_{ir}(p) = (1/r)(zᵢ(p) + ⋯ + zᵢ(p)) = (1/r){z_{i1} + ⋯ + z_{ir} : z_{ik} ∈ zᵢ(p)}` | `perReplicaSet`, `perReplicaExcessDemand` |
| p. 628 | As `r → ∞`, `z_{1r}(p̄) + {ω₁}` fills the segment `[x₁, x'₁]`: for `α ∈ [0, 1]` there is `a_r ∈ [0, r]` with `\|a_r/r - α\| ≤ 1/r`; `(a_r/r)x₁ + (1 - a_r/r)x'₁` is attained and is close to `αx₁ + (1 - α)x'₁` | `exists_nat_near`, `twoPoint_mem_perReplica`, `twoPoint_near`, `sum_fin_ite_lt` |
| p. 628 | For any `p ≫ 0` and any number of commodities, `z_{ir}(p)` converges as a set to `conv zᵢ(p)`; `z_{i∞}(p) = conv zᵢ(p)` | `section_17_I_convexification` (inclusion and Hausdorff convergence), `perReplicaSet_subset_convexHull`, `convexHull_near_perReplica` (rate `L·diam/r`), `tendsto_hausdorffDist_perReplica`, `shapley_folkman` (corrections 56) |
| p. 628; footnote 73 | In the limit the excess demand correspondence is convex valued and existence follows as in Section 17.C (Exercise 17.C.1, the comment after Proposition 17.C.2) | convex values: `convex_convexHull`; existence for the convexified economy (continuous, strongly monotone, possibly nonconvex preferences, `ωᵢ ≫ 0`) through `exercise_17_C_2`: `section_17_I_convexified_existence` (`convZ`, `convZ_uhc`, `convDemand_closed`, `convZ_boundary`, `convexHull_fin_rep`, `isCompact_convexHull_of_isCompact`, `exists_le_of_mem_convexHull`, `convDemand_subset_Icc`, `convDemand_eventually_Icc`, `convZ_demand_eq`); instance `section_17_I_convexified_instance` (`cvxEconomy`) (corrections 57) |
| p. 629; footnote 74 | For large `r` there is an allocation and price vector constituting a "near" equilibrium (no definition given) | `near_equilibrium` (two precise versions, given an equilibrium price of the convexified economy); existence of such a price, hence of near equilibria in every replica: `section_17_I_near_equilibrium_exists`; instance `figure_17_I_1_near_equilibrium` (corrections 57) |
| p. 629, small type | Choosing among indifferent bundles in the right proportions; dispersed preferences make the average excess demand a continuous function | listed (verbal) |
| Footnote 75, p. 629 | Dispersion with infinitely many agents is incompatible with finitely many types | listed (verbal) |
| Figure 17.I.2(a),(b), p. 629 | Aggregate excess demand with a continuum of identical consumers; dispersed individual correspondences | listed (graphical); the limit set in (a) at each price is `section_17_I_convexification` |
| Footnote 76, p. 629 | `z_{1,∞}(·)` is the correspondence whose graph is the limit graph of `z_r(·) = (1/r)(z(p) + ⋯ + z(p))` | listed (definition); the pointwise limit is `section_17_I_convexification` |
| p. 630, small type | Production: `r`-replica consumers and `J` closed production sets with `0 ∈ Yⱼ`, free disposal, bounded by `s`; a near equilibrium exists if `r` is large relative to `s` | listed (verbal sketch); OPEN as a theorem (the book gives no precise statement; it would need an existence theorem for the convexified production economy, Appendix B) |
| Footnote 77, p. 630 | Averaging is with respect to `r`, not `J`; free entry | listed (verbal) |
| p. 630, small type | Unbounded increasing returns (Figure 15.C.3): profits infinite whenever the output price is positive, so no near equilibrium (Exercise 17.I.2) | `exercise_17_I_2_profit_unbounded` |

## Exercises 17.I

| Source | Claim | Lean |
| --- | --- | --- |
| Exercise 17.I.1, p. 649 | Unequal numbers of consumers of different types (rational proportions) are covered by the replica procedure, after redefining the size of the original economy | `typeEconomy`, `exercise_17_I_1` (`kᵢr` consumers of type `i` = the `r`-replica of `kᵢ` of type `i`), `eqmPriceSet_eq_of_equiv`, `eqmPriceSet_subset_of_equiv`; rational proportions are integer proportions: `exercise_17_I_1_rational` (corrections 62) |
| Exercise 17.I.2, p. 649 | `q = v²`: `Y` is additive | `ex17I2Y`, `exercise_17_I_2_additive` |
| Exercise 17.I.2, p. 649 | The smallest cone `Y*` containing `Y` is not closed | `ex17I2Cone`, `ex17I2Cone_minimal`, `ex17I2Cone_eq`, `exercise_17_I_2_not_closed` |
| Exercise 17.I.2, p. 649 | Discuss in what sense the nonconvexity of `Y` is large | `conv Y = Y*`: `ex17I2_convexHull_eq`; points of `conv Y` arbitrarily far from `Y`: `exercise_17_I_2_large`; discussion listed (verbal) |
| Exercise 17.I.2, p. 649 | Whatever the number of consumers, no useful sense of near equilibrium | `exercise_17_I_2_profit_unbounded` (profit unbounded at every price with a positive output price); the argument listed (verbal) (corrections 63) |
| Exercise 17.I.3, p. 649 | The economy: two qualities, labor, rich and poor | `ex17I3f1`, `ex17I3f2`, `ex17I3XP`, `ex17I3uP`, `ex17I3PoorOpt`, `ex17I3RichOpt`, `Ex17I3State`, `Ex17I3State.profit₁`, `Ex17I3State.profit₂`, `Ex17I3State.wealthR`, `IsEx17I3Eqm` (corrections 64) |
| Exercise 17.I.3(a), p. 649 | Which standard hypothesis fails | convexity of the (poor's) consumption set: `exercise_17_I_3a` |
| Exercise 17.I.3(b), p. 649 | No equilibria other than with both qualities produced | `exercise_17_I_3b` |
| Exercise 17.I.3(c), p. 649 | An equilibrium exists | `exercise_17_I_3c` (explicit, every `0 < β < 1`) |

## Appendix A: characterizing equilibrium through welfare equations

| Source | Claim | Lean |
| --- | --- | --- |
| p. 630 | Reduced equation systems; a second approach through welfare properties | listed (verbal) |
| p. 630 | Pure exchange, `Xᵢ = ℝ^L₊`, continuous, strongly monotone, strictly convex preferences, `ωᵢ ≥ 0`, `∑ᵢ ωᵢ ≫ 0` | the hypotheses of `negishiAlloc_exists`, `supportingPrice_exists`, `quasiSupport_isSupporting`, `appendix_A_walras_iff` |
| p. 630 | A Walrasian equilibrium is Pareto optimal (Proposition 16.C.1) | Chapter 16 `proposition_16_C_1` (imported); the argument in the exchange setting is inside `exercise_17_AA_3` |
| p. 630 | Continuous utilities with `uᵢ(0) = 0`; to every `s ∈ Δ` a unique Pareto optimal `x(s)` with `(u₁(x₁(s)), …, u_I(x_I(s)))` proportional to `s` | `IsNegishiAlloc`, `negishiAlloc_exists` (`isCompact_inBox`, `negishi_redistribute`), `negishiAlloc_unique`, `negishiAlloc`, `negishiAlloc_spec`, `negishiAlloc_inBox`, `IsNegishiAlloc.u_eq` (corrections 58) |
| Figure 17.AA.1, p. 631 | Construction of `x(s)` on the utility frontier | `IsNegishiAlloc`; the picture listed (graphical) |
| p. 631 | `s` distributes "welfare" according to the shares `s` | listed (verbal) |
| p. 631 | By Proposition 16.D.1 and the small type after 16.D.3 there is `p(s)` with `x'ᵢ ≻ᵢ xᵢ(s) ⟹ p(s)·x'ᵢ > p(s)·xᵢ(s)` | `IsSupportingPrice`, `supportingPrice_exists` (normalized, `≫ 0`; via `secondWelfare_of_existence`); weak support suffices for normalized prices: `IsQuasiSupportingPrice`, `quasiSupport_isSupporting` |
| (17.AA.1), p. 631 | `(x(s*), p(s*))` is a Walrasian equilibrium iff `gᵢ(s*) = p(s*)·[ωᵢ - xᵢ(s*)] = 0` for all `i` | `appendix_A_walras_iff`, `walras_budget_eq`; `negishiG`, `negishiPrice` |
| Figure 17.AA.2, p. 631 | The Edgeworth box picture of `g₁(s)/p₁(s)` | listed (graphical); content `appendix_A_walras_iff` |
| p. 631 | Negishi (1960), Arrow-Hahn (1971); useful with few consumers; relies on Pareto optimality of equilibrium (fails with taxes, Exercise 17.C.3) | listed (verbal) |
| Footnote 78, p. 631 | Contrast with (17.B.2): in (17.AA.1) feasibility always holds, the wealth distribution agrees with the endowments only at a solution | feasibility: `negishiAlloc_inBox`; agreement exactly at solutions: `appendix_A_walras_iff`; contrast listed (verbal) |

## Exercises 17.AA

| Source | Claim | Lean |
| --- | --- | --- |
| Exercise 17.AA.1, p. 649 | Monotone, strictly convex preferences: for `s ≫ 0` at most one Pareto optimal `x` with `u(x)` proportional to `s` | `exercise_17_AA_1`; for every `s ≥ 0`, `s ≠ 0`: `negishiAlloc_unique` (corrections 59) |
| Exercise 17.AA.2, p. 649 | Hypotheses: continuous, strictly convex, strongly monotone preferences, `ωᵢ ≫ 0`, `g(s)` a function | `NegishiHyp` (with `NegishiHyp.ω_mem`, `NegishiHyp.total_pos`, `NegishiHyp.alloc_spec`, `NegishiHyp.alloc_inBox`, `NegishiHyp.price_spec`, `NegishiHyp.price_mem`); instance `logEconomy_negishiHyp` (`logU`, `logEconomy`, `log1p_concave`, `log1p_strict`, `logU_concaveOn`, `logU_strict`, `logU_continuousOn`, `logU_stronglyMonotone`, `logU_standard`, `logU_zero`, `logEconomy_total`, `logEconomy_diag`, `logU_support_diag`, `logEconomy_support_unique`) (corrections 60) |
| Exercise 17.AA.2, p. 649, parenthesis | Sufficient condition for `g` to be a function: differentiable utilities and, at every Pareto optimum, some consumer consuming every good | `exercise_17_AA_2_sufficient` (with a nonzero derivative; `aa2_support_pos`, `aa2_support_ker`, `aa2_grad`, `aa2_support_unique`); instance `exercise_17_AA_2_sufficient_instance` (`logU_hasFDerivAt`) (corrections 75) |
| Exercise 17.AA.2(a), p. 649 | `g(s)` is continuous | `exercise_17_AA_2a` (`negishiAlloc_continuousOn`, `negishiPrice_continuousOn`, `continuousOn_of_seq_graph`, `tendsto_dotProduct`) |
| Exercise 17.AA.2(b), p. 649 | `∑ᵢ gᵢ(s) = 0` | `exercise_17_AA_2b` |
| Exercise 17.AA.2(c), p. 649 | `sᵢ = 0 ⟹ gᵢ(s) > 0` (hint: `uᵢ(xᵢ(s)) = 0`, `p(s)·xᵢ(s) = 0`) | `exercise_17_AA_2c` |
| Exercise 17.AA.2(d), p. 649 | Complete the existence proof (as in Proposition 17.C.2) | `negishi_fixed_point` (Brouwer with Proposition 17.C.2's map `brouwerMap`), `exercise_17_AA_2d`; instance `exercise_17_AA_2_instance` |
| Exercise 17.AA.3, p. 649 | Concave increasing utilities, weights `λ ∈ Δ`: suggest an equation system via linear social welfare functions | `exercise_17_AA_3` (solutions of "x maximizes `∑λᵢuᵢ`, `p` supports `x`, `p·(ωᵢ - xᵢ) = 0`" are exactly the Walrasian equilibria), instance `exercise_17_AA_3_instance` (corrections 61) |

## Appendix B: a general approach to the existence of Walrasian equilibrium

| Source | Claim | Lean |
| --- | --- | --- |
| p. 632 | Existence at the generality of Chapter 16 (Arrow-Debreu 1954, McKenzie 1959); quasiequilibrium first, as in Section 16.D | listed (verbal) |
| Definition 17.BB.1, p. 632 | Walrasian quasiequilibrium: (i), (ii'), (iii), `p ≠ 0` | `IsWalrasQuasiEqm` |
| p. 632 | Definition 17.BB.1 is Definition 17.B.1 with (ii) weakened to (ii'); with local nonsatiation (ii') is expenditure minimization on `{xᵢ ≿ᵢ x*ᵢ}` | `smalltype_17_BB_expenditure` (binding budget, corrections 66); Chapter 16's `IsWalrasEqm` |
| Figure 17.BB.1, p. 632 | Discontinuity of preference maximization: limits of demands minimize expenditure but need not maximize preference | listed (graphical); the limit property is `lemma_17_BB_6_consumer` |
| p. 633 | Continuity makes quasiequilibrium easier; conditions making it an equilibrium | listed (verbal) |
| Definition 17.BB.2, p. 633 | Cheaper consumption condition | `CheaperConsumption` |
| Proposition 17.BB.1, p. 633 | Convex `Xᵢ`, continuous `≿ᵢ`: a consumer with a cheaper consumption maximizes preferences; if all do, the quasiequilibrium is an equilibrium | `proposition_17_BB_1`, `proposition_17_BB_1_eqm` (corrections 65); tools `bb_refl`, `bb_not_strict` |
| p. 633 (small type) | `0 ∈ Yⱼ`, `ωᵢ ≥ x̂ᵢ`, weak condition; situation (a) `p ≥ 0`, `p ≠ 0`, `ωᵢ ≫ x̂ᵢ` and (b) `p ≫ 0`, `ωᵢ ≠ x̂ᵢ` give the cheaper consumption condition (Exercise 17.BB.1 reference) | `smalltype_17_BB_cheaper_a`, `smalltype_17_BB_cheaper_b`, `bb_wealth_ge` (corrections 66) |
| p. 633 (small type) | One free-disposal production set gives `p ≥ 0` | `smalltype_17_BB_price_nonneg` |
| p. 633 (small type) | `Xᵢ + ℝ^L₊ ⊆ Xᵢ`, continuous strongly monotone preferences (and the weak condition) give `p ≫ 0` | `smalltype_17_BB_price_pos` |
| p. 633 (small type) | (a), (b) not weak; McKenzie's indecomposable economies | listed (verbal); see Exercise 17.BB.2 |
| Proposition 17.BB.2, p. 634 | `I, J > 0`; (i.1) `Xᵢ` closed convex, (i.2) rational, continuous, locally nonsatiated, convex `≿ᵢ`, (i.3) `ωᵢ ≥ x̂ᵢ ∈ Xᵢ`; (ii) `Yⱼ` closed, convex, `0 ∈ Yⱼ`, free disposal; (iii) `A` compact: a Walrasian quasiequilibrium exists | `GeneralExistenceHyp`, `bbFeasibleSet`, `proposition_17_BB_2`; instance `bbExample_hyp` (`bbExample`, `bbExampleTech`, `bbExample_feasible_bound`, `isClosed_bbFeasibleSet`) (corrections 67) |
| p. 634 | Convexity cannot be dispensed with; rationality is dispensable; free disposal is a convenience (Exercise 17.BB.3); meaning of (i.3); compactness of `A` from Appendix 16.A | listed (verbal); local nonsatiation is needed: `footnote_17_BB_80`; compactness conditions: Chapter 16's `proposition_16_AA_1` |
| Footnote 79, p. 634 | Qualification of Section 17.I | listed (verbal) |
| Footnote 80 and Figure 17.BB.2, pp. 634-635 | Edgeworth box with a consumer satiated at the origin (bads), the other strongly monotone, `ω₁, ω₂ ≫ 0`: no Walrasian quasiequilibrium | `fig17BB2Economy`, `footnote_17_BB_80` (corrections 69) |
| Footnote 81, p. 634 | `Yⱼ` convex closed, `-ℝ^L₊ ⊆ Yⱼ` imply `Yⱼ - ℝ^L₊ ⊆ Yⱼ` (Exercise 5.B.5) | `footnote_17_BB_81` (via Chapter 5's `exercise_5_B_5`) |
| Footnote 82, p. 634 | With `ωᵢ ≫ x̂ᵢ` for every `i`, Proposition 17.BB.2 yields an equilibrium; economic reading of `ωᵢ ≥ x̂ᵢ` vs `ωᵢ ≫ x̂ᵢ` | `footnote_17_BB_82`, instance `bbExample_eqm` (corrections 68); the reading listed (verbal) |
| p. 635 | The game-theoretic approach (Chapter 8, Arrow-Debreu, Gale-Mas-Colell) | listed (verbal) |
| Definition 17.BB.3, p. 635 | Free-disposal quasiequilibrium (iii') | `IsFreeDisposalQuasiEqm`; a quasiequilibrium is one: `IsWalrasQuasiEqm.isFreeDisposal` |
| p. 635 | Free disposal of one firm turns a free-disposal quasiequilibrium into a quasiequilibrium (Exercise 17.BB.4), so it suffices to find a free-disposal quasiequilibrium | `exercise_17_BB_4`; used in `proposition_17_BB_2` |
| p. 635 | The `I + J + 1` player game with a market agent | listed (verbal); formal objects below |
| pp. 635-636 | `r > 0` bounding `A`; truncated sets `X̂ᵢ`, `Ŷⱼ`; `A ⊆ ∏X̂ᵢ × ∏Ŷⱼ`; `x̂ᵢ ∈ X̂ᵢ`, `0 ∈ Ŷⱼ` | `bb_bound_of_compact`, `bbBox`, `bbOpenBox`, `mem_bbBox`, `isCompact_bbBox`, `convex_bbBox`, `isOpen_bbOpenBox`, `bbOpenBox_subset`, `bbTruncX`, `bbTruncY`, `bbTruncEconomy`, `bbTruncEconomy_wealth`, `isCompact_bbTruncX`, `isCompact_bbTruncY`; the memberships are steps of `proposition_17_BB_2` |
| Lemma 17.BB.1, p. 636 | A free-disposal quasiequilibrium of the truncated economy is one of the original economy | `lemma_17_BB_1` (`bb_near_box`, `bb_segment_box`, `bb_strict_trans`, `bb_convex_comb`, `bb_lns_near`) (corrections 67) |
| p. 636 | Limited liability wealth `wᵢ(p, y) = p·ωᵢ + Max {0, ∑ⱼ θᵢⱼ p·yⱼ}`; strategy sets `X̂ᵢ`, `Ŷⱼ`, `Δ`; consumer best responses (1)-(2), payoff 0/1 | `bbWealth`, `le_bbWealth`, `bbStrategySet`, `bbConsumerBR` |
| p. 637 | Firm best responses; market agent (17.BB.1) `max_{q ∈ Δ} (∑xᵢ - ∑ωᵢ - ∑yⱼ)·q` | `bbFirmBR`, `bbExcess`, `bbMarketBR` |
| p. 637 | The market agent raises the prices of goods in excess demand (as in Proposition 17.C.1) | listed (verbal) |
| Lemma 17.BB.2, p. 637 | An equilibrium of the game is a free-disposal quasiequilibrium of the truncated economy | `lemma_17_BB_2`, `bbWealth_eq` |
| Lemma 17.BB.3, p. 638 | Nonempty, convex valued, upper hemicontinuous best responses have a fixed point (Kakutani on `Ψ`) | `lemma_17_BB_3`, `bbGameSet`, `bbStrategySet_eq`, `priceSimplex_nonempty` (LeanEconomics `kakutani`) |
| Lemma 17.BB.4, p. 638 | Best responses are nonempty | `lemma_17_BB_4_consumer`, `lemma_17_BB_4_firm`, `lemma_17_BB_4_market`, `bb_exists_maximal`, `bb_dotProduct_mono`, `bb_continuous_dot` |
| Lemma 17.BB.5, p. 638 | Best responses are convex (consumers) | `lemma_17_BB_5_consumer`; the book's step is `exercise_17_BB_5` |
| Lemma 17.BB.6, pp. 638-639 | Best responses are upper hemicontinuous (consumers); closed graph is why expenditure minimization is used | `lemma_17_BB_6_consumer`, `bb_tendsto_wealth`, `bb_tendsto_excess`, `bb_bounded_of_subset_box`; the remark listed (verbal) |
| p. 639 | Lemmas 17.BB.4-17.BB.6 and 17.BB.3 complete the proof of Proposition 17.BB.2 | `proposition_17_BB_2` |
| Footnote 83, p. 638 | Firms and the market agent are covered by Proposition 8.D.3; consumers need a special argument (discontinuous payoffs) | listed (verbal) |
| Footnote 84, p. 638 | Continuity of `≿ᵢ` gives a continuous utility representation (Proposition 3.C.1; only continuity matters) | Chapter 3's `econ_debreu_representation` (imported); the use in Lemma 17.BB.4 is `bb_exists_maximal` |
| p. 639 (small type) | Only convex values and upper hemicontinuity of `x̃ᵢ`, `ỹⱼ` matter; preferences `uᵢ(·; x, y, p)` and technologies may depend continuously on the state; a quasiequilibrium still exists; "aggregate technology need not be convex" (Exercise 17.BB.8) | the abstract step for state-dependent best responses is `lemma_17_BB_3`; the state-dependent existence theorem is OPEN (needs state-dependent versions of Lemmas 17.BB.1, 17.BB.4 and 17.BB.6 with a joint continuity hypothesis on `uᵢ(·; x, y, p)` and on the technologies) |
| Footnote 85, p. 639 | Preferences `uᵢ(·; xᵢ)` depending on current consumption; induced `≿ᵢ`, `≻ᵢ` need not be complete or transitive | listed (verbal) |
| Footnote 86, p. 639 | Dependence on the overall consumption vector through expectations | listed (verbal) |
| pp. 639-640 | "Large space" proofs versus reduced systems | listed (verbal) |
| Footnotes 87-88, p. 640 | Not so for the generalizations; Debreu (1959) | listed (verbal) |
| p. 640 | The two-player game: aggregate consumer-firm with strategy set `∑X̂ᵢ - {∑ωᵢ} - ∑Ŷⱼ` and the market agent | `bbAggStrategy`, `bbAggResponse`, `bbPriceResponse`, `exercise_17_BB_9` |
| p. 640 | With single-valued `xᵢ(p)`, `yⱼ(p)` a one-player game (the proof of Proposition 17.C.1) | listed (verbal); `proposition_17_C_1` |
| pp. 640-641 | References | listed (bibliographic) |

## Exercises 17.BB

| Source | Claim | Lean |
| --- | --- | --- |
| Exercise 17.BB.1, pp. 649-650 | Graphical example (`L = 2`) of a quasiequilibrium with `p ≫ 0` that is not an equilibrium, with (i) `Yⱼ = -ℝ²₊`, (ii) `Xᵢ` nonempty closed convex, `Xᵢ + ℝ²₊ ⊆ Xᵢ`, (iii) continuous convex strongly monotone preferences, (iv) `ωᵢ ∈ Xᵢ` | `ex17BB1Economy`, `ex17BB1X0`, `ex17BB1u`, `ex17BB1Alloc`, `ex17BB1_X0`, `ex17BB1_X1`, `ex17BB1_hyp`, `exercise_17_BB_1` |
| Exercise 17.BB.1, p. 650 | Why this does not contradict the small type | `exercise_17_BB_1_why` (the only `x̂₀ ≤ ω₀` is `ω₀`; no cheaper consumption) |
| Exercise 17.BB.2, p. 650 | Consumers desiring subsets of goods (strongly monotone there), `∑ωᵢ ≫ 0`, indecomposability: every quasiequilibrium is an equilibrium | `PrefStronglyMonotoneIn`, `Indecomposable`, `exercise_17_BB_2`; instance `ex17BB2Economy`, `ex17BB2D`, `ex17BB2_instance` (corrections 70) |
| Exercise 17.BB.3, p. 650 | Edgeworth box, continuous strictly convex locally nonsatiated preferences, no free disposal: the offer curves cross and an equilibrium exists | OPEN: needs existence with prices of either sign (prices on the unit circle, demand defined only where the budget set admits a maximum, an intermediate value argument along the circle between the excluded quadrants); not formalised |
| Exercise 17.BB.3, p. 650 | At equilibrium the two prices cannot be negative | `exercise_17_BB_3_not_both_negative`, `exercise_17_BB_3_eqm` (any `L`; corrections 71) |
| Exercise 17.BB.3, p. 650 | At least one price is positive | `exercise_17_BB_3_no_demand`, `exercise_17_BB_3_pos_price`, `bb_convex_upper_of_strict` (any `L`) |
| Exercise 17.BB.4, p. 650 | Free disposal of firm 1 turns a free-disposal quasiequilibrium into a quasiequilibrium, changing only `y₁` | `exercise_17_BB_4` |
| Exercise 17.BB.5, p. 650 | Convexity: `xᵢ ≻ᵢ x_{iα}` and `x'ᵢ ≻ᵢ x_{iα}` cannot both hold | `exercise_17_BB_5` |
| Exercise 17.BB.6, p. 650 | Convexity of `ỹⱼ(x, y, p)` and `p̃(x, y, p)` | `exercise_17_BB_6_firm`, `exercise_17_BB_6_market` |
| Exercise 17.BB.7, p. 650 | Upper hemicontinuity of `ỹⱼ(·)` and `p̃(·)` | `exercise_17_BB_7_firm`, `exercise_17_BB_7_market` |
| Exercise 17.BB.8, p. 650 | The model: labor-only endowments, sectors of identical firms, `fₗ(v) = αₗ v^{βₗ}`, `αₗ = γₗ(∑ⱼ v_{ℓj})^{ρₗ}` | `ExtEconomy`, `ExtEconomy.α`, `ExtEconomy.profitAt`, `ExtEconomy.totalProfit` (corrections 72) |
| Exercise 17.BB.8(a), p. 650 | Define Walrasian equilibrium (firms take `αₗ` as given, equal shares) | `ExtEconomy.IsWalrasEqm`; instance `exercise_17_BB_8e_eqm` |
| Exercise 17.BB.8(b), p. 650 | Existence of a Walrasian equilibrium (with standard additional assumptions; the Appendix B proof with few adaptations) | OPEN: needs the state-dependent version of the Appendix B argument (firm technologies depending on sectoral labor: lower hemicontinuity of `α ↦ {(-v, q) : q ≤ α v^β}` for Lemma 17.BB.6, a uniform bound on `A` through `αₗ ≤ γₗ(∑ᵢ ω_{Li})^{ρₗ}`), plus an argument that the wage is positive at the quasiequilibrium (with `ρₗ > 0` an idle sector has `αₗ = 0`); the abstract fixed-point step for state-dependent best responses is `lemma_17_BB_3`, and each firm's convex technology is `exercise_17_BB_8_firm_convex` |
| Exercise 17.BB.8(c), p. 651 | The aggregate production set of a sector; returns to scale by `βₗ, γₗ, ρₗ` | `exercise_17_BB_8c_output`, `extSectorSet`, `exercise_17_BB_8c_set` (`q ≤ γ J^{1-β} V^{ρ+β}`), `exercise_17_BB_8c_returns` (increasing/constant/decreasing iff `ρ + β >, =, < 1`) |
| Exercise 17.BB.8(d), p. 651 | The aggregate set may be nonconvex while (b) applies; internalization | `exercise_17_BB_8d` (nonconvex for `ρ + β > 1`), `exercise_17_BB_8_firm_convex`; internalization (a sector-wide firm with a nonconvex technology, outside Proposition 17.BB.2) listed (verbal) |
| Exercise 17.BB.8(e), p. 651 | `L = 2`, `βₗ = 1`, quasilinear `uᵢ(x₁ᵢ) + x₂ᵢ`: bias of equilibrium production relative to the optimum, analytically and graphically | `ex17BB8eEconomy`, `exercise_17_BB_8e_eqm` (`V = 1`), `exercise_17_BB_8e_optimum` (`V = 1 + ρ`), `exercise_17_BB_8e_bias` (underproduction for `ρ > 0`); for `u = log`; the graphical discussion listed (graphical) |
| Exercise 17.BB.9, p. 651 | The existence argument through the two-player game | `exercise_17_BB_9`, `bbAggStrategy`, `bbAggResponse`, `bbPriceResponse`, `bb_continuous_excess`, `bbExcess_comb`, `bbConsumerBR_congr`, `bbAggResponse_convex`, `bbAggResponse_closedGraph` (corrections 73) |
