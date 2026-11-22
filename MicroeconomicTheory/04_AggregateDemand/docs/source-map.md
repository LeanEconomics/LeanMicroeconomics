# Source map

Mas-Colell, Whinston and Green, *Microeconomic Theory*, Chapter 4, "Aggregate Demand",
pp. 105-126. Printed pages; Lean names relative to `MWG.AggregateDemand`. Every definition,
numbered result, precise claim of the text and exercise subpart is listed. Page images were read
for every page. Departures are numbered as in [corrections](corrections.md). Dependencies are
MWG Chapters 1-3 (`MWGPreferenceChoice`, `MWGConsumerChoice`, `MWGClassicalDemand`, this
repository); the Chapter 2 and 3 results used are named in the module docstrings (Roy's identity
`proposition_3_G_4`, Shephard's lemma `shephard_lemma`, the Slutsky equation
`proposition_3_G_3`, `samuelson_sufficiency`, `proposition_2_F_1`, `theorem_M_J_2_i`, ...).

## Section 4.A

| Source | Claim | Lean |
| --- | --- | --- |
| Section 4.A, pp. 105-106 | The three aggregation questions | Verbal; formalized in Sections 4.B-4.D below |

## Section 4.B: aggregate demand and aggregate wealth

| Source | Claim | Lean |
| --- | --- | --- |
| p. 106 | Aggregate demand `∑ᵢ xᵢ(p, wᵢ)` | `aggDemand` |
| p. 106 | Invariance to redistributions of wealth | `RedistributionInvariant`, `invariant_transfer` |
| (4.B.1), p. 107 | Equal wealth effects under invariance | `equation_4_B_1` |
| Footnote 2, p. 107 | Boundaries neglected: statements are local | Wealths positive throughout; differential statements are local |
| Footnote 3, p. 107 | Wealth effect independent of the wealth level | `footnote_4_B_3` |
| p. 107, Figure 4.B.1 | Invariance iff straight parallel expansion paths (differentiable, `I ≥ 2`) | `ParallelLinearEngel`, `aggDemand_of_linear`, `invariant_of_parallel`, `parallel_of_invariant`, `invariant_iff_parallel` (correction 10) |
| p. 107 | Identical homothetic, or quasilinear in the same good: special cases | `gorman_of_homothetic`, `indirectUtility_homothetic`, `footnote_4_B_4` |
| Proposition 4.B.1, p. 107 | Gorman form `aᵢ(p) + b(p) wᵢ` iff parallel straight paths | sufficiency: `GormanForm`, `roy_gorman`, `proposition_4_B_1_sufficiency`; necessity (book: not proved): `ratio_const_of_grad`, `expenditure_hasFDerivAt_linear_engel`, `proposition_4_B_1_necessity` (correction 10) |
| Footnote 4, p. 108 | Quasilinear utility: `v = a(p) + w/p_ℓ` | `footnote_4_B_4` |
| p. 108 | Identical preferences: aggregate depends only on the wealth distribution | `aggDemand_perm` |
| p. 108 | Mean/variance dependence; references | Verbal |
| pp. 108-109 | Wealth distribution rules; aggregate demand `x(p, w)` | `IsWealthDistributionRule`, `ruleDemand`, `ruleDemand_eq_aggDemand`, `ruleDemand_spec` |

## Section 4.C: aggregate demand and the weak axiom

| Source | Claim | Lean |
| --- | --- | --- |
| p. 109 | Continuity, homogeneity and Walras' law pass to aggregate demand (footnote 6) | `ruleDemand_continuousOn`, `ruleDemand_homogeneousZero`, `ruleDemand_walrasLaw` |
| p. 109, footnote 5 | Methodological remark | Verbal |
| p. 109, footnote 7 | Share rule `wᵢ = αᵢ w`; proportional wealth changes are price changes | `shareRule`, `IsShareVector`, `shareDemand`, `shareDemand_eq_ruleDemand`, `isWealthDistributionRule_shareRule`, `footnote_4_C_7` |
| Definition 4.C.1, p. 109 | Weak axiom for aggregate demand | `definition_4_C_1` (MWG Chapter 2's `WeakAxiom`) |
| Example 4.C.1, p. 110, Figure 4.C.1 | Individual demands satisfy the WA, aggregate does not | `example_4_C_1`, `example_4_C_1_individual_weakAxiom`, `example_4_C_1_demands_exist`, `weakAxiom_of_unique_demand`, `walrasianDemand_minUtility`, `minUtility` |
| (4.C.1)-(4.C.2), pp. 110-111 | Changes compensated for every consumer satisfy the compensated law in the aggregate; footnote 8 | `aggregate_compensated_law` |
| p. 111 | Individual wealth effects can upset (4.C.1) | Verbal; instances: `example_4_C_1`, `exercise_4_C_12` |
| Definition 4.C.2, p. 111 | Uncompensated law of demand | `UncompensatedLawOfDemand` |
| p. 111 | ULD implies `D_p x` NSD; ND for all `p` implies ULD | `exercise_4_C_1_nsd`, `exercise_4_C_1_nd`, `hasDerivAt_dot_line` |
| Proposition 4.C.1, pp. 111-112 | ULD is additive and implies the WA (footnote 9) | `uld_shareDemand`, `weakAxiom_of_uld`, `proposition_4_C_1` (correction 1) |
| p. 112 | ULD is not implied by preference maximization | `exercise_4_C_3` |
| Proposition 4.C.2, p. 112 | Homothetic preferences satisfy the ULD | `proposition_4_C_2`, `proposition_4_C_2_pref`, `exists_pos_mem_budgetSet`; book's proof: `proposition_4_C_2_differential`, `proposition_4_C_2_negDef`, `dot_vecMulVec_mulVec` (correction 2) |
| Proposition 4.C.3, p. 112 | Mitiushin-Polterovich: `σ(x) < 4` implies the ULD | `proposition_4_C_3` (on `ℝ^L_+`, boundary demands included), `proposition_4_C_3_interior`, `mp_uld_on` (any convex set of bundles), `demand_variational`, `mp_dot_pos`, `interior_demand_gradient`, `mp_quadratic`; instances `proposition_4_C_3_instance`, `ql_uld` (correction 5) |
| p. 113 | The condition is not stringent; homothetic case | `exercise_4_C_6` |
| Proposition 4.C.4, p. 113 | Hildenbrand: uniform wealth on `[0, w̄]` gives the ULD | weak inequality, general: `proposition_4_C_4`, `young_square`, `hildenbrandDemand`, `integral_dot_hildenbrand`; strict part false: `proposition_4_C_4_strict_counterexample`, `hildU`, `hildKink`, `integral_two_piece`, `integral_affine`; strict part under the book's extra hypothesis (`v·S v < 0` off the ray, differentiable case): `proposition_4_C_4_strict`, `hild_ray_slutsky`; instance `cobbDouglasHalf_hildenbrand`, `cdHalf_hypotheses`, `cdHalf`, `cdHalfDp`, `cdHalfDw` (correction 4) |
| p. 113, proof | The mean income effect `∫ (v·D_w x̃)(v·x̃) = ½ (v·x̃(p, w̄))²` | `hildenbrand_mean_income_effect` |
| p. 113, footnote 10 | ULD additive for price-independent rules; price-dependent rules can fail | `uld_shareDemand`; `exercise_4_C_13` |
| pp. 113-114 | Additivity over preference types; nonincreasing density | `uld_shareDemand`; `exercise_4_C_7` |
| (4.C.4)-(4.C.6), p. 114 | Aggregate and summed Slutsky equations | `hasFDerivAt_shareDemand`, `priceJacobian_shareDemand`, `wealthJacobian_shareDemand`, `scaleWealthCLM`, `equation_4_C_4_5`, `equation_4_C_6` |
| (4.C.7)-(4.C.8), p. 114 | `S = ∑ Sᵢ - C`, `C` a covariance matrix; zero weighted means | `covMatrix`, `slutsky_aggregate_algebra`, `equation_4_C_7`, `equation_4_C_8`, `covariance_means_zero` |
| p. 114 | `dp·Sᵢ dp < 0` off the price ray "always" | False: `leontief_slutsky_zero` (correction 3) |
| p. 114 | `C` psd (and `Sᵢ` negative off the ray) suffices for the WA | `slutsky_negative_of_cov_psd`, `weakAxiom_of_cov_psd` |
| p. 115, Figure 4.C.2 | Positive/negative association of wealth effects and consumption | Graphical; the sign is `v·C v` |
| p. 115 | Cases (i) equal wealth effects, (ii) proportional consumption: `C = 0` | `cov_zero_of_equal_wealth_effects`, `cov_zero_of_proportional_consumption` |
| p. 115 | WA for a fixed distribution is weaker than invariance (homothetic, non-identical) | `homothetic_weakAxiom_not_invariant`, `leontiefRayDemand_homogeneousZero` |
| p. 115 | Identical preferences and wealth: aggregate satisfies the SA | `identical_consumers_strongAxiom` |
| pp. 115-116 | Why not the SA (robustness, perturbations) | Verbal |

## Section 4.D: the existence of a representative consumer

| Source | Claim | Lean |
| --- | --- | --- |
| Definition 4.D.1, p. 116 | Positive representative consumer | `IsPositiveRepresentative` |
| Footnote 14, p. 116 | Positive representative implies WA and SA | `weakAxiom_of_positiveRepresentative`, `strongAxiom_of_positiveRepresentative`, `rational_utilityPref` |
| Definition 4.D.2, p. 117 | Bergson-Samuelson social welfare function | `SocialWelfareFunction` |
| (4.D.1), p. 117 | The planner's problem and its value | `FeasibleDistribution`, `SolvesSWP`, `socialIndirectUtility`, `PlannerSetup` |
| Footnote 15, p. 117 | Concavity makes first-order conditions sufficient | Not needed by the proofs here |
| Footnote 16, p. 117; Exercise 4.D.1 | Distributing wealth versus bundles | `exercise_4_D_1`, `split_value_le` |
| Proposition 4.D.1, pp. 117-118 | `v(p, w)` is the indirect utility of a positive representative | `proposition_4_D_1_demand`, `proposition_4_D_1`, `repUtility`, `isCompact_splits` (correction 6) |
| (4.D.2), p. 118 | First-order conditions; Roy's identity argument | Superseded by the non-differentiable proof (correction 6) |
| Definition 4.D.3, p. 118 | Normative representative consumer | `IsNormativeRepresentative`, `proposition_4_D_1_normative` |
| Example 4.D.1, pp. 118-119 | Homothetic utilities, `W = ∑ αᵢ ln uᵢ`: optimal rule `αᵢ w` | `exercise_4_D_6` (correction 7) |
| Example 4.D.2, p. 119 | Gorman form, utilitarian `W`: any distribution optimal, `v = ∑ aᵢ + b w` | `exercise_4_D_7` |
| p. 119, footnotes 17-19 | `∑ aᵢ(p) + b(p) w` is the normative indirect utility for any `W` | `example_4_D_2_any_W`, `gorman_compensating_distribution` |
| p. 120, footnote 20 | Potential compensation test iff `V(p', w') > V(p, w)` | `example_4_D_2_compensation`, `PassesPotentialCompensation` |
| p. 120 | Passing the test: preferred by every normative representative | `exercise_4_D_8` |
| pp. 120-121, Figure 4.D.1 | Sets `A`, `B`; `A ⊆ B` is necessary for a normative representative | `normative_A_subset_B` |
| p. 121 | `A ⊆ B` implies `∑ᵢ Sᵢ - S` psd | `exercise_4_D_9`, `exists_hicksian_selection` |
| pp. 121-122 | Positive but no normative representative; the moral | Verbal; Exercise 4.D.10 below |

## Appendix A: regularizing effects of aggregation

| Source | Claim | Lean |
| --- | --- | --- |
| Example 4.AA.1, p. 122, Figure 4.AA.1(a) | Individual demand jumps at `p₁ = vᵢ` | `indivisibleDemand`, `example_4_AA_1_individual` |
| Example 4.AA.1, pp. 122-123, Figure 4.AA.1(b) | Dispersed values: average demand `1 - G(p₁)` continuous | `example_4_AA_1_continuum` |
| Example 4.AA.1, p. 123 | Finitely many consumers: `G` cannot be continuous | `example_4_AA_1_finite` |
| p. 123 | Convexifying effect (Section 17.I) | Cross-reference |

## Exercises

| Source | Claim | Lean |
| --- | --- | --- |
| Exercise 4.B.1, p. 123 | Sufficiency in Proposition 4.B.1 (Roy) | `roy_gorman`, `proposition_4_B_1_sufficiency` |
| Exercise 4.B.1, p. 123 | Common `b(p)` gives `eᵢ(p, u) = c(p) u + dᵢ(p)` | `exercise_4_B_1_expenditure`, `expenditure_pos_of_attainable` |
| Exercise 4.B.2(a), p. 124 | Invariance and homotheticity force identical demands | `exercise_4_B_2a`, `demand_hd1_of_homogeneousOne` (identical demand functions; identity of the preferences then follows from recoverability, not restated) |
| Exercise 4.B.2(b), p. 124 | Sufficient condition with family size | `exercise_4_B_2b`, `exercise_4_B_2b_gorman` |
| Exercise 4.C.1, p. 124 | ULD gives `D_p x` NSD; `D_p x` ND gives ULD | `exercise_4_C_1_nsd`, `exercise_4_C_1_nd` |
| Exercise 4.C.2, p. 124 | Proposition 4.C.1 via differential versions | `exercise_4_C_2`, `slutsky_negative_of_negDef` |
| Exercise 4.C.3, p. 124 | Demand not satisfying the ULD; interpretation | `exercise_4_C_3` |
| Exercise 4.C.4, p. 124 | L-shaped curves and ULD imply homothetic (differentiable, as in the hint) | `exercise_4_C_4`, `exercise_4_C_4_hint`, `slutsky_zero_minUtility`, `minUtility_kink_point`, `minUtility_demand_eq` |
| Exercise 4.C.5, p. 124 | Proof of Proposition 4.C.3 | `proposition_4_C_3`, `mp_uld_on`, `demand_variational`, `interior_demand_gradient`, `mp_quadratic` |
| Exercise 4.C.6, p. 124 | Homothetic: `σ(x) = 0` | `exercise_4_C_6` |
| Exercise 4.C.7, p. 124 | Nonincreasing density | `exercise_4_C_7`, `antitone_weighted_integral_nonpos`, `densityDemand` |
| Exercise 4.C.7, p. 124 | Unimodal densities can fail | `exercise_4_C_7_unimodal`, `tentDensity`, `integral_tent` (correction 9) |
| Exercise 4.C.8, p. 124 | Derive (4.C.7) | `exercise_4_C_8`, `equation_4_C_7` |
| Exercise 4.C.9, p. 124 | Homothetic: `C` psd | `exercise_4_C_9` |
| Exercise 4.C.10, p. 124 | Hildenbrand: `C` psd (continuum version) | `exercise_4_C_10` |
| Exercise 4.C.10, p. 124 | Conclude the WA | `exercise_4_C_10_weakAxiom`, `hildMeanDemand`; instance `cobbDouglasHalf_weakAxiom` (correction 11) |
| Exercise 4.C.11(a), p. 124 | Quasilinear pair: individual and aggregate demand | `exercise_4_C_11a_consumer1`, `exercise_4_C_11a_consumer2`, `exercise_4_C_11a`, `ql_bound`, `ql1`, `ql2`, `swap2` (interior and corner demands) |
| Exercise 4.C.11(b), pp. 124-125 | Individual Slutsky matrices (interior and corner) | `exercise_4_C_11b_consumer1`, `exercise_4_C_11b_consumer2`, `qlF1`, `qlC1`, `qlF2`, `qlC2`, `fderiv_eq_of_line`, `hasDerivAt_ratio_line`, `hasDerivAt_sqratio_line`, `ql_eventually` |
| Exercise 4.C.11(b), pp. 124-125 | Aggregate Slutsky matrix in the four regions; `dp·S dp < 0` off the ray | `exercise_4_C_11b_aggregate`, `exercise_4_C_11b_negative`, `ql_agg_slutsky`, `ql_prop_of_cross` (correction 12) |
| Exercise 4.C.11(b), p. 125 | Conclude the WA (everywhere, kinks included) | `exercise_4_C_11b_weakAxiom`, `ql_uld_consumer1`, `ql_uld_consumer2`, `ql_uld`, `qlGen`, `qlGrad`, `qlHess`, `ql1_facts`, `ql2_facts`, `homogeneousZero_of_singleton` |
| Exercise 4.C.11(c), p. 125 | `C` psd iff `w ≥ 16`; NSD for `8 < w < 16` | `exercise_4_C_11c` (at `p = (1, 1)`, `w > 8`: `v·C v = (w - 16)(v₁ - v₂)²/4`) |
| Exercise 4.C.11(c), p. 125 | `C` psd not necessary for the WA | `exercise_4_C_11c_conclusion` |
| Exercise 4.C.11(d), p. 125 | Pictures of expansion paths | Graphical |
| Exercise 4.C.12, p. 125 | Distribution-dependent aggregate demand need not satisfy the WA | `exercise_4_C_12`, `ex412Kink`, `ex412U` (correction 8) |
| Exercise 4.C.13, p. 125 | Price-dependent rule, homothetic consumers, WA fails | `exercise_4_C_13`, `ex413Rule`, `ex413Rule_sum`, `leontiefU`, `leontiefRayDemand`, `walrasianDemand_leontiefU`, `leontiefRayDemand_uld` |
| Exercise 4.D.1, p. 125 | Bundles versus wealth | `exercise_4_D_1` |
| Exercise 4.D.2, p. 125 | `v` has the properties of an indirect utility | `exercise_4_D_2` |
| Exercise 4.D.3, p. 125 | Proposition 4.D.1 with corners | `proposition_4_D_1` (no interiority used) |
| Exercise 4.D.4(a), p. 125 | Monotone, concave, quasiconcave, continuous `u` | `exercise_4_D_4a_monotone`, `exercise_4_D_4a_concave`, `exercise_4_D_4a_quasiconcave`, `exercise_4_D_4a_continuous` (interior, from concavity), `exercise_4_D_4a_continuousOn` (all of `ℝ^L_+`, `W` and `uᵢ` continuous), `splitValues`, `shareSimplex`, `isCompact_shareSimplex`, `splitValues_eq_image` |
| Exercise 4.D.4(b), p. 126 | Demand of `u` is aggregate demand | `proposition_4_D_1_demand`, `PlannerSetup.repUtility_spec` |
| Exercise 4.D.5, p. 126 | Shares with no positive representative | `exercise_4_D_5` |
| Exercise 4.D.6, p. 126 | Example 4.D.1 | `exercise_4_D_6` |
| Exercise 4.D.7, p. 126 | Example 4.D.2 | `exercise_4_D_7` |
| Exercise 4.D.8, p. 126 | Potential compensation | `exercise_4_D_8` |
| Exercise 4.D.9, p. 126 | `A ⊆ B` implies `S - ∑ Sᵢ` NSD | `exercise_4_D_9` |
| Exercise 4.D.10, p. 126 | Exercise 4.C.11: a positive representative exists | `exercise_4_D_10_positive` (WA, then MWG Ch. 3 `weakAxiom_rationalizable_two`) |
| Exercise 4.D.10, p. 126 | No normative representative (any nondecreasing `W`) | `exercise_4_D_10_normative`, `qlAgg`, `ql_sqrt_eq` (a twelve-step revealed-preference chain at `p̄ = (1, 1)`, `w̄ = 10`; correction 13) |
| Exercise 4.D.11, p. 126 | Hildenbrand with `L = 3`: no positive representative | `exercise_4_D_11`, `l3_demand_exists`, `l3U`, `l3U_demand`, `l3_demand`, `l3_agg`, `integral_three_piece`, `l3G0`, `l3G2`, `l3P0`, `l3P2`, `l3A`, `l3B`, `l3C`, `dotProduct_three`, `strictMono_l3P0`, `strictMono_l3P2`, `l3P0_l3G0`, `l3P2_l3G2`, `continuous_l3U` (a revealed-preference 3-cycle; correction 14) |

## OPEN

None. The items formerly open (Proposition 4.C.3 on the boundary, the strict part of
Proposition 4.C.4, Exercises 4.C.10 "conclude WA", 4.C.11(b), 4.D.4(a) on the boundary,
4.D.10 and 4.D.11) are closed in the rows above.
