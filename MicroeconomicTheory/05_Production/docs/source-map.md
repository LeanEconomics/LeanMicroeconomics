# Source map

Mas-Colell, Whinston and Green, *Microeconomic Theory*, Chapter 5, "Production", pp. 127-166,
with Mathematical Appendix Section M.M (linear programming, pp. 966-968). Printed pages; Lean
names relative to `MWG.Production`. Every definition, numbered result, precise claim of the
text and exercise subpart is listed. Page images were read for every page. Departures are
numbered as in [corrections](corrections.md). Dependencies are MWG Chapters 2 and 3
(`MWGConsumerChoice`, `MWGClassicalDemand`, this repository, Lake `path` requirements): Chapter 3's
support function and duality theorem (`supportFn`, `supportFnE`, `supportArgmin`,
`proposition_3_F_1`, `duality_differentiable_of_unique`, `separation_section_3_F`), separating
hyperplanes (`theorem_M_G_2_ii`), the CMP-as-EMP bridges (`example_3_E_1`,
`cdExpenditure_eq_book`, `cdHicksian_eq_book`, `exercise_3_E_6_expenditure`,
`exercise_3_E_6_hicksian`), line-derivative lemmas of Section M.C, and Chapter 2's
`theorem_M_D_5_v` (Neumann series), `jacobian`, `hessianMatrix`, `NegDef`, `PosSemidefMWG`,
`hasDerivAt_nonpos_of_right_le`.

## OPEN items

None. The items formerly open (Exercises 5.AA.1, 5.B.4 closed case, 5.C.7 explicit demand and
`n`-input correction, 5.D.3, 5.D.4(b)-(c), 5.D.5(a), 5.E.4, and Proposition 5.C.1(vii) for
nonconvex `Y`) are closed in the rows below.

## Section 5.B: production sets

| Source | Claim | Lean |
| --- | --- | --- |
| Example 5.B.1, p. 128 | Reading `y = (-5, 2, -6, 3, 0)` | `example_5_B_1` |
| p. 128 | Transformation function, transformation frontier | `IsTransformationFunction`; instance `isTransformationFunction_halfPlane` |
| p. 129, footnote 1 | `MRT_{lk}`, slope of the frontier `= -MRT` | `partialAt`, `MRT`, `mrt_slope` |
| p. 129 | Distinct inputs and outputs; single-output set `{(-z, q) : q ≤ f(z), z ≥ 0}` | `inputsOf`, `singleOutputSet`, `mem_singleOutputSet`, `extendVec`, `extendVec_inputsOf` |
| p. 130 | `MRTS_{lk}` | `partialF`, `MRTS` |
| Example 5.B.2, p. 130 | Cobb-Douglas `MRTS₁₂ = αz₂/(βz₁)` | `cdProd`, `cdProd_partial`, `example_5_B_2` |
| (i)-(ii), p. 130 | Nonempty, closed | Mathlib `Set.Nonempty`, `IsClosed` |
| (iii), p. 130 | No free lunch, `Y ∩ ℝ^L_+ ⊆ {0}` | `NoFreeLunch`, `noFreeLunch_iff` |
| (iv), p. 130 | Inaction | `InactionPossible` |
| Figures 5.B.2-5.B.3, p. 131 | Sunk costs, restricted sets | Graphical |
| (v), p. 131 | Free disposal, `Y - ℝ^L_+ ⊆ Y` | `FreeDisposal`, `freeDisposal_iff` |
| (vi), p. 132 | Irreversibility | `Irreversible` |
| Exercise 5.B.1, p. 132 | Two sets, violating / satisfying irreversibility | `exercise_5_B_1` |
| (vii), p. 132 | Nonincreasing returns; implies inaction | `NonincreasingReturns`, `inaction_of_nonincreasingReturns` (correction 1, `nonincreasingReturns_empty`) |
| (viii), p. 132 | Nondecreasing returns | `NondecreasingReturns` |
| (ix), p. 132 | Constant returns = (vii) ∧ (viii) | `ConstantReturns`, `constantReturns_iff` |
| Exercise 5.B.2, p. 132 | CRS iff `f` homogeneous of degree one | `exercise_5_B_2` |
| Example 5.B.3, p. 133 | `f(2z) = 2^{α+β}f(z)`; CRS / DRS / IRS | `example_5_B_3_hom`, `example_5_B_3` |
| (x), p. 133 | Additivity; `ky ∈ Y` | `Additive`, `additive_nsmul` |
| Figure 5.B.8, p. 133 | Additive staircase technology (nonconvex) | `figure_5_B_8` |
| (xi), p. 133 | Convexity | Mathlib `Convex ℝ Y` |
| p. 134 | Convexity + inaction ⇒ nonincreasing returns | `nonincreasingReturns_of_convex` |
| Exercise 5.B.3, p. 134 | `Y` convex iff `f` concave | `exercise_5_B_3` |
| (xii), p. 134 | Convex cone = convex ∧ CRS | `IsConvexCone`, `isConvexCone_iff` |
| Proposition 5.B.1, p. 134 | Additive ∧ NIRS iff convex cone | `proposition_5_B_1` |
| Proposition 5.B.2, pp. 134-135 | Convex `Y` is a section of a CRS convex `Y' ⊆ ℝ^{L+1}` | `proposition_5_B_2`; without `0 ∈ Y`: `proposition_5_B_2_general` |
| Small type, pp. 134-135 | Entrepreneurial factor | Verbal; Exercise 5.C.12 below |

## Section 5.C: profit maximization and cost minimization

| Source | Claim | Lean |
| --- | --- | --- |
| p. 135 | PMP | `profit`, `profitFn`, `supply`, `mem_supply_iff` |
| p. 136, footnote 5 | `π(p) = sup`, `+∞` allowed | `profitFn`, `profitFn_eq_top`, `profitFn_eq_coe`, `profitFn_lt_top_iff` |
| p. 136 | Example: one-for-one CRS, `π = 0` or `+∞` | `oneForOneTech`, `example_5_C_profit_oneForOne` |
| Exercise 5.C.1, p. 136 | NDRS ⇒ `π ≤ 0` or `+∞` | `exercise_5_C_1` |
| (5.C.1), pp. 136-137 | `p = λ∇F(y*)`; `p_l/p_k = MRT` | `foc_5_C_1`, `foc_5_C_1_ratio` (correction 2, `foc_5_C_1_needs_cq`) |
| (5.C.2), p. 137, footnote 7 | Single-output FOC; `MRTS = w_l/w_k` | `foc_5_C_2`, `foc_5_C_2_mrts` |
| p. 137 | FOC sufficient for convex `Y` | `foc_5_C_1_sufficient`, `foc_5_C_2_sufficient`, `concave_le_tangent` |
| p. 137 | `π(p) = -μ_{-Y}(p)` | `profit_eq_neg_supportFn`, `supply_eq_neg_supportArgmin`, `bddAbove_iff_bddBelow_neg` |
| Proposition 5.C.1(i), p. 138 | HD1 | `proposition_5_C_1_i` |
| Proposition 5.C.1(ii) / Exercise 5.C.2 | Convex | `proposition_5_C_1_ii`, `exercise_5_C_2`, `proposition_5_C_1_ii_real` |
| Proposition 5.C.1(iii) | Dual description of `Y` | corrected: `proposition_5_C_1_iii_nonneg`, `proposition_5_C_1_iii`; `proposition_5_C_1_iii_counterexample` (correction 3) |
| Proposition 5.C.1(iv) | HD0 | `proposition_5_C_1_iv` |
| Proposition 5.C.1(v) | Convex / single-valued | `proposition_5_C_1_v_convex`, `proposition_5_C_1_v_strict` |
| Proposition 5.C.1(vi) | Hotelling's lemma | `proposition_5_C_1_vi` (convex `Y`); `proposition_5_C_1_vi_nonconvex_counterexample` (correction 4) |
| Proposition 5.C.1(vii) | `Dy = D²π`, symmetric, PSD, `Dy p̄ = 0` | closed convex `Y`: `proposition_5_C_1_vii`; closed `Y`, no convexity: `proposition_5_C_1_vii_general` (via `supply_continuousAt_of_single`, `hotelling_of_continuousAt`); symmetry for any `Y` and any differentiable supply selection: `proposition_5_C_1_vii_symm` (via `supply_cyclic`, `deriv_cyclic`, `thinCycle`, `thinCycle_bound`, `cyclic_symm`); PSD and `Dy p̄ = 0` for all `Y`: `proposition_5_C_1_vii_psd`, `proposition_5_C_1_vii_euler`; nonconvex instances `ssY`, `ssSupply`, `ssSupply_mem_supply`, `ss_supply_eq`, `proposition_5_C_1_vii_symm_instance`, `proposition_5_C_1_vii_general_instance` (correction 4) |
| (5.C.3), pp. 138-139 | Law of supply | `law_of_supply` |
| p. 139 | CMP, `c(w, q)`, `z(w, q)` | `inputReq`, `costFn`, `costFnE`, `condDemand` |
| (5.C.4), p. 140 | CMP first-order conditions | `foc_5_C_4` (with constraint qualification; correction 5, `foc_5_C_4_needs_cq`) |
| Footnote 8, p. 140 | Sufficient for quasiconcave `f` | `foc_5_C_4_sufficient`, `quasiconcave_grad_nonneg` |
| p. 140 | `λ = ∂c/∂q` | `cost_lambda_subgradient`, `lambda_eq_marginal_cost` |
| Proposition 5.C.2(i) | HD1 in `w`, nondecreasing in `q` | `proposition_5_C_2_i_hom`, `proposition_5_C_2_i_mono` |
| Proposition 5.C.2(ii) | Concave in `w` | `proposition_5_C_2_ii` |
| Proposition 5.C.2(iii) | `Y = {(-z, q) : w·z ≥ c(w, q) ∀w ≫ 0}` | `proposition_5_C_2_iii` (via `vcost_iii`) |
| Proposition 5.C.2(iv) | HD0 | `proposition_5_C_2_iv` |
| Proposition 5.C.2(v) | Convex / single-valued | `proposition_5_C_2_v_convex`, `proposition_5_C_2_v_strict` |
| Proposition 5.C.2(vi) | Shephard's lemma (no convexity needed) | `proposition_5_C_2_vi`, `vcost_shephard`, `supportFn_hasFDerivAt_of_compact` |
| Proposition 5.C.2(vii) | `D_w z = D²_w c`, symmetric NSD, `D_w z w̄ = 0` | `proposition_5_C_2_vii`, `vdemand_derivative` |
| Proposition 5.C.2(viii)-(ix) / Exercise 5.C.3 | HD1 in `q`; convex in `q` | `proposition_5_C_2_viii`, `proposition_5_C_2_ix` |
| Exercise 5.C.4 | (i)-(vii) for multiple outputs | `exercise_5_C_4_i` … `exercise_5_C_4_vii` |
| p. 141 | One-to-one profit/cost functions | `proposition_5_C_1_iii_nonneg`, `proposition_5_C_2_iii` |
| (5.C.5)-(5.C.6), p. 141 | Output choice; price = marginal cost; sufficiency | `foc_5_C_6`, `foc_5_C_6_sufficient`, `convex_tangent_le` |
| Footnote 9, p. 141 | (5.C.4) with `λ = p` is (5.C.2) | `footnote_5_C_9` |
| Example 5.C.1, pp. 142-143 | CD factor demands and cost | `cdTheta`, `cdPhi`, `cd_inputReq_eq`, `cdTheta_eq`, `example_5_C_1_cost` |
| (5.C.7), p. 142 | Supply, `α + β < 1` | `example_5_C_1_supply` (correction 6, `example_5_C_1_printed_supply_counterexample`) |
| p. 142 | `α + β = 1` trichotomy | `example_5_C_1_crs` |
| pp. 142-143 | `α + β > 1`: no solution; doubling factor | `example_5_C_1_irs`, `example_5_C_1_doubling` (correction 7) |

## Section 5.D: the geometry of cost and supply

| Source | Claim | Lean |
| --- | --- | --- |
| (5.D.1), p. 143 | FOC, sufficiency for convex `C` | `foc_5_C_6`, `foc_5_C_6_sufficient` |
| Figures 5.D.1-5.D.2 | Convex technologies | Graphical |
| Figure 5.D.3, pp. 144-145 | Nonconvex supply locus, efficient scale | `outputSupply`, `supply_nonconvex` |
| Exercise 5.D.1, p. 144 | `AC(q̄) = C'(q̄)`; differentiability only at `q̄` | `exercise_5_D_1`, `exercise_5_D_1_onesided`, `exercise_5_D_1_kink` |
| Figures 5.D.4-5.D.5, p. 145 | Nonsunk setup costs | `figure_5_D_5` (linear `C_v`); Figure 5.D.4 graphical, covered by `supply_nonconvex` |
| Figure 5.D.6, p. 146 | Sunk costs | `sunk_cost_supply`, `sunk_cost_covers_variable` (correction 8, `sunk_cost_strict_fails`) |
| Exercise 5.D.2, p. 146 | Partially sunk costs | `exercise_5_D_2` (the drawing is graphical) |
| pp. 146-147, Figure 5.D.7 | Short-run vs long-run cost, envelope, marginal costs | `shortRunReq`, `shortRun_ge_longRun`, `shortRun_eq_longRun`, `longRun_lower_envelope`, `shortRun_marginal_eq` |

## Section 5.E: aggregation

| Source | Claim | Lean |
| --- | --- | --- |
| p. 147 | `Σ_j y_j(p)`, `Y₁ + ⋯ + Y_J` | `aggSupply`, `aggSet` |
| p. 147 | Sum of symmetric PSD; aggregate law of supply | `sum_symm_psd`, `aggregate_law_of_supply` |
| Proposition 5.E.1, p. 148 | `π* = Σπ_j`, `y* = Σy_j` | `proposition_5_E_1_i`, `proposition_5_E_1_i_real`, `proposition_5_E_1_ii` |
| p. 148 | Cost-minimizing allocation of output | Consequence of `proposition_5_E_1_ii` (verbal) |
| Small type, p. 149, Figure 5.E.2, footnote 12 | Averages nearly convex | Verbal (Shapley-Folkman belongs to Chapter 17) |
| Exercise 5.E.1, p. 163 | Differentiable proof of (ii) | `exercise_5_E_1`, `profit_fderiv_eq_of_mem_supply` |
| Exercise 5.E.2 | No convexity needed | `proposition_5_E_1_i`, `proposition_5_E_1_ii` (no convexity hypotheses) |
| Exercise 5.E.3 | Dual description of `ΣY_j` | `exercise_5_E_3`, `exercise_5_E_3_pos`, `exercise_5_E_3_counterexample` (correction 3), `aggSet_convex_freeDisposal` |
| Exercise 5.E.4(a), p. 163 | One Leontief technology: `q = 1` iff `w·z < 1`, profit `max(0, 1 - w·z)` | `exercise_5_E_4a` |
| Exercise 5.E.4(b), p. 164 | `π(w, 1) = 1/(600 w₁w₂)` for `w ≥ 1/10` | `e4AggProfit`, `exercise_5_E_4b` (via `e4_pow_integral`; correction 19) |
| Exercise 5.E.4(c), p. 164 | Aggregate input demands directly and from (b) | `e4AggDemand`, `e4AggDemand_eq`, `exercise_5_E_4c` (via `e4_step_integral`) |
| Exercise 5.E.4(d), p. 164 | Aggregate production function `(9z₁z₂/200)^{1/3}`; "what can you say" is verbal | `e4Prod`, `exercise_5_E_4d` |
| Exercise 5.E.5(a)-(c) | Weitzman allocation | `exercise_5_E_5a`, `exercise_5_E_5b`, `exercise_5_E_5c` |

## Section 5.F: efficient production

| Source | Claim | Lean |
| --- | --- | --- |
| Definition 5.F.1, p. 150 | Efficiency | `Efficient` |
| Figure 5.F.1, p. 150 | Efficient ⇒ boundary, not conversely | `efficient_mem_frontier`, `frontier_not_efficient` |
| Proposition 5.F.1, p. 150 | Profit max at `p ≫ 0` ⇒ efficient | `proposition_5_F_1` |
| Exercise 5.F.1, p. 151 | `p ≥ 0, p ≠ 0` not enough | `exercise_5_F_1` |
| Proposition 5.F.2, p. 151 | Convex `Y`: efficient ⇒ profit max at `p ≥ 0, p ≠ 0` | `proposition_5_F_2` (correction 9, `proposition_5_F_2_needs_dimension`) |
| Footnote 13, p. 151 | Weakly efficient version | `WeaklyEfficient`, `proposition_5_F_2_weak`, `Efficient.weaklyEfficient` |
| Figure 5.F.4, p. 152 | Cannot require `p ≫ 0` | `figure5F4Set`, `figure_5_F_4` |
| p. 152 | Concave `f`, `w = ∇f(z̄)` | `efficient_single_output_concave` |

## Section 5.G: objectives of the firm

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 152-153 | Unanimity of owners at fixed prices | `ownerBudget`, `unanimity_budget`, `unanimity_value`, `unanimity_strict`, `unanimity_profit_max` |
| p. 153, (i) | Price-dependent objectives differ | `price_dependence_example` |
| p. 153, (ii)-(iii), footnote 14 | Uncertainty, managers | Verbal |
| Exercise 5.G.1(a)-(c), p. 164 | Quasilinear owners | `exercise_5_G_1a`, `exercise_5_G_1b`, `exercise_5_G_1c`, `exercise_5_G_1c_not_profit` (correction 10) |

## Appendix A: the linear activity model

| Source | Claim | Lean |
| --- | --- | --- |
| p. 154 | Activities, `Y` a polyhedral cone, disposal activities | `coneOf`, `withDisposal`, `activity_convexCone` |
| p. 154 | Profit max exists iff `p·a_m ≤ 0`; `p ≥ 0` with disposal | `activity_profit`, `activity_supply_nonempty_iff`, `disposal_supply_nonempty_iff` |
| p. 154 | `p·a_m < 0` ⇒ `α_m = 0`; `y(p)` = cone of `A(p)` | `activity_level_zero`, `activity_supply_eq` |
| Figure 5.AA.1 | Two activities | Graphical |
| p. 155 | Efficient ⇒ profit max at `p ≫ 0` ("we shall not prove") | `linear_activity_efficient_pos_price` |
| pp. 155-156 | Leontief model, `A`, `b`, `Y`, productive | `leontiefMatrix`, `primaryReq`, `leontief_from_activities`, `leontiefSet`, `leontiefSet_eq_coneOf`, `Productive` |
| Proposition 5.AA.1, p. 156 | All-or-nothing | `proposition_5_AA_1` |
| Proof, p. 157 | Neumann series, `Aᴺ → 0`, `(I-A)⁻¹ ≥ 0` | `proposition_5_AA_1_neumann` (via Chapter 2 `theorem_M_D_5_v`) |
| Small type, p. 157 | Producible iff `ΣAⁿc` finite | `producible_iff_neumann_bounded` |
| Example 5.AA.1, p. 157, Figure 5.AA.3 | `A`, `(I-A)⁻¹`, productive iff `β < 1` | `example_5_AA_1` |
| p. 158 | LP production function; dual variables between one-sided marginal products | `lp_dual_supergradient`, `lp_dual_marginal_products` |
| Figure 5.AA.4, p. 159 | Unit isoquant; `V = {z ≥ α(2,1) + β(1,2), α + β ≥ 1}` | `aa1Acts`, `aa1Req`, `mem_aa1Req_iff`, `isClosed_aa1Req`, `aa1Req_nonneg` |
| Proposition 5.AA.2, p. 159 | Nonsubstitution theorem | `gensWithDisposal`, `proposition_5_AA_2` |
| p. 160 | Several primary factors | Verbal |

## Mathematical Appendix M.M: linear programming

| Source | Claim | Lean |
| --- | --- | --- |
| (M.M.1), p. 966, footnote 30 | Primal, general form | `primalFeasible`, `footnote_M_M_30` |
| (M.M.2), p. 967 | Dual | `dualFeasible` |
| (M.M.3), p. 967 | Weak duality | `equation_M_M_3` |
| Theorem M.M.1, p. 968 | Duality theorem | `theorem_M_M_1` (via `farkas`, `isClosed_coneOf`, `coneOf_caratheodory`) |
| (M.M.4), proof, footnote 31 | Complementary slackness; no CQ needed | `equation_M_M_4`; `theorem_M_M_1` has no CQ (correction 11, `theorem_M_M_1_proof_counterexample`) |
| Figures M.M.1-M.M.2, p. 968 | `x̄ = (1, 2)`, `λ̄ = (2/5, 1/5)`, value 3 | `example_M_M_figures` |
| (supporting) | Strictly positive separation (Stiemke) | `exists_pos_of_cone_inter_nonneg` |

## Exercises

| Source | Claim | Lean |
| --- | --- | --- |
| 5.B.1-5.B.3 | In text | See Section 5.B |
| 5.B.4 | Additive closure; not closed for DRS; closed for Figure 5.B.5(b) | `addClosure`, `exercise_5_B_4_closure`, `sqrtTech`, `exercise_5_B_4_not_closed`; closed case `exercise_5_B_4_closed` (via `b4_normal_form`, `b4_sum_mem_addClosure`), instance `sTech`, `exercise_5_B_4_closed_instance` (correction 18); representing `Y⁺` is graphical |
| 5.B.5 | Closed convex `⊇ -ℝ^L_+` ⇒ free disposal | `exercise_5_B_5` |
| 5.B.6(a) | The production set | `twoTechSet` |
| 5.B.6(b) | Subadditive `φ` ⇒ additive | `exercise_5_B_6b` |
| 5.B.6(c) | FOC, sufficiency for convex `φ` | `exercise_5_B_6c` |
| 5.B.6(d) | Strictly concave: one technique; isoquants graphical | `exercise_5_B_6d`, `exercise_5_B_6d_aux` |
| 5.C.1-5.C.5 | (In text / Prop 5.C.2) | See Section 5.C |
| 5.C.6(a)-(b) | `dq/dp > 0`, some input rises | `exercise_5_C_6_ab` |
| 5.C.6(c) | `∂z_ℓ/∂w_ℓ < 0` | `exercise_5_C_6_c` |
| 5.C.7 | Signs with cross partials | false as printed: `exercise_5_C_7_counterexample`; explicit demand `c7f`, `c7u`, `c7v`, `c7demand`, `c7f_technology`, `c7_foc`, `exercise_5_C_7_demand`, `exercise_5_C_7_explicit_counterexample`; corrected: two inputs `exercise_5_C_7_corrected`, `n` inputs `exercise_5_C_7_corrected_n` (via `negDef_offdiag_pos_solution_pos`), instance `c7H3`, `exercise_5_C_7_corrected_n_instance` (correction 12) |
| 5.C.8 | Inconsistent observations | `exercise_5_C_8` |
| 5.C.9(a)-(b) | Profit functions | `exercise_5_C_9a`, `exercise_5_C_9b` |
| 5.C.9(c) | CES with `ρ ≤ 1` | Constant returns: `exercise_5_C_10c` with `example_5_C_1_crs`-type trichotomy (verbal combination) |
| 5.C.10(a)-(c) | Cost functions | `exercise_5_C_10a`, `exercise_5_C_10b`, `exercise_5_C_10c` (`ρ ≠ 0`) |
| 5.C.11 | `∂z_ℓ/∂q > 0` iff MC increasing in `w_ℓ` | `exercise_5_C_11` |
| 5.C.12 | Entrepreneurial factor | `exercise_5_C_12` |
| 5.C.13 | `z₁ = αC/w₁` | `exercise_5_C_13` |
| 5.D.1-5.D.2 | In text | See Section 5.D |
| 5.D.3 | Long-run supply response ≥ short-run (Le Chatelier) | `exercise_5_D_3` (via `hotelling_1d`, `second_order_nonneg`), `exercise_5_D_3_instance`, `exercise_5_D_3_equal` (correction 16) |
| 5.D.4(a) | Decreasing AC ⇒ subadditive | `exercise_5_D_4a` |
| 5.D.4(b) | Decreasing ray average cost does not imply subadditivity | `Subadditive`, `DecreasingRayAC`, `cost4b`, `exercise_5_D_4b` (correction 17) |
| 5.D.4(c) | Decreasing ray AC + quasiconvex ⇒ subadditive | `exercise_5_D_4c`, `exercise_5_D_4c_instance` (correction 17) |
| 5.D.5(a) | IRS: average product nondecreasing; marginal product not | `exercise_5_D_5a_average`, `prod5a`, `exercise_5_D_5a_marginal` |
| 5.D.5(b) | MU = MC necessary | `exercise_5_D_5b` |
| 5.D.5(c) | Not sufficient | `exercise_5_D_5c` |
| 5.E.1-5.E.5 | See Section 5.E | |
| 5.F.1 | In text | `exercise_5_F_1` |
| 5.G.1 | See Section 5.G | |
| 5.AA.1 | `c(w, 1) = min(2w₂ + w₃, w₂ + 2w₃)`; `z(w, 1)`; `z = ∇_w c` where single-valued | `aa1_lower`, `aa1_mem_21`, `aa1_mem_12`, `aa1_dot`, `exercise_5_AA_1_cost`, `exercise_5_AA_1_demand`, `exercise_5_AA_1_gradient` |
| 5.AA.2(a)-(d) | Leontief efficiency and prices | `leontief_inverse_facts`, `exercise_5_AA_2a`, `exercise_5_AA_2b`, `exercise_5_AA_2c`, `exercise_5_AA_2d` |
| 5.AA.3(a)-(c) | PPF, prices, labour embodied | `exercise_5_AA_3` |
| 5.AA.3(d) | Locus of inputs | Graphical |
| 5.AA.3(e) | Switch at `β = 4` | `exercise_5_AA_3e` |
| 5.AA.4(a) | Membership | `aa4`, `aa4_coords`, `exercise_5_AA_4a` |
| 5.AA.4(b)-(c) | Efficient / inefficient | `exercise_5_AA_4bc` |
| 5.AA.5(a)-(c) | Convex, no free lunch, no free disposal | `aa5`, `exercise_5_AA_5abc`, `freeDisposal_withDisposal` |
| 5.AA.5(d) | Inefficient activities | `exercise_5_AA_5d`, `exercise_5_AA_5d_correction` (correction 13) |
| 5.AA.5(e) | `a₁`, `a₂` dominated | `exercise_5_AA_5e` |
| 5.AA.5(f) | Efficient set | `exercise_5_AA_5f` |
| 5.AA.5(g)-(h) | LP and its solution | `exercise_5_AA_5gh` |
