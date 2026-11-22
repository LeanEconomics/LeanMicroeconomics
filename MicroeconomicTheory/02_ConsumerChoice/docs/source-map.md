# Source map

Mas-Colell, Whinston and Green, *Microeconomic Theory*, Chapter 2, "Consumer Choice",
pp. 17-39, and Mathematical Appendix Sections M.A (pp. 926-927), M.B (pp. 928-929) and M.D
(pp. 935-940). Printed pages; Lean names relative to `MWG.ConsumerChoice`. Every definition,
proposition, example, small-type claim and exercise subpart of Sections 2.A-2.F and
Exercises 2.D.1-2.F.17 is accounted for below, as are the appendix sections. Vectors are
`Fin L → ℝ`; prices are strictly positive and wealth positive (`PWDomain`). Demand
derivatives are Fréchet derivatives `D` of `(p, w) ↦ x(p, w)` at the point in question
(`HasFDerivAt`), and `∂x_ℓ/∂p_k`, `∂x_ℓ/∂w` are `priceEffect D ℓ k`, `wealthEffect D ℓ`.
Notions coinciding with Kreps (Kreps Ch. 1 `Rational`, `PrefChoice`; Kreps Ch. 3
`NonnegativeOrthant`, `BudgetSet`) are imported with bridge theorems. MWG Chapter 1's choice
structures and weak axiom (`MWG.PreferenceChoice.ChoiceStructure`, `MWG.PreferenceChoice.WeakAxiom`)
are imported, and the Walrasian budget family is shown to be a choice structure. One item,
the converse direction of Exercise 2.F.3(e)-(f), remains OPEN; it is explained in the last
table.

## Sections 2.A-2.D: commodities, consumption sets, budgets

| Source | Claim | Lean |
| --- | --- | --- |
| Section 2.A, p. 17 | Introduction | Listed only (exposition) |
| Section 2.B, pp. 17-18; footnote 1 | Commodity vectors in `ℝ^L`; time and states as commodities; aggregation (small type) | Listed only (exposition); vectors are `Fin L → ℝ` throughout |
| Section 2.C, p. 19 | Consumption set `ℝ^L_+`; bridge to Kreps | `nonnegOrthant`, `mem_nonnegOrthant_iff`, `range_val_nonnegativeOrthant` |
| Footnote 2, p. 19 | Entries of a convex combination | `convexCombination_apply` |
| Section 2.C, p. 19 | `ℝ^L_+` is convex | `convex_nonnegOrthant` |
| Figures 2.C.1-2.C.6, pp. 19-20 | The six consumption sets | `figure_2_C_1_set` ... `figure_2_C_6_set` |
| Section 2.C, p. 20 | Sets of Figures 2.C.1, 2.C.4, 2.C.5, 2.C.6 convex; 2.C.2, 2.C.3 not | `convex_figure_2_C_1`, `convex_figure_2_C_4`, `convex_figure_2_C_5`, `convex_figure_2_C_6`, `not_convex_figure_2_C_2`, `not_convex_figure_2_C_3` |
| Footnote 3, p. 20 | Aggregation can convexify | Listed only (verbal) |
| Section 2.D, p. 20 | `p ≫ 0`; price taking | `StrictlyPositive`; price taking listed only |
| Definition 2.D.1, p. 21 | Walrasian budget set | `budgetSet`, `definition_2_D_1`; bridge `image_val_krepsBudgetSet` (Kreps Ch. 3 `BudgetSet`) |
| Footnote 4, p. 21 | Wealth vs income terminology | Listed only (terminology) |
| Section 2.D, p. 21 | `w = 0` leaves only `x = 0` | `budgetSet_zero_wealth` |
| Section 2.D, p. 21; Figure 2.D.1 | Budget hyperplane; slope `-(p₁/p₂)` | `budgetHyperplane`, `budgetLine_two_goods` |
| Figure 2.D.2, p. 21 | A fall in `p₂` enlarges the budget set and steepens the line | `budgetSet_subset_of_price_fall`, `budgetSet_ssubset_of_price_fall`, `budgetLine_steeper` |
| Figure 2.D.3, p. 22; footnote 5 | `p` orthogonal to the budget hyperplane | `budgetHyperplane_orthogonal`; footnote 5 listed only (drawing convention) |
| Section 2.D, p. 22 | `B_{p,w}` convex | `convex_budgetSet` |
| Figure 2.D.4, pp. 22-23 (small type) | Overtime/tax budget set | `figure_2_D_4_income`, `figure_2_D_4_consumption`, `figure_2_D_4_set` |
| Exercise 2.D.1, p. 36 | Lifetime budget is Walrasian (present-value prices) | `exercise_2_D_1` |
| Exercise 2.D.2, p. 36 | Consumption-leisure budget set | `exercise_2_D_2` |
| Exercise 2.D.3(a), p. 36 | Not convex with the Figure 2.C.3 set | `exercise_2_D_3a` (general `budgetSetOn`, `budgetSetOn_nonnegOrthant`) |
| Exercise 2.D.3(b), p. 36 | Convex `X` gives convex `B_{p,w}` | `exercise_2_D_3b` |
| Exercise 2.D.4, p. 36 | Figure 2.D.4 budget set not convex | `exercise_2_D_4` |

## Section 2.E: demand functions and comparative statics

| Source | Claim | Lean |
| --- | --- | --- |
| Section 2.E, p. 23 | Demand correspondence and function | `DemandCorrespondence`, `DemandFunction`, `PWDomain` |
| Definition 2.E.1, p. 23 | Homogeneity of degree zero | `HomogeneousZeroCorr`, `HomogeneousZero`, `homogeneousZero_iff_corr` |
| Section 2.E, p. 23 | `B_{αp,αw} = B_{p,w}` | `budgetSet_smul` |
| Definition 2.E.2, p. 23 | Walras' law | `WalrasLawCorr`, `WalrasLaw`, `walrasLaw_iff_corr` |
| Exercise 2.E.1, p. 23 | Homogeneous for every `β`; Walras' law iff `β = 1` | `demand_2_E_1`, `exercise_2_E_1_homogeneous`, `demand_2_E_1_expenditure`, `exercise_2_E_1_walras_iff` |
| Section 2.E, p. 24; footnote 6 | Normalisations `p_ℓ = 1`, `w = 1` | `normalize_price`, `normalize_wealth` |
| Section 2.E, p. 24 (small type) | `(𝓑^W, x(·))` is a choice structure; it omits two- and three-element sets | `walrasianBudgetFamily`, `vertex_mem_budgetSet`, `budgetSet_eq_imp_proportional`, `demand_depends_only_on_budget`, `budgetSet_infinite`, `finite_not_mem_walrasianBudgetFamily` |
| Section 2.E, pp. 24-26; footnote 7 | Engel function, expansion path, wealth/price effects, `D_w x`, `D_p x`, normal, inferior, Giffen | `engelFunction`, `wealthExpansionPath`, `priceEffect`, `wealthEffect`, `priceJacobian`, `wealthJacobian`, `prod_eq_sum_single`, `deriv_apply_eq`, `deriv_apply_eq_mulVec`, `NormalAt`, `InferiorAt`, `NormalDemand`, `GiffenAt`, `inferiorAt_iff_not_normalAt`, `priceEffect_fderiv` |
| Figures 2.E.1-2.E.4, pp. 25-26 | Expansion path, demand curves, offer curves, Giffen offer curve | Listed only (graphical); the potato story is verbal |
| Section 2.E, p. 27 | Differentiating `x(αp, αw) = x(p, w)` and `p·x(p, w) = w` | `hasDerivAt_line`, `hasDerivAt_path`, `hasDerivAt_path_apply`, `eventually_pwDomain`, `hasDerivAt_eq_zero_of_eventually_const`, `homogeneous_deriv_identity`, `walras_deriv_identity` |
| Proposition 2.E.1, p. 27; (2.E.1)-(2.E.3) | Homogeneity restriction, matrix and elasticity forms | `proposition_2_E_1`, `proposition_2_E_1_matrix`, `priceElasticity`, `wealthElasticity`, `proposition_2_E_1_elasticity` |
| Proposition 2.E.1, p. 27 | "Special case of Euler's formula" | Remark; Euler's formula is `theorem_M_B_2` (different domain), proof here is direct |
| Proposition 2.E.2, p. 28; (2.E.4)-(2.E.5); footnote 8 | Cournot aggregation | `proposition_2_E_2`, `proposition_2_E_2_matrix` |
| Proposition 2.E.3, p. 28; (2.E.6)-(2.E.7) | Engel aggregation | `proposition_2_E_3`, `proposition_2_E_3_matrix` |
| Exercise 2.E.2, p. 28 | Elasticity forms with budget shares | `budgetShare`, `exercise_2_E_2_price`, `exercise_2_E_2_wealth` |
| Exercise 2.E.3, p. 36 | `p·D_p x p = -w`; "interpret" | `exercise_2_E_3`, `exercise_2_E_3_via_homogeneity`; interpretation listed only |
| Exercise 2.E.4, pp. 36-37 | `ε_ℓw = 1`; `D_w x = x/w`; linear Engel functions; "interpret" | `HomogeneousOneInWealth`, `exercise_2_E_4`, `exercise_2_E_4_wealthJacobian`, `exercise_2_E_4_engel` (Walras' law not needed) |
| Exercise 2.E.5, p. 37 | `x_ℓ = α_ℓ w/p_ℓ` | `exercise_2_E_5` (corrected: `α_ℓ ≥ 0`, `∑ α_ℓ = 1`), `demand_eq_of_own_price_eq`; counterexample to `α_ℓ > 0`: `demand_2_E_5_counterexample`, `demand_2_E_5_counterexample_differentiableAt`, `exercise_2_E_5_alpha_pos_counterexample` |
| Exercise 2.E.6, p. 37 | Props. 2.E.1-2.E.3 hold for Exercise 2.E.1 demand, `β = 1` | `demand_2_E_1_differentiableAt`, `exercise_2_E_6` |
| Exercise 2.E.7, p. 37 | `x₂ = (1-α)w/p₂`; homogeneous | `exercise_2_E_7` |
| Exercise 2.E.8, p. 37 | Elasticities as log derivatives; log-linear estimation | `hasDerivAt_exp_price_curve`, `exercise_2_E_8_price`, `exercise_2_E_8_wealth`, `exercise_2_E_8_loglinear` |

## Section 2.F: the weak axiom and the law of demand

| Source | Claim | Lean |
| --- | --- | --- |
| Section 2.F, pp. 28-29; footnotes 9-10 | Standing assumptions; relation to Ch. 3 | Listed only (exposition) |
| Definition 2.F.1, p. 29 | Weak axiom for Walrasian demand | `WeakAxiom` |
| Figure 2.F.1, p. 30 | Permissible/impermissible pairs | `PairWeakAxiom`, `RevealedPreferred`, `pairWeakAxiom_of_weakAxiom`; figure listed (graphical) |
| Section 2.F, p. 30; Figure 2.F.2 | Slutsky compensation, compensated price change | `compensatedWealth`, `ValuesInOrthant`, `compensatedWealth_pos` |
| Proposition 2.F.1, pp. 30-32; (2.F.1)-(2.F.4) | WA ⟺ compensated law of demand | `CompensatedLawOfDemand`, `proposition_2_F_1_i`, `proposition_2_F_1_ii`, `proposition_2_F_1` |
| Pp. 31-32 (small type); Figure 2.F.3 | WA holds iff it holds for compensated changes | `weakAxiom_iff_compensated` |
| P. 32 | Own-price compensated change: `Δp_ℓ > 0 ⇒ Δx_ℓ < 0` | `own_price_compensated_law` (corrected); counterexample `leontiefDemand`, `leontiefDemand_walras`, `leontiefDemand_homogeneous`, `leontiefDemand_orthant`, `leontiefDemand_weakAxiom`, `own_price_strict_counterexample` |
| Figure 2.F.4, p. 33 | Compensated fall in `p_ℓ` cannot lower `x_ℓ` | `figure_2_F_4` |
| Figure 2.F.5, p. 33 | WA does not give the uncompensated law of demand | `figure_2_F_5`; the parenthetical on preference maximization is a forward reference to Ch. 3, listed only |
| (2.F.5)-(2.F.10), pp. 33-34 | Slutsky matrix; `S v` is the compensated derivative | `slutskyMatrix`, `slutskyMatrix_eq`, `slutskyMatrix_mulVec`, `hasDerivAt_nonpos_of_right_le` |
| Proposition 2.F.2, p. 34 | `S(p, w)` negative semidefinite | `proposition_2_F_2` |
| Definition (p. 34), footnote 11 | Negative (semi)definite without symmetry | `NegSemidef`, `NegDef` (see M.D) |
| P. 34 | `s_ℓℓ ≤ 0`; Giffen ⇒ inferior | `slutsky_diag_nonpos`, `giffen_imp_inferior` |
| P. 34 | `S` symmetric for `L = 2`, not in general | `exercise_2_F_11`; non-symmetry: `exercise_2_F_10a`, `exercise_2_F_15_not_symm` |
| Proposition 2.F.3, p. 35; Exercise 2.F.7 | `p·S = 0`, `S p = 0` | `proposition_2_F_3`, `exercise_2_F_7` |
| P. 35 | `S` singular, not negative definite | `slutsky_det_eq_zero`, `slutsky_not_negDef` |
| P. 35 (small type) | NSD `S` not sufficient for WA (Exercise 2.F.16) | `exercise_2_F_16b`, `exercise_2_F_16c` |
| P. 35 (small type) | Samuelson / Kihlstrom-Mas-Colell-Sonnenschein: `v·Sv < 0` for `v ≠ αp` suffices for WA | `samuelson_sufficiency`, `neg_at_one_of_deriv_neg_at_zeros` (hypotheses made explicit: correction 13) |
| P. 35 | Prop. 1.D.2 does not apply: `𝓑^W` lacks small sets | `finite_not_mem_walrasianBudgetFamily` |
| Example 2.F.1, p. 35; Exercise 2.F.2, p. 37 | Pairwise WA, revealed preference cycle, no rationalization | `example_2_F_1_prices`, `example_2_F_1_choices`, `example_2_F_1_walras`, `exercise_2_F_2_pairs`, `exercise_2_F_2_cycle`, `example_2_F_1_not_rationalizable` |
| P. 36 | Example only persuasive; summary (i)-(iii) | (i) `proposition_2_F_1`; (ii) `proposition_2_F_2`; (iii) `exercise_2_F_11`, `exercise_2_F_15_not_symm`; rest verbal |
| Exercise 2.F.1, p. 37 | Definition 2.F.1 = Definition 1.C.1 on Walrasian budgets | `zero_mem_budgetSet`, `walrasianChoiceStructure` (MWG Ch. 1 `ChoiceStructure`), `walrasianChoiceRule`, `walrasianChoiceRule_budgetSet`, `exercise_2_F_1` (MWG Ch. 1 `WeakAxiom`) |
| Exercise 2.F.3(a)-(d), p. 37 | Ranges of `y` | `exercise_2_F_3_p1`, `exercise_2_F_3_x1`, `exercise_2_F_3_p2`, `exercise_2_F_3_x2`, `exercise_2_F_3_w2`, `exercise_2_F_3_rp12`, `exercise_2_F_3_rp21`, `exercise_2_F_3a`, `exercise_2_F_3b`, `exercise_2_F_3c`, `exercise_2_F_3d` |
| Exercise 2.F.3(e)-(f), p. 37 | Inferior goods deduced (`y < 75`; `75 < y < 100`) | `exercise_2_F_3_compensated`, `exists_inferiorAt_of_decrease`, `exercise_2_F_3e`, `exercise_2_F_3f`, `exercise_2_F_3_inconsistent`, `exercise_2_F_3_homothetic_bound` (for `75 ≤ y ≤ 80` the data contradict the weak axiom, so the conclusion is vacuous; correction 14). The remaining "only these ranges" direction is explained in the last table |
| Exercise 2.F.4(a)-(c), pp. 37-38 | Laspeyres, Paasche, expenditure indices | `laspeyresQuantity`, `paascheQuantity`, `expenditureIndex`, `exercise_2_F_4a`, `exercise_2_F_4b`, `exercise_2_F_4c`; the GNP remark is verbal |
| Exercise 2.F.5, p. 38 | Uncompensated law of demand under homotheticity, finite and infinitesimal | `exercise_2_F_5`, `exercise_2_F_5_infinitesimal` |
| Exercise 2.F.6, p. 38 | WA tested at one wealth level | `exercise_2_F_6` |
| Exercise 2.F.8, p. 38 | `s̃_ℓk = ε_ℓk + ε_ℓw b_k` | `exercise_2_F_8` |
| Exercise 2.F.9(a), p. 38 | `A` vs `A + Aᵀ`; determinant condition necessary, not sufficient | `exercise_2_F_9a` (with `theorem_M_D_1_i`, `theorem_M_D_1_i_semidef`, `theorem_M_D_2_iii`) |
| Exercise 2.F.9(b), p. 38 | `L = 2`, rank 1: NSD iff a diagonal entry negative | `exercise_2_F_9b` |
| Exercise 2.F.10(a), p. 38 | `S` at `(1,1,1)`: NSD, not symmetric | `slutsky_2_E_1_mulVec`, `hasDerivAt_share_term`, `slutsky_mulVec_of_hasDerivAt`, `hasDerivAt_affine`, `exercise_2_F_10a_matrix`, `exercise_2_F_10a` |
| Exercise 2.F.10(b), p. 38 | WA fails (`S` not NSD at `(1,1,ε)`) | `exercise_2_F_10b_quadratic`, `exercise_2_F_10b` |
| Exercise 2.F.11, p. 38 | `L = 2`: `S` symmetric | `symmetric_of_two_by_two`, `exercise_2_F_11` |
| Exercise 2.F.12, p. 38 | Preference-generated demand satisfies WA | `exercise_2_F_12` (Kreps `Rational`, `PrefChoice`) |
| Exercise 2.F.13(a)-(d), pp. 38-39 | Multivalued demand: generalized WA, (*), generalized CLD, converse | `GeneralizedWeakAxiom`, `walrasianCorrStructure`, `exercise_2_F_13a`, `generalizedWeakAxiom_toCorrespondence_iff`, `dotProduct_pos_of_nonneg`, `exercise_2_F_13b`, `GeneralizedCompensatedLaw`, `exercise_2_F_13c`, `exercise_2_F_13d` |
| Exercise 2.F.14, p. 39 | WA ⇒ homogeneity | `exercise_2_F_14` |
| Exercise 2.F.15, p. 39 | Demand on `ℝ³`: WA, `v·Sv < 0` off `p`, `S` not symmetric | `demand_2_F_15`, `quadForm_pos`, `exercise_2_F_15_basic`, `exercise_2_F_15_unique`, `exercise_2_F_15_weakAxiom`, `demand_2_F_15_differentiableAt`, `slutsky_2_F_15_mulVec`, `exercise_2_F_15_quadratic`, `exercise_2_F_15_negDef_off_p`, `exercise_2_F_15_not_symm`; the note on `ℝ³_+` is verbal |
| Exercise 2.F.16(a)-(c), p. 39 | Homogeneous + Walras, violates WA, `v·Sv = 0` | `demand_2_F_16`, `exercise_2_F_16a`, `exercise_2_F_16b`, `demand_2_F_16_differentiableAt`, `exercise_2_F_16c` |
| Exercise 2.F.17(a)-(d), p. 39 | `x_k = w/∑p_ℓ`: homogeneous, Walras, WA; `S = 0`: NSD, not ND, symmetric | `demand_2_F_17`, `sum_prices_pos`, `exercise_2_F_17a`, `exercise_2_F_17b`, `exercise_2_F_17c`, `demand_2_F_17_differentiableAt`, `exercise_2_F_17d_zero`, `exercise_2_F_17d` |
| Exercises 2.E.1, 2.E.2, 2.F.7 | "In text" | As above |

## Mathematical Appendix M.A and M.B

| Source | Claim | Lean |
| --- | --- | --- |
| M.A, p. 926 | Column vectors, `x·y = xᵀy`, `x·A = xᵀA` | `dotProduct_eq_transpose_mul`, `vecMul_eq_transpose_mul` |
| M.A, pp. 926-927 | `Df(x)`, `∇f(x) = [Df(x)]ᵀ`, `D_x f(x, y)`, Hessian | `jacobian`, `jacobian_mulVec`, `gradientVec`, `gradient_eq_transpose_jacobian`, `fderiv_apply_eq_gradient_dot`, `partialJacobianFst`, `partialJacobianFst_apply`, `hessianMatrix` |
| (M.A.1), p. 927 | Chain rule | `equation_M_A_1` |
| (M.A.2)-(M.A.5), p. 927 | Product rules; `g Dh` rank one; (M.A.4) special case of (M.A.5) | `equation_M_A_2`, `equation_M_A_3`, `equation_M_A_4`, `equation_M_A_5`, `rank_vecMulVec_le_one` |
| Definition M.B.1, p. 928 | Homogeneity of degree `r` on `ℝ^N_+` | `HomogeneousOfDegree` |
| M.B, p. 928 | `x₁/x₂` degree 0; `(x₁x₂)^{1/2}` degree 1; normalisations | `example_M_B_quotient`, `example_M_B_sqrt`, `homogeneous_zero_normalize`, `homogeneous_one_normalize` |
| Theorem M.B.1, p. 928 | Partials homogeneous of degree `r - 1` (all of `ℝ^N_+`) | `interior_nonnegOrthant_nonempty`, `theorem_M_B_1`, `theorem_M_B_1_partial` |
| M.B, p. 928 | Example `∂(x₁x₂)^{1/2}/∂x₁` | `example_M_B_sqrt_partial` |
| M.B, pp. 928-929; footnote 1; Figure M.B.1 | Radial expansion of level sets; slopes constant on rays | `level_set_radial`, `level_set_slope_radial` |
| M.B, p. 929 | Homothetic functions: same level sets and slopes | `homothetic_level_sets`, `homothetic_slope_radial` |
| Theorem M.B.2, p. 929 | Euler's formula; degree-zero case | `theorem_M_B_2`, `euler_degree_zero` |

## Mathematical Appendix M.D

| Source | Claim | Lean |
| --- | --- | --- |
| Definition M.D.1, p. 935 | (Semi)definite matrices, positive versions; bridges to Mathlib | `NegSemidef`, `NegDef`, `PosSemidefMWG`, `PosDefMWG`, `posSemidefMWG_iff_neg`, `posDefMWG_iff_neg`, `NegDef.negSemidef`, `posSemidefMWG_iff_posSemidef`, `posDefMWG_iff_posDef` |
| M.D, p. 935 | Characteristic values; real for symmetric matrices | `IsCharacteristicValue`, `isCharacteristicValue_ofReal_iff`, `isCharacteristicValue_real` |
| Theorem M.D.1(i)-(iv), p. 936; footnote 7 | `M + Mᵀ`; eigenvalues; inverse; stability of `KM` | `dotProduct_transpose_mulVec`, `theorem_M_D_1_i`, `theorem_M_D_1_i_semidef`, `dotProduct_self_pos_of_ne_zero`, `theorem_M_D_1_ii`, `theorem_M_D_1_ii_complex`, `NegDef.det_ne_zero`, `NegDef.inv`, `theorem_M_D_1_iii`, `Stable`, `theorem_M_D_1_iv` |
| M.D, p. 936 | `ₜMₜ`, `M^π` | `leadingMinorMatrix`, `permuteMatrix` |
| Theorem M.D.2(i), pp. 936-937 | Sylvester's criterion (both directions) | `theorem_M_D_2_i`, `sylvester_posDef`, `quadratic_castSucc_split`, `leadingMinorMatrix_castSucc` |
| Theorem M.D.2(ii), pp. 936-937 | Semidefinite test with permutations; permutations needed | `theorem_M_D_2_ii`, `exists_perm_extend`, `principalMinor_eq_permuted`, `posSemidef_of_principal_minors`, `theorem_M_D_2_ii_permutations_needed` |
| Theorem M.D.2(iii), pp. 936-937; footnote 8 | Nonsymmetric necessity; P-matrices | `sum_extend_mul`, `quadratic_submatrix`, `NegDef.submatrix`, `NegSemidef.submatrix`, `PosDefMWG.det_ne_zero`, `PosDefMWG.det_pos`, `theorem_M_D_2_iii`, `IsPMatrix`, `negDef_neg_isPMatrix` |
| M.D, p. 937 | Non-sufficiency in the nonsymmetric case | `exercise_2_F_9a` |
| Example M.D.1, p. 937 | `2 × 2` ND/NSD criteria (matrix part; concavity via M.C.2 is outside these sections) | `quadratic_two_by_two`, `example_M_D_1_negDef`, `example_M_D_1_negSemidef` |
| M.D, p. 938; footnote 9 | Positive versions; `|-ₜMₜ| = (-1)^r |ₜMₜ|` | `posDefMWG_iff_neg`, `det_neg_eq_pow` |
| Theorem M.D.3(i), p. 938 | Bordered test for ND on a subspace | `borderedMatrix`; printed statement false: `theorem_M_D_3_i_counterexample`; corrected (top `S × S` block of `B` nonsingular): `theorem_M_D_3_i`, with `bordered`, `bordered_det_eq_zero_of_not_injective`, `bordered_det_ne_zero`, `posDefMWG_transpose_mul`, `posDefMWG_mul_transpose`, `bordered_sign_pos`, `bordered_det_eq`, `transpose_mulVec_extend`, `negDef_on_ker_submatrix`, `leadingRows_injective`, `leadingRows_transpose_injective` |
| Theorem M.D.3(ii), p. 938 | Bordered test for NSD on a subspace | True as printed (with `Bᵀz = 0`): `theorem_M_D_3_ii`; necessity needs no rank hypothesis (`theorem_M_D_3_ii_forward`); sufficiency uses rank `S` in the form "some `S` rows of `B` are independent". Supporting: `det_one_add_eq_sum_minors`, `det_add_diagonal_expansion`, `det_bordered_submatrix_disjSum`, `bordered_perturbation_expansion`, `card_le_of_mulVec_injective`, `transpose_injective_of_card_eq`, `bordered_sign_pos_square`, `det_bordered_reindex`, `bordered_sign_of_printed` |
| Example M.D.2, pp. 938-939 | `N = 2`, `S = 1` bordered determinant; `x₁x₂` | `example_M_D_2_det`, `example_M_D_2_line`, `example_M_D_2_negDef`, `example_M_D_2_negSemidef`, `example_M_D_2_product` (quasiconcavity via M.C.4 is outside these sections) |
| Theorem M.D.4(i)-(iii), p. 939 | Definiteness on `T_p` and of `M̂` | `quadratic_sub_smul`, `theorem_M_D_4_ii`, `extend_succAbove_self`, `extend_succAbove_restrict`, `theorem_M_D_4_iii`, `rank_le_of_two_kernel_vectors`, `theorem_M_D_4_i` |
| Definitions M.D.2-M.D.3, p. 939 | Dominant diagonal; gross substitute sign pattern | `DominantDiagonal`, `GrossSubstituteSign` |
| Theorem M.D.5(i)-(iv), pp. 939-940 | Nonsingularity; ND from dominance and gross substitutes | `theorem_M_D_5_i`, `theorem_M_D_5_ii`, `theorem_M_D_5_iii`, `theorem_M_D_5_iv` |
| Theorem M.D.5(v), p. 940 | Productive matrices: `(I - M)⁻¹ = ∑ Mᵏ` | `pow_entry_nonneg`, `theorem_M_D_5_v` |

## Open item

| Source | Status |
| --- | --- |
| Exercise 2.F.3(e)-(f), p. 37, converse | OPEN. Proved: the forcing directions (`exercise_2_F_3e`, `exercise_2_F_3f`); that `75 ≤ y ≤ 80` contradicts the weak axiom (`exercise_2_F_3_inconsistent`); and that a homothetic (degree-one-in-wealth) witness exists only if `y ≥ 120` (`exercise_2_F_3_homothetic_bound`). Missing: for each remaining `y`, a demand function on all of `ℝ²₊₊ × ℝ₊₊` that satisfies the weak axiom, Walras' law and homogeneity, reproduces both observations, and never makes the relevant good inferior. For `y > 80` the relevant good is good 1; for `y < 75` or `y ≥ 100` it is good 2. Quasilinear demand `u = x₁ + ax₂ - (b/2)x₂²` with `b = 0.2/(y-100)` reproduces the data and has no inferior good for `y > 100`; its weak axiom (via unique maximisers) was not formalised. For `80 < y ≤ 100` (good 2 must be inferior) and for `y < 75` (good 1 must be inferior), no witness was found. Homothetic and quasilinear forms are excluded there, and logistic-share forms with separable index failed. |
