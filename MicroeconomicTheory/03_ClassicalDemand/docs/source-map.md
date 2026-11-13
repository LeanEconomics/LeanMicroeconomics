# Source map

Mas-Colell, Whinston and Green, *Microeconomic Theory*, Chapter 3, "Classical Demand Theory".
This file covers **part A**: Sections 3.A-3.D (pp. 40-57), Exercises 3.B.1-3.D.8 (pp. 96-98)
and Mathematical Appendix Sections M.C (pp. 930-935), M.F (pp. 943-945), M.J (pp. 954-955) and
M.K (pp. 956-964). Sections 3.E-3.J and Appendix 3.A are appended below by later parts.
Printed pages; Lean names relative to `MWG.ClassicalDemand`. Bundles are `Fin L → ℝ`; a
preference is a relation on bundles and every property is stated on a consumption set `X`
(default `nonnegOrthant L` from MWG Ch. 2). `≻`, `∼` and `Represents` are Kreps Ch. 2's
`Strict`, `Indifferent`, `Represents` (bridges `rationalOn_iff_rational`,
`representsOn_iff_represents`). Budgets are MWG Ch. 2's `budgetSet`/`budgetSetOn`. Imported
results are named with their package: Kreps Ch. 2 `PreferenceProperties` (Debreu's theorem
`proposition_2_9`, the diagonal utility, continuity characterisations `proposition_1_14a/c`,
`lexicographic_not_representable`), Kreps Ch. 3 `ConsumerDemand` (Berge's theorem
`maximum_theorem`/`consumer_maximum_theorem`, `cobbDouglas_demand`), MWG Ch. 2
`MWGConsumerChoice` (`budgetSet_smul`, `convex_budgetSet`, `gradientVec`,
`fderiv_apply_eq_gradient_dot`, `NegSemidef`/`NegDef`), all at the worktree's current commit.
Items marked OPEN are listed in the last table. Modules `AppendixMCHessian`, `UtilityMore`, `UMPMore` close several items left open in the first pass.


## Open items (current status of the whole chapter)

This list is authoritative. The OPEN tables in the part sections below record each part's
state when it was written; items listed there were closed in later parts (E, F1, F2, F3, G),
whose sections give the Lean names.

| Source | Item | What is missing |
| --- | --- | --- |
| Footnote 29, p. 91 | The area variation can misrank two equal-revenue taxes even for small taxes | An explicit example; Cobb-Douglas preserves the ranking at leading order. A candidate three-good example and the remaining steps are in Part G. The footnote's Cobb-Douglas computation and the Figure 3.I.8 comparison are proved. |

## Section 3.A-3.B: preference relations

| Source | Claim | Lean |
| --- | --- | --- |
| Section 3.A, pp. 40-41 | Overview | Listed only (exposition) |
| Section 3.B, p. 41 | Consumption set `X ⊆ ℝ^L_+` | Preferences take `X` as a parameter |
| Definition 3.B.1, p. 42 | Rational on `X` | `RationalOn`, `rationalOn_iff_rational` |
| Definition 3.B.2, p. 42 | Monotone, strongly monotone | `PrefMonotone`, `PrefStronglyMonotone` |
| Definition 3.B.3, p. 42; footnote 3 | Local nonsatiation, Euclidean distance | `LocallyNonsatiated`, `euclidDist`, `abs_sub_le_euclidDist`, `dist_le_euclidDist`, `euclidDist_le_sqrt_mul_dist` |
| Footnote 2, p. 42 | Bads redefined as goods | Listed only (verbal) |
| Exercise 3.B.1(a), pp. 43, 96 | Strongly monotone ⇒ monotone | `exercise_3_B_1a` (needs `L ≥ 1`, correction 1) |
| Exercise 3.B.1(b), pp. 43, 96 | Monotone ⇒ locally nonsatiated | `exercise_3_B_1b`, `exercise_3_B_1b_orthant`; `exercise_3_B_1_needs_commodity` |
| Section 3.B, p. 43 | Indifference, upper and lower contour sets | `indifferenceSet`, `upperContour`, `lowerContour` |
| Section 3.B, p. 43 | LNS rules out all-bads and thick indifference sets (Fig. 3.B.2) | `locallyNonsatiated_not_all_bads`, `locallyNonsatiated_no_thick_indifference` |
| Definition 3.B.4, p. 44 | Convexity | `PrefConvex`, `definition_3_B_4`, `prefConvex_iff_of_convex` |
| Section 3.B, p. 44 | Diminishing MRS, diversification (verbal); `½x + ½y` no worse | Verbal parts listed; `half_mixture_of_prefConvex` |
| Small type, p. 44 | Convexity only possible for convex `X` | `convex_of_prefConvex` (for complete `≿`) |
| Definition 3.B.5, p. 44 | Strict convexity, strengthens convexity | `PrefStrictlyConvex`, `PrefStrictlyConvex.prefConvex` |
| Figure 3.B.4, p. 45 | Convex, not strictly convex | `figure_3_B_4` |
| Definition 3.B.6, p. 45 | Homothetic | `Homothetic` (monotonicity is a separate hypothesis) |
| Definition 3.B.7, p. 45; footnote 5 | Quasilinear w.r.t. any commodity `k` on `(-∞,∞) × ℝ^{L-1}_+` | `QuasilinearWrt`, `quasilinearDomain`, `unitVec` |
| Exercise 3.B.2, p. 96 | Transitive, LNS, weakly monotone ⇒ monotone | `exercise_3_B_2` |
| Exercise 3.B.3, p. 96 | Convex, LNS, not monotone (draw) | `exercise_3_B_3` (`u = x₁ - x₂`) |

## Section 3.C: preference and utility

| Source | Claim | Lean |
| --- | --- | --- |
| Example 3.C.1, p. 46 | Lexicographic order | `lexPref` |
| Example 3.C.1, p. 46; Exercise 3.C.1 | Complete, transitive, strongly monotone, strictly convex | `exercise_3_C_1_rational`, `exercise_3_C_1_stronglyMonotone`, `exercise_3_C_1_strictlyConvex` |
| Example 3.C.1, small type, p. 46 | No utility representation | `example_3_C_1_not_representable` (via Kreps `lexicographic_not_representable`) |
| Definition 3.C.1, p. 46 | Continuity (sequential, on `X`) | `PrefContinuous`; `prefContinuous_iff_continuousPreference` (Kreps `proposition_1_14a`) |
| Section 3.C, p. 47 | Continuity ⇒ closed contour sets | `PrefContinuous.isClosed_contours` |
| Example 3.C.1 continued, p. 47 | Lexicographic not continuous | `example_3_C_1_not_continuous` |
| Proposition 3.C.1, p. 47 | Continuous rational `≿` has a continuous utility | `proposition_3_C_1` (`ℝ^L_+`, Kreps `proposition_2_9`), `proposition_3_C_1_convex` (any convex `X`); general `X` OPEN |
| Proof of Prop. 3.C.1, pp. 47-49 (incl. small type) | Diagonal utility `α(x)e ∼ x`, represents, continuous | `proposition_3_C_1_monotone` (Kreps `DiagonalUtility`, `diagonalUtility_continuous`) |
| Section 3.C, p. 49 | Increasing transformations represent; discontinuous representations exist | `representsOn_comp_strictMono`, `discontinuous_representation` |
| Figure 3.C.3, p. 49 | Leontief preferences: no differentiable utility | `figure_3_C_3`, `leontiefUtility`, `directional_deriv_zero_of_const` |
| Section 3.C, p. 49 | `C²` utility assumed; smoothness of indifference sets | Listed only (convention) |
| Section 3.C, p. 49 | Monotone ⇒ `u(x) > u(y)` for `x ≫ y` | `utility_strict_of_monotone` |
| Section 3.C, pp. 49-50 | Convex ⟺ quasiconcave `u`; strictly convex ⟺ strictly quasiconcave | `prefConvex_iff_quasiconcaveOn`, `prefStrictlyConvex_iff_strictlyQuasiconcaveOn` |
| Section 3.C, p. 50 | A convex `≿` may have no concave utility | `convex_pref_no_concave_utility` |
| Section 3.C, p. 50 (i)-(ii); footnote 6 | Homothetic/quasilinear forms are cardinal | See Exercise 3.C.5 |
| Exercise 3.C.2, p. 96 | Continuous utility ⇒ continuous `≿` | `exercise_3_C_2` |
| Exercise 3.C.3, p. 96 | Closed contour sets ⇒ continuous | `exercise_3_C_3` (rational `≿`); `exercise_3_C_3_needs_rationality` (correction 3) |
| Exercise 3.C.4, p. 96 | Representable but not continuous | `exercise_3_C_4` |
| Exercise 3.C.5(a), p. 96 | Homothetic ⟺ HD1 utility | `exercise_3_C_5a_only_if` (monotone, `L ≥ 1`), `exercise_3_C_5a_if`, `HomogeneousOneOn` |
| Exercise 3.C.5(b), p. 96 | Quasilinear ⟺ `x₁ + φ(x₋₁)` | "if": `exercise_3_C_5b_if`; "only if" OPEN |
| Exercise 3.C.5, last sentence | Forms are cardinal | `exercise_3_C_5_cardinal_homogeneous`, `exercise_3_C_5_cardinal_quasilinear` |
| Exercise 3.C.6(a), p. 97 | CES at `ρ = 1` is linear | `exercise_3_C_6a` |
| Exercise 3.C.6(b), p. 97 | CES → Cobb-Douglas as `ρ → 0` | `exercise_3_C_6b`, `exercise_3_C_6b_transform`, `rpow_sub_one_div_tendsto` |
| Exercise 3.C.6(c), p. 97 | CES → Leontief as `ρ → -∞` | `exercise_3_C_6c`, `rpow_inv_tendsto_one` |

## Section 3.D: the utility maximization problem

| Source | Claim | Lean |
| --- | --- | --- |
| Section 3.D, p. 50 | UMP, Walrasian demand `x(p,w)`, preference version | `walrasianDemandOn`, `walrasianDemand`, `walrasianDemandPref`, `walrasianDemand_eq_pref_of_represents` |
| Proposition 3.D.1 and proof, pp. 50-51 | Existence; `B_{p,w}` compact | `proposition_3_D_1` (any `w ≥ 0`), `isCompact_budgetSet`, `budgetSet_coord_le` |
| Footnote 7, p. 51 | Terminology | Listed only |
| Proposition 3.D.2(i), p. 52 | Homogeneity of degree zero | `proposition_3_D_2_i`, `homogeneousZeroCorr_walrasianDemand` |
| Proposition 3.D.2(ii), p. 52 | Walras' law from LNS | `proposition_3_D_2_ii`, `walrasLawCorr_walrasianDemand`, `exists_better_affordable` |
| Proposition 3.D.2(iii), p. 52 | Convexity / uniqueness | `proposition_3_D_2_iii`, `proposition_3_D_2_iii_convex`, `proposition_3_D_2_iii_unique` |
| (3.D.1), p. 53; footnote 8 | Kuhn-Tucker conditions at any solution | `ump_kuhn_tucker` (no constraint qualification needed), `deriv_nonpos_of_feasible` |
| (3.D.2)-(3.D.4), p. 53 | Matrix form, interior form | `equations_3_D_2_3`, `equation_3_D_4` |
| (3.D.5), p. 54; footnote 9 | MRS = price ratio | `equation_3_D_5`; footnote 9 listed (verbal) |
| Section 3.D, pp. 54-55 | `λ` = marginal utility of wealth | `lagrange_multiplier_marginal_utility` |
| Footnote 10, p. 55 | `λ > 0` | `footnote_3_D_10` |
| Small type, p. 55 | KT conditions sufficient | `ump_kuhn_tucker_sufficient_quasiconcave` (book's hypotheses), `ump_kuhn_tucker_sufficient` (under (M.K.9)), `ump_kuhn_tucker_sufficient_concave`, `quasiconcave_gradient_pos`, `utility_mono_of_strict`; the local (bordered Hessian) remark listed only |
| Example 3.D.1, pp. 55-56 | Cobb-Douglas demand, expenditure shares | `example_3_D_1`, `example_3_D_1_shares`, `cobbDouglasUtility`, `cobbDouglasDemand` (via Kreps `cobbDouglas_demand`); correction 4 |
| Exercise 3.D.1, p. 56 | Three properties for CD demand | `exercise_3_D_1_homogeneous`, `exercise_3_D_1_walras`, `exercise_3_D_1_unique` |
| Section 3.D, p. 56 | Continuity of demand (App. A) | Deferred to part C (Appendix 3.A) |
| Section 3.D, p. 56 | Indirect utility `v(p,w)` | `indirectUtility`, `indirectUtilityOn`, `indirectUtility_eq_of_mem` |
| Proposition 3.D.3(i), p. 56 | HD0 | `proposition_3_D_3_i` |
| Proposition 3.D.3(ii), p. 56 | Strictly increasing in `w`, nonincreasing in `p` | `proposition_3_D_3_ii_wealth`, `proposition_3_D_3_ii_prices` |
| Proposition 3.D.3(iii), pp. 56-57; footnote 11 | Quasiconvex | `proposition_3_D_3_iii` |
| Proposition 3.D.3(iv), p. 56 | Continuous (proof omitted in book) | `proposition_3_D_3_iv` (Kreps `consumer_maximum_theorem`) |
| Section 3.D, p. 57 | `ṽ = f(v)` | `indirectUtility_comp` |
| Example 3.D.2, p. 57 | Indirect utility of log Cobb-Douglas | `example_3_D_2`, `example_3_D_2_log`, `cobbDouglasIndirect`, `cobbDouglasLogIndirect` |
| Exercise 3.D.2, p. 57 | Four properties | `exercise_3_D_2_i`, `exercise_3_D_2_ii`, `exercise_3_D_2_iii`, `exercise_3_D_2_iv` |
| Exercise 3.D.3(a), p. 97 | HD1 `u` ⇒ HD1 demand and `v`, ray, unit elasticities | `exercise_3_D_3a_demand`, `exercise_3_D_3a_indirect`, `exercise_3_D_3a_forms`, `exercise_3_D_3a_ray`, `exercise_3_D_3a_elasticity` |
| Exercise 3.D.3(b), p. 97 | HD1 `v` ⇒ HD1 `u` | `exercise_3_D_3b_full` (with `∇u ≫ 0` on `ℝ^L_{++}`, correction 14), `demanded_at_supporting_prices`, `exercise_3_D_3b` |
| Exercise 3.D.4(a), p. 97 | Quasilinear: goods 2..L wealth-independent, unit wealth effect on good 1 | `exercise_3_D_4a`, `exercise_3_D_4a_independent` (utility `x₁ + φ`) |
| Exercise 3.D.4(b), p. 97 | `v = w + φ(p)` | `exercise_3_D_4b` |
| Exercise 3.D.4(c), p. 97 | Nonnegative numeraire; when the constraint is irrelevant | `exercise_3_D_4c_high`, `exercise_3_D_4c_low`, `exercise_3_D_4c_irrelevant`, `concave_mono_left_of_max` (proved directly; Kreps `QuasiLinearWealth` not needed) |
| Exercise 3.D.5(a)-(d), p. 97 | CES demand, properties, limits, elasticity of substitution | OPEN |
| Exercise 3.D.6(a)-(c), p. 98 | Linear expenditure system | OPEN |
| Exercise 3.D.7(a)-(e), p. 98 | Revealed-preference regions (graphical) | OPEN |
| Exercise 3.D.8, p. 98 | `w ∂v/∂w = -p·∇_p v` | `exercise_3_D_8` |

## Mathematical Appendix M.C: concave and quasiconcave functions

| Source | Claim | Lean |
| --- | --- | --- |
| Definition M.C.1, p. 930 | Concave, strictly concave | `definition_M_C_1`, `definition_M_C_1_strict` (Mathlib `ConcaveOn`) |
| (M.C.2), p. 931 | Finite Jensen | `equation_M_C_2` |
| (M.C.3), p. 931 (small type) | Jensen for distributions | Listed only |
| Section M.C, p. 931 | Convex iff `-f` concave | `concaveOn_iff_neg_convexOn` |
| Theorem M.C.1, p. 931 | Gradient inequality | `theorem_M_C_1`, `theorem_M_C_1_necessity`, `theorem_M_C_1_sufficiency`, `theorem_M_C_1_strict`, `theorem_M_C_1_convex` |
| Definition M.C.2, p. 932 | (Semi)definite matrices | MWG Ch. 2 `NegSemidef`, `NegDef` |
| Theorem M.C.2, p. 933 | Concave ⟺ `D²f` NSD; ND ⇒ strictly concave | `theorem_M_C_2`, `theorem_M_C_2_strict`, `mc_eventually_gt_of_quad_pos`, `mc_line_second_deriv_at` |
| Section M.C, p. 933 | `-x⁴` strictly concave, `f''(0) = 0` | `neg_pow_four_strictConcave` |
| Definition M.C.3, p. 933 | Quasiconcave, strictly; quasiconvex | `definition_M_C_3`, `StrictlyQuasiconcaveOn`, `StrictlyQuasiconvexOn`, `strictlyQuasiconcaveOn_iff_min`, `quasiconcaveOn_iff_neg_quasiconvexOn`, `strictlyQuasiconcaveOn_iff_neg` |
| (M.C.7), p. 934 | Minimum form | `equation_M_C_7` |
| Section M.C, p. 934 | Concave ⇒ quasiconcave, not conversely; ordinal vs cardinal | `quasiconcaveOn_of_concaveOn`, `quasiconcave_not_concave_cube`, `quasiconcaveOn_monotone_comp`, `concave_not_preserved` |
| Theorem M.C.3, p. 934 | (M.C.8) characterisation; strict parts; `x³` | `theorem_M_C_3`, `theorem_M_C_3_necessity`, `theorem_M_C_3_sufficiency`, `theorem_M_C_3_strict_sufficiency`, `theorem_M_C_3_strict_necessity`, `theorem_M_C_3_cube` |
| Theorem M.C.4, p. 935 | Hessian on `{z : ∇f·z = 0}` | `theorem_M_C_4_necessity`, `theorem_M_C_4_strict`; printed "if" false: `theorem_M_C_4_if_false` (correction 6) |

## Mathematical Appendix M.F: continuous functions and compact sets

| Source | Claim | Lean |
| --- | --- | --- |
| Definition M.F.1, p. 943 | Convergence | `definition_M_F_1` |
| Definition M.F.2, p. 943 | Continuity (sequential), coordinates | `definition_M_F_2`, `definition_M_F_2_coord` |
| Definition M.F.3, pp. 943-944; Theorem M.F.1(i)-(ii) | Relatively open/closed sets, unions/intersections | Listed only (Mathlib subspace topology) |
| Theorem M.F.1(iii), p. 944 | Closed ⟺ sequentially closed | `theorem_M_F_1_iii` (`X = ℝ^N`) |
| Section M.F, p. 945 | Relative interior, closure, boundary | Listed only (Mathlib `interior`, `closure`, `frontier`) |
| Definition M.F.4, p. 945 | Bounded, compact | `EuclidBounded`, `definition_M_F_4` |
| Theorem M.F.2, p. 945 | Images; maximizers | `theorem_M_F_2_i`, `theorem_M_F_2_ii` |
| Theorem M.F.3, p. 945 | Convergent subsequences; discrete compact sets finite | `theorem_M_F_3_i`, `theorem_M_F_3_ii` |

## Mathematical Appendix M.J: unconstrained maximization

| Source | Claim | Lean |
| --- | --- | --- |
| Definition M.J.1, p. 954 | Local/global maximizer | `definition_M_J_1_local`, `definition_M_J_1_global` |
| Theorem M.J.1, p. 954 | `∇f(x̄) = 0` | `theorem_M_J_1` |
| Section M.J, p. 955 | `x₁² - x₂²` saddle | `saddle_not_extremum` |
| Theorem M.J.2(i)-(ii), p. 955 | Second-order conditions; minimizer versions | `theorem_M_J_2_i`, `theorem_M_J_2_i_min`, `theorem_M_J_2_ii`, `theorem_M_J_2_ii_strict`, `hessianMatrix`, `hessianMatrix_quad`; misprint: `theorem_M_J_2_printed_counterexample` (correction 5); minimizer version of (ii) listed (apply to `-f`) |
| Section M.J, p. 955 | `x³`: semidefinite not sufficient | `cube_semidefinite_not_extremum` |
| Theorem M.J.3, p. 955; footnote 21 | Critical points of concave/convex functions | `theorem_M_J_3`, `theorem_M_J_3_convex` |

## Mathematical Appendix M.K: constrained maximization

| Source | Claim | Lean |
| --- | --- | --- |
| Section M.K, p. 956 | Constraint set, local constrained maximizer | `eqConstraintSet`, `local_constrained_maximizer_iff` |
| Theorem M.K.1, (M.K.2)-(M.K.3), p. 956 | Lagrange multipliers under rank condition | `theorem_M_K_1`, `equation_M_K_2` (strict differentiability, correction 7) |
| Figure M.K.1, pp. 957-958 | CQ indispensable | `figure_M_K_1` |
| Section M.K, p. 958 | Lagrangian and its FOCs | `lagrangian`, `lagrangian_hasFDerivAt_x`, `lagrangian_hasDerivAt_lam`, `lagrangian_stationary_iff` |
| Section M.K, p. 958 | Second-order conditions on the tangent subspace | OPEN |
| (M.K.4), pp. 958-959 | Inequality-constrained problem, CQ on binding constraints | `kktConstraintSet` |
| Theorem M.K.2, p. 959 | Kuhn-Tucker conditions | `theorem_M_K_2` (general `M`, `K`), `mk_curve`, `mk_range_pi_eq_top` |
| (M.K.8), pp. 960-961 | Nonnegativity constraints | `equation_M_K_8_iff` |
| Section M.K, p. 961 | `h_k ≥ c_k`; minimization signs | `theorem_M_K_2_min`; `≥`-constraint version listed (apply `theorem_M_K_2` to `-h_k`) |
| Theorem M.K.3, p. 961; footnotes 23-24 | Sufficiency | `theorem_M_K_3`; linear equality constraints (fn. 23) and the minimizer version (fn. 24) listed |
| Section M.K, p. 962; footnote 25 | (M.K.9) for concave or quasiconcave `f` with `∇f ≠ 0`; convex `C` | `MK9_of_concave`, `MK9_of_quasiconcave`, `convex_constraintSet_of_quasiconvex`; fn. 25 CQ remark listed |
| Figure M.K.4, p. 962 | (M.K.9) indispensable | `figure_M_K_4` |
| Theorem M.K.4, p. 962; footnote 26 | At most one maximizer; convex set of maximizers | `theorem_M_K_4`, `theorem_M_K_4_no_existence` (correction 8), `footnote_M_K_26` |
| Small type (i)-(ii), pp. 962-963 | Dropping constraints | `drop_constraint_i`, `drop_constraint_ii` |
| Theorem M.K.5, p. 963; footnote 27 | Shadow prices | `theorem_M_K_5` (equality constraints); inequality constraints OPEN |
| Theorem M.K.6, p. 963 | Theorem of the maximum | `theorem_M_K_6` (Kreps `maximum_theorem`; correction 9) |
| Small type, p. 964 | `x₁ + x₂` example: uhc but not continuous; fails on `[0,1]²` | OPEN |

## OPEN items

| Item | What is missing |
| --- | --- |
| Proposition 3.C.1 for a general consumption set `X` | The book states it for any `X ⊆ ℝ^L_+` but proves only `X = ℝ^L_+`. Proved here for `ℝ^L_+` and every convex `X`; the general (possibly disconnected) case is Debreu's theorem, which needs the open-gap lemma, not available in Mathlib or the dependencies |
| Exercise 3.C.5(b), "only if" | Existence of an `x₁ + φ(x₋₁)` representation for a continuous quasilinear `≿`; needs a connectedness argument showing every indifference class meets the numeraire axis |
| Exercises 3.D.5(a)-(d), 3.D.6(a)-(c), 3.D.7(a)-(e) | Not formalized (CES and Stone-Geary demand computations; revealed-preference regions requiring constructed rationalizations) |
| Theorems M.K.1/M.K.2 for merely differentiable functions | Halkin (1974), via Brouwer's fixed point theorem; proved here for strictly differentiable (`C¹`) functions. Not attempted to completion |
| Second-order conditions, p. 958 | Need a second-order expansion along the implicit-function curve (`mk_curve` gives only first order) |
| Theorem M.K.5 with inequality constraints | Same argument as `theorem_M_K_5` with parameters `(b̄, c̄)`; not written |
| Small type, p. 964 example | Maximizer sets of `x₁ + x₂` on `[0,1]²` with `q₁x₁ + q₂x₂ ≤ q₁q₂`; not written |

## Part B: 3.E-3.G, M.E, M.G, M.L

Mas-Colell, Whinston and Green, *Microeconomic Theory*, Chapter 3, **part B**: Sections 3.E
(the expenditure minimization problem), 3.F (duality: a mathematical introduction) and 3.G
(relationships between demand, indirect utility and expenditure functions), pp. 57-75; the
end-of-chapter Exercises 3.E.1-3.G.18 (pp. 98-102); and Mathematical Appendix Sections M.E
(implicit function theorem, pp. 940-943), M.G (convex sets and separating hyperplanes,
pp. 946-949) and M.L (the envelope theorem, pp. 964-966). Printed pages; Lean names relative
to `MWG.ClassicalDemand`. The EMP is posed on `ℝ^L_+` (part A's `nonnegOrthant`) for a utility
`u` representing `≿` (part A's `RepresentsOn`); the expenditure function is by definition the
support function of `{x ∈ ℝ^L_+ : u(x) ≥ ū}`. The book's extended-real support function
(value `-∞`) is `supportFnE`; `supportFn` is its real version. Derivatives are Mathlib's
`HasFDerivAt`; gradients, Jacobians, the Slutsky matrix and negative semidefiniteness are MWG
Chapter 2's `gradientVec`, `jacobian`, `slutskyMatrix`, `NegSemidef`, `hessianMatrix`. Items
marked OPEN are collected in the last table; departures are in
[corrections-B](corrections.md).

### Section 3.E: the expenditure minimization problem

| Source | Claim | Lean |
| --- | --- | --- |
| Section 3.E, p. 58 | The EMP, its constraint set, Hicksian demand `h(p, ū)`, expenditure function `e(p, ū)` | `empConstraintSet`, `hicksianDemand`, `expenditure`, `mem_hicksianDemand_iff`, `expenditure_eq_of_mem` |
| Footnote 12, p. 57 | `u(0)` and the restriction `ū > u(0)` | Hypotheses `u 0 < ub` where used |
| Footnote 13, p. 58; Figure 3.E.1 | "Dual" terminology; EMP picture | Listed only (verbal, graphical) |
| Proposition 3.E.1(i), p. 58 | UMP solution solves the EMP at `u(x*)`, minimized expenditure `w` | `proposition_3_E_1_i` |
| Proposition 3.E.1(ii), pp. 58-59 | EMP solution solves the UMP at `p·x*`, maximized utility `ū` | `proposition_3_E_1_ii`, `exp_dotProduct_pos`, `exp_exists_scale_down` |
| Section 3.E, p. 59; Exercise 3.E.3, p. 98 | Existence when the constraint set is nonempty | `exercise_3_E_3`, `isClosed_empConstraintSet` |
| Section 3.E, p. 59 | Nonempty for every `ū > u(0)` if `u` is unbounded above | Listed (immediate) |
| Section 3.E, p. 59 | `e(p, ū) = p·x*` | `expenditure_eq_of_mem`, `expenditure_nonneg` |
| Proposition 3.E.2(i), p. 59 | Homogeneous of degree one in `p` | `proposition_3_E_2_i` |
| Proposition 3.E.2(ii), p. 59 | Strictly increasing in `ū`, nondecreasing in `p_l` | `proposition_3_E_2_ii_utility`, `proposition_3_E_2_ii_prices` |
| Proposition 3.E.2(iii), p. 60 | Concave in `p` | `proposition_3_E_2_iii`, `exp_convex_strictlyPositive` |
| Proposition 3.E.2(iv), p. 59 | Continuous in `(p, ū)` (proof omitted in the book) | `proposition_3_E_2_iv`, `expDomain`, `lt_expenditure_iff`, `expenditure_lt_iff`, `exp_continuousAt_indirectUtility_prices`, `exp_indirectUtility_zero_wealth` |
| Section 3.E, p. 60; Figure 3.E.2 | `e(·, ū)` lies below `p ↦ p·x̄` and touches it at `p̄` | `expenditure_le_linear` |
| Equation (3.E.1), p. 60 | `e(p, v(p, w)) = w`, `v(p, e(p, ū)) = ū` | `equation_3_E_1_left`, `equation_3_E_1_right`, `exp_indirectUtility_ge_zero` |
| Section 3.E, pp. 60-61 | Hicksian demand correspondence; Figure 3.E.3 | `hicksianDemand`; figure listed |
| Proposition 3.E.3(i), p. 61 | `h(αp, ū) = h(p, ū)` | `proposition_3_E_3_i` |
| Proposition 3.E.3(ii), p. 61 | No excess utility | `proposition_3_E_3_ii` (for `ū ≥ u(0)`) |
| Proposition 3.E.3(iii), p. 61 | Convexity / uniqueness | `proposition_3_E_3_iii`, `exercise_3_E_4_convex`, `exercise_3_E_4_unique` |
| Exercise 3.E.1, p. 61 | First-order conditions (3.E.2)-(3.E.3); comparison with the UMP | `exercise_3_E_1` (multiplier `1/λ`), `exercise_3_E_1_lam_pos`; `exercise_3_E_1_counterexample` (correction B2) |
| Small type, p. 62 | Continuity/differentiability of `h` not discussed | Listed only |
| Equation (3.E.4), p. 62 | `h(p, ū) = x(p, e(p, ū))`, `x(p, w) = h(p, v(p, w))` | `equation_3_E_4_left`, `equation_3_E_4_right` |
| Section 3.E, p. 62; Figure 3.E.4 | Hicksian wealth compensation `e(p', ū) - w` | Listed (definition); see `hicks_le_slutsky_compensation` |
| Proposition 3.E.4, (3.E.5), pp. 62-63 | Compensated law of demand | `proposition_3_E_4` (any selections) |
| Section 3.E, p. 63 | Compensated own-price effects nonpositive | `compensated_own_price` |
| Section 3.E, p. 63 | Walrasian demand need not satisfy the law of demand | Listed (Giffen goods, MWG Ch. 2) |
| Example 3.E.1, p. 63 | Cobb-Douglas `h(p, ū)`, `e(p, ū)` | `example_3_E_1`, `cdExpenditure_eq_book`, `cdHicksian_eq_book`, `cdConst`, `cobbDouglasIndirect_eq`, `cobbDouglas_continuousOn`, `cobbDouglas_lns` |
| Exercise 3.E.2, p. 63 | Cobb-Douglas satisfies Propositions 3.E.2-3.E.3 | `exercise_3_E_2` |

### Section 3.F: duality

| Source | Claim | Lean |
| --- | --- | --- |
| Section 3.F, p. 63 | Convex sets; intersections of convex sets are convex | `convex_inter_section_3_F` (Mathlib `Convex`) |
| Section 3.F, p. 64; Figure 3.F.1 | Half-space, hyperplane, normal vector; both convex | `halfSpace`, `hyperplane`, `hyperplane_normal`, `convex_halfSpace`, `convex_hyperplane`, `isClosed_halfSpace` |
| Section 3.F, p. 64 | Separating hyperplane theorem (as used) | `separation_section_3_F` (Mathlib `geometric_hahn_banach_point_closed`) |
| Section 3.F, pp. 64-65; Figure 3.F.2 | Closed convex `K` = intersection of half-spaces containing it; for any `K`, the closed convex hull | `halfspace_inter_eq_closure`, `exercise_3_F_1`, `exercise_3_F_1_halfspaces` |
| Definition 3.F.1, p. 64 | Support function `μ_K(p) = inf {p·x : x ∈ K}` | `supportFn`, `supportFnE`, `supportFnE_eq_coe`, `supportFnE_eq_bot`, `supportArgmin`, `eq_supportFnE_iff`, `supportFn_eq_of_mem_argmin`, `supportFn_le`, `le_supportFn` |
| Section 3.F, p. 65 | Infimum vs minimum; value `-∞` | `supportFnE_eq_bot`; rest listed (exposition) |
| Section 3.F, p. 65 | `K = {x : p·x ≥ μ_K(p) ∀p}`; nonconvex case gives the closed convex hull | `exercise_3_F_1`, `halfspace_inter_eq_closure`, `subset_supportHalfSpace` |
| Section 3.F, p. 65; Figure 3.F.3 | `μ_K` homogeneous of degree one and concave (lower envelope) | `supportFn_smul`, `supportFn_concaveOn`, `convex_supportDomain` |
| Proposition 3.F.1, p. 66 | Duality theorem: unique minimizer ⟺ differentiable; `∇μ_K(p̄) = x̄` | `proposition_3_F_1` (closed convex `K`), `SupportDifferentiableAt`, `duality_unique_of_differentiable` (every closed `K`), `duality_differentiable_of_unique`, `duality_key_estimate`, `supportFn_bounded_sublevel`; counterexample `proposition_3_F_1_nonconvex_counterexample`, `dualityCounterexampleSet` (correction B1) |
| Section 3.F, p. 66; footnote 14 | `ξ(p) = p·x̄ - μ_K(p)` is minimized at `p̄`; differentiable only if the minimizer is unique | `footnote_3_F_14` |
| Section 3.F, p. 66 | The expenditure function is the support function of `{u ≥ ū}`; HD1 and concavity follow | `expenditure_eq_supportFn`, `proposition_3_E_2_i`, `proposition_3_E_2_iii` |
| Small type, pp. 66-67; Figure 3.F.4 | Strictly convex `K`, unique minimizer `(1, 1)` at `(½, ½)`, slope 1 | Listed (graphical); the instance is Example 3.E.1 with `α = ½`, `ū = 1` |
| Small type, pp. 66-67; Figure 3.F.5 | Kink; one-sided derivatives equal the range of minimizers | OPEN |
| Exercise 3.F.1, p. 99 | Closed convex set = intersection of half-spaces | `exercise_3_F_1`, `exercise_3_F_1_halfspaces` (`L ≥ 1`) |
| Exercise 3.F.2, p. 99 | Separation fails for nonconvex sets; some `x ∉ K` cannot be separated | `exercise_3_F_2_example` (`K = {0, 2} ⊆ ℝ`), `exercise_3_F_2` (closedness not needed) |

### Section 3.G: demand, indirect utility and expenditure functions

| Source | Claim | Lean |
| --- | --- | --- |
| Section 3.G, pp. 67-68; footnote 15 | Standing assumptions; strict convexity makes demands single-valued; local version | Hypotheses (`PrefStrictlyConvex`); footnote 15 listed |
| Proposition 3.G.1, (3.G.1), p. 68 | Shephard's lemma `h(p, ū) = ∇_p e(p, ū)` | `proposition_3_G_1`, `shephard_lemma`, `convex_empConstraintSet` |
| Proof 1, p. 68 | Via the duality theorem | The proof of `shephard_lemma` (`duality_differentiable_of_unique`) |
| Proofs 2-3, pp. 68-69; footnote 16 | First-order-conditions and envelope proofs | Listed; Proof 3's envelope step is `envelope_objective_only` |
| Proposition 3.G.2(i), p. 69 | `D_p h = D²_p e` | `proposition_3_G_2_i`, `eventually_hasFDerivAt_expenditure` |
| Proposition 3.G.2(ii), p. 69 | `D_p h` negative semidefinite | `proposition_3_G_2_ii` (from (3.E.5), as on p. 70) |
| Proposition 3.G.2(iii), p. 69 | `D_p h` symmetric | `proposition_3_G_2_iii`, `dualityDotLin` (Mathlib `second_derivative_symmetric_of_eventually`) |
| Proposition 3.G.2(iv), p. 69 | `D_p h(p, ū) p = 0` | `proposition_3_G_2_iv` |
| Section 3.G, p. 70 | Differential compensated law; `∂h_l/∂p_l ≤ 0` | `proposition_3_G_2_ii` (diagonal: inside `every_good_has_substitute`) |
| Section 3.G, p. 70; footnote 17 | Symmetry as path independence | Listed (verbal) |
| Section 3.G, p. 70 | Substitutes/complements; every good has a substitute | Definitions listed; `every_good_has_substitute` |
| Proposition 3.G.3, (3.G.3)-(3.G.4), p. 71 | Slutsky equation | `proposition_3_G_3`, `jacobian_slutsky_comp`, `relations_indirectUtility_gt_zero` |
| Figure 3.G.1, pp. 71-72 | Normal/inferior goods and demand slopes | Listed (graphical) |
| Section 3.G, p. 72 | `S(p, w)` negative semidefinite, symmetric, `S(p, w)p = 0` | `slutsky_matrix_properties` |
| Small type, p. 72; Figure 3.G.2 | `Δw_Hicks ≤ Δw_Slutsky`; equal derivatives | `hicks_le_slutsky_compensation`; derivative equality is `proposition_3_G_3` |
| Section 3.G, p. 73 | Preferences cannot rationalize an asymmetric `S` | `no_rationalization_of_asymmetric_slutsky` |
| Proposition 3.G.4, p. 73 | Roy's identity | `proposition_3_G_4` (needs `∂v/∂w ≠ 0`); `proposition_3_G_4_printed_counterexample`, `royCounterexampleUtility`, `royCounterexample_demand`, `relations_cube_strictMono` (correction B4) |
| Proof 1, p. 74 | Differentiate `v(p, e(p, ū)) = ū` | The proof of `proposition_3_G_4` |
| Proofs 2-3, p. 74 | First-order-conditions and envelope proofs | Listed |
| Section 3.G, p. 75 | Gorman form gives linear expansion paths | `exercise_3_G_11` |
| Figure 3.G.3, p. 75 | Summary diagram | Listed (graphical) |

### Exercises 3.E-3.G (pp. 98-102)

| Source | Claim | Lean |
| --- | --- | --- |
| Exercise 3.E.1 | In text | See Section 3.E |
| Exercise 3.E.2 | In text | `exercise_3_E_2` |
| Exercise 3.E.3 | EMP solution exists | `exercise_3_E_3` |
| Exercise 3.E.4 | Convex `≿` ⇒ `h` convex; strictly convex ⇒ single-valued | `exercise_3_E_4_convex`, `exercise_3_E_4_unique`; as printed false: `exercise_3_E_4_printed_counterexample`, `exercise_3_E_4_utility` (correction B3) |
| Exercise 3.E.5 | HD1 `u` ⇒ `h(p, ū) = ū h(p, 1)`, `e(p, ū) = ū e(p, 1)` | `exercise_3_E_5_hicksian`, `exercise_3_E_5_expenditure`, `exp_homogeneousOneOn_zero` |
| Exercise 3.E.6 | CES Hicksian demand and expenditure function | OPEN |
| Exercise 3.E.7 | Quasilinear: `h_l`, `l ≠ 1`, independent of `ū`; form of `e` | `exercise_3_E_7`, `exercise_3_E_7_expenditure`, `hicksianDemandOn` (utility `x_k + φ(x)`) |
| Exercise 3.E.8 | Cobb-Douglas (3.E.1), (3.E.4); `e` inverts `v` | `exercise_3_E_8_values`, `exercise_3_E_8_demands` |
| Exercise 3.E.9 | Prop. 3.D.3 ⟺ Prop. 3.E.2 via (3.E.1) | `exercise_3_E_9_forward`, `exercise_3_E_9_backward`, `equation_3_E_1_instance`; continuity: `proposition_3_E_2_iv` (from 3.D.3(iv)) |
| Exercise 3.E.10 | Prop. 3.D.2 ⟺ Prop. 3.E.3 via (3.E.1), (3.E.4) | `exercise_3_E_10_forward`, `exercise_3_E_10_backward` (corrections B7) |
| Exercise 3.F.1 | Half-space representation | `exercise_3_F_1`, `exercise_3_F_1_halfspaces` |
| Exercise 3.F.2 | Nonconvex sets | `exercise_3_F_2`, `exercise_3_F_2_example` |
| Exercise 3.G.1 | Proposition 3.G.1 from Roy's identity | `exercise_3_G_1` |
| Exercise 3.G.2 | Cobb-Douglas satisfies all of Section 3.G | OPEN |
| Exercise 3.G.3(a)-(e) | Linear expenditure system | OPEN |
| Exercise 3.G.4(a) | Additive separability is cardinal, preserved only by linear transformations | Partial: `exercise_3_G_4a_affine`, `exercise_3_G_4a_not_ordinal`; "only" OPEN |
| Exercise 3.G.4(b) | Ordering on a group independent of the other goods | `exercise_3_G_4b`; the converse (Debreu 1960) is not asked |
| Exercise 3.G.4(c)-(d) | No inferior goods; gross substitutes | OPEN |
| Exercise 3.G.5(a)-(c) | Hicksian composite commodities | OPEN |
| Exercise 3.G.6(a) | Demand for good 3 | `exercise_3_G_6a` |
| Exercise 3.G.6(b) | Homogeneity | `exercise_3_G_6b`, `exercise_3_G_6_x1`, `exercise_3_G_6_x2` |
| Exercise 3.G.6(c)-(e) | Restrictions; indifference curves (draw); form of `u` | OPEN ((d) graphical) |
| Exercise 3.G.7 | `g(x) = ∇u/(x·∇u)`, `x(p) = ∇v/(p·∇v)` | `exercise_3_G_7_indirect_demand`, `exercise_3_G_7_demand` |
| Exercise 3.G.8 | Log-homogeneous `v` ⇒ `x(p, 1) = -∇_p v(p, 1)` | `exercise_3_G_8` |
| Exercise 3.G.9 | Slutsky matrix from `v` | OPEN |
| Exercise 3.G.10 | Conditions on Gorman `a(·)`, `b(·)` | OPEN |
| Exercise 3.G.11 | Gorman form ⇒ linear expansion paths | `exercise_3_G_11`, `relations_partial_price_eq` |
| Exercise 3.G.12 | Gorman form for homothetic and quasilinear preferences | OPEN |
| Exercise 3.G.13 | Polynomial `v` ⇒ expansion path in a subspace of dimension `≤ n + 1` | `exercise_3_G_13`; interpretation listed |
| Exercise 3.G.14 | Complete the substitution matrix; properties | `exercise_3_G_14`, `exercise_3_G_14_matrix` |
| Exercise 3.G.15(a)-(d) | `u = 2x₁^{1/2} + 4x₂^{1/2}` | OPEN |
| Exercise 3.G.16(a)-(c) | Given expenditure function | OPEN |
| Exercise 3.G.17(a) | Local demand by Roy's identity | `exercise_3_G_17a`, `exercise_3_G_17_v` |
| Exercise 3.G.17(b) | Local expenditure function | `exercise_3_G_17b`, `exercise_3_G_17_e` |
| Exercise 3.G.17(c) | Local Hicksian demand `∂e/∂p₁` | `exercise_3_G_17c` |
| Exercise 3.G.18 | Chains of substitutes | OPEN |

### Mathematical Appendix M.E: the implicit function theorem

| Source | Claim | Lean |
| --- | --- | --- |
| (M.E.1), p. 940; footnote 10 | The system `f(x; q) = 0`, open domains | Statements on Banach spaces `X × Q` (balls for neighbourhoods) |
| Definition M.E.1, p. 941; Figure M.E.1 | Locally solvable | `LocallySolvable`, `locallySolvable_of_eventually` |
| Theorem M.E.1, (M.E.2)-(M.E.3), pp. 941-942 | Implicit function theorem and first-order effects | `theorem_M_E_1` (strict differentiability; `Dη = -[D_x f]⁻¹ D_q f`), `theorem_M_E_1_contDiff` (`C^n` implicit function), `swapSystem`, `hasStrictFDerivAt_swapSystem` (Mathlib `implicitFunctionOfProdDomain`, `ContDiffAt.implicitFunction`) |
| Section M.E, p. 942 | One-variable formula | `implicit_function_one_variable` |
| Section M.E, p. 942 | Inverse function theorem as a special case | `inverse_function_theorem_M_E` |
| Section M.E, pp. 942-943; Figure M.E.2 | (M.E.2) generic | Listed (verbal) |
| Definition M.E.2, p. 943 | Regular system | `RegularSystemAt` |
| Theorem M.E.2, p. 943; footnote 11 | Transversality theorem | OPEN |

### Mathematical Appendix M.G: convex sets and separating hyperplanes

| Source | Claim | Lean |
| --- | --- | --- |
| Definition M.G.1, p. 946 | Convex set | `definition_M_G_1` |
| Footnote 14, p. 946 | Strictly convex set | `footnote_M_G_14`; as printed: `StrictlyConvexPrinted`, `footnote_M_G_14_printed_open`, `footnote_M_G_14_printed_counterexample` (correction B5) |
| Section M.G, p. 946; Figure M.G.1 | Hypograph of a concave function convex; intersections convex, unions not | `convex_hypograph_M_G`, `convex_sInter_M_G`, `union_not_convex_M_G` |
| Definition M.G.2, p. 946; Figure M.G.2 | Convex hull; as convex combinations | `definition_M_G_2`, `convexHull_eq_combinations` |
| Definition M.G.3, p. 946; Figure M.G.3 | Extreme point | `definition_M_G_3` (Mathlib `extremePoints`); as printed: `ExtremePointPrinted`, `definition_M_G_3_printed_vacuous` (correction B5); figure listed |
| Theorem M.G.1, p. 947 | Compact convex `B`: every point a convex combination of `≤ N + 1` extreme points | Partial: `caratheodory_M_G_1`, `theorem_M_G_1_closure`; exact statement OPEN |
| Definition M.G.4, p. 947; Figure M.G.4 | Hyperplane, half-spaces above and below; convex | `hyperplane`, `halfSpace`, `halfSpaceBelow`, `convex_halfSpaceBelow`, `convex_halfSpace`, `convex_hyperplane` |
| Theorem M.G.2, p. 948; Figure M.G.5 | Separating hyperplane theorem (point and closed convex set; disjoint convex sets) | `theorem_M_G_2_i` (`N ≥ 1`), `theorem_M_G_2_ii` (nonempty sets), `theorem_M_G_2_i_needs_dimension`, `theorem_M_G_2_ii_needs_nonempty` (correction B6), `appendixMG_exists_ne_zero_vec` |
| Proof of M.G.2, footnote 15, p. 948 | Closest-point construction | Listed (proof via Mathlib's Hahn-Banach) |
| Theorem M.G.3, (M.G.1), p. 949; Figure M.G.6 | Supporting hyperplane theorem | `theorem_M_G_3` (`N ≥ 1`) |
| Section M.G, p. 949 | Support function | See Section 3.F |

### Mathematical Appendix M.L: the envelope theorem

| Source | Claim | Lean |
| --- | --- | --- |
| (M.L.1), p. 964; footnote 28 | Parametrized constrained problem; value function | Statement data of `theorem_M_L_1`; footnote 28 listed |
| (M.L.2)-(M.L.3), pp. 964-965 | One variable, no constraints: `dv/dq = ∂f/∂q` | `equation_M_L_3` (any dimension) |
| Section M.L, p. 965; Figure M.L.1 | Envelope: `f(x̄; ·) ≤ v` touching at `q̄` | `envelope_tangency`, `envelope_objective_only` |
| Theorem M.L.1, (M.L.4)-(M.L.5), pp. 965-966; footnote 29 | Envelope theorem with multipliers | `theorem_M_L_1` (along a differentiable feasible maximizer path, the book's proof); with only `v` differentiable OPEN; footnote 29 listed |

### OPEN items

| Item | What is missing |
| --- | --- |
| Small type pp. 66-67, Figure 3.F.5 | Directional-derivative version of the duality theorem (one-sided derivatives equal the range of minimizers); the kink example |
| Exercise 3.E.6 | CES Hicksian demand and expenditure (part A's CES exercises 3.C.6, 3.D.5 are also OPEN) |
| Exercise 3.G.2 | Cobb-Douglas verification of Propositions 3.G.1-3.G.4 (Cobb-Douglas preferences are not strictly convex on the boundary of `ℝ²_+`, so the general theorems need an interior version) |
| Exercise 3.G.3(a)-(e) | Linear expenditure system (part A's Exercise 3.D.6 is OPEN) |
| Exercise 3.G.4(a) "only linear", (c), (d) | Functional equation for transformations preserving additivity; comparative statics of additively separable demand |
| Exercise 3.G.5(a)-(c) | Hicksian composite commodity theorem |
| Exercise 3.G.6(c), (e) | Slutsky restrictions `α = 100`, `β = γ = -5` (needs the Slutsky entries computed from derivatives) and the form of `u` |
| Exercises 3.G.9, 3.G.10, 3.G.12 | Slutsky matrix from `v`; admissible Gorman `a`, `b`; homothetic/quasilinear Gorman forms |
| Exercises 3.G.15, 3.G.16, 3.G.18 | Computational verifications (3.G.15-3.G.16) and the chain-of-substitutes result (3.G.18) |
| Theorem M.E.2 | Transversality theorem (needs Sard's theorem) |
| Theorem M.G.1 | Minkowski's theorem `B = Co(ext B)` for compact convex `B ⊆ ℝ^N` (Mathlib has only the closure form) |
| Theorem M.L.1 with only `v` differentiable | Needs feasible curves through `x̄` built under a constraint qualification |

## Part C: 3.J, Appendix 3.A, M.H

Mas-Colell, Whinston and Green, *Microeconomic Theory*, Chapter 3. This file covers **part C,
stage 1**: Section 3.J (the strong axiom of revealed preference, pp. 91-92), Appendix A to
Chapter 3 (continuity and differentiability of Walrasian demand, pp. 92-95), Exercises 3.J.1 and
3.AA.1 (p. 104), and Mathematical Appendix Section M.H (correspondences, pp. 949-952). Sections
3.H-3.I and Exercise 3.AA.2 (which needs `h(p, u)` and `e(p, u)`) are stage 2. Printed pages;
Lean names relative to `MWG.ClassicalDemand`. A demand function is MWG Ch. 2's `DemandFunction`
on the domain `PWDomain` (`p ≫ 0`, `w > 0`); `≻` and `Rational` are Kreps Ch. 2's `Strict` and
`Rational` as in part A. Imported results are named with their package: MWG Ch. 2
`MWGConsumerChoice` (`WeakAxiom`, `WalrasLaw`, `ValuesInOrthant`, Example 2.F.1 data and
`exercise_2_F_2_cycle`, `demand_2_F_15`, `exercise_2_F_15_weakAxiom`, `demand_2_F_17`,
`exercise_2_F_17d_zero`, `slutskyMatrix`, `gradientVec`, `jacobian`, `jacobian_mulVec`,
`hessianMatrix`, `figure_2_C_2_set`), MWG Ch. 1 `MWGPreferenceChoice` (`ChoiceStructure`,
`Rationalizable`), Kreps Ch. 1 `ChoicePreferenceUtility` (`SGARP`, `RationalizesData`,
`sgarp_of_rationalizes`, `rationalizes_of_sgarp`), Kreps Ch. 4 `RevealedPreference`
(`MarketData`, `GARP`), Kreps Ch. 3 `ConsumerDemand` (`SequentialUpper`, `SequentialLower`,
`continuous_of_singleton_correspondence`), and Mathlib (`LinearExtension`,
`implicitFunctionOfProdDomain`, `UpperHemicontinuous`, `LowerHemicontinuous`), all at the
worktree's current commit. Items marked OPEN are listed in the last table.

### Section 3.J: the strong axiom of revealed preference

| Source | Claim | Lean |
| --- | --- | --- |
| Section 3.J, p. 91 | Motivation (WA without rationalizability, Houthakker) | Listed only (exposition) |
| Definition 3.J.1, p. 91 | Strong axiom of revealed preference | `StrongAxiom` (lists of length `≥ 2`); printed form `StrongAxiomPrinted`, `strongAxiomPrinted_false`, `strongAxiomPrinted_false_of_walrasLaw`, `strongAxiom_of_printed` (correction C1) |
| Section 3.J, p. 91 | Verbal restatement ("directly or indirectly revealed preferred") | Listed only (verbal); formal content is `strongAxiom_iff_acyclic` |
| Section 3.J, p. 91 | "The SA was violated in Example 2.F.1" | `example_2_F_1_not_sa` (MWG Ch. 2 `exercise_2_F_2_cycle`) |
| Section 3.J, p. 91 | "The SA is satisfied if demand originates in rational preferences" | `strongAxiom_of_rationalizes` (demand in `ℝ^L_+`); abstract `sarpAcyclic_of_rationalizes` |
| Proposition 3.J.1, p. 91 | SA ⇒ rationalized by a rational `≿` | `proposition_3_J_1`; full proof content `proposition_3_J_1_extends`; with converse `proposition_3_J_1_iff` |
| Proof of Prop. 3.J.1, p. 92 | `≻¹`, `≻²`, transitivity of `≻²` | `sarpRevealedDirect`, `sarpRevealedIndirect`, `sarpRevealedIndirect_trans`, `sarp_transGen_iff_chain` |
| Proof of Prop. 3.J.1, p. 92 | "According to the SA, `≻²` is irreflexive" (and conversely) | `strongAxiom_iff_acyclic` |
| Proof of Prop. 3.J.1, p. 92 | Zorn: total extension `≻³`; `≿` complete, transitive, rationalizing | `sarp_rationalization` (Mathlib `LinearExtension`), `sarp_strict_trans` |
| Small type, p. 92 | Only single-valuedness is used; same for Chapter 1's abstract choice | `sarpDirect`, `SarpAcyclic`, `RationalizesChoice`, `sarp_rationalization`, `sarpAcyclic_iff_rationalizable`, `chapter1_sarp_rationalizable` (MWG Ch. 1 choice structures), `sarpRevealedDirect_eq` |
| Small type, p. 92 | Budgets being competitive is immaterial | Same abstract theorems (menus arbitrary) |
| Section 3.J, p. 92 | Bridge: Kreps SGARP / Proposition 1.23 | `sarp_rationalizes_iff_rationalizesData`, `sgarp_of_strongAxiom`, `strongAxiom_iff_sgarp` (`sarpMenus`, `sarpChosen`, `SarpPWIndex`, `sarpHalfspace`, `sarpChoice`) |
| Section 3.J (Kreps Ch. 4 bridge) | Finite data from an SA demand satisfy GARP | `garp_of_strongAxiom` |
| Section 3.J, p. 92 | SA implies WA (WA = lists of length two) | `weakAxiom_of_strongAxiom` |
| Exercise 3.J.1, pp. 92, 104 | `L = 2`: SA ⟺ WA | `exercise_3_J_1` (Walras' law, correction C2); `strongAxiom_of_weakAxiom_two`; minimal-cycle lemmas `SarpRelCycle`, `sarp_succ_mod_cases`, `SarpRelCycle.periodic`, `sarp_relCycle_of_transGen`, `SarpRelCycle.shortcut`, `sarp_exists_minimal_relCycle`; geometry `sarp_twoGoods_between_false` |
| Section 3.J, p. 92 | `L = 2` and WA ⇒ a rationalizing preference exists | `weakAxiom_rationalizable_two` |
| Section 3.J, p. 92 | "A result we have already seen in Section 3.H" | Stage 2 (Section 3.H) |
| Section 3.J, p. 92 | When `L > 2` the SA is stronger than the WA | `strongAxiom_stronger_three` (Exercise 2.F.15 demand, seven-bundle cycle via `sarp_demand_2_F_15_revealed`; correction C3) |
| Small type, p. 92 | SA essentially equivalent to rationality and to Slutsky symmetry + NSD; preferences without transitivity (Kihlstrom-Mas-Colell-Sonnenschein) | Listed only (discussion; the Slutsky part belongs to Sections 3.G-3.H) |
| Footnotes 30, 31, p. 92 | Literature (Mas-Colell 1982, Afriat 1967) | Listed only (citations) |

### Appendix A to Chapter 3: continuity and differentiability of Walrasian demand

| Source | Claim | Lean |
| --- | --- | --- |
| Appendix A, p. 92 | Standing assumption `x ≫ 0` for `(p, w) ≫ 0` | Hypothesis `hint` of the differentiability theorems |
| Definition 3.AA.1, p. 93 | Upper hemicontinuity of `x(p, w)` at `(p̄, w̄)` | `DemandUHCAt`; bridges `demandUHC_iff_hasClosedGraph` (M.H.2), `demandUHC_iff_sequentialUpper` (Kreps), `demand_uhc_mwg` (M.H.3) |
| Footnote 32, p. 93 | Notation `zⁿ → z`; definition for locally bounded correspondences; demand locally bounded at `(p, w) ≫ 0` | `footnote_3_AA_32`, `appendixA_walrasianDemand_subset_budgetSet`, `demand_uhc_mwg` |
| Section 3.AA, p. 93 | Single-valued: uhc ⟺ continuity | `demandUHC_iff_continuousOn` (Kreps `continuous_of_singleton_correspondence`) |
| Figure 3.AA.1, p. 93 | Uhc correspondence with a jump | Listed only (graphical) |
| Proposition 3.AA.1, p. 93 | Continuous `u` on `ℝ^L_+`: `x(p, w)` uhc at all `(p, w) ≫ 0`; continuous if a function | `proposition_3_AA_1`, `proposition_3_AA_1_continuous`, `proposition_3_AA_1_stated` (correction C4: LNS unused) |
| Proof of Prop. 3.AA.1, pp. 93-94 | Limit argument; `y` near `x̄` with `p̄·y < w̄` | `demand_uhc_of_locallyCheaper`, `locallyCheaperAt_nonnegOrthant`, `appendixA_tendsto_dotProduct_seq`, `appendixA_isClosed_nonnegOrthant` |
| Figure 3.AA.2, p. 94 | Finding `y` | Listed only (graphical; content in `locallyCheaperAt_nonnegOrthant`) |
| Small type, p. 94 | Closed `X`: uhc at `(p̄, w̄)` passing the locally cheaper test | `LocallyCheaperAt`, `demand_uhc_of_locallyCheaper` |
| Figure 3.AA.3, p. 94 | Good 2 indivisible: test fails at `(1, w̄, w̄)`; demand `(w̄, 0)` for `p₂ > w̄`, `(0, 1)` at `p̄`; not uhc | `figure_3_AA_3_utility`, `figure_3_AA_3_not_locallyCheaper`, `figure_3_AA_3_demand_dear`, `figure_3_AA_3_demand_bar`, `figure_3_AA_3_not_uhc`, `appendixA_tendsto_figure_prices` (correction C5) |
| Small type, p. 94 | The proof fails without the locally cheaper condition | Listed only (verbal; illustrated by the Figure 3.AA.3 theorems) |
| Differentiability, p. 94 | Standing assumptions: `u` strictly quasiconcave, `C²`, `∇u ≠ 0` | Hypotheses of `appendixA_differentiable_iff_bordered_primitive` (correction C6); consistency witness `appendixA_oneGoodUtility_assumptions` |
| Differentiability, p. 94 | FOC: `x(p, w) ≫ 0` solves `∇u(x) - λp = 0`, `p·x - w = 0` | `appendixA_foc_of_demand` (with `λ = ∇u·x / w`, `appendixADemandMultiplier`) |
| Differentiability, p. 95 | Jacobian of the system in `(x, λ)` is `[[D²u, -p], [pᵀ, 0]]` | `appendixAFocSystem`, `appendixAFocSystem_hasStrictFDerivAt`, `appendixAFocJacobian`, `appendixAFocJacobian_mulVec`, `appendixAFocJacobian_det_ne_zero_iff`, `appendixA_gradient_hasStrictFDerivAt` |
| Differentiability, p. 95 | Implicit function theorem: nonzero Jacobian determinant ⇒ differentiable | `appendixA_demand_differentiableAt_of_jacobian` (Mathlib `implicitFunctionOfProdDomain`; `appendixA_isOpen_pwDomainSet`, `appendixAPosOrthant`) |
| Differentiability, p. 95 | `∇u = λp`, `λ > 0`: Jacobian determinant ≠ 0 ⟺ bordered Hessian determinant ≠ 0 | `appendixABorderedHessian`, `appendixABorderedHessian_eq_mul`, `appendixABorderedHessian_det_eq`, `appendixAFocJacobian_det_ne_zero_iff_bordered` |
| Differentiability, p. 95 | Geometric interpretation (nonzero curvature) | Listed only (verbal) |
| Differentiability, p. 95 | `f(x) = -x⁴` strictly concave with `f''(0) = 0` | `appendixA_strictConcave_neg_pow_four` |
| Differentiability, p. 95 | A strictly quasiconcave function can have zero bordered Hessian determinant | `appendixA_bordered_zero_example` (`u = x₂ - x₁⁴`; `appendixABorderedZeroUtility`, `appendixA_hasFDerivAt_borderedZeroUtility`, `appendixA_gradient_borderedZeroUtility`) |
| Differentiability, p. 95 | `x(p, w)` differentiable iff bordered Hessian determinant ≠ 0 | Both directions: `appendixA_demand_differentiableAt_of_jacobian`, `appendixA_jacobian_of_demand_differentiableAt`; `appendixA_differentiable_iff_bordered`, `appendixA_differentiable_iff_bordered_primitive`, `appendixA_exists_demandFunction_of_strictlyQuasiconcave` |
| Differentiability, p. 95 | Differentiable `x(p, w)` ⇒ `rank S(p, w) = L - 1` ("which we shall not prove here") | `appendixA_slutsky_rank`, via `appendixA_linearized_foc` (MWG Ch. 2 `slutskyMatrix_mulVec`) |
| Footnote 33, p. 95 | Leontief demand `(w/(p₁+p₂), w/(p₁+p₂))` is differentiable, generated by `min`, Slutsky matrix zero (rank 0) | `footnote_3_AA_33_demand`, `footnote_3_AA_33` (MWG Ch. 2 Exercise 2.F.17, part A `leontiefUtility`) |
| Exercise 3.AA.1(a), p. 104 | `X = {x₁ + x₂ ≥ 1}`, `u = x₂`: locally cheaper test fails at `(1, 1, 1)` | `exercise_3_AA_1_set`, `exercise_3_AA_1_utility`, `exercise_3_AA_1a` |
| Exercise 3.AA.1(b), p. 104 | Demand not continuous at `(1, 1, 1)` | `exercise_3_AA_1b`, `exercise_3_AA_1b_demand_bar`, `exercise_3_AA_1b_demand_dear` |
| Exercise 3.AA.1, p. 104 | "Represent graphically", "interpret economically" | Listed only (graphical/verbal) |
| Exercise 3.AA.2, p. 104 | `h(p, u)` uhc, `e(p, u)` continuous; differentiability of `h` | Stage 2 (needs the expenditure function and Hicksian demand of Section 3.E) |

### Mathematical Appendix M.H: correspondences

| Source | Claim | Lean |
| --- | --- | --- |
| Definition M.H.1, p. 949 | Correspondence `f : A → Y`; may be empty-valued; single-valued = function | `CorrMapsInto` (correspondences are `α → Set β`) |
| Section M.H, p. 949 | Graph | `corrGraph` |
| Definition M.H.2, p. 949 | Closed graph | `HasClosedGraph`, `hasClosedGraph_of_isClosed` |
| Section M.H, p. 950 | Closed graph = closedness relative to `A × Y` | `hasClosedGraph_iff_closure` |
| Definition M.H.3, p. 950 | Upper hemicontinuity | `UpperHemicontinuousMWG` |
| Footnotes 16-17, p. 950 | Image of a compact set under a uhc correspondence is compact | `footnote_M_H_17` |
| Section M.H, p. 950 | Compact `Y`: uhc reduces to closed graph | `uhc_iff_hasClosedGraph_of_isCompact` |
| Figure M.H.1(a), p. 950 | Closed graph, not uhc | `figure_M_H_1a`, `figure_M_H_1a_spec` |
| Figure M.H.1(b), p. 950 | A uhc correspondence | `figure_M_H_1b`, `figure_M_H_1b_uhc` |
| Theorem M.H.1, p. 950 | Single-valued: uhc ⟺ continuous | `theorem_M_H_1` (`appendixMH_continuousOn_of_seq`, `appendixMH_biUnion_singleton_eq_image`; correction C7) |
| Footnote 18, p. 950 | A convergent sequence with its limit is bounded (compact) | `footnote_M_H_18` |
| Definition M.H.4, p. 951 | Lower hemicontinuity | `LowerHemicontinuousMWG` (correction C7) |
| Figure M.H.2(a), p. 951 | Lhc, not uhc | `figure_M_H_2a`, `figure_M_H_2a_spec` |
| Figure M.H.2(b), p. 951 | Uhc, not lhc | `figure_M_H_2b`, `figure_M_H_2b_spec` |
| Section M.H, p. 951 | Explosions/implosions | Listed only (verbal) |
| Footnote 19, p. 951 | Open graph ⇒ lhc | `footnote_M_H_19` |
| Section M.H, p. 951 | Function: lhc ⟺ continuity | `lhc_singleton_iff` |
| Section M.H, p. 951 | Continuous correspondence = uhc and lhc | `ContinuousCorrMWG` |
| Figure M.H.3, p. 952 | A continuous correspondence | `figure_M_H_3`, `figure_M_H_3_continuous` |
| Bridges (Kreps App. 4, Mathlib) | Closed graph = Kreps `SequentialUpper`; lhc = Kreps `SequentialLower` = Mathlib `LowerHemicontinuous`; uhc ⇒ Mathlib `UpperHemicontinuous` | `hasClosedGraph_iff_sequentialUpper`, `lhc_iff_sequentialLower`, `lhc_iff_lowerHemicontinuous`, `upperHemicontinuous_of_uhc` |

### OPEN (part C, stage 1)

| Source | Claim | What is missing |
| --- | --- | --- |
| Exercise 3.AA.2, p. 104 | Hicksian demand uhc, expenditure function continuous, differentiability of `h` | Stage 2: needs `h(p, u)` and `e(p, u)` from Section 3.E (built by the 3.E-3.G agent). |

## Part D: 3.H-3.I

Mas-Colell, Whinston and Green, *Microeconomic Theory*, Chapter 3, **part D**: Sections 3.H
(integrability, pp. 75-80) and 3.I (welfare evaluation of economic changes, pp. 80-91), the
in-text Exercises 3.I.1-3.I.2 and the end-of-chapter Exercises 3.H.1-3.H.7 and 3.I.1-3.I.12
(pp. 102-104). Printed pages; Lean names relative to `MWG.ClassicalDemand`. The expenditure and
indirect utility functions are part B's `expenditure` and part A's `indirectUtility` (the EMP and
UMP on `ℝ^L_+`); `V_u` is `recoveredSet`; the recovered utility `sup {u : x ∈ V_u}` is
`recoveredUtility`, valued in `EReal` (correction D1); (3.H.2) is `SolvesPDE`. Demand functions,
Slutsky matrices and negative semidefiniteness are MWG Chapter 2's `DemandFunction`,
`slutskyMatrix`, `NegSemidef`. Items marked OPEN are collected in the last table; departures are
in [corrections-D](corrections.md).

### Section 3.H: integrability

| Source | Claim | Lean |
| --- | --- | --- |
| Section 3.H, p. 75 | HD0, Walras' law, symmetric n.s.d. `S` are necessary | Parts A-B (`proposition_3_D_2_i`, `walrasLawCorr_walrasianDemand`, `slutsky_matrix_properties`) |
| Section 3.H, pp. 75-76 | They are also sufficient ("all of its consequences") | `integrability_of_pde` (given a solution of (3.H.2)), `integrability_theorem`; existence of the solution OPEN for `L > 2` |
| Section 3.H, p. 76 | WA + HD0 + Walras rationalizable iff `S` symmetric | "only if": `no_rationalization_of_asymmetric_slutsky` (part B), `section_3_H_no_solution`; "if": `integrability_of_pde`, `integrability_two_goods` (conditional, see OPEN) |
| Section 3.H, p. 76 | Practical motivations; two-step plan | Listed (verbal) |
| Section 3.H, p. 76 | `e` has the properties of Prop. 3.E.2 and is differentiable (3.F.1, 3.G.1) | Part B: `proposition_3_E_2_*`, `proposition_3_G_1` |
| Section 3.H, p. 77 | `V_u` and `e(p, u) = Min {p·x : x ∈ V_u}` | `recoveredSet`, `HD1OnPos`, `MonotoneOnPos`, `posPrices` |
| Proposition 3.H.1, p. 77 | `e(·, u)` concave, HD1, nondecreasing, differentiable ⇒ `e(p, u) = min_{V_u} p·x` | `proposition_3_H_1` (differentiability only at `p`; strict monotonicity in `u` and continuity not used) |
| Proof of 3.H.1, p. 77 | Concavity gives `e(p') ≤ e(p) + ∇e·(p' - p)` (Section M.C) | `integ_concave_le_tangent` |
| Proof of 3.H.1, p. 77 | Euler's formula `e(p) = p·∇e(p)` | `integ_euler` |
| Proof of 3.H.1, p. 77 | `∇e ≥ 0`, so `∇e ∈ V_u` and the minimum is attained | `integ_gradient_nonneg`, `integ_supergradient_mem`, `integ_strictlyPositive_of_le`, `integ_apply_eq_dot` |
| Proof of 3.H.1, p. 77 | `V_u` nonempty, closed, bounded below; the minimum exists | `isClosed_recoveredSet`, `recoveredSet_subset_orthant`, `proposition_3_H_1` (attainment) |
| Section 3.H, p. 77 | `u' > u` ⇒ `V_u ⊋ V_{u'}`; each `V_u` closed, convex, bounded below | `recoveredSet_ssubset`, `recoveredSet_antitone`, `convex_recoveredSet`, `isClosed_recoveredSet`, `recoveredSet_upward` |
| Section 3.H, p. 77; Figure 3.H.1 | The sets `V_u` define a preference with expenditure function `e` | `exercise_3_H_1`, `recoveredUtility`, `recoveredPref`; figure listed |
| Small type, p. 78 | Proposition 3.H.1 holds without differentiability | `proposition_3_H_1_general` (for `e(·, u)` continuous), `integ_exists_supergradient` |
| Small type, p. 78; Figure 3.H.2 | `V_u` generates `e` for the actual (possibly nonconvex) preference | `recoveredSet_generates_expenditure`, `subset_recoveredSet` |
| Small type, p. 78 | `V_u` is the convex hull of the actual at-least-as-good set | `recoveredSet_eq_closure_convexHull` (closed convex hull, upward-closed sets; correction D2) |
| Small type, p. 78 | `e` differentiable ⇒ every generating preference is convex | Partial: `exercise_3_H_2`; the convexity conclusion OPEN |
| Section 3.H, p. 78 | Recovering `e` from demand: assumptions WL, HD0, single-valued | Hypotheses of `integrability_of_pde`, `integrability_two_goods` |
| Equation (3.H.1), p. 78 | `e'(p₁) = x₁(p₁, 1, e(p₁))`, `e(p₁⁰) = w⁰` | `equation_3_H_1_local_exists` (local existence) |
| Section 3.H, p. 78 | A solution of (3.H.1) is the expenditure function at `u⁰` | `integrability_recovers_expenditure`, `pde_solution_unique`, `expenditure_solvesPDE` (uniqueness for `C¹` demand); `twoGoodsLift_solvesPDE` (from (3.H.1) to (3.H.2)) |
| Footnote 18, p. 78 | (3.H.1) is an autonomous system in the `(p₁, e)` plane | The proof of `equation_3_H_1_local_exists` (Picard-Lindelöf on `(1, x₁(p₁, e))`) |
| Section 3.H, p. 79 | Solution continuous; nondecreasing since `x₁ ≥ 0` | `equation_3_H_1_local_exists` (differentiable), `equation_3_H_1_monotone` |
| Section 3.H, p. 79 | `e'' = s₁₁ ≤ 0`, so `e` concave | `equation_3_H_1_concave` |
| Section 3.H, p. 79; Figure 3.H.3 | "A few weak regularity assumptions guarantee that a solution exists for any initial condition" | Local existence `equation_3_H_1_local_exists`; global existence OPEN |
| Equation (3.H.2), p. 79 | The system `∂e/∂p_l = x_l(p, e(p))` | `SolvesPDE` |
| Section 3.H, p. 79 | Existence not guaranteed for `L > 2` | `section_3_H_no_solution` (Exercise 2.F.15 demand) |
| Section 3.H, pp. 79-80 | `D²e(p) = D_p x + D_w x xᵀ = S(p, e(p))`; symmetry necessary | `pde_hessian_eq_slutsky`, `pde_jacobian_eq_slutsky`, `pde_chain`, `pde_slutsky_symmetric` |
| Section 3.H, p. 80 | Frobenius: symmetry sufficient for a solution | OPEN for `L > 2` |
| Section 3.H, p. 80 | With `S` n.s.d. a solution has the properties of an expenditure function | `pde_concave`, `pde_hd1`, `pde_monotone`, `pde_line_le` |
| Section 3.H, p. 80 | Necessary and sufficient condition: symmetric n.s.d. `S` | `integrability_of_pde` (sufficiency given a solution); necessity `pde_slutsky_symmetric` |
| Footnote 19, p. 80 | "Minor technical requirements" | Listed |
| Section 3.H, p. 80 | WA ⇒ n.s.d. (2.F); `L = 2` ⇒ symmetric; `L = 2` always rationalizable | `proposition_2_F_2`, `exercise_2_F_11` (MWG Ch. 2); `integrability_two_goods` (given the global flow of (3.H.1), see OPEN) |
| Section 3.H, p. 80 | `L > 2`: WA demand need not have symmetric `S` | `section_3_H_no_solution` (`exercise_2_F_15_weakAxiom`, `exercise_2_F_15_not_symm`) |
| Small type, p. 80 | Solving (3.H.2) one price at a time; path dependence without symmetry | `exercise_3_I_7b` (explicit path dependence); `twoGoodsLift_solvesPDE` (`L = 2`); general construction OPEN |

### Section 3.I: welfare evaluation of economic changes

| Source | Claim | Lean |
| --- | --- | --- |
| Section 3.I, pp. 80-81 | Rational, continuous, LNS consumer; wealth `w > 0`; price change `p⁰ → p¹` | Hypotheses `hrep`, `hu`, `hlns`, `hw` |
| Footnote 20, p. 81 | Changes affecting wealth: Exercise 3.I.12 | `exercise_3_I_12` |
| Section 3.I, p. 81 | Worse off iff `v(p¹, w) < v(p⁰, w)` | Definition (listed) |
| Section 3.I, p. 81; Figure 3.I.1 | Money metric `e(p̄, v(p, w))` is an indirect utility function | `moneyMetric`, `moneyMetric_le_iff`, `moneyMetric_self`, `welfare_e_lt_iff`, `welfare_e_le_iff`, `welfare_v_attainable` |
| Footnote 21, p. 81 | The money metric is independent of the indirect utility used | `footnote_3_I_21`, `expenditure_comp` |
| Equations (3.I.1)-(3.I.2), p. 82 | `EV = e(p⁰, u¹) - w`, `CV = w - e(p¹, u⁰)` | `equivalentVariation`, `compensatingVariation`, `equation_3_I_1`, `equation_3_I_2` |
| Section 3.I, p. 82; footnote 22 | `v(p⁰, w + EV) = u¹`, `v(p¹, w - CV) = u⁰` | `footnote_3_I_22`, `cv_indirectUtility` |
| Section 3.I, p. 82; Figure 3.I.2 | Interpretations of EV, CV | Listed (verbal, graphical) |
| Section 3.I, p. 82 | EV and CV rank `p⁰`, `p¹` correctly | `welfare_ranking` |
| Equations (3.I.3)-(3.I.4), p. 83 | EV, CV as areas under Hicksian demand curves | `equation_3_I_3`, `equation_3_I_4`, `expenditure_line_integral`, `hicksianOf`, `hicksianOf_mem`, `priceLine`, `priceLine_pos`, `priceLine_mono`, `priceLine_hasDerivAt` |
| Section 3.I, p. 83; Figure 3.I.3 | Normal good: `EV > CV` (both directions) | `normal_good_cv_le_av_le_ev` (weak inequality; correction D5), `welfare_expenditure_sides` |
| Section 3.I, p. 83 | Inferior good: reversed | `inferior_good_ev_le_av_le_cv`, `exercise_3_I_3` |
| Section 3.I, p. 83; footnote 23 | No wealth effect: `CV = EV` = Marshallian surplus | `marshallian_surplus` |
| Exercise 3.I.1, p. 84 | Two prices: EV, CV as sums of integrals; equal without wealth effects | `exercise_3_I_1` |
| Example 3.I.1, p. 84 | Deadweight loss `(-T) - EV = w - T - e(p⁰, u¹)` | `example_3_I_1_u1` (first conjunct) |
| Equation (3.I.5), p. 84 | DWL as an integral; nonnegative; positive if `h₁` strictly decreasing | `example_3_I_1_u1` |
| Small type, pp. 84-85; Figure 3.I.5 | `x(p¹, w)` on the budget line of `B_{p⁰, w-T}`; DWL as vertical distance | `example_3_I_1_budget_line`, `example_3_I_1_u1`; figure listed |
| Equation (3.I.6), p. 85; Figure 3.I.4 | Deficit of compensating at `u⁰` as an integral; positive | `example_3_I_1_u0` (misprint, correction D6) |
| Exercise 3.I.2, p. 86 | Derivative of the DWL in `t`; zero at `0`; positive for `t > 0` | `exercise_3_I_2` (fixed utility level; correction D4) |
| Small type, p. 86 | `EV(p⁰, ·, w)` ranks `p¹`, `p²`; CV difference `e(p², u⁰) - e(p¹, u⁰)` | `ev_compare`, `cv_difference` |
| Footnote 24, p. 86 | Sign of `CV(p¹, p², w)` ranks `p¹`, `p²` | `footnote_3_I_24` |
| Small type, p. 86; Figure 3.I.6 | Two taxes with the same revenue: better iff smaller DWL | `two_taxes_compare` |
| Section 3.I, p. 87; footnote 25 | Summary; practical recovery | Listed |
| Proposition 3.I.1, p. 87 | `(p¹ - p⁰)·x⁰ < 0` ⇒ strictly better off | `proposition_3_I_1`, `proposition_3_I_1_pref` |
| Equation (3.I.7), p. 87 | Taylor expansion; remainder nonpositive by concavity | `equation_3_I_7`; the `o(‖p¹ - p⁰‖)` expansion itself is differentiability (listed) |
| Proposition 3.I.2, p. 88 | `(p¹ - p⁰)·x⁰ > 0` ⇒ worse off for small `α` | `proposition_3_I_2` (for `α ∈ (0, ᾱ)`; correction D3) |
| Figure 3.I.7, p. 88 | Illustration | Listed (graphical) |
| Equation (3.I.8), p. 89 | Area variation measure | `areaVariation` |
| Section 3.I, p. 89 | No wealth effects: AV = EV = CV | `marshallian_surplus` |
| Section 3.I, p. 89 | Normal good: `CV ≤ AV ≤ EV`; inferior: reversed | `normal_good_cv_le_av_le_ev`, `inferior_good_ev_le_av_le_cv` |
| Section 3.I, p. 89 | AV can misrank several price changes | `exercise_3_I_10` |
| Section 3.I, p. 89 | Marshall's argument; Vives; fallacy of composition | Listed (verbal) |
| Section 3.I, pp. 89-90; Figure 3.I.8 | Error of AV small relative to CV but not to DWL for small changes | OPEN (asymptotic comparison) |
| Footnote 27, p. 89 | Same for EV | Listed |
| Footnote 28, p. 90 | Derivatives of CV, EV, AV in `p¹₁` at `p⁰₁` equal `x₁(p⁰, w)` | `footnote_3_I_28_ev`, `footnote_3_I_28_av`; the CV part OPEN |
| Footnote 29, p. 90 | AV can misrank equal-revenue taxes even for small taxes | OPEN |
| Equation (3.I.9), pp. 90-91; Figure 3.I.9 | `h̃(p, u⁰) = x(p⁰, w) + S(p⁰, w)(p - p⁰)`, first-order approximation of `h` | `equation_3_I_9` |
| Section 3.I, p. 91 | `h̃` better than AV for small changes; either can be better for large | OPEN (asymptotic comparison); listed |

### Exercises 3.H and 3.I (pp. 102-104)

| Source | Claim | Lean |
| --- | --- | --- |
| Exercise 3.H.1 | `u(x) = sup {u : x ∈ V_u}` generates `e` | `exercise_3_H_1`, `exercise_3_H_1_pos`, `mem_recoveredSet_iff`, `le_recoveredUtility`, `exists_of_lt_recoveredUtility`; as printed: `exercise_3_H_1_min_not_attained`, `exercise_3_H_1_sup_empty`, `integExpFamily` (correction D1) |
| Exercise 3.H.2 | `e` differentiable ⇒ no (strongly monotone) nonconvex preference generates `e` | Partial: `exercise_3_H_2` (unique minimizer `∇e` in the actual set and in `V_u`); convexity OPEN |
| Exercise 3.H.3 | Recover `v` from `e` | `exercise_3_H_3` |
| Exercise 3.H.4 | Recover `≿` from the indirect demand `g(x)`, `L = 2` | `exercise_3_H_4` (indifference curves solve `φ' = -g₁/g₂`); procedure verbal |
| Exercise 3.H.5 | Recover `e` and `u` from `v` | `exercise_3_H_5_expenditure`, `exercise_3_H_5_utility` |
| Exercise 3.H.6 | `x_l = α_l w/p_l`: expenditure function and utility | `cdExpL`, `cdDemandL`, `cdLogUtility`, `cdUpperSet`, `cdExpL_pos`, `cdL_solvesPDE`, `cdL_amgm`, `cdL_le_dot`, `cdL_expenditure_eq_supportFn`, `cdL_concave`, `cdDemandL_walras`, `exercise_3_H_6_rationalizes`, `exercise_3_H_6_utility` |
| Exercise 3.H.7(a) | Demand of 2.F.17: `e(p, 1)` | `exercise_3_H_7a` (`e(p, 1) = ∑ p_l`, unique solution), `demandDomain`, `isOpen_demandDomain` |
| Exercise 3.H.7(b) | Upper contour set of `(1, ..., 1)` | `exercise_3_H_7b` |
| Exercises 3.I.1-3.I.2 | In text | See Section 3.I |
| Exercise 3.I.3 | Price fall, inferior good ⇒ `CV > EV` | `exercise_3_I_3` (weak; strict with strict inferiority and `x_l > 0`); `exercise_3_I_3_printed_counterexample` (correction D5) |
| Exercise 3.I.4 | CV comparison can misrank | `exercise_3_I_4`, `shiftLeontief`, `shiftLeontief_continuous`, `shiftLeontief_lns`, `shiftLeontief_expenditure`, `shiftLeontief_indirect` |
| Exercise 3.I.5 | Quasilinear ⇒ `CV = EV` | `exercise_3_I_5`, `expenditureOn`, `expenditureOn_quasilinear_add` |
| Exercise 3.I.6 | `∑ CV_i > 0` ⇒ everybody can be compensated | `exercise_3_I_6` |
| Exercise 3.I.7(a) | Restrictions from utility maximization | `exercise_3_I_7a`, `quadForm_nonpos_iff`, `slutsky_eq_priceEffect_of_no_wealth` |
| Exercise 3.I.7(b) | EV from `(1, 1)` to `(2, 2)`; no path independence without symmetry | `exercise_3_I_7b`, `bilinEV`, `bilinEVAlt`, `bilinEV_eq`, `bilinEVAlt_eq`, `integral_affine` |
| Exercise 3.I.7(c) | `EV` vs `EV₁ + EV₂` | `exercise_3_I_7c` (`EV - (EV₁ + EV₂) = -c`); interpretation verbal |
| Exercise 3.I.7(d) | `DW` vs `DW₁ + DW₂` | `exercise_3_I_7d`, `linDeadweight` |
| Exercise 3.I.7(e) | Optimal taxes for small revenue `R` | `exercise_3_I_7e`, `exercise_3_I_7e_deadweight` (revenue linearized) |
| Exercise 3.I.8(a) | Most general utilities with wealth-independent demand for goods 1, 2 | "if": `exercise_3_I_8a` (quasilinear in good 3); "only if" OPEN |
| Exercise 3.I.8(b) | Restrictions from utility maximization | `exercise_3_I_8b` |
| Exercise 3.I.8(c) | Welfare measure from `p` to `p'` | `exercise_3_I_8c` |
| Exercise 3.I.8(d) | `EV₁`, `EV₂`, `EV₃`; when `EV₃ = EV₁ + EV₂` | `exercise_3_I_8d` (correction D7) |
| Exercise 3.I.9 | `s_ll < 0` ⇒ optimal tax with rebate is zero | `exercise_3_I_9` (weak, no `s_ll` needed), `exercise_3_I_9_strict`, `priceLine_dot` |
| Exercise 3.I.10 | AV misranks with several price changes | `exercise_3_I_10`, `shiftLeontiefDemand`, `shiftLeontief_walrasianDemand`, `areaVariationTwo` |
| Exercise 3.I.11 | `(p¹ - p⁰)·x¹ > 0` ⇒ worse off; `p⁰·(x¹ - x⁰) < 0`; first-order approximation at `p¹` | `exercise_3_I_11`; the `(x₁, x₂)` picture listed |
| Exercise 3.I.12 | EV, CV and the partial-information test for `(p⁰, w⁰) → (p¹, w¹)` | `exercise_3_I_12`, `equivalentVariationPW`, `compensatingVariationPW` |

### OPEN

| Source | Claim | What is missing |
| --- | --- | --- |
| Section 3.H, p. 80 | Frobenius: a symmetric (n.s.d.) Slutsky matrix gives a solution of (3.H.2) for `L > 2` | The sufficiency half of Frobenius' theorem (integrability of a symmetric `C¹` gradient system on a simply connected domain); Mathlib has no Frobenius or Poincaré lemma for such systems. Proved: necessity (`pde_slutsky_symmetric`), uniqueness (`pde_solution_unique`), and everything downstream of a solution (`integrability_of_pde`) |
| Section 3.H, pp. 79-80 | `L = 2`: a global solution of (3.H.1) for every initial condition, strictly increasing and continuous in the initial value | Global continuation of the local Picard-Lindelöf solution (`equation_3_H_1_local_exists`) to all `p₁ > 0` (the bound `0 ≤ e' ≤ e/p₁` rules out blow-up, but Mathlib has no maximal-solution theorem), and monotone continuous dependence on `w⁰` (non-crossing follows from `pde_solution_unique`-type uniqueness). With them `integrability_two_goods` gives the book's `L = 2` conclusion |
| Small type, p. 80 | General `L`, symmetric `S`: solving (3.H.2) one price at a time | Same as the Frobenius item (the coordinate-path solution is well defined only after path independence is proved) |
| Small type, p. 78; Exercise 3.H.2 | `e` differentiable ⇒ every generating (strongly monotone) preference is convex | Proved: unique minimizer `∇e` in the actual set and in `V_u` (`exercise_3_H_2`), `V_u` = closed convex hull (`recoveredSet_eq_closure_convexHull`). Missing: every point of `V_u` dominates a point of the actual set, e.g. via density of properly efficient points (Arrow-Barankin-Blackwell) |
| Exercise 3.I.8(a) | Wealth-independent demand for goods 1, 2 ⇒ utility quasilinear in good 3 | A converse integrability argument (`e(p, u) = u - ψ(p)` from (3.H.2) with `x₁, x₂` independent of `w`) on the quasilinear consumption set |
| Footnote 28, p. 90 | `∂CV(p¹, p⁰, w)/∂p¹₁ = x₁(p⁰, w)` at `p⁰` | Differentiability of `e(p⁰, ·)` in the utility level and of `v`, combined with Roy's identity |
| Section 3.I, pp. 89-91; Figure 3.I.8; footnote 29 | Asymptotic comparisons: AV error small relative to CV, not to the DWL; (3.I.9) better than AV for small changes | Second-order expansions of the integrals in `p¹ - p⁰` |

## Part E: closing items across 3.C-3.G, 3.AA.2, M.G, M.K

MWG, Chapter 3 (Sections 3.B-3.G, Exercise 3.AA.2) and Mathematical Appendix M.E, M.G, M.K, M.L.
This part closes items listed as OPEN in [source-map.md](source-map.md) (part A) and
[source-map-B.md](source-map.md) (part B), in the modules `Closer*`. One row per item: either
the Lean names that close it, or OPEN with what is missing. Departures are in
[corrections-E.md](corrections.md).

### Part A items

| Source | Claim | Lean |
| --- | --- | --- |
| Exercise 3.C.5(b), "only if", p. 96 | A continuous quasilinear `≿` on `(-∞, ∞) × ℝ^{L-1}_+` has a utility `x_k + φ(x_{-k})` | `exercise_3_C_5b_only_if`, `closer_quasilinear_axis`, `convex_quasilinearDomain`, `quasilinearDomain_shift`, `quasilinearDomain_axis` |
| Exercise 3.D.5(a), p. 97 | CES Walrasian demand and indirect utility | `exercise_3_D_5a_demand`, `exercise_3_D_5a_indirect`, `cesUtility`, `cesDemand`, `cesIndirect`, `cesUtility_eq_extend` (Kreps `problem_3_7`), `cesUtility_cesDemand` |
| Exercise 3.D.5(b), p. 97 | Properties of Propositions 3.D.2 and 3.D.3 | `exercise_3_D_5b_demand_homogeneous`, `exercise_3_D_5b_walras`, `exercise_3_D_5b_nonneg`, `exercise_3_D_5b_indirect_homogeneous`, `exercise_3_D_5b_indirect_wealth`, `exercise_3_D_5b_indirect_prices`, `exercise_3_D_5b_indirect_quasiconvex`, `exercise_3_D_5b_indirect_continuous` (single-valuedness: `exercise_3_D_5a_demand`) |
| Exercise 3.D.5(c), p. 97 | Linear and Leontief demand and indirect utility; CES limits as `ρ → 1` and `ρ → -∞` | `exercise_3_D_5c_linear`, `exercise_3_D_5c_leontief`, `exercise_3_D_5c_limit_linear_lt`, `exercise_3_D_5c_limit_linear_gt`, `exercise_3_D_5c_limit_linear_eq`, `exercise_3_D_5c_limit_linear_indirect`, `exercise_3_D_5c_limit_leontief`, `exercise_3_D_5c_limit_leontief_indirect` |
| Exercise 3.D.5(d), p. 97 | `ξ₁₂ = 1/(1 - ρ)`; linear, Leontief, Cobb-Douglas values | `elasticityOfSubstitution`, `exercise_3_D_5d_ratio`, `exercise_3_D_5d`, `exercise_3_D_5d_limits` (linear `∞`, Leontief `0`, `ρ = 0` gives `1`), `exercise_3_D_5d_cobbDouglas`, `exercise_3_D_5d_leontief` |
| Exercise 3.D.6(a), p. 98 | Exponents may be normalized to sum to one | `exercise_3_D_6a` |
| Exercise 3.D.6(b), p. 98 | Linear expenditure system: demand and indirect utility | `exercise_3_D_6b_demand`, `exercise_3_D_6b_indirect`, `lesUtility`, `lesDemand`, `lesIndirect`, `lesDemand_walras` (the first-order conditions are the method, listed) |
| Exercise 3.D.6(c), p. 98 | Properties of Propositions 3.D.2 and 3.D.3 | `exercise_3_D_6c_demand`, `exercise_3_D_6c_indirect`, `lesDomain_convex_subset` |
| Exercise 3.D.7(a)-(e), p. 98 | Regions of choices `x¹` consistent with (quasilinear, normal, homothetic) preference maximization | OPEN: each region needs both the necessary (revealed-preference) inequalities and, for sufficiency, a constructed rational preference of the required kind rationalizing `x⁰` and `x¹`; not attempted for lack of time |
| Proposition 3.C.1, general `X ⊆ ℝ^L_+`, p. 47 | Continuous rational `≿` on any `X` has a continuous utility | OPEN. The printed generality is true (Debreu's theorem: every subset of `ℝ^L` is second countable), so there is no counterexample; a proof for disconnected `X` needs Debreu's open-gap lemma, which neither Mathlib nor the Kreps dependencies provide (Kreps's Proposition 2.9 needs connectedness, giving `proposition_3_C_1_convex`) |
| Theorems M.K.1/M.K.2 for merely differentiable `f`, `g`, pp. 956, 959 | Lagrange/Kuhn-Tucker without `C¹` | OPEN: Halkin's (1974) proof needs Brouwer's fixed point theorem, which is in LeanEconomics but not a dependency of this project (dependency requested) |
| Section M.K, p. 958, second-order sufficiency | `x̄` feasible, `L` stationary, `D²_x L` negative definite on `{∇g_m·z = 0}` ⇒ strict local constrained maximizer | `theorem_M_K_second_order_sufficient`, `closerMK_second_order_estimate` |
| Section M.K, p. 958, second-order necessity | At a local constrained maximizer (CQ), `D²_x L` is negative semidefinite on the tangent subspace | OPEN: needs a twice-differentiable feasible curve through `x̄` in every tangent direction (`C²` implicit function theorem) and the second-order chain rule along it; `mk_curve` gives only first order |
| Theorem M.K.5 with inequality constraints, p. 963 | `∂v/∂b_m = λ_m`, `∂v/∂c_k = λ_k` | `theorem_M_K_5_inequality`, `closerMK_prod_decomp` |
| Small type, p. 964 | `x₁ + x₂` on `[0, 1]²` with `q₁x₁ + q₂x₂ ≤ q₁q₂`: maximizers; uhc but not continuous; fails on `[0, 1]²` | `mk964Constraint`, `mk964Argmax`, `mk964_argmax_iff`, `example_M_K_964_argmax`, `example_M_K_964_closed_graph`, `example_M_K_964_not_lhc`, `example_M_K_964_boundary` |

### Part B items

| Source | Claim | Lean |
| --- | --- | --- |
| Small type, pp. 66-67; Figure 3.F.5 | One-sided derivatives of `μ_K` are the least and largest values over the minimizing set | `closerDuality_right_derivative`, `closerDuality_left_derivative`, `proposition_3_F_small_type`, `closerDuality_argmin_nonempty` (compact `K`; correction E5); the figure itself is listed |
| Exercise 3.E.6, p. 98 | CES Hicksian demand and expenditure; Propositions 3.E.2, 3.E.3 | `exercise_3_E_6_hicksian`, `exercise_3_E_6_expenditure`, `cesHicks_apply`, `exercise_3_E_6_homogeneous`, `exercise_3_E_6_monotone`, `exercise_3_E_6_concave`, `exercise_3_E_6_continuous`, `exercise_3_E_6_hicks_properties` |
| Exercise 3.G.2, p. 99 (the "interior version") | Cobb-Douglas satisfies Propositions 3.G.1-3.G.4 | `exercise_3_G_2`, `cobbDouglas_eq_les`, `hicksianDemand_congr`, `les_roy` (Cobb-Douglas as the linear expenditure system with `b = 0`; no interior version of the general propositions is needed) |
| Exercise 3.G.3(a), p. 99 | LES Hicksian demand, expenditure; Propositions 3.E.2, 3.E.3 | `exercise_3_G_3a`, `exercise_3_G_3a_properties`, `lesExpenditure`, `lesHicks` |
| Exercise 3.G.3(b), p. 99 | `∂e/∂p_k = h_k` | `exercise_3_G_3b`, `lesIndex_hasDerivAt`, `lesHicks_apply` |
| Exercise 3.G.3(c), p. 99 | Slutsky equation | `exercise_3_G_3c`, `les_price_derivative`, `les_wealth_derivative`, `les_hicks_derivative` |
| Exercise 3.G.3(d), p. 99 | Negative own-substitution, symmetric cross effects | `exercise_3_G_3d` |
| Exercise 3.G.3(e), p. 99 | `S` negative semidefinite of rank 2 | `exercise_3_G_3e` (rank `L - 1`, kernel `ℝp`), `exercise_3_G_3e_three`, `lesSlutsky_mulVec`, `les_weighted_variance` |
| Exercise 3.G.4(a), "only linear" | Additive separability preserved only by (affine) linear transformations | `exercise_3_G_4a_only_affine`, `closer_additive_monotone_linear` |
| Exercise 3.G.4(c) | No inferior goods with strictly concave `u_l` | `exercise_3_G_4c` |
| Exercise 3.G.4(d) | Gross substitutes if `-t û''/û' < 1` | `exercise_3_G_4d`, `closer_mul_deriv_strictMono` |
| Exercise 3.G.5(a), p. 100 | Composite-commodity problem gives actual `x` and `z = q₀·y` | `exercise_3_G_5a`, `compositeUtility` |
| Exercise 3.G.5(b)-(c), p. 100 | Propositions 3.D.2, 3.G.4 for `x(p, α, w)`, `z(p, α, w)`; 3.E.3, 3.G.1-3.G.3 for the composite Hicksian demand | OPEN: requires showing that `ũ` inherits continuity, local nonsatiation, strict convexity and the differentiability used in those propositions (theorem of the maximum and envelope arguments for the inner problem); not formalized |
| Exercise 3.G.6(c), p. 100 | Restrictions `α = 100`, `β = γ = -5` | `exercise_3_G_6c` (Slutsky symmetry iff), `exercise_3_G_6c_derivatives` |
| Exercise 3.G.6(e), p. 100 | Form of `u` | `exercise_3_G_6e` (`x₁ ≡ x₂`: perfect complements); the form `U(min {x₁, x₂}, x₃)` is verbal, listed |
| Exercise 3.G.9, p. 100 | Slutsky matrix from `v` | `exercise_3_G_9`, `closer_neg_div_hasDerivAt` |
| Exercise 3.G.10, p. 100 | Conditions on Gorman `a`, `b` | `exercise_3_G_10_homogeneous`, `exercise_3_G_10_wealth`, `exercise_3_G_10_prices`, `exercise_3_G_10_continuous` (quasiconvexity remains a condition on `v` itself, listed) |
| Exercise 3.G.12, p. 101 | Gorman form for homothetic and quasilinear preferences | `exercise_3_G_12_homothetic`, `exercise_3_G_12_quasilinear` |
| Exercise 3.G.15(a), p. 101 | Demand for `2x₁^{1/2} + 4x₂^{1/2}` | `exercise_3_G_15a`, `sqDemand`, `sq_tangent`, `sqDemand_eq` |
| Exercise 3.G.15(b), p. 101 | Hicksian demand | `exercise_3_G_15b`, `sqHicks` |
| Exercise 3.G.15(c), p. 101 | Expenditure function, `h = ∇_p e` | `exercise_3_G_15c`, `sqExpenditure` |
| Exercise 3.G.15(d), p. 101 | Indirect utility, Roy's identity | `exercise_3_G_15d_indirect`, `exercise_3_G_15d_roy`, `sqIndirect` |
| Exercise 3.G.16(a), p. 101 | Restrictions on `α`, `β` | `exercise_3_G_16a_homogeneous` (`∑α = 1`, `∑β = 0`, iff), `exercise_3_G_16a_alpha_nonneg`, `exercise_3_G_16a_increasing` |
| Exercise 3.G.16(b), p. 101 | The corresponding indirect utility | `exercise_3_G_16b`, `givenIndirect` |
| Exercise 3.G.16(c), p. 101 | Roy's identity and the Slutsky equation | Roy: `exercise_3_G_16c_roy`. Slutsky equation OPEN: the second price derivatives of `h` and `x` were not computed |
| Exercise 3.G.18, p. 102 | Chains of weak substitutes | `exercise_3_G_18`, `closer_substitute_chain`, `closer_substitute_across` |
| Theorem M.E.2, p. 943 | Transversality theorem | OPEN: needs Sard's theorem for `C^r` maps `ℝ^{N+S} → ℝ^N` (Mathlib has only the equal-dimension, measure-of-critical-values results) |
| Theorem M.G.1, p. 947 | Every point of a compact convex `B ⊆ ℝ^N` is a convex combination of at most `N + 1` extreme points | `theorem_M_G_1`, `theorem_M_G_1_weights`, `theorem_M_G_1_minkowski` (`B = Co(ext B)`), `closerMG_minkowski`, `closerMG_minkowski_finrank`, `closerMG_support_of_endpoint`, `closerMG_endpoint`, `closerMG_face_finrank_lt` |
| Theorem M.L.1 with only `v` differentiable, pp. 965-966 | Envelope theorem without a differentiable solution path | OPEN: needs, for `q` near `q̄`, feasible points `y(q)` with `g(y(q); q) = b̄`, `y(q̄) = x̄`, differentiable in `q` (implicit function theorem for the non-square system under the constraint qualification); then the argument of `theorem_M_K_5` applies |

### Appendix 3.A

| Source | Claim | Lean |
| --- | --- | --- |
| Exercise 3.AA.2, p. 95 | `h(p, u)` upper hemicontinuous | `exercise_3_AA_2_uhc` (Definition 3.AA.1 form, `p ≫ 0`), `exercise_3_AA_2_bounded` (local boundedness, footnote 32) |
| Exercise 3.AA.2, p. 95 | `e(p, u)` continuous | `exercise_3_AA_2_continuous` (jointly on `p ≫ 0`) |
| Exercise 3.AA.2, p. 95 | "even if we replace minimum by infimum and allow `p = 0`" | `exercise_3_AA_2_inf_continuous` (`e(·, ū)` continuous on all of `ℝ^L_+`, any `u`). Joint continuity in `(p, ū)` at boundary prices: OPEN (lower semicontinuity in `ū` at prices with zero components not proved) |
| Exercise 3.AA.2, p. 95 | Conditions for differentiability of `h` | `exercise_3_AA_2_differentiable` (`h` differentiable at `p̄` iff `∇_p e` is) |

### OPEN items

| Item | What is missing |
| --- | --- |
| Exercise 3.D.7(a)-(e) | Rationalizing constructions for each candidate region (and the matching necessary inequalities) |
| Proposition 3.C.1 for a general (disconnected) `X` | Debreu's open-gap lemma |
| Theorems M.K.1/M.K.2, merely differentiable | Brouwer's fixed point theorem (LeanEconomics, not a dependency) for Halkin's proof |
| Second-order necessary conditions, p. 958 | `C²` feasible curves and the second-order chain rule |
| Exercise 3.G.5(b)-(c) | Continuity, convexity and differentiability properties of `ũ` |
| Exercise 3.G.16(c), Slutsky part | Second derivatives of `e` |
| Theorem M.E.2 | Sard's theorem in unequal dimensions |
| Theorem M.L.1 with only `v` differentiable | Implicit function theorem for the constraint system with parameters, non-square case |
| Exercise 3.AA.2, joint continuity of `e` at boundary prices | Continuity of `e(p, ·)` in `ū` at prices with zero components |

## Part F1: hard analysis items (Halkin, second order, envelope, transversality, L = 2 integrability)

Mas-Colell, Whinston and Green, *Microeconomic Theory*, Chapter 3 and Mathematical Appendix M.E,
M.K, M.L. This part closes analysis items listed OPEN in the "Open items" table of
`docs/source-map.md`, in the new modules `HardIntegrability`, `HardHalkin`, `HardSecondOrder`,
`HardEnvelope` and `HardSard`. Printed pages; Lean names relative to `MWG.ClassicalDemand`.
Departures are in `docs/corrections-F1.md`.

### Items closed

| Source | Claim | Lean |
| --- | --- | --- |
| Section 3.H, footnote 18, p. 79 | (3.H.1) has a solution on all of `p₁ > 0` through every initial condition, positive, unique | `footnote_3_18_global`, `footnote_3_18_unique`; ODE layer `hardInt_lipschitz`, `hardInt_unique_Ioo`, `hardInt_unique`, `hardInt_exists_local`, `hardInt_exists_global`, `hardInt_strict_order`; logarithmic coordinates `hardIntLogField`, `hardInt_strictlyPositive_exp`, `hardIntLogField_contDiff`, `hardIntLogField_abs_le`, `hardInt_lift_hasDerivAt`, `hardInt_log_hasDerivAt` |
| Section 3.H, pp. 79-80 | Solutions strictly increasing, continuous and onto `(0, ∞)` in the initial value | `hardInt_solution_family` |
| Section 3.H, p. 80 | `L = 2`: every (C¹) demand with the weak axiom, homogeneity of degree zero and Walras' law is rationalized by preferences, from primitive hypotheses | `integrability_two_goods_global` (C¹, F1-1) |
| Theorem M.K.1, p. 956 | Lagrange multipliers with merely differentiable functions | `theorem_M_K_1_differentiable` (f differentiable at `x̄`; `g_m` differentiable at `x̄`, continuous near it), `theorem_M_K_1_book` (all differentiable on `ℝ^N`, as printed); Halkin's lemma `hardHalkin_feasible` and cone lemma `hardHalkin_cone` (LeanEconomics `brouwer`) |
| Theorem M.K.2, p. 959 | Kuhn-Tucker conditions with merely differentiable functions | `theorem_M_K_2_differentiable`, `theorem_M_K_2_book` |
| Section M.K, p. 958 | Second-order necessary conditions: `D²_x L(x̄, λ)` negative semidefinite on `{z : ∇g_m(x̄)·z = 0}` | `theorem_M_K_second_order_necessary`, `theorem_M_K_second_order_necessary_matrix` (Hessian form), key estimate `hardSO_bound`. Feasible points from Halkin's lemma replace the C² curves (first-order accuracy suffices since `∇L(x̄) = 0`) |
| Theorem M.L.1, (M.L.4)-(M.L.5), pp. 965-966 | Envelope theorem with only `v` differentiable | `theorem_M_L_1_value` (with the constraint qualification, F1-2); `hardEnv_range_pi_eq_top`; the constraint qualification is needed: `theorem_M_L_1_needs_CQ` |
| Theorem M.E.2, p. 943; footnote 11 | Transversality theorem: regular for almost every `q̄ ∈ B` | `theorem_M_E_2` (bad set has Lebesgue measure zero), `theorem_M_E_2_ae`, `theorem_M_E_2_regular` (`RegularSystemAt` a.e. for `A = ℝ^N`, `B = ℝ^M`); local step `hardSard_local`, `hardSard_exists_complement_map`, `hardSard_isInvertible_of_injective`. Uses Mathlib's equal-dimension Sard lemma `addHaar_image_eq_zero_of_det_fderivWithin_eq_zero` in charts of the zero set (inverse function theorem); no unequal-dimension Sard theorem is needed |

### Items still OPEN

| Source | Item | What remains |
| --- | --- | --- |
| Section 3.H, pp. 79-80 | Integrability sufficiency for `L > 2` (Frobenius): a C¹ demand with homogeneity of degree zero, Walras' law and a symmetric negative semidefinite Slutsky matrix has solutions of (3.H.2) | Not proved. The planned route: define `E(p)` by the scalar ODE `y' = (p - p⁰)·x(p⁰ + t(p - p⁰), y)`, `y(0) = w⁰`, on `[0, 1]`. Global existence on `[0, 1]` follows as in `HardIntegrability` (Walras' law and `x ≥ 0` give `|(p - p⁰)·x| ≤ c·w`, so in `log w` the field is bounded). The missing step is the differentiability of `E` with `∇E(p) = x(p, E(p))`. Mathlib v4.34.0 has existence, uniqueness, Gronwall bounds and Lipschitz dependence on the initial point (`Mathlib/Analysis/ODE/*`), but no differentiable dependence of solutions on initial data or parameters. The direct argument: for `δ(t) = y(t; p + εh) - y(t; p)`, the function `δ*(t) = tε h·x(γ_p(t), y(t; p))` solves the linearized equation exactly, because the defect is `tε (hᵀS v - vᵀS h) = 0` by Slutsky symmetry (`v = p - p⁰`); Gronwall's inequality for `δ - δ*` with a uniform first-order Taylor remainder of `(q, w) ↦ (q - p⁰)·x(p⁰ + t(q - p⁰), w)` on compact sets would give `δ(1) = ε h·x(p, E(p)) + o(ε)`. The uniform Taylor remainder and this Gronwall estimate are not formalized |
| Small type, p. 80 | One-price-at-a-time construction for general `L` | Same missing ingredient (differentiability of an ODE solution in the prices held fixed) |

## Part F3: Frobenius integrability for any L

Mas-Colell, Whinston and Green, *Microeconomic Theory*, Section 3.H, pp. 79-80. This part closes
the two items left OPEN in `docs/source-map.md` and `docs/source-map-F1.md`: the sufficiency half
of Frobenius' theorem for (3.H.2), hence the integrability theorem for any number of goods from
primitive hypotheses, and the small-type one-price-at-a-time construction. New modules
`FrobeniusDependence`, `FrobeniusTheorem`, `FrobeniusIntegrability`, `FrobeniusOnePrice`
(37 theorems). Printed pages; Lean names relative to `MWG.ClassicalDemand`. Departures are in
`docs/corrections-F3.md`.

### Items closed

| Source | Claim | Lean |
| --- | --- | --- |
| Section 3.H, p. 80 | Frobenius' theorem, sufficiency: symmetry of the derivative matrix of (3.H.2) gives a solution (general form, one unknown function) | `frobenius_ray_family` (system `∂Z/∂q = f(q, Z)` on `ℝ^L × ℝ`, `f` `C¹`, `|v·f| ≤ ‖v‖`, integrability condition `h·Df(v, v·f) = v·Df(h, h·f)`; solutions through every initial value, defined on all of `ℝ^L`); ray construction `frobRayField`, `frobRayField_contDiff`, `frobRayField_abs_le`, `frobRayField_fderiv_apply`, `frob_ray_exists`, `frob_ray_unique`, `frob_ray_strict_order`, `frob_hasDerivAt_dotProduct` |
| (needed for the above; not in Mathlib v4.34.0) | Differentiable dependence of an ODE solution on a parameter, given a solution of the variational equation | `frob_hasFDerivAt_endpoint` (two Gronwall estimates: Lipschitz dependence, then the first-order remainder); `frob_uniform_taylor` (uniform first-order Taylor remainder on compact convex sets) |
| Equation (3.H.2), pp. 79-80 | For `C¹` demand with Walras' law, `x ≥ 0` and symmetric `S(p, w)`, (3.H.2) has a solution through every `(p⁰, w⁰) ≫ 0`, on all of `p ≫ 0` | `frob_3_H_2_exists`; family indexed by utility, strictly increasing, continuous and onto `(0, ∞)` in `u`: `frob_expenditure_family`. Logarithmic coordinates: `frobLogField`, `frobLogField_contDiff`, `frobLogField_abs_dot_le`, `frobLogField_fderiv_apply`, `frobLogField_dot_fderiv`, `frobLogField_symm` (symmetry of `S` is the integrability condition), `frob_slutsky_mulVec`, `frob_exp_mem_domain`, `frob_hasFDerivAt_log`, `frob_solvesPDE_of_log` |
| Section 3.H, p. 80 | "The necessary and sufficient condition for the recovery of an underlying expenditure function is the symmetry and negative semidefiniteness of the Slutsky matrix" (sufficiency, any `L`) | `integrability_general`: a `C¹`, nonnegative demand with Walras' law and symmetric negative semidefinite `S` is the Walrasian demand of the recovered preference at every `(p, w) ≫ 0`. Necessity was already proved (`pde_slutsky_symmetric`, Section 2.F results) |
| Small type, p. 80 | Each one-price subproblem is an equation of the form (3.H.1) and "can be solved"; this "makes mechanical sense even if `S(p, w)` is not symmetric" | `frob_line_exists` (global positive solution on `r > 0`, no symmetry), `frob_line_unique`; logarithmic coordinates `frobLineField`, `frobLineField_contDiff`, `frobLineField_abs_le`, `frob_line_lift`, `frob_line_log`; `frob_update_strictlyPositive` |
| Small type, p. 80 | Changing prices one at a time from `p⁰` to `p̄` "we eventually get to `e(p̄)`" | `frob_one_price_at_a_time` (any solutions of the successive subproblems end at `E(p̄)` for any solution `E` of (3.H.2)), `frob_one_price_at_a_time_exists` (from primitive hypotheses, with symmetric `S`); `frob_line_hasDerivAt` (a solution of (3.H.2) solves each subproblem); path `frobOnePricePath`, `frobOnePricePath_pos`, `frobOnePricePath_zero`, `frobOnePricePath_last`, `frobOnePricePath_update_start`, `frobOnePricePath_update_end` |
| Small type, p. 80 | Without symmetry, `e(p̄)` depends on the path ("absurdity") | Verbal. Without symmetry (3.H.2) has no solution (`pde_slutsky_symmetric`, `section_3_H_no_solution`); an explicit path dependence is `exercise_3_I_7b` |

### Items still OPEN

None from this part.

## Part F2: economics items (Debreu, 3.D.7, 3.H.2, 3.I, 3.AA.2)

Mas-Colell, Whinston and Green, *Microeconomic Theory*, Chapter 3. Part F2 works through the
ECONOMICS items of the "Open items" table at the top of [source-map.md](source-map.md):
Proposition 3.C.1 for a general consumption set, Exercises 3.D.7, 3.G.5(b)-(c), 3.G.16(c),
3.H.2, 3.I.8(a) ("only if"), 3.AA.2, footnote 28 (CV) and the asymptotic comparisons of CV, EV
and AV on pp. 89-91 with footnote 29. Modules `EconDebreu`, `EconIntegrability`,
`EconGivenExpenditure`, `EconBoundary`, `EconWelfare`, `EconRevealed`. Printed pages; Lean names
relative to `MWG.ClassicalDemand`. Departures are in [corrections-F2.md](corrections.md).

### Status of the assigned open items

| Source | Item | Status after part F2 |
| --- | --- | --- |
| Proposition 3.C.1, p. 47 | Continuous utility for a general (possibly disconnected) `X` | CLOSED: `proposition_3_C_1_general` |
| Exercise 3.D.7(a)-(e), p. 98 | Regions of permissible `x¹`, with rationalizations | CLOSED for (a), (b), (c), (e); (d) necessity proved, sufficiency OPEN |
| Exercise 3.G.5(b)-(c), p. 100 | Composite-commodity demand and `ũ` | OPEN |
| Exercise 3.G.16(c), p. 101 | Slutsky equation | CLOSED: `exercise_3_G_16c_slutsky` |
| Exercise 3.H.2 / p. 78 | Differentiable `e` ⇒ every generating preference convex | CLOSED: `exercise_3_H_2_convex`, `exercise_3_H_2_prefConvex` |
| Exercise 3.I.8(a) | "Only if": wealth-independent demand ⇒ quasilinear utility | OPEN |
| Footnote 28, p. 90 | CV part | CLOSED: `footnote_3_I_28_cv` |
| pp. 89-91, footnote 29 | Asymptotic comparisons of CV, EV, AV | Partly CLOSED (relative errors, second-order accuracy of (3.I.9)); comparison with the deadweight loss and footnote 29 OPEN |
| Exercise 3.AA.2 | Joint continuity of `e(p, ū)` at boundary prices | CLOSED by counterexample: `exercise_3_AA_2_boundary_counterexample` (correction F2-1) |

### Section 3.C: Proposition 3.C.1 (module `EconDebreu`)

| Source | Claim | Lean |
| --- | --- | --- |
| Proposition 3.C.1, p. 47 | A continuous rational `≿` on any `X ⊆ ℝ^L` (in particular any `X ⊆ ℝ^L_+`, connected or not) has a utility continuous on `X` | `proposition_3_C_1_general` |
| Proof (Debreu's theorem) | On any second-countable space, a continuous rational preference has a continuous representation | `econ_debreu_representation` |
| Proof, step 1 | Countable base `bₙ`; `v(x) = ∑ {2⁻ⁿ : bₙ ⊆ {z : x ≻ z}}` represents `≿`, values in `[0, 2]` | `econBaseUtility`, `econBaseUtility_summable`, `econBaseUtility_bounds`, `econBaseUtility_represents`, `econ_exists_nat_basis` |
| Proof, step 2 (open-gap lemma) | If all `{v < v z}`, `{v > v z}` are open, a strictly increasing transformation of `v` is continuous | `econ_gap_lemma` (via `econJumps`, `econDense`, `econGapOrder`, `econGapUtility`, `econJumps_countable`, `econDense_countable`, `econDense_subset`, `econDense_between`) |

### Section 3.D: Exercise 3.D.7 (module `EconRevealed`)

`p⁰ = (1, 1)`, `w⁰ = 8`, `x⁰ = (4, 4)`, `p¹ = (1, 4)`, `w¹ = 26`, `x¹ = (26 - 4t, t)`
(`econP0`, `econP1`, `econX0`, `econP0_dot`, `econP1_dot`, `econX0_mem`).

| Source | Claim | Lean |
| --- | --- | --- |
| Exercise 3.D.7(a), p. 98 | Any (locally nonsatiated) preference maximization: region `t < 6`; Afriat-type utility `min(p⁰·x - 8, c(p¹·x - 26) + s - 8)` | `exercise_3_D_7a_necessary`, `exercise_3_D_7a`, `econ_affine_concaveOn` |
| Exercise 3.D.7(b), p. 98 | Quasilinear in good 1: region `t ≤ 4`; `φ(τ) = min(4τ, 3t + τ, 3t + 4)` | `exercise_3_D_7b`, `econQL` |
| Exercise 3.D.7(c), p. 98 | Quasilinear in good 2: region `x¹₁ ≥ 4` (`t ≤ 11/2`); `φ(τ) = min(τ, 3 + τ/4, 3 + x¹₁/4)` | `exercise_3_D_7c` |
| Exercise 3.D.7(d), p. 98 | Both goods normal: necessarily `t ≤ 11/2` | `exercise_3_D_7d`; sufficiency OPEN (below) |
| Exercise 3.D.7(e), p. 98 | Homothetic: region `t ≤ 26/5`; `u = min(p⁰·x, (2/5)p¹·x)` | `exercise_3_D_7e` |
| Exercise 3.D.7, hint | Pictures | Listed only (graphical) |

### Section 3.G: Exercise 3.G.16(c) (module `EconGivenExpenditure`)

| Source | Claim | Lean |
| --- | --- | --- |
| Exercise 3.G.16(c), p. 101 | Hicksian demand `h_l = ∂e/∂p_l = e(α_l + β_lΠu)/p_l` | `givenHicks`, `econ_givenHicks_hasDerivAt`, `econ_givenPi_hasDerivAt`, `econ_givenA_hasDerivAt` |
| Exercise 3.G.16(c), p. 101 | Walrasian demand `x_l = w(α_l + β_l(log w - A))/p_l = h_l(p, v(p, w))` | `givenDemand`, `econ_givenDemand_eq` |
| Exercise 3.G.16(c), p. 101 | Slutsky equation `∂h_l/∂p_k = ∂x_l/∂p_k + (∂x_l/∂w)x_k` at `w = e(p, u)` | `exercise_3_G_16c_slutsky` (Roy's identity: `exercise_3_G_16c_roy`, earlier module) |

### Section 3.H: Exercise 3.H.2 (module `EconIntegrability`)

| Source | Claim | Lean |
| --- | --- | --- |
| Small type, p. 78; Exercise 3.H.2, p. 102 | If `e(·, ū)` is differentiable at every `p ≫ 0`, the at-least-as-good set of a continuous, locally nonsatiated, strongly monotone `≿` is convex and equals `V_ū` | `exercise_3_H_2_convex`, `econ_recoveredSet_subset` |
| Small type, p. 78; Exercise 3.H.2 | Differentiable `e` (all levels) ⇒ every such generating preference is convex | `exercise_3_H_2_prefConvex` |
| Proof | Penalised problem `min p·c - e(p) + ε∑(p_l + 1/p_l)` attains its minimum at some `p* ≫ 0`; first-order conditions `∂e/∂p_l = c_l + ε - ε/p*_l²` | `econPenalty`, `econPenalty_ge_term`, `econPenalty_nonneg`, `econPenalty_exists_min`, `econPenalty_foc` |

### Section 3.I: welfare approximations (module `EconWelfare`)

| Source | Claim | Lean |
| --- | --- | --- |
| Footnote 28, p. 90 | `∂CV(p¹, p⁰, w)/∂p¹_l` at `p⁰_l` equals `x_l(p⁰, w)` (no differentiability of `e` in `u` or of `v` needed) | `footnote_3_I_28_cv`, `econ_priceLine_priceLine` (EV and AV parts: `footnote_3_I_28_ev`, `footnote_3_I_28_av`, earlier module) |
| Section 3.I, p. 89, footnote 27 | For small price changes the AV error (and the EV-CV gap) is small as a fraction of the welfare change | `welfare_av_relative_error`, `welfare_ev_relative_error` |
| Section 3.I, p. 89 | The same holds for any measure with the same first derivative | `econ_relative_error_of_deriv` |
| Section 3.I, pp. 90-91, (3.I.9) | The `h̃` approximation is a second-order expansion of `e`: error `o((p¹_l - p⁰_l)²)` | `equation_3_I_9_second_order`, `econ_second_order_taylor` |
| Section 3.I, p. 90, Figure 3.I.8 | The AV error need not be small relative to the deadweight loss | OPEN (below) |
| Footnote 29, p. 90 | AV can misrank equal-revenue taxes even for small taxes | OPEN (below) |
| Section 3.I, p. 91 | `h̃` better than AV for small changes; "adequate approximation to the deadweight loss" | Second-order accuracy proved (`equation_3_I_9_second_order`); the ratio statement against the deadweight loss OPEN (below) |

### Appendix 3.A: Exercise 3.AA.2 (module `EconBoundary`)

| Source | Claim | Lean |
| --- | --- | --- |
| Exercise 3.AA.2, p. 95 | `e(p, ū)` continuous "allowing `p = 0`": false jointly at boundary prices | `exercise_3_AA_2_boundary_counterexample`, `econBoundaryUtility`, `econBoundaryPrice`, `econBoundaryUtility_continuousOn`, `econBoundaryUtility_lns`, `econBoundaryPrice_dot` (correction F2-1); corrected statements `exercise_3_AA_2_continuous`, `exercise_3_AA_2_inf_continuous` (earlier module) |

### OPEN after part F2

| Source | Item | What remains |
| --- | --- | --- |
| Exercise 3.D.7(d), p. 98 | Sufficiency: every `x¹ = (26 - 4t, t)`, `t ≤ 11/2`, chosen by a preference on `ℝ²_+` with both goods normal | A demand *function* on all of `ℝ²_{++} × ℝ_+` with normal goods through `x⁰` and `x¹`. For `t ≤ 26/5` the homothetic utility of (e) works once a normal (degree-one) selection of its demand correspondence is written down; for `t ∈ (26/5, 11/2]` a non-homothetic construction (e.g. quasilinear in good 2 with a smooth strictly concave `φ`, `φ'(4) = 1`, `φ'(x¹₁) = 1/4`, and its corner solutions on `ℝ²_+`) must be verified for all `(p, w)` |
| Exercise 3.G.5(b)-(c), p. 100 | Propositions 3.D.2, 3.G.4 for `x(p, α, w)`, `z(p, α, w)`; 3.E.3, 3.G.1-3.G.3 for the Hicksian demand of `ũ` | Transfer through `x(p, α, w) = x(p, αq₀, w)`, `z = q₀·y(p, αq₀, w)`: HD0, Walras' law and convexity/uniqueness are immediate; the Slutsky matrix of the composite demand is `JᵀSJ` with `J = diag(I, q₀)` (chain rule on the product of `ℝ^A` and `ℝ^B`, which this project's `Fin L` demand machinery does not support); for (c), `ũ` must be shown continuous (Berge), locally nonsatiated and strictly quasiconcave, which the project's EMP results on `ℝ^{A+1}_+` then need through an identification of `(Fin A → ℝ) × ℝ` with `Fin (A + 1) → ℝ` |
| Exercise 3.I.8(a) | "Only if": demand for goods 1, 2 independent of wealth ⇒ utility quasilinear in good 3 | By Shephard's lemma `∂e/∂p_l(p, u) = x_l(p)` is independent of `u` (`l = 1, 2`), so `e(p, u) = A(p) + B(u)` and `B(v(p, w)) = w - A(p)` is an indirect utility; the recovered utility is `x₃ + inf_p(p₁x₁ + p₂x₂ - A(p))`. Missing: the EMP and Shephard's lemma on the quasilinear consumption set `ℝ²_+ × ℝ` (the project's are on `ℝ^L_+`, where wealth-independence fails at low wealth), and, for preferences rather than utilities, the duality step that recovers `≿` on non-demanded bundles (convexity and monotonicity needed) |
| p. 90, Figure 3.I.8; footnote 29 | AV error not small relative to the deadweight loss; AV can misrank two equal-revenue taxes for small taxes | An explicit example. For Cobb-Douglas `x₁ = αw/p₁`, with the price of good 1 raised from `a` to `s`: `DWL(s) = w((s/a)^α - 1) - αw(s - a)/s ~ α(α+1)w(s - a)²/(2a²)` and the AV-based loss differs by `-α²w(s - a)²/(2a²) + o`, so the relative error tends to `-α/(α+1) ≠ 0`; formalizing needs the second-order expansions of these explicit functions (`econ_second_order_taylor` applies) and their identification with the project's `compensatingVariation`/`areaVariation` for Cobb-Douglas; footnote 29 then needs two goods with different wealth effects and equal revenue |

## Part G: last items (3.D.7(d), 3.G.5, 3.I.8(a), Figure 3.I.8, footnote 29)

Mas-Colell, Whinston and Green, *Microeconomic Theory*, Chapter 3. Part G closes the five items
left OPEN in [source-map-F2.md](source-map.md): Exercise 3.D.7(d) (sufficiency), Exercise
3.G.5(b)-(c), Exercise 3.I.8(a) ("only if"), the deadweight-loss comparison of p. 90 (Figure
3.I.8) and the Cobb-Douglas computation attached to footnote 29. Modules `LastRevealed`,
`LastWelfare`, `LastQuasilinear`, `LastComposite`, `LastCompositeApps`. Printed pages; Lean names
relative to `MWG.ClassicalDemand`. Departures are in [corrections-G.md](corrections.md).

### Status of the assigned items

| Source | Item | Status after part G |
| --- | --- | --- |
| Exercise 3.D.7(d), p. 98 | Both goods normal: region `t = x¹₂ ≤ 11/2`, sufficiency | CLOSED: `exercise_3_D_7d_iff` (correction G-1) |
| Exercise 3.G.5(b)-(c), p. 100 | Propositions 3.D.2, 3.G.4 for `x(p, α, w)`, `z(p, α, w)`; 3.E.3, 3.G.1-3.G.3 for the Hicksian demand of `ũ` | CLOSED: `exercise_3_G_5b`, `exercise_3_G_5b_actual`, `exercise_3_G_5b_roy`, `exercise_3_G_5c_E3`, `exercise_3_G_5c_G1`, `exercise_3_G_5c_G2`, `exercise_3_G_5c_G3` (correction G-3) |
| Exercise 3.I.8(a), p. 103 | "Only if": wealth-independent demand ⇒ quasilinear utility | CLOSED: `exercise_3_I_8a_only_if`, `exercise_3_I_8a_only_if_all` (correction G-4) |
| Section 3.I, p. 90, Figure 3.I.8 | The AV deadweight loss can be far off as a fraction of the deadweight loss, even for small price changes | CLOSED: `figure_3_I_8`, `figure_3_I_8_ev`, `figure_3_I_8_cv` |
| Footnote 29, p. 90 | Cobb-Douglas computation with limit `-α/(α+1)` | CLOSED for the measure that gives this limit: `footnote_3_I_29_mixed` (correction G-2). The footnote's own claim (misranking of two equal-revenue taxes) remains OPEN (last table) |

### Section 3.D: Exercise 3.D.7(d) (module `LastRevealed`)

`p⁰ = (1, 1)`, `w⁰ = 8`, `x⁰ = (4, 4)`, `p¹ = (1, 4)`, `w¹ = 26`, `x¹ = (26 - 4t, t)`.

| Source | Claim | Lean |
| --- | --- | --- |
| Exercise 3.D.7(d), p. 98 | `x¹ ∈ ℝ²_+` with `p¹·x¹ = 26` is chosen, together with `x⁰`, by a continuous, concave, monotone utility on `ℝ²_+` whose demand function (on `p ≫ 0`, `w ≥ 0`) has both goods normal at every `p`, iff `t ≤ 11/2` | `exercise_3_D_7d_iff` |
| Necessity | Any locally nonsatiated preference with a demand function on `p ≫ 0` and good 1 normal at `p¹` has `t ≤ 11/2` | `last_exercise_3_D_7d_necessary` |
| Sufficiency: utility | `u(x) = x₂ + φ(x₁)`, `φ(τ) = min(τ, 3 + τ/4, 3 + x¹₁/4)`, on `ℝ²_+`; continuous, concave, monotone, locally nonsatiated | `lastPhi`, `lastNormalUtility`, `lastNormalUtility_continuous`, `lastNormalUtility_concaveOn`, `lastNormalUtility_monotone`, `last_lns_of_monotone` |
| Sufficiency: demand function | `x₁ = min(w/p₁, c(p))`, `x₂ = (w - p₁x₁)/p₂`, `c(p) ∈ {0, 4, x¹₁}` by the price ratio; it solves the UMP at every `p ≫ 0`, `w ≥ 0` and both coordinates are nondecreasing in `w` | `lastNormalLevel`, `lastNormalDemand`, `lastNormalLevel_nonneg`, `lastPhi_quarter`, `lastPhi_opt`, `lastNormalDemand_mem`, `lastNormalDemand_mono` |
| (on `exercise_3_D_7d`) | The hypothesis "optimal at every `(p, w)`, `p = 0` included" is never satisfied by a locally nonsatiated preference | `last_exercise_3_D_7d_hyp_unsatisfiable` (correction G-1) |

### Section 3.G: Exercise 3.G.5(b)-(c) (modules `LastComposite`, `LastCompositeApps`)

Standing assumptions: `q₀ ≫ 0`; `u` continuous on `ℝ^A_+ × ℝ^B_+`, strictly increasing in the
`y` goods, strictly quasiconcave on `ℝ^{A+B}_+`. Consistent: `last_composite_instance`
(`u = √x + √y`, `q₀ = 1`).

| Source | Claim | Lean |
| --- | --- | --- |
| Bridge | `(x, z) ∈ ℝ^A × ℝ` ↔ `Fin.snoc x z ∈ ℝ^{A+1}`; prices `(p, α)`; `(p, α)·(x, z) = p·x + αz`; orthant and `≫ 0` correspond | `lastSnoc`, `lastCompositeVec`, `lastCompositeVec_snoc`, `lastSnoc_init`, `lastSnoc_castSucc`, `lastSnoc_last`, `last_snoc_dot`, `last_snoc_mem`, `last_snoc_pos` |
| Exercise 3.G.5, p. 99 | `ũ(x, z) = max_{y ≥ 0, q₀·y ≤ z} u(x, y)`: the max is attained; at a maximizer `q₀·y = z` | `last_composite_set_eq`, `last_composite_attained`, `last_composite_section`, `last_composite_exhausts` |
| Exercise 3.G.5(c) | `ũ` is continuous on `ℝ^{A+1}_+` (Berge) | `last_composite_continuousOn` |
| Exercise 3.G.5(c) | The preference of `ũ` is locally nonsatiated | `last_composite_lns` |
| Exercise 3.G.5(c) | `ũ` is strictly quasiconcave (its preference strictly convex) | `last_composite_strictlyQuasiconcave`, `last_composite_hyps` |
| Exercise 3.G.5(b), Proposition 3.D.2 | `(x, z)(p, α, w)`: homogeneous of degree zero, Walras' law `p·x + αz = w`, exists and is unique | `exercise_3_G_5b` |
| Exercise 3.G.5(b) with (a) | The composite demand is `{(x*, q₀·y*)}` for the consumer's actual choice `(x*, y*)` at `(p, αq₀, w)` | `exercise_3_G_5b_actual` |
| Exercise 3.G.5(b), Proposition 3.G.4 | Roy's identity for the composite demand where `ṽ` is differentiable | `exercise_3_G_5b_roy` |
| Exercise 3.G.5(c), Proposition 3.E.3 | Hicksian demand of `ũ`: homogeneous of degree zero in `P`, no excess utility, single-valued | `exercise_3_G_5c_E3` |
| Exercise 3.G.5(c), Proposition 3.G.1 | Shephard's lemma for `ẽ(·, ū)` | `exercise_3_G_5c_G1` |
| Exercise 3.G.5(c), Proposition 3.G.2 | `D_P h̃ = D²_P ẽ`, negative semidefinite, symmetric, `D_P h̃ P = 0` | `exercise_3_G_5c_G2` |
| Exercise 3.G.5(c), Proposition 3.G.3 | Slutsky equation for the composite demand | `exercise_3_G_5c_G3` |

### Section 3.I: Exercise 3.I.8(a), "only if" (module `LastQuasilinear`)

Numeraire `k` (the book's good 3), consumption set `X = {x : x_l ≥ 0, l ≠ k}` (Definition
3.B.7), normalized prices `P = {p ≫ 0, p_k = 1}` (`lastNormPrices`).

| Source | Claim | Lean |
| --- | --- | --- |
| Exercise 3.I.8(a), p. 103 | If `u` is continuous on `X`, strictly increasing in good `k`, and its demand for the goods `l ≠ k` is a continuous wealth-independent function `y(p)` (`y(p) + (w - p·y(p)) e_k ∈ x(p, w)` for all `w ∈ ℝ`), then `x_k + φ(x)`, `φ(x) = inf_{p ∈ P}(p·x - x_k - E(p))` independent of `x_k`, represents `u` on every demanded bundle | `exercise_3_I_8a_only_if` |
| Same | If every bundle of `X` is demanded at some prices, `x_k + φ(x)` represents `u` on `X` | `exercise_3_I_8a_only_if_all` |
| Proof | `P` is convex; a function with increments `≤ |(p' - p)·(y(p') - y(p))|`, `y` continuous, is constant on `P` (zero derivative along segments) | `lastNormPrices_convex`, `last_const_of_small_variation` |
| Hypotheses consistent | `u = x₂ + 2√x₁`, `y(p) = (1/p₁², 0)` satisfy all hypotheses | `lastSqrtUtility`, `lastSqrtDemand`, `last_3_I_8a_instance` |
| Exercise 3.I.8(a), "if" | (earlier module) | `exercise_3_I_8a` |

### Section 3.I: Figure 3.I.8 and footnote 29 (module `LastWelfare`)

Cobb-Douglas `x₁^α x₂^{1-α}`, `α ∈ (0, 1)`, `p⁰ ≫ 0`, `w > 0`; the price of good 1 moves from
`a = p⁰₁` to `s`, `p¹ = (s, p⁰₂)`, `τ = s - a`. Measures: (3.I.5) `DWL_EV = -τx₁(p¹, w) - EV`;
(3.I.6) `DWL_CV = -CV - τh₁(p¹, u⁰)`; the Walrasian-curve version `DWL_AV = -AV - τx₁(p¹, w)`.

| Source | Claim | Lean |
| --- | --- | --- |
| Closed forms | The three measures (and the mixed measure) computed from the project's `expenditure`, `indirectUtility`, `equivalentVariation`, `compensatingVariation`, `hicksianOf`, `areaVariation`; `e(p, v(p', w)) = wC(p')/C(p)`; `AV = αw log(a/s)` | `last_cd_dwl_ev_eq`, `last_cd_dwl_cv_eq`, `last_cd_dwl_av_eq`, `last_cd_dwl_mixed_eq`, `last_cd_expenditure_indirect`, `last_cdConst_priceLine`, `last_priceLine_zero`, `last_priceLine_one`, `lastQ`, `lastQ_pos`, `lastQ_self`, `lastQ_hasDerivAt`, `lastDwlEV`, `lastDwlCV`, `lastDwlAV`, `lastDwlMixed` |
| Expansions | `DWL_EV, DWL_CV = α(1-α)w(s-a)²/(2a²) + o`, `DWL_AV = αw(s-a)²/(2a²) + o`, mixed `α(1+α)w(s-a)²/(2a²) + o` | `lastDwlEV_expansion`, `lastDwlCV_expansion`, `lastDwlAV_expansion`, `lastDwlMixed_expansion`, `last_quadratic_of_deriv`, `last_revenue_hasDerivAt`, `last_inv_sq_hasDerivAt` |
| Ratio lemma | `F ≈ c(s-a)²`, `G ≈ d(s-a)²`, `c ≠ 0` ⇒ `(G - F)/F → (d - c)/c` | `last_ratio_limit` |
| Section 3.I, p. 90, Figure 3.I.8 | "The percentage difference between these two areas need not grow small as the price change grows small": `(DWL_AV - DWL)/DWL → α/(1-α) ≠ 0` for both book measures | `figure_3_I_8_ev`, `figure_3_I_8_cv`, `figure_3_I_8` |
| Footnote 29, p. 90 (computation of source-map-F2) | With the mixed measure `-CV - τx₁(p¹, w)`, the limit is `-α/(α+1)` | `footnote_3_I_29_mixed` |

### OPEN after part G

| Source | Item | What remains |
| --- | --- | --- |
| Footnote 29, p. 90 | "The area variation measure need not give the correct ranking even for small taxes" (two taxed goods, equal revenue `T`) | Cobb-Douglas cannot show it: with taxes on goods of shares `α₁, α₂` and equal revenue, both rankings are by `α_l` at leading order. A three-good example that works at leading order: `u = x₁^α (x₃ + 2β√x₂)^{1-α}` (full income `W = w + β²/p₂`, `x₁ = αW/p₁`, `x₂ = β²/p₂²`, good 2 without wealth effect) at `p = (1, 1, 1)` with `α < 1/5` and `max(2β²/(1-α), (1-α)β²/(2α)) < W < β²/(2α)` (e.g. `α = 1/10`, `β = 1`, `W = 4.75`): then `DWL₁ ≈ R²(1-α)/(2αW) < DWL₂ ≈ R²/β² < AV-DWL₁ ≈ R²/(2αW)`. Missing: the EMP/UMP closed forms for this utility on `ℝ³_+` (corner `x₃ = 0` at low wealth), the equal-revenue tax rates as functions of `T` (inverting `τ x_l(p + τe_l)`), and the second-order expansions in `T` |
