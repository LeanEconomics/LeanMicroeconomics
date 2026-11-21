# Source map

Mas-Colell, Whinston and Green, *Microeconomic Theory*, Chapter 14, "The Principal-Agent
Problem", pp. 477-510, with Appendices A and B and all end-of-chapter exercises. Printed pages;
Lean names relative to `MWG.PrincipalAgent` (hidden-action names in `HAModel`, hidden-information
names in `HIModel`, the two-type screening program in `Screen`). In Section 14.B profits have a
density `f(π|e)` with respect to an arbitrary measure `ν` on `ℝ` (MWG: Lebesgue measure on
`[π̲, π̄]`; footnote 6's discrete version is a sum of Dirac masses, `dmeas`). The printed chapter
has two states in Section 14.C (and `N` states in Exercise 14.C.1); it has no continuum-of-types
model. No item is **OPEN**. Departures are in [corrections](corrections.md).

## Section 14.A: introduction

| Source | Claim | Lean |
| --- | --- | --- |
| 14.A, pp. 477-478, footnote 1 | Hidden actions and hidden information; uses of "moral hazard" | verbal |

## Section 14.B: hidden actions

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 478-479, footnotes 2-4 | The model: profits with density `f(π|e) > 0`, effort set `E`, observability of actions to courts | `HAModel`, `HAModel.Standing`, `HAModel.Adm`, `HAModel.EW`, `HAModel.EV`, `HAModel.GP`; footnotes 2-4 verbal |
| p. 479 | Strict first-order stochastic dominance; it raises expected profit | `HAModel.F`, `HAModel.FOSD` (strict at a point, corrections 6); profit comparison: `exA_GP` (instance) |
| pp. 479-480, footnote 5 | `u(w, e) = v(w) - g(e)`, `v' > 0`, `v'' ≤ 0`, `g(e_H) > g(e_L)`; risk-neutral owner | `HAModel.EU`, `HAModel.OP`, `HAModel.Standing` (`v_deriv`, `dv_pos`, `v_conc`); footnote 5: Exercise 14.B.1 |
| (14.B.1), p. 480 | The owner's problem with observable effort | `HAModel.ObsFeasible`, `HAModel.IsObsOptimal`, `HAModel.ha_OP_eq` |
| (14.B.2), p. 480 | Cost minimization for a given effort; the constraint binds | `HAModel.IsCostMin`, `HAModel.ha_costMin_binds` |
| (14.B.3), footnote 6, p. 481 | First-order condition; with `v'` strictly decreasing it forces a fixed wage; full-measure qualification | `HAModel.ha_foc_constant`, `HAModel.ha_costMin_unique` (a.e., footnote 6), discrete version `dmeas` |
| (14.B.4), p. 481 | The fixed wage `w*_e` with `v(w*_e) - g(e) = ū` is optimal; higher for `e_H` | `HAModel.ha_cost_lower_bound`, `HAModel.ha_fixed_wage_feasible`, `HAModel.ha_fixed_wage_costMin`, `HAModel.ha_wage_higher`; Jensen: `tpa_jensen`, `tpa_jensen_eq`, `HAModel.ha_EV_le` |
| p. 481 | Risk-neutral manager: every scheme with expected wage `ū + g(e)` is optimal | `HAModel.ha_riskNeutral_costMin` |
| (14.B.5), Proposition 14.B.1, p. 481 | Optimal observable-effort contract; uniquely optimal if `v'' < 0` | `HAModel.proposition_14_B_1`, `HAModel.proposition_14_B_1_unique` (a.e.); instance `exA_proposition_14_B_1` |
| (14.B.6)-(14.B.8), Proposition 14.B.2, pp. 482-483 | Risk-neutral manager: selling the project attains the first best; every optimal contract gives the same effort and utilities | `HAModel.proposition_14_B_2`, `HAModel.proposition_14_B_2_every`, `HAModel.ha_value_le_obs`; instance `exA_proposition_14_B_2` |
| (14.B.9), p. 483 | Optimal incentive scheme; incentive constraint | `HAModel.IC`, `HAModel.HAFeasible`, `HAModel.IsHACostMin`, `HAModel.IsHAOptimal` |
| pp. 483-484 | Implementing `e_L` with the observable fixed wage | `HAModel.ha_implement_low` |
| (ii_H), (14.B.10), p. 484 | Incentive constraint for `e_H`; Kuhn-Tucker condition | `HAModel.ha_IC_two`, `HAModel.ha_kt_sufficient` (sufficiency); instance `exA_optimal` |
| Footnote 7, p. 484 | Reformulation in utility levels: convex program, Kuhn-Tucker conditions sufficient and necessary | sufficiency: `HAModel.ha_kt_sufficient`; convexity in utility levels: `HAModel.ha_mix`, `HAModel.ha_EV_mix`; necessity: `HAModel.ha_kt_necessary` (via `kt_convexlike`, `kt_sign`, `kt_le`, `HAModel.ha_kt_general`, `HAModel.ha_slater`, `HAModel.ha_raise`, `HAModel.ha_piece_integral`, `HAModel.ha_piece_adm`, `HAModel.ha_setIntegral_pos`, `HAModel.ha_ae_min`; corrections 6); instance `inst_kt_necessary` |
| Lemma 14.B.1, p. 484 | `γ > 0` and `μ > 0` | `HAModel.lemma_14_B_1` (for every scheme satisfying (ii_H) and (14.B.10) a.e.), `HAModel.lemma_14_B_1_every` (in every solution of (14.B.9) the multipliers exist and are positive), `HAModel.ha_fosd_set`; instances `exA_lemma_14_B_1`, `inst_kt_necessary` |
| Footnote 8, p. 485 | Direct argument that (i) binds | `HAModel.ha_shift`, `HAModel.shift`, `HAModel.ha_v_hits`, `HAModel.ha_dv_anti`, `HAModel.footnote_8`, `HAModel.ha_optimal_binds`; instance `inst_footnote_8` |
| p. 485 | `w(π) > ŵ` iff likelihood ratio `< 1` | `HAModel.ha_wage_vs_what` |
| p. 485 | Monotone scheme iff monotone likelihood ratio | `HAModel.ha_monotone_iff_mlrp` |
| Figure 14.B.1, p. 486 | FOSD without MLRP; non-monotone optimal scheme | `exA_fosd`, `exA_not_mlrp`, `exA_optimal`, `exA_not_monotone` |
| p. 486 | The optimal contract is not simple (e.g. linear) | verbal (illustrated by `exA_not_monotone`) |
| p. 486 | Jensen: expected wage for `e_H` exceeds `w*_{e_H}` | `HAModel.ha_EW_gt_of_IC`; instance `inst_EW_gt` |
| pp. 486-487 | Downward distortion only; welfare loss when `e_H` is optimal under observability | `HAModel.ha_no_upward_distortion`, `HAModel.ha_welfare_loss` (strict optimality), `HAModel.ha_no_loss_of_tie`, `exA_tie` (corrections 3), instance `exA_welfare_loss` |
| Footnote 9, p. 487 | Constrained Pareto optimality | `HAModel.footnote_9` |
| Proposition 14.B.3, p. 487 | The summary | `HAModel.proposition_14_B_3`, `HAModel.ha_welfare_loss`, `HAModel.ha_no_upward_distortion` |
| p. 487 | Upward distortion possible with many efforts | Exercise 14.B.4(d): `exercise_14_B_4d_obs`, `exercise_14_B_4d_unobs` |
| (14.B.11), pp. 487-488 | A second signal `y`; product densities; sufficient statistic; converse; Jensen improvement | `signal_ratio_indep`, `signal_ratio_suffstat`, `signal_foc_indep`, `signal_depends`, `signal_jensen`, `signal_same_utility`, `signal_lower_cost` |
| p. 488 | Extensions in the literature | verbal |

## Section 14.C: hidden information

| Source | Claim | Lean |
| --- | --- | --- |
| p. 489, footnotes 10-11 | The model: `π(e)`, `u = v(w - g(e, θ))`, assumptions on `g` | `HIModel`, `HIModel.Standing`; `g_θ < 0` at `e = 0` inconsistent: `hi_g_theta_inconsistent` (corrections 1); `g_eθ < 0`: `hi_cross_of_deriv`; footnotes verbal |
| p. 490, footnote 12 | `v'' < 0`; single crossing; two states; risk-neutral case | `HIModel.Standing` (`v_conc`), `HIModel.hi_hyp`; footnote 12: Exercise 14.C.2 |
| (14.C.1)-(14.C.5), p. 490 | Full-information program and first-order conditions | `HIModel.ObsFeas`, `HIModel.IsObsOpt`, `HIModel.hi_obs_foc` |
| (14.C.6)-(14.C.7), p. 491 | Equal marginal utilities, full insurance at `ū`, efficient efforts `π'(e*) = g_e(e*, θ)`, `e* > 0` | `HIModel.hi_obs_foc`, `HIModel.hi_fbH_of_foc`, `HIModel.hi_fbL_of_foc`, `HIModel.hi_isFB_of_crit` |
| Figure 14.C.1, p. 491 | Tangency; profit equals the intercept | `HIModel.hi_isoprofit_axis`; figure graphical |
| Figure 14.C.2, p. 492 | `e*_H > e*_L` | `HIModel.hi_fb_order` |
| Proposition 14.C.1, p. 492 | The full-information optimal contract (unique) | `HIModel.proposition_14_C_1`; instance `exB_proposition_14_C_1` |
| p. 492 | With the first-best contract the manager lies in state `θ_H`, lowering profit | `HIModel.hi_H_prefers_L` |
| pp. 492-493 | Possible forms of contracts | verbal |
| Proposition 14.C.2, pp. 493-494, footnotes 13-14 | The revelation principle; the example; deterministic outcomes | `proposition_14_C_2`, `proposition_14_C_2_payoff`, `revelation_example`; footnotes verbal (deterministic mechanisms, corrections 8) |
| p. 494, footnote 15 | Infinite risk aversion; limit of `-v^ρ` | `infinite_ra_insure`, `ceRho`, `footnote_15_order`, `footnote_15` (via Chapter 3's `exercise_3_C_6c`), `ceRho_ge_min`, `footnote_15_accept`, `footnote_15_reject` |
| (14.C.8), pp. 494-495 | The program with an infinitely risk-averse manager | `Screen`, `HIContract`, `Screen.Feas`, `Screen.IsOpt`, `HIModel.scr` (`c = v⁻¹(ū)`) |
| p. 495 | The first-best contract violates (iii) | `Screen.screen_fb_violates_iii` |
| Lemma 14.C.1, Figure 14.C.3, p. 495 | (ii) can be ignored | `Screen.lemma_14_C_1` |
| Lemma 14.C.2, p. 495 | (i) binds | `Screen.lemma_14_C_2`; instance `inst_lemmas_14_C` |
| Lemma 14.C.3, Figures 14.C.4-14.C.6, pp. 496-497 | `e_L ≤ e*_L`, `e_H = e*_H` | `Screen.lemma_14_C_3`, `Screen.screen_eL_le_eH`, `Screen.screen_Q_min`, `Screen.screen_opt_iff` |
| p. 497, footnote 16 | Only (iii) binds | `Screen.lemma_14_C_2`, `Screen.screen_iv_slack`; footnote 16: `exercise_14_C_1_local` |
| Lemma 14.C.4, Figures 14.C.7-14.C.8, pp. 497-499 | `e_L < e*_L` (envelope argument) | `HIModel.lemma_14_C_4`, `HIModel.hi_Q_crit` |
| p. 499, footnote 17 | Trade-off; `e_L = 0` only if `g_e(0, θ_L) > 0` | `HIModel.hi_eL_pos`, `footnote_17` |
| (14.C.9), p. 499 | First-order condition for `e_L`; signs of its terms; `e_L` falls as `λ/(1 - λ)` rises | `HIModel.hi_foc_14_C_9`, `HIModel.hi_14_C_9_terms`, `HIModel.hi_eL_falls`; instance `inst_eL_falls` |
| Proposition 14.C.3, footnotes 18-19, p. 499 | The optimal contract with hidden information; owner's loss; constrained optimality | `HIModel.proposition_14_C_3`, `Screen.screen_H_rent`, `Screen.screen_loss`, `Screen.FBval`; instance `exB_proposition_14_C_3`, `exB_opt`; footnote 18 is the definition of infinite risk aversion; footnote 19: every optimal contract has (i) binding (`Screen.lemma_14_C_2`), so no feasible contract gives the manager more than `ū` in state `θ_L` at the same profit (verbal otherwise) |
| pp. 499-500, footnote 20 | Unobservable profits; state-dependent profits `π_i(e)` with `π'_H ≥ π'_L > 0` | `HIModel` (fields `pH`, `pL`, `dp_le`); Exercise 14.C.5; footnote 20 verbal |
| (14.C.10), p. 500, footnote 21 | Monopolistic screening; `π_i(t) = θ_i(1 - μt)` | `Screen` with `c = ū`; `footnote_21_misprint`, `footnote_21_corrected`, `footnote_21_limit` (corrections 2) |
| pp. 500-501, footnote 22 | Maskin-Riley and Baron-Myerson | `maskin_riley`, `baron_myerson`; footnote 22 verbal |

## Section 14.D: hybrid models

| Source | Claim | Lean |
| --- | --- | --- |
| p. 501 | Revelation principle with truthfulness and obedience (Myerson 1982) | `hybrid_revelation` |
| p. 502 | Forcing contracts with deterministic profits | `hybrid_forcing` (finite penalty, corrections 9) |
| p. 502 | The hybrid model is the hidden-information model in wage-profit pairs | `hybrid_change_of_variables`; the state-dependent version (`π(e, θ)`, `ĝ(π, θ) = g(ê(π, θ))`) is the same program `Screen` with `g := ĝ` and `π_i = id` (definitional) |

## Appendix A: multiple effort levels

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 502-503 | Questions (a)-(c); with two efforts `e_L` and `e_H` can be induced | `HAModel.ha_implement_low`; `HAModel.aa_high_implementable` (when `v` is unbounded above), counterexample `aa_high_not_implementable` (corrections 4); instance `inst_high_implementable` |
| Figure 14.AA.1, p. 503 | `e_M` may not be implementable | `HAModel.aa_not_implementable`; numerical case Exercise 14.B.4(b) |
| (14.AA.1), p. 503 | The program; `K - 1` incentive constraints; convex in utility levels | `HAModel.IsHACostMin`, `HAModel.aa_IC_iff`; convexity in utility levels: `HAModel.ha_mix`, `HAModel.ha_EV_mix` |
| (14.AA.2)-(14.AA.3), p. 504 | The first-order approach and its condition | `foa_sufficient` (sufficiency of (14.AA.3) for the relaxed program); necessity: `HAModel.foa_necessary` (via `kt_convexlike_eq`; corrections 15); instance `inst_foa_necessary` (`exFOA`, `exWf`) |
| p. 504 | The relaxed solution need not solve the true problem | `foa_fails` |
| p. 504 | Concavity of the agent's objective; MLRP as differential condition | Exercises 14.AA.1-14.AA.2 |
| p. 504 | Upward distortion; inefficient effort and risk bearing together | `exercise_14_B_4d_obs`, `exercise_14_B_4d_unobs` (`e₁` with `v_H ≠ v_L` instead of `e₂`) |

## Appendix B: the hidden-information program

| Source | Claim | Lean |
| --- | --- | --- |
| (14.BB.1), p. 505 | Program without (ii) | `Screen.Feas3`, `Screen.lemma_14_C_1` |
| (14.BB.2)-(14.BB.5), p. 505 | Kuhn-Tucker conditions | `HIModel.appendix_B_steps` (hypotheses), `HIModel.appendix_B_multipliers` (they hold at every optimum with `γ = 1`, `φ_H = λ`, `φ_L = 0`) |
| Steps 1-5, (14.BB.6)-(14.BB.7), pp. 505-506 | `φ_H > 0`, `γ = 1`, `e_L, e_H > 0`, `φ_L = 0`; first-order conditions | `HIModel.appendix_B_steps`; instance `inst_appendix_B_steps`; also `HIModel.hi_foc_14_C_9` |
| p. 506 | Alternative: drop (iv) | `Screen.exercise_14_BB_1` |

## Exercises

| Source | Claim | Lean |
| --- | --- | --- |
| Exercise 14.B.1 | Must (i) bind with general `u(w, e)`? No | `exercise_14_B_1`, `b1c`, `b1_c_deriv`, `b1_uw_pos`, `b1_c_convex`, `b1_uH_lt` |
| Exercise 14.B.2 | First-order condition with a risk-averse owner | `HAModel.exercise_14_B_2` (sufficiency), `HAModel.exercise_14_B_2_necessary` (necessity); instance `inst_14_B_2_necessary` |
| Exercise 14.B.3(a) | Mean-variance utility of a linear scheme under normal profits | `exercise_14_B_3a` (Mathlib `gaussianReal`) |
| Exercise 14.B.3(b) | Optimal contract with observable effort | `exercise_14_B_3b`; instance `inst_14_B_3b` |
| Exercise 14.B.3(c) | Optimal linear scheme; effects of `β` and `σ²` | `exercise_14_B_3c`, `exercise_14_B_3c_beta`, `exercise_14_B_3c_sigma`; instance `inst_14_B_3c` |
| Exercise 14.B.4(a) | Observable effort | `exercise_14_B_4a` |
| Exercise 14.B.4(b) | `e₂` not implementable; threshold `g(e₂) ≤ 3/2` | `exercise_14_B_4b`, `exercise_14_B_4b_threshold` |
| Exercise 14.B.4(c) | Unobservable effort: `e₁` with wages `4`, `1` | `exercise_14_B_4c` |
| Exercise 14.B.4(d) | `g(e₁) = √8`, `x → 1`: observable `e₂`, unobservable `e₁` (higher) | `exercise_14_B_4d_obs`, `exercise_14_B_4d_unobs` (for `x ∈ [99/100, 1)`) |
| Exercise 14.B.5 | Free disposal: a nondecreasing optimal scheme exists | `exercise_14_B_5`, `effw`, `effw_mono`, `effw_idem`, `IsDisp` (finite profit levels, corrections 7) |
| Exercise 14.B.6(a) | First-order condition; dependence on `R` and `C` | `exercise_14_B_6a` |
| Exercise 14.B.6(b) | Revenue can be reduced; the optimal scheme | `exercise_14_B_6b` (the (a)-scheme is effectively independent of `R`), `exercise_14_B_6b_opt` (every revenue-proof scheme is weakly, and under strict risk aversion strictly, dominated by a scheme depending on costs only; corrections 21); instance `exercise_14_B_6b_instance` |
| Exercise 14.B.6(c) | Pay contingent on revenue only | `exercise_14_B_6c`, `mlrp_expect_mono` (`e_C` cannot be implemented) |
| Exercise 14.B.7 | Two periods: do period-2 wages depend on period-1 profits? Yes | `b7U`, `B7Feas`, `b7Cost`, `b7_local_inv`, `b7_shift`, `b7_improve` (inverse Euler condition), `exercise_14_B_7` (no memoryless contract is optimal; corrections 16); instance `exercise_14_B_7_instance` (`b7f`, `b7w`) |
| Exercise 14.B.8 | Costly investigation: the optimal contract for `e_H` | `b8F`, `b8EV`, `b8Cost`, `B8Feas`, `b8A`, `b8B`, `b8_persp` (convex in the perspective variables), `b8_lag`, `b8_upd`, `b8_foc`, `exercise_14_B_8` (corrections 17); instance `exercise_14_B_8_instance`, `exercise_14_B_8_instance_applied` (`b8fq`, `b8_exp_bound`) |
| Exercise 14.C.1 | `N` states | `exercise_14_C_1_mono`, `exercise_14_C_1_IR`, `exercise_14_C_1_rent`, `exercise_14_C_1_bound`, `exercise_14_C_1_local`; the optimum: `C1Feas`, `c1Prof`, `c1Rent`, `c1Wage`, `c1VS`, `c1Ext`, `c1_D_mono`, `c1_D_nonneg`, `c1_rent_le`, `c1_prof_le_VS`, `c1_wage_feasible`, `c1_prof_wage`, `c1_VS_ext`, `exercise_14_C_1_opt` (binding constraints, virtual-surplus maximization), `exercise_14_C_1_suff` (converse), `exercise_14_C_1_distortion` (no distortion at the top, `e_i ≤ e*_i`), `c1_VS_update`, `exercise_14_C_1_strict` (strict distortion below the top; corrections 19); instances `exercise_14_C_1_instance`, `exercise_14_C_1_strict_instance` |
| Exercise 14.C.2 | Risk-neutral manager: sellout and revelation mechanism | `exercise_14_C_2`; graph verbal |
| Exercise 14.C.3(a) | `u = v(w) - g(e, θ)`: full-information contract | `exercise_14_C_3a` (equal wages), `exercise_14_C_3a_suff`, `c3_foc_state`, `exercise_14_C_3a_necessary` (first-order conditions necessary), `exercise_14_C_3b_order`; instance `exercise_14_C_3a_necessary_instance` |
| Exercise 14.C.3(b) | Feasible with hidden `θ`? No | `exercise_14_C_3b` |
| Exercise 14.C.4 | Finitely risk-averse manager | `C4Feas`, `c4Prof`, `c4_mk`, `c4_prof_mk`, `c4_dv_lt`, `c4_spread`, `c4_part`, `exercise_14_C_4` (binding participation and (iii), `e_H = e*_H`, `e_L ≤ e*_L`, the manager bears risk), `c4_left_gt`, `exercise_14_C_4_strict` (`e_L < e*_L`; corrections 18); instance `exercise_14_C_4_instance`, `exercise_14_C_4_instance_applied` (`c4κ`, `c4a`, `c4g`, `c4wH`, `c4wL`, `c4_exp_bound`) |
| Exercise 14.C.5 | State-dependent profits; failure of `π'_H ≥ π'_L` | `HIModel` with `pH`, `pL` (all Section 14.C results), `exercise_14_C_5_reversal`, `screen_relax_opt` |
| Exercise 14.C.6 | Single employer in Exercise 13.D.1; comparison | `monopsony`, `monopsony_hyp`, `exercise_14_C_6` (Chapter 13's `exercise_13_D_1`), `exercise_14_C_6_instance` |
| Exercise 14.C.7(a) | Nondiscriminating monopolist serves both types | `c7_demand`, `c7_surplus`, `exercise_14_C_7a_theta`, `exercise_14_C_7a_lambda`, `exercise_14_C_7a_price` |
| Exercise 14.C.7(b) | Third-degree discrimination | `exercise_14_C_7b` |
| Exercise 14.C.7(c) | Two-part tariff | `exercise_14_C_7c` (concave case; when to serve both: comparison of the two profits, verbal) |
| Exercise 14.C.7(d) | Optimal nonlinear tariff; comparison | `exercise_14_C_7d`, `exercise_14_C_7d_compare` |
| Exercise 14.C.8(a) | Indifference curves and formulation | `C8Feas`, `C8Profit`, `C8Opt`; curves graphical |
| Exercise 14.C.8(b)-(c) | Tourists indifferent; business travellers buy late and are indifferent | `exercise_14_C_8_IRB`, `exercise_14_C_8b`, `exercise_14_C_8c` |
| Exercise 14.C.8(d) | The optimal scheme and its parameters | `exercise_14_C_8d_feas`, `exercise_14_C_8d_bound`, `exercise_14_C_8d` |
| Exercise 14.C.8(e) | Serving only business travellers | `exercise_14_C_8e` |
| Exercise 14.C.9(a) | Observable risk: full insurance | `exercise_14_C_9a` |
| Exercise 14.C.9(b) | Hidden risk; rationing | `c9Profit`, `exercise_14_C_9b` (sufficiency), `exercise_14_C_9b_shape`, `exercise_14_C_9b_rationed`, `exercise_14_C_9b_instance`; every optimal menu: `exercise_14_C_9b_necessary` (high risk fully insured, low risk partially, binding constraints; via `kt_convexlike`, `kt_foc_1d`, `c9_r_order`; corrections 20), instance `exercise_14_C_9b_necessary_instance` |
| Exercise 14.C.9(c) | Comparison with Exercise 13.D.2 | verbal |
| Exercise 14.AA.1 | Differential monotone likelihood ratio | `exercise_14_AA_1`, `exercise_14_AA_1_strict`, `exercise_14_AA_1_strict_false` (corrections 5), `aa_mono_iff`, `aa_neBot` |
| Exercise 14.AA.2 | Validity of the first-order approach; optimal contract | `exercise_14_AA_2_valid`, `exercise_14_AA_2_contract`; instance `inst_14_AA_2` |
| Exercise 14.BB.1 | Relaxed program | `Screen.exercise_14_BB_1` |

## Supporting material

| Source | Claim | Lean |
| --- | --- | --- |
| Section M.C (Jensen) as used on pp. 481, 486, 488 | Jensen for densities; tangent lines | `tpa_jensen`, `tpa_jensen_eq`, `tpa_jensen_two`, `tpa_jensen_two_lt`, `tpa_tangent_le`, `tpa_tangent_lt`, `tpa_tangent_ge_convex`, `tpa_tangent_gt_convex` |
| Footnote 6 | Finite profit levels | `dmeas`, `dmeas_integral`, `dmeas_integrable`, `dmeas_setIntegral`, `dmeas_ae` |
| Examples | Proved instances | `exA`, `exModel`, `exTie`, `exRN`, `exB`, `exC`, `exRev`, `Instances` module |
