# Source map

Mas-Colell, Whinston and Green, *Microeconomic Theory*, Chapter 23, "Incentives and Mechanism
Design", pp. 857-925: Sections 23.A-23.F, Appendix A (strong implementation), Appendix B
(implementation in environments with complete information), footnotes 1-62 and Exercises
23.B.1-23.BB.3, every subpart. Printed pages; Lean names are relative to `MWG.MechanismDesign`.
Every definition, proposition, corollary, example, numbered equation group, footnote, claim of
the text and exercise subpart is accounted for below. Types are primitive: agent `i` of type
`θᵢ` has a Bernoulli utility `uᵢ(·, θᵢ)`, the induced preference is `inducedPref` and MWG's
`𝓡ᵢ` is `prefSet`; MWG's `𝒫` is Chapter 21's `StrictPrefs` (imported from
`MWGSocialChoice`, as are `topProfile`, Proposition 21.E.1 used in the Gibbard-Satterthwaite
proof and the median voter results used in Exercise 23.C.5). Beliefs are measures `B i θᵢ`
on type profiles; with independent types they are the product prior (`indepBeliefs`); type
distributions with a density are `TypeDensity`. Departures and false printed claims are in
[corrections](corrections.md); they are marked "(corr. n)" below. Items marked **OPEN** are
mathematical claims of the book that are not formalised, with what is missing. "Listed only"
marks verbal, bibliographical or graphical items that contain no precise claim beyond those
formalised elsewhere. No Mathematical Appendix section belongs to this chapter.

## Section 23.A: introduction

| Source | Claim | Lean |
| --- | --- | --- |
| Section 23.A, pp. 857-858 | Overview: private information, mechanisms, outline of the chapter | Listed only (exposition) |
| Footnote 1, p. 857 | Earlier encounters with private information (Chapters 13, 14) | Listed only (cross-reference) |

## Section 23.B: the mechanism design problem

| Source | Claim | Lean |
| --- | --- | --- |
| Section 23.B, p. 858 | Agents, alternatives `X`, types `θᵢ ∈ Θᵢ`, utilities `uᵢ(x, θᵢ)`, induced preferences `≿ᵢ(θᵢ)`, the sets `𝓡ᵢ`; common prior `φ` | `inducedPref`, `prefSet`, `inducedPref_rational` (Kreps `Rational`); beliefs `B i θᵢ` in `Bayesian` |
| Footnote 2, p. 858 | Private values; interdependent values are possible | Listed only (modelling remark; interdependent values reappear in (23.F.10)) |
| Footnote 3, p. 858 | In Section 21.E a type was an ordinal preference | Listed only (cross-reference; the ordinal setting is `OrdinalSCF`, `rankU`) |
| Footnote 4, p. 858 | Deterministic, single-valued social choice functions | Listed only (modelling remark; `SocialChoiceFunction` is a function) |
| Definition 23.B.1, p. 859 | Social choice function `f : Θ₁ × ⋯ × Θ_I → X` | `SocialChoiceFunction` |
| Definition 23.B.2, p. 859 | Ex post efficiency | `ExPostEfficient`, `exPostEfficient_iff` |
| Example 23.B.1, p. 860 | `X = {x, y, z}`, one type for agent 1, two for agent 2; `f(θ̄₁, θ₂') = y`, `f(θ̄₁, θ₂'') = x` is ex post efficient but agent 2 of type `θ₂''` claims `θ₂'` | `b1Θ`, `b1U`, `b1F`, `b1Prof`, `b1Example`, `b1_strategyProof_iff`, `example_23_B_1_efficient`, `example_23_B_1` |
| Example 23.B.2, pp. 860-861, Figure 23.B.1 | Exchange economy; Walrasian equilibrium | `WmOpt`, `WmEq`, `wmCD`, `wmLeontief`, `wmU2`; demands `wm_cd_opt_iff`, `wm_leontief_opt_iff` |
| Example 23.B.2, Figure 23.B.1 | The Walrasian social choice function is well defined (unique equilibria) and consumer 2 gains by misreporting | Concrete economy (corr. 29): `example_23_B_2_truthful`, `example_23_B_2_misreport`, `example_23_B_2` |
| Example 23.B.2, p. 860 | "this social choice function is ex post efficient" | `wm_first_welfare`, `WmLNS`, `wm_cost_ge`, `wm_cd_lns`, `wm_leontief_lns`, `example_23_B_2_efficient` |
| Example 23.B.3, p. 861 | Public project, `X = {(k, t) : k ∈ {0, 1}, ∑ tᵢ ≤ -ck}`, `uᵢ = θᵢk + m̄ᵢ + tᵢ` | `ppK`, `PPAlt`, `ppU`, `pp_improve` |
| Example 23.B.3, (23.B.1)-(23.B.2), p. 861 | `k = 1` iff `∑θᵢ ≥ c` and `∑tᵢ = -ck` give ex post efficiency (sufficient; exact characterisation allows either `k` at `∑θᵢ = c`) | `example_23_B_3_efficient`, `example_23_B_3_efficient_iff` (corr. 18) |
| Example 23.B.3, p. 861 | Egalitarian contributions `tᵢ = -(c/I)k` | `ppEgal`, `ppEgal_efficient` |
| Example 23.B.3, p. 862 | With `c > ∑_{i≠1} θ̄ᵢ > c(I-1)/I`, agent 1 of type `c - ∑θ̄ᵢ + ε` claims `θ₁ = 0` | `example_23_B_3` |
| Example 23.B.4, p. 862 | Single indivisible good: ex post efficiency iff `yᵢ(θ)(θᵢ - max θⱼ) = 0` and `∑tᵢ = 0` | `goodV`, `goodV_efficient_iff`, `example_23_B_4_efficient_iff` |
| Example 23.B.4, p. 863 | Bilateral trade: three cases of the type intervals | `example_23_B_4_bilateral` |
| Example 23.B.4, (23.B.3)-(23.B.8), p. 863 | Auction with seller agent 0; winner pays his valuation; ex post efficient | `auctionSCF`, `fullPriceT`, `twoY`, `example_23_B_4_auction_efficient` |
| Example 23.B.4, pp. 863-864 | Buyer's problem `max (θ₁ - θ̂₁)θ̂₁`, solution `θ̂₁ = θ₁/2` | `fullPrice_interim`, `example_23_B_4_firstPriceType` |
| Example 23.B.4, p. 864 | Second-price variant: truth telling weakly dominant | `example_23_B_4_secondPriceType`, `secondPriceT` |
| Footnote 5, p. 863 | `I + 1` agents, the seller is agent 0 | `auctionSCF` (seller agent `0`; omitted in `twoY` since `t₀` does not affect buyers) |
| Footnote 6, p. 864 | Trade-off as for a monopolist | Listed only (analogy) |
| Footnote 7, p. 864 | Other implementable functions: Exercise 23.B.1 | Listed only (cross-reference) |
| Example 23.B.5, p. 865 | First-price auction; linear bids `bᵢ = αᵢθᵢ`; best response `min(θ₁/2, α₂)` | `fpMech2`, `linStrat`, `fp_interim`, `fp_br_ineq`, `example_23_B_5_bestResponse` |
| Example 23.B.5, (23.B.9)-(23.B.14), pp. 865-866 | `bᵢ = θᵢ/2` is a Bayesian Nash equilibrium implementing `y` with `tᵢ = -θᵢyᵢ/2` | `example_23_B_5`, `firstPriceT`, `IsBNEOn` (corr. 19) |
| Footnote 8, p. 865 | Ties go to the lowest-numbered bidder | `twoY`, `auctionWinner`, `auctionWinner_le` |
| Example 23.B.6, p. 866 | Second-price auction: `bᵢ = θᵢ` weakly dominant; implements the second-price function | `spMech`, `bidValue`, `exercise_23_B_3`, `sp_truth_dominant`, `example_23_B_6` |
| Footnote 9, p. 866 | Vickrey auction | Listed only (name and reference) |
| Footnote 10, p. 866 | Ties again to the lowest-numbered bidder | `auctionWinner`, `auctionWinner_le`, `auctionWinner_fin_two` |
| Definition 23.B.3, p. 866 | Mechanism `Γ = (S₁, …, S_I, g)` | `Mechanism`, `play` |
| Section 23.B, p. 867 | Induced Bayesian game `ũᵢ(s, θᵢ) = uᵢ(g(s), θᵢ)` | `Mechanism`, `play`, `interimUtility` |
| Footnote 11, p. 867 | Normal-form representation | Listed only (modelling remark; `Mechanism` is the normal form) |
| Footnote 12, p. 867 | Other equilibrium notions in Appendix B | Listed only (cross-reference) |
| Section 23.B, p. 867 | First- and second-price outcome functions for `I` bidders | `firstPriceOutcome`, `secondPriceOutcome`, `auctionWinner`, `auctionWinner_max`, `auctionWinner_eq_of_gt`, `au_maxSet_nonempty`, `othersMax`, `othersMax_fin_two`, `winU`, `firstPriceOutcome_fin_two` |
| Definition 23.B.4, p. 867 | `Γ` implements `f` (relative to a solution concept) | `Implements` |
| Section 23.B, p. 867 | Remark on multiple equilibria | Listed only (taken up in Appendix A: `StronglyImplements`) |
| Definition 23.B.5, p. 868 | Direct revelation mechanism | `directMechanism`, `truthful`, `play_truthful` |
| Footnote 13, p. 868 | History of the revelation principle | Listed only (references) |
| Definition 23.B.6, p. 868 | Truthful implementability | `TruthfullyImplementable`, `implements_of_truthfullyImplementable` |
| Example 23.B.7, pp. 868-869 | Direct mechanism for (23.B.9)-(23.B.14): truth is optimal | `example_23_B_7` |

## Section 23.C: dominant strategy implementation

### Dominant strategies and the revelation principle

| Source | Claim | Lean |
| --- | --- | --- |
| Footnote 14, p. 869 | Further reading | Listed only (references) |
| (23.C.1), p. 869 | Weak dominance in the Bayesian sense, against all `s₋ᵢ(·)` | `WeaklyDominantInExpectation`, `interimUtility` |
| Footnote 15, p. 869 | The expectation is over `θ₋ᵢ` | Listed only (notation; `interimUtility`) |
| (23.C.2), p. 870 | Ex post weak dominance | `WeaklyDominantExPost` |
| Footnote 16, p. 870 | (23.C.1) for all `s₋ᵢ(·)` iff (23.C.2) | `footnote_23_16_expost`, `footnote_23_16_expectation`, `footnote_23_16` |
| Definition 23.C.1, p. 870 | Dominant strategy equilibrium | `IsDominantStrategyEquilibrium` |
| Definition 23.C.2, p. 870 | Implementation in dominant strategies | `ImplementsInDominantStrategies` |
| Footnote 17, p. 870 | Several weakly dominant strategies | Listed only (taken up in Appendix A: `weaklyDominant_indifferent`) |
| Footnote 18, p. 870 | Robustness to relaxations of rationality | Listed only (verbal) |
| Section 23.C, p. 870 | Dominant strategy implementation does not depend on beliefs `φ` | By construction: `IsDominantStrategyEquilibrium`, `ImplementsInDominantStrategies`, `StrategyProof` take no beliefs |
| Definition 23.C.3, (23.C.3), p. 871 | Strategy-proofness | `StrategyProof`, `strategyProof_iff_truthfullyImplementable`, `strategyProof_implements` |
| Proposition 23.C.1, (23.C.4)-(23.C.5), p. 871 | Revelation principle for dominant strategies | `proposition_23_C_1` |
| Section 23.C, p. 872 | Weak preference reversal; lower contour sets `Lᵢ(x, θᵢ)` | `WeakPreferenceReversal`, `lowerContour`, `exercise_23_C_1` |
| Proposition 23.C.2, (23.C.6), p. 872 | Strategy-proof iff (23.C.6) | `proposition_23_C_2`, `IPM`, `ipm_iff` |
| Figures 23.C.1-23.C.2, pp. 872-873 | Preference reversal; single crossing | Listed only (graphical) |

### The Gibbard-Satterthwaite theorem

| Source | Claim | Lean |
| --- | --- | --- |
| Section 23.C, p. 873 | `𝒫`; `f(Θ)` | `StrictPrefs` (Chapter 21), `Set.range f` |
| Definition 23.C.4, p. 873 | Dictatorial | `Dictatorial` |
| Definition 23.C.5, p. 873 | Monotonic | `MonotonicSCF` |
| Figure 23.C.3, p. 873 | Monotonicity | Listed only (graphical) |
| Proposition 23.C.3 (Gibbard-Satterthwaite), p. 874 | Finitely many agents, `|X| ≥ 3`, `𝓡ᵢ = 𝒫`, onto: strategy-proof iff dictatorial | `proposition_23_C_3` (with `Nonempty ι`, corr. 1) |
| Proof, Step 1, p. 874 | Strategy-proof implies monotonic | `gs_single_change`, `gs_change_on`, `gs_step_1`, `eq_of_utility_eq`, `lt_of_le_of_ne'` |
| Proof, Step 2, pp. 874-875 | Monotonic and onto implies ex post efficient | `gs_step_2`, `topPref`, `topPref_mem`, `topPref_top`, `topPref_outside`, `topTwo`, `topTwo_mem`, `topTwo_first`, `topTwo_second`, `exists_type_of_pref` |
| Proof, Step 3, p. 875 | Monotonic and ex post efficient implies dictatorial (Proposition 21.E.1) | `gs_step_3` (uses Chapter 21's `proposition_21_E_1`) |
| Proof, p. 874 | "It is immediate" that a dictatorial `f` is strategy-proof | `strategyProof_of_dictatorial` |
| Proposition 23.C.3, non-vacuity | Rank utilities, strict-preference types, a dictatorial onto rule | `rankUtil`, `rankUtil_le_iff`, `StrictType`, `RationalType`, `rankU`, `prefSet_rankU`, `topOf`, `topOf_spec`, `topPref_singleton_top`, `exists_strict_top`, `dictatorRule`, `proposition_23_C_3_instance` |
| Footnote 19, p. 874 | Finiteness of `X` is not required | `footnote_23_19` |
| Footnote 19, p. 874 | Without finiteness `𝓡ᵢ = 𝒫` may fail (lexicographic order, Example 3.C.1) | Listed only (cross-reference to Chapter 3) |
| Footnote 19, p. 874 | Barberà-Peleg (1990): the theorem holds for arbitrary `X` with `𝓡ᵢ` the continuous preferences | **OPEN**: not formalised (a cited theorem about continuous preferences on a topological space; needs its own proof) |
| Section 23.C, p. 875 | With `|X| = 2` majority voting is strategy-proof (Exercise 23.C.2) | `exercise_23_C_2`, `exercise_23_C_2_instance` (corr. 15) |
| Section 23.C, p. 875 | ... and nondictatorial (with rich types) | `I ≥ 3`, every majority voting function: `majority_nondictatorial`; `I ≥ 2`, ties to `x₁`: `majority_tieTrue_nondictatorial`, `majority_tieTrue_strategyProof`, `remark_23_C_majority` (onto, nondictatorial, strategy-proof); `MtRich`, `mt_counts`, `mt_profile`, `majorityTieTrue` |
| Section 23.C, p. 875 | (scope) with `I = 2` a majority voting function can be dictatorial | `majority_two_agents_dictatorial`, `majorityTieZero` (corr. 30) |
| Section 23.C, p. 875 | With `𝓡ᵢ = 𝒫` an ex post efficient `f` is onto (Exercise 23.C.3) | `exercise_23_C_3` |
| Corollary 23.C.1, p. 875 | `𝒫 ⊆ 𝓡ᵢ`, `X` finite, `|X| ≥ 3`, onto: strategy-proof implies dictatorial | `corollary_23_C_1` (proof via `exercise_23_C_4`), `botOf`, `botOf_spec` |
| Corollary 23.C.1, p. 875 | Converse "again immediate" | False with indifference: `corollary_23_C_1_converse_false` (`optU`, `tieBreakRule`, `zeroBottom`, `zeroTop`); true under `𝓡ᵢ ⊆ 𝒫`: `strategyProof_of_dictatorial` (corr. 2) |
| Definition 23.C.6, p. 876 | Dictatorial on `X̂` | `DictatorialOn` |
| Corollary 23.C.2, p. 876 | `|f(Θ)| ≥ 3`, `𝒫 ⊆ 𝓡ᵢ`: strategy-proof implies dictatorial on `f(Θ)` | `corollary_23_C_2`, `extendPref`, `extendPref_mem`, `extendPref_restrict` |
| Corollary 23.C.2, p. 876 | Converse | False with indifference: `corollary_23_C_2_converse_false`; true under `𝓡ᵢ ⊆ 𝒫`: `strategyProof_of_dictatorialOn` (corr. 2) |
| Section 23.C, p. 876 | Implications of the theorem | Listed only (verbal) |

### Quasilinear environments: Groves-Clarke mechanisms

| Source | Claim | Lean |
| --- | --- | --- |
| Section 23.C, p. 876 | `x = (k, t)`, `uᵢ = vᵢ(k, θᵢ) + m̄ᵢ + tᵢ` | `qlU` |
| Section 23.C, p. 877 | `X = {(k, t) : ∑tᵢ ≤ 0}` | `QLAlt` |
| Footnote 20, p. 877 | `X` not compact: no dictatorial social choice function | `footnote_23_20` |
| Example 23.C.1, p. 877 | Public project, `vᵢ = ṽᵢ(k) - c(k)/I` | Listed only (an instance of `qlU`; no separate claim) |
| Footnote 21, p. 877 | Choice of the base contribution method is immaterial | Listed only (verbal) |
| Example 23.C.2, p. 877 | Single good: `K` = winners, `vᵢ = θᵢyᵢ` | `goodV`, `goodV_efficient_iff` |
| (23.C.7), p. 877 | Efficient project rule; necessary for ex post efficiency | `EfficientProject`, `exPostEfficient_ql_iff` |
| Proposition 23.C.4 (Groves), (23.C.8), p. 877 | Groves transfers give strategy-proofness | `grovesTransfer`, `IndepOwn`, `proposition_23_C_4` |
| Footnote 22, p. 878 | Terminology "Groves mechanism" | Listed only (terminology) |
| Section 23.C, p. 878 | Clarke (pivotal) mechanism; transfer `0` if not pivotal, else "negative" | `clarkeH`, `EfficientForOthers`, `clarke_strategyProof`, `clarke_transfer_props`; "negative" false with ties: `clarke_pivotal_zero_tax` (corr. 3) |
| Footnote 23, p. 878 | Clarke is feasible; `hᵢ ≤ -∑_{j≠i} vⱼ(k₋ᵢ*)` sufficient, not necessary | `footnote_23_23`, `footnote_23_23_not_necessary` |
| Section 23.C, p. 879 | Single good: Clarke = second-price auction | `clarke_single_good` |
| Proposition 23.C.5 (Green-Laffont), (23.C.9)-(23.C.11), p. 879 | With `𝒱` rich, every strategy-proof `f` with efficient `k*` is Groves | `proposition_23_C_5` (corr. 4: `-∞` replaced) |
| Footnote 24, p. 879 | Another route: small-type discussion, Exercise 23.C.10 | Listed only (cross-reference) |
| (23.C.12), p. 880 | Budget balance | `BudgetBalanced` |
| Proposition 23.C.6 (Green-Laffont), p. 880 | With `𝒱` rich, no strategy-proof `f` satisfies (23.C.7) and (23.C.12) | `proposition_23_C_6` (needs `I ≥ 2`, `|K| ≥ 2`: `proposition_23_C_6_false_one_project`, `proposition_23_C_6_false_one_agent`, corr. 5); `sum_sum_erase`, `sum_grovesTransfer`, `mixProfile`, `alternating_sum_indepOwn`, `mixedDifference_eq_zero` |
| Footnote 25, p. 880 | Another negative result: small-type discussion, Exercise 23.C.10 | Listed only (cross-reference) |
| Section 23.C, p. 881 | Outside agent 0 restores budget balance | `outside_agent` |
| Section 23.C, p. 881 | Caveats on the outside agent | Listed only (verbal) |

### The differentiable case (small type)

| Source | Claim | Lean |
| --- | --- | --- |
| Section 23.C, p. 881 | `K = ℝ`, `v` `C²`, `vₖₖ < 0`, `vₖθ ≠ 0`, interval types | `SmallTypeEnv`, `quadEnv`, `InBox`, `inBox_update`, `StrategyProofOnBox`, `strategyProofOnBox_iff`, `sp_slice`, `EfficientOnBox`, `EfficientProject.efficientOnBox` |
| (23.C.13), p. 881 | First-order condition of truth telling | `eq_23_C_13`, `dc_foc_slice`, `dc_deriv_nonneg_of_monotoneOn` |
| (23.C.14), p. 881 | Transfer as an integral | `eq_23_C_14`, `dc_integral_slice` |
| (23.C.15), p. 882 | First-order condition of efficiency | `eq_23_C_15`, `efficient_foc`, `dc_strict_max`, `sum_update_split`, `sum_erase_update` |
| Section 23.C, p. 882 | Implicit function theorem: `k*` is `C¹`, `∂k*/∂θᵢ ≠ 0` | `dc_implicit`, `dc_implicit_root`, `efficient_slice_implicit`, `efficient_slice_continuousOn`, `efficient_slice_hasDerivAt`, `efficient_slice_deriv_ne_zero` |
| Section 23.C, p. 882 | Hence every strategy-proof `f` with efficient `k*` is Groves | `differentiable_case_groves`, `differentiable_case_groves_iff`, `groves_strategyProofOnBox`, `dc_groves_slice` |
| Footnote 26, p. 882 | Any `C¹` `k*` | `footnote_23_26` |
| (23.C.16)-(23.C.17), p. 882 | `I = 2`: no budget balanced strategy-proof efficient rule | `differentiable_case_no_budget_balance` (via `exercise_23_C_10c_decomposition`, `dc_mixed_pos`, `dc_delta_monotone`, `dc_sign_of_ne`, `smallTypeEnv_exists_pair`, `smallTypeEnv_strict_max`, `vec2_update0`, `vec2_update1`, `vec2_inBox`; corr. 6) |
| Section 23.C, p. 882 | `I > 2`: budget balance possible (Laffont-Maskin, Exercise 23.C.10) | `exercise_23_C_10b` |
| Section 23.C, pp. 881-882 | Non-vacuity | `quadK`, `quadK_efficient`, `differentiable_case_instance` |

## Section 23.D: Bayesian implementation

| Source | Claim | Lean |
| --- | --- | --- |
| Footnote 27, p. 883 | Further reading | Listed only (references) |
| Footnote 28, p. 883 | Pure strategy equilibria | `IsBayesianNash` (pure strategies by construction) |
| Definition 23.D.1, p. 883 | Bayesian Nash equilibrium | `IsBayesianNash`, `interimUtility` |
| Definition 23.D.2, p. 883 | Implementation in Bayesian Nash equilibrium | `ImplementsInBNE` |
| Definition 23.D.3, (23.D.1), p. 883 | Bayesian incentive compatibility | `BayesianIC`, `bayesianIC_iff` |
| Proposition 23.D.1, (23.D.2)-(23.D.4), p. 884 | Revelation principle for Bayesian Nash equilibrium | `proposition_23_D_1` |
| Footnote 29, p. 884 | Used implicitly in Section 14.C | Listed only (cross-reference) |
| Section 23.D, p. 884 | Dominant strategy implementation implies Bayesian implementation | `isBayesianNash_of_dominant`, `implementsInBNE_of_dominant`, `bayesianIC_of_strategyProof`, `ms_bic_of_dsic` (integrability, corr. 13) |
| (23.D.5)-(23.D.7), p. 885 | Quasilinear with `m̄ᵢ = 0`; ex post efficiency = (23.D.6) + (23.D.7) | `qlU`, `EfficientProject`, `BudgetBalanced`, `exPostEfficient_ql_iff` |
| Footnote 30, p. 885 | Risk neutrality matters here, unlike Section 23.C | Listed only (remark; contrast `exercise_23_C_11`) |
| Section 23.D, p. 886 | Independent types | `indepBeliefs`, `splice`, `measurable_splice`, `map_splice`, `integral_integral_update`, `integral_eval_pi` |
| Footnote 31, p. 886 | Correlated types: references | Listed only (references) |
| (23.D.8), p. 886 | Expected externality transfers are Bayesian incentive compatible | `expectedExternality`, `agvTransfer`, `agv_bayesianIC` |
| (23.D.9), p. 886 | Budget-balancing `hᵢ` | `agvH`, `agvH_indepOwn`, `agv_budgetBalanced` (needs `I ≥ 2`, corr. 13) |
| Section 23.D, p. 887 | Ex post efficient `f` Bayesian implementable with independent types | `agv_exPostEfficient_bic`, `agv_finite` |
| Section 23.D, p. 887 | Intuition; individual rationality may fail | Listed only (verbal; failure is `exercise_23_E_1`) |
| Section 23.D, p. 887 | Linear utility `θᵢvᵢ(k) + tᵢ`, `v̄ᵢ`, `t̄ᵢ` | `linU`, `interimBenefit`, `interimTransfer`, `InterimIntegrable`, `BayesianICOn` |
| (23.D.10), p. 888 | `E[uᵢ | θᵢ, θ̂ᵢ] = θᵢv̄ᵢ(θ̂ᵢ) + t̄ᵢ(θ̂ᵢ)` | `eq_23_D_10` |
| Footnote 32, p. 888 | Single-crossing preferences over `(v̄, t̄)` | Listed only (remark) |
| Section 23.D, p. 888 | `Uᵢ(θᵢ) = θᵢv̄ᵢ(θᵢ) + t̄ᵢ(θᵢ)` | `interimU` |
| Proposition 23.D.2, (23.D.11)-(23.D.13), pp. 888-889 | BIC iff `v̄ᵢ` nondecreasing and the integral formula | `proposition_23_D_2`, `linearIC_iff`, `LinearIC`, `integral_eq_of_slope_bounds` |
| Proof, p. 888 | "`Uᵢ'(θᵢ) = v̄ᵢ(θᵢ)` for all `θᵢ`" | False at jumps: `proposition_23_D_2_derivative_false` (corr. 12) |
| Section 23.D, p. 889 | Expected transfer formula; `tᵢ(θ) = t̄ᵢ(θᵢ)` realises it | `expected_transfer_formula`, `interimTransfer_of_own` |
| Footnote 33, p. 889 | Budget balance may restrict the transfers | Listed only (remark) |
| Section 23.D, p. 889 | Auction setting `vᵢ(y) = yᵢ` | `allocV` |
| Footnote 34, p. 889 | The seller's value is not needed | Listed only (modelling remark) |
| Section 23.D, pp. 887-891 | Densities `φᵢ > 0` on `[θ̲ᵢ, θ̄ᵢ]`, `Φᵢ` | `TypeDensity`, `TypeDensity.measure`, `TypeDensity.cdf`, `TypeDensity.isProbabilityMeasure`, `TypeDensity.measure_compl_Icc`, `TypeDensity.measure_singleton`, `TypeDensity.measure_Ioo_pos`, `TypeDensity.integral_eq`, `TypeDensity.measureReal_Iic`, `TypeDensity.measureReal_Ici`, `TypeDensity.absolutelyContinuous`, `TypeDensity.continuous_cdf`, `uniformDensity`, `uniform01`, `uniform01_integral`, `uniform01_cdf` |
| Proposition 23.D.3 (revenue equivalence), p. 890 | Same `y` and same `Uᵢ(θ̲ᵢ)` give the same expected revenue | `proposition_23_D_3`, `re_expected_transfer`, `re_interimTransfer_eq` (no densities needed, corr. 14) |
| Footnote 35, p. 890 | Versions by many authors | Listed only (references) |
| Proof, p. 890 | "Integration by parts" `∫(∫ ȳ)φ = ∫ ȳ(1 - Φ)` | `TypeDensity.integral_integral_eq`, `td_integral_integral_eq` (Fubini form, corr. 14) |
| (23.D.14), p. 890 | Expected payment via virtual valuation | `eq_23_D_14`, `TypeDensity.virtualValue` |
| (23.D.15), p. 891 | Multiple-integral form | `eq_23_D_15` |
| (23.D.16), p. 891 | Expected revenue `∫ ∑ yᵢJᵢ ∏φ - ∑ Uᵢ(θ̲ᵢ)` | `eq_23_D_16`, `eq_23_D_16_instance` |
| Section 23.D, p. 891 | First- and second-price auctions (uniform) have equal revenue | `exercise_23_D_3_revenue_equivalence` |
| Section 23.D, p. 891 | Symmetric case (Exercise 23.D.4) | `exercise_23_D_4c` |

## Section 23.E: participation constraints

| Source | Claim | Lean |
| --- | --- | --- |
| Section 23.E, p. 891 | Introduction | Listed only (exposition) |
| Example 23.E.1, p. 892 | Public project with two types; no strategy-proof, ex post IR, feasible `f` with the efficient rule | `partVal`, `partK`, `partV`, `partF`, `PartFeasible`, `example_23_E_1_efficient`, `example_23_E_1`, `part_vec2`; each pair satisfiable: `example_23_E_1_sp_ir`, `example_23_E_1_sp_feasible`, `example_23_E_1_ir_feasible` |
| Footnote 36, p. 892 | Excluding an agent from the project is ex post inefficient | Listed only (modelling remark: exclusion is outside the alternative set of Example 23.E.1) |
| Example 23.E.1, p. 893 | An outside agent with `t₀ ≥ 0` does not help | `example_23_E_1_outside` |
| (23.E.1), p. 893 | Ex post participation constraints | `ExPostParticipation` |
| Footnote 37, p. 893 | Outside option depends on own type only | `ExPostParticipation` (outside option `ūᵢ : Θᵢ → ℝ`) |
| Footnote 38, p. 893 | No loss of generality in requiring participation | Listed only (verbal argument) |
| (23.E.2), p. 893 | Interim participation constraints | `InterimParticipation`, `scfInterimU` |
| (23.E.3), p. 893 | Ex ante participation constraints | `ExAnteParticipation`, `scfExAnteU` |
| Footnotes 39-40, pp. 893-894 | Common prior; bankruptcy and enforceability | Listed only (remarks) |
| Section 23.E, p. 894 | (23.E.1) ⇒ (23.E.2) ⇒ (23.E.3) | `interimParticipation_of_exPost`, `exAnteParticipation_of_interim`, `ms_interimIR_of_exPostIR` |
| Section 23.E, p. 894 | The reverse implications fail | `participation_interim_not_exPost`, `participation_exAnte_not_interim`, `partUnifBelief`, `partUnifBelief_isProb`, `part_integral_unif` |
| Section 23.E, p. 894 | Bilateral trade setting, interim IR `U₁ ≥ θ₁`, `U₂ ≥ 0` | `InTypes`, `ExPostEfficientTrade`, `BudgetBalancedOn`, `InterimIR`, `DominantICOn`, `ExPostIR` |
| Section 23.E, p. 894 | Expected externality mechanism fails interim IR | `exercise_23_E_1` |
| Footnote 41, p. 895 | Overlap iff `θ̄₂ > θ̲₁` and `θ̄₁ > θ̲₂` | `footnote_23_41` (nondegenerate intervals, corr. 9) |
| Proposition 23.E.1 (Myerson-Satterthwaite), p. 895 | No BIC, ex post efficient, interim IR `f` | `proposition_23_E_1`, `proposition_23_E_1_general`, `ms_core`, `msVcgT`, `ms_vcg_bic`, `ms_vcg_interimIR` (other route, corr. 10); by MWG's route `proposition_23_E_1_mwg` |
| Proposition 23.E.1, non-vacuity | Each dropped hypothesis is necessary | `exercise_23_E_1` (no IR), `proposition_23_E_1_instance_no_bb`, `proposition_23_E_1_instance_no_eff` (`postQ`, `postY`, `postT`), `proposition_23_E_1_instance_no_bic` (`splitT`) |
| Proof, Step 1, (23.E.4), p. 895 | BIC + IR with `y₁ + y₂ = 1`, `t₁ + t₂ = 0` imply `∫∫ y₂[J₂ - K₁]φ₁φ₂ ≥ 0` | `eq_23_E_4`, `eq_23_E_4_instance`, `TypeDensity.virtualCost` |
| Proof, (23.E.5), p. 895 | Buyer's expected payment | `eq_23_E_5` |
| Proof, p. 895 | `U₁(θ̲₁) = U₁(θ̄₁) - ∫∫ y₁φ₂` | `eq_23_E_5_seller_U`, `mss_interimBenefit_seller` |
| Proof, (23.E.6), p. 895 | Seller's expected payment from the top type | `eq_23_E_6`, `mss_payment_from_top` |
| Proof, p. 896 | `∫∫ (θ₁ + Φ₁/φ₁)φ₁φ₂ = θ̄₁` | `mss_integral_virtualCost`, `mss_expect_virtualCost` (Fubini, corr. 11) |
| Proof, (23.E.7), p. 896 | With `y₁ + y₂ = 1` | `eq_23_E_7` |
| Proof, p. 896 | Adding (23.E.5) and (23.E.7) with budget balance | `eq_23_E_sum` |
| Proof, Step 2, p. 896 | Efficient trade violates (23.E.4): every display | `mss_step2_inner`, `mss_step2_display1`, `mss_step2_display23`, `mss_step2_display4`, `mss_step2_display5`, `mss_step2_neg`, `mss_step2`, `mss_integral_key`, `mss_integral_cdf` (corr. 11) |
| Section 23.E, pp. 896-897 | Interpretation | Listed only (verbal) |
| Footnote 42, p. 897 | Date of delivery in Exercise 23.E.4 | `exercise_23_E_4_payoffs` (discounting as a trading probability; corr. 25) |
| Footnote 43, p. 897 | Hence in any perfect Bayesian or sequential equilibrium | Listed only (remark) |

## Section 23.F: optimal Bayesian mechanisms

| Source | Claim | Lean |
| --- | --- | --- |
| Section 23.F, p. 897 | Introduction | Listed only (exposition) |
| (23.F.1)-(23.F.2), p. 898 | `F_BIC`, `F_IR`, `F* = F_BIC ∩ F_IR` | `fBIC`, `fIRExPost`, `fIRInterim`, `fIRExAnte`, `incentiveFeasible`, `incentiveFeasible_subset` |
| Definition 23.F.1, p. 898 | Ex ante efficient in `F` | `ExAnteEfficientIn` |
| Definition 23.F.2, p. 898 | Interim efficient in `F` | `InterimEfficientIn` |
| Proposition 23.F.1, p. 899 | Ex ante efficient in `F` implies interim efficient in `F` | False with null types: `proposition_23_F_1_false`, `wcSpike`; corrected: `proposition_23_F_1`, `proposition_23_F_1_pointMass` (corr. 16) |
| Footnotes 44-46, pp. 899-900 | Interpretation of the welfare criteria | Listed only (remarks) |
| Definition 23.F.3, p. 900 | Ex post efficient in `F` | `ExPostEfficientIn` |
| Section 23.F, p. 900 | Definition 23.B.2 = Definition 23.F.3 with all social choice functions | `exPostEfficientIn_univ_iff` |
| Section 23.F, p. 900 | Myerson-Satterthwaite: no element of `F*` is ex post efficient | `proposition_23_E_1`, `proposition_23_E_1_general` |
| Section 23.F, p. 900 | Ex post / ex ante classical efficiency | Listed only (terminology) |
| Example 23.F.1, pp. 900-901 | Principal-agent with hidden information | `ocU`, `OCFeasible`, `ocPayoff` |
| Footnote 47, p. 901 | `J` nondecreasing: reference | Listed only (reference) |
| (23.F.3), p. 902 | BIC iff (i) `e(·)` nondecreasing, (ii) integral formula; (iii) ⇔ (iii') | `eq_23_F_3`, `oc_monotone_comp_iff`, `eq_23_F_iii_iff`, `oc_one_sub_cdf_nonneg`, `oc_one_sub_cdf_pos` |
| (23.F.4), p. 902 | Expected payoff via virtual valuation | `eq_23_F_4`, `oc_integrable_vJ` |
| (23.F.5), p. 902 | `U(θ̲) = ū`; relaxed problem | `eq_23_F_5`, `example_23_F_1`, `OCArgmax` |
| (23.F.6), p. 902 | First-order condition; IFT gives `e(·)` nondecreasing | `eq_23_F_6`; monotone comparative statics instead of the IFT: `oc_maximizer_mono`, `oc_maximizer_monotoneOn`, `oc_strictConcave`, `oc_argmax_unique` (corr. 17) |
| Footnote 48, p. 902 | Under the assumptions the optimal contract is interior (`e(θ) > 0` for almost all `θ`) | `footnote_23_48` (every optimal feasible contract, given `v'(0) > 0`, `g'(0) = 0` and a pointwise solution of the relaxed problem); instance `footnote_23_48_instance`, `oc_instance_argmax` |
| Example 23.F.1, p. 903 | `e(θ) ≤ e*(θ)`, `=` at `θ̄`, `<` below | `example_23_F_1_le_firstBest`, `example_23_F_1_eq_firstBest_hi`, `example_23_F_1_lt_firstBest`, `oc_virtualValue_facts`, `oc_not_argmax_zero` |
| Example 23.F.1, non-vacuity | Uniform types on `[-2, -1]`, `g = e²`, `v = 2e - e²` | `example_23_F_1_instance`, `oc_integrable_of_bound` |
| Footnote 49, p. 903 | Perturbation argument is heuristic | Listed only (heuristic) |
| Example 23.F.2, pp. 903-904 | Optimal auction setting; feasible allocations | `FeasAlloc`, `PointwiseOptAlloc`, `auctionRevenue`, `OptAuctionFeasible` |
| Footnote 50, p. 903 | `J` not monotone: Myerson (1981) | Listed only (reference) |
| Footnote 51, p. 904 | No waste without loss of generality | `FeasAlloc` (seller keeps `1 - ∑yᵢ`), `auctionRevenue` |
| (23.F.7)-(23.F.8), p. 904 | Reduced problem; (iv) ⇔ (iv'); `Uᵢ(θ̲ᵢ) = 0` | `example_23_F_2`, `eq_23_F_iv_iff`, `oa_sum_split` |
| (23.F.9), p. 905 | Pointwise rule `Jᵢ > max{0, maxₖ Jₖ}` | `eq_23_F_9`, `eq_23_F_9_converse` (ties free, corr. 17) |
| Example 23.F.2, p. 905 | `J` nondecreasing ⇒ the pointwise rule has `yᵢ`, `ȳᵢ` nondecreasing, so with `tᵢ = Uᵢ - θᵢȳᵢ` it solves the full problem | `example_23_F_2_general` (general densities), rule `oaRule`, `oaWins`, `oa_wins_unique`, `oa_exists_wins`, `oaRule_pointwiseOpt`, `oaRule_mono`, `oaRule_measurable`, `oa_measurable_virtualValue`, `oa_integrable_virtualValue`; instance `example_23_F_2_general_instance`; earlier instances `example_23_F_2_instance`, `example_23_F_2_remark2` with `exercise_23_D_3` (corr. 17(b)) |
| Proposition 23.D.2, p. 888, sufficiency, as used on p. 905 | A measurable bounded allocation rule nondecreasing in own type, completed by the envelope transfers, is Bayesian incentive compatible with `Uᵢ(θᵢ) = cᵢ + ∫ ȳᵢ` | `ec_mechanism`, `ecTransfer`, `ec_integrable_update`, `ec_interimBenefit_abs_le`, `ec_interimBenefit_mono` |
| Example 23.F.2, p. 905 | "`Jᵢ(θᵢ) = Max{0, Maxₖ≠ᵢ Jₖ(θₖ)}` is a zero probability event" | Not used: the rule breaks ties by a fixed order of bidders, which keeps `yᵢ` monotone whatever the tie probability (corr. 17(b)) |
| Remark (1), p. 905 | Asymmetric bidders: not ex post efficient | `example_23_F_2_remark1`, `oa_uniform_cdf`, `oa_uniform_virtualValue` |
| Remark (2), p. 905 | Symmetric, `J(θ̲) > 0`: first- and second-price auctions optimal | `example_23_F_2_remark2_pointwise`, `example_23_F_2_remark2` |
| Remark (3), p. 905 | `I = 1`: posted price with `J(p*) = 0`; FOC `1 - Φ - pφ = 0` | `example_23_F_2_remark3_pointwise`, `example_23_F_2_remark3_foc`, `example_23_F_2_remark3_foc_iff`, `example_23_F_2_instance`, `oaPostY`, `oaPostT`, `oa_uniform01_virtualValue` |
| (23.F.10), p. 905 | Interdependent values: BIC with `uᵢ(x, θ)` | Not formalised as a general definition (`BayesianIC` has private values). Its only use, Example 23.F.3, has one informed agent, and there (23.F.10) is (23.F.15)-(23.F.16): `BasSCF.ICH`, `BasSCF.ICL` |
| Example 23.F.3, (23.F.11)-(23.F.14), p. 906 | Seller with two qualities; IR constraints | `BasSCF`, `BasSCF.U1L`, `BasSCF.U1H`, `BasSCF.U2`, `BasSCF.U1`, `BasSCF.Prob`, `BasSCF.IR1L`, `BasSCF.IR1H`, `BasSCF.IR2` |
| Footnote 52, p. 906 | No waste of good or numeraire | `BasSCF` (trade probability and one transfer per type) |
| Example 23.F.3, p. 906 | Ex post efficiency means `y_L = y_H = 1` (Exercise 23.F.8) | `exercise_23_F_8`, `BasPairEfficient`, `BasExPostEfficient`, `basPairEfficient_iff` |
| (23.F.15)-(23.F.16), p. 907 | Incentive constraints; `F*` | `BasSCF.ICH`, `BasSCF.ICL`, `basFStar` |
| Example 23.F.3, p. 907 | Properties (i)-(iii) (Exercise 23.F.9) | `exercise_23_F_9a`, `exercise_23_F_9b`, `exercise_23_F_9c` |
| (23.F.17), p. 907 | Interim efficiency problem | `basC17`, `BasSolves17`, `basC17_iff`, `basFStar_of_C17` |
| Footnote 53, p. 907 | All expressed as gains from trade | `basC17_iff` |
| Steps 1-4, pp. 907-908 | `y_L = 1`; `y_H < 1`; (ii) binds; (i) redundant | `bas_step1`, `bas_step2`, `bas_step3`, `bas_step4`, `bas_solves17_i_redundant` |
| (23.F.18)-(23.F.19), Figure 23.F.1, p. 908 | Reduced problems and solution | `basC19`, `BasSolves19`, `bas_solves19_iff`, `bas_solves17_iff`, `bas_key` |
| Figure 23.F.2, p. 909 | Interim incentive efficient set; `y_H ≤ 4/7` | `basShaded`, `bas_shaded_iff`, `bas_shaded_yH_le`, `bas_interimIE_iff`, `bas_interimIE_yH_le`, `bas_interimIE_iff_solves17`, `basInterimDominates`, `BasInterimEfficientIn` |
| Figure 23.F.3, pp. 909-910 | Ex ante incentive efficient set `t_H = 40y_H`; ex ante utilities | `bas_exAnte_utilities`, `bas_key_exAnte`, `bas_exAnteIE_iff`, `bas_interimIE_of_exAnteIE`, `basExAnteDominates`, `BasExAnteEfficientIn`, `bas_nonvacuous` |
| Example 23.F.3, p. 910 | High-quality seller's IR binds | `bas_exAnteIE_IR1H_binds` |
| Footnote 54, p. 910 | `y_H ≤ 4/7 < 1`; contrast with Section 13.B | `footnote_23_54` (the comparison with 13.B is verbal) |

## Appendix A: implementation and multiple equilibria

| Source | Claim | Lean |
| --- | --- | --- |
| Definition 23.AA.1, p. 910 | Strong implementation | `EveryEquilibriumYields` (as printed), `StronglyImplements`, `definition_23_AA_1_literal_counterexample` (corr. 20) |
| Footnotes 55-56, pp. 910-911 | Motivation; terminology | Listed only (remarks) |
| Appendix A, p. 911 | Strictly dominant strategies give strong implementation | `strong_of_strictlyDominant`, `strong_of_strictlyDominant_instance`, `StrictlyDominantAction`, `weaklyDominantAction_of_dse`, `WeaklyDominantAction` |
| Appendix A, p. 911 | "Always the case" without indifference | False: `noIndifference_not_strictlyDominant`; true: `dse_outcome_eq`, `strong_of_noIndifference` (corr. 21) |
| Appendix A, p. 911 | Two weakly dominant strategies are payoff equivalent | `weaklyDominant_indifferent` |
| Example 23.AA.1, pp. 911-912 | Expected externality public project: truth is a BNE | `bern`, `bern_isProb`, `integral_bern`, `typeVal`, `aaV`, `aaK`, `aaK_efficient`, `update_fin_two`, `aaP`, `integral_aaP`, `other`, `xi_aa`, `aaMech`, `aa_gain`, `example_23_AA_1_truth` |
| Example 23.AA.1, p. 912 | "Always announce `θ_H`" is a second BNE | False: `example_23_AA_1_alwaysHigh_not_BNE`; truth is the unique pure BNE: `example_23_AA_1_unique` (corr. 22) |
| Appendix A, p. 912 | Strong implementation cannot restrict to direct mechanisms | `exercise_23_AA_1`, `exercise_23_AA_1_direct_not_strong` |
| Appendix A, p. 912 | Strongly implementable only if implementable; necessary conditions stay necessary | `StronglyImplements.implements`, `stronglyImplements_strategyProof` |
| Appendix A, p. 912 | Social choice correspondences | `StronglyImplementsSCC`, `stronglyImplementsSCC_singleton` |

## Appendix B: implementation with complete information

| Source | Claim | Lean |
| --- | --- | --- |
| Appendix B, pp. 912-913 | Agents observe `θ`; Nash equilibrium of the induced game | `IsNashAt` |
| Footnote 57, p. 913 | Natural in contracting | Listed only (remark) |
| Footnote 58, p. 913 | Complete information as perfectly correlated signals | Listed only (modelling remark; complete information is modelled directly by `IsNashAt`) |
| Appendix B, p. 913 | Dominant strategy implementation unaffected | `dominant_implementsInNash` |
| Footnote 59, p. 913 | Same for strong implementation in dominant strategies | By construction (`StronglyImplements` with dominant strategy equilibria takes no beliefs) |
| Definition 23.BB.1, p. 913 | Implementation and strong implementation in Nash equilibrium | `ImplementsInNash`, `implementsInNash_iff`, `StronglyImplementsInNash`, `EveryNashYields`, `stronglyImplementsInNash_iff`, `stronglyImplementsInNash_iff_full`, `definition_23_BB_1_literal_counterexample` (corr. 23) |
| Appendix B, pp. 913-914 | `I ≥ 3`: every `f` is Nash implementable (agreement mechanism) | `agreementMech`, `agreementMech_outcome`, `nash_exists_third`, `nash_allBut_iff_card`, `nash_agreement_isNash`, `nash_any_implementable` |
| Appendix B, p. 914 | Every `x ∈ f(Θ)` is an equilibrium outcome at every `θ` | `nash_agreement_every_value` |
| Proposition 23.BB.1 (Maskin), p. 914 | Strong Nash implementation implies monotonicity | `proposition_23_BB_1` |
| Footnotes 60-61, p. 914 | Definition 23.C.5; lower contour sets | `MonotonicSCF`, `lowerContour` |
| Proposition 23.BB.2, p. 914 | `𝓡ᵢ = 𝒫`, `|X| ≥ 3`, onto: strongly Nash implementable iff dictatorial | `proposition_23_BB_2`, `proposition_23_BB_2_necessity`, `dictatorMech`, `dictatorMech_strongly`, `proposition_23_BB_2_instance` (no finiteness, corr. 23) |
| Appendix B, p. 915 | No veto power | `NoVetoPower`, `noVetoPower_iff_card` |
| Proposition 23.BB.3 (Maskin), p. 915 | `I ≥ 3`, monotonic, no veto power ⇒ strongly Nash implementable (proof omitted in MWG) | `proposition_23_BB_3`, `maskinMech`, `MaskinMsg`, `maskinOutcome`, `maskin_rule1`, `maskin_rule2`, `maskin_rule3`, `maskin_win`, `nvpU`, `proposition_23_BB_3_instance` |
| Appendix B, p. 915 | No veto power trivial with a transferable private good; monotonicity then necessary and sufficient | `noVetoPower_of_noCommonTop`, `nashQLU`, `nash_ql_no_best`, `noVetoPower_ql`, `noVetoPowerSCC_ql`, `nash_ql_strong_iff_monotonic` |
| Appendix B, p. 915 | Correspondences: monotonicity, full implementation, results carry over | `MonotonicSCC`, `NoVetoPowerSCC`, `StronglyImplementsSCCInNash`, `FullyImplementsInNash`, `FullyImplementsInNash.stronglyImplementsSCC`, `proposition_23_BB_1_correspondence`, `maskin_fullyImplements`, `monotonicSCC_singleton`, `noVetoPowerSCC_singleton` |
| Appendix B, p. 915 | The Pareto correspondence is monotonic | False in general: `paretoSet_not_monotonic`, `nashParetoCxU`; true for the weak Pareto set and with a transferable good: `weakParetoSet_monotonic`, `paretoSet_ql_monotonic`, `nash_ql_pareto_fullyImplements`, `ParetoSet`, `WeakParetoSet` (corr. 24) |
| Example 23.BB.1 (Moore-Repullo), pp. 915-916, Figure 23.BB.1 | Cobb-Douglas/Leontief economy; `f` not monotonic, so not strongly Nash implementable | `MRBox`, `mrXC`, `mrXL`, `mrY`, `mrZ`, `mrU`, `mrF`, `mrXL_ne_mrXC`, `example_23_BB_1_figure`, `example_23_BB_1_lowerContour`, `example_23_BB_1_not_monotonic`, `example_23_BB_1_not_strongly` (the figure made concrete, corr. 28) |
| Example 23.BB.1, p. 916 | Three-stage mechanism: unique SPE yields `f(θ)` | `mrStage3`, `mrStage2`, `mrOutcome`, `IsMRSubgamePerfect`, `example_23_BB_1` |
| Appendix B, p. 916 | Other refinements (Palfrey-Srivastava) | Listed only (references) |
| Footnote 62, p. 916 | Iterated dominance results | Listed only (references) |

## Exercises

### Section 23.B

| Source | Claim | Lean |
| --- | --- | --- |
| Exercise 23.B.1(a), p. 918 | `y, y`: truthful | `exercise_23_B_1a` |
| Exercise 23.B.1(b) | `z, x`: truthful | `exercise_23_B_1b` |
| Exercise 23.B.1(c) | `z, y`: truthful | `exercise_23_B_1c` |
| Exercise 23.B.1(d) | `z, z`: truthful | `exercise_23_B_1d` |
| Exercise 23.B.1(e) | `y, z`: not truthful | `exercise_23_B_1e` |
| Exercise 23.B.2, p. 918 | Split-the-difference: the buyer announces `2θ₂/3`; interpretation | `exercise_23_B_2` (the interpretation is in its docstring) |
| Exercise 23.B.3, p. 918 | Bidding one's valuation is weakly dominant in the second-price auction | `exercise_23_B_3`, `sp_truth_dominant` |
| Exercise 23.B.4(a), p. 918 | Double auction: linear BNE, implemented SCF, not ex post efficient | `daMech`, `daStrat`, `da_seller_interim`, `da_buyer_interim`, `da_seller_ineq`, `da_buyer_ineq`, `exercise_23_B_4a`, `exercise_23_B_4a_outcome`, `daQL`, `daQL_utility`, `exercise_23_B_4a_not_efficient` (corr. 19) |
| Exercise 23.B.4(b), p. 918 | That SCF is BIC | `exercise_23_B_4b` |

### Section 23.C

| Source | Claim | Lean |
| --- | --- | --- |
| Exercise 23.C.1, p. 918 | Preference reversal implies strategy-proofness | `exercise_23_C_1` |
| Exercise 23.C.2, p. 918 | Majority voting with two alternatives is strategy-proof | `exercise_23_C_2`, `exercise_23_C_2_instance`, `IsMajorityVoting`, `OrdinalSCF`, `numPref`, `numPref_update`, `inducedPref_bool_eq`; cardinal tie-breaking: `exercise_23_C_2_cardinal` (corr. 15) |
| Exercise 23.C.3, p. 919 | `𝓡ᵢ = 𝒫`: ex post efficient implies onto | `exercise_23_C_3` |
| Exercise 23.C.4, p. 919 | Restriction preserves strategy-proofness | `exercise_23_C_4` |
| Exercise 23.C.5, p. 919 | Condorcet winner rule is strategy-proof (single peaked, odd `I`) | `exercise_23_C_5`, `exercise_23_C_5_instance`, `typeProfile`, `strict_inducedPref_iff`, `singlePeaked_fin3` (Chapter 21's `proposition_21_D_1`, `median_exists`) |
| Exercise 23.C.6(a), p. 919 | IPM does not imply monotonicity | `exercise_23_C_6a` |
| Exercise 23.C.6(b) | Monotonicity does not imply IPM | `exercise_23_C_6b`, `c6U`, `c6F` |
| Exercise 23.C.6(c) | IPM and `𝓡ᵢ ⊆ 𝒫` imply monotonicity | `exercise_23_C_6c`, `exercise_23_C_6_instance` |
| Exercise 23.C.6(d) | Monotonicity and `𝓡ᵢ = 𝒫` imply IPM | `exercise_23_C_6d`, `exercise_23_C_6_instance` |
| Exercise 23.C.7, p. 919 | Maximiser of a nonnegatively responsive SWF is strategy-proof | `NonnegResponsive`, `exercise_23_C_7`, `exercise_23_C_7_instance` (corr. 15) |
| Exercise 23.C.8(a), p. 920 | `f` ex post efficient | `exercise_23_C_8a`, `c8U`, `c8F` |
| Exercise 23.C.8(b) | `f` satisfies (23.C.6) | `exercise_23_C_8b` |
| Exercise 23.C.8(c) | Truth not the unique weakly dominant strategy; the untruthful one fails to implement | `exercise_23_C_8c`, `c8Untruthful` |
| Exercise 23.C.9, p. 920 | `C¹` `f` strategy-proof iff `k` nondecreasing and the integral formula | `exercise_23_C_9`, `dc_sp_slice_iff` (corr. 6) |
| Exercise 23.C.10(a), p. 920 | Efficient, budget balanced strategy-proof `f` exists iff `V* = ∑ᵢ Vᵢ(θ₋ᵢ)` | `exercise_23_C_10a_if`, `exercise_23_C_10a_only_if`, `exercise_23_C_10a_only_if_false_one_agent` (corr. 5) |
| Exercise 23.C.10(b) | `I = 3`, `vᵢ = θᵢk - k²/2`: such an `f` exists (also `I > 2`) | `exercise_23_C_10b`, `quadV` |
| Exercise 23.C.10(c) | `∂ᴵV*/∂θ₁⋯∂θ_I = 0` necessary (and sufficient) | `exercise_23_C_10c`, `exercise_23_C_10c_sufficient`, `exercise_23_C_10c_decomposition`, `mixedDifference_eq_zero` (corr. 6) |
| Exercise 23.C.10(d) | Small type, `I = 2`: impossible | `exercise_23_C_10d` |
| Exercise 23.C.11, p. 920 | Proposition 23.C.4 with `uᵢ(vᵢ + m̄ᵢ + tᵢ)` | `exercise_23_C_11` |

### Section 23.D

| Source | Claim | Lean |
| --- | --- | --- |
| Exercise 23.D.1(a), p. 920 | The set of alternatives | `BargainX`, `bargSellerU`, `bargBuyerU` |
| Exercise 23.D.1(b), p. 921 | Earliest trade time when `θₛ = 9` | `exercise_23_D_1b`, `bargOutcome`, `bargSellerVal` |
| Exercise 23.D.2(a), p. 921 | Expected externality transfers for uniform bilateral trade | `exercise_23_D_2a`, `exercise_23_D_2a_xi`, `bilatV`, `bilatK`, `bilatK_efficient`, `bilat_xi_integrand` |
| Exercise 23.D.2(b) | Truth telling is a BNE | `exercise_23_D_2b` |
| Exercise 23.D.3, p. 921 | Revenue equivalence for Examples 23.B.5-23.B.6 | `exercise_23_D_3`, `exercise_23_D_3_revenue_equivalence`, `re_twoY_bic`, `firstPriceT_interim`, `secondPriceT_interim`, `unif2` |
| Exercise 23.D.4(a), p. 921 | Equilibrium bids nondecreasing | `exercise_23_D_4a` (types with positive winning probability, corr. 25), `exercise_23_D_4_instance` |
| Exercise 23.D.4(b) | No flat interval; strictly increasing | `exercise_23_D_4b`, `exercise_23_D_4b_strictMono` |
| Exercise 23.D.4(c) | Same revenue as the second-price auction | `exercise_23_D_4c` |
| Exercise 23.D.5, p. 921 | All-pay auction: same revenue | `exercise_23_D_5_monotone`, `exercise_23_D_5` |
| Exercise 23.D.6, p. 921 | Queue: expected wait of the first in line; doubling `β`, doubling `I` | `exercise_23_D_6_bne`, `queueExpectedWait`, `queue_bernoulli`, `exercise_23_D_6` (corr. 25) |

### Section 23.E

| Source | Claim | Lean |
| --- | --- | --- |
| Exercise 23.E.1, p. 921 | Expected externality mechanism: some type prefers not to participate | `exercise_23_E_1`, `agvBT`, `agvBT_facts`, `agvBT_interim` |
| Exercise 23.E.2(a), p. 921 | No DSIC, interim IR `f` (with ex post efficiency) | `exercise_23_E_2a`; as printed false: `exercise_23_E_2_literal_false`, `noTradeY` (corr. 7) |
| Exercise 23.E.2(b), p. 922 | No BIC, ex post IR `f` (with ex post efficiency) | `exercise_23_E_2b`, `exercise_23_E_2_literal_false` (corr. 7) |
| Exercise 23.E.3, p. 922 | Discrete types: BIC, ex post efficient, IR `f` exists | `exercise_23_E_3`, `discVal`, `discU`, `discF` (the "conclude" is verbal) |
| Exercise 23.E.4, p. 922 | Discounting: efficiency requires immediate trade; no voluntary process is efficient | `exercise_23_E_4_efficient`, `exercise_23_E_4_payoffs`, `exercise_23_E_4`, `discY`, `discSurplus` (corr. 25) |
| Exercise 23.E.5(a), p. 922 | Continuum of traders: efficient trading rule | `exercise_23_E_5a`, `MarketClears` |
| Exercise 23.E.5(a)-(b) | Existence of a market-clearing price | `exercise_23_E_5_clearing` (masses `m_S, m_B ≥ 0`, intermediate value theorem), `exercise_23_E_5_competitive`; `cp_measureReal_Iic`, `cp_measureReal_Iio`, `cp_measureReal_Ioi`, `cp_smul_real`, `cp_cdf_lo_hi` |
| Exercise 23.E.5(b) | Competitive mechanism: BIC, IR, budget balance | `exercise_23_E_5b`, `compSellerU`, `compBuyerU` |
| Exercise 23.E.5(b) | "Conclude" (large markets, Gresik-Satterthwaite) | Listed only (verbal) |
| Exercise 23.E.6(a), p. 922 | Partnership: efficient trading rule | `exercise_23_E_6a` |
| Exercise 23.E.6(b) | Symmetric linear BNE `2θ/3` | `exercise_23_E_6b`, `partnerEU`, `partnerEU_eq`, `trade_ii_le`; uniqueness among strictly increasing linear strategies: `exercise_23_E_6b_unique`, `partnerEULin`, `partnerEULin_two_thirds`, `partnerEULin_eq`, `partner_foc` (corr. 25) |
| Exercise 23.E.6(c) | Implemented SCF: BIC, ex post efficient, IR; intuition | `exercise_23_E_6c`, `partnerSCF`, `partnerEU_eq_equilibrium` (intuition in the docstring) |
| Exercise 23.E.7(a), pp. 922-923 | BIC, interim IR, efficient trade: sum of utilities `≥ 5/6` | `exercise_23_E_7a` (efficient trading rule only, corr. 8), `ms_unif_hyps`, `ms_unif_mean`, `ms_unif_gains` |
| Exercise 23.E.7(b), p. 923 | No `f` gives a sum above `2/3` | `exercise_23_E_7b`, `exercise_23_E_7b_surplus`, `exercise_23_E_7` |

### Section 23.F

| Source | Claim | Lean |
| --- | --- | --- |
| Exercise 23.F.1, p. 923 | Ex post classically efficient in `F_IR` ⇒ ex ante and interim incentive efficient | `exercise_23_F_1_exAnte`, `exercise_23_F_1_interim`, `wc_sum_le_of_exPostEfficientIn`, `wc_exAnteU_eq`, `UpClosed`, `exPostParticipation_upClosed`, `interimParticipation_upClosed` (finite types; interim needs positive probabilities, corr. 16) |
| Exercise 23.F.1, p. 923 | The ex ante part for arbitrary measurable type spaces | `exercise_23_F_1_exAnte_general` (comparison with the incentive feasible SCFs whose utilities are measurable and integrable, `WcRegular`), `wc_exAnteU_eq_general`; continuum instance `exercise_23_F_1_exAnte_general_instance` (corr. 16) |
| Exercise 23.F.1, p. 923 | In Example 23.F.1 some ex post classically efficient SCF is incentive feasible, and the derived interim incentive efficient SCF is not ex post efficient | `exercise_23_F_1_firstBest` (first best with the agent as residual claimant is ex post efficient, BIC and IR, general `v`, `g`), `exercise_23_F_1_example` (uniform instance: `OCFeasible`, and the optimal contract is not ex post efficient at `θ = -2`); also `example_23_F_1_lt_firstBest` |
| Exercise 23.F.2, p. 923 | Maskin-Riley: optimal selling mechanism | `exercise_23_F_2`, `exercise_23_F_2_foc`, `exercise_23_F_2_exclusion`, `oc_maximizer_monotoneOn` |
| Exercise 23.F.3, p. 923 | Second-price auction with reserve `J(r) = 0` optimal (symmetric, `θ̲ = 0`) | `exercise_23_F_3` |
| Exercise 23.F.3 | Nonsymmetric case | The optimal rule is (23.F.9): `eq_23_F_9`, `eq_23_F_9_converse`; the description as a "modified second-price auction" is listed only (verbal) |
| Exercise 23.F.4, p. 923 | Optimal `y` with seller valuation `θ₀` | `exercise_23_F_4`, `exercise_23_F_4_rule` |
| Exercise 23.F.5(a), p. 923 | Divisible unit, two buyers: optimal prices | `exercise_23_F_5a`, `exercise_23_F_5a_foc` |
| Exercise 23.F.5(b) | Relation to Example 23.F.2 | `exercise_23_F_5b` |
| Exercise 23.F.6(a), pp. 923-924 | Proposition 23.D.2 adapted to regulation | `exercise_23_F_6a`, `exercise_23_F_6a_price`, `exercise_23_F_6a_ir`, `bmProfit` |
| Exercise 23.F.6(b), p. 924 | Optimal scheme for `α < 1` | `exercise_23_F_6b_objective`, `exercise_23_F_6b`, `exercise_23_F_6b_price`, `bmWelfare`, `bmVirtual`, `BMFeasible`, `bmFeasible_instance`; printed objective unbounded: `exercise_23_F_6b_printed_unbounded` (corr. 26) |
| Exercise 23.F.6(b) | What if `α ≥ 1`? | `exercise_23_F_6b_alpha_ge_one` |
| Exercise 23.F.7, p. 924 | Dana-Spier: Cournot outcomes; virtual welfare; monotonicity | `exercise_23_F_7_monopoly`, `exercise_23_F_7_duopoly`, `dsProduces`, `dsGross`, `dsSurplus`, `dsVirtualCost`, `dsVirtualWelfare`, `dsVirtualCost_strictMono`, `exercise_23_F_7` |
| Exercise 23.F.7 | Reduction of expected welfare to virtual welfare; optimality; instance | `exercise_23_F_7_reduction`, `exercise_23_F_7_optimal`, `exercise_23_F_7_instance`, `dsX`, `dsAlloc`, `dsTau`, `dsProfit`, `dsWelfare`, `ds_linU`, `DSFeasible`, `ds_virtualWelfare_eq`, `ds_gross_eq`, `dsUnif`, `ds_unif_virtualCost` (corr. 27) |
| Exercise 23.F.7 | The pointwise rule can be completed by transfers into a feasible mechanism for every `(c, λ > 1, φ)` with `Φ/φ` nondecreasing | `exercise_23_F_7_general` (rule `dsRule`, transfers `dsRuleT`, `Uⱼ(θ̄ⱼ) = 0`, optimal), `dsVW`, `dsRule_max`, `dsRule_measurable`, `dsRule_mono`, `ds_vw_shift`, `ds_measurable_virtualCost`; instance `exercise_23_F_7_general_instance` (corr. 27) |
| Exercise 23.F.8, p. 924 | Ex post classically efficient ⇒ `y_L = y_H = 1` | `exercise_23_F_8` |
| Exercise 23.F.9(a), p. 924 | No feasible SCF is ex post efficient | `exercise_23_F_9a` |
| Exercise 23.F.9(b) | `y_H ≤ y_L`, `t_H ≤ t_L` | `exercise_23_F_9b` |
| Exercise 23.F.9(c) | `t_L - 20y_L ≥ t_H - 40y_H` | `exercise_23_F_9c` |
| Exercise 23.F.10, p. 924 | Interim and ex ante incentive efficient sets without the seller's IR | `basFBuyerIR`, `exercise_23_F_10_interim`, `exercise_23_F_10_exAnte`, `exercise_23_F_10_compare` |

### Appendices A and B

| Source | Claim | Lean |
| --- | --- | --- |
| Exercise 23.AA.1, p. 924 | Non-direct mechanism implementing Exercise 23.C.8's `f` with unique dominant strategies | `exercise_23_AA_1`, `aa1G`, `aa1Mech`, `aa1S`, `exercise_23_AA_1_direct_not_strong` |
| Exercise 23.AA.2, pp. 924-925, first question | Groves: dominant strategies not unique | `exercise_23_AA_2a`, `grovesMech`, `valU`, `groves_payoff`, `gr_sum_update`, `effChoice`, `effChoice_spec`, `exercise_23_AA_2_instance` |
| Exercise 23.AA.2, second question | Normalized Groves: unique (`I ≥ 2`) | `exercise_23_AA_2b`, `NormVal`, `normGrovesMech`, `normalize`, `norm_update_coe`, `eff_eq_of_strict_max` |
| Exercise 23.BB.1(a), p. 925 | Normal form and Nash equilibria | `exercise_23_BB_1a`, `exercise_23_BB_1a_not_strongly`, `IsMRNash`, `mrOutcome` |
| Exercise 23.BB.1(b) | Subgame perfect equilibria | `exercise_23_BB_1b`, `exercise_23_BB_1_spe_nash` |
| Exercise 23.BB.2, p. 925, first question | DS implementable ⇒ Nash implementable | `dominant_implementsInNash` |
| Exercise 23.BB.2, second question | Not necessarily strongly | `exercise_23_BB_2b_not_strongly`, `exercise_23_BB_2b_strategyProof`, `exercise_23_BB_2b_implementable`, `exercise_23_BB_2b_not_monotonic` |
| Exercise 23.BB.3, p. 925 | Which Groves properties must a Nash implementable SCF with efficient `k` satisfy | Weak: neither (`exercise_23_BB_3_weak`, `exercise_23_BB_3_weak_not_I`, `exercise_23_BB_3_weak_not_II`); strong: (i) must hold, (ii) never (`exercise_23_BB_3_constant`, `exercise_23_BB_3_strong_I`, `exercise_23_BB_3_strong_not_II`, `exercise_23_BB_3_strong_exists`); `bbV`, `bbU`, `GrovesPropertyI`, `GrovesPropertyII`, `bbK`, `bbV_sum`, `bbK_efficient`, `bb_eff_true`, `bb_eff_false`, `bb_sum_update`, `bb_erase_update`, `bb_sum_erase_single`, `bbF0`, `bbF1`, `bb_lower_up`, `bb_lower_down` (corr. 23) |

## OPEN items

1. Footnote 19 (p. 874): the Barberà-Peleg version of the Gibbard-Satterthwaite theorem for
   continuous preferences on an arbitrary (topological) set of alternatives. It is a cited
   research theorem; its proof (Barberà and Peleg 1990) needs a theory of continuous utility
   representations on a metric space and a separate combinatorial argument not given in MWG,
   so it is not reachable from the book's statement.
