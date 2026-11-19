# Source map

Mas-Colell, Whinston and Green, *Microeconomic Theory*, Chapter 6, "Choice Under Uncertainty",
pp. 167-216 (text pp. 167-206, exercises pp. 208-215). The chapter has no appendix and no
Mathematical Appendix section is assigned to it. Printed pages; Lean names relative to
`MWG.ChoiceUnderUncertainty`. Every definition, numbered result, precise claim of the text,
footnote with mathematical content and exercise subpart is listed. Statements were checked
against the page images. Departures are numbered as in [corrections](corrections.md).

Dependencies (Lake `path` requirements, imported, not copied): Kreps Chapter 5
(`ChoiceUnderUncertainty`: `SimpleLottery`, `Mix`, `MixtureAxioms`, Propositions 5.3, 5.4, 5.12,
the uniqueness theorems and `subjective_*_unique`), Kreps Chapter 6 (`UtilityForMoney`:
`AbsoluteRiskAversion`, `RelativeRiskAversion`, Propositions 6.7-6.8, `ExponentialUtility`,
`proposition_6_12_exponential`, `symmetricUtility_quotient`, `GeneralQuantile`,
`midpoint_gap_nonneg`, `proposition_6_16c`, `expectedUtility_jensen`), MWG Chapter 1
(`MWGPreferenceChoice`: rationality, `rational_iff_mwg`) and MWG Chapter 3
(`MWGClassicalDemand`: `exercise_3_G_4c`, used for Exercise 6.E.2(c); `RationalOn`,
`PrefContinuous` and `prefContinuous_iff_continuousPreference`, used for Proposition 6.E.2).
Kreps Chapter 6's finite coupling theorem `supermartingaleCoupling_of_dominance` is the finite
step of Proposition 6.D.2, (i) ⇒ (ii). Kreps Chapter 2 (`PreferenceProperties`, a transitive
Lake dependency through `MWGClassicalDemand`) supplies Debreu's additive representation
theorem `proposition_2_14_exists`, used for Proposition 6.E.2.

## Conventions

* Simple lotteries over a finite outcome set `C` are Kreps's `SimpleLottery C` (Mathlib's
  `StdSimplex ℝ C`), identified with MWG's probability vectors by `definition_6_B_1`;
  `αL + (1-α)L'` is Kreps's `Mix`. MWG's continuity (Definition 6.B.3, closed sets of weights)
  and independence (Definition 6.B.4, interior weights) are MWG's own definitions
  (`MixContinuous`, `Independence`); `mixtureAxioms_of_mwg` bridges them to Kreps's axioms.
* Money lotteries are Borel probability measures on `ℝ` concentrated on a compact interval
  (`IsMoneyLottery`); Section 6.D uses MWG's restriction `F(0) = 0`, `F(x̄) = 1`
  (`IsMWGDist`). Distribution functions are Mathlib's `cdf`. See correction 1.
* "Increasing" Bernoulli utilities are strictly increasing; "decreasing" risk-aversion
  coefficients are nonincreasing (correction 4).

## OPEN items

None. The two items formerly open are proved:

1. **Proposition 6.D.2, (i) ⇒ (ii)** (p. 199) for arbitrary MWG distributions
   (`proposition_6_D_2_i_ii`; the full equivalence is `proposition_6_D_2`), with the converse
   claim of Example 6.D.2 and both inclusions of Exercise 6.D.4(c). Proof (modules
   `StrassenGrid`, `StrassenFinite`, `StrassenLimit`, `Strassen`): hat-function
   discretizations on the grid of mesh `x̄/(n+1)`, a contraction `Fₙ` of `F` and a dilation
   `Gₙ` of `G` with `Fₙ ≥ F ≥ G ≥ Gₙ` for concave utilities; Kreps's finite coupling
   `supermartingaleCoupling_of_dominance` gives a martingale coupling of `Fₙ` and `Gₙ` (equal
   means force zero drift); Mathlib's Prokhorov theorem gives a weak cluster point `π` on a
   compact square; marginals and the martingale identity `∫ φ(x)(y - x) dπ = 0` pass to the
   limit; disintegration (`Measure.condKernel`) and
   `ae_eq_zero_of_integral_contDiff_smul_eq_zero` give a kernel with conditional mean zero.
2. **Proposition 6.E.2** (p. 204), with the correction that at least three states must be
   *essential* (correction 16): `proposition_6_E_2` (module `DebreuAdditive`), from Kreps's
   `proposition_2_14_exists`; the printed statement is refuted by `proposition_6_E_2_false`.

## Section 6.A: Introduction (pp. 167-168)

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 167-168 | Overview of the chapter | Verbal |

## Section 6.B: Expected utility theory

| Source | Claim | Lean |
| --- | --- | --- |
| p. 168 | Outcome set `C`, finite | `Fintype C` throughout |
| Definition 6.B.1, p. 168 | Simple lottery `(p₁,…,p_N)`, `p ≥ 0`, `∑ p = 1` | `definition_6_B_1`, `lotteryOfVec`, `lotteryOfVec_weights` |
| p. 169, Figure 6.B.1 | Lotteries are points of the simplex `Δ`; vertices are degenerate lotteries | `lottery_vectors_eq_simplex`, `degenerate_lottery_weights` |
| Footnote 2, p. 169 | Equilateral triangle of altitude 1: perpendicular to the side opposite vertex `n` has length `p_n` | `footnote_6_2` |
| Definition 6.B.2, p. 169 | Compound lottery and reduced lottery `p_n = ∑ α_k p_n^k` | `reducedVec`, `reducedLottery`, `reducedLottery_weights` |
| Footnote 3, p. 169 | More than two stages | Verbal |
| Footnote 4, p. 170 | Reduced probabilities sum to one | `footnote_6_4` |
| p. 170, Figure 6.B.2 | `L = ∑ α_k L_k`; midpoint `½L₁ + ½L₂` | `reducedLottery_two`, `figure_6_B_2` |
| Figure 6.B.3, p. 170 | Two compound lotteries with reduced lottery `(1/2,1/4,1/4)` | `figure_6_B_3` |
| p. 171 | Rational preference on `ℒ` (MWG Definition 1.B.1) | `rational_iff_mwg` |
| Definition 6.B.3, p. 171 | Continuity | `MixContinuous` |
| p. 171 | Continuity ⇒ utility representation | Consequence of Proposition 6.B.3 under independence; general case is Chapter 3 |
| Definition 6.B.4, p. 171 | Independence axiom | `Independence` |
| Footnote 5, p. 171 | History | Verbal |
| Figure 6.B.4, p. 172 | Coin-toss illustration | `independence_left` |
| Exercise 6.B.1, p. 172 | Strict and indifference versions; `L ≻ L'`, `L'' ≻ L'''` ⇒ mixtures ranked | `exercise_6_B_1_strict`, `exercise_6_B_1_indifferent`, `exercise_6_B_1_both` |
| Definition 6.B.5, p. 173 | Expected utility form; v.N-M utility | `HasExpectedUtilityForm`, `hasExpectedUtilityForm_iff` (= Kreps `ExpectedUtility`) |
| p. 173 | `U(Lⁿ) = u_n` | `expectedUtilityForm_degenerate` |
| Proposition 6.B.1, p. 173 | Expected utility form ⇔ linear (6.B.1) | `proposition_6_B_1`, `IsLinearUtility`, `reducedLottery_degenerate` |
| Proposition 6.B.2, p. 173 | v.N-M utilities unique up to `βU + γ`, `β > 0` | `proposition_6_B_2` (via Kreps `proposition_5_4_unique`) |
| Footnote 6, p. 173 | Best and worst lotteries exist | `footnote_6_6` |
| p. 174 | `u₁ - u₂ > u₃ - u₄` ⇔ `(½,0,0,½) ≻ (0,½,½,0)`; preserved by linear transformations | `utility_differences_meaning`, `utility_differences_invariant` |
| p. 175 | EU form ⇒ continuous | `continuous_of_expectedUtilityForm` |
| Exercise 6.B.2, p. 175 | EU form ⇒ independence | `exercise_6_B_2` |
| p. 175, Figure 6.B.5(a) | EU ⇔ straight parallel indifference lines | `indifference_set_hyperplane` |
| p. 175-176, Figure 6.B.5(b)-(c) | Independence ⇒ straight and parallel indifference curves | `indifference_straight`, `indifference_parallel` |
| Proposition 6.B.3, p. 176 | Expected utility theorem | `proposition_6_B_3`; converse `proposition_6_B_3_converse`; bridge `mixtureAxioms_of_mwg` |
| Step 1, p. 176 | `L ≻ αL + (1-α)L' ≻ L'` | `proposition_6_B_3_step1` |
| Step 2, p. 176 | `βL̄ + (1-β)L̲ ≻ αL̄ + (1-α)L̲` iff `β > α` | `proposition_6_B_3_step2` |
| Step 3, p. 177 | Unique `α_L` | `proposition_6_B_3_step3` |
| Steps 4-5, p. 177 | `U(L) = α_L` represents and is linear | `proposition_5_4` (Kreps) via `proposition_6_B_3` |
| Footnote 7, p. 176 | Best/worst exist under independence | `exercise_6_B_3` |
| Example 6.B.1, p. 178, Figure 6.B.6 | Inference along a segment; fails for general maps | `example_6_B_1`, `example_6_B_1_general_map_fails` |
| Example 6.B.2, pp. 179-180, Figure 6.B.7 | Allais paradox; parallel segments | `allaisL1` … `allaisL2'`, `figure_6_B_7`, `example_6_B_2`, `example_6_B_2_axioms` |
| Footnote 8, p. 179 | Classroom experience | Verbal |
| p. 180 | Four reactions; regret theory | Verbal |
| Example 6.B.3, pp. 180-181 | Machina's paradox | `example_6_B_3` |
| p. 181 | Independence ⇒ convex not-better-than sets; strictly weaker | `dutchBook_convexity`, `noBetter_isConvexSet`, `dutchBook_convexity_weaker` |
| p. 181 | Dutch book narrative | Verbal |
| Example 6.B.4, pp. 181-182 | Induced preferences; four-outcome formulation | `example_6_B_4`, `example_6_B_4_outcomes` |
| Footnote 9, p. 182 | Ex post actions give EU | `footnote_6_9` |
| Footnote 10, p. 182 | Intertemporal consumption | Verbal |
| p. 182-183, Figure 6.B.8 | Induced utility convex, not linear | `exercise_6_B_6_convex`, `example_6_B_4` |
| Exercise 6.B.3, p. 208 | Best and worst lotteries under independence | `exercise_6_B_3` |
| Exercise 6.B.4(a), p. 208 | EU function for the agency | `exercise_6_B_4a` |
| Exercise 6.B.4(b), p. 208 | Distributions under both criteria; criterion 2 preferred | `exercise_6_B_4b` |
| Exercise 6.B.5(a), p. 209 | Independence ⇒ betweenness | `Betweenness`, `exercise_6_B_5a` |
| Exercise 6.B.5(b), p. 209 | Betweenness ⇔ straight indifference curves; need not be parallel | `exercise_6_B_5b`, `exercise_6_B_5c` |
| Exercise 6.B.5(c), p. 209 | Betweenness strictly weaker than independence | `exercise_6_B_5c`, `weightedPref_betweenness`, `weightedPref_rational_continuous` |
| Exercise 6.B.5(d), p. 209 | Allais choices with a betweenness map | `exercise_6_B_5d`, `weightedV` |
| Exercise 6.B.6, p. 209 | Induced utility convex; nonlinear example | `exercise_6_B_6_convex`, `example_6_B_4` |
| Exercise 6.B.7, p. 209 | `L ≻ L'` iff `x_L > x_{L'}` | `exercise_6_B_7` |

## Section 6.C: Money lotteries and risk aversion

| Source | Claim | Lean |
| --- | --- | --- |
| p. 183 | Money lotteries as distribution functions; mixtures of distributions | `IsMoneyLottery`, `mixM`, `cdf_mixM`, `mixM_isProbabilityMeasure` (correction 1) |
| Figure 6.C.1, p. 184 | A distribution function with three atoms | `figure_6_C_1_lottery`, `figure_6_C_1` |
| (6.C.1), p. 184 | `U(F) = ∫ u dF` under the axioms | False as stated: `expectedUtility_6_C_1_counterexample` (correction 2); true on simple lotteries (Kreps `proposition_5_3`) |
| Footnote 11, p. 184 | Expectation notation | `integral_binLot`, Mathlib integral |
| Footnote 12, p. 184 | Terminology | Verbal |
| p. 185 | Bernoulli utility increasing and continuous | Standing hypotheses |
| Footnote 13, p. 185 | `u(0) = -∞` exception | Verbal |
| p. 185 | St. Petersburg-Menger paradox | `stPetersburg`, `stPetersburg_probabilities` |
| Footnote 14, p. 185 | Concave on `ℝ` and bounded ⇒ constant | `footnote_6_14`, `concave_bddBelow_le` |
| Definition 6.C.1, p. 185 | Risk averter, risk neutral, strictly risk averse | `RiskAverter`, `RiskNeutral`, `StrictlyRiskAverse`, `euPref` |
| (6.C.2), p. 185 | Risk aversion ⇔ Jensen | `riskAverter_iff_jensen`, `jensen_moneyLottery` |
| p. 186 | Risk aversion ⇔ concave; strict ⇔ strictly concave; neutral ⇔ linear | `proposition_6_C_1_i_ii`, `strictlyRiskAverse_iff`, `riskNeutral_iff_affine` |
| Figure 6.C.2, p. 186 | `½u(1) + ½u(3) < u(2)`; linear case | `figure_6_C_2a`, `figure_6_C_2b` |
| Definition 6.C.2(i), p. 186 | Certainty equivalent (6.C.3); existence, uniqueness | `IsCertaintyEquivalent`, `certaintyEquivalent_exists`, `certaintyEquivalent_unique` |
| Definition 6.C.2(ii), p. 186 | Probability premium (6.C.4) | `probPremium`, `probPremium_spec` |
| Figure 6.C.3, p. 187 | Constructions; `x + 2επ` | `figure_6_C_3b` |
| p. 187 | `c(F,u) ≤ ∫x dF` ⇔ … ⇔ Jensen | `certaintyEquivalent_le_mean_iff` |
| Proposition 6.C.1, p. 187 | (i)-(iv) equivalent | `proposition_6_C_1`, `proposition_6_C_1_ii_iii`, `proposition_6_C_1_ii_iv`, `concaveOn_of_midpoint` |
| Footnote 16, p. 187 | Concave ⇔ `u'' ≤ 0` | `footnote_6_16` |
| Example 6.C.1, pp. 187-188 | Insurance: expected wealth, FOC, fair ⇒ `α* = D`, direct argument | `insuranceEU`, `example_6_C_1_expected_wealth`, `example_6_C_1_foc`, `example_6_C_1` |
| Example 6.C.2, pp. 188-189 | Favorable risky asset ⇒ `α* > 0` | `assetEU`, `example_6_C_2` |
| Footnote 17, p. 189 | Objective concave in `α` | `footnote_6_17` |
| Example 6.C.3, p. 189 | Portfolio utility increasing, continuous, concave | `portfolioU`, `exercise_6_C_4a/b/c` (two assets: `N = 2`) |
| p. 189 | Commodity lotteries: risk aversion ⇔ concavity; induced money lotteries | `exercise_6_C_5a`, `exercise_6_C_5b` |
| Definition 6.C.3, p. 190 | Arrow-Pratt coefficient | `arrowPratt`, `arrowPratt_eq_kreps` |
| p. 190 | `u''` not invariant; `r_A` invariant | `second_derivative_not_invariant`, `arrowPratt_affine_invariant` |
| p. 190 | `r_A(x) = 4π'(0)` | `arrowPratt_eq_four_probPremium_slope` (correction 3) |
| Footnote 18, p. 190 | See Exercise 6.C.20 | `exercise_6_C_20` |
| p. 191 | `u` recovered from `r_A` up to two constants | `utility_determined_by_arrowPratt` |
| Example 6.C.4, p. 191 | `r_A(-e^{-ax}) = a`; general CARA form | `example_6_C_4`, `example_6_C_4_general` |
| (i)-(v), p. 191 | Five definitions of "more risk averse" | `MoreRiskAverseI` … `MoreRiskAverseV` |
| Footnote 19, p. 191 | Reading of (v) | `MoreRiskAverseV` |
| Proposition 6.C.2, p. 191 | (i)-(v) equivalent | `proposition_6_C_2`; pieces `moreRiskAverse_ii_iii`, `moreRiskAverse_iii_v`, `moreRiskAverse_v_iii`, `moreRiskAverse_iii_iv`, `moreRiskAverse_iv_i`; bridges `kreps_of_moreRiskAverseV`, `moreRiskAverseII_of_kreps`, `kreps_of_moreRiskAverseII` |
| p. 191-192 | Proof (i) ⇔ (ii) for differentiable utilities | Kreps `proposition_6_8`, `proposition_6_7` inside `proposition_6_C_2` |
| p. 192 | Partial ordering, transitive, far from complete | `moreRiskAverseI_trans`, `moreRiskAverse_not_complete`, `arrowPratt_log` |
| Example 6.C.2 continued, p. 192 | More risk averse invests less | `invest_compare`, `example_6_C_2_continued`, `concave_supergradient` (correction 5) |
| Definition 6.C.4, p. 193 | Decreasing absolute risk aversion | `DecreasingAbsoluteRiskAversion` |
| Proposition 6.C.3, p. 193 | (i)-(v) equivalent | `proposition_6_C_3`, `shift_tfae`, `shiftU` |
| Exercise 6.C.8, p. 193 | DARA ⇒ risky asset normal | `exercise_6_C_8` |
| Definition 6.C.5, p. 194 | Relative risk aversion | `relativeRiskAversion`, `relativeRiskAversion_eq`, `relativeRiskAversion_eq_kreps` |
| p. 194 | Decreasing relative ⇒ decreasing absolute (risk averse); not conversely | `decreasingAbsolute_of_decreasingRelative`, `decreasingRelative_not_of_decreasingAbsolute` |
| Proposition 6.C.4, p. 194 | (i)-(iii) equivalent (all three directions) | `proposition_6_C_4`, `scale_tfae`, `scaleU` |
| Example 6.C.2 continued, p. 194 | Proportion invested and `r_R` | `exercise_6_C_11`, `proportion_objective` |
| Exercise 6.C.1, p. 209 | Unfair insurance ⇒ incomplete insurance | `exercise_6_C_1` |
| Exercise 6.C.2(a), p. 209 | Quadratic utility depends on mean and variance; note on `β < 0` | `exercise_6_C_2a`, `exercise_6_C_2a_moments`, `exercise_6_C_2a_note` |
| Exercise 6.C.2(b), p. 209 | Mean-variance incompatible with any Bernoulli utility; FOSD violation | `exercise_6_C_2b`, `meanVarianceU` |
| Exercise 6.C.3, p. 210 | Proposition 6.C.1 equivalences | `exercise_6_C_3`, `proposition_6_C_1` |
| Exercise 6.C.4(a)-(c), p. 210 | Portfolio utility increasing, concave, continuous | `exercise_6_C_4a`, `exercise_6_C_4b`, `exercise_6_C_4c` |
| Exercise 6.C.5(a), p. 210 | Concavity ⇔ risk aversion over bundles | `exercise_6_C_5a` |
| Exercise 6.C.5(b), p. 210 | Derived utility of wealth concave | `exercise_6_C_5b` (Kreps `proposition_6_16c`) |
| Exercise 6.C.5(c), p. 210 | Converse fails | `exercise_6_C_5c`, `bumpUtility` |
| Exercise 6.C.6(a), p. 210 | (ii) ⇔ (iii) | `moreRiskAverse_ii_iii`, `proposition_6_C_2` |
| Exercise 6.C.6(b), p. 210 | (iii) ⇔ (v) | `moreRiskAverse_iii_v`, `moreRiskAverse_v_iii` |
| Exercise 6.C.7, p. 210 | (iii) ⇒ (iv) ⇒ (i) | `moreRiskAverse_iii_iv`, `moreRiskAverse_iv_i` |
| Exercise 6.C.8, p. 210 | In text | `exercise_6_C_8` |
| Exercise 6.C.9(a), p. 211 | Precautionary saving | `exercise_6_C_9a`, `hasDerivAt_expected` |
| Exercise 6.C.9(b), p. 211 | Prudence comparison; implications | `exercise_6_C_9b`, `prudence`, `prudence_eq_arrowPratt` |
| Exercise 6.C.9(c), p. 211 | `v''' > 0`, `E y = 0` ⇒ `E v'(x+y) > v'(x)` | `exercise_6_C_9c`, `exercise_6_C_9c_degenerate` (correction 8) |
| Exercise 6.C.9(d), p. 211 | DARA ⇒ prudence ≥ `r_A`, `v''' > 0` | `exercise_6_C_9d`, `exercise_6_C_9d_cara` (correction 9) |
| Exercise 6.C.10, p. 211 | Proposition 6.C.3 | `proposition_6_C_3` |
| Exercise 6.C.11, p. 211 | `r_R` increasing/decreasing ⇒ proportion decreasing/increasing | `exercise_6_C_11` |
| Exercise 6.C.12(a), p. 211 | CRRA `ρ ≠ 1` | `exercise_6_C_12a`, `exercise_6_C_12a_printed_counterexample` (correction 6) |
| Exercise 6.C.12(b), p. 211 | CRRA 1 ⇔ `β ln x + γ` | `exercise_6_C_12b` |
| Exercise 6.C.12(c), p. 211 | Limit to `ln x` | `exercise_6_C_12c`, `exercise_6_C_12c_printed_counterexample` (correction 7) |
| Exercise 6.C.13, p. 211 | Risk-neutral firm prefers random prices | `exercise_6_C_13`, `maxProfit` |
| Exercise 6.C.14(a), p. 211 | Strongly more risk averse ⇒ Arrow-Pratt | `exercise_6_C_14a` |
| Exercise 6.C.14(b), p. 211 | Bounded `u`: only `ku + c` | `exercise_6_C_14b` |
| Exercise 6.C.14(c), p. 211 | Strictly stronger concept | `exercise_6_C_14c` |
| Exercise 6.C.15(a), p. 212 | Necessary condition for `x₁ > 0` | `exercise_6_C_15a`, `twoAssetEU` |
| Exercise 6.C.15(b), p. 212 | Necessary condition for `x₂ > 0` | `exercise_6_C_15b` |
| Exercise 6.C.15(c), p. 212 | First-order condition | `exercise_6_C_15c`, `twoAssetFOC` |
| Exercise 6.C.15(d), p. 212 | `dx₁/da ≤ 0` (indeed `< 0`) for `a < 1` | `exercise_6_C_15d`, `foc_along_a` |
| Exercise 6.C.15(e), p. 212 | Conjecture `dx₁/dπ ≥ 0`; interpretation | `exercise_6_C_15f` (statement); interpretation verbal |
| Exercise 6.C.15(f), p. 212 | Proof via the FOC | `exercise_6_C_15f`, `foc_along_π` |
| Exercise 6.C.16(a), p. 212 | Selling price | `IsSellingPrice`, `exercise_6_C_16a` |
| Exercise 6.C.16(b), p. 212 | Buying price | `IsBuyingPrice`, `exercise_6_C_16b` |
| Exercise 6.C.16(c), p. 212 | Equal for CARA and riskless lotteries; interpretation | `exercise_6_C_16c_cara`, `exercise_6_C_16c_riskless`; `exercise_6_C_16d` shows inequality |
| Exercise 6.C.16(d), p. 212 | `√x`, `G = 10`, `B = 5`, `w = 10` | `exercise_6_C_16d` (selling price for every `p`; both prices at `p = 1/2`) |
| Exercise 6.C.17, p. 212 | CRRA ⇒ `α₀ = α₁`; fails under CARA | `exercise_6_C_17_period1`, `exercise_6_C_17_period0`, `exercise_6_C_17_log`, `exercise_6_C_17_cara`, `caraObjective_eq` |
| Exercise 6.C.18(a), p. 212 | `r_A(5) = 1/10`, `r_R = 1/2` | `exercise_6_C_18a`, `arrowPratt_sqrt` |
| Exercise 6.C.18(b), p. 212 | CE `9`, `π = (√10 - 3)/2` | `exercise_6_C_18b` |
| Exercise 6.C.18(c), p. 212 | CE `25`, `π = (√26 - 5)/2`; comparison | `exercise_6_C_18c` |
| Exercise 6.C.19, pp. 212-213 | CARA with normal returns: demand | `exercise_6_C_19`, `exercise_6_C_19_exists`, `caraPortfolioEU_eq`, instance `exercise_6_C_19_instance` |
| Exercise 6.C.20, p. 213 | `c''(ε) → -r_A(x)` | `exercise_6_C_20`, instance `exercise_6_C_20_instance` |

## Section 6.D: Comparison of payoff distributions

| Source | Claim | Lean |
| --- | --- | --- |
| p. 195 | Restriction `F(0) = 0`, `F(x̄) = 1` | `IsMWGDist`, `IsMWGDist.ae_mem`, `IsMWGDist.isMoneyLottery` |
| Footnote 20, p. 195 | Rothschild-Stiglitz | Verbal |
| Definition 6.D.1, p. 195 | First-order stochastic dominance | `FOSD` |
| Proposition 6.D.1, p. 195 | FOSD ⇔ `F ≤ G` (both directions, all distributions) | `proposition_6_D_1`, `monotone_step`, `integral_step`, `IsMWGDist.integrable_monotone` |
| p. 196, Figure 6.D.1 | FOSD ⇒ higher mean; converse false | `exercise_6_D_2_mean`, `exercise_6_D_2_example` |
| Example 6.D.1, p. 196 | Upward probabilistic shift ⇒ FOSD | `example_6_D_1` |
| Figure 6.D.2, p. 196 | `G` uniform on `{1,4}`, shifted `F` | `figure_6_D_2`, `lot3M`, `integral_lot3M` |
| Example 6.D.1, p. 197 | Converse: FOSD ⇒ upward shift | `example_6_D_1_converse` |
| Definition 6.D.2, p. 197 | Second-order stochastic dominance | `SOSD`, `IsMWGDist.integrable_concave` |
| Example 6.D.2, p. 197 | Mean-preserving spread ⇒ SOSD, equal means | `IsMeanPreservingSpread`, `sosd_of_meanPreservingSpread` |
| Example 6.D.2, p. 197, Figure 6.D.3 | `(2,3)` spread to uniform `{1,2,3,4}` | `example_6_D_2`, `example_6_D_2_spread`, `dirac_compProd_map_add` |
| Example 6.D.2, p. 198 | Converse (SOSD ⇒ MPS); the two notions are equivalent | `proposition_6_D_2_i_ii`, `example_6_D_2_equivalence` |
| Example 6.D.3, p. 198, Figure 6.D.4 | Elementary increase in risk | `elementaryIncrease`, `integral_elementaryIncrease`, `exercise_6_D_3` |
| (6.D.1), p. 198 | Equal areas with equal means | `equal_areas`, `integral_min_eq` |
| (6.D.2), p. 198 | Integral condition | `IntegralCondition` |
| p. 198-199, Figures 6.D.4-6.D.5 | Single crossing ⇒ (6.D.2) | `integralCondition_of_single_crossing` |
| Footnote 21, p. 198 | (6.D.2) ⇔ SOSD | `proposition_6_D_2_i_iii` |
| Proposition 6.D.2, p. 199 | (i) ⇔ (iii); (ii) ⇒ (i); (i) ⇒ (ii) | `proposition_6_D_2`, `proposition_6_D_2_i_iii`, `sosd_integralCondition`, `sosd_of_integralCondition`, `sosd_of_meanPreservingSpread`, `proposition_6_D_2_i_ii` |
| Proposition 6.D.2, (i) ⇒ (ii): grid step | Hat functions, partition of unity, `∑ λ_j x_j = t`, concave interpolation; dilation and contraction of a distribution, their means and the concave-utility inequalities | `hatFn`, `hatFn_grid_sum`, `hatFn_sum_one`, `hatFn_sum_id`, `hatFn_sum_concave`, `hatFn_sum_approx`, `gridMass`, `gridCtr`, `gridMass_sum`, `gridMass_mul_ctr`, `abs_gridCtr_sub_le`, `dilation_le`, `dilation_mean`, `le_contraction`, `contraction_mean` |
| Proposition 6.D.2, (i) ⇒ (ii): finite step | Martingale coupling of the discretizations (Kreps `supermartingaleCoupling_of_dominance`) | `atomLottery`, `expectedUtility_atomLottery`, `exists_grid_martingale_coupling` |
| Proposition 6.D.2, (i) ⇒ (ii): limit step | Prokhorov cluster point with marginals `F`, `G` and `∫ φ(x)(y - x) dπ = 0` | `tendsto_hat_average`, `eq_of_mapClusterPt_of_tendsto`, `truncAt`, `exists_martingale_coupling` |
| Exercise 6.D.1(a), p. 213 | FOSD region in the simplex | `exercise_6_D_1a` |
| Exercise 6.D.1(b), p. 213 | `F ≤ G` region; same | `exercise_6_D_1b`, `lot3M_isMWGDist` |
| Exercise 6.D.2, p. 213 | FOSD ⇒ higher mean; counterexample | `exercise_6_D_2_mean`, `exercise_6_D_2_example` |
| Exercise 6.D.3, p. 213 | Elementary increase in risk is SOSD-dominated | `exercise_6_D_3` |
| Exercise 6.D.4(a), p. 213 | Equal means: a line in the simplex | `exercise_6_D_4a` |
| Exercise 6.D.4(b), p. 213 | SOSD region | `exercise_6_D_4b` |
| Exercise 6.D.4(c), p. 213 | MPS region | `exercise_6_D_4c` (MPS ⊆ region), `exercise_6_D_4c_converse` (region ⊆ MPS), `exercise_6_D_4c_iff`, instance `exercise_6_D_4c_instance` |
| Exercise 6.D.4(d), p. 213 | (6.D.2) region | `exercise_6_D_4d` |

## Section 6.E: State-dependent utility

| Source | Claim | Lean |
| --- | --- | --- |
| p. 200 | States with probabilities `π_s` | `Fintype S`, `π : S → ℝ` |
| Definition 6.E.1, p. 200 | Random variable; induced distribution `F(x) = ∑_{g(s) ≤ x} π_s` | `inducedLaw`, `inducedLaw_cdf`, `integral_inducedLaw` |
| Footnote 23, p. 200 | Abstract outcomes possible | Proposition 6.E.1 is stated for an arbitrary prize type |
| Definition 6.E.2, p. 201 | Extended expected utility representation | `HasExtendedEU` |
| Footnote 24, p. 201 | State-uniform: EU of the induced lottery | `footnote_6_24` |
| p. 201, Figure 6.E.1 | MRS on the certainty line | `certainty_line_mrs` |
| Example 6.E.1, pp. 201-202, Figure 6.E.2 | Fair insurance: full insurance (uniform); not with state dependence | `example_6_E_1_uniform`, `example_6_E_1_dependent` |
| p. 202 | Absorbing `π_s` into `u_s` | `absorb_probabilities` |
| Footnote 25, p. 202 | Corollary of the EU theorem | Verbal (Proposition 6.E.1 is proved through Kreps 5.12) |
| Definition 6.E.3, p. 203 | Extended independence axiom | `ExtendedIndependence` |
| Proposition 6.E.1, p. 203 | Extended expected utility theorem | `proposition_6_E_1` (finitely supported state lotteries; Kreps `proposition_5_12`), converse `proposition_6_E_1_converse`; general distributions false (correction 10) |
| p. 204 | Risk aversion ⇔ every `u_s` concave | `riskAversion_iff_concave_states` |
| Definition 6.E.4, p. 204 | Sure-thing axiom | `SureThing` (on `ℝ^S`), `SureThingOn` (on a domain such as `ℝ^S_+`), `SureThing.sureThingOn` |
| p. 204 | Extended EU ⇒ sure-thing | `sureThing_of_additive` |
| Proposition 6.E.2, p. 204 | Sure-thing + continuity + rationality on `ℝ^S_+`, at least three essential states ⇒ `∑_s u_s(x_s)` with continuous `u_s` | `proposition_6_E_2`, `EssentialState`; instance `proposition_6_E_2_instance` (correction 16) |
| Proposition 6.E.2, p. 204 | As printed ("at least three states"): false for every `S ≥ 2` | `proposition_6_E_2_false`, `thomsenPref`, `thomsenPref_rational`, `thomsenPref_continuous`, `thomsenPref_sureThing`, `thomsenPref_not_additive`, `thomsenPref_essential` (correction 16) |
| Exercise 6.E.1, pp. 213-214 | Regret: intransitivity | `regret`, `exercise_6_E_1` |
| Exercise 6.E.2(a), p. 214 | Convex preferences on contingent commodities | `exercise_6_E_2a` |
| Exercise 6.E.2(b), p. 214 | Risk averse over vector lotteries | `exercise_6_E_2b` |
| Exercise 6.E.2(c), p. 214 | Normal demands | `exercise_6_E_2c` (MWG `exercise_3_G_4c`) |
| Exercise 6.E.3, p. 214 | `G*` SOSD `G`; means equal | `exercise_6_E_3` |

## Section 6.F: Subjective probability theory

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 204-205 | Setting with state-contingent lotteries | `HorseLottery` (Kreps) |
| Footnote 26, p. 205 | Arbitrary outcome sets | Arbitrary prize type `X` |
| p. 205 | `u_s` not identified separately from `π_s` | `absorb_probabilities` |
| p. 206 | State preferences `≿_s` | `statePref` |
| Definition 6.F.1, p. 206 | State uniformity | `StateUniform` |
| p. 206 | `u_s = π_s u + β_s` | `stateUniform_affine` |
| Proposition 6.F.1, p. 206 | Subjective expected utility theorem | `proposition_6_F_1`, `proposition_6_F_1_sure` |
| Exercise 6.F.1, p. 214 | Uniqueness of `u` and of the probabilities | `exercise_6_F_1_utility`, `exercise_6_F_1_probabilities`, `exercise_6_F_1_probabilities_not_unique` (correction 11) |
| p. 206 | Discussion of axioms | Verbal |
| Example 6.F.1, p. 206 | Ellsberg variation | `example_6_F_1` |
| Footnote 27, p. 206 | Source | Verbal |
| Exercise 6.F.2(a), p. 215 | Single belief: vNM; equivalence | `gsUtilityW`, `gsUtilityB`, `exercise_6_F_2a` |
| Exercise 6.F.2(b), p. 215 | `P = [0.4, 0.6]` explains the experiments | `exercise_6_F_2b` |
