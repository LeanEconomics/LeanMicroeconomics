# Corrections and departures

MWG, Chapter 4, pp. 105-126. Each item names what the book prints, what is proved here, and
the Lean declarations. Page images were checked for every item.

1. **Proposition 4.C.1 (p. 111): wealth shares `αᵢ ≥ 0`.** A consumer with `αᵢ = 0` has wealth
   `0`, outside the domain `p ≫ 0`, `w > 0` on which MWG Chapter 2 defines demand functions,
   homogeneity, Walras' law and the ULD. The proposition is proved for `αᵢ > 0`
   (`uld_shareDemand`, `proposition_4_C_1`, `aggregate_compensated_law`, `exercise_4_C_2`). A
   consumer with zero share and zero demand at zero wealth can be dropped from the sum without
   changing aggregate demand.

2. **Proposition 4.C.2 (p. 112): the differentiable proof.** The book's proof uses
   `dp·Sᵢ(p, wᵢ) dp < 0` for `dp` not proportional to `p`, which is not implied by preference
   maximization (item 3). The proposition itself is true for every homothetic preference with
   single-valued demand: `proposition_4_C_2` (utility homogeneous of degree one, no
   differentiability) and `proposition_4_C_2_pref` (rational, continuous, monotone, homothetic,
   strictly convex preference). The book's identity `D_p x = S - (1/w) x xᵀ` and its conclusion
   under the extra hypothesis are `proposition_4_C_2_differential` and
   `proposition_4_C_2_negDef`.

3. **Section 4.C (p. 114): "For an individual Slutsky matrix we always have
   `dp·Sᵢ(p, αᵢw) dp < 0` for `dp ≠ 0` not proportional to `p`."** False: the Leontief demand
   `x(p, w) = w/(p₁ + p₂) (1, 1)` (utility `min(x₁, x₂)`) is differentiable with Slutsky matrix
   `0` (`leontief_slutsky_zero`); more generally every L-shaped preference has `S = 0`
   (`slutsky_zero_minUtility`). Preference maximization gives only negative semidefiniteness.
   The sufficient condition for the weak axiom (`slutsky_negative_of_cov_psd`,
   `weakAxiom_of_cov_psd`) therefore carries "`Sᵢ` negative off the price ray" as a hypothesis.

4. **Proposition 4.C.4 (p. 113): Hildenbrand's aggregate demand "satisfies the ULD".**
   Definition 4.C.2 includes the strict inequality when demand changes. The weak inequality
   `(p' - p)·[x(p') - x(p)] ≤ 0` holds for every individual demand satisfying the weak axiom and
   Walras' law, with no differentiability (`proposition_4_C_4`, via the Young-type inequality
   `young_square`). The strict inequality fails in general:
   `proposition_4_C_4_strict_counterexample` gives an L-shaped preference, wealth uniform on
   `[0, 4]` and `p = (1, 1)`, `p' = (13/10, 1/2)` with `x(p) = (11/2, 5/2)`,
   `x(p') = (21/4, 47/20)` and `(p' - p)·[x(p') - x(p)] = 0`. The book's proof uses
   "`v·S v < 0` unless `v` is proportional to `p`", an extra hypothesis (item 3). Under that
   hypothesis, in the book's differentiable case (directional price derivatives and the wealth
   derivative of `x̃` with quadratic forms continuous on `ℝ^L_{++} × [0, w̄]`, `x̃(p, 0) = 0`), the
   strict statement is proved: `(p' - p)·[x(p') - x(p)] < 0` for all `p ≠ p'`
   (`proposition_4_C_4_strict`). The proof does not differentiate under the integral sign: it
   integrates the price derivative along `p + t(p' - p)` and swaps the two integrals (Fubini). On
   the price ray the Slutsky form vanishes by Walras' law (`hild_ray_slutsky`), and the strict
   sign there comes from the mean income effect, as in the book. The hypotheses hold for
   Cobb-Douglas demand (`cobbDouglasHalf_hildenbrand`).

5. **Proposition 4.C.3 (p. 112) and Exercise 4.C.5.** Proved on `X = ℝ^L_+` with boundary
   demands (`proposition_4_C_3`): the hypotheses on `u` are required at every `x ≥ 0`, `x ≠ 0`
   (where the quotient `σ(x)` is defined), with differentiability in the sense of a function on
   `ℝ^L`. The hint's self-duality `g(x(p, 1)) = p` holds only at interior optima; at corners the
   first-order condition `∇u(x)·(y - x) ≤ 0` on the budget set (`demand_variational`) gives
   `w g(x(p, w))·y ≤ p·y` for `y ≥ 0`, which suffices. Concavity enters through the Hessian being
   negative semidefinite (MWG Theorem M.C.2), `x·∇u(x) > 0` is assumed (it is implicit in
   `σ(x)`), and the demand is single-valued as the book presupposes. A version for any convex set
   of bundles containing all demands (`mp_uld_on`) covers utilities such as `x₁ + 4√x₂`
   (Exercise 4.C.11), which are not differentiable on all of `ℝ^L_+` but have corner demands
   (`ql_uld`); `proposition_4_C_3_interior` keeps the interior version.

6. **Proposition 4.D.1 (p. 117).** The book's proof uses first-order conditions, Roy's identity
   and the envelope theorem, and neglects corners. Here (`proposition_4_D_1_demand`,
   `proposition_4_D_1`) it is proved without differentiability, which also settles Exercise 4.D.3.
   For the representative to be a *positive* representative consumer (single-valued demand),
   the solution of (4.D.1) must be unique; the book treats `(wᵢ(p, w))` as a function and does
   not state this. The proof also assumes `W` continuous and strictly increasing, `uᵢ`
   continuous with single-valued demand (the book's standing assumptions in Section 4.D).
   Without uniqueness, `x(p, w)` is still a Walrasian demand of the representative and `v(p, w)`
   its indirect utility (`proposition_4_D_1_demand`).

7. **Example 4.D.1 / Exercise 4.D.6 (pp. 118-119).** `W(u) = ∑ᵢ αᵢ ln uᵢ` is defined only for
   positive utilities, so the optimality of `wᵢ = αᵢ w` is proved among positive distributions
   (`exercise_4_D_6`), where it is the unique optimum.

8. **Exercise 4.C.12 (p. 125).** "Wealths `w₁ = 1` and `w₂ = 3`" is formalized as the share
   rule `(1/4, 3/4)` (exact wealths `1` and `3` at `w = 4`), so that aggregate demand is a demand
   function of `(p, w)` to which the weak axiom applies (`exercise_4_C_12`).

9. **Exercise 4.C.7 (p. 124), second part.** "Unimodal" is realized by the tent density on
   `[5/2, 7/2]` (`exercise_4_C_7_unimodal`).

10. **Proposition 4.B.1 (p. 107), necessity.** The book does not prove it. It is proved here
    (`proposition_4_B_1_necessity`) for continuous, locally nonsatiated, strictly convex
    preferences; "admits an indirect utility function of the Gorman form" is formalized as: the
    Gorman function orders price-wealth pairs exactly as `vᵢ`. The invariance characterization
    (pp. 106-107) needs at least two consumers (`invariant_iff_parallel`).

11. **Exercise 4.C.10 (p. 124): "conclude that aggregate demand satisfies the WA".** The
    covariance matrix adapted to the continuum is positive semidefinite (`exercise_4_C_10`). The
    conclusion needs the hypothesis of item 3 (`Sᵢ` negative off the price ray); with it, and
    with the regularity of item 4 for every `w̄`, the aggregate demand as a function of mean
    wealth, `X(p, m) = (1/2m) ∫₀^{2m} x̃(p, w) dw` (wealth uniform on `[0, 2m]`), is homogeneous
    of degree zero, satisfies Walras' law and the strict ULD, hence the WA
    (`exercise_4_C_10_weakAxiom`; instance `cobbDouglasHalf_weakAxiom`). The proof uses the ULD
    route of Proposition 4.C.1 rather than the decomposition `S = ∫ Sᵢ - C`.

12. **Exercise 4.C.11(b) (pp. 124-125).** Individual demands have corners; there `Sᵢ = 0`
    (`exercise_4_C_11b_consumer1`, `exercise_4_C_11b_consumer2`). Aggregate demand is
    differentiable only off the kinks `w/2 = 4p₁²/p₂`, `w/2 = 4p₂²/p₁`; in each of the four open
    regions `v·S v = κ (p₂ v₁ - p₁ v₂)²` with `κ < 0` (`exercise_4_C_11b_aggregate`,
    `exercise_4_C_11b_negative`). "dp·S dp < 0 for all (p, w)" is therefore proved where `S`
    exists. The weak axiom is proved everywhere, kinks included, from the ULD of each
    quasilinear consumer (Proposition 4.C.3 with corners) and Proposition 4.C.1
    (`exercise_4_C_11b_weakAxiom`), not from the Slutsky matrix.

13. **Exercise 4.D.10 (p. 126).** The positive representative comes from the WA via MWG
    Chapter 3's Exercise 3.J.1 (WA ⟺ SA for `L = 2`) and Proposition 3.J.1
    (`exercise_4_D_10_positive`), not from the differentiable integrability theorem (aggregate
    demand has kinks). "No normative representative" is proved for every nondecreasing `W` (the
    standing assumption of p. 117) by a finite argument instead of Exercise 4.D.9 (which would
    need differentiability and strict convexity of the unknown representative): at `p̄ = (1, 1)`,
    `w̄ = 10`, a chain of twelve revealed preferences of the representative, `p_k = (1, 1 + k/100)`,
    ranks `x(p₁₂, w₁₂)` strictly below `x̄`, while optimal redistribution at `(p₁₂, w₁₂)` can give
    each consumer her utility at `x̄` (the Hicksian bundles cost `38/7 + 3164/625 < w₁₂`), so the
    representative's utility there is at least its utility at `x̄` (`exercise_4_D_10_normative`).

14. **Exercise 4.D.11 (p. 126).** The hint argues via an asymmetric Slutsky matrix, which would
    need the (unformalized) fact that a differentiable demand rationalized by an arbitrary
    rational preference has a symmetric Slutsky matrix. The proof here is finite: for an explicit
    three-good Hildenbrand economy (identical L-shaped preferences with a non-planar polygonal
    expansion path, wealth uniform on `[0, 2m]`), aggregate demand has a cycle of three strict
    revealed preferences, which no relation rational on `ℝ³_+` can rationalize
    (`exercise_4_D_11`).

15. **Exercise 4.D.4(a) (p. 125).** "Continuous" is proved on all of `ℝ^L_+` assuming only `W`
    and the `uᵢ` continuous (`exercise_4_D_4a_continuousOn`): distributions of `x` are `θᵢ ⊙ x`
    with `θ` in a fixed compact set, so `u` is the maximum of a jointly continuous function over a
    compact set. Concavity gives only continuity on `ℝ^L_{++}` (`exercise_4_D_4a_continuous`).
