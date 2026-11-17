# Corrections

Departures from the printed text of MWG Chapter 5 and Section M.M, checked against the page
images.

1. **Property (vii), p. 132.** "Nonincreasing returns to scale imply that inaction is possible"
   needs `Y` nonempty (property (i)): `∅` has nonincreasing returns. Proved:
   `inaction_of_nonincreasingReturns`; counterexample `nonincreasingReturns_empty`.
2. **Condition (5.C.1), p. 136.** `p = λ∇F(y*)` needs a constraint qualification
   `∇F(y*) ≠ 0`. For the transformation function `F(y) = (y₁ + y₂)³` of `{y₁ + y₂ ≤ 0}`,
   `∇F(0) = 0` and `0 ∈ y(1, 1)` (`foc_5_C_1_needs_cq`). Proved with the qualification:
   `foc_5_C_1`.
3. **Proposition 5.C.1(iii), p. 138, and Exercise 5.E.3, p. 163.** False with prices `p ≫ 0`:
   `Y = {y ∈ ℝ² : y₂ ≤ 0}` is nonempty, closed, convex and has free disposal, but `π(p) = +∞` for
   all `p ≫ 0` (`proposition_5_C_1_iii_counterexample`, `exercise_5_E_3_counterexample`). True
   with all `p ≥ 0` (`proposition_5_C_1_iii_nonneg`, `exercise_5_E_3`) and with `p ≫ 0` when
   profits are bounded at some `p₀ ≫ 0` (`proposition_5_C_1_iii`, `exercise_5_E_3_pos`).
4. **Proposition 5.C.1(vi), Hotelling's lemma, p. 138.** Needs `Y` convex (as its proof via
   Proposition 3.F.1 does): `Y = ℝ²_- ∪ {y₁ + y₂ ≤ -1}` is closed with free disposal,
   `y(1, 1) = {0}`, yet `π(1 + δ, 1) = +∞` for all `δ > 0`
   (`proposition_5_C_1_vi_nonconvex_counterexample`). Proved for closed convex `Y`:
   `proposition_5_C_1_vi`. Part (vii) does not need convexity: for any `Y`, the derivative at
   `p̄` of any supply selection differentiable at `p̄` is symmetric (`proposition_5_C_1_vii_symm`,
   by cyclic monotonicity, `supply_cyclic`, `deriv_cyclic`, `cyclic_symm`), positive
   semidefinite and has `Dy(p̄)p̄ = 0` (`proposition_5_C_1_vii_psd`, `proposition_5_C_1_vii_euler`);
   for closed `Y` with `y(·)` single-valued near `p̄`, `y(·)` is continuous near `p̄`
   (`supply_continuousAt_of_single`), so Hotelling's lemma holds near `p̄`
   (`hotelling_of_continuousAt`) and `D²π(p̄) = Dy(p̄)` (`proposition_5_C_1_vii_general`; instance
   on the nonconvex `ssY`: `proposition_5_C_1_vii_general_instance`). Free disposal is never
   used. For closed convex `Y`: `proposition_5_C_1_vii`. By contrast Shephard's lemma,
   Proposition 5.C.2(vi), holds without convexity (`vcost_shephard`).
5. **Condition (5.C.4), p. 140.** Needs a constraint qualification: for `f(z) = (z - 1)³ + 1`,
   `w = q = 1`, `z* = 1` solves the CMP but no `λ` satisfies (5.C.4) (`foc_5_C_4_needs_cq`).
   Proved with a qualification: `foc_5_C_4`. The sufficiency claim of footnote 8 needs the
   complementary slackness `λ(f(z*) - q) = 0`, which (5.C.4) leaves implicit
   (`foc_5_C_4_sufficient`).
6. **Example 5.C.1, p. 142.** The output supply for `α + β < 1` is
   `q = [(α+β)p/θφ(w)]^{(α+β)/(1-α-β)}`, not `(α+β)[p/θφ(w)]^{(α+β)/(1-α-β)}`
   (`example_5_C_1_supply`; for `α + β = 1/3`, `θφ = p = 1` the printed value `1/3` violates
   (5.C.7) and is not optimal: `example_5_C_1_printed_supply_counterexample`).
7. **Example 5.C.1, p. 143.** With increasing returns doubling output multiplies costs by
   `2^{1/(α+β)} < 2`, not `> 2` (`example_5_C_1_doubling`).
8. **Section 5.D, p. 146.** "`p = C_v'(q)` implies `pq > C_v(q)`" needs strict convexity; for
   convex `C_v` with `C_v(0) = 0` only `pq ≥ C_v(q)` holds (`sunk_cost_covers_variable`;
   `sunk_cost_strict_fails` for `C_v(q) = q`).
9. **Proposition 5.F.2, p. 151.** Needs `L ≥ 1` (in `ℝ⁰` no `p ≠ 0` exists):
   `proposition_5_F_2_needs_dimension`. The caption of Figure 5.F.4 says "Proposition 5.C.2";
   it refers to Proposition 5.F.2.
10. **Exercise 5.G.1(c), p. 164.** With identical preferences and shares the owners agree
    (`exercise_5_G_1c`), but on maximizing their common welfare `v(p(z)) + θπ(z)`, which is not
    profit maximization in general: for one owner with utility `2√x - z` and `f(z) = z`, welfare
    is maximized at `z = 1` and profit at `z = 1/4` (`exercise_5_G_1c_not_profit`).
11. **Theorem M.M.1, proof, p. 968.** The proof states `Aᵀλ̄ = f`; with the constraints `x ≥ 0`
    only `Aᵀλ̄ ≥ f` with `(Aᵀλ̄ - f)·x̄ = 0` holds (`equation_M_M_4`). For `max -x` s.t. `x ≤ 1`,
    `x ≥ 0`, no `λ ≥ 0` has `Aᵀλ = f` (`theorem_M_M_1_proof_counterexample`). The theorem itself
    is proved (`theorem_M_M_1`) via Farkas' lemma.
12. **Exercise 5.C.7, p. 161.** False with `∂²f/∂z_ℓ∂z_k < 0`: for the negative definite Hessian
    `[[-3/4, -1/4], [-1/4, -3/4]]` (of `-e^{-z₁} - e^{-z₂} - e^{-z₁-z₂}` at `(ln 2, ln 2)`) and
    `p = 1`, the first-order conditions force `∂z₁/∂w₂ = 1/2 > 0`
    (`exercise_5_C_7_counterexample`). With `∂²f/∂z₁∂z₂ > 0` (two inputs) the claims hold
    (`exercise_5_C_7_corrected`), and for `n` inputs with all cross partials positive every
    `∂z_ℓ/∂w_k < 0` and `∂z_ℓ/∂p > 0` when `∇f ≥ 0`, `∇f ≠ 0` (`exercise_5_C_7_corrected_n`: `-D²f`
    is a nonsingular M-matrix with a strictly positive inverse). The counterexample is realized by
    an explicit demand function: for `f(z) = -e^{-z₁} - e^{-z₂} - e^{-z₁-z₂}` the unique
    profit-maximizing demand is `c7demand` (closed form with a square root and logarithms,
    `exercise_5_C_7_demand`), equal to `(ln 2, ln 2)` at `p = 1`, `w = (3/4, 3/4)`, where
    `∂z₁/∂w₂ = 1/2 > 0` (`exercise_5_C_7_explicit_counterexample`). The demand maximizes profit
    over `z ∈ ℝ²`; it is `≫ 0` near that price, so it also maximizes over `ℝ²_+` there.
13. **Exercise 5.AA.5(d), p. 166.** The direct comparisons `a₂/a₄`, `a₁/a₅`, `a₆/a₇` show `a₄`,
    `a₅`, `a₆` inefficient (`exercise_5_AA_5d`), but comparing `a₃` with `a₈` shows nothing: both
    are efficient (`exercise_5_AA_5d_correction`). The inefficient activities are `a₁`, `a₂`,
    `a₄`, `a₅`, `a₆` (with (e), `exercise_5_AA_5e`).
14. **Proposition 5.B.2, p. 134.** The hypothesis `0 ∈ Y` is not used
    (`proposition_5_B_2_general`). Not an error; the generalization is recorded.
15. **Exercise 5.D.4(a), p. 163, and Proposition 5.AA.2, p. 159.** Subadditivity is stated for
    `J ≥ 1` firms and `C(0) ≥ 0`; the nonsubstitution theorem is proved without the hypothesis
    that the model is productive (the conclusion is vacuous otherwise).
16. **Exercise 5.D.3, p. 162.** The long-run supply response is at least the short-run one
    (`exercise_5_D_3`), not strictly larger in general: when fixing input 1 does not raise
    costs (`c_s = c`), the responses are equal (`exercise_5_D_3_equal`; a strict instance is
    `exercise_5_D_3_instance`). The proof assumes, as the book's differential argument does,
    that the supply functions are continuous near `p̄` and differentiable at `p̄`; strict
    convexity of `c` is not used.
17. **Exercise 5.D.4(b)-(c), p. 163.** Decreasing ray average cost "`C(q) > C(kq)/k` for any
    `q ∈ ℝ^M_+`" fails at `q = 0` whenever `C(0) = 0`, as (c) assumes; it is required for
    `q ≠ 0` (`DecreasingRayAC`). In (c) continuity is not needed (`exercise_5_D_4c` assumes `C`
    nondecreasing, `C(0) = 0`, quasiconvex, decreasing ray average cost).
18. **Exercise 5.B.4, p. 160.** The claim that `Y⁺` is closed for Figure 5.B.5(b) is proved
    under a precise hypothesis read from the figure: increasing returns at small scale, in the
    form that two plans each using less than some `δ > 0` of the input can be merged into one
    (`exercise_5_B_4_closed`, with closedness, inputs `y₁ ≤ 0` and output bounded for bounded
    input). Instance: `{y₁ ≤ 0, y₂ ≤ min(y₁², 1)}` (`exercise_5_B_4_closed_instance`).
19. **Exercise 5.E.4, pp. 163-164.** The integrals over the square `[0, 10]²` are written as
    iterated interval integrals (`e4AggProfit`, `e4AggDemand`); the aggregate demand for `z₂` is
    the iterated integral with `z₂` outer. Technologies with `w·z = 1` (a null set) are taken
    to produce nothing. The formulas of (b)-(c) are proved for `w₁, w₂ ≥ 1/10`, as the book
    states.
