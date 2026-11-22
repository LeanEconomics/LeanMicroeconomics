# Corrections and departures

Mas-Colell, Whinston and Green, *Microeconomic Theory*, Chapter 20 and Section M.N. Lean names
are relative to `MWG.EquilibriumTime`.

1. **Positive discount factor (comment (1), comment (2), Exercises 20.B.1-20.B.2, pp. 733-734).**
   MWG only require `δ < 1`. With `δ = 0` time impatience fails (`(0, 1, 0, ...)` and its
   forward shift are indifferent) and stationarity fails. Counterexamples:
   `impatience_fails_at_zero_discount`, `stationarity_fails_at_zero_discount`; the exercises are
   proved for `0 < δ < 1` (`exercise_20_B_1`, `exercise_20_B_2_stationary`).

2. **Recursive utility (aside after (20.B.3), p. 736).** For `G(u, V) = u^α + δ V^α` the
   continuation value `V(c^T)` cannot be given an arbitrary value: for the zero stream both
   `V ≡ 0` and `V ≡ δ^{1/(1-α)}` solve the aggregator equation, and the truncations with
   continuation value `δ^{1/(1-α)}` never move (`recursive_aggregator_two_solutions`).
   Exercise 20.B.4 holds as its hint states (truncations with continuation value `0`):
   `exercise_20_B_4_bounded`, `exercise_20_B_4_limit`, `exercise_20_B_4_aggregator`.

3. **Definition 20.D.1 (p. 744).** Prices are required to be nonnegative and the wealth series
   `∑_t (π_t + p_t · ω_t)` to converge (MWG derive finiteness of wealth from monotonicity). The
   same convention is used in Definition 20.G.1 (`WalrasEq`, `WalrasEqI`).

4. **Example 20.D.1(iii) (p. 747) is false for a general technology.** The claim that a constant
   fraction `δ` of wealth is invested, `k_{t+1} = δ F(k_t)`, relies on
   `∑_{t ≥ T+1} p_t c_t = p_{T+1} F(k_T)`, which fails when future profits are positive. For
   `F(k) = k^α` the first-order conditions and `k_{t+1} = δ F(k_t)` force `α = 1`
   (`example_20_D_1_iii_false`); the correct rule is `k_{t+1} = αδ F(k_t)`, which satisfies the
   Euler equation (`example_20_D_1_iii_corrected`). Part (ii) (linear technology, zero profits)
   is correct and is a full Walrasian equilibrium (`example_20_D_1_ii`).

5. **(20.D.11) (p. 753) is off by the factor `δ`.** For the value `V₈` of the objective (20.D.8)
   as printed, `∑_{t ≥ 1} δ^t u(k_{t-1}, k_t)`, the Bellman equation reads
   `V₈(k) = δ max [u(k, k') + V₈(k')]`, not `V₈(k) = max u(k, k') + δ V₈(k')`; with `u ≡ 1`,
   `V₈ = δ/(1 - δ) ≠ 1 + δ V₈` (`bellman_20_D_11_printed_false`). The chapter uses
   `W(k) = ∑_{t ≥ 0} δ^t u(k_t, k_{t+1}) = V₈/δ` (`objective_20_D_8`), for which (20.D.11) and
   (20.D.12) hold as printed (`bellman_20_D_11`, `exercise_20_D_8_ii`).

6. **Example 20.D.4 (p. 753).** "If we try `k₁ ≥ k₀`, the path is feasible" holds only for
   `k₀ ≤ k₁ < 2k₀`; for `k₁ ≥ 2k₀` consumption `2k₀ - k₁` is not positive
   (`example_20_D_4_infeasible`).

7. **Proposition 20.D.5 (p. 749).** Proved under a uniform bound on all feasible production paths
   (MWG's alternative on p. 744) rather than only on the consumption streams they generate
   (`proposition_20_D_5`).

8. **Proposition 20.D.7 (p. 751).** Proved against bounded competitors (all paths are bounded in
   MWG from p. 744, and the printed proof assumes it), for finite-dimensional `K`
   (`proposition_20_D_7`). The proof is by the gradient inequality and a telescoping sum
   instead of MWG's splicing argument.

9. **Exercise 20.D.8(i) (p. 784).** Concavity of the value function is proved with `u` bounded
   above on `A` (to keep objectives summable) (`exercise_20_D_8_i`).

10. **The bound on `|ψ'(k)|` (p. 762) has the wrong direction.** From `∇²₂₂u ≤ 0` and
    `δ∇²₁₁u ≤ δV'' ≤ 0` it follows that `|ψ'| ≥ |∇²₂₁u / (∇²₂₂u + δ∇²₁₁u)|` (and
    `|ψ'| ≤ |∇²₂₁u / ∇²₂₂u|`), not `≤` (`policy_deriv_lower_bound`). Counterexample to the printed
    inequality: `∇²₂₁u = 1`, `∇²₂₂u = -1`, `∇²₁₁u = -4`, `V'' = 0`, `δ = 1/2` give `ψ' = 1` against
    the bound `1/3` (`policy_deriv_bound_printed_false`). The text's conclusion is presented as
    "plausible" and is not used elsewhere.

11. **Exercise 20.F.2 (p. 785) is false on `ℝ_{++}`.** `ψ(k) = k/2` is a contraction of `(0, ∞)`
    with no steady state (`exercise_20_F_2_false`). On `ℝ_+` the claim holds (unique steady state,
    global stability: `exercise_20_F_2`).

12. **Golden rule efficiency (p. 756).** Proved for `f = F(·, 1)` strictly concave with
    `f'(k̂) = 1` and output strictly increasing in labor at `k̂` (otherwise a path saving labor
    could dominate) (`golden_rule_efficient`, `golden_rule_capital`).

13. **Example 20.C.6, (20.C.1)-(20.C.2) (p. 741).** Sufficiency of (20.C.1)-(20.C.2) for efficiency
    uses strictly positive wages, i.e. a positive marginal product of labor, to apply
    Proposition 20.C.1 with `p ≫ 0` (`efficient_of_20_C_1_20_C_2`). Example 20.C.1's technology is
    shown to satisfy (i)-(iv) for `F` continuous, concave, nondecreasing with `F(0) = 0`
    (`example_20_C_1`).

14. **Exercise 20.C.4 (p. 783).** "For any other production path" is read as "for any path whose
    profit series converges"; Exercise 20.C.4(a) then uses truncation, assumption (iv)
    (`OverallProfitMax`, `exercise_20_C_4a`).

15. **Propositions 20.E.1-20.E.2 (pp. 754-755)** are proved in the smooth case that MWG treat
    (`SmoothAt`); the inefficiency half of Proposition 20.E.2 also assumes `Y` has nonempty
    interior, which makes the "below the tangent hyperplane" test exact
    (`exists_mem_of_smooth_neg`). The nonsmooth case of Proposition 20.E.1 is OPEN.

16. **Definition 20.H.1 (p. 771).** Prices are required to be positive, and for a real asset
    (`ε > 0`) the value `∑ p_t` finite (MWG argue it must be, p. 773) (`OLGEq`).

17. **The monetary steady state (p. 774).** Generation 0 consumes `(1, 1 - γ)`, and its
    optimality fixes `p₁/p₀` by its marginal rate of substitution at `(1, 1 - γ)`; the price
    sequence is constant only from `t = 1`. With `u = ln c_b + ln c_a` (`γ = 1/2`) generation 0's
    optimality forces `p₁ = 2p₀` (`monetary_steady_state_prices_log`). The same remark applies to
    "`p_t = α^t`" in Figure 20.H.1.

18. **Proposition 20.G.2 and Exercise 20.G.1.** Proposition 20.G.2 is proved for interior
    equilibria with differentiable, concave, strictly increasing utilities (MWG give only an
    intuitive argument); the representative utility is
    `u(c) = sup {∑ η_i u_i(c_i) : ∑ c_i ≤ c, c_i ≥ 0}` (`proposition_20_G_2`). Exercise 20.G.1 is
    proved from the equilibrium first-order conditions and binding budgets, which are
    established for interior equilibria by Exercise 20.D.3 and `budget_binds`
    (`exercise_20_G_1`).

19. **Footnote 32 and Exercise 20.G.4 (pp. 768, 786).** Both directions are proved for interior
    consumption with differentiable utilities (MWG give no proof). The repetition of a static
    equilibrium is an intertemporal equilibrium for concave utilities with `p̄ ≫ 0` and
    `∂_0 u_i > 0` (`exercise_20_G_4_repetition`). The converse ("the intertemporal equilibria
    correspond exactly to the repetitions") uses strict concavity, the first-order conditions
    (20.D.6) of Exercise 20.D.3 and binding budgets (`exercise_20_G_4_static`): with merely
    concave (e.g. linear) utilities, consumption need not be constant over time.

20. **Optimality of the monetary steady state (p. 774, Figure 20.H.3).** MWG give no rigorous
    proof. It is proved for `u` continuous on `ℝ²_+`, nondecreasing in `c_b`, strictly increasing
    in `c_a`, with `(γ, 1 - γ)` the unique maximizer of `u` on `{b + a ≤ 1}` (the steady-state
    equilibrium condition plus strict quasiconcavity) (`monetary_steady_state_optimal`).

21. **Figures 20.H.5-20.H.6 (p. 777).** The cycles are constructed in the purely nominal case
    (`ε = 0`, bubble `M > 0`) rather than in the real-asset case drawn in the figures, with
    concave, increasing, piecewise linear utilities (so the offer curves have kinks)
    (`figure_20_H_5_period_two`, `figure_20_H_6_period_three`).

22. **Exercise 20.B.5, uniqueness (p. 783).** "The additively separable form is a cardinal
    property" is proved for one good, two additive utilities with the same discount factor
    `0 < δ < 1`, continuous one-period utilities on `ℝ_+` and `u` strictly increasing: if they
    rank nonnegative bounded streams alike then `w = α u + β` with `α > 0`
    (`exercise_20_B_5_unique`).

23. **Global tâtonnement stability (p. 778).** Proved for an excess demand defined and
    differentiable on all of `ℝ^L` with negative definite derivative everywhere and for
    trajectories of `dp/dt = z(p)` defined for all real `t` (`tatonnement_global_stable_negDef`);
    the general form only needs continuity and `(p - p*) · z(p) < 0` for `p ≠ p*`
    (`tatonnement_global_stable`). MWG's short-run demands live on positive prices; keeping the
    trajectory in that domain is not addressed.

24. **Optimal nominal equilibria and the bubble (p. 774).** MWG leave the claim without proof.
    It is proved for the stationary economy `u(b, a) = √b + √a` with a purely nominal asset
    (`olg_sqrt_optimal_iff_bubble`), where every equilibrium is either the monetary steady state
    or has a vanishing real bubble and is Pareto dominated by the steady state. For general
    utilities it remains OPEN.

25. **Golden rule efficiency in the multisector model (p. 758).** MWG assert it ("we could also
    prove"). It is proved for bounded capital paths when `G` lies below its zero-interest tangent
    plane at `(k̂, k̂)` by a quadratic margin in the current capital stock
    (`golden_rule_multisector_efficient`). Concavity alone does not suffice: for the linear
    `G(k, k') = k - k'` the golden rule is inefficient (`golden_rule_linear_inefficient`).

