# Corrections and departures

Departures from Mas-Colell, Whinston and Green, *Microeconomic Theory*, Chapter 14. Lean names
are relative to `MWG.PrincipalAgent`.

1. **Inconsistent assumptions on `g` (p. 489).** The book assumes `g(0, θ) = 0` for all `θ` and
   `g_θ(e, θ) < 0` "for all `e`". At `e = 0` the function `θ ↦ g(0, θ)` is constant, so
   `g_θ(0, θ) = 0`: the assumptions cannot hold together (`hi_g_theta_inconsistent`). The
   consistent version is `g_θ < 0` for `e > 0`. The formalization does not use `g_θ`: what is
   needed (`g(e, θ_H) < g(e, θ_L)` for `e > 0`) follows from `g_eθ < 0` and `g_e(0, θ) = 0`
   (`HIModel.hi_hyp`, `hi_cross_of_deriv`).

2. **The example of p. 500 (footnote 21).** The book illustrates `π'_H(t) ≥ π'_L(t) > 0` with
   `π_i(t) = θ_i(1 - μt)`, `μ > 0`. Then `π'_i = -θ_iμ < 0` and `π'_H < π'_L`
   (`footnote_21_misprint`). The intended example (Exercise 13.D.1) is `π_i(t) = θ_i(1 + μt)`,
   which satisfies the assumption (`footnote_21_corrected`) and tends to `θ_i` as `μ → 0`
   (`footnote_21_limit`).

3. **Welfare loss in Proposition 14.B.3 (p. 487).** "Whenever the optimal effort level with
   observable effort would be `e_H`, nonobservability causes a welfare loss" fails when `e_H` and
   `e_L` tie under observability: the observable-effort fixed wage for `e_L` is feasible with
   unobservable effort and attains the first-best payoff (`HAModel.ha_no_loss_of_tie`; concrete
   model `exTie`, `exA_tie`). The statement holds when `e_H` is strictly better under
   observability (`HAModel.ha_welfare_loss`, instance `exA_welfare_loss`).

4. **"`e_H` could always be induced" (Appendix A, p. 503).** With two efforts, incentives that
   are high enough at outcomes favouring `e_H` need not exist when the utility of income is
   bounded above. In `exC` (`v(w) = -exp(-w)`, strict first-order stochastic dominance,
   `g(e_H) = 1/2`, `ū = -1`) the observable-effort contract for `e_H` exists but no scheme
   satisfies the participation and incentive constraints (`aa_high_not_implementable`). Corrected
   statement: with strict first-order stochastic dominance and `v` unbounded above, `e_H` can be
   implemented (`HAModel.aa_high_implementable`).

5. **Exercise 14.AA.1 with "increasing" read strictly (p. 510).** The equivalence holds for
   nondecreasing functions (`exercise_14_AA_1`); the strict version of "only if" holds
   (`exercise_14_AA_1_strict`), but the strict version of "if" is false: for
   `f(π|e) = exp(e³π)` (times any normalizing factor) every ratio `f(π|e'')/f(π|e')` is strictly
   increasing in `π`, while `f_e/f = 3e²π` is constant at `e = 0`
   (`exercise_14_AA_1_strict_false`).

6. **Modelling of Section 14.B.** Profits have a density with respect to an arbitrary measure `ν`
   on `ℝ` (MWG: Lebesgue measure on `[π̲, π̄]`; the discrete version of footnote 6 is `dmeas`);
   densities are positive everywhere and compensation schemes are measurable with finite
   expected wage and utility (`HAModel.Adm`). Strict first-order stochastic dominance is used in
   the weaker form "strict at some `π`" (MWG: on an open set); the proof of Lemma 14.B.1 uses a
   set of positive measure where `f(π|e_L) > f(π|e_H)` (MWG: an open set). "Uniquely optimal"
   (Proposition 14.B.1) and the first-order conditions hold at almost every profit level
   (footnote 6). The Kuhn-Tucker conditions (14.B.10) are proved sufficient (footnote 7,
   `HAModel.ha_kt_sufficient`) and necessary (`HAModel.ha_kt_necessary`). For necessity MWG cite
   the finite-dimensional Kuhn-Tucker theorem of Section M.K; the program is posed over schemes,
   so the formalization uses the convex-like duality theorem `kt_convexlike` (separation in the
   finite-dimensional space of objective and constraint values) and derives the pointwise condition
   by changing the scheme on measurable sets (`HAModel.ha_ae_min`); the condition holds at almost
   every profit level. Slater's condition is not assumed: it is derived from feasibility and
   strict first-order stochastic dominance (`HAModel.ha_slater`). Lemma 14.B.1 is proved both for
   every scheme satisfying (ii_H) and (14.B.10) and, as stated, for every solution of (14.B.9)
   (`HAModel.lemma_14_B_1_every`).

7. **Finitely many profit levels in Exercises 14.B.5-14.B.6.** These exercises are formalized with
   finitely many profit (revenue) levels (MWG's footnote 6 discrete version), where the
   effective scheme under free disposal is a maximum over finitely many values. Exercise 14.B.4
   has two outcomes as printed.

8. **The revelation principle (Proposition 14.C.2, p. 493).** Formalized for any contract in
   which the manager makes a choice from an arbitrary set (`proposition_14_C_2`); outcomes are
   deterministic, as MWG restricts them (footnote 14).

9. **Forcing contracts (p. 502).** MWG's wage of `-∞` off the target profit is replaced by any
   finite penalty exceeding the disutility of the target effort (`hybrid_forcing`).

10. **Modelling of Section 14.C.** Effort lies in `[0, ∞)` and derivatives are taken within
    `[0, ∞)`; `π'' < 0` and `g_ee > 0` are used through the strict concavity of `π` and strict
    convexity of `g(·, θ)` they imply; `g_eθ < 0` through `g_e(e, θ_H) < g_e(e, θ_L)` for `e > 0`
    (`hi_cross_of_deriv` derives it). The full-information efforts `e*_i` are given as solutions of
    (14.C.7) (MWG presupposes they exist). The model allows state-dependent profits
    `π_H, π_L` with `π'_H ≥ π'_L > 0` (Exercise 14.C.5; MWG's model is `π_H = π_L`). With an
    infinitely risk-averse manager only `c = v⁻¹(ū)` enters (`Screen`). The general program
    `Screen` needs only that `D(e) = g(e, θ_L) - g(e, θ_H)` vanishes at `0` and is strictly
    increasing, which also covers (14.C.10).

11. **Footnote 15 (p. 494).** The transformation `-v^ρ` requires the utility levels `v_H, v_L` to be
    positive; this is assumed. The limit is Chapter 3's Exercise 3.C.6(c), imported.

12. **Exercise 14.B.4(d).** "As `x` approaches 1" is formalized for `x ∈ [99/100, 1)`: there the
    unobservable optimum implements `e₁` while the observable optimum implements `e₂` (for every
    `x ∈ (0, 1)`).

13. **Exercise 14.C.7.** Part (a) is formalized through two sufficient conditions (`θ_L > (θ_H + c)/2`;
    `λ(θ_L - c)²/θ_L > (1 - λ)(θ_H - c)²/θ_H`, which holds for `λ` near `1`); part (c) through the
    case in which profit is concave in the unit price.

14. **Exercise 14.C.3.** The ordering `e_L < e_H` of the full-information efforts is derived from
    the first-order conditions (`exercise_14_C_3b_order`), which are shown sufficient
    (`exercise_14_C_3a_suff`) and, at interior efforts with `π` and `g(·, θ)` differentiable there,
    necessary (`exercise_14_C_3a_necessary`).

15. **(14.AA.3), necessity (p. 504).** The relaxed program has an equality constraint
    `∫ v(w) f_e = g'(e)`; its multiplier `μ` has no sign restriction. Necessity is proved
    (`HAModel.foa_necessary`, via `kt_convexlike_eq`) under the qualification that `f_e(·|e)` is
    positive on a set of positive measure and negative on another (true for the derivative of a
    non-constant family of densities, since `∫ f_e = 0`), with `f_e` measurable and `v(w) f_e`
    integrable for admissible schemes (as for `foa_sufficient`).

16. **Exercise 14.B.7 (two periods).** Formalized with finitely many profit levels (footnote 6);
    the manager's plans choose period-2 effort after observing `π₁`; the reservation utility is for
    the two periods together; `v'' < 0` is used as strict concavity with `v` differentiable. The
    answer "yes" is proved in the equivalent form "no feasible contract whose period-2 wages do not
    depend on period-1 profits is optimal: a strictly cheaper feasible contract exists"
    (`exercise_14_B_7`), through the inverse Euler condition (`b7_improve`); the existence of an
    optimal contract is not asserted.

17. **Exercise 14.B.8 (costly investigation).** Formalized with finitely many profit levels and
    signal values; investigation is chosen with probability `p(π)` after observing `π`. The
    program is not convex in `(p, w)`, but it is convex in the perspective variables
    `((1 - p) v(w(π)), p, p v(w(π, y)))` (`b8_persp`), so the Kuhn-Tucker conditions are necessary;
    the characterization (`exercise_14_B_8`) is stated through the pointwise Lagrangians `A_π`
    (no investigation) and `B_π` (investigation, including its cost). Slater's condition is
    derived from feasibility and `f(π|e_L) < f(π|e_H)` at some `π`.

18. **Exercise 14.C.4 (finite risk aversion).** MWG give no model; the formalization uses the
    model of pp. 489-490 with an ex ante participation constraint in expected utility and the
    self-selection constraints of (14.C.8), a single profit function `π`, given unique first-best
    efforts `e*_L ≤ e*_H` and `D(e) = g(e, θ_L) - g(e, θ_H)` strictly increasing on `[0, ∞)`
    (`g_eθ < 0`). `e_L ≤ e*_L` holds in general (`exercise_14_C_4`); the strict distortion
    `e_L < e*_L` uses differentiability at `e*_L > 0` and `D'(e*_L) > 0`
    (`exercise_14_C_4_strict`).

19. **Exercise 14.C.1 (`N` states).** States are indexed by `ℕ` with the constraints imposed on
    `0, …, N-1`; single crossing is assumed for every pair `i < j`; the first-best efforts `e*_i`
    are given as unique maximizers of `π - g(·, θ_i)` on `[0, ∞)` and nondecreasing (strictly
    increasing for the strict distortion `exercise_14_C_1_strict`, which also uses
    differentiability at `e*_k > 0` and `D_k'(e*_k) > 0`). The optimal efforts maximize the virtual
    surplus among nondecreasing profiles (`exercise_14_C_1_opt`); the converse is
    `exercise_14_C_1_suff`.

20. **Exercise 14.C.9(b), necessity.** The full program has both participation and both
    self-selection constraints. The shape of every optimum (`exercise_14_C_9b_necessary`) uses
    `φ = u⁻¹` differentiable with `φ'` positive and strictly increasing (`u` strictly increasing and
    strictly concave), `0 < θ_L < θ_H < 1`, and `r_H < r_L`, which holds for the no-insurance
    reservation levels (`c9_r_order`).

21. **Exercise 14.B.6(b).** Formalized with finitely many revenue and cost levels (as in item 7).
    The answer is that the optimal scheme does not depend on revenue: every scheme nondecreasing in
    revenue (all that revenue reduction allows) is weakly dominated by one depending on costs only,
    strictly so under strict risk aversion if it depends on revenue at a cost level of positive
    probability (`exercise_14_B_6b_opt`); the scheme then solves the problem of part (a) with
    revenues ignored.

22. **Instance of Exercise 14.B.2's necessity theorem.** The exercise asks for a strictly
    risk-averse owner; the necessity theorem assumes only that the owner's utility is concave,
    nondecreasing and differentiable, and its proved instance (`inst_14_B_2_necessary`) uses the
    risk-neutral owner `U(y) = y` of Figure 14.B.1.
