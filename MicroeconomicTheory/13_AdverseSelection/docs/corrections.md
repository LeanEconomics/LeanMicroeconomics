# Corrections and departures

Departures from Mas-Colell, Whinston and Green, *Microeconomic Theory*, Chapter 13. Lean names
are relative to `MWG.AdverseSelection`.

1. **Constant `r` with an atom (p. 440).** The book says that with `r(θ) = r` and
   `F(r) ∈ (0, 1)` the competitive equilibrium is not Pareto optimal. This needs `F` atomless
   at `r`: with types `1` and `2` equally likely and `r = 1`, `F(r) = 1/2`, `W* = {3/2}`, every
   worker is employed and aggregate surplus is maximal (`const_atom_counterexample`, measure
   `atomMeas`). Proved under no atoms: `const_inefficient`.

2. **Proposition 13.B.1(i) needs `r` continuous (pp. 443-444).** The proposition assumes `r`
   strictly increasing and a positive density. The proof's deviation to a wage just below `w*`
   is profitable only if that wage attracts workers with positive probability. Counterexample
   `counterexample_13_B_1_i`: types uniform on `[1, 2]`, `r(1) = 0` and `r(θ) = θ` for `θ > 1`
   (`jumpR`). Every printed hypothesis holds, with `W* = {1}`, `w* = 1 > r(θ̲) = 0` and
   `E[θ | r(θ) ≤ w'] = 1 > w'` on `(0, 1)`. Yet both firms offering `1/2` is a pure SPNE, so
   the SPNE is not unique. Corrected statement: `proposition_13_B_1_i`, with `r` continuous on
   `[θ̲, θ̄]` (field `cont` of `RegularModel`). Part (ii), `exists_isGreatest_eqWages` and
   Proposition 13.B.2 are also proved under continuity.

3. **Conditional expectation of a null set (pp. 439-442).** `E[θ | Θ*]` is undefined when `Θ*`
   has probability zero but is nonempty. Figure 13.B.2 and Example 13.B.1 nevertheless use
   `E[θ | r(θ) ≤ r(θ̲)] = θ̲`, the limit value (p. 441). `condMean` takes `θ̲` for null sets
   meeting `[θ̲, θ̄]` and `E[θ]` for sets missing it, which is the book's `Θ* = ∅` convention.
   Wages are compared through the profit `∫_{Θ(w)} (θ - w) dF`, which needs no convention
   (`firmProfit`, `firmProfit_eq`).

4. **Measurability.** `r` is assumed measurable wherever integrals over `Θ(w)` are taken
   (`RegularModel.meas`, `aggSurplus_le_opt`). The book does not state this.

5. **The signaling and screening games are bespoke (Sections 13.C, 13.D, Appendix A).**
   Education, task levels and wages are continuous choices, so the games are not Chapter 9's
   finite extensive forms. We use the book's own equivalent PBE conditions (p. 452, p. 468):
   `SigModel.IsPBE` and `SignalingGame.IsPBE`. In both, condition (iii) is a Nash equilibrium
   of a Chapter 8 normal form game (`wageGame`, `responseGame`). The screening SPNE
   (`IsScreenEq`) takes the book's stage-2 tie-breaking rules as given worker behaviour. Only
   pure strategies are considered, as in the book.

6. **Cost function (Section 13.C).** Of the book's assumptions on `c(e, θ)` we use
   `c(0, θ) = 0`, `c(·, θ)` strictly increasing and continuous, and single crossing in
   integrated form (`SigModel.Valid`). `c_θ < 0` follows (`Valid.c_lt_of_pos`). Convexity is
   not used. The signaling results are proved for any home earnings `0 ≤ r < θ_H`, which covers
   both the main text (`r = 0`) and the small type on p. 459.

7. **Existence of the cutoffs `ẽ`, `e₁`, `e'`, `t̂_H`.** The book reads these off figures. We
   take them as given solutions of their defining equations, or state the results with the
   equations directly (`separating_iff`, `pooling_iff`). For `education_IC_unique` we assume
   `c(·, θ_L)` unbounded, so that the low type's indifference curves reach `θ_H`.

8. **Dominance with `Min`/`Max` (Appendix A).** "`Min_{s'} u₁(a', s', θ) > Max_s u₁(a, s, θ)`"
   is read as "every payoff from `a'` exceeds every payoff from `a`". The two readings agree
   when the extrema exist, as the book presupposes (`DominatedFor`). In (13.AA.4), when
   `Θ**(a) = ∅` we use all beliefs (`icTypes`), matching the convention for reasonable beliefs.

9. **Two-type equivalence (p. 472).** The book says that with two types the intuitive
   criterion and reasonable beliefs are equivalent. As a statement about PBEs this is too
   strong. A PBE can pass the intuitive criterion while keeping an unreasonable off-path belief
   that no type would act on. We prove the outcome form: with `Θ**(a) = {b}`, imposing the only
   admissible belief together with a suitable equilibrium response leaves a PBE with the same
   outcome (`two_types_reasonable`), and that belief is unique (`two_types_singleton`).

10. **Example 13.AA.1.** The book describes the types' preferences only through beliefs over
    `{θ₂, θ₃}`. Our concrete game (`exGame`) has these preferences, with the book's weak
    inequalities (`μ(θ₂|â) ≥ 1/4`, `≤ 3/4`). The supporting PBE puts weight on `θ₁` after `â`.

11. **Exercise 13.C.3.** With linear indifference curves for both types (the exercise's hint),
    a cross-subsidy improves on the best separating equilibrium exactly when banning signaling
    does: all payoffs are linear in the subsidy. The example (`crossModel`) keeps the low type's
    cost linear and makes the high type's strictly convex.

12. **Exercise 13.B.10.** Proposition 13.B.2 is proved without `r(θ) ≤ θ`
    (`MonoModel.isConstrainedPO`), which is the exercise. The budget constraint is written as
    an inequality; footnote 15 shows that a surplus is never optimal.

13. **Welfare of screening equilibria (p. 466, footnote 25).** The book says that when an
    equilibrium exists it is a constrained Pareto optimum, and that screening must make the
    high type better off. What holds: if an SPNE exists, no incentive compatible allocation
    gives both types strictly more at a strictly positive expected profit
    (`screening_no_strict_improvement`), and the high type gets at least `E[θ]`
    (`screening_high_better`). Both stronger readings fail: in `linModel` (`θ_L = 1`,
    `θ_H = 2`, `λ = 1/2`, `c(t, θ_L) = t`, `c(t, θ_H) = t/2`) an SPNE exists, the high type gets
    exactly `E[θ] = 3/2`, and the pooling allocation `(3/2, 0)` is budget balanced, gives the
    low type `3/2 > 1` and the high type `3/2`: a constrained Pareto improvement
    (`footnote_25_counterexample`). This is a weak-improvement version of the gap the book
    concedes in footnote 25.

14. **Exercise 13.B.1, arbitrary `r`.** The book reads equilibria off the diagram with `r`
    "otherwise quite arbitrary". A crossing `r(θ̂) = E[θ | θ ≤ θ̂]` is an equilibrium exactly
    when the types in `[θ̲, θ̄]` accepting `r(θ̂)` are `[θ̲, θ̂]` (`exercise_13_B_1_cutoff`); this
    holds for increasing `r`, where `exercise_13_B_1` characterizes `W*`. Counterexample for
    non-monotone `r`: types uniform on `[0, 2]`, `r(θ) = 1 - θ`, `θ̂ = 2/3`: `r(θ̂) = 1/3 =
    E[θ | θ ≤ 2/3]` but `1/3 ∉ W*` (`exercise_13_B_1_nonmono`). Exercise 13.B.3(b) is proved as
    printed (`r(θ) > θ`, `exercise_13_B_3b`); the reading `r(θ) < θ` is also proved
    (`exercise_13_B_3b_lt`).

15. **Exercise 13.B.3(c) needs `θ̂ > θ̲`.** With `θ̂ = θ̲` (allowed by "there exists a `θ̂`")
    types uniform on `[1, 2]` and `r(θ) = 2 - θ` give the equilibrium `w* = 3/2` employing
    everybody, which is the Pareto optimum (`exercise_13_B_3c_counterexample`). Proved with
    `θ̂ ∈ (θ̲, θ̄)`: `exercise_13_B_3c`.

16. **Exercise 13.B.7.** The increase statement (`exercise_13_B_7_increase`) assumes the level
    sets `{r = c}` are null, true in the model of Section 13.B (`MonoModel.levelNull`); the
    reduction statement (`exercise_13_B_7_reduce`) needs only measurable `r`. "Reduces
    (increases) employment" means the employed set in `[θ̲, θ̄]` is a strict subset
    (superset) of the equilibrium set, and the right-hand sides include it.

17. **Exercise 13.B.6, modelling.** The `N` firms are a continuum of mass `N`; `g` is
    continuous, positive and integrates to 1 (`FirmDensity`); for (c)-(d) `θ̲ > 0`, `r`
    measurable and nondecreasing with `r(θ̲) ≥ 0` (`WilsonEconomy.Valid`). In (b) "strictly
    increasing at `w̃`" is read as `z*'(w̃) > 0` (`exercise_13_B_6b`).

18. **Exercise 13.B.6(d)(ii).** The book says the highest-wage equilibrium `w*` is an SPNE iff
    `z*(w) ≤ z*(w*)` for all `w > w*`. In the wage-offer game (`WilsonEconomy.IsSPNE`: firms
    offer wages or stay out, workers take the highest acceptable offer with random rationing)
    "only if" holds (`WilsonEconomy.exercise_13_B_6d_ii_necessary`) but "if" fails: high-`γ`
    firms deviate upward whenever `μ(w) > μ(w*)`. Counterexample
    `exercise_13_B_6d_ii_counterexample` (`stepEconomy 1 3`: types uniform on `[1, 2]`,
    `r = 0` for `θ ≤ 3/2` and `3` above, `g = e^{-γ}`). Corrected: a CE `w*` is an SPNE iff
    `μ(w) ≤ μ(w*)` for all `w > w*` (`WilsonEconomy.exercise_13_B_6d_ii_corrected`). Part
    (d)(i) is proved over common-wage, market-clearing outcomes.

19. **Exercise 13.B.8 is false in the model of p. 446.** With interventions consisting of an
    employment wage `w_e` and a benefit `b(x)` conditioned on the observed purchase `x(θ)` of a
    worker at home, and Pareto improvements requiring strict gains on a set of positive
    probability, no Pareto-improving intervention exists at the highest-wage equilibrium when
    `r` is strictly increasing, continuous, `r(θ) ≤ θ` with positive density, for any `x` and
    `b` (`exercise_13_B_8_false`). Corrected (`exercise_13_B_8`): with `x` injective and a
    positive mass of employed types with `r(θ) > θ` (the setting of Exercise 13.B.10), paying
    exactly those types `w* - θ` to stay home is a budget-neutral Pareto improvement; instance
    `exercise_13_B_8_instance`, where the equilibrium is constrained optimal for
    `(w_e, w_u)` schemes. A constant `x` does not help (`exercise_13_B_8_const_x`).

20. **Exercise 13.C.1.** "All worker types submit to the test" holds for every `θ > θ̲`; the
    non-tester wage is exactly `θ̲`, and `θ̲` is indifferent, so "all test" and "all but `θ̲`
    test" are both equilibria (`exercise_13_C_1`, `exercise_13_C_1_instance`). Reduced form
    `IsTestEq` as for `IsPBEC4`.

21. **Exercise 13.D.1.** The characterization `exercise_13_D_1` holds for every `μ ≥ 0`. The
    full-information outcome can be the unique SPNE (`exercise_13_D_1_fullinfo`); otherwise the
    high type's task is distorted upward (`exercise_13_D_1_distorted`); an SPNE need not exist
    (`exercise_13_D_1_nonexistence`).

22. **Exercise 13.D.2.** Contracts are described by the utility levels they give in the two
    states, equivalent by part (a) when `u` maps the wealth domain onto `ℝ` (e.g. `log`);
    `0 < p_L < p_H < 1`, `L > 0`; an indifferent individual chooses the policy with more
    coverage. Existence and nonexistence instances use `u = log`.

23. **Exercise 13.D.3.** The cost enters as `u(w - c)`, not working gives `u(0)`; part (a) is
    part (b) with `p_H = 1`, `p_L = 0`; part (c) assumes `0 < p_L < p_H < 1`, `q_B < q_G`, low
    expected output above `c` and `u` onto `ℝ` (instances `u(x) = log(1 + x)`); ties favour the
    flatter wage schedule.

24. **Exercise 13.D.4.** The free-entry equilibrium (`IsFreeEntryEq`): firms indexed by `ℕ`,
    finitely many active, one contract or none each, equal sharing, no firm gains by changing
    its offer (implies no profitable entry, `IsFreeEntryEq.no_entry`). The outcome is that of
    Proposition 13.D.2 (`exercise_13_D_4`). The pooling form of nonexistence carries over
    (`exercise_13_D_4_nonexistence`); the pair-of-contracts form does not: in
    `screenModel (2/5)` the two-firm game has no SPNE but a free-entry equilibrium exists
    (`exercise_13_D_4_pair`).

25. **Exercise 13.AA.1.** Education levels in `NNReal`, linear costs `c(e, θ) = k_θ e` with
    `k = (1, 1/2, 1/4)`, productivities `(1, 2, 10)`, uniform prior. Two PBE pass the intuitive
    criterion: separating `(0, 1, 17)` and partially pooling `(0, 0, 17)`
    (`exercise_13_AA_1`).

26. **Exercise 13.C.4: the PBE is not unique.** With a continuum of types and `c = e²/θ` the
    book asks for "the (unique)" PBE. Besides the separating PBE `e*(θ) = √((θ² - θ̲²)/2)`
    (`exercise_13_C_4_separating`), everybody choosing `e = 0`, paid `E[θ]`, with wage `θ̲`
    after any `e > 0`, is a PBE (`exercise_13_C_4_pooling`, `exercise_13_C_4_instance` with
    types uniform on `[1, 2]`). Corrected statement: every separating PBE is the one above
    (`exercise_13_C_4_unique_separating`). PBE are in reduced form (`IsPBEC4`): wages are the
    means of the firms' beliefs.

27. **Both types work in every screening SPNE (p. 462).** The book's "it is not difficult to
    see" is proved (`IsScreenEq.exists_bothEmployed`), so Lemma 13.D.1 and Proposition 13.D.2
    are stated without the earlier `BothEmployed` assumption, and the nonexistence theorems
    rule out every SPNE.

28. **Exercise 13.B.9.** `IsParetoImprovement` quantifies over all of `[θ_L, θ_H]`, including
    the null intermediate types; with `r` decreasing the results do not depend on them. The
    exact condition `exercise_13_B_9_exact` (`r(θ_L) ≤ θ_L`) uses `r` strictly decreasing, not
    `r(θ_H) < θ_H`.
