# Corrections and departures

Departures from MWG Chapter 18 as printed (pp. 652-686). Every item was checked against the page
images. Items 1-5, 8, 17, 18 and 27 refute printed claims (counterexample plus corrected statement);
items 4, 14, 22 are misprints or numbering slips; the rest record how an informal claim was made
precise or proved under different (usually weaker) hypotheses.

1. **Proposition 18.B.3 (p. 657) is false with `ωₕ ≥ 0` only.** With one type, two goods,
   `ω = (1, 0)`, `u = √x₁ + √x₂`, `Y = -ℝ²₊`, the allocation `x* = ω` is in every `C_N` but is
   not Walrasian for any `p` (`proposition_18_B_3_false`). Corrected: with `ωₕ ≫ 0` (as in
   Debreu-Scarf, and as in the book's own special-case proof), for any convex constant returns
   technology and any numbers of goods and types (`proposition_18_B_3`).
2. **p. 659: a nonzero `p` supporting `V` at `∑ωᵢ` is a Walrasian price.** The final step from
   `p·x ≥ p·ωᵢ` to `p·x > p·ωᵢ` needs `p·ωᵢ > 0`; in the economy of item 1, `p = (0, 1)` supports
   `V` and is not Walrasian (`supporting_price_needs_positive_endowment`). Corrected with
   `ωᵢ ≫ 0` and at least one consumer (`supporting_price_isWalrasEqm`).
3. **p. 659: core ⇒ `∑ωᵢ` is not interior to `V`** needs `L > 0` (with no goods `V = ℝ⁰`)
   (`core_not_mem_interior_coreV`).
4. **p. 666, misprint.** "It is enough to take `B = {x*₁, ..., x*_I}`" must read the net trades
   `{z*₁, ..., z*_I}`: `selfSelective_iff_netTrades`; with consumptions the claim fails
   (`selfSelective_consumptions_misprint`).
5. **Exercise 18.B.5(a), "matched ⟺ Pareto optimal", fails in both directions.** A matched
   allocation that discards pairs is not Pareto optimal (`shoe_matched_not_paretoOptimal`); a
   Pareto optimum need not be matched (one consumer holding one right and two left shoes,
   `shoe_paretoOptimal_not_matched`). True: Pareto optimal iff `∑ᵢ min(Rᵢ, Lᵢ) = I`
   (`shoe_paretoOptimal_iff`); matched allocations using all right shoes are Pareto optimal
   (`exercise_18_B_5a`); Pareto optima are matched after discarding useless left shoes
   (`exercise_18_B_5a_converse`).
6. **Figure 18.B.2.** The formal example (`figure_18_B_2`) has the roles of the two types
   interchanged relative to the figure (two consumers of the disfavoured type and one of the
   favoured type block).
7. **Exercise 18.B.5(c).** Besides the equilibria with `p_L = 0` there are no-trade equilibria
   with `p_R, p_L > 0` in which nobody can afford a pair; they are neither Pareto optimal nor in
   the core (`exercise_18_B_5c`, `exercise_18_B_5d`). Not a book error; part of the answer.
8. **Example 18.C.2 is internally inconsistent as printed.** `p(q₁, q₂) ≫ 0` and `ψ` strictly
   increasing cannot hold together with `ψ(·, 0) ≡ 0`, which forces `∂ψ/∂x₁(s, 0) = 0`
   (`partialOne_axis_eq_zero`). The claim that null production is an equilibrium is proved
   assuming only that `ψ` vanishes on both axes (`example_18_C_2`).
9. **Example 18.C.1, "very elastic".** Made precise as: the selection `p(·)` is nonincreasing and
   `s·p(s)` is nondecreasing on `[0, b']` (as Figure 18.C.3 is drawn), with `p ≥ 1/λ` there and
   `p ≤ 1/γ` beyond `b'` (`example_18_C_1`); a concrete selection is `cournotStepSel`.
10. **Footnote 8.** The achievable net trades lie in the hyperplane `p̄·z = 0`; the effective
    budget set itself lies in the Walrasian budget set when `p̄ ≥ 0` (`footnote_18_8`).
11. **Example 18.C.3, trading-post convention.** Payouts follow the share rule (Lean's `x/0 = 0`):
    a side facing no offers receives nothing; this equals the book's `a''/p - a'` whenever both
    sides are active (`example_18_C_3_rule`). The inactive-post theorem assumes utilities
    nondecreasing in goods and money.
12. **Insensitivity (p. 661).** Proved for actions in `ℝ^m` and a continuous `φ`, uniformly over
    profiles, agents and deviations (`price_insensitivity`).
13. **Exercise 18.E.3.** Every Walrasian trader gets strictly less than her marginal
    contribution (the left partial derivative of `v`, i.e. the loss from removing a marginal
    trader) at every equilibrium with both prices positive (`exercise_18_E_3`); at the boundary
    equilibrium with prices `(1, 0)` one type gets exactly her contribution
    (`exercise_18_E_3_boundary`). The exercise asks only that it be possible.
14. **p. 672 numbering.** The text refers to "Exercise 18.E.4" for the role of smoothness; the
    exercise is 18.E.3 (there is no 18.E.4).
15. **Proposition 18.E.1, method and hypotheses.** The multipliers (18.E.4) are obtained from
    first-order conditions for transfers between types, not from Section M.K, and (18.E.5)
    (Exercise 18.E.2) from `v ≤ g` with `g` linear touching at `μ`, not from the envelope theorem
    of M.L. The proof uses only `ψₕ` concave and nondecreasing, differentiable at `y*ₕ`, `v`
    differentiable at `μ`, and `y* ≫ 0` (money may be negative); the direction
    Walrasian ⇒ marginal product needs neither concavity nor differentiability of `ψ`.
16. **(18.E.1)-(18.E.2).** `v` is defined as a supremum (the book writes "Max"); existence of a
    maximiser is used only where an optimal allocation is given or exhibited.
17. **Example 18.AA.1: `V(S)` need not be closed.** With `L = 2`, one consumer,
    `Y = {y : y₁ < 0, y₂ < -y₁} ∪ {0}` (a convex cone), `ω = (1, 0)`, `u(x) = x₂`,
    `V = {w : w < 1}` (`example_18_AA_1_not_closed`, `openConeTech_isCRS`). Closedness of `Y` is not
    enough either: with free production, `Y = ℝ₊` (`L = 1`, a closed convex cone), `ω = 0` and the
    continuous, strictly increasing, concave `u(x) = 1 - 1/(1 + x)`, again `V = {w : w < 1}`
    (`example_18_AA_1_free_production`). Corrected: `V(S)` is closed whenever `Y` is a closed cone
    with no free production, `Y ∩ ℝ^L₊ = {0}`, and utilities are continuous on `ℝ^L₊`
    (`example_18_AA_1_closed_cone`, `example_18_AA_1_closed_crs`; key lemma `c18_cone_bounded`;
    instance `example_18_AA_1_closed_halfPlane` with `Y = {y₁ + y₂ ≤ 0} ⊄ -ℝ²₊`); the special
    case `Y ⊆ -ℝ^L₊` is `example_18_AA_1_closed`. Convexity of `Y` and `ωᵢ ≥ 0` are not used.
18. **Footnote 28** ("`v(S) + v(T) > v(I)` for any partition") needs `ωᵢ > 0`: with a zero
    endowment a coalition can have `v(S) = f(0) = 0`. Proved with `ωᵢ > 0`, and `n ≥ 2` for the
    empty core (`footnote_18_28`, `footnote_18_28_core_empty`).
19. **Example 18.AA.6** does not need continuity of `f`; `ωᵢ ≥ 0` is used and `∑ωᵢ = 0` is
    handled (`example_18_AA_6`).
20. **Example 18.AA.5.** "The two cores are identical" is stated as: `x` is in the economy's core
    iff `x` is feasible and its utility vector is in the game's core (`example_18_AA_5`).
21. **Example 18.AA.8 / Exercise 18.AA.7.** The game is first proved convex under increasing
    differences of `f` on `ℝ^N₊` (`IncreasingDifferences`, `exercise_18_AA_7`). The printed
    hypothesis `∂²f(z)/∂z_h∂z_k ≥ 0` "for all `z` and `h, k`" is made precise as: `f` is `C²` on an
    open set containing `ℝ^N₊` and the second partials are nonnegative on `ℝ^N₊`; it implies
    increasing differences for every `N` (`example_18_AA_8_increasingDifferences`, by the mean
    value theorem along coordinate-monotone segments), so the game is convex
    (`exercise_18_AA_7_crossPartials`; instance `f(z) = z₁z₂`, `exercise_18_AA_7_product`). For
    `N = 1`: `example_18_AA_8_one_input_deriv`.
22. **p. 683 numbering.** The text assigns the convexity of the production game to
    "Exercise 18.AA.8"; it is Exercise 18.AA.7.
23. **Appendix A proof routes.** Proposition 18.AA.1 is proved via "every marginal vector is in
    the core" and (18.AA.3), not the book's lemma `Shᵢ(S) ≤ Shᵢ(T)`; (18.AA.4) = (18.AA.3) via
    Harsanyi dividends; Exercise 18.AA.9(d) uses Chapter 22's permutation symmetry; Exercise
    18.AA.9(b) is strengthened to equality of the core with the `α`-family.
24. **Exercise 18.AA.10(c)-(d).** With `0 < γ < 1` total profit `α₁x₁ + α₂x₂ - C` is unbounded
    above, so no efficient choice exists (`exercise_18_AA_10c_unbounded`,
    `exercise_18_AA_10c_no_max`); the Shapley rule charges each division more than `C'`
    (`exercise_18_AA_10c_foc`). Part (d) is answered by the corrected statement that no
    differentiable rule with `ψ₁ + ψ₂ = C` charges each division `∂ψᵢ/∂xᵢ = C'(x₁ + x₂)` on the
    open quadrant (`exercise_18_AA_10d`).
25. **Proposition 18.D.1** is proved in a corrected smooth form (`proposition_18_D_1_smooth`,
    with `z` assumed continuous and C¹) and in a continuum form for `L = 2`
    (`proposition_18_D_1_continuum`): types `t ∈ [0, 1]`, a population measure `ν` finite on
    compacts with `ν([0, 1]) ≠ 0` (characteristics present: all `t ∈ [0, 1]`, connected through
    `t`), measure feasibility `∫_{[0,1]} z dν = 0`, no envy among types, a common supporting price
    `p ≠ 0` (each bundle best in its budget) with first-order conditions `Du(x(t); t) = λ(t) p`,
    `λ(t) ≥ λ₀ > 0`. Regularity made explicit (the book: "far from rigorous"): continuous
    endowments; utilities jointly continuous in `(t, x)`, strictly quasiconcave, differentiable
    near the bundles with derivatives uniformly equicontinuous in `x` (uniformly in `t`); bundles
    interior with a uniform margin `η`; bounded net trades. The continuity of `z(t)`, asserted
    informally in the book, is derived (`c18_continuousOn_of_noEnvy`), not assumed. The
    supporting price is a hypothesis (the second welfare theorem for the continuum is OPEN); its
    converse, that a supported allocation is Pareto optimal in the measure sense, is
    `c18_isMeasurePareto_of_supported`. `L ≥ 3` is OPEN (the planar step fails there).
26. **Weaker hypotheses than printed** (stronger results): Proposition 18.B.1 uses only the cone
    property of `Y` and no preference assumptions; Exercise 18.B.3 does not need continuity; the
    identity of p. 658 holds for any feasible `y`; the special-case argument of pp. 657-658
    works for any CRS technology; Exercise 18.D.1 needs only rational strictly convex preferences
    and exact Edgeworth feasibility; the p. 667 claim holds with `B = {p·z ≤ 0}` as well
    (`walras_isParetoOptimal_selfSelective`, which assumes `L > 0` and a nonempty set of
    consumers).
27. **p. 673, the hypergeometric-average formula as printed is not the Shapley value.** Read
    literally (weight `1/I` times the probability of `I'` in a sample of size `|I'|` from the
    population `I`, times `Δ_h v(I') = v(I') - v(I' - e_h)` over `I' ≤ I` with `I'_h ≥ 1`), with
    one consumer of each of two types and `v(I') = I'₁ + I'₂` it gives `3/4`, while the Shapley
    value is `1` (`c18_book_formula_counterexample`). Exact formula: for a consumer of type `h`,
    `Sh_h = ∑_{m ≤ I - e_h} (1/I) [∏_k C((I - e_h)_k, m_k) / C(I - 1, |m|)] (v(m + e_h) - v(m))`,
    sampling from the OTHER consumers (`c18_shapley_hypergeometric`, weights summing to one,
    `c18_hypergeometric_weights_sum`); the printed version is its large-economy approximation.
