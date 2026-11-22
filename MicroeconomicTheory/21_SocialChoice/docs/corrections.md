# Corrections and departures

Three printed exercise claims are false (items 9, 11, 13), and so are the literal reading of
21.D.8(a) and the first-order reading of 21.D.8(c) (item 15); the remaining items are proof repairs, missing hypotheses or precise readings.

1. **Proposition 21.C.1, Step 9, pp. 798-799 (proof repair).** The book takes, for the agents
   of `T ⊆ I \ S` who regard `x` as at least as good as `y`, a profile with `x ≻ᵢ y ≻ᵢ z`. On
   the domain `𝓡^I` such an agent may be indifferent between `x` and `y`, and then pairwise
   independence does not connect the two profiles. `arrow_step_9` uses `x ∼ᵢ y ≻ᵢ z` for those
   agents (the profile is in `𝓡^I`; on `𝓟^I` the case does not occur). The statement of Step 9
   and of Arrow's theorem are unchanged.
2. **Proposition 21.C.1, Step 8 (precise reading).** "Iterating Step 7" is formalized by taking
   a decisive set of minimal cardinality (`arrow_step_8`). The set of alternatives may be
   infinite; the set of agents is finite.
3. **Example 21.C.1, p. 794 (missing hypothesis).** The Borda count is Paretian only with at
   least one agent (`example_21_C_1_paretian` assumes `Nonempty ι`).
4. **Definition 21.D.1(ii), p. 800 (empty set).** Acyclicity is printed with "every finite
   subset"; the empty subset has no maximal element, so read literally no relation is acyclic
   (`acyclic_as_printed_false`). `Acyclic` quantifies over nonempty finite sets.
5. **Exercise 21.D.1, p. 812 (empty set).** Likewise "every strict subset" must exclude `∅`;
   `exercise_21_D_1` is stated for nonempty strict subsets.
6. **Definition 21.D.5, p. 802 (missing hypothesis).** "A median agent always exists" needs at
   least one agent (`median_exists` assumes `Nonempty ι`).
7. **Section 21.D, p. 803 (proof route).** "Proposition 21.D.1 guarantees that `F̂` is acyclic":
   restricting a single-peaked preference with indifferences to a finite subset need not give a
   single-peaked preference (ties across the peak), so Proposition 21.D.1 does not apply
   directly. `majorityRel_acyclic` proves the claim by splitting each agent into two who break
   ties left and right (`doubleProfile`, `majorityRel_doubleProfile`).
8. **Example 21.D.4, p. 801 (missing hypothesis).** `[a, b]` must be nonempty: for `a > b`
   every relation is strictly convex and none is single peaked (`example_21_D_4_empty`). The
   necessity direction needs no continuity (`exercise_21_D_4`).
9. **Exercise 21.D.9(c), p. 814 (false).** With preferences that are merely intermediate along
   segments of parameters, `B(x, y)` need not be the intersection of the parameter set with a
   half-space: `exercise_21_D_9c_counterexample` (parameters `[0, 1]`, `x ≻ y` at `0` and `1`,
   `x ∼ y` inside) has `B(x, y) = {0, 1}`, not convex. What remains true: the complement
   `{β : y ≿_β x}` is convex (`exercise_21_D_9c`).
10. **Exercise 21.D.9(e), p. 814 (hypothesis made precise).** "`g(β*) > 0`" does not by itself
    give positive mass near `β*` (a density is defined only almost everywhere); we assume
    positive mass on every open set whose closure contains `β*` (true for a density continuous
    and positive at `β*`). Utilities are taken linear in the parameter, `⟪β, H(x)⟫`, without the
    positivity restriction `β ∈ ℝ^N_{++}`; instance: `exercise_21_D_9e_instance`.
11. **Exercise 21.D.10(d), p. 814 (false).** With pretax wealth `(1 - t²)wᵢ`, ex post wealth
    `(1 - t²)((1 - t)wᵢ + t w̄)` is a product of positive affine functions on `[0, 1)`, hence
    strictly log-concave, and vanishes at `t = 1`; every agent's preference over tax rates is
    single peaked (`exercise_21_D_10d`, via `wealthD_strictQuasiconcave` and Example 21.D.4).
12. **Exercise 21.D.10(b), p. 814 (exception).** An agent with `wᵢ = w̄` is indifferent between
    all tax rates, so not single peaked (`exercise_21_D_10b_mean_agent`). The Condorcet-winner
    claims hold (`exercise_21_D_10b_condorcet`). In (c) we prove `t_c = 0` when `w* ≥ w̄/2` and
    `t_c > 0` when `w* < w̄/2` (`exercise_21_D_10c`). `w̄` is any positive number in these
    results.
13. **Exercise 21.E.2, p. 816 (false).** On `𝓡^I` the "smallest label among agent 1's most
    preferred alternatives" rule is dictatorial and weakly Paretian but not monotonic when there
    are at least two alternatives: if agent 1 moves from `x₂ ≻ x₁` to `x₁ ∼ x₂`, `x₂` maintains
    its position but the choice switches to `x₁` (`exercise_21_E_2_not_monotonic`). On `𝓟^I`
    the rule is monotonic (`exercise_21_E_2_strict`), as the text on p. 808 says for dictatorial
    functions on `𝓟^I` (`dictatorial_strict_spec`).
14. **Exercise 21.D.7(b), p. 813 (missing hypothesis).** The point `x` must be nonzero: for
    `x = 0` no `y` satisfies `‖x - y‖ < ‖x‖` (`exercise_21_D_7b_zero`). We prove (a) and (b)
    for utilities merely differentiable at the origin, without the hint's linearity.
15. **Exercise 21.D.8, p. 813 (reading of "directional median"; scope of (c)).** Read literally
    ("any alternative having a strict majority against the origin must make this agent strictly
    better off", a statement about utility levels), part (a) is false even for concave
    utilities with a pointed gradient cone: `exercise_21_D_8a_global_counterexample` (utilities
    `Re z`, `Im z`, `Re z + Im z - 2(Re z - Im z)²`, gradients `1, I, 1 + I` at the origin; for
    each agent some alternative is preferred to the origin by the other two while that agent is
    not better off). What is true is the first-order statement, for the gradients
    (`IsDirectionalMedian`): a directional median exists when the cone contains no half-space
    (`exercise_21_D_8a`), and in fact iff the cone is not the whole plane
    (`exercise_21_D_8a_iff`). Part (b) is proved with Euclidean utilities on the half-plane
    `{z₁ < 8}` (`exercise_21_D_8b`). Part (c) holds for arbitrary utilities under the literal
    notion (`exercise_21_D_8c_global`) and for linear utilities under the first-order notion
    (`exercise_21_D_8c`), but under the first-order notion it is false for nonlinear utilities:
    `exercise_21_D_8c_counterexample` takes `X = ℝ²` and the concave, continuously
    differentiable utilities `Im z - (Re z)²`, `Im z`, `Im z - (max (Re z) 0)²`. All gradients
    have second component `1`, so the cone is pointed everywhere; agent 2's gradient equals agent
    1's where `Re x ≤ 0` and agent 0's where `Re x ≥ 0`, so agent 2 is the directional median at
    every point; yet `(0, -1/4)`, `(1, 1/2)`, `(-1, 0)` form a Condorcet cycle (agents 0, 1 prefer
    `(1, 1/2)` to `(-1, 0)` while agent 2's utility falls). The corrected statement is the
    literal one, `exercise_21_D_8c_global`.
16. **Example 21.D.6, p. 805 (generality).** The median is defined for every probability
    measure (each open half-space through `x*` has mass at most `1/2`); with null hyperplanes this
    is the book's definition (`isMedianPoint_iff_book`). Median ⇔ Condorcet winner is proved for
    every probability measure (`example_21_D_6`).
17. **Exercise 21.D.13(a), p. 815 (generality).** General position is not needed for `J` odd
    (`exercise_21_D_13a`); for `J` even the claim fails (`exercise_21_D_13a_even`). In (b) masses
    are nonnegative and sum to one.
18. **Exercise 21.D.12(b), p. 815 (discussion made precise).** With exactly one zero tax an
    alternative is defeated (`exercise_21_D_12b_one_zero`); when one agent pays everything it is
    a (weak) Condorcet winner (`exercise_21_D_12b_one_payer`).
19. **Proposition 21.B.1, p. 792 (proof route and generality).** The book's "without loss of
    generality" reordering is replaced by lowering the excess supporters of `x` to
    indifference (`may_plus`); May's characterization is proved for every `F : (ι → ℤ) → ℤ`.
20. **Exercise 21.E.1, p. 815 (generality).** Finiteness of `X` is not needed.
21. **Representation of the plane.** Exercises 21.D.7, 21.D.8 and 21.D.13 use `ℂ` with its real
    inner product as the Euclidean plane; Example 21.D.5 uses pairs of reals.
22. **Figure 21.D.8(b), p. 806, and Exercise 21.D.9(d), p. 814 (precise reading).** "The uniform
    density over a triangle" is Lebesgue measure restricted to the open triangle (the boundary
    is null), not normalised (the median property is invariant under scaling). No median exists
    for the standard triangle (`figure_21_D_8b`) and, by affine invariance of medians
    (`isMedianPoint_of_affine_image`), for every image of it under an affine bijection, i.e.
    every triangle with nonempty interior (`figure_21_D_8b_affine`); the triangle with vertices
    `(1, 1)`, `(2, 1)`, `(1, 2)` gives the nonexistence half of Exercise 21.D.9(d)
    (`exercise_21_D_9d_not_exists`). The proof uses only the three lines through the candidate
    point parallel to the sides, which would all have to bisect the area.
