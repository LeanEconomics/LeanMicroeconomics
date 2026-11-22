# Corrections and departures

MWG, Chapter 22. Lean names are relative to `MWG.WelfareBargaining`.

1. **Example 22.B.2, p. 820 (sign of the multiplier).** The book states that the Ramsey prices
   satisfy `λ(p̄ₗ - 1)xₗ'(p̄ₗ) = (1 - λ)xₗ(p̄ₗ)` for some `λ < 0`. The Kuhn-Tucker multiplier of
   the revenue constraint gives this equation with `λ > 1`, and then (22.B.1) holds with
   `α = (λ - 1)/λ ∈ (0, 1)`. Counterexample: two goods with `xₗ(p) = 2 - p`, unit cost, `R = 3/8`;
   `p̄ = (5/4, 5/4)` is optimal and the equation holds only for `λ = 3/2`
   (`example_22_B_2_correction`, which also checks `tε = 1/3 = (λ-1)/λ`). In general
   (`exercise_22_B_2`, Exercise 22.B.2) the multiplier satisfies `λ ≥ 0`, and with positive,
   downward-sloping demands and `R > 0` it satisfies `λ > 1`, giving (22.B.1) with
   `α = (λ-1)/λ ∈ (0, 1)` (`exercise_22_B_2_ramsey`).
2. **Exercise 22.D.5, p. 852.** "`F'` inherits the Paretian condition from `F`" is false for the
   weak half of Definition 22.D.2: Definition 21.C.2 only asks unanimous *strict* preference to be
   respected. The tie-broken dictatorship `tieBreakDict` is a Paretian, pairwise independent
   social welfare functional on `𝓡^I` whose `F'` violates the weak half
   (`exercise_22_D_5_weak_not_inherited`). Corrected statement: with the additional hypothesis
   that unanimous weak preference is respected, the route of p. 837 proves Arrow's theorem
   (`exercise_22_D_5`); Arrow's theorem in general is MWG Proposition 21.C.1 (imported from
   Chapter 21). The "assume Proposition 22.D.3 under the weakened assumption" of the exercise is
   not needed: that extension is proved (`proposition_22_D_3_relation`).
3. **Exercise 22.D.6(b), p. 853.** "If `W` is symmetric and `g(0) = 0` then `g ≥ 0`" is false:
   `W(u) = ū + |u₁ - u₂|/4` is continuous, increasing and symmetric with `g(s) = -|s₁ - s₂|/4`
   (`exercise_22_D_6b_counterexample`). Corrected: true if `W` is also quasiconcave
   (`exercise_22_D_6b`).
4. **Small type, p. 838 (Maskin).** "Under weak conditions the only additively separable social
   welfare functions invariant to common changes of origin are utilitarian": the conditions
   must exclude the Kolm-Pollak function `-∑ e^{-uᵢ}`, which is continuous, increasing,
   symmetric, concave, separable and common-origin invariant but not utilitarian
   (`kolmPollak_invCommonOrigins`, `kolmPollak_not_utilitarian`). No corrected positive
   statement is formalized (see the source map).
5. **Exercise 22.E.1 / Example 22.E.2.** The utilitarian solution is symmetric (and satisfies IIA)
   only where the maximizer is unique (e.g. strictly convex `U`); in general it is a selection
   (footnote 30). We prove symmetry and IIA under uniqueness (`utilSol_symmetric_of_unique`,
   `utilSol_IIA_of_unique`, `utilPoint_unique_of_strictConvex`) and that some utilitarian
   selection violates IIA (`exercise_22_E_10`).
6. **Definition 22.E.3, p. 840.** Stated for normalised problems in the book; we scale the threat
   point as well (`IUU`), which is equivalent under IUO (`normalize_eq`).
7. **Exercise 22.D.3, p. 833.** Transferring the Pareto property to `ℝ^I` needs two distinct
   alternatives (hypothesis of `exercise_22_D_3`); with one alternative the claim is vacuous/false.
8. **Example 22.C.4, p. 829.** For `ρ ≥ 1` the utilities must be positive, not just nonnegative
   (`ln 0`, `0^{1-ρ}` are undefined); we work on `u ≫ 0`. The printed
   `h(W) = [1/(1-ρ)]W^{1/(1-ρ)}` is not an increasing transformation for `ρ > 1`, where
   `W = ∑ g_ρ(uᵢ) < 0`: for `ρ = 3/2` it is `-2W^{-2}`, which ranks `(1, 1)` above `(4, 4)`
   (`example_22_C_4_printed_h`). Corrected: `h(W) = (W/(1-ρ))^{1/(1-ρ)}`, with
   `W_ρ = h(∑ g_ρ)` (`example_22_C_4_h`) representing the same ordering
   (`example_22_C_4_represent`).
9. **Misprints.** p. 835: "Proposition 23.D.2" should read 22.D.2, and "invariance to identical
   changes of units" in the proof of Proposition 22.D.2 should read "origins". p. 843: the proof
   of Proposition 22.E.1 refers to "Example 22.E.4"; Example 22.E.3 is meant.
10. **Exercise 22.C.3(d), p. 851 (Harsanyi).** As printed, "`U = β₁U₁ + ⋯ + β_IU_I` with
    `βᵢ ≥ 0`, some `βᵢ ≠ 0`" is false. (i) A constant is needed: with `U₁ = U₂ = p₁`, the
    Paretian `U = p₁ + 1` is no such combination (`exercise_22_C_3d_constant`). (ii) Some
    agreement is needed: with opposed individuals (`U₂ = -U₁`) every `U` is Paretian, which is
    part (c) of the same exercise, and `U = p₂` is no combination `β₁U₁ + β₂U₂ + c`
    (`exercise_22_C_3d_opposed`). Corrected (`exercise_22_C_3d`, `I = 2` as the exercise allows,
    any `N`): if some pair of lotteries is strictly preferred by both individuals, then
    `U = β₁U₁ + β₂U₂ + c` on the simplex with `β ≥ 0`, `β ≠ 0`; for any number of individuals
    `exercise_22_C_3d_general` (via Farkas's lemma from MWG Chapter 5).
11. **Exercise 22.C.7, p. 851.** If the two Edgeworth box economies differ only in how a fixed
    aggregate endowment is split, their utility possibility sets coincide and the requested
    property holds for any outcomes (`exercise_22_C_7_same_total`), so the exercise is only
    interesting when the endowment vectors themselves differ. `exercise_22_C_7` gives such a
    Scitovsky reversal with verified competitive equilibria.
12. **Exercise 22.D.7, p. 853 (domain).** The constant elasticity functionals are defined on
    profiles of positive utilities (Example 22.C.4), so the invariance properties are stated for
    positive profiles (`InvCommonUnitsPos`, `InvCommonOriginsPos`); for `ρ = 0` and `ρ = ∞` the
    full invariance on all profiles is proved.
13. **Exercise 22.E.5(b), p. 854.** As printed (independence of utility origins, weak Pareto,
    strong monotonicity) the curve need not start at the origin: the egalitarian solution
    measured from the threat point shifted to `(-1, 0)` satisfies all three properties, its
    values on normalized problems lie on the line `u₂ = u₁ + 1` (none within `1/2` of the
    origin), and the box `{u ≤ (1/2, 1/2)}` gets the value `(-1/2, 1/2)`
    (`exercise_22_E_5b_needs_IR`). Corrected (`exercise_22_E_5b`): adding individual
    rationality (Definition 22.E.6), the values `C` on normalized problems are `≫ 0`, any two
    are equal or strictly ordered (`≪`), `C` comes arbitrarily close to the origin, and on every
    normalized problem `f(U)` is the unique point of `C` on the weak Pareto boundary of `U`;
    with IUO, `f(U) - u* ∈ C` in general. The "curve" is formalized as this strictly ordered set
    of values (no parametrization is constructed).
14. **Exercise 22.E.11(b), p. 854 (formulation).** "Nearly equal to the Nash solution payoffs" is
    formalized for the agreed shares (both stationary proposals converge to the Nash share as
    `δ → 1`, `exercise_22_E_11b`), assuming in addition that `u₁` is continuous on `[0, m]`.
15. **Exercise 22.F.7(b), p. 856.** With separable costs no approximation is needed: the Shapley
    value charges each project exactly the average cost `cₗ(qₗ)/qₗ` of its type
    (`exercise_22_F_7b`).
16. **Exercise 22.E.11(a) existence and 22.E.11(c), p. 854 (hypothesis).** The utilities are
    assumed continuous on `[0, m]` (`exercise_22_E_11a_exists`, `exercise_22_E_11c`). MWG assume
    differentiable utilities, which implies this; a concave increasing function on `[0, m]` may
    jump at `0`, where the Shaked-Sutton limit argument and the existence of the stationary
    configuration need continuity. As in Chapter 9, subgame perfection is required at histories
    of feasible offers (`UIsSPNE`). The result proved is stronger than asked: every SPNE has, at
    every such history, the stationary payoffs, the stationary offer and immediate agreement
    (`uSPNE_unique`).
17. **Debreu's separability theorem, p. 838 (small type).** As printed, with MWG's "increasing"
    (p. 825: weakly increasing, strictly increasing on `≫`), the claim is false for `I = 3`:
    `W(u) = u₁ + u₂ + min(u₁, u₂)` is continuous, increasing and independent of irrelevant
    individuals, but no functions `gᵢ` represent it additively, because agents 1 and 2 violate
    the Thomsen condition and agent 3 never matters (`debreu_counterexample_null_agent`).
    Debreu's theorem needs at least three agents who matter. Proved
    (`debreu_separability`, `debreu_separability_transform`): for `I ≥ 3`, a continuous `W`,
    strictly increasing in each agent's utility, independent of irrelevant individuals and
    unrestrictedly solvable (`IsSolvableSWF`: any welfare level can be reached by changing any
    one agent's utility; implied by continuity and unboundedness of each agent's section,
    `isSolvableSWF_of_unbounded`) has continuous strictly increasing `gᵢ` with
    `W(u) ≤ W(u') ↔ ∑ gᵢ(uᵢ) ≤ ∑ gᵢ(u'ᵢ)`. Solvability is an added hypothesis, not a correction:
    Debreu's theorem holds without it, but that case (e.g. `∑ arctan uᵢ`) is left OPEN. For
    `I = 2` the conclusion fails even with all the hypotheses (`debreu_fails_two_agents`).
