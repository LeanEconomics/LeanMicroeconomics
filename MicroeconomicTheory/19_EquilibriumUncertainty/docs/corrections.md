# Corrections and departures

Each item states what MWG prints, what is proved, and the Lean names (namespace
`MWG.EquilibriumUncertainty`). Page references are to the printed book. Items 1-9 correct
printed claims (with counterexamples where a claim is false); items 10-23 are departures in
modelling or method.

## Corrections

1. **Ownership shares (p. 689).** The book writes `∑ⱼ θⱼᵢ = 1` for every consumer `i`, where
   `θⱼᵢ` is the share of firm `j` owned by consumer `i`. The correct normalization is
   `∑ᵢ θⱼᵢ = 1` for every firm `j` (`SharesValid`, and `hθ : ∀ j, ∑ i, E.θ j i = 1` in
   `adEqm_paretoOptimal`). With one firm owned half-and-half by two consumers the printed
   condition fails (`shares_printed_normalization_fails`).

2. **Proposition 19.D.1(ii) (p. 697) and Proposition 19.E.2(ii) (p. 705): exact market clearing.**
   A Radner equilibrium only requires `∑ᵢ x*ᵢ ≤ ∑ᵢ ωᵢ`, while an Arrow-Debreu equilibrium
   (Definition 19.C.1(iii)) requires equality. Without monotonicity the conclusion fails: one
   consumer with constant utility, `x* = 0` (`proposition_19_D_1_ii_counterexample`). What holds
   in general is optimality in the Arrow-Debreu budget sets at the prices `μ_s p_s` with
   `∑ᵢ x*ᵢ ≤ ∑ᵢ ωᵢ` (`proposition_19_D_1_ii_le`); with strongly monotone utilities and positive
   prices the conclusion holds as printed (`proposition_19_D_1_ii`, `proposition_19_E_2_ii`).

3. **Example 19.E.6 (p. 707), the dispersion argument.** The book argues
   `q'₂(c) = q₃ + q₂(c) ≥ q₂(c)`, pricing `r₃ = r'₂(c) - r₂(c)` and `r₂(c)` by arbitrage. In the
   economy with dispersion `α'` the multipliers differ from those with `α`, and the identity
   fails with either set of multipliers: `α = 1/2`, `α' = 1`, `q₂ = 3`, `c = 2` give
   `q₂(c) = 5/4`, `q'₂(c) = 3/2`, `μ·r₃ = 5/12`, `μ'·r₃ = 3/8`
   (`example_19_E_6_identity_fails`). The conclusion `q'₂(c) ≥ q₂(c)` is true for arbitrage-free
   `q₂` and is proved directly from (19.E.2) (`example_19_E_6_dispersion`).

4. **Exercise 19.E.6(d) (p. 727).** Adding a riskless asset `(1, 1, 1)` at price `1` to
   `r₁ = (64, 16, 4)` (price `32`) and `r₂ = (0, 0, 1)` (price `1`) makes the structure complete,
   but the three prices admit an arbitrage (buy the riskless asset, sell `r₂`: cost `0`, returns
   `(1, 1, 0)`); the unique linear state prices `(7/12, -7/12, 1)` are not nonnegative, so these
   prices cannot arise in equilibrium with strongly monotone preferences (`exercise_19_E_6d`).

5. **Example 19.F.1 (pp. 709-710): state independence of Pareto optima needs `π_s > 0`.** The
   strict-concavity step only pins down consumption in states of positive probability. With
   `π = (1, 0)` the allocation `(1, 0)` is Pareto optimal but not state independent
   (`example_19_F_1_needs_pos`). The statement is proved with `π ≫ 0` (`example_19_F_1_po`,
   `po_stateIndependent`, which also only needs the aggregate endowment to be state
   independent).

6. **Example 19.H.4 (p. 723): the pooled prices.** With the endowments of Example 19.H.2 (one unit
   of good 1 per consumer) the pooled information prices are `2`, `1` and `3/2` in cases (i)-(iii)
   (`postCoef_pooled19H4`, `example_19_H_4`), not the printed `β/2 = 1`, `β/2 = 1/2` and `3/4`;
   the printed values are the prices when each consumer owns two units
   (`example_19_H_4_printed`). Exercise 19.H.4 ("complete the missing step") is the case (iii)
   computation: the posterior stays `1/2` and the price is `3/2`.

7. **Exercise 19.G.2 (p. 729) cannot be answered as asked.** With `L = 1`, a single initial asset
   with nonnegative nonzero returns, strongly monotone utilities and a firm with returns
   `εa ≥ 0` introduced as a tradeable asset owned in shares `θᵢ ≥ 0`, every consumer is at least as
   well off after the introduction as before: before, `q > 0` forces `x ≤ ω`; after, keeping the
   shares is affordable and gives `ω + θᵢ εa ≥ ω` (`exercise_19_G_2_no_one_worse_off`). So no
   example can make one consumer significantly worse off; what can happen is that the gains are
   very unequal.

8. **Proposition 19.H.1 and Exercise 19.H.2.** Not an error: the proof given (`proposition_19_H_1`,
   via the cell-sum identity `sum_eq_sum_cells`) does not need the budgets to be `σ`-measurable
   once both plans `x^σ` and `x^{σ'}` exist; measurability (Exercise 19.H.2) is what makes the
   plan of each signal well defined. Recorded because the formal statement is more general
   (`exercise_19_H_2`).

9. **Exercise 19.H.1(a) (p. 729), second part.** "Need not be true if `σ` is not completely
   revealing" is shown by an explicit counterexample (`exercise_19_H_1a_counterexample`).

## Departures

10. **Numeraire good.** The book uses good 1 for contingent trade and asset returns; the
    formalization takes an arbitrary good `g : Fin L` (`radnerFeasible`, `IsRadnerEqm`).
    Contingent vectors are `Fin S → Fin L → ℝ` (`CVec`); the book's ordering in `ℝ^{LS}` is
    `flat`, and Definition 19.C.1 is shown to be Definition 16.B.3 for the economy with `LS`
    commodities (`isADEqm_iff_isWalrasEqm`), through which the Chapter 16 welfare theorems are
    applied.

11. **Exchange economies with utilities.** From Section 19.D on, consumers have consumption sets
    `ℝ^{LS}_+` and utility functions (`IsADEqmU`, shown to be Definition 19.C.1 with no firms,
    `isADEqmU_iff`). Pareto optimality uses `∑ᵢ xᵢ ≤ ∑ᵢ ωᵢ` (pp. 694, 710; `IsParetoOptimalU`), and
    its first welfare theorem is proved directly under strong monotonicity
    (`adEqmU_paretoOptimal`).

12. **First-order conditions.** "Differentiable utility" is a `HasDerivAt` hypothesis at the
    points used; interior optima give the Lagrange condition through `foc_dir`, `foc_eu1` and
    `foc_halfspace`. `GoodBernoulli` (strictly concave, strictly increasing, differentiable on
    `ℝ_{++}`) is the standing hypothesis of Examples 19.C.1(b), 19.C.2, Exercise 19.C.2 and
    19.C.4(b), with the instance `√·` (`goodBernoulli_sqrt`).

13. **Proposition 19.E.1, Proof 2.** The book derives the first-order conditions from the
    indirect utilities `v_s(p_s, w)`, whose differentiability it does not establish. Here the
    reduced problem of footnote 18 is solved for any `v_s` differentiable at the optimum with
    positive derivative (`proposition_19_E_1_proof2`); for one good (`v_s = u_s`) the reduction
    from the Radner problem is proved (`proposition_19_E_1_proof2_radner`).

14. **Lemma 19.E.1 (Proof 1).** The book separates `V` from `ℝ^S_+ \ {0}` after dropping zero rows
    "without loss of generality" (footnote 17). The formal proof does exactly this, applying
    Theorem M.G.2 (Chapter 3) to the subtype of states with a nonzero row (`lemma_19_E_1`,
    `separation_fintype`). The standing assumption of Proposition 19.E.1 (nonnegative nonzero
    returns, `NonnegNonzeroReturns`) is a hypothesis; without it the lemma fails (a zero return
    column admits every price).

15. **Strong monotonicity where the book's proofs use it.** Propositions 19.E.1 (equilibrium
    prices arbitrage free), 19.E.3 (the book: "by strong monotonicity") and 19.F.1 (applied
    through the first welfare theorem in the book; proved directly here) assume strongly
    monotone utilities and nonnegative nonzero returns.

16. **Existence hypotheses.** Chapter 17 is not a dependency. Example 19.D.1 assumes that `ω̄/2` is
    the demand at a symmetric spot price (with the instance `u = min`,
    `example_19_D_1_instance`); Exercise 19.F.1 assumes a spot Walrasian equilibrium; the sunspot
    equilibrium of Example 19.F.1 is built from given spot equilibria (a spot economy with a
    continuum of equilibria is `leontief_spot_eqm`).

17. **Logarithmic utilities.** In the quasilinear economies of Section 19.H the consumption of
    good 1 is required to be positive (`ln 0` is not `-∞` in Mathlib) and the numeraire is
    unrestricted in sign (the book leaves its endowment unspecified). In Exercise 19.H.7 the
    entry "`2 ln x₁₂ × x₂₂`" of the table is read as `2 ln x₁₂ + x₂₂`, as in every other entry.

18. **Example 19.H.1.** In the perfect-information spot economies one good is worthless, so its
    price must be zero; the section's normalization of good 2's price to `1` is impossible in
    state 1. The theorems characterize every spot equilibrium without normalization
    (`example_19_H_1_state1`, `example_19_H_1_state2`).

19. **Weaker or explicit hypotheses in exercises.** Exercise 19.C.3 uses concavity (not strict
    concavity) and strictly positive subjective probabilities; Exercise 19.C.5 uses concave,
    nondecreasing Bernoulli utilities; Exercise 19.C.4(a) uses only strict concavity and
    differentiability of `u₂` at the equilibrium; Exercise 19.F.5(c) states the condition on
    marginal utilities as `U_a'(k/2) ≤ U_d'(k/2)`.

20. **Exercises 19.D.3 and 19.D.4.** "Proposition 19.D.1 remains valid" is proved as the equality
    of the Arrow-Debreu and Radner budget sets in both directions (with the induced prices and
    multipliers), which is the content of the proof of Proposition 19.D.1
    (`exercise_19_D_3_i`, `exercise_19_D_3_ii`, `exercise_19_D_4c_i`, `exercise_19_D_4c_ii`).

21. **Exercise 19.F.3: "the" equilibrium, and the asset structures.** The exercise speaks of the
    equilibrium with complete and incomplete markets. The formalization exhibits equilibria and
    compares them; uniqueness is not claimed. The economy of (a) has linear Bernoulli utilities
    (`U19F3`); "incomplete markets" in (a) is the economy with no assets (spot markets only,
    `exercise_19_F_3a_spot`), "complete markets" is the Arrow-Debreu equilibrium
    (`exercise_19_F_3a_AD`, and as a Radner equilibrium with contingent trade,
    `exercise_19_F_3a_complete_radner`). In (c) the assets pay good 1: `r_A = (-1, -1, 2, 2)`,
    `r_B = (8, -9, 0, 0)`, `r_C = (0, 0, 8, -9)` (`R1_19F3`, `R3_19F3`). In MWG's model (no
    consumption at date 0) the asset `r_A` has price `1 > 0` in both equilibria and is not traded,
    as the exercise's symmetry argument intends. (Informally, not formalized: with `q_A = 0` and no
    trade in `r_A`, both consumers would have to value `r_A` at zero, which in the three-asset
    economy forces equal marginal utilities of wealth in the two roles; the Arrow-Debreu
    allocation of (a) would then maximize the sum of utilities, contradicting (a).) With these
    choices both consumers' utilities fall from `3/2` to `23/16` (`exercise_19_F_3c`).

22. **Exercise 19.H.6(b)-(e): equilibria constructed from first-order conditions.**
    "Non-contingent markets within an event `E`" is formalized as trade in net bundles `τ` delivered
    in every state of `E`, at prices `P`, with budget `P·τ ≤ 0` (`IsNCEqm19H6`); conditional
    expected utility over `E` is replaced by the (proportional) sum over `E`. The equilibria are
    shown to be equilibria when `t` solves consumer 2's first-order condition
    `∑_{s ∈ E} 1/√(w_s + t) = 2|E|` with `t ≤ 0` (`ncEqm19H6`); existence of such `t` for general
    `w` and uniqueness are not formalized. All equilibria are computed in closed form for
    `ω₂₁ = 6`, `w = (1205/1156, 13/4, 541/100)` (`exercise_19_H_6_instance`), where the comparisons
    of (e) are strict. Consumer 1's ex ante utility is `ω₂₁` in all four settings, so the
    information of (c) is socially valuable in the weak Pareto sense with non-contingent markets,
    and the information of (d) has no value with contingent markets (`exercise_19_H_6e`).

23. **Exercise 19.F.4: real assets and Hart's example.** Real assets are bundles valued at the
    spot prices (`IsRadnerEqmReal`, which reduces to Definition 19.E.2 for returns in one good,
    `isRadnerEqmReal_single`). The example is: two equally likely states, Bernoulli utilities
    `2√x₁ + √x₂` and `√x₁ + 2√x₂`, endowments `(2, 1), (0, 1)` and `(0, 1), (2, 1)`, and two
    assets, asset `k` paying one unit of good `k` in every state. No Radner equilibrium exists for
    any prices (`exercise_19_F_4`). Prices are unrestricted in sign; positivity is derived from
    optimality.
