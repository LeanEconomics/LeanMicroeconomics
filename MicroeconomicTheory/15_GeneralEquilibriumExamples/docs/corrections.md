# Corrections and departures

Each item states what MWG prints, what is proved, and the Lean names. Page references are to the
printed book.

1. **Utility representations and consumption sets.** The book states Section 15.B for
   preference relations on `ℝ²₊`. We work with utility representations (as in Chapter 10), and
   the exchange economy `ExchangeEconomy` allows general consumption sets so that later chapters
   can reuse it. Where the book's utility is `-∞` on part of the boundary we either restrict the
   consumption set to the bundles with finite utility (Example 15.B.2, item 3; Exercise
   15.B.10(a), `ex15B10aEconomy`) or use an equivalent finite representation: Blair's CES utility
   `(A x₁⁻² + B x₂⁻²)^{-1/2}` is written `x₁x₂/√(A x₂² + B x₁²)` (`cesNeg2`, equal on `ℝ²₊₊` by
   `cesNeg2_eq`), and `ln x₁ + ln x₂` (Exercise 15.C.2) is represented by `x₁^{1/2}x₂^{1/2}`
   (`ex15C2Economy`). Definitions 15.B.1 and 15.B.3 are formalized as printed (`IsWalrasEqm`,
   `IsEqmWithTransfers`, which do not require the equilibrium bundle to be affordable); under local
   nonsatiation they coincide with the demand forms (`isWalrasEqm_iff_isDemandEqm`,
   `ExchangeEconomy.IsEqmWithTransfers.wealth_eq`).

2. **The offer curve passes through the endowment, p. 517.** As a general statement this is false:
   in the economy of Figure 15.B.10(a) (which the book itself discusses) consumer 1's endowment is
   never demanded at strictly positive prices (`fig_15_B_10a_endowment_not_optimal`), so it is not
   on his offer curve. Corrected statement: if preferences are convex, the utility is continuous on
   `ℝ^L₊` and differentiable at `ωᵢ ≫ 0` with `∇u(ωᵢ) ≫ 0`, then `ωᵢ` is demanded at `p = ∇u(ωᵢ)`
   (`endowment_mem_offerCurve`); offer curves are taken over strictly positive prices
   (`ExchangeEconomy.offerCurve`).

3. **Example 15.B.2, pp. 521-522.** The utilities `x₁₁ - x₂₁⁻⁸/8` and `-x₁₂⁻⁸/8 + x₂₂` are `-∞`
   where the non-numeraire good is zero; the consumption sets are `{x₁ ≥ 0, x₂ > 0}` and
   `{x₁ > 0, x₂ ≥ 0}` (`ex15B2Economy`). The printed claims are all confirmed: `r > 0`, the offer
   curves are as printed and strictly positive at every `p ≫ 0`, and the equilibrium price ratios
   are exactly `1/2, 1, 2` (the market-clearing polynomial `r t⁹ - t⁸ + t - r` has exactly these
   positive roots, `ex15B2_roots`).

4. **Second welfare theorem in the one-consumer economy, p. 528.** The book assumes a strictly
   concave increasing `f`, drawn smooth. We prove the result for `f` concave and strictly
   increasing on `[0, ∞)` and differentiable at the optimal labor input `z* > 0`, with supporting
   prices `p = 1`, `w = f'(z*)` (`rc_second_welfare`). Without differentiability the supporting
   wage is a supergradient chosen by a separation argument, which we do not formalize.

5. **The 2 × 2 model, pp. 532-537.** The model is formalized through the production functions and
   the cost-minimizing unit input vectors `aⱼ(w)` (assumed unique, as in the book). We add the
   assumption that `aⱼ` is continuous in the relative factor price (it holds in all examples and
   follows from uniqueness by the maximum theorem); from it we prove Shephard's lemma along relative
   prices (`TwoByTwo.unitCost_hasDerivAt`), which the book uses without proof. The global
   Stolper-Samuelson theorem is proved directly (the book reduces to an infinitesimal change). The
   Leontief instance (`leontiefModel`) used for non-vacuity and for Exercises 15.D.4 and 15.D.9 is
   not differentiable; it satisfies all assumptions the proofs use. Exercise 15.D.4(b) is proved for
   this instance only.

6. **(15.D.3)-(15.D.4), p. 531, and factor prices as marginal revenue products, p. 532.** The
   cost-function conditions are proved in their constant-returns form, `pⱼ = cⱼ(w)` and
   `∑ⱼ qⱼ aⱼ(w) = z̄` (`TwoByTwo.interior_eqm_iff`). That equilibrium factor prices equal the
   gradient of the aggregate revenue function is proved in supergradient form
   (`factorEqm_supergradient`), which gives the comparative statics claim without
   differentiability (`factor_price_endowment_opposite`, weak inequality).

7. **Tax incidence, pp. 539-540.** The book differentiates the equilibrium paths `w(t)`, `z(t)`,
   `z₁(t)` without establishing them. We assume the paths exist and are differentiable at `0`
   (`general_eqm_wage_derivative`) and give an explicit instance (`quadratic_eqm_path`).

8. **Exercise 15.B.4(d), p. 541.** "Non-normal" means that the demand for a good rises with its
   price while the demand for the other does not rise. With a weak fall of the other demand the
   Slutsky decomposition only yields a weakly non-normal good (`∂x/∂w ≤ 0`); with a strict fall it
   yields a strictly inferior good (`exercise_15_B_4d`, proved in this form).

9. **Exercise 15.B.10(b), p. 542.** The claim that a transfer to consumer 1 cannot lower his
   utility when preferences are quasilinear with the same numeraire is false when the equilibrium
   price is not unique: with the continuous, strictly convex, strongly monotone utility
   `min(2x₁, x₁ + 1) + √x₁ + x₂` for both consumers, `p = (5/2, 1)` is an equilibrium before and
   `p = (3/2, 1)` an equilibrium after a transfer of `1/10` of good 1, and consumer 1 is worse off
   (`exercise_15_B_10b_counterexample`). Corrected statement: for every equilibrium before the
   transfer there is an equilibrium after it at the same prices in which consumer 1 gains `p·z/p₂`
   (`exercise_15_B_10b`, numeraire unrestricted in sign as in Definition 3.B.7); in particular the
   claim holds whenever the equilibrium price is unique.

10. **Exercise 15.C.1(b), p. 542.** At an equilibrium the slope of the excess demand for labor is
    the compensated own-price effect on leisure plus the slope of labor demand
    (`exercise_15_C_1b`), hence nonpositive; it is negative when either term is negative (e.g. a
    strictly decreasing labor demand), not in general (`exercise_15_C_1b_sign`). A neighborhood
    statement additionally needs continuity of the derivative.

11. **Exercise 15.D.9 (Heckscher-Ohlin), p. 544.** As printed the claim is false: increasing,
    concave, homogeneous utilities need not have unique demands. In a Leontief world at
    `p = (3, 3)`, country A (endowment `(5, 4)`) produces `(2, 1)` and country B (`(4, 5)`) produces
    `(1, 2)`; with the linear utility `x₁ + x₂` the consumptions `(3, 0)` and `(0, 3)` are demanded,
    world markets clear, both countries are diversified, and A imports good 1
    (`exercise_15_D_9_counterexample`). Corrected statement: if the countries' consumption vectors
    are proportional (`exercise_15_D_9`), in particular if the homogeneous utility has a unique
    demand (`exercise_15_D_9_unique_demand`), country A exports good 1.

12. **Exercise 15.B.7 and p. 533, "on one side of the diagonal".** Proved in the weak form: under
    continuity, strong monotonicity, strict convexity, homotheticity and `ω̄ ≫ 0`, either every
    Pareto optimum has `x₁₁ω̄₂ ≤ x₂₁ω̄₁` or every one has `≥` (`exercise_15_B_7_homothetic`). The two
    origins always lie on the diagonal, and the Pareto set can be the whole diagonal (the economy
    with identical utilities `√x₁ + √x₂`, `sqrtEconomy_paretoSet`); a Pareto optimum other than the
    origins on the diagonal forces the Pareto set to be the diagonal (`exercise_15_B_7_diagonal`).
    Connectedness is proved by showing that consumer 1's utility is a homeomorphism from the
    (compact) Pareto set onto `[u₁(0), u₁(ω̄)]` (`exercise_15_B_7_homeomorph`).

13. **Exercise 15.B.10(d), hint.** "An equilibrium at the no-transfer situation where consumer 1
    gets an even lower level of utility" is proved with "no higher" (`≤`):
    `exercise_15_B_10d_lower_eqm` (hypotheses: (15.B.7)'s standing hypotheses, `ω₁ ≥ 0`, `z ≥ 0`).
    The exercise's claim itself (a transfer paradox implies two equilibria with different
    allocations before the transfer) is proved in full (`exercise_15_B_10d`). The parenthetical "not
    more generally" is a remark.

14. **Exercise 15.C.1(c).** The two-consumer economy `TCEconomy` uses the budget of Section 15.C as
    formalized in `RCEconomy` (no constraint `x₁ ≤ L̄ᵢ`; leisure beyond the endowment is paid for from
    profit income). In the example (`exercise_15_C_1c`, `f(z) = 7z^{1/7}`, quasilinear utilities)
    consumer 2 consumes more leisure than his endowment in both equilibria. Multiplicity needs an
    inferior good or a strongly decreasing-returns firm; the example uses the latter. Under constant
    returns `f(z) = αz` the equilibrium allocation is unique (`exercise_15_C_1c_crs`) and
    `w/p = α` when output is positive (`exercise_15_C_1c_crs_wage`); with zero output every
    `w/p ≥ α` supports the same allocation, so prices need not be unique.

15. **Exercise 15.D.6(c)-(d).** "The unit-dollar isoquants intersect at most once under factor
    intensity" is false for the model as formalized (`TwoByTwo.IsModel` with factor intensity): for
    the Leontief technologies at `p = (1, 2)` both isoquants contain `(2, 1)` and `(3, 1)`
    (`exercise_15_D_6c_counterexample`). Corrected statement (`TwoByTwo.exercise_15_D_6c`): if in
    addition every factor ratio is an expansion ray (`TwoByTwo.RaySurjective`) and `t ↦ fⱼ(t, 1)` is
    differentiable (`TwoByTwo.RayDifferentiable`), two strictly positive intersection points
    coincide; the Cobb-Douglas model satisfies both (`exercise_15_D_6c_cdModel`). In (d) existence
    of the specialized equilibrium strictly outside the cone uses ray-surjectivity (the Leontief
    model has no specialized equilibrium with `w ≫ 0` there); the uniqueness theorems need no extra
    hypothesis but determine `w` only up to the factor ratio of the produced good, which pins `w`
    down when that ratio is injective (Cobb-Douglas, Exercise 15.D.8).

16. **The Pareto set of factor allocations, p. 533, and Exercise 15.D.1(a).** The Pareto set is
    formalized as the efficient factor allocations (`TwoByTwo.IsEfficientAllocation`); the book's
    tangency as support by common factor prices `w ≫ 0`. Supported allocations are efficient under
    `IsModel` alone (`TwoByTwo.supported_isEfficient`); interior efficient allocations are supported
    for technologies that are ray-surjective and differentiable along rays
    (`TwoByTwo.efficient_isSupported`). Exercise 15.D.1(a) and the diagonal claim are proved for
    interior supported allocations without the factor intensity condition
    (`TwoByTwo.exercise_15_D_1a`, `TwoByTwo.diagonal_pareto_set`) and for the Pareto set itself under
    the smoothness hypotheses (`TwoByTwo.exercise_15_D_1a_pareto`,
    `TwoByTwo.diagonal_pareto_set_efficient`). Footnote 16 is proved for interior equilibria before
    and after the price change with the intensity ranking assumed only at the initial equilibrium
    (`TwoByTwo.footnote_16`).

17. **Exercise 15.D.1(b).** False as printed: with the Leontief technologies and `z̄ = (3, 3)` the
    allocations `((1, 1/2), (2, 5/2))` and `((2, 1), (1, 2))` are both efficient, distinct and on the
    same ray from firm 1's origin, while the Pareto set is not the diagonal
    (`exercise_15_D_1b_counterexample`). Corrected: for technologies differentiable along rays the
    factor intensities are strictly decreasing in the relative factor price
    (`TwoByTwo.relRatio_strictAnti`), both fall and firm 1's input vector rises in both coordinates
    as `w₁/w₂` rises (`TwoByTwo.exercise_15_D_1b_monotone`), and a ray from either origin meets the
    interior supported allocations at most once (`TwoByTwo.exercise_15_D_1b`); instance
    `exercise_15_D_1b_cdModel`.

18. **Exercise 15.D.4(b), general model.** Proved for any model with factor intensity for
    equilibria with strictly positive factor prices (`TwoByTwo.exercise_15_D_4b_general`): any two
    have proportional prices and the same outputs and consumption. `TwoByTwo.IsModel` does not
    constrain `aⱼ(w)` unless `w ≫ 0`, so equilibria with a zero factor price are covered only in the
    Leontief instance (`exercise_15_D_4b`).
