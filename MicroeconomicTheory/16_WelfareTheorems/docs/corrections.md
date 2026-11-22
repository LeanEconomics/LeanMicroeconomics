# Corrections and departures

Each item states what MWG prints, what is proved, and the Lean names. Page references are to the
printed book. Items 1-6 are corrections of printed claims (each with a counterexample); items
7-16 are departures in modelling or method.

## Corrections

1. **A price equilibrium with transfers is a price quasiequilibrium with transfers (p. 552).**
   Definition 16.D.1 requires `p ≠ 0` and Definition 16.B.4 does not, so the claim fails for
   `p = 0`. In `priceEqmCounterEconomy` (one consumer indifferent among all bundles, one firm with
   `Y = ℝ`) the allocation `x* = y* = 0` is a price equilibrium with transfers at `p = 0` but is
   not a price quasiequilibrium with transfers for any price vector
   (`priceEqmCounterEconomy_counterexample`). True statements: with `p ≠ 0`
   (`PrefEconomy.IsPriceEqmWithTransfers.isPriceQuasiEqm`), and under local nonsatiation with
   `I ≥ 1`, where `p ≠ 0` is automatic (`PrefEconomy.IsPriceEqmWithTransfers.isPriceQuasiEqm_of_lns`).

2. **Proposition 16.D.3 (p. 555) needs local nonsatiation.** As printed (convex `Xᵢ ∋ 0`,
   continuous preferences, `w ≫ 0`) it is false: in `satiatedEconomy` (two consumers indifferent
   among all bundles) a price quasiequilibrium with `w = (1/2, 3/2)` gives consumer 1 a bundle
   costing `1 > w₁`, so it is not a price equilibrium with these wealth levels
   (`proposition_16_D_3_needs_lns`). With the standing assumption of p. 552 ("locally nonsatiated
   preferences, which we always make") it holds (`proposition_16_D_3`).

3. **Proposition 16.AA.1 (p. 573) and the closedness claim of p. 574.** The aggregate production
   set `Y = ∑ⱼ Yⱼ` is assumed convex but not closed, and the text asserts that irreversibility
   "yields the closedness of `Y`". Both fail: `aaCounterEconomy` (one consumer on `ℝ²₊`,
   `Y₁ = {0} ∪ {(a, b) : a ≥ 0, ab ≤ -1}`, `Y₂ = -ℝ²₊`) satisfies every printed assumption (closed
   `Xᵢ` bounded below, closed `Yⱼ`, `Y` convex with `0 ∈ Y`, no free lunch, irreversibility), but
   `Y = {y₂ < 0} ∪ {(y₁, 0) : y₁ ≤ 0}` is not closed and the feasible set is unbounded
   (`proposition_16_AA_1_counterexample`, with `aaCounter_agg`). With `Y` closed added, `A` is
   bounded (`proposition_16_AA_1`); the closedness and nonemptiness parts hold as printed
   (`exercise_16_AA_1`, `proposition_16_AA_1_nonempty`).

4. **Footnote 18 (p. 563).** "The assumption of strictly positive gradients ... implies that the
   constraint qualification ... is satisfied." For the constraint qualification of Section M.K
   (linearly independent gradients of the binding constraints, Theorem M.K.2) this is false: in
   `footnote_18_counterexample` (two consumers, one good, `ū₂ = 1`) the solution has `x₁ = 0` and
   four binding constraints whose gradients sum to zero. The Kuhn-Tucker conditions (16.F.2)-(16.F.3)
   nevertheless hold at every solution (`exercise_16_F_2`, proved from the Fritz John conditions
   `fritz_john` and a direct argument for the degenerate case).

5. **Exercise 16.G.4 (p. 576)** asks to show that "under the general conditions of Section 16.G"
   with one consumer some marginal cost price equilibrium is an optimum. Those conditions do not
   ensure that an optimum exists: in `exercise_16_G_4_needs_optimum` (two firms `F₁ = y₁ + 2y₂`,
   `F₂ = 2y₁ + y₂`, gradients `≫ 0`, `Fⱼ(0) = 0`, `ω̄ = 0`) the two plans together produce `(1, 1)`
   from nothing and no allocation is Pareto optimal. With a nonempty compact feasible set the claim
   holds (`exercise_16_G_4`).

6. **Definition 16.G.1 (p. 569), the wealth condition.** As printed,
   `∑ᵢ wᵢ = ∑ᵢ p₁x*₁ᵢ + (∑ᵢ p₂ᵢ)q* - p₁z*`; the definition is announced as the price equilibrium
   with transfers of the artificial economy, whose condition `∑ᵢ wᵢ = p·ω̄ + p·y*` reads
   `∑ᵢ wᵢ = p₁ω̄₁ + (∑ᵢ p₂ᵢ)q* - p₁z*`. Given market clearing the printed sum is smaller by `p₁z*`
   (`definition_16_G_1_wealth_gap`); with locally nonsatiated consumers the printed definition
   forces `p₁z* = 0` (`definition_16_G_1_printed_forces`), and the artificial-economy equilibrium of
   `definition_16_G_1_printed_counterexample` satisfies the corrected definition (`IsLindahlEqm`)
   but the printed one (`IsLindahlEqmPrinted`) for no wealth level. The rest of Example 16.G.3 uses
   the corrected definition (`lindahl_isParetoOptimal`, `footnote_23`, `lindahl_second_welfare`).

## Departures

7. **Proposition 16.F.1 (p. 566): weights.** The discussion before the proposition takes `λ ≫ 0`.
   The weights produced from the Pareto optimum are `λᵢ = δᵢ ≥ 0` with `λ_{i₀} = 1`; a weight can
   vanish only for a consumer with `xᵢ = 0` (`proposition_16_F_1`, `section_16_F_constraints_bind`),
   for whom the marginal utility of wealth `αᵢ = 1/λᵢ` is undefined. The proposition is proved in
   this form.

8. **Preferences and the economy.** Chapter 16 works with rational preference relations `≿ᵢ` on
   consumption sets; `PrefEconomy` stores relations (`pref i x y` reads `x ≿ᵢ y`, as in Chapter 3),
   and utility economies are `PrefEconomy.ofUtility`. Allocations are Chapter 10's `Allocation`.
   Feasibility is the equality (16.B.1). The standing assumptions (`I, J > 0`, rationality, `Yⱼ`
   nonempty and closed) are hypotheses of the results that use them, and are dropped where not
   needed (e.g. `exercise_16_C_3b` does not use rationality; `exercise_16_E_1b` does not use
   `0 ∈ Yⱼ`; `exercise_16_E_1c` does not use local nonsatiation). Bridges: Chapter 10's competitive
   equilibrium (`isWalrasEqm_iff_competitiveEqm`), Chapter 15's exchange economy
   (`exchangeToPrefEconomy`, `exchange_isFeasible_iff`, `exchange_isDemandEqm_isPriceEqm`).

9. **Proposition 16.D.1.** The separating hyperplane step uses Chapter 3's Theorem M.G.2
   (`theorem_M_G_2_ii`), which needs `L ≥ 1`; this follows from local nonsatiation and `I ≥ 1`
   inside the proof (`proposition_16_D_1`). The consumption sets need not be convex, as printed.

10. **The pure exchange claims of p. 556** are proved with at least one disposal firm (the book's
    `J > 0`): `footnote_9`, `pureExchange_quasiEqm_isPriceEqm_of_interior`,
    `pureExchange_quasiEqm_isPriceEqm_of_strongMono` (from `exercise_16_D_3`).

11. **Exercise 16.D.4** (two goods, "the differentiable case is simpler") is proved for any number
    of goods `L ≥ 1`, without differentiability (`exercise_16_D_4`); the replica threshold `r₀` is
    the number of copies needed to realize an integer combination of preferred trades.

12. **Section 16.F.** Utilities and transformation functions are functions on `ℝ^L` with
    derivatives assumed exactly where used (often only at the allocation), instead of twice
    continuously differentiable functions on `ℝ^L₊`. `J ≥ 1` and `L ≥ 1` are assumed where the
    normalization `δ₁ = 1` needs them (`exercise_16_F_2`). Strong monotonicity and free disposal are
    derived from the gradient assumptions (`strictMono_of_grad_pos`, `mono_of_grad_pos`).

13. **Exercise 16.F.4.** (16.F.4)-(16.F.6) are derived by the first-order perturbation argument at
    interior solutions of (16.F.7), (16.F.8) and (16.F.1) (`exercise_16_F_4_i`, `_ii`, `_iii`). The
    book's route to (16.F.6) through problem (16.F.9) in the value functions `u(x̄)`, `f(ȳ)`
    presupposes differentiable value functions and envelope identities that are not established in
    the text; it is not formalized.

14. **Figures and graphical exercises.** Figures 16.C.1, 16.D.2, 16.D.4-16.D.5, 16.E.1, 16.G.1 and
    16.G.2 and Exercises 16.D.2, 16.E.1(a) and 16.G.3 are drawn or posed without formulas; we give
    concrete economies with the stated properties. In Exercise 16.G.3 the consumer values only the
    output (`u = x₃`), and uniqueness is proved among marginal cost price equilibria with efficient
    production (`F(y*) = 0`); condition (16.G.1) alone does not determine the output level.

15. **Exercise 16.E.1(b)** is proved in the form "a feasible allocation that is not Pareto optimal
    has its utility vector in the interior of `U`" (`exercise_16_E_1b_interior`), which gives the
    printed statement (`exercise_16_E_1b`); the hint's `U' = U ∩ ℝ^I₊` is `exercise_16_E_1b_hint`.

16. **Exercise 16.G.5.** Utilities are compared through `√(ef)` (`α = 1/2`); the marginal cost
    price equilibrium of (e) is verified with wages `w_L = w_T = 1/2` (the values implied by
    competitive food production with `L_f = T_f`), and the equilibrium education level is shown to be
    the unique solution of the market-clearing equation (`exercise_16_G_5e_level`).
