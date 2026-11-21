# Corrections and departures

Each item states what MWG prints, what is proved, and the Lean names. Page references are to
the printed book.

1. **Supply derivative, p. 319.** The book states that with strictly convex `cⱼ` and `cⱼ' → ∞`,
   `qⱼ'(p) = 1/cⱼ''(qⱼ(p)) > 0` at every `p > cⱼ'(0)`. Strict convexity allows `cⱼ'' = 0` at
   isolated points, where supply is not differentiable. Counterexample: `c'(q) = 2 + (q - 1)³`
   (`cubicFirm`), whose supply is not differentiable at `p = 2`
   (`supply_not_differentiable_example`). Corrected statement: the formula holds where
   `cⱼ''(qⱼ(p)) > 0` (`QLFirmStrict.supply_hasDerivAt`). The same hypothesis is used for the
   formula for `p*'(0)` on p. 324 (`example_10_C_1_formula`).

2. **Proposition 10.D.2, p. 327, and existence with convex costs.** The second welfare theorem
   presupposes that a competitive equilibrium exists, and Section 10.C proves existence only for
   strictly convex costs with `cⱼ' → ∞`. We prove existence for merely convex costs (`c' > 0`,
   `c'' ≥ 0`) by maximizing aggregate surplus on a compact set (`optimalLevels_exist`,
   `ql_eqm_exists_convex`, `ql_competitiveEqm_exists_convex`; the gap condition is not needed
   for existence) and uniqueness of the price and of individual consumptions under
   `maxᵢ φᵢ'(0) > minⱼ cⱼ'(0)` (`ql_eqm_unique_convex`). Proposition 10.D.2 therefore holds
   without presupposing an equilibrium (`proposition_10_D_2_convex`; instances
   `inst_convex_existence`, `inst_proposition_10_D_2_convex`).

3. **Exercise 10.B.1(b).** The equivalence of weak and strong Pareto efficiency is proved
   without the interiority assumption (`exercise_10_B_1b_general`); the stated version is
   `exercise_10_B_1b`. Interiority is therefore not needed when `Xᵢ = ℝ^L_+` and utilities are
   continuous and strongly monotone; part (c)'s example drops strong monotonicity
   (`exercise_10_B_1c`).

4. **Exercise 10.B.2.** Proved for every price vector, not only `p* ≫ 0`
   (`exercise_10_B_2`).

5. **Lemma 10.B.1.** Only `p_k > 0` (and shares summing to one) is used (`lemma_10_B_1`); the
   book's `p ≫ 0` version is `lemma_10_B_1_strictlyPositive`.

6. **Exercise 10.C.8(b).** The weakest sufficient condition for profits to fall for every
   demand with `x' ≤ 0` is `c_α > q c_qα` (`exercise_10_C_8b`, with the book's `c_α > 0`). The
   book adds that if the condition fails there are demands for which profits increase. This
   holds when `q c_qα > c_α`, but in the boundary case `q c_qα = c_α` profits are unchanged to
   first order for a vertical demand and fall for every other demand
   (`exercise_10_C_8b_converse`).

7. **Exercise 10.F.3.** As printed (`φ'' < 0`), the cost `K + φ(q)` has no efficient scale when
   `K > 0` and `φ(0) ≥ 0`: average cost falls from `q` to `2q` (`exercise_10_F_3_printed`). We
   use `φ'' > 0`, as in (10.F.1). The question "which tax raises more revenue after the
   long-run adjustment" has no unconditional answer: the lump-sum tax leads to a lower price and
   larger firms (`exercise_10_F_3_scale`, `exercise_10_F_3_prices`); with perfectly inelastic
   demand the ad valorem tax raises more (`exercise_10_F_3_inelastic`), but for an elastic
   demand the lump-sum tax raises more (`exercise_10_F_3_counterexample`: revenues `3/10`
   against more than `17/10`).

8. **Exercise 10.F.7.** The book asks to show that the short-run cost curve has a kink at the
   long-run equilibrium when a factor can be increased but not decreased. This is true with
   fixed proportions (`exercise_10_F_7_leontief`, `exercise_10_F_7_leontief_kink`, where
   short-run supply is vertical over a range of prices, `exercise_10_F_7_vertical_supply`),
   but false with smooth substitution: for `√(z₀z₁)` the short-run cost is differentiable at
   the long-run output with derivative equal to the long-run marginal cost
   (`exercise_10_F_7_cd_shortRun`, `exercise_10_F_7_cd_smooth`); only the slope of marginal
   cost jumps.

9. **Exercise 10.E.2.** The identity `∫₀^{x(p̂)} [P(s) - p̂] ds = ∫_{p̂}^∞ x(s) ds` is proved
   through the common value `CS(p̂)`, by the fundamental theorem of calculus and the envelope
   theorem `CS'(p) = -x(p)`, not by the change of variables and integration by parts the book
   suggests (`exercise_10_E_2`, `eq_10_E_7`, `eq_10_E_8`).

10. **Exercise 10.F.2(b).** The short run keeps the number of firms fixed and treats the fixed
    cost `K` as sunk, so a firm supplies along its marginal cost `α + 2βq` (as in
    Example 10.F.1); the book does not say whether `K` is sunk (`exercise_10_F_2b_supply`).

11. **Exercise 10.F.4.** The cost function is an abstract `c(w, q)` that is nondecreasing,
    homogeneous of degree one and concave in `w` (the properties of Proposition 5.C.2(i)-(ii),
    proved in Chapter 5), with an efficient scale for every `w` (`exercise_10_F_4`).

12. **Example 10.C.1.** The equilibrium producer price `p*(t)` is defined and unique for taxes
    in `(-minⱼ cⱼ'(0), maxᵢ φᵢ'(0) - minⱼ cⱼ'(0))` (`taxRange`, `taxPrice_spec`,
    `taxPrice_unique`); this includes small subsidies, needed for a two-sided derivative at
    `t = 0`. The derivative formula (10.C.8) is proved under the book's differentiability
    assumptions on `x` and `q` with `x' < 0` (`eq_10_C_8`); differentiability of `p*` is
    proved, not assumed. The quantity traded falls strictly (the book says weakly; here costs
    are strictly convex).

13. **Exercise 10.C.3.** Proved for costs with `c' > 0` and `c'' ≥ 0` (the standing assumptions
    of Section 10.C), under which the output constraint binds. Part (c) shows that the
    cost-minimizing outputs maximize profit at `p = C'(q)` (`exercise_10_C_3c`); with strictly
    convex costs they are the unique supplies, so `C' = q⁻¹` (`exercise_10_C_3c_strict`).

14. **Exercise 10.C.4.** Proved for consumers of Section 10.C (`QLConsumer`). Part (a)'s
    characterization uses only concavity; parts (b)-(c) also use the existence of the optimal
    allocation, which follows from boundedness of `φ`.

15. **Exercises 10.C.8-10.C.11, 10.F.5(b), 10.G.3-10.G.5.** These comparative statics are
    formalized as derivative computations along differentiable equilibrium paths (the
    differentiability that the implicit function theorem provides, assumed as in the book), with
    the equilibrium identities required on a neighbourhood. For Exercise 10.C.5 the paths are
    derived in the model of Section 10.C (`exercise_10_C_5_derived`, via `eq_10_C_8`), and for
    Exercise 10.E.1(a) the tariff path is derived from a one-variable implicit function theorem
    (`implicit_path`, `implicit_1d`, `exercise_10_E_1a_derived`); the general
    `exercise_10_C_5` and `exercise_10_E_1_deriv` keep the path as a hypothesis.

16. **Exercise 10.E.3(b).** The Ramsey rule holds unconditionally at a local constrained optimum
    with continuously differentiable demands and a nonzero marginal revenue: the multiplier is
    obtained from Mathlib's Lagrange theorem and `λ ≠ -1` follows from `x_ℓ > 0`
    (`exercise_10_E_3b_lagrange`, `ramsey_strict`, instance `inst_exercise_10_E_3b`).
    `exercise_10_E_3b` is the derivation from given Lagrange conditions.

17. **Exercise 10.G.1.** The equilibrium is stated by the maximization conditions of consumers
    and firms (`IsGroupEqm`); the `(I + J + 1)M` first-order equations are proved necessary
    (`group_consumer_foc`, `group_firm_foc`).

18. **Conventions.** Derivatives of `φᵢ` and `cⱼ` on `x ≥ 0` are taken within `[0, ∞)`
    (one-sided at `0`), matching the book's domain. The quasilinear economy is an instance of
    Definition 10.B.3 with goods `0` (numeraire) and `1` (good `ℓ`). Exercise 10.C.1 uses
    strictly positive bundles (`ln 0` is undefined).
