# Corrections and departures

MWG, Chapter 23. Lean names are relative to `MWG.MechanismDesign`. Items 2, 3, 5, 7, 12, 16,
20-24, 26 and 30 are false printed claims, each refuted by a counterexample theorem and replaced by
a corrected statement; the others are departures (extra or dropped hypotheses, different proof
routes, readings of ambiguous statements).

1. **Proposition 23.C.3, p. 874 (Gibbard-Satterthwaite); Proposition 23.BB.2, p. 914.** The
   proof needs at least one agent (`Nonempty ι`), which MWG leave implicit. Finiteness of `X`
   is not used: `proposition_23_C_3` holds for any `X` (`footnote_23_19`, as footnote 19 says),
   and likewise Proposition 23.BB.2 needs no finiteness (`proposition_23_BB_2`).
2. **Corollaries 23.C.1-23.C.2, pp. 875-876, converse.** "It is again immediate that a
   dictatorial social choice function is truthfully implementable" is false once `𝒫 ⊆ 𝓡ᵢ`
   allows indifference: a dictator who is indifferent can have his tie broken by another
   agent's report. `tieBreakRule` (agent 0's best alternative, and agent 1's worst alternative
   when agent 0 is totally indifferent; three alternatives, two agents) is dictatorial and onto
   but not strategy-proof (`corollary_23_C_1_converse_false`), and it is dictatorial on
   `f(Θ) = X` (`corollary_23_C_2_converse_false`). Corrected: the converses hold when
   `𝓡ᵢ ⊆ 𝒫` (`strategyProof_of_dictatorial`, `strategyProof_of_dictatorialOn`).
3. **Clarke mechanism, p. 878.** "The transfer is negative if agent `i`'s announcement changes
   the project decision" is false with ties: two agents, `K = Bool`, agent 0 values `true` at
   `1`, agent 1 is indifferent, `k₋₀* = false`; agent 0 is pivotal but his transfer is `0`
   (`clarke_pivotal_zero_tax`). Corrected: the transfer is `0` when the agent is not pivotal and
   `≤ 0` always (`clarke_transfer_props`).
4. **Proposition 23.C.5, (23.C.10), p. 879.** MWG's type `θᵢ'` has valuation `-∞` off two
   projects, which is not a real-valued function and so not in `𝒱`. The proof uses
   `-∑_{j≠i} vⱼ(k, θⱼ) - 1` there instead (`proposition_23_C_5`).
5. **Proposition 23.C.6, p. 880; Exercise 23.C.10(a), p. 920.** Stated without `I ≥ 2` and
   `|K| ≥ 2`, the proposition is false: with one project, or with one agent, `t = 0` is
   efficient, budget balanced and strategy-proof (`proposition_23_C_6_false_one_project`,
   `proposition_23_C_6_false_one_agent`). Corrected statement with `I ≥ 2` and two distinct
   projects: `proposition_23_C_6` (MWG omit the proof; ours shows that a Groves scheme with
   budget balance forces `V*(θ) = ∑ᵢ Vᵢ(θ₋ᵢ)`, whose `I`-fold mixed difference vanishes,
   `mixedDifference_eq_zero`, and exhibits types where it does not). In the same way the "only
   if" of Exercise 23.C.10(a) needs `I ≥ 2` (`exercise_23_C_10a_only_if_false_one_agent`) and
   the richness hypothesis of Proposition 23.C.5 (`exercise_23_C_10a_only_if`).
6. **The differentiable case, pp. 881-882; Exercises 23.C.9, 23.C.10(c)-(d), p. 920.**
   (a) Valuations, project rule and transfers are functions on all of `ℝ` (resp. `ℝ^I`);
   strategy-proofness and efficiency are required on the box of types only. (b) The `I = 2`
   budget-balance impossibility is not proved through (23.C.16)-(23.C.17): differentiating
   (23.C.16) again takes second derivatives of `tᵢ` and `k*`, but `f` is only `C¹` and the
   implicit function theorem gives `k*` only `C¹` when `v` is `C²`. We prove it through the
   decomposition `V*(θ) = -h₁(θ₂) - h₂(θ₁)` and a strictly nonzero mixed difference of `V*`
   (`differentiable_case_no_budget_balance`, `exercise_23_C_10c_decomposition`,
   `exercise_23_C_10d`). (c) Exercise 23.C.9 does not need `∂²v/∂k² < 0`, and its "only if" for
   monotonicity needs no differentiability (`exercise_23_C_9`).
7. **Exercise 23.E.2(a)-(b), pp. 921-922.** As printed ("no social choice function that is
   dominant strategy incentive compatible and interim individually rational"; "... Bayesian
   incentive compatible and ex post individually rational") the claims omit ex post efficiency
   and are false: the no-trade rule is dominant strategy and Bayesian incentive compatible,
   budget balanced and ex post individually rational (`exercise_23_E_2_literal_false`).
   Corrected, with ex post efficiency: `exercise_23_E_2a`, `exercise_23_E_2b`, from Proposition
   23.E.1.
8. **Exercise 23.E.7(a), pp. 922-923.** "Ex post efficient" must mean that the trading rule is
   efficient, without budget balance: with budget balance no such `f` exists (Proposition
   23.E.1) and (a) would be vacuous. `exercise_23_E_7a` is proved in that reading.
9. **Footnote 41, p. 895.** The equivalence "`(θ̲₁, θ̄₁) ∩ (θ̲₂, θ̄₂) ≠ ∅` iff `θ̄₂ > θ̲₁` and
   `θ̄₁ > θ̲₂`" needs nondegenerate intervals (`footnote_23_41`).
10. **Proposition 23.E.1 (Myerson-Satterthwaite), p. 895.** All requirements (efficiency,
    budget balance) are imposed on `Θ` only, the trading rule may break ties `θ₁ = θ₂` freely,
    and integrability is explicit. Besides MWG's proof (`proposition_23_E_1_mwg`, item 11) we
    give a second route that needs no densities (`proposition_23_E_1_general`, `ms_core`): by
    Proposition 23.D.2 a BIC rule's interim transfers differ by constants from those of the VCG
    rule `t₀ = θ₁y₁`, `t₁ = -θ₀y₁` (`msVcgT`, `ms_vcg_bic`); budget balance and interim IR at
    `θ̄₀`, `θ̲₁` then give `E[(θ₁ - θ₀)⁺] ≤ E[(θ₁ - θ̄₀)⁺] + E[(θ̲₁ - θ₀)⁺]`, which fails by a
    strict pointwise inequality on a box of positive probability in the overlap. The statement
    with densities is `proposition_23_E_1`.
11. **Proof of Proposition 23.E.1, pp. 895-896.** Every display is correct as printed if
    `φᵢ = 0` outside `[θ̲ᵢ, θ̄ᵢ]` and `Φᵢ = 0` below, `1` above (the `TypeDensity` convention);
    this matters when `θ₂ < θ̲₁` (the inner interval `[θ̲₁, Min{θ₂, θ̄₁}]` is reversed and the
    inner integral is `0`) and when `θ̄₁ > θ̄₂`. MWG evaluate `∫(θφ + Φ) = [θΦ]` and
    `∫[(θ₂ - θ̄₁)φ₂ + Φ₂ - 1] = [(θ₂ - θ̄₁)(Φ₂ - 1)]` by the fundamental theorem of calculus,
    which needs `Φ' = φ` (continuous `φ`); we prove both for measurable densities by Fubini
    (`mss_integral_cdf`, `mss_integral_key`). The expectations `E[y₂J₂]`, `E[y₂K₁]` in Step 1
    are assumed to exist (they do for bounded measurable `y`: `mss_integrable_y_mul`).
12. **Proposition 23.D.2, proof, p. 888.** "`Uᵢ'(θᵢ) = v̄ᵢ(θᵢ)` for all `θᵢ`" is false at jumps
    of `v̄ᵢ`: one agent on `[0, 1]`, `v̄(θ) = 1{θ ≥ 1/2}`, `t̄ = -v̄/2` is incentive compatible
    but `U(θ) = max(0, θ - 1/2)` is not differentiable at `1/2`
    (`proposition_23_D_2_derivative_false`). Only the integral form (23.D.12) is needed; it is
    proved without differentiability of `U` (`integral_eq_of_slope_bounds`,
    `proposition_23_D_2`).
13. **Section 23.D, pp. 884-887.** "Dominant strategy implementation implies Bayesian
    implementation" needs the conditional expectations to exist (integrable payoffs:
    `isBayesianNash_of_dominant`, `implementsInBNE_of_dominant`, `bayesianIC_of_strategyProof`);
    with finitely many types this is automatic (`agv_finite`). The budget-balancing `hᵢ` of
    (23.D.9) divides by `I - 1` and needs `I ≥ 2` (`agv_budgetBalanced`).
14. **Proposition 23.D.3 and (23.D.14)-(23.D.16), pp. 890-891.** Revenue equivalence needs no
    densities, only that each type distribution is concentrated on its interval
    (`proposition_23_D_3`). The "integration by parts" of p. 890 is replaced by a Fubini
    identity that needs only integrability on the interval (`TypeDensity.integral_integral_eq`).
    (23.D.15)-(23.D.16) assume that `E[yᵢ(θ)Jᵢ(θᵢ)]` exists (it does in the instance
    `eq_23_D_16_instance`).
15. **Exercises 23.C.2, 23.C.5, 23.C.7, pp. 918-919.** (a) Exercise 23.C.2 holds for majority
    voting functions that depend only on ordinal preferences (`OrdinalSCF`, as in Section 21.E);
    with cardinal types a tie-break by intensity breaks it: two agents, `f(θ) = x₁` iff
    `θ₁ + θ₂ ≥ 0`, agent 1 of type `1` facing `-2` gains by announcing `3`
    (`exercise_23_C_2_cardinal`). (b) Exercise 23.C.5's rule is any selection of a Condorcet
    winner (unique by the median voter theorem). (c) Exercise 23.C.7 assumes transitivity of the
    social preferences at the profiles that arise and that the `F`-maximal alternative is unique
    (MWG's set-valued `f(θ) = {x : …}` is a singleton).
16. **Proposition 23.F.1, p. 899; Exercise 23.F.1, p. 923.** "Ex ante efficient in `F` implies
    interim efficient in `F`" is false when types can have probability zero: one agent,
    `θ` uniform on `[0, 1]`, `u = x`, `F = {0, 1{θ = 1/2}}`; `f ≡ 0` is ex ante but not interim
    efficient (`proposition_23_F_1_false`). Corrected: an ex ante efficient `f` has no interim
    improvement that is strict on a set of types of positive probability
    (`proposition_23_F_1`); if every type has positive probability, ex ante efficiency implies
    interim efficiency (`proposition_23_F_1_pointMass`). Exercise 23.F.1 is proved for finite
    type spaces and an `F_IR` closed under ex post improvements (which the ex post and interim
    sets are); its interim part needs positive probabilities by the same counterexample
    (`exercise_23_F_1_exAnte`, `exercise_23_F_1_interim`). For arbitrary measurable type spaces
    the ex ante part is proved with `f` compared to the incentive feasible social choice
    functions whose ex post utilities are measurable and integrable, so that their ex ante
    utilities exist (`WcRegular`, `exercise_23_F_1_exAnte_general`).
17. **Examples 23.F.1-23.F.2, pp. 900-905.** (a) Example 23.F.1: MWG's implicit function
    theorem argument for monotonicity of `e(·)` (p. 902) is replaced by monotone comparative
    statics (`oc_maximizer_mono`, `oc_maximizer_monotoneOn`): with `g` strictly increasing, `J`
    nondecreasing and unique maximisers, `e(·)` is nondecreasing. Derivative hypotheses on `v`,
    `g` are replaced where possible by their consequences; integrability is explicit.
    (b) Example 23.F.2: feasibility is required on `Θ`; the competing social choice functions
    are those whose expectations exist (`OptAuctionFeasible`); ties in (23.F.9) are left free
    and optimality is stated for any pointwise maximiser (`example_23_F_2`, `eq_23_F_9`,
    `eq_23_F_9_converse`). For the completion into a feasible mechanism with general densities
    (`example_23_F_2_general`) the rule `oaRule` breaks ties `Jᵢ = maxₖ Jₖ` by a fixed order of
    the bidders (lowest index wins) and keeps the good when all `Jᵢ ≤ 0`; this keeps `yᵢ`
    nondecreasing in `θᵢ`, so MWG's remark that ties have probability zero (which needs more
    than `Jᵢ` nondecreasing, e.g. no flat stretches of `Jᵢ`) is not used.
    (c) Footnote 48: interiority is proved for every optimal feasible contract, almost
    everywhere, assuming (as MWG's standing assumptions give) `v'(0) > 0`, `g'(0) = 0` and a
    feasible contract solving the relaxed problem pointwise (`footnote_23_48`); MWG's
    assumptions are not shown to produce such a contract in general (they do in the instance,
    `footnote_23_48_instance`).
18. **Examples 23.B.3-23.B.4, pp. 861-863.** Types are real numbers; MWG's type sets
    (`[0, ∞)`, `{θ̄ᵢ}`, `[θ̲ᵢ, θ̄ᵢ]`) are subsets and ex post efficiency restricts to them. In
    Example 23.B.3 the conditions (23.B.1)-(23.B.2) are sufficient ("is ex post efficient if":
    `example_23_B_3_efficient`); the exact characterisation allows either project level when
    `∑θᵢ = c` (`example_23_B_3_efficient_iff`).
19. **Section 23.B auctions, pp. 863-869; Exercise 23.B.4, p. 918.** Bayesian Nash equilibria
    are required for types in `[0, 1]` and bids `b ≥ 0` (`IsBNEOn`). Example 23.B.5's best
    response divides by `α₂` and so needs `α_j > 0` (`example_23_B_5_bestResponse`). Exercise
    23.B.4(a) asks for "a" linear equilibrium: the Chatterjee-Samuelson equilibrium
    `b₁ = 2θ₁/3 + 1/4`, `b₂ = 2θ₂/3 + 1/12` is verified (`exercise_23_B_4a`); other linear
    equilibria are not classified.
20. **Definition 23.AA.1, p. 910.** As printed ("every equilibrium yields `f`") there is no
    existence requirement, so strong implementation does not imply implementation, contrary to
    the remark on p. 912: one agent, one type, `X = ℕ`, `u(x) = x`, "announce `n`, get `n`" has
    no dominant strategy equilibrium, so every equilibrium "yields" `f ≡ 0`
    (`definition_23_AA_1_literal_counterexample`). `StronglyImplements` is implementation plus
    the printed condition (`EveryEquilibriumYields`), and then
    `StronglyImplements.implements`, `stronglyImplements_strategyProof` hold.
21. **Appendix A, p. 911.** "Strict dominance is always the case in any environment in which
    agents' preferences never involve indifference" is false: one agent, `X = Bool` with
    `true ≻ false`, messages `0`, `1` giving `true` and `2` giving `false`; announcing `0` is
    dominant but not strictly dominant (`noIndifference_not_strictlyDominant`). True instead:
    without indifference all dominant strategy equilibria yield the same outcomes
    (`dse_outcome_eq`), so dominant strategy implementation is strong
    (`strong_of_noIndifference`).
22. **Example 23.AA.1, p. 912.** "Both agents always announce `θ_H`" is not a second Bayesian
    Nash equilibrium of the expected externality mechanism: against it, announcing `θ_L` raises
    the expected transfer by `-λθ_L > 0` and leaves the (certain) project unchanged; MWG's
    comparison of `(λθ_L + (1-λ)θ_H) + hᵢ(θ_H)` with `(1-λ)θ_H + hᵢ(θ_H)` has the wrong sign
    (`example_23_AA_1_alwaysHigh_not_BNE`). Truth telling is the unique pure strategy Bayesian
    Nash equilibrium (`example_23_AA_1_unique`).
23. **Appendix B, pp. 913-915; Exercises 23.BB.2-23.BB.3, p. 925.** (a) Definition 23.BB.1's
    strong implementation, as printed, has no existence requirement, and then Proposition
    23.BB.1 is false: one agent, two types, `u(x, θ) = x` on `X = ℕ`, "announce `n`, get `n`"
    has no Nash equilibrium, so it "strongly implements" the non-monotonic `f(true) = 0`,
    `f(false) = 1` (`definition_23_BB_1_literal_counterexample`). `StronglyImplementsInNash`
    includes existence, as MWG's proof uses. (b) Proposition 23.BB.2 needs no finiteness of `X`
    (item 1). (c) Exercise 23.BB.2: dominant strategy implementability implies Nash
    implementability (`dominant_implementsInNash`) but not strong Nash implementability: the
    function of Exercise 23.C.8 is strategy-proof but not monotonic
    (`exercise_23_BB_2b_not_monotonic`, `exercise_23_BB_2b_not_strongly`). (d) Exercise 23.BB.3:
    with `I ≥ 3` every social choice function is Nash implementable, so neither Groves property
    is necessary (`exercise_23_BB_3_weak_not_I`, `exercise_23_BB_3_weak_not_II`); for strong
    implementation monotonicity makes the outcome constant on `{k = 1}` and on `{k = 0}`, so (i)
    must hold and (ii) can never hold (`exercise_23_BB_3_strong_I`,
    `exercise_23_BB_3_strong_not_II`); such functions exist (`exercise_23_BB_3_strong_exists`).
24. **Appendix B, p. 915, Pareto correspondence.** "If `f(θ)` is the Pareto set for all `θ`,
    then `f` is monotonic" is false in general: with two agents and two alternatives, `x` is
    Pareto optimal while agent 1 strictly prefers it, its lower contour sets do not shrink when
    agent 1 becomes indifferent, but then `y` Pareto dominates `x` (`paretoSet_not_monotonic`).
    Corrected: the weak Pareto correspondence is monotonic (`weakParetoSet_monotonic`), and with
    a transferable private good, MWG's setting, so is the Pareto correspondence
    (`paretoSet_ql_monotonic`), which is then fully Nash implementable
    (`nash_ql_pareto_fullyImplements`).
25. **Exercises 23.D.4, 23.D.5, 23.D.6, 23.E.4, 23.E.5, 23.E.6, pp. 921-922.** Exercise
    23.D.4(a) is proved for types that win with positive probability (bids that never win are
    payoff irrelevant and not pinned down by the equilibrium conditions;
    `exercise_23_D_4a`); 23.D.4(a)-(b) and 23.D.5 are stated for a general nondecreasing
    winning-probability function `P(b)`. In 23.D.6 the probability that an individual of value
    `θ` is first in line is the independence formula `θⁿ`. In 23.E.4 trading times are
    deterministic and discounting enters as the trade "probability" `δ^(t-1)` (footnote 42);
    in 23.E.5 traders are finite measures of valuations; in (a)-(b) the market-clearing price is
    taken as given, and its existence is proved for type densities and any masses of buyers and
    sellers (`exercise_23_E_5_clearing`). In 23.E.6(b) the equilibrium is
    `b(θ) = 2θ/3`, unique among strictly increasing linear strategies
    (`exercise_23_E_6b_unique`; for constant strategies ties have positive probability and the
    mechanism's tie rule matters).
26. **Exercise 23.F.6(b), p. 924.** The printed objective `∫_{p(θ)}^{∞} x(s) ds + απ` (consumer
    surplus gross of the transfer) has no optimum for `α > 0`: raising every transfer by `c`
    keeps the scheme feasible and raises the objective by `αc`
    (`exercise_23_F_6b_printed_unbounded`). We use consumer surplus net of the transfer,
    `S(p) - t + απ`, as in Baron-Myerson (`bmWelfare`, `exercise_23_F_6b`); for `α > 1` that
    objective is unbounded and for `α = 1` transfers are irrelevant
    (`exercise_23_F_6b_alpha_ge_one`). Prices are restricted to `p ≥ 0` (MWG: `p > 0`).
27. **Exercise 23.F.7, p. 924 (Dana-Spier).** Participation is interim (`Uⱼ(θⱼ) ≥ 0`), market
    structures are deterministic, and the reduction to virtual welfare
    (`exercise_23_F_7_reduction`) holds for any `λ` and for different densities of the two
    firms (MWG: one common `C¹` density). The completion of the pointwise virtual-welfare rule
    by transfers into a feasible mechanism (`exercise_23_F_7_general`) needs only `λ > 1` and
    `Φⱼ/φⱼ` nondecreasing (MWG: increasing, with `C¹` densities); the rule `dsRule` breaks ties
    between market structures in a fixed order, and any selection works because the virtual
    cost is then strictly increasing.
28. **Example 23.BB.1, pp. 915-916, Figure 23.BB.1.** MWG give the allocations only in the
    figure. We make it concrete: Edgeworth box with endowment `(10, 10)`, `u₁ᶜ = ab`,
    `u₁ᴸ = min(a, b)`, `u₂ᶜ = (10 - a)(10 - b)`, `u₂ᴸ = min(10 - a, 10 - b)`, `xᶜ = (5, 5)`,
    `xᴸ = (4, 4)`, `y = (3, 3)`, `z = (9, 2)`, which reproduce every ordering read from the figure
    (`example_23_BB_1_figure`). In the figure the two Cobb-Douglas indifference curves through
    `xᶜ` are drawn crossing; our `xᶜ` is on the contract curve, which plays no role.
29. **Example 23.B.2, pp. 860-861, Figure 23.B.1.** MWG argue with offer curves and do not give
    preferences. We make the example concrete (`example_23_B_2`): endowments `ω₁ = (0, 1)`,
    `ω₂ = (1, 0)`, `u₁ = xy`; consumer 2's true type has `u₂ = xy` and the announced type the
    Leontief preference `min(x, 3y/2)` (monotone and convex, so in `𝓡_E`, but not smooth as
    drawn). Equilibrium prices are required to be strictly positive (`WmEq`). The Walrasian
    allocation is unique at both profiles (`example_23_B_2_truthful`,
    `example_23_B_2_misreport`), and consumer 2 gets `(3/4, 1/2)` instead of `(1/2, 1/2)` by
    misreporting. Ex post efficiency is the first welfare theorem under local nonsatiation
    (`wm_first_welfare`, `example_23_B_2_efficient`).
30. **Section 23.C, p. 875.** "A majority voting social choice function is both nondictatorial
    and truthfully implementable in dominant strategies" needs at least three agents, or a tie
    rule that does not follow one agent: with two agents, majority voting with ties broken by
    agent `0`'s preference is a majority voting function and agent `0` is a dictator
    (`majority_two_agents_dictatorial`). With rich types every majority voting function is
    nondictatorial when `I ≥ 3` (`majority_nondictatorial`), and majority voting with ties to
    `x₁` is nondictatorial for `I ≥ 2` (`majority_tieTrue_nondictatorial`,
    `remark_23_C_majority`).
