# Corrections and departures

Each item states what MWG prints, what is proved, and the Lean names. Page references are to
the printed book.

1. **Existence of a monopoly optimum, p. 385 and footnote 5.** MWG assumes `p`, `c` twice
   differentiable, `p(0) > c'(0)` and a unique `q° > 0` with `p(q°) = c'(q°)`, and says a
   solution of (12.B.2) "can be shown to exist"; footnote 5 uses the "fact" that `p(q) < c'(q)`
   for `q > q°`, which uniqueness of `q°` does not imply. Counterexample: `p(q) = 1 + 1/(1+q)²`,
   `c(q) = arctan(q − 1) − 1/(1+q)` (`p' < 0`, `c' > 0`, unique `q° = 1`), where profit is
   unbounded and no optimum exists (`footnote_12_5_counterexample`). Corrected: with `p' ≤ 0` and
   `p < c'` beyond `q°`, an optimum exists in `[0, q°]` (`footnote_12_5`); the same hypothesis
   gives `qᵐ < q°` (`monopoly_quantity_lt`).

2. **Proposition 12.C.1, proof (p. 389).** The deviations to `p_j − ε` and to
   `c + (p_k − c)/2` need not earn a positive profit when demand vanishes there (prices at or
   above `p̄`). The statement is true; the proof deviates to a price chosen by continuity of
   `(p − c)x(p)` (`bertrand_deviation`, `exercise_12_C_1`, `proposition_12_C_1`).

3. **Lemma 12.AA.1, "only if" (p. 418).** False. Condition (12.AA.1) uses the best-response
   payoff `π̂_i(q_{jt})`, which includes `a = q_{it}`; when `q_{it}` is itself the best response
   and the continuation gives player `i` less than `π_i(q*)/(1 − δ)`, the profile can be an SPNE
   while (12.AA.1) fails. Counterexample: `counterexample_12_AA` (stage game `cexG`, unique Nash
   equilibrium `(D, L)`, stationary path `(U, R)`, `δ = 1/2`). Corrected (iff): the Nash reversion
   profile is an SPNE iff `π_i(a, q_{-i,t}) + δπ_i(q*)/(1 − δ) ≤ v_i(Q, t)` for all `t`, `i`,
   `a ≠ q_{it}` (`nashReversion_spne_iff`); (12.AA.1) is sufficient (`lemma_12_AA_1_if`).

4. **Proposition 12.AA.2 (p. 420).** False: in the same example the Nash reversion profile is an
   SPNE at `δ = 1/2` but not at `δ' = 3/5` (`counterexample_12_AA`). Corrected: if (12.AA.1) holds
   at `δ > 0` it holds at every `δ' ∈ [δ, 1)` (`proposition_12_AA_2_corrected`).

5. **Exercise 12.AA.1 (p. 420).** False: in the same example player 1 gets `π₁(q) = 1 < 2 =
   π₁(q*)` on a stationary Nash reversion SPNE path (`counterexample_12_AA`). Corrected: if a
   stationary `q` with `π_i(q) < π_i(q*)` is sustained, then `q_i` is a best response to `q_{-i}`
   with margin `δ(π_i(q*) − π_i(q))/(1 − δ)` (`exercise_12_AA_1_corrected`); under MWG's
   characterization (12.AA.3) the claim holds (`exercise_12_AA_1_printed_condition`).

6. **Propositions 12.AA.1 and 12.AA.4 (pp. 419, 421; Exercise 12.AA.2).** False as printed.
   MWG assumes two players, actions in `ℝ`, `π_i` differentiable at the stage Nash equilibrium
   `q*` with `∂π_i(q*)/∂q_j ≠ 0` (and, for 12.AA.4, `π_i(q*) > π̲_i`); the proof of 12.AA.1 also
   invokes the envelope property (12.AA.6), that `π̂_i` is differentiable at `q_j*` with
   derivative `∂π_i(q*)/∂q_j`, which does not follow. Counterexample `sclG`: actions clamped to
   `[-1, 1]`, `π_1 = q_2 − q_1² − min(q_1, 0)|q_2|^{1/4}`, `π_2 = q_1 − q_2²`, with bounded
   payoffs, the unique Nash equilibrium `q* = 0`, best responses that exist, `π_i`
   differentiable at `q*` with cross partials `1`, and `π̲_i < π_i(q*)` (`sclG_hypotheses`); but
   `π̂_1(q_2) = q_2 + |q_2|^{1/2}/4`. For `δ ∈ (0, 1/5]` no Pareto improvement over `q*` is
   sustained by Nash reversion (`proposition_12_AA_1_false`); for `δ ∈ (0, 1/2000]` every SPNE
   gives player 1 at least `π_1(q*)` in every subgame (`sclG_spne_value_nonneg`), so no SPNE gives
   both players less (`proposition_12_AA_4_false`); both together, and emptiness of
   `LocalGameData sclG 0`, in `counterexample_12_AA_1_4`. Corrected: both propositions hold for
   every `δ ∈ (0, 1)` (bounded payoffs, actions in `ℝ`) under MWG's hypotheses plus the one-sided
   bound `π̂_i(q_j) ≤ π_i(q*) + ∂π_i(q*)/∂q_j·(q_j − q_j*) + o(q_j − q_j*)`
   (`proposition_12_AA_1_upper`, `proposition_12_AA_4_upper`; instances `scl_upper_instance_1`,
   `scl_upper_instance_4`). Given the other hypotheses this bound is equivalent to (12.AA.6)
   (`scl_env_of_upper`, `scl_upper_of_hasDerivAt`), so the envelope versions
   `proposition_12_AA_1`, `proposition_12_AA_4` (`LocalGameData`, instance `locG_data`) are the
   same result; `∂π_i(q*)/∂q_i = 0` is derived (`scl_own_partial_zero`). The hypothesis
   `π_i(q*) > π̲_i` of 12.AA.4 is not needed. Uniqueness of `q*` is not used.

7. **Proposition 12.D.2, first part (p. 403), and Exercise 12.D.2 (p. 405).** False as printed:
   a lower price may earn more than `p ∈ (c, pᵐ)` when `(p − c)x(p)` is not monotone on
   `[c, pᵐ]`. Counterexample: `cexDemand` with `c = 1`, `pᵐ = 103/2`, `p = 2`, `δ = 1/2`
   (`proposition_12_D_2_counterexample`). Corrected: the statements hold when no lower price
   earns more than `p`, e.g. when profit is nondecreasing on `[0, p]`
   (`bertrand_nashReversion_iff`, `exercise_12_D_2_corrected`,
   `proposition_12_D_2_part1_corrected`); Proposition 12.D.1 (`p = pᵐ`) is unaffected.

8. **Proposition 12.D.2, second part (pp. 403-404).** The statement is proved. MWG's argument
   stops at "`π_t ≤ 0` for all `t`"; the proof adds that every firm then earns zero in every
   period, which forces the lowest price to be `c` (`proposition_12_D_2_part2`). MWG's case
   split (i)/(ii) is replaced by a supremum argument.

9. **Exercise 12.D.3(b) (p. 433).** The printed interval `q ∈ [(a − c)/2b, (a − c)/b]` gives
   prices at most `c`, and no such output is sustainable for any `δ`
   (`exercise_12_D_3b_printed_false`). On the intended interval `[(a − c)/4b, (a − c)/3b)` the
   minimal discount factor is `δ(q) = 9(A − 3bq)/(5A − 3bq)` (`exercise_12_D_3b_corrected`),
   which is differentiable and *decreasing* in `q`, not increasing
   (`exercise_12_D_3b_threshold`).

10. **Modelling departures in the repeated games.** Repeated Bertrand prices are restricted to
    `p ≥ 0` (bounded per-period profits are needed for discounted values;
    `bertrandStage`). The Cournot game of Example 12.AA.1 has quantities in a compact interval
    `[0, B]`, as in footnote 36 (`cfG`). Strategies are pure, as in MWG's Appendix A. The folk
    theorem is for two players; "feasible" means a convex combination of pure stage payoffs
    (which, by `Schedule`, is exactly the average payoff of a pure outcome path for `δ` near 1);
    punishments use any mutual-punishment profile enforcing levels `w_i` (the minimax payoffs
    when attained; `folk_theorem`).

11. **Exercise 12.B.4 (p. 429).** "Increasing" in `φ` is read as strictly increasing
    differences. Because the monopoly price need not be unique, the conclusion is
    `x(p₂) ≤ x(p₁)` and `p₁ ≤ p₂` whenever `x(p₂) > 0` (`exercise_12_B_4_cost`,
    `exercise_12_B_4_param`).

12. **Elasticity (Exercise 12.B.1).** The price elasticity is expressed with the inverse demand,
    `ε = −p(q)/(p'(q)q)`, equal to `−x'(p)p/x` with `x' = 1/p'` (`priceElasticity`,
    `priceElasticity_eq_demand`).

13. **Exercise 12.D.1.** Formalized as the comparison of collusive and best-deviation payoffs
    that the one-shot deviation principle reduces the question to; the stochastic and growing
    environments themselves are not modelled as games.

14. **Exercise 12.C.8(d) (p. 431).** As printed (demand downward sloping "but otherwise
    arbitrary", cost increasing and convex, quantities in `[0, ∞)`) a symmetric pure-strategy
    equilibrium need not exist: with `P(Q) = 1 + 1/(1 + Q)` and `c(q) = q` profit
    `q/(1 + Q₋ⱼ + q)` has no maximizer, so there is no best response and no equilibrium at all
    (`exercise_12_C_8d_counterexample`). Corrected: with quantities in a compact interval
    `[0, B]` and `P`, `c` continuous (and `P` strictly decreasing, `c` convex), a symmetric pure
    equilibrium exists (`exercise_12_C_8d`), proved from part (c) by a supremum argument. Part (c)
    holds for any interval strategy set and does not need `c` increasing (`exercise_12_C_8c`).

15. **Exercise 12.F.1 (p. 435) and step (i) of Proposition 12.F.1 (p. 412).** False as printed.
    For `p(s) = 1 + e^{−(s+1)²}` (differentiable, `p' < 0` on `[0, ∞)`) and `c(q) = q²`, at every
    `α ≥ 4` best responses exist and are unique, but `b(2α² + 1) > b(2α²)`
    (`exercise_12_F_1_counterexample`, `exercise_12_F_1_false`): the cross partial
    `p'(s)/α + q p''(s)/α²` is positive far in the tail, because `p''/(−p')` is unbounded.
    Corrected: if `p'' ≤ L(−p')` on `[0, ∞)` and costs bound best responses by `B`
    (`c(q) − c(0) > p(0)q` for `q > B`), best responses are weakly decreasing for all `α > LB`
    (`exercise_12_F_1`); linear demand has `L = 0` (`linear_brDecreasing`).

16. **Proposition 12.F.1 (p. 412), modelling.** The SPNE is defined explicitly
    (`IsCournotEntrySPNE`): potential firms `ℕ`, finite entry sets, a Cournot equilibrium after
    every entry set, entrants earn at least `0` net of `K`, and an outsider would earn at most `0`
    in the continuation after its own entry. Inverse demand `p` is primitive (strictly decreasing
    on `[0, ∞)`, continuous at `x(c̄)`); the proof uses convexity of `c` only, not strict
    convexity. Because step (i) is false in general (item 15), "best responses are unique and
    weakly decreasing for all large `α`" (`BRDecreasing`; uniqueness is MWG's standing
    assumption) is a hypothesis of `proposition_12_F_1`; `proposition_12_F_1_of_exercise_12_F_1`
    derives it from the corrected condition of item 15, and `proposition_12_F_1_instance`
    verifies all hypotheses. `competitive_limit` needs only that `c̄` is the infimum of average
    cost, which also gives footnote 29 (`footnote_12_29`).

17. **Exercise 12.F.2(b) (p. 435).** The one-stage model is formalized as: the `J` active firms
    produce the symmetric Cournot outputs (the unique Cournot equilibrium, Exercise 12.C.7) and
    earn at least `K`, and no outsider earns a positive net profit entering with any output
    against them (`IsOneStageCournotEntry`). In both models per-firm profit lies in `[K, 4K]`
    (`cournot_entry_profit_bounds`), which drives the limits (`exercise_12_F_2b`).

18. **Exercise 12.F.3 (p. 435).** Proved for the linear model of Example 12.E.1 (inverse demand
    `a − bq`, cost `cq`), the model in which Section 12.F's phenomenon is first exhibited; the
    loss is measured against the first best `(a − c)²/(2b) − K` (one firm at the competitive
    output), which bounds welfare with any number of firms, so the loss against the
    welfare-optimal number of firms also tends to `0` (`exercise_12_F_3`). The general
    strictly convex model is not treated.

19. **Exercise 12.F.4 (p. 435).** Ill-posed as printed. The demand `xⱼ(p) = α[γ − β(Jpⱼ/∑ₖ pₖ)]`
    is homogeneous of degree zero in prices, so with zero marginal cost: if `γ ≥ βJ` no best
    response exists (`exercise_12_F_4_no_br`); if `γ < βJ` the best response is proportional to
    the rivals' price sum (`exercise_12_F_4_br`); a symmetric equilibrium with positive prices
    exists iff `γ = β(2 − 1/J)`, i.e. only for the single number of firms `J = β/(2β − γ)`
    (`exercise_12_F_4_symmetric`), and then every common price is an equilibrium, with quantities
    `α(γ − β)` independent of the price and profits taking every positive value
    (`exercise_12_F_4_indeterminate`). The equilibrium price level and the entry outcome are
    therefore not determined, and no welfare comparative statics in `α`, `β` follow.

20. **Appendix B (pp. 423-427) and Exercise 12.BB.2: linear model.** MWG argues with a general
    concave inverse demand and the curves of Figures 12.BB.1-12.BB.8. The general claims that
    do not depend on the shape of the curves are proved for general concave, strictly
    decreasing `p`: strict concavity of profits (`appendixB_profit_strictConcave`),
    downward-sloping best responses (`appendixB_br_antitone`), E's profit falling along its best
    response (`figure_12_BB_1`), the truncated best response `min{b(q_E | w), k_I}`
    (`figure_12_BB_2`) and Exercise 12.BB.1 (`exercise_12_BB_1`, assuming I's profit along E's
    best response is concave). Everything that refers to the positions of the points `A`, `B`,
    `S`, `Z`, `k_π` (the stage-3 equilibrium, the three stage-1 cases, the `k_π`-versus-`k_Z`
    criterion and Exercise 12.BB.2) is proved in the linear model `p(Q) = a − Q` with `r > 0`
    and `a − w − 2r > 0` (point `B` interior), where `k_B = (a − w + r)/3`,
    `k_Z = a − w − r − 2√F`, `S = (a − w − r)/2`, `k_π = (a − w − r)(2 + √2)/4`. In this model
    the Stackelberg point is never strictly to the right of `Z` when entry is not blockaded and
    `S` is not right of `B` (`appendixB_linear_S_le_Z`), so Exercise 12.BB.1 has content only
    in the general model.

21. **Appendix B, p. 426-427: the tie at `Z`.** MWG's stage-2 rule is that E "will enter if it
    expects nonnegative profits net of its entry cost `F`", and then says I deters entry "by
    picking a capacity level at least as large as point `k_Z`". At `k_Z` E's net profit is
    exactly zero, so under the printed rule `k_Z` does not deter; when deterrence is optimal
    (`k_Z < k_π`), every capacity above `k_Z` is beaten by a smaller one still above `k_Z`, and
    no SPNE exists in which E follows the printed rule (`appendixB_bookRule_no_spne`). Corrected:
    in every SPNE E stays out at the tie `k_Z`, I builds exactly `k_Z`, and such an SPNE exists
    for every optimal entry strategy that stays out at `k_Z` (`figure_12_BB_7_deter`,
    `edStayOutRule`). Similarly, blockaded entry and inevitable entry are taken with strict
    inequalities (`π_E(b(0 | w + r)) < F`, `π_E(k_B) > F`).

22. **Exercise 12.BB.3 (p. 435).** Formalized as follows. Demand at an end is the mass of
    consumers whose delivered price there is at most `v` and at most the delivered price at the
    other end (`bb3D`); two plants at the same end split their customers by price, equally at a
    tie (`bb3ShareE`). The opposite-ends duopoly is Example 12.C.2's model (`example_12_C_2`),
    which applies because with `v > c + 3t` every consumer buys at the equilibrium prices. The
    subgame in which E builds next to an I plant (I having one or two plants) is shown to give E
    zero operating profit in every price equilibrium, by a Bertrand undercutting argument
    (`bb3_coloc_zero`), and an equilibrium is exhibited. The stage-1 comparison takes E to stay
    out when indifferent at `F = tM/2` (`bb3PayOne`); the two cases `F < tM/2` (two plants, no
    entry) and `F > tM/2` (one plant, no entry) are proved (`exercise_12_BB_3`). Welfare is total
    surplus with every consumer served; it is the same in the equilibrium, with no entrant, and
    with an entrant but a one-plant incumbent, while consumer surplus is higher by
    `M(v − c − 3t/2)` in the last case when `F < tM/2` (`exercise_12_BB_3_welfare`).

23. **Capacity constraints, p. 395: sales of the high-priced firm.** MWG says that by charging
    `p₁ ∈ (c, p(q̄))` firm 1 "sells to the remaining demand at price `p₁`, making sales of
    `x(p₁) − q̄ > 0`". With capacity `q̄` the sales are `min{q̄, x(p₁) − q̄}`, which equals
    `x(p₁) − q̄` only when `x(p₁) ≤ 2q̄` (true for MWG's `q̄ = ¾x(c)`, not for every `q̄ < x(c)`).
    Proved: `capacity_assured_sales` (sales at least `min{q̄, x(p₁) − q̄} > 0` whatever the rival
    charges, with the exact value when the rival is cheaper).

24. **Exercise 12.C.11 (p. 432).** Formalization: `p(·)` is a right inverse of `x` on positive
    quantities (`x(p(Q)) = Q`); "`x(p)` concave" is read as concave on the set where `x > 0`;
    `q_i < b_c(q_j)` means some Cournot best response to `q_j` (`IsCournotBRc`) exceeds `q_i`
    (the best response is in fact unique, by strict concavity, `cap_pi_three`). (a) holds with
    `q₁, q₂ ≥ 0` not both zero (`exercise_12_C_11a`), and the equilibrium is unique with positive
    capacities and continuous demand (`capacity_unique`, MWG p. 395). (b) is false as printed:
    with `q₂ = 0` firm 1 is an unconstrained monopolist and has an equilibrium
    (`exercise_12_C_11b_counterexample_zero_capacity`), and when `b_c(q₂) = 0` (`q₂ ≥ x(c)`) the
    prices `p₁ = p₂ = c` are an equilibrium (`exercise_12_C_11b_counterexample_zero_br`).
    Corrected (`exercise_12_C_11b`): with `q₁, q₂ > 0`, continuous nonnegative demand and
    `q₁ > b_c(q₂) > 0` (or symmetrically), no pure equilibrium exists.

25. **Small type, p. 393: existence via Proposition 8.D.3.** Proposition 8.D.3 needs compact
    strategy sets, while Cournot quantities range over `[0, ∞)`. Proved: with quantities in
    `[0, B]`, `p` continuous on `[0, ∞)`, costs continuous and profits quasiconcave in own output,
    an equilibrium exists (`smallType_12_C_393`); with constant marginal cost `c` and `p(Q) ≤ c`
    for `Q ≥ B` it is an equilibrium on `[0, ∞)` (`smallType_12_C_393_unbounded`). The
    nonexistence example (`smallType_12_C_393_nonexistence`) uses costs that are prohibitive
    except at two output levels per firm (so profits are not quasiconcave and the costs are
    discontinuous); MWG gives no example.

26. **Exercise 12.C.14(c) (p. 432).** The uniqueness of the equilibrium `(v + c)/2` needs
    `v > c`: with `v = c` both `p₁ = p₂ = c` and `p₁ = p₂ = c + 1` are equilibria
    (`exercise_12_C_14c_counterexample`). Proved with `c < v < c + t` (`exercise_12_C_14c`).

27. **Representative consumer, (12.C.13), p. 399.** The first-order conditions are necessary at
    an interior optimum (`eq_12_C_13`). For them to characterize demand we add
    `G'(∑ f(x_j)) ≥ 0` (sufficiency, `eq_12_C_13_sufficient`) and, for uniqueness ("can be
    inverted"), `f` strictly concave and `G' > 0` (`eq_12_C_13_unique`); MWG assumes only that
    `G` and `f` are concave. Product differentiation (p. 396): demand is taken nonnegative
    (`diffProducts_br_above_cost`).

28. **Circular city (p. 399) and Exercise 12.C.16.** MWG prints no equilibrium for the circular
    city. When firm `j` charges `q` and the others `p`, firm `j`'s demand is pinned down by the
    local formula `2M·max{0, min{1/J, x̂(q)}}` for `q ≥ p − w` (`w = t/J` linear, `t/J²`
    quadratic), where consumers past a neighbour prefer that neighbour (`circLin_beyond`,
    `circQuad_beyond`); for lower prices the proofs use only that demand is nonnegative. The
    symmetric equilibrium is `c + t/J` (linear, `circularCity_linear`) and `c + t/J²` (quadratic,
    `exercise_12_C_16`), and no other symmetric price is an equilibrium.

29. **Linear city with nonpurchase (p. 398, Exercises 12.C.13-12.C.14).** Demand counts the
    consumers who strictly prefer a firm to the other firm and to not buying (`lcv_buys_iff`;
    ties are a null set, `lcvShare_spec`). "All consumers purchase" (Ex. 12.C.13) is read as the
    two market shares summing to one. Exercises 12.C.14(a)-(b) use open intervals; the
    equilibrium `c + t` is proved unique for every `v ≥ c + 3t/2` (`smallType_12_C_398`). In
    12.C.14(d) the answer to "are there asymmetric equilibria?" is yes: the equilibria are
    exactly the pairs with `p₁ + p₂ = 2v − t` and `p₁, p₂ ∈ [(4v − 3t − c)/3, (3v − 2t − c)/2]`
    (`exercise_12_C_14d`).

30. **Exercise 12.C.2 (p. 430).** MWG does not specify the space of prices for mixed strategies.
    A mixed strategy is a Mathlib probability measure on `ℝ` with no mass on negative prices
    (`IsMixedPrice`); prices in `[0, c)` are allowed. On `[0, ∞)` profits are bounded and
    measurable, and expected profit is the iterated integral `mbPayoff` (equal to the product
    expectation). Deviations are to any mixed strategy. The full result is proved: `(δ_c, δ_c)` is
    the unique mixed-strategy equilibrium (`exercise_12_C_2`).

31. **Exercise 12.C.4(a) (p. 430).** The answer depends on how ties are resolved. With demand split
    equally (the rule of the text), `(p₁, p₂)` is an equilibrium iff `p₁ < p₂`, `p₁ ≤ c₂`,
    `c₁ < p₂` and `p₁` is firm 1's best price below `p₂` (`exercise_12_C_4a`); when firm 1's
    monopoly price exceeds `c₂` (`g₁` strictly increasing on `[c₁, pᵐ]`, `pᵐ > c₂`) there is no
    pure-strategy equilibrium (`exercise_12_C_4a_none`), while a drastic cost advantage gives
    equilibria (`exercise_12_C_4a_drastic_instance`). The familiar answer `p₁ = p₂ = c₂` needs ties
    resolved in favour of firm 1; then the equilibria are all `p₁ = p₂ ∈ [c₁, c₂]` and firm 2's
    price is weakly dominated in each (`exercise_12_C_4a_tieRule`). We assume `x(c₂) > 0`.

32. **Exercise 12.C.4(b) (p. 431).** "As the grid becomes finer" is made explicit: `x(p̂₂) > 0` at
    the smallest grid price `p̂₂` above `c₂`, `g₁` strictly increasing on `[c₁, p̂₂]`,
    `g₁(p) < 2g₁(p − Δ)` for `p ≥ c₂` with `x(p) > 0`, and (for the undominated equilibrium)
    `c₁ < p̂₂ − Δ`; all hold for linear demand and small `Δ` (`exercise_12_C_4b_instance`). The
    equilibria are `(mΔ, (m + 1)Δ)` with `c₁ ≤ mΔ ≤ c₂` and `g₁((m + 1)Δ) ≤ 2g₁(mΔ)`; only
    `(p̂₂ − Δ, p̂₂)` avoids weakly dominated strategies, and it converges to `(c₂, c₂)`.

33. **Exercise 12.C.5 (p. 431).** MWG does not state a tie-breaking rule. We break ties in favour of
    the buyer with the higher valuation (smaller index), the reading under which "every buyer
    bidding `v_{q+1}`" assigns the units to buyers `1, …, q` as the exercise says. "Competitive
    equilibrium price" is formalized as: at `v_{q+1}` exactly `q` buyers strictly want a unit, buyer
    `q + 1` is indifferent, the rest do not (`exercise_12_C_5_competitive`).

34. **Exercise 12.C.10 (pp. 431-432).** We assume `c̃` and the inverse demand differentiable on `ℝ`
    with `p' < 0` (without `p'(Q*) ≠ 0` the claim of (a) can fail: with a flat demand the
    first-order conditions equate marginal costs). "Not produced efficiently" means some
    reallocation of `Q*` has strictly lower total cost (`exercise_12_C_10a`). In (b) costs are
    nonnegative; the welfare loss is `S(Q°) − W(q*)` with `S` computed with the efficient
    aggregate cost `C(Q)` (Section 10.E), decomposed in `exercise_12_C_10b`. In (c) the example is
    `a = 10`, `b = 1`, `c₂ = 1`, `c₁` falling from `5` to `9/2` (the "why" is verbal: output shifts
    to the high-cost firm).

35. **Exercise 12.C.12 (p. 432).** "Increasing/decreasing" is proved as nondecreasing/nonincreasing
    (`exercise_12_C_12a`): at a corner (`0` or `q̄`) a best response can be locally constant even
    with a nonzero cross partial; it is strictly monotone from interior points. Strict concavity is
    used only for uniqueness of the best response (`exercise_12_C_12a_unique`). Differentiability
    is within `[0, q̄]`.

36. **Exercise 12.C.17 (p. 433).** When `c₂ − c₁ ≥ 3t` the equilibria with firm 2 making no sales
    form a continuum: `p₁ = p₂ − t` with `c₁ + 3t ≤ p₂ ≤ c₂` (`exercise_12_C_17`); in all but
    `p₂ = c₂` firm 2 prices below its cost. The boundary `c₂ − c₁ = 3t` belongs to both cases
    (the interior formula gives `p₂ = c₂` and zero sales for firm 2). Positivity of `c₁, c₂` is
    not used.

37. **Exercise 12.C.18(a) (p. 433).** We assume `p` twice differentiable on `ℝ`, a constant unit
    cost `c < p(0)` (otherwise nothing is produced and the comparisons are equalities), and the
    existence of a Cournot equilibrium, of the follower's best-response function and of a leader
    optimum; MWG's hypotheses `p' < 0`, `p' + p''q < 0` are kept. All four claims hold strictly
    (`exercise_12_C_18a`).

38. **Exercise 12.C.20 (p. 433).** With a convex differentiable cost `c(q)`, MWG's `p(0) > c` becomes
    `p(0) > c'(0)` and the conclusion `c < p(Q*)` becomes `c'(qⱼ*) < p(Q*)` for each firm, with
    `p(Q*) < p(qᵐ)` for the monopoly output with cost `c(q)` (`exercise_12_C_20`); `p` and `c` are
    differentiable on `ℝ`.

39. **Finitely repeated Bertrand game (p. 401).** The repeated game is Chapter 9's multi-stage game
    with observed actions over `T` periods (`IsFiniteRepeatedSPNE`); Proposition 9.B.4 of Chapter 9
    is for finite stage games, so backward induction is re-proved for pure strategies
    (`finite_repeated_unique_spne`). Prices are `p ≥ 0`; `c > 0` and `x(c) > 0` are assumed (for
    the uniqueness of the stage equilibrium, Proposition 12.C.1). Uniqueness holds for every
    discount factor; existence (charging `c` after every history is an SPNE) uses `δ ≥ 0`.

40. **Exercise 12.D.4 (p. 434).** We treat the duopoly (the threshold `δ ≥ 1/2` is the duopoly
    one). (a) The cost change is permanent; "the most profitable price that can be sustained" is
    the monopoly price at the new cost, which is sustained and maximizes per-period profit
    (`exercise_12_D_4a`) and is weakly increasing in the cost when `x(pᵐ(c)) > 0`
    (`exercise_12_D_4a_monotone`). (b) Play from period 2 on is Nash reversion at `pᵐ(c₂)`, the
    most profitable continuation by (a); period-1 sustainability is subgame perfection of the
    whole profile in the game with history-dependent costs (`CostChangeSustains`, proved
    equivalent to a period-1 condition in `costChange_spne_iff`). We add that
    `R₁(p) = (p − c₁)x(p)` is strictly increasing on `[c₁, pᵐ₁]`. When `Γ = δR₂(pᵐ₂)/(1 − δ)` is
    at least `R₁(pᵐ₁)` the period-1 monopoly price is sustainable (prices above it can then be
    sustainable too, so "maximal price" is read as the most profitable one); otherwise the
    maximal sustainable period-1 price is strictly below `pᵐ₁` (`exercise_12_D_4b`), which always
    happens at `δ = 1/2` (`exercise_12_D_4b_compare`).

41. **Exercise 12.D.5 (p. 434).** The stochastic repeated game is not built: Nash reversion with
    state-contingent prices is formalized by its one-shot deviation conditions with expected
    continuation values (`IsRSNashReversion`); the reduction (one-shot deviation principle for
    bounded discounted payoffs with i.i.d. observed states) is argued in the module docstring.
    The threshold is `δ̂ = 1/(1 + λ + (1 − λ)α)`. In (b) we assume `0 < α < 1`, `0 < λ < 1`, and
    for the highest sustainable `p_H` that `(p − c)x(p)` is strictly increasing on `[c, pᵐ]`;
    "for `δ < δ̂` a firm will want to deviate from `pᵐ` in the high state" is proved for every
    `p_L`. (c) is a statement about these Nash reversion strategies, and is proved for all of them
    (any `p_H`, `p_L ≥ 0`), with `c ≥ 0`, `δ ≥ 0`, `x(c) > 0`; it is not a claim about all SPNE.

42. **Footnote 24 (p. 409).** Besides strict (A1), the strict inequality uses `p` strictly
    decreasing (MWG's `p' < 0`, which `proposition_12_E_1` had weakened to nonincreasing).

43. **Example 12.E.4 (pp. 410-411).** As printed (only "`p > [K + cx(p)]/x(p)` for some `p`") the
    claim that all sales occur at `p*` is false: `example_12_E_4_counterexample` gives a Bertrand
    demand whose profit `(p − 1)x(p)` equals `K = 1` on `[2, 3]` and exceeds it at `4`, with
    `p* = 2`, and an equilibrium at the price `3`. MWG's argument "a firm could gain by setting a
    price `p* − ε`" (sic) needs profits above `K` just above `p*`. We add single peakedness: `R`
    strictly increasing on `[c, pᵐ]` with `R(pᵐ) > K` (`example_12_E_4`). Further choices: finitely
    many (at least two) potential firms; the allocation among firms naming the lowest price is an
    arbitrary selection rule (footnote 26), and the result holds for every rule; `c ≥ 0`.

44. **Footnote 26 (p. 411).** "The only division of demand compatible with equilibrium" is
    formalized as: with MWG's earlier equal-sharing rule there is no pure-strategy equilibrium
    (`footnote_12_26`, under the hypotheses of correction 43); other division rules are not
    classified.

45. **Footnote 27 (p. 411).** The planner's problem is stated in quantities with inverse demand
    `P` nonincreasing and continuous (`footnote_12_27`); that its solution `Q*` equals `x(p*)` is
    checked in the linear instance (`footnote_12_27_instance`), not in general.

46. **Exercise 12.E.1 (p. 434).** Answered by an example (`exercise_12_E_1`): costs `1 < 2`, demand
    `max{0, 10 − p}`, `K = 10`. In the duopoly subgame ties go to the low-cost firm
    (Exercise 12.C.4); with equal sharing that subgame has no pure-strategy equilibrium
    (`exercise_12_C_4a_none`). The entry stage is an equilibrium for every selection of stage-2
    equilibria.

47. **Exercise 12.E.3 (p. 434).** In Example 12.E.2 the `J ≥ 2` Bertrand firms are taken to share
    the competitive output equally (`bertrandEntryOutput`; welfare does not depend on the split).
    The loss in Example 12.E.1 is stated for every pair `(J*, J°)` and its limit is uniform over
    all `J° ≥ 1` (from `exercise_12_F_3`); in Example 12.E.2 it tends to the monopoly deadweight
    loss, not to `0`.

48. **Exercise 12.E.4 (p. 434).** The monopoly outcome enters only through the monopoly surplus
    `S` and profit `πᵐ` (`K ≤ πᵐ`).

49. **Exercise 12.E.5 (p. 434).** That both planners face `M(v − c) − JK − tM/(12J²)` (nearest-firm
    purchases, prices as transfers) is argued in the docstring, not derived from consumer choice;
    the theorem compares any welfare-maximizing `J°` with the free-entry `J*` (`J° ≤ J*`), with
    the instance `J° = 3 < 6 = J*`.

50. **Exercise 12.E.6 (p. 434).** The one-stage equilibria considered have the active firms at the
    symmetric Cournot outputs (`IsOneStageCournotEntryGen`). "Two-stage implies one-stage" uses
    `p` nonincreasing, business stealing `q_{J+1} ≤ q_J` and the best-response property of
    `q_{J+1}`; "no more firms" uses `π_J` nonincreasing; all hold in the linear model
    (`exercise_12_E_6_linear`).

51. **Exercise 12.E.7 (pp. 434-435).** An equilibrium is formalized as a sustainable configuration
    (`IsPriceEntryConfig`): an entrant announcing a lower price may serve any part of the demand
    it attracts (MWG does not specify rationing); `P` is strictly decreasing and the minimum of
    `AC` is attained only at `q̄`. The claim is true for `J* ≥ 2` (`exercise_12_E_7`) but false for
    `J* = 1`: `exercise_12_E_7_counterexample` has a non-competitive equilibrium with price `3/2`
    and output `1/2` when `c̄ = 1`, `q̄ = 1`, `x(1) = 1`. The competitive configuration is an
    equilibrium and first-best efficient for every `J* ≥ 1` (`exercise_12_E_7_efficient`).

52. **Exercise 12.B.5 (p. 429).** A verbal "argue" exercise; the models are ours. Not discerning
    preferences means the monopolist offers ONE menu `M ⊆ ℕ × ℝ` of (units, total payment) offers
    to every consumer, containing the null offer `(0, 0)` (any nonlinear price schedule `T` is the
    menu `{(k, T k)}`; a single per-unit price `p` is `{(k, pk)}`); unit cost is a constant `c`;
    offers are deterministic. (a) Unit demand (`unitUtility`: value `vᵢ` for one unit, nothing for
    more); for any menu and any utility-maximizing choices there is a price `p ≥ 0` and optimal
    choices at `p` with at least the same profit (`exercise_12_B_5a`). We assume `c ≥ 0` (the
    book does not specify costs). (b) Costless resale in a competitive resale market is modelled as
    a resale equilibrium (`IsResaleEquilibrium`): given the resale price `ρ`, each consumer chooses
    an offer and a final consumption, trading the difference at `ρ`, and the resale market clears.
    Purchases then maximize `ρk − t` and consumptions are the demands at the single price `ρ`
    (`isResaleEquilibrium_iff`), and the profit is at most that of the single price `ρ`
    (`exercise_12_B_5b`). The theorem concerns any resale equilibrium; existence is not claimed
    (with one consumer and a bundle menu none need exist). Without resale the claim is false
    (`exercise_12_B_5b_needs_resale`: a bundle `(2, 4)` earns `4`, every single price at most `3`).
