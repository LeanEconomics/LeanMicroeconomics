# Corrections

Departures from the printed text of MWG Chapter 17, numbered in book order of discovery.

1. **Proposition 17.B.2 (p. 581): endowments in the consumption set.** The book assumes only
   `∑ᵢ ωᵢ ≫ 0`. If some `ωᵢ ∉ ℝ^L₊`, consumer `i`'s wealth `p·ωᵢ` can be negative at some `p ≫ 0`;
   his budget set is then empty and `z(p)` is undefined. Counterexample: `negEndowEconomy`
   (`ω₁ = (2, -1)`, `ω₂ = (0, 2)`, `p = (1, 3)`), `negEndowEconomy_demand_empty`. All results
   of Sections 17.B-17.C assume `ωᵢ ∈ ℝ^L₊` (`proposition_17_B_2`, `eqm_iff_isEqmPrice`,
   `proposition_17_C_1_economy`, ...).
2. **Exercise 17.B.4 (p. 642): `0 ∈ Yⱼ`.** Closed, strictly convex, bounded above production sets
   and a producible `x̄ ≫ 0` do not guarantee nonnegative wealth: a firm making losses at every
   price may be owned by a consumer without endowment. Counterexample: `negProfitEconomy` (disc
   technology centred at `(-1, -1)`, owned by consumer 0 with `ω₀ = 0`; `x̄ = (2, 2)`), for which
   every printed hypothesis holds and no Walrasian equilibrium exists (`zeroMem_needed`). The
   corrected statement `exercise_17_B_4` adds `0 ∈ Yⱼ` (also used by `prod_eqm_iff`,
   `production_existence`).
3. **Exercise 17.C.2 (p. 642): nonempty values.** The empty correspondence is convex valued,
   upper hemicontinuous and satisfies (ii)-(v) vacuously, but `0 ∈ z(p)` has no solution
   (`exercise_17_C_2_needs_nonempty`). `exercise_17_C_2` assumes nonempty values (and uses the
   upper hemicontinuity of Definition M.H.3 only through its closed graph).
4. **Departure: Proposition 17.B.1 (p. 580) and (17.B.1').** Proved under local nonsatiation
   alone (`proposition_17_B_1`); continuity and strict convexity are not used, and strict
   convexity only makes demand single valued (`proposition_17_B_1'`). (17.B.1') is stated at
   prices where every consumer's demand is nonempty, since at other `p ∈ ℝ^L₊` (e.g. with a zero
   price and monotone preferences) `z(p)` is undefined.
5. **Departure: number of goods.** Results that use local nonsatiation derived from strong
   monotonicity assume `L ≥ 1` (`eqm_iff_isEqmPrice`, `proposition_17_C_1_economy`,
   `secondWelfare_of_existence`, `proposition_17_C_2`); `proposition_17_B_2`,
   `proposition_17_C_1`, `exercise_17_B_4` and `exercise_17_C_2` cover `L = 0` separately.
   In Proposition 17.C.2 homogeneity is a hypothesis (as printed) that the proof does not use.
6. **Exercise 17.C.6 (p. 644): the list of conditions.** The exercise asks for four examples but
   lists only "(i), (iii), and (iv)"; the fourth condition is (v). Examples:
   `exercise_17_C_6_i`, `exercise_17_C_6_iii`, `exercise_17_C_6_iv`, `exercise_17_C_6_v`. Why (ii)
   is not listed: (i), (iii), (iv), (v) alone imply existence for every `L`, since
   `z(p/∑ₗ pₗ)` satisfies (i)-(v) (`homogenize_isStandard`, `exercise_17_C_6_ii`).
7. **Exercise 17.D.1 (p. 644): false as printed.** With `u₁ = (2x₁₁^ρ + x₂₁^ρ)^{1/ρ}`,
   `u₂ = (x₁₂^ρ + 2x₂₂^ρ)^{1/ρ}`, `ρ = -4`, `ω₁ = (1, 0)`, `ω₂ = (0, 1)`, the equilibrium is unique
   (`p = (1, 1)`): with `s = p₁^{1/5}`, `c = 2^{1/5}`, `z₁(p₁, 1) = 0` iff
   `(s - 1)(s⁴ + (1 - c)(s³ + s² + s) + 1) = 0`, and the quartic is positive because `c < 5/3`
   (`exercise_17_D_1_printed`). Multiple equilibria need weight `α ≥ (5/3)⁵`; with
   `α = (31/14)⁵` there are exactly three, `p₁ ∈ {1/32, 1, 32}` (`exercise_17_D_1_corrected`).
8. **Departure: Definition 17.D.1 and Proposition 17.D.1.** Regularity includes differentiability
   of `ẑ` at the equilibrium (the book assumes `z` is `C¹`); local isolation
   (`proposition_17_D_1_isolated`) uses only that. The finiteness part
   (`proposition_17_D_1_finite`) is stated for any `z` with (i)-(v) of Proposition 17.B.2 (which
   the book's economies have, `proposition_17_B_2`).
9. **Proposition 17.D.2 (p. 593): proved for `L = 2` only.** `proposition_17_D_2_two_goods`
   (with the oddness `two_goods_card_odd` and the alternation of slopes) uses only (i)-(v) and
   regularity. For general `L` the index theorem is OPEN (Brouwer degree / Poincaré-Hopf are not
   in Mathlib); it is verified for one-consumer Cobb-Douglas economies in every dimension
   (`exercise_17_D_8`).
10. **Proposition 17.D.3 (p. 595): proved for `M ≥ N`.** `proposition_17_D_3` (`M = N`, from
    Chapter 3's `theorem_M_E_2`, with `C¹`) and `proposition_17_D_3_over` (`M > N`, by padding the
    unknowns). The underdetermined case `M < N` is OPEN: it needs Sard's theorem for `C^k` maps
    with `k > N - M`, while Mathlib only has the equal-dimension measure-zero lemma. The economic
    application (Proposition 17.D.5) has `M = N = L - 1`.
11. **Departure: Proposition 17.D.5 (p. 596).** The book's differentiability assumption ("`z` is
    continuously differentiable", footnote 13) is placed on the consumers: each has a demand
    function `xᵢ(p, w)` that is `C¹` on `{p ≫ 0} × (0, ∞)`, and `ẑ(p; ω) = ∑ᵢ (x̂ᵢ(p, p·ωᵢ) - ω̂ᵢ)`
    (`proposition_17_D_5`). No preference structure is used (Proposition 17.D.4 needs only that
    consumer 1's demand depends on `ω₁` through wealth). The instance is Cobb-Douglas
    (`proposition_17_D_5_cobbDouglas`), whose demand is the Walrasian demand of the utility
    (`walrasianDemand_cobbDouglas`) and whose excess demand satisfies (i)-(v)
    (`cdED_isStandard`), although Cobb-Douglas preferences are not strongly monotone on the
    boundary of `ℝ^L₊`. The endowment vector is indexed by `Fin (I · L)` (consumer-major order).
12. **Departure: footnote 14 (p. 591).** Proved as a statement about the principal
    `(L-1) × (L-1)` minors of `A = Dz(p)` at one `p` (`footnote_17_14`): if `A p = 0`, `pᵀA = 0`,
    `p ≫ 0` and `rank A = L - 1`, every principal minor is nonzero and `det A_{kk} = λ p_k²` for
    one `λ ≠ 0`. Normalizing good `k` evaluates `Dz` at `p/p_k` instead of `p`; by homogeneity of
    degree zero `Dz(p/p_k) = p_k Dz(p)`, which multiplies the minor by `p_k^{L-1} > 0` (this
    rescaling is not formalised). For the last good the minor is exactly `Dẑ`
    (`normED_hasFDerivAt`, `isRegularEqm_of_rank`).
13. **Departures: Exercises 17.D.6 and 17.D.7.** In 17.D.6 the system is
    `λ₁∇_{x₁}u₁(x₁, x₂) = p`, `λ₂∇u₂(x₂) = p`, two budget equations and one market equation; the
    "appropriate differentiability conditions" are `C¹` gradients with nonsingular `D_{x₁}∇u₁`,
    `D∇u₂`. Generic regularity and local isolation are proved (`exercise_17_D_6`,
    `exercise_17_D_6_isolated`); finiteness is proved when the equilibrium set is compact
    (`exercise_17_D_6_finite`), compactness under externalities requiring boundary assumptions
    the book does not state. In 17.D.7 "no communication" is modelled as separate markets with one
    normalization per island, and "free transportation" as one price system with aggregate market
    clearing `∑ₖ z(pₖ) = 0` (`exercise_17_D_7a`, `exercise_17_D_7b`).
14. **Departure: Exercise 17.D.4 (p. 644).** The "appropriate differentiability conditions" are
    `C¹` demand functions with negative own substitution effects
    `∂x₁ᵢ/∂p₁ + x₁ᵢ ∂x₁ᵢ/∂w < 0` (the Slutsky hint), assumed directly on the demand functions
    (`exercise_17_D_4`); finiteness additionally assumes (i)-(v) of Proposition 17.B.2 for the
    economies considered (`exercise_17_D_4_finite`). Both hold for Cobb-Douglas consumers
    (`cd_slutsky_neg`, `exercise_17_D_4_cobbDouglas`).
15. **Departure: Proposition 17.E.1 (p. 600).** The proof's count "at most `I` of the `I + 1`
    vectors `p, z₁(p), …, z_I(p)` are linearly independent" needs `I ≥ 1` (with no consumer, `p ≠ 0`
    is independent and for `L = 1` no `dp ≠ 0` with `p·dp = 0` exists); `proposition_17_E_1` assumes a
    nonempty set of consumers. "The substitution matrices are negative semidefinite" is derived,
    not assumed: the consumers are differentiable demand functions satisfying Walras' law and the
    weak axiom, and Chapter 2's `proposition_2_F_2` applies at `(p, p·ωᵢ)` with `p·ωᵢ > 0`. The
    derivative `Dz(p)` is the Fréchet derivative, which exists by (17.E.3) (`eq_17_E_3`).
16. **Correction: footnote 24 (p. 599).** "`z(p)` can take any value" holds only for values with
    `p·z = 0`. Any demanded bundle `ω + z` is affordable, so `p·z ≤ 0` (`footnote_17_24_necessary`);
    a value with `p·z > 0` is impossible, and with locally nonsatiated preferences so is `p·z < 0`.
    For every `z` with `p·z = 0` the construction works (`footnote_17_24`).
17. **Departure: Proposition 17.E.2 (p. 600).** The consumers are explicit (Exercise 17.E.3):
    `uᵢ(x) = p·(x - x̄) - c ∑_{k ≠ i} |xₖ - x̄ₖ|` with `x̄ = R𝟙`, `0 < c < minₖ pₖ`, endowments
    `ωᵢ = R𝟙 + pᵢaⁱ ≫ 0`; utilities are continuous, concave and strongly monotone but, like the
    book's "vertex" preferences, not strictly convex. Demand is single-valued at all prices near
    `p`, so `z` is a function there and `Dz(p) = A` is a genuine derivative. The hypothesis
    `p·z = 0` is implied by `Ap = 0` and `p·A = -z` (unused in `proposition_17_E_2`).
18. **Departure and OPEN item: Proposition 17.E.3 (p. 602).** Proved for every `L` and `ε > 0`
    (`proposition_17_E_3`, and the book's two-good proof `proposition_17_E_3_two`): the consumers
    have consumption sets `ℝ^L_+`, endowments `≫ 0` with `ωᵢ + zⁱ(p) ≥ 0`, and continuous, convex,
    strongly monotone preferences with single-valued demand on `P_ε`. What is not obtained is the
    chapter's standing requirement that preferences be **strictly** convex: the constructed
    upper contour sets are intersections of half-spaces (`smd_rationalize`), whose indifference
    sets have flat pieces. OPEN: strictly convex preferences generating the same demand on `P_ε`
    (a smoothing of the support functions `σ(·, c)` that keeps their value and slope at the
    demanded normal and their strict monotonicity in `c` is missing). The book's step "fit an
    indifference map" (`L = 2`) and the appeal to "SA ⟹ rational preferences" (footnote 34,
    `L > 2`) are replaced by a direct construction (`smd_rationalize`): utility level = price
    ratio (`L = 2`) or `pᵢ` on the unit sphere (Debreu), better-than sets generated by the offer
    points of lower level, rotated towards the other axes (`debreuRho`) so that they vary
    continuously with the level, and each `αᵢ` extended off the normalized prices by Tietze. For
    `ε > 1`, `P_ε = ∅`; for `L = 1`, `z = 0` on `P_ε`; these cases are handled directly.
19. **Remark: the "small constant" `ε` (p. 602).** No smallness is needed; the statement is
    proved for every `ε > 0`.
20. **Departure: Exercise 17.E.4 (p. 645).** The exercise's domain is `ε < p₁/p₂ < 1/ε` (strict),
    nonempty only for `ε < 1`, which is assumed. "Generated from a rational preference relation"
    is modelled as: one consumer with an arbitrary consumption set, endowment and utility function
    whose demand at each price of the domain is the single bundle `ω + z(p)`; the example
    `z(p) = ((p₁ - p₂)/(p₁ + p₂)²)(p₂, -p₁)` violates the weak axiom at `(1, a)` and `(a, 1)`
    (`exercise_17_E_4`).
21. **Departure: Exercise 17.E.5 and the text of p. 604.** The number of consumers is not given.
    The claim is proved for two consumers (`exercise_17_E_5`; `L = 2` consumers as in
    Proposition 17.E.3), for any `p` steeper than `p'` and only upper bounds `(1, 1)` on
    endowments. Writing `zᵢ(p) = αᵢz(p)`, `zᵢ(p') = βᵢz(p')`, the weak axiom forces `αᵢ < 0` or
    `βᵢ < 0` (or both `0`) while `∑αᵢ = ∑βᵢ = 1`, `αᵢ, βᵢ ≤ 1` (`ex17E5_shares`, any number of
    consumers); the same count excludes three consumers (`exercise_17_E_5_three`). With four consumers the shares `α = (1, 1, -1/2, -1/2)`,
    `β = (-1/2, -1/2, 1, 1)` meet every constraint and the weak axiom is not violated
    (`exercise_17_E_5_four`), so the book's statement is false for four or more consumers unless
    their number is bounded; an explicit four-consumer economy is not constructed.
22. **Departure: Exercise 17.E.6 (p. 645).** "Proportional" is taken as "a positive multiple".
    The claim needs `pᵢ > 0` (true on `P_ε`): on unit vectors with `pᵢ = 0`, `zⁱ(p) = eⁱ` is
    constant. Proved on `{‖p‖ = 1, pᵢ > 0}` (`exercise_17_E_6`).
23. **OPEN: Proposition 17.E.4 (p. 603) and footnote 28 (p. 601).** Proposition 17.E.4 is stated
    without proof in the book (Mas-Colell 1977) and is not formalised. Footnote 28 (prescribed
    substitution matrices `Sᵢ`) is not formalised.
24. **Example 17.F.1 (p. 611) and footnote 48 (p. 613): "compatible ... even with the property of
    gross substitution".** In the example consumer 1 trades only goods 1-2 and consumer 2 only
    goods 3-4, so raising `p₃` leaves `z₁` unchanged: the aggregate excess demand can never have
    the (strict) gross substitute property of Definition 17.F.2 (`example_17_F_1_not_GS`,
    `ex17F1Z_not_GS`); with Cobb-Douglas consumers it has the weak property (`ex17F1Z_weakGS`).
    The conclusion the book draws ("the GS property does not imply the WA", footnote 48) is
    true: adding a small Cobb-Douglas consumer with `ω ≫ 0` gives a gross substitute excess
    demand `gsNotWAZ` that violates the weak axiom (`gs_not_weakAxiom`), and so a constant
    returns economy with two equilibria (`footnote_17_48`).
25. **Proof of Proposition 17.F.3 (p. 613): sign of the key inequality.** Lowering the prices of
    the goods `k ≠ ℓ` from `p'` to `p` cannot increase `zₗ` (gross substitution), so
    `zₗ(p) < zₗ(p')`, not "`zₗ(p) > zₗ(p')`" (`gs_path`). Counterexample to the printed sign: one
    Cobb-Douglas consumer, `a = ω = (1, 1)`, `p = (1, 1) ≤ p' = (1, 2)`, `z₁(p) = 0 < 1/2 = z₁(p')`
    (`proposition_17_F_3_printed_sign`). The conclusion `z(p) ≠ z(p')` is unaffected
    (`proposition_17_F_3`).
26. **The differential version of gross substitution (p. 612).** Gross substitution gives only
    `∂zₖ/∂pₗ ≥ 0` (`gs_partial_nonneg`); `> 0` is a sufficient condition (`gs_of_partial_pos`),
    not a consequence. Counterexample: `gsCubicZ` (`z₁ = r h(r)`, `z₂ = -h(r)`, `r = p₂/p₁`,
    `h(r) = (r - 1)³ + 1`) is homogeneous, satisfies Walras' law and gross substitution
    (`gsCubicZ_props`), yet `∂z₂/∂p₁ = 0` at `(1, 1)` (`gs_partial_not_pos`).
27. **The own-price claim of p. 611 needs `L ≥ 2`.** With one good, homogeneity makes `z₁`
    constant and gross substitution is vacuous (`gs_own_price_one_good`); `gs_own_price` assumes
    a second good.
28. **Exercise 17.F.1 (p. 645): "negative semidefinite".** With proportional endowments or
    consumptions the matrix (17.F.2) is negative semidefinite on the price changes with
    `dp·z(p) = 0` (`exercise_17_F_1a`, `exercise_17_F_1b`), the sense of (17.F.1), which covers
    every `dp` at an equilibrium. Without that restriction the term `-(1/p·ω̄)x̄z(p)ᵀ` can make it
    indefinite even for one consumer: `S = 0`, `p = ω = (1, 1)`, `x = (2, 0)`, `dp = (1, 2)` give
    `dp·Dz dp = 1 > 0` (`exercise_17_F_1_unrestricted`).
29. **Misprint (p. 614).** "This is summarized in Proposition 12.F.4" refers to Proposition
    17.F.4 (`proposition_17_F_4`).
30. **Remarks on Propositions 17.F.1-17.F.2 (pp. 607-609).** Equilibrium prices are `≫ 0`
    (strong monotonicity), so `p ≫ 0` is part of `IsCREqmPrice` and of the conclusion of
    `proposition_17_F_1`; the cone property of `Y` is used only to make profits zero
    (`cr_profit_zero`). The convexity half of Proposition 17.F.2 holds for every `Y`, convex and
    constant returns or not (`proposition_17_F_2_convex`); the necessity half is proved from the
    weaker hypothesis of uniqueness for closed constant returns `Y` only
    (`proposition_17_F_2_necessity`). (17.F.1) is proved with differentiability on all of
    `ℝ^L_{++}` (`eq_17_F_1_sufficient`), and (17.F.3), which the book leaves unproved, is proved
    for every `L` (`eq_17_F_3`; Exercise 17.F.7 is the case `L = 2`).
31. **Remark on Proposition 17.F.5 (pp. 614-615).** Only strict convexity of preferences
    (strictly quasiconcave utilities on `ℝ^L₊`) is used; the appeal to the first welfare theorem
    is replaced by the same budget argument applied to `½x + ½ω` (`proposition_17_F_5`). The
    same argument proves Exercise 17.F.9 (`exercise_17_F_9`).
32. **Exercise 17.F.5 / Example 17.F.2 (pp. 612, 645).** The condition `-xu''/u' < 1` is used in
    the form "`t u'(t)` strictly increasing" (equivalent for `C²` utilities with `u' > 0`,
    `ex17F5_rra`), together with strictly decreasing marginal utilities; the gross substitute
    conclusion is proved whenever demand is an interior first-order point (`exercise_17_F_5`),
    which the book takes for granted. For CES (`0 < ρ < 1`) interiority holds and the conclusion
    is proved for all endowments `ω ≥ 0`, `ω ≠ 0` (`exercise_17_F_5_ces`); for `ω = 0` the excess
    demand is `0`, which is not GS.
33. **Exercise 17.F.6 (p. 645) is false as printed; proved for homothetic consumers.** In the
    induced economy (Cobb-Douglas unit costs `c_g`, Shephard requirements, goods priced at
    average cost) the factor-1 excess demand is `Z₁ = (1/w₁)∑ᵢ Iᵢ(β₁ + (β₀ - β₁)sᵢ(c₀/c₁)) - ω̄₁`
    (`fgeInduced_eq`), `sᵢ` the share of good 0 in consumer `i`'s spending. With homothetic
    consumers whose demand has the gross substitute property (`sᵢ` strictly decreasing; such
    demand is normal, `fgeDemand_gs_normal`) and `ω̄ ≫ 0`, the induced factor excess demand has
    the gross substitute property for any endowments and `β₀, β₁ ∈ (0, 1)`
    (`exercise_17_F_6_homothetic`), so the equilibrium is unique (`exercise_17_F_6_unique`).
    Without homotheticity the claim fails (`exercise_17_F_6_counter`): one consumer with demand
    `fgeLux` (share `Iq₁/(Iq₁ + q₀²)` on good 0; income exhausted, homogeneous of degree zero,
    both goods strictly normal and strict gross substitutes at all prices and incomes, negative
    compensated own-price effect), `ω = (1, 1/1000)`, `c₀ = √(w₁w₂)`, `c₁ = w₁^{1/4}w₂^{3/4}`:
    raising `w₂` from `1` to `16` lowers `Z₁`. The income effect of the factor-price change on
    the luxury good 0, produced intensively with factor 1, outweighs the substitution effect.
    Whether uniqueness (the exercise's last claim) survives is not settled.
34. **Example 17.F.3 (p. 615) / Exercise 17.F.13 (p. 646): the index of the symmetric
    equilibrium is `+1`.** With `uᵢ = x_{Hi} - x_{Fi}^ρ`, `-1 < ρ < 0`, the demand for the foreign
    good is `X(r) = (r/(-ρ))^σ`, `σ = 1/(ρ - 1) ∈ (-1, -1/2)` (`exercise_17_F_13_demand`), the
    symmetric equilibrium has each country consume `κ = X(1) < 1` of the foreign good
    (`exercise_17_F_13_eqm`), and near `(1, 1)` `z₁(t, 1) = X(t) - X(1/t)/t` has slope
    `κ(1 + 2σ) < 0` at `t = 1`. So `(1, 1)` is regular with index `+1` for every printed `ρ`
    (`exercise_17_F_13_index`): country 1's demand for good 1 does rise with `p₁` (rate
    `κ(1 + σ) > 0`), but less than country 2's falls (rate `κσ`). The book's sufficient condition
    for an asymmetric equilibrium (a negative index) is therefore never met in this example; the
    index argument itself is proved (`example_17_F_3_index`, instance `ex17F3_index`). (For
    `ρ < -1` the symmetric equilibrium is at a corner, `x_H = 0`, where `z₁ = 1/t - 1`, again of
    index `+1`; not formalised.)
35. **Misprint: Proposition 17.G.2 (p. 617) and its proof (p. 618).** The hypothesis "`D_q ẑ(p̄; q̄)`
    is negative definite" and the proof's "`[D_q ẑ(p̄; q̄)]⁻¹` is negative definite" should read
    `D_p ẑ` (`D_q ẑ` is `(L - 1) × N`); the proof's displayed formula uses `D_p ẑ`. Proved as
    `proposition_17_G_2` for any local solution `p(·)` differentiable at `q̄` (only
    `D_p ẑ ∘ Dp(q̄) = -D_q ẑ` is used, and only semidefiniteness would be needed), and with
    existence for strictly differentiable `ẑ` (`proposition_17_G_2_exists`).
36. **Departure: Proposition 17.G.1 (p. 617).** The prescribed endowments are `ω̂₁ ≥ 0` (the first
    consumer also owns one unit of good `L`); prices are normalized `p_L = 1`. The first consumer
    is Cobb-Douglas with equal exponents, for which `|D_{ω̂₁} ẑ₁| = (-1)^{L-1}/L ≠ 0` (`cseM_det`).
    `Dp(ω̂₁) = B` is proved for the implicit function of Theorem M.E.1, which needs a strict
    derivative; for this, Proposition 17.E.2 (`proposition_17_E_2`, module PriceEffectsEconomy) now
    states that the constructed excess demand is strictly differentiable at `p` (it is smooth near
    `p`; a small change to an earlier batch's module, needed here).
37. **Remark: Proposition 17.G.3 (p. 618).** The hypothesis of a negative diagonal is not used (it
    follows from homogeneity and the positive off-diagonal entries). The proof avoids the
    productive input-output matrix of Appendix 5.AA: with `B` the truncated matrix, `Bp̂ ≪ 0`, and
    `By ≥ 0`, `y ≠ 0` force `y ≪ 0` (`cs_neg_of_nonneg`), which gives nonsingularity and `B⁻¹ ≪ 0`
    (`cs_inv_neg`).
38. **Exercise 17.F.14 (p. 646).** (a) holds for any exponents `α ≫ 0` at `v ≫ 0` (the bound
    `∑ α ≤ 1` is not needed; `exercise_17_F_14a`). (b) is false as printed: the linear
    `f(v) = v₁ + v₂` is concave, increasing, `C²` and of constant returns, with every second
    partial `0`, so no input is a complement to another (`exercise_17_F_14b_counter`). True
    statement: with constant returns `∑ₗ' vₗ' ∂²f/∂vₗ∂vₗ' = 0`, so if `∂²f/∂vₗ² < 0` some `ℓ' ≠ ℓ` is
    a complement to `ℓ` (`exercise_17_F_14b`). (c) A strictly concave `C²` function need not have a
    nonsingular Hessian (e.g. `-x⁴` at `0`); the result is proved for a negative definite Hessian,
    by differentiating the first-order conditions (`exercise_17_F_14c`).
39. **Departures: Exercise 17.F.16 (pp. 646-647).** "Strictly increasing in `p`" (SGS) is read as
    `p ≤ p'`, `p ≠ p'` ⟹ strict increase of every coordinate. (b) assumes `g` continuously
    differentiable on all of `ℝ^N` (`exercise_17_F_16b`). (g) is proved for `N = 1`
    (`exercise_17_F_16g_one`); for `N ≥ 2` it is OPEN (the book's argument is the index theorem
    in `N` dimensions). (h) is proved directly: `Dĝ(p̂)p̂ ≪ 0` when the cross effects of the
    numeraire are positive (gross substitution gives them only `≥ 0`), and uniqueness follows from
    Proposition 17.F.3 (`exercise_17_F_16h`); the boundary conditions of 17.F.16 are not meaningful
    for excess demand, so (g) is not applied literally. Exercise 17.G.3 needs neither continuity nor
    uniqueness (`exercise_17_G_3`).
40. **Departures: Exercise 17.F.15 (p. 646).** The model: the primary factor is good `0` and the
    numeraire for producers, every good is produced, so producer prices are the zero-profit
    prices `q = (1, a)` (`taxProfit_zero`); taxes are levied on net purchases at producer prices,
    `T = ∑ tₗqₗ(xₗ - ωₗ)`, and rebated lump sum (`IsLeontiefTaxEqm`). Normal goods are modelled as
    a demand path `X(W)` at the fixed consumer prices that is nondecreasing and exhausts wealth;
    uniqueness uses only market clearing (`exercise_17_F_15`). The example of nondispensability is a
    wealth-expansion path with an inferior output and a subsidy (`exercise_17_F_15_normality`);
    the path is the demand at the consumer prices of the continuous, weakly monotone, convex
    utility `fn15U` (`fn15U_demand`, `exercise_17_F_15_preferences`). These preferences are not
    strongly monotone (Leontief-type kinks).
41. **Remark: Exercise 17.G.2 (p. 647).** It needs at least three goods: with two goods, a negative
    `D_p ẑ` and strict normality force `∂p₁/∂ω₁₁ < 0` (`exercise_17_G_2_two_goods`). The example
    has `L = 3` (`exercise_17_G_2`).
42. **Remark: Exercise 17.G.1 (p. 647).** Of strict normality only `∂x_{L1}/∂w₁ > 0` is used, with
    Walras' law (`p·D_w x₁ = 1`, `exercise_17_G_1_walras`): `|D_{ω̂₁} ẑ₁| = (-1)^{L-1}∂x_{L1}/∂w₁`
    (`exercise_17_G_1_det`). `rank Dp(ω̂₁) = L - 1` holds for any differentiable solution function
    (`exercise_17_G_1_rank`).
43. **Departure: Exercise 17.F.17 (p. 647).** "Uniformly among the nonnegative consumptions on the
    budget line" is modelled by the constant-speed parametrization `x(s)`, `s` uniform on `[0, 1]`
    (`beckerLine_props`), and "average excess demand" of the continuum as the expected excess demand
    of one consumer; endowments `ω ≥ 0`.
44. **Proposition 17.H.1 (p. 623).** The proof uses, besides `z(p*) = 0` and `p*·z(p) > 0` off the
    ray, continuity, Walras' law, and the bounds (iv)-(v) of Proposition 17.B.2: the compactness
    step that makes the rate of approach bounded away from zero away from the ray must exclude
    trajectories drifting to the boundary of `ℝ^L_{++}` (`tat_unif_pos`). These are standing
    properties of excess demand (p. 582) and are hypotheses of `proposition_17_H_1`. The conclusion
    is proved in the stronger form `p(t) → λp*` (`λ` fixed by `∑ₗ pₗ(0)²/cₗ`). In the displayed
    computation the second line drops the factor `2`: `df(p(t))/dt = -2p*·z(p(t))`
    (`proposition_17_H_1_deriv`); the sign, and the argument, are unaffected.
45. **Departure: trajectories of (17.H.1).** A trajectory is a function on `[0, ∞)` with `p(t) ≫ 0`
    (where `z` is defined) and derivative `(cₗzₗ(p(t)))ₗ`, one-sided at `t = 0` (`IsTatPath`). The
    book takes existence for granted; it is proved for `C¹` excess demand with Walras' law when
    small prices rise (`tat_exists`), e.g. one Cobb-Douglas consumer (`cd1_tat_exists`). All
    stability theorems hold for every trajectory.
46. **Properties (a)-(b), two goods (pp. 621-622).** "Locally stable" is formalized for the relative
    price: `|p₁(0)/p₂(0) - r̄| < ε ⟹ p₁(t)/p₂(t) → r̄`; "locally totally unstable": every trajectory
    starting within `ε` of `r̄` (and not at `r̄`) leaves the `ε`-neighbourhood
    (`tat_two_locally_stable`, `tat_two_locally_totally_unstable`). Property (b) is proved when the
    equilibrium is unique (`footnote_17_62_two_goods`) and, with any number of equilibria, as
    convergence of `p₁(t)/p₂(t)` to the relative price of some equilibrium
    (`section_17_H_property_b`). The field `z₁(r, 1)` is only continuous, so trajectories need not
    be unique; the proof shows that every solution of `dr/dt = g(r)k(t)`, `k > 0`, is monotone
    (no strict peak or valley: `ctg_no_peak`, `ctg_monotone`) and then uses the boundary
    behaviour (footnote 8).
47. **Local stability and eigenvalues (p. 624).** "`p*` is locally stable if and only if all the
    eigenvalues of `CDẑ(p*)` have negative real parts" is false in the "only if" direction:
    `tat_eigen_counterexample` gives a homogeneous excess demand with Walras' law (three goods)
    and a regular equilibrium at which `Dẑ` has eigenvalues `±i`, yet every normalized trajectory
    converges to it (Lyapunov function `x² + y²`, `dV/dt = -2(x⁴ + y⁴)`). True statement: negative
    real parts imply local stability (Lyapunov's indirect method), and an eigenvalue with positive
    real part implies instability; the first is proved for negative definite `Dẑ(p*)`
    (`tat_local_stable_of_negDef`) and for two goods (`tat_two_locally_stable`); both general
    statements are OPEN here.
48. **Departure: Newton's method (17.H.2), p. 625.** `Dẑ(p*)` "nonsingular" is used with strict
    differentiability at `p*` (inverse function theorem), and "succeeds after a small disturbance"
    is proved for every Newton trajectory starting close to `p*` (`newton_restores`); existence of
    Newton trajectories is not addressed (instance `newton_instance`).
49. **Proposition 17.H.2 (p. 626) is false as printed.** In `proposition_17_H_2_counter` the single
    consumer has the strictly concave utility `log x₁ + log x₂`, `ω = (1, 1)`, `Y` is compact and
    convex, `ȳ = 0` is the unique equilibrium, and the trajectory
    `y(t) = (1/4 + e^{-t}/4, -1/4 - e^{-t}/4)` is admissible with `p(y(t))·dy/dt > 0` throughout,
    but `y(t) → (1/4, -1/4)`. The book itself notes the gap ("the dynamics cannot be so sluggish
    that we never reach the equilibrium"). Corrected statement (`proposition_17_H_2`): with `Y`
    compact and convex, `u` continuous and strictly concave, and a *uniformly* admissible trajectory
    (`p(y(t))·dy/dt ≥ δ(ε) > 0` whenever `‖y(t) - ȳ‖ ≥ ε`), `y(t) → ȳ`. Modelling choices: the
    short-run price is `p(y) = ∇u(y + ω)` (the book's `μ(t)p(y(t)) = ∇u`, with `μ = 1`), and the
    step "equality only at equilibrium" uses concavity of `u` (the gradient inequality
    `concave_le_fderiv`) rather than strict quasiconcavity.
50. **Departure: Exercise 17.H.1(a) (p. 648).** `z` is assumed differentiable on `ℝ^L_{++}` (the
    hint's argument is the derivative of `zₗ/pₗ` at a maximizing index); weak gross substitution
    suffices. `ψ(p(t))` is proved nonincreasing on `[0, ∞)` and strictly decreasing on every time
    interval on which `z(p(t)) ≠ 0` (`exercise_17_H_1a`); the book's "decreasing if `z(p(0)) ≠ 0`"
    would also need that a trajectory cannot reach equilibrium in finite time (uniqueness of
    solutions), which is not addressed.
51. **Departure: Exercise 17.H.2 (p. 648).** Model: Walras `dp/dt = z(p) - s(p)` with `s = P⁻¹` the
    direct supply; Marshall `dq/dt = z⁻¹(q) - P(q)`; joint `dp/dt = z(p) - q`, `dq/dt = p - P(q)`;
    "nearly constant returns" is `P'(1) = ε` small. Stability is read off the linearization (sign of
    the slope; for the joint system the eigenvalues, `rh2`). (d) holds for small `ε` only:
    with `z'(1) = 1/4`, `ε = 1/2` the joint system is stable but not Marshallian stable
    (`exercise_17_H_2d_small_needed`). In (e) the expectation of sales enters as
    `dq/dt = p - 1 + β(z(p) - q)`, `β > 0`.
52. **Exercise 17.H.3 (p. 648).** The answer "no" rests on the index theorem (Proposition 17.D.2:
    a unique regular equilibrium has index `+1`), which is OPEN here for `L = 3` except for
    Cobb-Douglas economies (Exercise 17.D.8); what is proved is that an equilibrium of index `+1`
    is never a saddle of `CDẑ` (`exercise_17_H_3`), with the Cobb-Douglas instance
    (`exercise_17_H_3_cd`).
53. **Figure 17.I.1 (p. 627): a concrete economy.** The book gives only a picture (nonconvex
    consumer with two interior demands `x₁`, `x'₁` at `p̄`). We take `u₁ = x₁² + x₂²` (Chapter 16's
    `sqNormU`), `u₂ = x₁x₂`, `ωᵢ = (1, 1)`; at `p̄ = (1, 1)` consumer 1 demands the corners `(2, 0)`
    and `(0, 2)`. Then `E(r)` is computed for every `r ≥ 1` (`figure_17_I_1`): empty for odd `r`,
    the ray `p₁ = p₂ > 0` for even `r`, which proves the printed claims for `r = 1, 2`
    (`figure_17_I_1_one_two`).
54. **Footnote 71 (p. 628): "no inclusion relationship".** In the economy of Figure 17.I.1 the
    inclusion `E(r') ⊆ E(r'')` fails for `(r', r'') = (2, 3)` and `E(r'') ⊆ E(r')` fails for
    `(3, 4)` (`footnote_71_no_inclusion`). A single pair with both inclusions failing needs two
    nonconvex types switching at different prices, and (since such switches and convex
    gross-substitute types all move excess demand the same way) a type whose demand for a good
    rises with its price. `fn71Economy` has four types on `ℝ²₊`: `x₁² + x₂²` and `(2x₁)² + x₂²`
    with `ω = (0, 1)`, `min(x₁, x₂)` with `ω = (13, 0)`, `min(x₁, x₂/4)` with `ω = (0, 25)`; then
    `(1, 1) ∈ E(2) \ E(3)` and `(2, 1) ∈ E(3) \ E(2)` (`footnote_71_neither`). The positive part
    `E(r') ⊆ E(mr')` is `footnote_71_mul`.
55. **Equilibrium price sets `E(r)`** are taken in demand form (Chapter 15's `IsDemandEqm`: every
    consumer demands his bundle at `p`, markets clear with equality); under local nonsatiation this
    is Definition 15.B.1 (Chapter 15's `isWalrasEqm_iff_isDemandEqm`).
56. **Convexification (p. 628).** "`z_{ir}(p)` converges as a set to `conv zᵢ(p)`" is proved as
    Hausdorff-distance convergence for every `p ≫ 0` with `Xᵢ = ℝ^L₊` (demand is then bounded),
    with the explicit rate `L·diam zᵢ(p)/r` (`convexHull_near_perReplica`), from the
    Shapley-Folkman theorem (`shapley_folkman`, proved from Carathéodory's theorem), which the
    book does not state. No convexity, continuity or monotonicity of preferences is used.
57. **Near equilibrium (p. 629, footnote 74).** The book declines to define it. `near_equilibrium`
    proves two precise versions for an `r`-replica, given a price `p` at which the convexified
    economy clears (`∑ᵢ x̄ᵢ = ω̄`, `x̄ᵢ ∈ conv xᵢ(p)`): exact clearing with at most `L` of the `Ir`
    consumers off their demand sets, and per-replica excess demand of norm at most
    `L·∑ᵢ diam xᵢ(p)/r` with everyone on his demand set. The existence of such a `p` ("as in
    Section 17.C") is proved for continuous, strongly monotone, possibly nonconvex preferences
    on `ℝ^L₊` with `ωᵢ ≫ 0` (`section_17_I_convexified_existence`, through `exercise_17_C_2`;
    upper hemicontinuity of `p ↦ conv xᵢ(p)` by Proposition 3.AA.1 and a separation argument,
    which needs the compactness of the convex hull of a compact set, proved from Carathéodory's
    theorem). Hence every replica has a near equilibrium (`section_17_I_near_equilibrium_exists`).
    Instances: Figure 17.I.1 at `p̄ = (1, 1)` (`figure_17_I_1_near_equilibrium`) and
    `section_17_I_convexified_instance`.
58. **Appendix A (p. 630): existence of `x(s)`.** The book asserts that every `s ∈ Δ` determines a
    unique Pareto optimal allocation with utilities proportional to `s`. Existence is proved
    (`negishiAlloc_exists`) with continuous, strongly monotone utilities, `uᵢ(0) = 0` and
    `ωᵢ ≥ 0` (strict convexity is not needed); uniqueness (`negishiAlloc_unique`) for every
    `s ≥ 0`, `s ≠ 0`, uses only strict convexity. `uᵢ(0) = 0` is needed when some `sᵢ = 0`.
59. **Exercise 17.AA.1 (p. 649).** Monotonicity is not needed; strict convexity is used as strict
    quasiconcavity of `uᵢ` on a convex `Xᵢ` (`exercise_17_AA_1`).
60. **Exercise 17.AA.2 (p. 649).** "`g(s)` is a function" is formalised as: for every `s ∈ Δ` the
    supporting price of `x(s)` normalized to `Δ` is unique (`NegishiHyp.price_unique`); weak and
    strict support coincide for normalized prices (`quasiSupport_isSupporting`), which is what
    makes the limit of supporting prices supporting in (a). `I ≥ 1` and `L ≥ 1` are assumed. The
    parenthetical sufficient condition is not formalised in general (source map); the instance
    `logEconomy` verifies uniqueness directly. In (d) the fixed-point map is that of Proposition
    17.C.2 on the weight simplex (`negishi_fixed_point`).
61. **Exercise 17.AA.3 (p. 649).** "Increasing" is read as strongly monotone and `I ≥ 1`, `L ≥ 1`.
    The suggested system (welfare maximization for `λ ∈ Δ`, a supporting price, the budget
    equations `p·(ωᵢ - xᵢ) = 0`) is justified by proving that its solutions are exactly the
    Walrasian equilibria (`exercise_17_AA_3`), using Chapter 16's convexity of the utility
    possibility set (Exercise 16.E.2) and `pareto_isWelfareOptimum`.
62. **Exercise 17.I.1 (p. 649).** "Effectively include" is formalised as equality of equilibrium
    price sets between the economy with `kᵢr` consumers of type `i` and the `r`-replica of the
    economy with `kᵢ` consumers of type `i` (`exercise_17_I_1`), with rational proportions
    written as integer proportions (`exercise_17_I_1_rational`).
63. **Exercise 17.I.2 (p. 649).** The production set includes free disposal of output,
    `Y = {(-v, q) : v ≥ 0, q ≤ v²}`, and "the smallest cone containing `Y`" is
    `Y* = {ty : t ≥ 0, y ∈ Y} = {z : z₁ < 0} ∪ {z : z₁ = 0, z₂ ≤ 0}` (`ex17I2Cone_eq`), which is
    also `conv Y` (`ex17I2_convexHull_eq`). The "no useful sense of near equilibrium" is
    formalised as unbounded profits at every price with positive output price
    (`exercise_17_I_2_profit_unbounded`).
64. **Exercise 17.I.3 (p. 649): modelling.** The two "very large" classes are a continuum of mass
    `1/2` each (so a fraction `a` of the poor may take one optimal bundle and `1 - a` another;
    every distribution over the poor's optimal set is of this form since it has at most two
    points); each agent supplies his unit of labor inelastically (labor has no utility value);
    the rich have utility `x₁` on `ℝ²₊` ("spend all their wealth on the high-quality good"). With
    this, (b) and (c) hold as stated for every `0 < β < 1`; in the equilibrium of (c),
    `p₁ = 2p₂`, so the poor are indifferent and split.
65. **Proposition 17.BB.1 (p. 633).** Stated with completeness of `≿ᵢ` (`RationalOn`, the
    chapter's standing rationality assumption) besides convexity of `Xᵢ` and continuity: the
    conclusion "preference maximizing" (`x*ᵢ ≿ᵢ xᵢ` for every `xᵢ` in the budget set) needs
    completeness, since the proof only shows that no budget-feasible bundle is strictly better
    (`proposition_17_BB_1`, `proposition_17_BB_1_eqm`).
66. **Small type after Proposition 17.BB.1 (p. 633).** Situations (a) and (b) give the cheaper
    consumption condition without the "weak condition" `∑ᵢ ωᵢ + ∑ⱼ ŷⱼ ≫ ∑ᵢ x̂ᵢ`
    (`smalltype_17_BB_cheaper_a`, `smalltype_17_BB_cheaper_b`; they use `0 ∈ Yⱼ`, `θᵢⱼ ≥ 0` and,
    in (a), `p ≥ 0`, `p ≠ 0`). The weak condition is what the following paragraph's `p ≫ 0`
    argument uses (`smalltype_17_BB_price_pos`, which needs `∑ᵢ θᵢⱼ = 1`, convex `Xᵢ` and
    rational preferences for Proposition 17.BB.1, but not `x̂ᵢ ≤ ωᵢ`). The p. 632 claim that
    with local nonsatiation (ii') is expenditure minimization on `{xᵢ ≿ᵢ x*ᵢ}` is proved for a
    binding budget `p·x*ᵢ = wᵢ` (`smalltype_17_BB_expenditure`).
67. **Proposition 17.BB.2 (p. 634): hypotheses and proof route.** The hypotheses are bundled in
    `GeneralExistenceHyp` exactly as printed ((i.1)-(i.3), (ii), (iii) compactness of `A` with
    the inequality `∑ᵢ xᵢ ≤ ∑ᵢ ωᵢ + ∑ⱼ yⱼ`), plus the standing valid shares (`θᵢⱼ ∈ [0, 1]`,
    `∑ᵢ θᵢⱼ = 1`); `I, J > 0` are `Nonempty` instances. `L > 0` is not assumed: it follows from
    local nonsatiation. Instance: `bbExample_hyp` (one consumer, one linear technology).
    Departures inside the proof: (1) Lemma 17.BB.1 does not need convexity of `Xᵢ` (convex upper
    contour sets suffice; `lemma_17_BB_1`). (2) The consumer's best response `x̃ᵢ(x, y, p)`
    depends only on `(y, p)` (`bbConsumerBR`). (3) Lemma 17.BB.3 is stated for best responses
    depending on the whole profile, with upper hemicontinuity as Definition M.H.3 on the
    strategy profiles and values in the strategy sets, and `L > 0` (so `Δ ≠ ∅`). (4) Lemma
    17.BB.4 obtains a maximal element of `≿ᵢ` on the compact budget set by the finite
    intersection property (`bb_exists_maximal`) instead of a continuous utility representation
    (footnote 84; the general representation theorem is Chapter 3's
    `econ_debreu_representation`). (5) Lemma 17.BB.5 for consumers uses the convex upper contour
    set of `x''ᵢ` directly; the book's route through Exercise 17.BB.5 is `exercise_17_BB_5`.
    (6) Lemma 17.BB.6 for consumers passes condition (2) to the limit directly (for `x''ᵢ` with
    `p·x''ᵢ < wᵢ(p, y)`, eventually `pⁿ·x''ᵢ < wᵢ(pⁿ, yⁿ)`), rather than through `x''ᵢ ≻ᵢ x'ᵢ`.
    The free-disposal quasiequilibrium is turned into a quasiequilibrium with Exercise 17.BB.4
    applied to any firm.
68. **Footnote 82 (p. 634).** The equilibrium also has `p ≥ 0`, `p ≠ 0` (`footnote_17_BB_82`);
    the instance `bbExample_eqm` applies it.
69. **Footnote 80 / Figure 17.BB.2 (pp. 634-635).** The figure's economy is made concrete:
    `Xᵢ = ℝ²₊`, `ωᵢ = (1, 1)`, `Y = -ℝ²₊` (one firm, shares `1/2`), `u₀ = -(x₁ + x₂)`,
    `u₁ = x₁ + x₂` (`fig17BB2Economy`). The footnote's step "`p ≫ 0`" is not needed: `p ≥ 0`
    (free disposal) and zero profits already give `p·x*₀ ≥ p·ω₀ > 0` (`footnote_17_BB_80`).
70. **Exercise 17.BB.2 (p. 650): modelling.** Pure exchange is `Xᵢ = ℝ^L₊` with every firm the
    free disposal technology (at least one firm; profits then vanish). "Desires only the goods
    in `Dᵢ`, strongly monotone in them" is `PrefStronglyMonotoneIn`: `y ≥ x` on `Dᵢ` with a
    strict inequality in `Dᵢ` implies `y ≻ᵢ x`, whatever the other coordinates; holdings are
    `ωᵢ ≥ 0`. Indecomposability (`Indecomposable`) quantifies over every split `G`, `Gᶜ` (which
    covers "one of the groups"). Rationality and continuity are used (Proposition 17.BB.1).
    Instance: `ex17BB2_instance`.
71. **Exercise 17.BB.3 (p. 650).** The sign claims are proved at the level of one consumer and
    for any `L`: no demand at `p ≪ 0` (rational, continuous, locally nonsatiated preferences on
    `ℝ^L₊`, `exercise_17_BB_3_not_both_negative`), and no demand at any `p ≤ 0` once preferences
    are also strictly convex (`exercise_17_BB_3_no_demand`); hence at every equilibrium some
    price is positive (`exercise_17_BB_3_pos_price`, `exercise_17_BB_3_eqm`). The existence part
    ("the offer curves must cross") is OPEN (source map).
72. **Exercise 17.BB.8 (pp. 650-651): modelling.** The consumption sets are a field of
    `ExtEconomy` (`ℝ^L₊` in the book) so that (e) can use `log x₁ + x₂` on `{x₁ > 0, x₂ ≥ 0}`;
    (e) is worked for one consumer and one firm (`β = 1`, so aggregate output is `α V` however
    labor is split), with equilibrium `V = 1` and optimum `V = 1 + ρ`. (c) assumes `J > 0`,
    `0 < β ≤ 1`, `γ, ρ ≥ 0` and represents the sectoral set in (labor, output) coordinates;
    returns to scale are stated for the frontier `c V^{ρ+β}`. (b) is OPEN (source map): the
    route of Appendix B gives, at best, a quasiequilibrium, and with `ρ_ℓ > 0` a sector with
    zero aggregate labor has `α_ℓ = 0`, so the step from quasiequilibrium to equilibrium needs an
    argument (or an extra assumption) excluding a zero wage with idle sectors (not formalised).
73. **Exercise 17.BB.9 (p. 651).** The aggregate player's consumers use the limited-liability
    wealth `bbWealth`, equal to the book's `p·ωᵢ + ∑ⱼ θᵢⱼ p·yⱼ` because profit maximizing
    `yⱼ ∈ Ŷⱼ ∋ 0` have nonnegative profits; all profit maximizing `yⱼ` have the same profit, so
    the aggregate response is convex valued (`bbAggResponse_convex`).
74. **Footnote 62 (p. 623), `L = 3`.** The counterexample is Scarf's (1960) economy
    (`scarfEconomy`): consumer `i` owns one unit of good `i` and has utility `min(xᵢ, xᵢ₊₁)`.
    Its equilibrium is unique (the ray `p₁ = p₂ = p₃`, `scarfZ_eqm_iff`); `∑ pₗ²` and `p₁p₂p₃`
    are constant along tâtonnement trajectories (`c = (1, 1, 1)`), trajectories exist
    (`scarf_tat_exists`), and none starting off the ray converges to an equilibrium
    (`scarf_not_converge`; from `(1, 2, 2)`: `footnote_17_62_three_goods`). Departure: Leontief
    preferences are only weakly monotone, and the excess demand satisfies (i)-(iv) of
    Proposition 17.B.2 but not the boundary condition (v) (`scarfZ_not_boundary`); the footnote
    itself states no hypotheses. A counterexample satisfying (v) as well is not constructed.
75. **Exercise 17.AA.2 (p. 649), the parenthetical sufficient condition.** Proved as
    `exercise_17_AA_2_sufficient`: with the exercise's other hypotheses (continuity, strong
    monotonicity, `uᵢ(0) = 0`, `ωᵢ ≥ 0`; strict convexity is not used), if every `uᵢ` has a
    nonzero derivative at strictly positive bundles and at every Pareto optimum some consumer
    has a strictly positive bundle, the supporting price of `x(s)` in `Δ` is unique for every
    `s ∈ Δ`. Departure: "differentiable" is read as differentiable with a nonzero derivative
    there. A differentiable representation can have a zero derivative at a kink of an
    indifference curve (e.g. `(v(x) - v(x̄))³` with `v` kinked at `x̄`), and then the supporting
    price is not determined (not formalised). Instance: `exercise_17_AA_2_sufficient_instance`.
