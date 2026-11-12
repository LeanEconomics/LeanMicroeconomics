# Corrections and departures

MWG, Chapter 3. **Part A** (Sections 3.B-3.D, Exercises 3.B.1-3.D.8, Appendix M.C, M.F, M.J,
M.K) is listed first; later parts append their items. Each item gives what the book says,
what is proved, and the Lean names.

## Part A: Sections 3.B-3.D and Appendix M.C, M.F, M.J, M.K

1. **Exercise 3.B.1 (p. 43) needs a commodity.** With `L = 0`, `ℝ^0_+ = {0}` and the
   everywhere-indifferent relation is strongly monotone but neither monotone nor locally
   nonsatiated (`exercise_3_B_1_needs_commodity`). Proved with `0 < L`: `exercise_3_B_1a`,
   `exercise_3_B_1b` (the latter also uses the free-disposal assumption made for
   Definition 3.B.2).

2. **Small type, p. 44.** "The convexity assumption can hold only if `X` is convex" is proved
   for complete preferences (`convex_of_prefConvex`); for incomplete relations it can fail
   (the empty relation has convex, empty upper contour sets on any `X`).

3. **Exercise 3.C.3 (p. 96) needs rationality.** Closed upper and lower contour sets do not
   imply Definition 3.C.1 for a general relation: on `ℝ¹_+`, relating each `1/(n+1)` only to
   itself gives closed (singleton) contour sets but violates continuity at `0`
   (`exercise_3_C_3_needs_rationality`). Proved for rational `≿` (as assumed throughout 3.B):
   `exercise_3_C_3`.

4. **Examples 3.D.1-3.D.2 (pp. 55-57).** The book uses `α ln x₁ + (1-α) ln x₂` with
   `ln 0 = -∞`. Real logarithms in Lean have `log 0 = 0`, so the book's problem is formalized
   with the Cobb-Douglas utility `k x₁^α x₂^{1-α}` itself (`example_3_D_1`), which has the same
   demand; the book's indirect utility is the logarithm of the Cobb-Douglas one
   (`example_3_D_2_log`). Existence and the demand formula hold for all `w ≥ 0`.

5. **Theorem M.J.2 (p. 955) misprint.** The hypothesis is printed `f(x̄) = 0`; the proof uses
   `∇f(x̄) = 0`. As printed, part (ii) is false: `f(x) = x - x²` has `f(0) = 0` and
   `D²f(0) = -2` negative definite, but `0` is not a local maximizer
   (`theorem_M_J_2_printed_counterexample`). Proved with `∇f(x̄) = 0` (needed only for (ii)):
   `theorem_M_J_2_i`, `theorem_M_J_2_ii`, `theorem_M_J_2_ii_strict`, assuming `f`
   differentiable near `x̄` with `∇f` differentiable at `x̄` (weaker than `C²`).

6. **Theorem M.C.4 (p. 935).** The printed "if and only if" fails in the "if" direction:
   `f(x) = x⁴` on `ℝ` has `z f''(x) z ≤ 0` whenever `f'(x) z = 0`, but is not quasiconcave
   (`theorem_M_C_4_if_false`). Proved: the "only if" direction (`theorem_M_C_4_necessity`) and
   the strict sufficiency printed as the theorem's second sentence (`theorem_M_C_4_strict`).
   Theorems M.C.2 and M.C.4 assume an open convex domain (footnote 4) and, instead of `C²`,
   differentiability on `A` with `∇f` differentiable at each point (`theorem_M_C_2`,
   `theorem_M_C_2_strict`).

7. **Theorems M.K.1-M.K.2 (pp. 956, 959): differentiability.** The book assumes only
   differentiability; we assume strict differentiability at `x̄` (implied by continuous
   differentiability), as Mathlib's Lagrange multiplier theorem does (`theorem_M_K_1`,
   `theorem_M_K_2`). The book's proof of M.K.2 covers `M = 0` and assumes, rather than
   proves, that `x̄` solves the linearized problem; `theorem_M_K_2` covers general `M`, `K`
   and proves that step with the implicit function theorem (`mk_curve`). The
   merely-differentiable case is OPEN. The constraint qualification is stated as linear
   independence of the derivatives (equivalently, full row rank of the Jacobian).

8. **Theorem M.K.4 (p. 962).** "There is a unique global constrained maximizer" is false as
   to existence: `f(x) = x` is strictly quasiconcave on the convex set `C = ℝ` and has no
   maximizer (`theorem_M_K_4_no_existence`). Proved: at most one maximizer
   (`theorem_M_K_4`).

9. **Theorem M.K.6 (p. 963).** Continuity of the constraint correspondence (Section M.H) is
   expressed through Kreps's sequential upper and lower hemicontinuity plus a local compact
   bound (`theorem_M_K_6`); this matches compact-valued continuous correspondences into
   `ℝ^N`. Upper hemicontinuity of the maximizer correspondence is delivered as a closed graph
   with a local compact bound.

10. **Theorem M.K.3 (p. 961).** The constraint qualification is not needed for sufficiency;
    `theorem_M_K_3` omits it, and uses (M.K.9) only at `x̄`.

11. **Theorem M.K.5 (p. 963).** Proved for equality constraints without the envelope theorem
    and without differentiability of the solution: it suffices that `v` bounds the objective
    on nearby constraint sets, equals it at `x̄`, and is differentiable at `b̄`
    (`theorem_M_K_5`).

12. **Section M.K, p. 958, Lagrangian.** The book writes `L(x, λ) = f(x) - ∑ λ_m g_m(x)` and
    reads the constraints off `∂L/∂λ = 0`, which gives `g_m(x) = 0` rather than `g_m(x) = b̄_m`.
    We use `f(x) - ∑ λ_m (g_m(x) - b̄_m)` (`lagrangian`, `lagrangian_stationary_iff`).

13. **Domains and generality (no correction).** Proposition 3.C.1 is proved on `ℝ^L_+` and on
    every convex `X` without monotonicity (Debreu's theorem via Kreps), and the book's own
    monotone construction separately; Proposition 3.D.1 for `w ≥ 0`; Walras' law
    (Prop. 3.D.2(ii)) for any price vector; the Kuhn-Tucker conditions for the UMP
    (`ump_kuhn_tucker`) without any constraint qualification, as footnote 8 asserts.

14. **Exercise 3.D.3(b) (p. 97).** The book assumes `u` differentiable and strictly
    quasiconcave. The proof needs every bundle to be demanded at some prices; we assume `u`
    continuous and quasiconcave on `ℝ^L_+` with `∇u(x) ≫ 0` for `x ≫ 0` (monotonicity, as in
    Section 3.D), which suffices (`demanded_at_supporting_prices`, `exercise_3_D_3b_full`).

15. **Small type, p. 55.** The sufficiency of the Kuhn-Tucker conditions is proved under the
    book's hypotheses (quasiconcave, monotone, `∇u(x*) ≠ 0`), together with continuity of `u`,
    `w > 0` and an exhausted budget, which the book's UMP setting provides
    (`ump_kuhn_tucker_sufficient_quasiconcave`). `∇u ≠ 0` is needed only at `x*`.

16. **Figure 3.C.3 (p. 49).** Proved in the form: no utility representing Leontief
    preferences on `ℝ²_+` is differentiable at every point of `ℝ²_{++}` (`figure_3_C_3`).

## Part B: 3.E-3.G, M.E, M.G, M.L

MWG, Chapter 3, Sections 3.E-3.G, Exercises 3.E.1-3.G.18 and Mathematical Appendix M.E, M.G,
M.L. Each item gives what the book says, what is proved, and the Lean names.

B1. **Proposition 3.F.1 (p. 66), the duality theorem, needs convexity.** The book states it
    for every nonempty closed `K`. The direction "`μ_K` differentiable at `p̄` ⇒ a unique
    minimizer `x̄`, and `∇μ_K(p̄) = x̄`" holds for every nonempty closed `K`
    (`duality_unique_of_differentiable`, `footnote_3_F_14`). The converse is false for
    nonconvex sets: `K = {0} ∪ {x ∈ ℝ² : x₂ = 1}` is closed, `0` is the unique minimizer of
    `p̄·x` at `p̄ = (0, 1)`, but `μ_K(δ, 1) = -∞` for every `δ > 0`, so `μ_K` is not
    differentiable at `p̄` (`proposition_3_F_1_nonconvex_counterexample`). The full theorem is
    proved for nonempty closed convex `K` (`proposition_3_F_1`), as the task required.
    "Differentiable" for the extended-real `μ_K` is read as finite near `p̄` and differentiable
    (`SupportDifferentiableAt`).

B2. **Exercise 3.E.1 (p. 61) needs a constraint qualification.** "Assume `u` is
    differentiable; show the first-order conditions are `p ≥ λ∇u(x*)`,
    `x*·[p - λ∇u(x*)] = 0` for some `λ ≥ 0`" is false without one: for `L = 1`,
    `u(x) = (x - 1)³`, `p = 1`, `ū = 0 > u(0)`, the EMP solution is `x* = 1`, `u'(1) = 0`, and
    `x*·[p - λu'(x*)] = 1 ≠ 0` for every `λ` (`exercise_3_E_1_counterexample`). Proved: at an
    EMP solution the UMP conditions hold at wealth `p·x*` with some `λ ≥ 0`, and whenever
    `λ > 0` (e.g. some consumed good has nonzero marginal utility,
    `exercise_3_E_1_lam_pos`) the EMP conditions hold with multiplier `1/λ`
    (`exercise_3_E_1`). This is also the comparison with the UMP that the exercise asks for.

B3. **Exercise 3.E.4 (p. 98) misprint.** "If `u(x)` is strictly convex, then `h(p, u)` is
    single-valued" is false: `u(x) = x₁² + x₂²` is strictly convex, but at `p = (1, 1)`,
    `ū = 1` both `(1, 0)` and `(0, 1)` solve the EMP
    (`exercise_3_E_4_printed_counterexample`). Proved with `≿` strictly convex (`u` strictly
    quasiconcave), as in Proposition 3.E.3(iii): `exercise_3_E_4_unique`,
    `proposition_3_E_3_iii`.

B4. **Proposition 3.G.4 (p. 73), Roy's identity, needs `∂v/∂w ≠ 0`.** The book divides by
    `∂v(p̄, w̄)/∂w` without assuming it is nonzero. For `L = 1` and `u(x) = (x - 1)³` on
    `ℝ_+` (continuous, locally nonsatiated, strictly convex), `v(p, w) = (w/p - 1)³` is
    differentiable at `(1, 1)` with zero derivative, while `x(1, 1) = 1`; the printed formula
    gives `0/0` (`proposition_3_G_4_printed_counterexample`). Proved: `∂v/∂p_l + (∂v/∂w) x_l = 0`
    always, and Roy's formula when `∂v/∂w ≠ 0` (`proposition_3_G_4`). Exercises 3.G.1, 3.G.7,
    3.G.8, 3.G.11, 3.G.13 carry the corresponding nonvanishing hypotheses.

B5. **Definition M.G.3 and footnote 14 (p. 946) omit distinctness.** As printed, `x ∈ B` is
    extreme if it is not `αy + (1-α)z` for any `y, z ∈ B`, `α ∈ (0, 1)`; taking `y = z = x`
    shows no point of any set is extreme (`definition_M_G_3_printed_vacuous`). Likewise a set
    is "strictly convex" if `αx + (1-α)x'` is interior for all `x, x' ∈ A`; taking `x = x'`
    forces `A` open (`footnote_M_G_14_printed_open`), so the closed interval `[-1, 1]` fails
    it although it is strictly convex (`footnote_M_G_14_printed_counterexample`). Corrected
    (with `y ≠ z`, `x ≠ x'`) these are Mathlib's `extremePoints` and `StrictConvex`
    (`definition_M_G_3`, `footnote_M_G_14`).

B6. **Theorems M.G.2-M.G.3 (pp. 948-949) side conditions.** The first part of M.G.2 and M.G.3
    need `N ≥ 1`: in `ℝ⁰` the closed convex set `∅` and the point `0 ∉ ∅` admit no `p ≠ 0`
    (`theorem_M_G_2_i_needs_dimension`). The second part of M.G.2 needs nonempty sets: `∅`
    and `ℝ^N` are disjoint convex sets that no hyperplane separates
    (`theorem_M_G_2_ii_needs_nonempty`). Proved with these conditions: `theorem_M_G_2_i`,
    `theorem_M_G_2_ii`, `theorem_M_G_3`.

B7. **Departures (no correction).**
    - Proposition 3.E.1(i) does not need `w > 0` (`proposition_3_E_1_i`); 3.E.3(ii) is
      proved for `ū ≥ u(0)` (`proposition_3_E_3_ii`); the compensated law of demand (3.E.5)
      holds for arbitrary selections from `h` (`proposition_3_E_4`); Proposition 3.E.2(iv),
      whose proof the book omits, is proved on `{(p, ū) : p ≫ 0, ū attainable}` via the
      continuity of `v` (`proposition_3_E_2_iv`).
    - Proposition 3.G.1 does not need local nonsatiation; "for all `p` and `u`" means `p ≫ 0`
      and `ū` attainable, the book's standing assumption (`proposition_3_G_1`).
    - Proposition 3.G.2 assumes only that `h(·, ū)` is differentiable at `p̄` (the book: `C¹`);
      negative semidefiniteness is derived from (3.E.5), as on p. 70.
    - Proposition 3.G.3 assumes a differentiable Walrasian demand function; differentiability
      of `h(·, ū)` at `p̄` is derived, not assumed (`proposition_3_G_3`).
    - Theorem M.E.1 is proved for strictly differentiable systems (implied by `C¹`) with a
      separate `C^n` version, on Banach spaces; Theorem M.L.1 is proved along a differentiable
      feasible maximizer path, as in the book's proof (`theorem_M_L_1`); the version assuming
      only that `v` is differentiable is OPEN.
    - Exercise 3.F.1 in half-space form needs `L ≥ 1` (`exercise_3_F_1_halfspaces`); in the
      support-function form it holds for every `L` (`exercise_3_F_1`). Exercise 3.F.2 does not
      need `K` closed (`exercise_3_F_2`).
    - Exercise 3.E.10's first sentence names "Proposition 3.E.4"; the text on p. 62 describes
      the exercise as deriving the properties of `h` from those of `x` and back, i.e.
      Proposition 3.D.2 ⟺ Proposition 3.E.3, which is what is proved
      (`exercise_3_E_10_forward`, `exercise_3_E_10_backward`). Exercises 3.E.9 and 3.E.10 are
      proved for abstract functions satisfying only the relations (3.E.1)/(3.E.4), with the
      actual `e`, `v` shown to satisfy them (`equation_3_E_1_instance`).
    - Exercise 3.E.7 uses the quasilinear utility `x_k + φ(x)` (part A's
      `exercise_3_C_5b_if` form; the "only if" of Exercise 3.C.5(b) is OPEN in part A).
    - Example 3.E.1 uses `x₁^α x₂^{1-α}` (part A's correction 4); the formulas hold for
      `ū > 0 = u(0)`.

## Part C: 3.J, Appendix 3.A, M.H

MWG, Chapter 3, Section 3.J, Appendix A to Chapter 3, Exercises 3.J.1 and 3.AA.1, and
Mathematical Appendix M.H. Each item gives what the book says, what is proved, and the Lean names.

C1. **Definition 3.J.1 (p. 91) must exclude one-element lists.** As printed, the strong axiom
    quantifies over every list `(p¹, w¹), ..., (p^N, w^N)`. For `N = 1` both hypotheses are vacuous
    and the conclusion reads `p¹·x(p¹, w¹) > w¹`, which fails for every demand function that is
    affordable at some `(p, w) ≫ 0`, in particular for every demand satisfying Walras' law
    (`strongAxiomPrinted_false`, `strongAxiomPrinted_false_of_walrasLaw`). `StrongAxiom` takes
    lists of length at least two (indexed `0, ..., N`, `N ≥ 1`); it is implied by the printed form
    (`strongAxiom_of_printed`) and is equivalent to irreflexivity of `≻²`
    (`strongAxiom_iff_acyclic`), which is what the proof of Proposition 3.J.1 uses.

C2. **Exercise 3.J.1 (p. 104) is proved under Walras' law.** The exercise speaks of "`x(p, w)`";
    `exercise_3_J_1` assumes Walras' law, the standing assumption on Walrasian demand under which
    Section 2.F studies the weak axiom. The direction SA ⇒ WA needs nothing
    (`weakAxiom_of_strongAxiom`); the direction WA ⇒ SA (`strongAxiom_of_weakAxiom_two`, Rose's
    theorem) uses `p·x(p, w) = w` to place each observed bundle on its budget line.

C3. **"When `L > 2` the SA is stronger than the WA" (p. 92): the witness has consumption set
    `ℝ³`.** `strongAxiom_stronger_three` uses MWG Ch. 2's demand of Exercise 2.F.15 (Walras' law and
    the weak axiom are Ch. 2's `exercise_2_F_15_basic`, `exercise_2_F_15_weakAxiom`), which takes
    negative values in good 2, and exhibits an explicit seven-bundle revealed-preference cycle. A
    witness with values in `ℝ³_+` (e.g. Gale's example) is not formalized.

C4. **Proposition 3.AA.1 (p. 93) does not need local nonsatiation.** The book assumes that `u`
    represents locally nonsatiated preferences; its proof uses only continuity of `u` and `w̄ > 0`.
    `proposition_3_AA_1` and `proposition_3_AA_1_continuous` drop the assumption;
    `proposition_3_AA_1_stated` keeps it as printed. Definition 3.AA.1 (`DemandUHCAt`) quantifies
    over sequences of price-wealth pairs `≫ 0`, the domain of `x(p, w)`.

C5. **Figure 3.AA.3 (p. 94) with a concrete utility.** The figure fixes no utility; the dashed
    indifference between `(0, 1)` and `z` (with `z₁ > w̄`) is realised by `u(x) = x₁ + 2w̄x₂`
    (`figure_3_AA_3_utility`). With it the book's claims are proved: demand `(w̄, 0)` for
    `p₂ > w̄`, `(0, 1)` at `(1, w̄, w̄)`, failure of the locally cheaper test and of upper
    hemicontinuity.

C6. **Differentiability (pp. 94-95): smoothness on `x ≫ 0`.** The book assumes `u` strictly
    quasiconcave and `C²` with `∇u(x) ≠ 0` "for all `x`", and `x(p, w) ≫ 0` for all `(p, w) ≫ 0`.
    A utility that is `C²` on all of `ℝ^L` cannot have the boundary behaviour (e.g. infinite
    marginal utility at `0`) that usually delivers interior demand everywhere, so the theorems
    assume `C²`, strict quasiconcavity and `∇u ≠ 0` on `x ≫ 0` only, with continuity on `ℝ^L_+`
    and local nonsatiation (for Walras' law, as in Section 3.D). The statement "differentiable iff
    the bordered Hessian determinant is nonzero" is proved in both directions
    (`appendixA_differentiable_iff_bordered`, `appendixA_differentiable_iff_bordered_primitive`);
    the "only if" direction uses `∇u(x(p, w)) ≠ 0` (so `λ ≠ 0`). The multiplier is identified as
    `λ = ∇u(x)·x / w`. `appendixA_oneGoodUtility_assumptions` shows the hypotheses are consistent.

C7. **Section M.H: unused hypotheses dropped.** Theorem M.H.1 assumes a closed range `Y` and
    Definition M.H.4 a compact `Y`; neither is used (`theorem_M_H_1`, `LowerHemicontinuousMWG`,
    `lhc_singleton_iff`). `Y` appears only where the book uses it: closedness of the graph relative
    to `A × Y` (`hasClosedGraph_iff_closure`), the compact-range case
    (`uhc_iff_hasClosedGraph_of_isCompact`) and footnote 19 (`footnote_M_H_19`). Correspondences are
    stated for metric spaces `α`, `β` (`β` proper where Bolzano-Weierstrass is used), with `ℝ^N`,
    `ℝ^K` and the figures' `ℝ` as instances. The figures' correspondences are concrete choices
    matching the drawings (`figure_M_H_1a`, ..., `figure_M_H_3`).

## Part D: 3.H-3.I

MWG, Chapter 3, Sections 3.H-3.I and Exercises 3.H.1-3.I.12. Each item gives what the book says,
what is proved, and the Lean names.

D1. **Exercise 3.H.1 (p. 102): the recovered utility and the minimum.** The book defines
    `u(x) = Sup {u : x ∈ V_u}` for `x ≫ 0` and claims `e(p, u) = Min {p·x : u(x) ≥ u}`. Two
    problems. (i) As a real number the supremum can be over the empty set: for
    `e(p, u) = (1 + exp u) p₁` on `ℝ¹` and `x = 1/2`, no `u` has `x ∈ V_u`
    (`exercise_3_H_1_sup_empty`); it can also be over an unbounded set. Proved with the supremum
    in `EReal` (`recoveredUtility`). (ii) With the domain `x ≫ 0` the minimum need not exist:
    `e(p, u) = exp(u) p₁` on `ℝ²` satisfies every hypothesis, but no `x ≫ 0` with `U(x) ≥ u`
    attains `p·x = e(p, u)` (`exercise_3_H_1_min_not_attained`, `integExpFamily`). Proved: the
    minimum over `x ∈ ℝ^L_+` (`exercise_3_H_1`, with continuity of `e` in `p` and
    nondecreasing, continuous `e` in `u`, which "continuous" and "increasing" in the book
    provide), and the infimum over `x ≫ 0` (`exercise_3_H_1_pos`).

D2. **Small type, p. 78: "this set is the convex hull" of the actual at-least-as-good set.**
    `V_u` is closed, so it is the *closed* convex hull. Proved for a nonempty actual set that is
    closed upward in `ℝ^L_+` (monotone preferences): `V_u = closure (convexHull K)`
    (`recoveredSet_eq_closure_convexHull`). Whether the closure can be dropped is not settled
    here (no counterexample is claimed).

D3. **Proposition 3.I.2 (p. 88): "for all `α < ᾱ`".** At `α = 0` (and `α < 0`) the conclusion
    `e((1 - α)p⁰ + αp¹, u⁰) > w` fails (`= w` at `α = 0`). Proved for `α ∈ (0, ᾱ)`
    (`proposition_3_I_2`), with differentiability of `e(·, u⁰)` at `p⁰` only.

D4. **Exercise 3.I.2 (p. 86): "if `h₁(p, u⁰)` is strictly decreasing in `p₁`, the derivatives
    are strictly positive at all `t > 0`".** The derivative of the deadweight loss at a fixed
    utility level is `-t ∂h₁/∂p₁(p⁰₁ + t)` (`exercise_3_I_2`); a strictly decreasing
    differentiable function can have a zero derivative at a point (`-(s - c)³`), so strict
    decrease gives only `≥ 0`, and `> 0` holds exactly when `∂h₁/∂p₁ < 0` (proved as an iff in
    `exercise_3_I_2`). Such a Hicksian demand curve exists by Proposition 3.H.1 (e.g.
    `e(p, u) = u p₂ f(p₁/p₂)` with `f' = exp(-(r - 1)³)`); that consumer is not built in Lean.
    The theorem treats (3.I.6) exactly and (3.I.5) with `u¹` held fixed; in (3.I.5) `u¹`
    depends on `t`, and the derivative of that measure is not formalized.

D5. **Strict inequalities between EV and CV (p. 83 and Exercise 3.I.3, p. 102).** "When good 1
    is normal, `EV > CV`" and "if `p¹ ≤ p⁰` and good `ℓ` is inferior, `CV > EV`" fail when
    `p¹ = p⁰` (both are `0`; `exercise_3_I_3_printed_counterexample` holds for every consumer),
    and in general the inequalities are weak. Proved: `CV ≤ AV ≤ EV` for a normal good and
    `EV ≤ AV ≤ CV` for an inferior good, for price falls and rises
    (`normal_good_cv_le_av_le_ev`, `inferior_good_ev_le_av_le_cv`); and `CV > EV` when the price
    falls strictly, the good is consumed at `p⁰` and its demand is strictly decreasing in
    wealth (`exercise_3_I_3`). "Normal" and "inferior" are used in the global sense
    (`x_ℓ(p, ·)` monotone in wealth along the price line), which follows from the book's
    derivative sign condition by the mean value theorem.

D6. **Equation (3.I.6), p. 85, first line: misprint.** The book prints
    `-CV(p⁰, p¹, w) - th₁(p¹, u) = ...`; the term is `th₁(p¹, u⁰)` (as in the text above it and
    the following lines). Proved with `u⁰` (`example_3_I_1_u0`).

D7. **Exercise 3.I.8(d), p. 103: parameter values.** The values `b₁ = c₂ = 1` violate the
    restriction `b₁ ≤ 0`, `c₂ ≤ 0` that part (b) derives from utility maximization (own-price
    effects of goods without wealth effects are Slutsky diagonal terms, hence `≤ 0`), so no
    utility-maximizing consumer has this demand. The computations are carried out as asked
    (`EV₁ = EV₂ = -7/2`, `EV₃ = -15/2`, and `EV₃ = EV₁ + EV₂` iff `c₁ = 0`), together with
    the violated restriction (`exercise_3_I_8d`, `exercise_3_I_8b`).

D8. **Departures (no correction).**
    - Proposition 3.H.1 is proved under weaker hypotheses than printed: differentiability at the
      given `p` only, without strict monotonicity in `u` or continuity (`proposition_3_H_1`).
    - The integrability theorem (pp. 75-80) is proved conditionally on a solution of (3.H.2)
      (`integrability_theorem`, `integrability_of_pde`); the existence of the solution is OPEN
      for `L > 2`, and for `L = 2` only local existence is proved (see the OPEN table).
    - Section 3.I's integral formulas assume strictly convex preferences (single-valued
      demands, as the book assumes "whenever convenient") and use the Walrasian demand
      selection `xs` with `h(p, ū) = x(p, e(p, ū))`.
    - Exercise 3.I.5 is proved on the quasilinear consumption set with `p_k = 1`, for the
      expenditure function on that set (`expenditureOn`), assuming the expenditure minimization
      is bounded below; the indirect utility can be any function.
    - Exercise 3.I.7(e): the "small" revenue `R` is the linearized revenue constraint
      `t·x⁰ = R`; the deadweight loss is exact (`exercise_3_I_7e_deadweight`).
    - EV in Exercises 3.I.7-3.I.8 is the line integral of demand (exact without wealth
      effects, `marshallian_surplus`, `exercise_3_I_1`).
    - Exercise 3.I.9 is first proved without the hypothesis `s_ll < 0` (`exercise_3_I_9`: zero
      tax is optimal, weakly); `s_ll < 0` gives strict optimality (`exercise_3_I_9_strict`).

## Part E: closing items across 3.C-3.G, 3.AA.2, M.G, M.K

MWG, Chapter 3 and Mathematical Appendix: items closed in the `Closer*` modules. Each item gives
what the book says, what is proved, and the Lean names.

E1. **Exercise 3.D.5 and 3.E.6 (pp. 97-98), CES domain.** The utility
    `(x₁^ρ + x₂^ρ)^{1/ρ}` (`α₁ = α₂ = 1`) is used for `ρ < 1`, `ρ ≠ 0`, and for `ρ < 0` it is
    extended by `0` on the boundary of `ℝ²_+` (its limit), as in Kreps's `CESUtility`
    (`cesUtility`, `cesUtility_eq_extend`). Exercise 3.E.6 is proved for `ū ≥ 0`, the range of
    `u` on `ℝ²_+` (`exercise_3_E_6_hicksian`, `exercise_3_E_6_expenditure`). The linear limit
    `ρ → 1⁻` is proved separately for `p₁ < p₂`, `p₂ < p₁` (convergence to the unique linear
    demand) and `p₁ = p₂` (the CES demand is constant and lies in the linear demand
    correspondence) (`exercise_3_D_5c_limit_linear_lt`, `..._gt`, `..._eq`). The elasticity of
    substitution is the elasticity of the demand ratio as a function of the price ratio
    (`elasticityOfSubstitution`); for linear utility the demand ratio is not a function, and the
    book's "`ξ = ∞`" is formalized as the limit `1/(1 - ρ) → ∞` (`exercise_3_D_5d_limits`).

E2. **Exercise 3.D.6 and 3.G.3 (pp. 98-99), the linear expenditure system.** The book's
    `(x₁ - b₁)^α (x₂ - b₂)^β (x₃ - b₃)^γ` is only meaningful on `{x ≫ b}`. It is formalized as
    `∏_l (max (x_l - b_l) 0)^{a_l}` (`lesUtility`), which is the book's formula on `{x ≥ b}` and
    `0` elsewhere, with `b ≥ 0`, `a ≫ 0`, `w > p·b` (and `ū > 0` for the EMP); this keeps `u`
    continuous on `ℝ³_+`. All results hold for any number `L ≥ 1` of goods; Exercise 3.G.3(e)'s
    "rank 2" is the case `L = 3` of `rank S = L - 1` (`exercise_3_G_3e`,
    `exercise_3_G_3e_three`). Partial derivatives are one-variable derivatives along each price
    (`Function.update p k t`).

E3. **Exercise 3.G.4(a) (p. 99), "preserved only under linear transformations".** Proved in the
    form: if `f` is increasing on `[0, ∞)` and `f(x₁ + x₂) = v₁(x₁) + v₂(x₂)` on `ℝ²_+`, then
    `f(s) = cs + d` on `[0, ∞)` (`exercise_3_G_4a_only_affine`). The transformation is affine
    (the book's "linear"); exhibiting one additively separable `u` already forces this.

E4. **Exercise 3.G.4(c)-(d) (p. 99).** As the book permits ("you can assume differentiability
    and interiority"), interior solutions are characterized by the first-order conditions
    `u_l'(x_l) = λ p_l`, and strict concavity enters as strictly decreasing `u_l'`. The results
    are proved for finite changes: a rise in wealth raises every demand (`exercise_3_G_4c`), and
    a rise in `p_k` strictly raises every other demand (`exercise_3_G_4d`). For (d) this gives
    `∂x_l/∂p_k ≥ 0`; the strict derivative inequality `∂x_l/∂p_k > 0` printed in the book is
    not claimed.

E5. **Small type, pp. 66-67 (Figure 3.F.5).** The one-sided directional derivatives of `μ_K` are
    proved for nonempty **compact** `K` (Danskin's theorem: `closerDuality_right_derivative`,
    `closerDuality_left_derivative`, `proposition_3_F_small_type`); the book's `K` is closed and
    the figure's `K` unbounded. For closed `K` the right derivative can fail to exist
    (`proposition_3_F_1_nonconvex_counterexample` of part B gives `μ_K = -∞` off `p̄`).

E6. **Section M.K, p. 958, second-order conditions.** The book prints
    `D²_x L(x̄, λ) = D²f(x̄) - ∑ λ_m ∇g_m(x̄)`, a misprint for `∑ λ_m D²g_m(x̄)`; the theorem is
    stated with the second derivative of the Lagrangian `lagrangian` itself, required in the
    sense of Theorem M.J.2 (differentiable near `x̄`, gradient differentiable at `x̄`) rather
    than `C²` (`theorem_M_K_second_order_sufficient`). Sufficiency is proved and gives a
    **strict** local maximizer; necessity remains OPEN.

E7. **Theorem M.K.5 (p. 963) with inequality constraints.** As for equality constraints
    (correction 11 of part A), neither the constancy of the binding set on a neighborhood nor a
    differentiable solution is needed: it suffices that `v` bounds the objective on nearby
    constraint sets, equals it at `(b̄, c̄)`, and is differentiable there. The constraint
    qualification is linear independence of the gradients of the equality and binding
    inequality constraints (`theorem_M_K_5_inequality`).

E8. **Exercise 3.C.5(b) "only if" (p. 96).** The function `φ` is stated as `φ : ℝ^L → ℝ` invariant
    under shifts of the numeraire (`φ(x + t e_k) = φ(x)`), i.e. a function of `x_{-k}`, matching
    the "if" direction of part A (`exercise_3_C_5b_only_if`). The book's hint cites
    "Proposition 3.G.1"; the continuous representation used is Proposition 3.C.1
    (`proposition_3_C_1_convex`).

E9. **Exercise 3.G.6(e) (p. 100).** Proved: under the restrictions of (c), `x₁ ≡ x₂`, so goods 1
    and 2 are perfect complements (`exercise_3_G_6e`). The resulting form `U(min {x₁, x₂}, x₃)`
    of `u` is stated verbally, since many utilities generate the same demand on the observed
    domain.

E10. **Exercises 3.G.9, 3.G.10, 3.G.12 (pp. 100-101).** 3.G.9 is the quotient-rule computation
     of `s_lk` from the partial derivatives of `v` (`exercise_3_G_9`). 3.G.10 gives necessary and
     sufficient conditions on `a`, `b` for homogeneity, monotonicity in `w` and in prices, and
     continuity (`exercise_3_G_10_*`); quasiconvexity is a condition on `v` that does not reduce
     to separate conditions on `a` and `b`. 3.G.12 starts from the Gorman-form demand
     `x = -(∇a + w∇b)/b` of Exercise 3.G.11 (`exercise_3_G_12_homothetic`,
     `exercise_3_G_12_quasilinear`).

E11. **Exercise 3.G.2 (p. 99).** Cobb-Douglas preferences are not strictly convex on `ℝ²_+`, so
     the general Propositions 3.G.1-3.G.4 of part B do not apply. The exercise is verified
     directly, Cobb-Douglas being the linear expenditure system with `b = 0`
     (`exercise_3_G_2`, `cobbDouglas_eq_les`).

E12. **Exercise 3.G.18 (p. 102).** Proved for every negative semidefinite matrix `S` with
     `S p = 0`, `p ≫ 0` (`closer_substitute_chain`), and then for Hicksian derivative matrices
     under the hypotheses of Proposition 3.G.2 (`exercise_3_G_18`).

E13. **Exercise 3.AA.2 (p. 95).** Upper hemicontinuity of `h` is proved in the sequential form of
     Definition 3.AA.1 at `p̄ ≫ 0` (`exercise_3_AA_2_uhc`), with local boundedness
     (`exercise_3_AA_2_bounded`). With the infimum, `e(·, ū)` is continuous on all of `ℝ^L_+`
     for every `u` and attainable `ū` (`exercise_3_AA_2_inf_continuous`); joint continuity in
     `(p, ū)` at boundary prices is not proved (OPEN). "Conditions for differentiability" is
     answered by: `h(·, ū)` is differentiable at `p̄` iff `∇_p e(·, ū)` is
     (`exercise_3_AA_2_differentiable`).

E14. **Exercise 3.G.5(a) (p. 100).** `ũ(x, z)` is defined as a supremum, so no continuity of `u`
     is needed; the optimum `(x*, y*)` of the original UMP yields the optimum `(x*, q₀·y*)` of the
     composite problem with the same value (`exercise_3_G_5a`).

E15. **Theorem M.G.1 (p. 947).** No departure: proved as printed (`theorem_M_G_1`), via Minkowski's
     theorem `B = Co(ext B)` in any finite-dimensional inner product space
     (`closerMG_minkowski`) and Carathéodory's bound.
