# Corrections and departures

MWG, Chapter 2 and Mathematical Appendix M.A, M.B, M.D. Each item gives what the book says,
what is proved, and the Lean names.

1. **Own-price compensated law (p. 32).** The book: for a compensated change in `p_ℓ` alone,
   `Δp_ℓ > 0` implies `Δx_ℓ < 0`. This fails when demand does not move. Proved:
   `Δp_ℓ Δx_ℓ ≤ 0`, strictly if `x(p', w') ≠ x(p, w)` (`own_price_compensated_law`).
   Counterexample: Leontief demand `x = (w/(p₁+p₂))(1, 1)` satisfies the weak axiom, Walras'
   law and homogeneity, and a compensated rise of `p₁` from 1 to 2 at `p = (1, 1)`, `w = 2`
   leaves `x₁ = 1` unchanged (`own_price_strict_counterexample`, `leontiefDemand_weakAxiom`).

2. **Exercise 2.E.5 (p. 37).** The book asks to show `x_ℓ(p, w) = α_ℓ w/p_ℓ` with `α_ℓ > 0`.
   Proved: there are `α_ℓ ≥ 0` with `∑ α_ℓ = 1` (`exercise_2_E_5`). Strict positivity does not
   follow: `x(p, w) = (w/p₁, 0)` satisfies every hypothesis
   (`exercise_2_E_5_alpha_pos_counterexample`). The proof uses differentiability of demand on
   the domain (implicit in "cross-price effects") and values in `ℝ^L_+` (for `α_ℓ ≥ 0`).

3. **Theorem M.D.3 (p. 938).** (a) The subspace is printed `{z : Bz = 0}` for an `N × S`
   matrix `B`; it must be `{z : Bᵀz = 0}` (as Example M.D.2 shows with `B = ∇f`).
   (b) Part (i) is false under the printed hypothesis `rank B = S`: for `N = 3`, `S = 1`,
   `M = -I`, `B = (0, 0, 1)ᵀ`, `M` is negative definite on `{z₃ = 0}` but the bordered
   determinant of order 2 is `0` (`theorem_M_D_3_i_counterexample`). Corrected (i), proved:
   if the top `S × S` block of `B` is nonsingular, `M` is negative definite on `{z : Bᵀz = 0}`
   iff `(-1)^r |bordered_r| > 0` for `r = S+1, …, N` (`theorem_M_D_3_i`). (c) Part (ii) as
   printed quantifies over all permutations, hence over every set of `r` rows, so the
   degeneracy in (b) does not refute it, and (ii) is true as printed (`theorem_M_D_3_ii`).
   Necessity holds without any rank hypothesis (`theorem_M_D_3_ii_forward`). Sufficiency
   uses rank `S` in the form "some `S` rows of `B` are linearly independent". Its proof expands
   `(-1)^r |bordered_r(M - εI)|` in powers of `ε`, with bordered principal minors as
   coefficients (`bordered_perturbation_expansion`), and applies corrected (i) to `M - εI`.

4. **Hypotheses not needed (stronger statements).** Proposition 2.F.1 and Proposition 2.F.2
   are stated in the book with homogeneity of degree zero; it is not used
   (`proposition_2_F_1`, `proposition_2_F_2`). Direction (i) of Proposition 2.F.1 uses only
   Walras' law; direction (ii) also uses that demand lies in `ℝ^L_+`, the book's consumption
   set (`ValuesInOrthant`), to keep the interpolated wealth positive. Exercise 2.E.4 does not
   need Walras' law (`exercise_2_E_4`); Exercise 2.E.3 needs only Walras' law
   (`exercise_2_E_3`; the hint's route is `exercise_2_E_3_via_homogeneity`). Exercise 2.F.5
   uses homogeneity of degree one in wealth, the weak axiom, Walras' law and values in
   `ℝ^L_+`, but not homogeneity of degree zero (`exercise_2_F_5`).

5. **Implicit hypotheses made explicit.** Walrasian demand takes values in `B_{p,w}`
   (Section 2.E, p. 24, "choice structure"). This is assumed where used: Exercise 2.F.1 (with
   homogeneity, so that `(𝓑^W, x(·))` is a choice structure; `exercise_2_F_1`), Exercise 2.F.14
   (`exercise_2_F_14`), and Exercise 2.F.13, where in addition values are nonempty for (d)
   (`exercise_2_F_13a`-`exercise_2_F_13d`). Elasticities are meaningful only where
   `x_ℓ(p, w) ≠ 0`; the elasticity form of Proposition 2.E.1 needs no hypothesis in Lean (both
   sides are `0` when `x_ℓ = 0`), while Exercise 2.E.2 assumes every `x_ℓ ≠ 0`.

6. **Differential arguments made rigorous.** The book's "differentiate with respect to `α`",
   `dp`, `dw` arguments (pp. 27-28, 33-34) are replaced by derivatives along lines
   `t ↦ (p + tv, w + tc)` of a Fréchet-differentiable demand, using that identities on the open
   domain hold near `t = 0` (`DemandCalculus`). Proposition 2.F.2 is proved from the finite
   compensated law of demand by one-sided difference quotients along the compensated path.

7. **Exercise 2.F.3(e)-(f) (p. 37).** "Inferior at some price" is formalised both discretely
   (demand for the good falls as wealth rises at prices `p²`) and, under differentiability, as
   a wealth level with `∂x_ℓ/∂w < 0` (mean value theorem). Proved: `y < 75` forces good 1 to be
   inferior and `75 < y < 100` forces good 2 to be inferior (`exercise_2_F_3e`,
   `exercise_2_F_3f`). That no other `y` forces it would require constructing WA demand
   functions for the remaining data and is not formalised.

8. **Exercise 2.F.10(b) (p. 38).** "For `ε > 0` small" is made explicit: `0 < ε < 1/22`, with
   `v = (1, 0, 3ε/2)` giving `v·Sv = (1 - 22ε)/(4(2+ε)²)` (`exercise_2_F_10b_quadratic`); the
   violation of the weak axiom follows from Proposition 2.F.2 at `ε = 1/44`
   (`exercise_2_F_10b`).

9. **Exercise 2.F.15 (p. 39).** The hint points to Samuelson's sufficiency result, which is now
   proved (`samuelson_sufficiency`, item 13). It does not apply directly here: the consumption
   set is `ℝ³`, not `ℝ³_+`. The weak axiom is therefore proved directly
   (`exercise_2_F_15_weakAxiom`), and `v·Sv < 0` off the ray of `p` is proved separately
   (`exercise_2_F_15_negDef_off_p`).

10. **Theorem M.D.1(iv) and Theorem M.D.5(v).** The book proves (iv) through a cited Lyapunov
    criterion and refers (v) to the Appendix of Chapter 5. Both are proved directly here
    (`theorem_M_D_1_iv`, `theorem_M_D_5_v`). Theorem M.D.2 (i), (ii) sufficiency and (iii)
    necessity, which the book leaves unproved or only sketches, are proved
    (`theorem_M_D_2_i`, `theorem_M_D_2_ii`, `theorem_M_D_2_iii`).

11. **Encodings of figures and verbal set-ups.** The budget set of Figure 2.D.4 (Exercise
    2.D.4) is modelled with wages `0 < s < s'` for the first 8 and further hours, a tax rate
    `t ≥ 0` on labour income above `M > 8s`, and price 1 for consumption
    (`figure_2_D_4_set`). The lifetime budget of Exercise 2.D.1 is modelled with saving or
    borrowing at an interest rate `r > -1` (`exercise_2_D_1`). Figure 2.F.5 is witnessed by two
    explicit observations (`figure_2_F_5`). These are constructed formalisations, not printed
    formulas.

12. **Domains in M.B.** Functions in Section M.B are defined on `ℝ^N_+`; here they are
    functions on `ℝ^N` whose homogeneity is required only on `ℝ^N_+`, and Theorem M.B.1 is
    proved at every point of `ℝ^N_+`, including boundary points (`theorem_M_B_1`).

13. **Samuelson's sufficiency result (p. 35, small type).** The book states it informally. Here
    it is proved in this precise form: `x` is homogeneous of degree zero, satisfies Walras' law,
    takes values in `ℝ^L_+` and is differentiable at every `p ≫ 0`, `w > 0`, and
    `v·S(p, w)v < 0` holds for every `(p, w)` and every `v` not proportional to `p`. Then `x`
    satisfies the weak axiom (`samuelson_sufficiency`). The proof follows
    `φ(t) = (p'-p)·[x(p + t(p'-p), w + t(p'-p)·x̄) - x̄]` along a compensated path and shows that
    `φ' < 0` at every zero of `φ` (`neg_at_one_of_deriv_neg_at_zeros`). No continuity of the
    derivative is needed.

14. **Exercise 2.F.3(e)-(f) (p. 37).** Under the exercise's assumption that the weak axiom
    holds, the data with `75 ≤ y ≤ 80` are impossible (`exercise_2_F_3_inconsistent`). For
    those `y` every conclusion, including inferiority, holds vacuously. The book's answers
    (`y < 75` for good 1, and the range for good 2) are therefore the ranges in which the data
    are consistent and force inferiority; the forcing is proved. The remaining direction (that
    no other consistent `y` forces it) is OPEN; see the source map. A homothetic witness exists
    only for `y ≥ 120` (`exercise_2_F_3_homothetic_bound`).

15. **MWG Chapter 1 dependency.** Exercises 2.F.1 and 2.F.13(a) use MWG Chapter 1's
    `ChoiceStructure` and `WeakAxiom`. The Walrasian budget family with the demand's choice rule
    is shown to be a choice structure (`walrasianChoiceStructure`, `walrasianCorrStructure`).
    For correspondences this requires nonempty values in the budget sets, which Chapter 1 builds
    into the definition of a choice structure.
