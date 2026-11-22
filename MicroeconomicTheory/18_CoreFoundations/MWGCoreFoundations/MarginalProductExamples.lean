/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGCoreFoundations.MarginalProduct
import MWGWelfareBargaining.Shapley

/-!
# Marginal productivity: examples and Exercise 18.E.3 (MWG Section 18.E, pp. 670-673, 685)

Concrete instances for the hypotheses of `MWGCoreFoundations.MarginalProduct`.

* The square-root economy `sqrtQLEconomy`: two types, one non-numeraire good,
  `ψ_h(y) = 2√y`, type 0 endowed with one unit of the good, type 1 with nothing. Here
  `v(μ) = 2√((μ₀ + μ₁) μ₀)` on `ℝ²₊` (`sqrtQL_v`), `v` is differentiable at `μ = (1, 1)`, the
  Walrasian equilibrium has price `√2` and utilities `3√2/2`, `√2/2`, which are the partial
  derivatives of `v` (a marginal product allocation, Proposition 18.E.1). As a finite economy
  with one consumer of each type: `Δ₀v = 2√2 > 3√2/2`, `Δ₁v = 2√2 - 2 > √2/2`, and
  `∑ Δ_h v > v(1, 1)`, so no feasible allocation gives everyone her marginal contribution and the
  Walrasian allocation is not a marginal product allocation in the finite sense (p. 672).
* **Exercise 18.E.3**: the Leontief economy `leontiefQLEconomy` (`ψ_h(y) = min(y₁, y₂)`, type 0
  owns one unit of good 1, type 1 one unit of good 2, `μ = (1, 1)`). `v(μ) = min(μ₀, μ₁)`, which
  is not differentiable at `(1, 1)`. The marginal contribution of a trader is taken as the loss
  from removing a marginal trader, the left partial derivative of `v`, equal to `1` (and equal to
  the finite `Δ_h v(1, 1)`); the right partial derivative is `0`. At every Walrasian equilibrium
  with both prices positive each type's utility is strictly below `1` (`exercise_18_E_3`); an
  equilibrium with prices `(1/2, 1/2)` exists. With prices `(1, 0)` (also an equilibrium)
  type 0 gets exactly `1`, so positivity of both prices is needed for "every trader".
* p. 673: the efficiency identity of the Shapley value of the TU game of a finite economy,
  `∑ᵢ Shᵢ = v(I)` (`claim_18_E_shapley_sum`), from Chapter 22's `shapley_pareto`.
-/

namespace MWG.CoreFoundations

open Filter Topology

variable {K : ℕ}

/-! ### The square-root economy -/

/-- **Section 18.E** example (MWG, pp. 670-672). Two types, one non-numeraire good,
`ψ_h(y) = 2√y`; type 0 owns one unit of the good, type 1 owns nothing (both own no money). -/
noncomputable def sqrtQLEconomy : QLEconomy (Fin 2) 1 where
  ψ := fun _ y => 2 * Real.sqrt (y 0)
  ω := ![((fun _ => 1 : Fin 1 → ℝ), (0 : ℝ)), (0, 0)]

/-- The square-root economy satisfies the concavity hypothesis. -/
theorem sqrtQL_concave : ∀ h, ConcaveOn ℝ (Set.Ici 0) (sqrtQLEconomy.ψ h) := by
  intro h
  refine ⟨convex_Ici 0, fun y hy y' hy' a b ha hb hab => ?_⟩
  have := Real.strictConcaveOn_sqrt.concaveOn.2 (Set.mem_Ici.2 ((Set.mem_Ici.1 hy) 0))
    (Set.mem_Ici.2 ((Set.mem_Ici.1 hy') 0)) ha hb hab
  simp only [sqrtQLEconomy, smul_eq_mul, Pi.add_apply, Pi.smul_apply] at this ⊢
  linarith

/-- The square-root economy satisfies the monotonicity hypothesis. -/
theorem sqrtQL_mono : ∀ h, MonotoneOn (sqrtQLEconomy.ψ h) (Set.Ici 0) := by
  intro h y _ y' _ hle
  simp only [sqrtQLEconomy]
  gcongr
  exact hle 0

/-- `ψ_h` is differentiable at every `y` with `y > 0`. -/
theorem sqrtQL_differentiableAt (h : Fin 2) {y : Fin 1 → ℝ} (hy : 0 < y 0) :
    DifferentiableAt ℝ (sqrtQLEconomy.ψ h) y :=
  ((differentiableAt_apply 0 y).sqrt hy.ne').const_mul 2

/-- Endowments of non-numeraire goods are nonnegative. -/
theorem sqrtQL_omega_nonneg : ∀ h, 0 ≤ (sqrtQLEconomy.ω h).1 := by
  intro h l
  fin_cases h <;> simp [sqrtQLEconomy]

/-- Every feasible allocation gives at most `2√((μ₀ + μ₁) μ₀)` (Cauchy-Schwarz). -/
theorem sqrtQL_welfare_le {μ : Fin 2 → ℝ} (hμ : 0 ≤ μ) {x : Fin 2 → (Fin 1 → ℝ) × ℝ}
    (hx : sqrtQLEconomy.IsFeasible μ x) :
    sqrtQLEconomy.welfare μ x ≤ 2 * √((μ 0 + μ 1) * μ 0) := by
  have hy : μ 0 * (x 0).1 0 + μ 1 * (x 1).1 0 ≤ μ 0 := by
    simpa [Fin.sum_univ_two, sqrtQLEconomy] using hx.2.1 0
  have hm : μ 0 * (x 0).2 + μ 1 * (x 1).2 ≤ 0 := by
    simpa [Fin.sum_univ_two, sqrtQLEconomy] using hx.2.2
  have ha : 0 ≤ (x 0).1 0 := hx.1 0 0
  have hb : 0 ≤ (x 1).1 0 := hx.1 1 0
  have h0 : 0 ≤ μ 0 := hμ 0
  have h1 : 0 ≤ μ 1 := hμ 1
  set s := √((x 0).1 0)
  set t := √((x 1).1 0)
  have hs : s ^ 2 = (x 0).1 0 := Real.sq_sqrt ha
  have ht : t ^ 2 = (x 1).1 0 := Real.sq_sqrt hb
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have key : μ 0 * s + μ 1 * t ≤ √((μ 0 + μ 1) * μ 0) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    rw [← hs, ← ht] at hy
    have e : (μ 0 + μ 1) * (μ 0 * s ^ 2 + μ 1 * t ^ 2) - (μ 0 * s + μ 1 * t) ^ 2 =
        μ 0 * μ 1 * (s - t) ^ 2 := by ring
    linarith [mul_nonneg (mul_nonneg h0 h1) (sq_nonneg (s - t)),
      mul_le_mul_of_nonneg_left hy (add_nonneg h0 h1)]
  simp only [QLEconomy.welfare, QLEconomy.u, Fin.sum_univ_two, sqrtQLEconomy]
  nlinarith

/-- **Section 18.E** example (MWG, p. 671). `v(μ) = 2√((μ₀ + μ₁) μ₀)` on `ℝ²₊`, attained by
giving each type `μ₀/(μ₀ + μ₁)` units of the good. -/
theorem sqrtQL_v {μ : Fin 2 → ℝ} (hμ : 0 ≤ μ) :
    sqrtQLEconomy.v μ = 2 * √((μ 0 + μ 1) * μ 0) := by
  have h0 : 0 ≤ μ 0 := hμ 0
  have h1 : 0 ≤ μ 1 := hμ 1
  set c := μ 0 / (μ 0 + μ 1)
  have hc : 0 ≤ c := div_nonneg h0 (add_nonneg h0 h1)
  have hSc : (μ 0 + μ 1) * c ≤ μ 0 := by
    rcases (add_nonneg h0 h1).eq_or_lt with hS | hS
    · rw [← hS, zero_mul]; exact h0
    · rw [mul_div_cancel₀ _ hS.ne']
  let x : Fin 2 → (Fin 1 → ℝ) × ℝ := fun _ => (fun _ => c, 0)
  have hfeas : sqrtQLEconomy.IsFeasible μ x := by
    refine ⟨fun _ _ => hc, fun l => ?_, ?_⟩
    · simp [x, Fin.sum_univ_two, sqrtQLEconomy]
      linarith
    · simp [x, Fin.sum_univ_two, sqrtQLEconomy]
  have hval : sqrtQLEconomy.welfare μ x = 2 * √((μ 0 + μ 1) * μ 0) := by
    simp only [QLEconomy.welfare, QLEconomy.u, Fin.sum_univ_two, sqrtQLEconomy, x, add_zero]
    rcases (add_nonneg h0 h1).eq_or_lt with hS | hS
    · have e0 : μ 0 = 0 := by linarith
      have e1 : μ 1 = 0 := by linarith
      simp [e0, e1]
    · have : (μ 0 + μ 1) * √c = √((μ 0 + μ 1) * μ 0) := by
        have e1 : (μ 0 + μ 1) * μ 0 = (μ 0 + μ 1) ^ 2 * c := by
          simp only [c]
          field_simp
        rw [e1, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hS.le]
      linear_combination 2 * this
  refine IsGreatest.csSup_eq ⟨⟨x, hfeas, hval⟩, ?_⟩
  rintro s ⟨x', hx', rfl⟩
  exact sqrtQL_welfare_le hμ hx'

/-- The population `μ = (1, 1)`, i.e. the finite economy with one consumer of each type. -/
def qlOnes : Fin 2 → ℝ := fun _ => 1

/-- **Footnote 21** instance (MWG, p. 671). In the square-root economy `v` is differentiable at
`μ = (1, 1)`. -/
theorem sqrtQL_v_differentiableAt : DifferentiableAt ℝ sqrtQLEconomy.v qlOnes := by
  have hF : DifferentiableAt ℝ (fun μ : Fin 2 → ℝ => 2 * √((μ 0 + μ 1) * μ 0)) qlOnes :=
    ((((differentiableAt_apply 0 qlOnes).add (differentiableAt_apply 1 qlOnes)).mul
      (differentiableAt_apply 0 qlOnes)).sqrt (by norm_num [qlOnes])).const_mul 2
  refine hF.congr_of_eventuallyEq ?_
  filter_upwards [ql_eventually_nonneg_of_pos (μ := qlOnes) (fun _ => one_pos)] with ν hν
  exact sqrtQL_v hν

/-- The Walrasian allocation of the square-root economy at `μ = (1, 1)`: each type consumes `1/2`
of the good; type 0 receives `√2/2` units of money, type 1 pays `√2/2`. -/
noncomputable def sqrtQLStar : Fin 2 → (Fin 1 → ℝ) × ℝ :=
  ![((fun _ => 1 / 2 : Fin 1 → ℝ), √2 / 2), (fun _ => 1 / 2, -(√2 / 2))]

/-- `√(1/2) = √2/2`. -/
theorem ql_sqrt_half : √(1 / 2 : ℝ) = √2 / 2 := by
  rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by positivity)]
  nlinarith [Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

/-- The tangent line of `2√y` at `y = 1/2`: `2√y ≤ √2 y + √2/2`. -/
theorem ql_sqrt_tangent {y : ℝ} (hy : 0 ≤ y) : 2 * √y ≤ √2 * y + √2 / 2 := by
  have hs := Real.sq_sqrt hy
  have h2 := Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have e : √2 * (√y - √2 / 2) ^ 2 = √2 * √y ^ 2 - (√2 * √2) * √y + (√2 * √2) * √2 / 4 := by
    ring
  rw [h2, hs] at e
  linarith [mul_nonneg (Real.sqrt_nonneg 2) (sq_nonneg (√y - √2 / 2))]

/-- **Section 18.E** example (MWG, pp. 671-672). `(√2, x*)` is a Walrasian equilibrium of the
square-root economy with `μ = (1, 1)`. -/
theorem sqrtQL_walras : sqrtQLEconomy.IsWalrasEqm qlOnes (fun _ => √2) sqrtQLStar := by
  have hu : ∀ h, sqrtQLEconomy.u h (sqrtQLStar h) =
      qlPrice (fun _ => √2) (sqrtQLEconomy.ω h) + √2 / 2 := by
    intro h
    have h2 := Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have h2' : (0 : ℝ) < √2 := by positivity
    fin_cases h <;>
      simp [QLEconomy.u, qlPrice, sqrtQLEconomy, sqrtQLStar, dotProduct] <;> field_simp <;>
      nlinarith
  refine ⟨⟨fun h l => ?_, fun l => ?_, ?_⟩, fun h => ⟨?_, fun x' hx' hb => ?_⟩⟩
  · fin_cases h <;> simp [sqrtQLStar]
  · simp [Fin.sum_univ_two, sqrtQLStar, sqrtQLEconomy, qlOnes]
    norm_num
  · simp [Fin.sum_univ_two, sqrtQLStar, sqrtQLEconomy, qlOnes]
  · fin_cases h <;> simp [qlPrice, sqrtQLStar, sqrtQLEconomy, dotProduct] <;> ring_nf <;> simp
  · rw [hu]
    have ht := ql_sqrt_tangent (hx' 0)
    simp only [qlPrice, dotProduct, Finset.univ_unique, Fin.default_eq_zero,
      Finset.sum_singleton] at hb
    simp only [QLEconomy.u, sqrtQLEconomy, qlPrice, dotProduct, Finset.univ_unique,
      Fin.default_eq_zero, Finset.sum_singleton] at hb ⊢
    linarith

/-- **(18.E.5)** instance (MWG, p. 672). The partial derivatives of `v` at `(1, 1)` are the
Walrasian utilities: `∂v/∂μ₀ = 3√2/2` and `∂v/∂μ₁ = √2/2`. -/
theorem sqrtQL_partial :
    fderiv ℝ sqrtQLEconomy.v qlOnes (Pi.single 0 1) = 3 * √2 / 2 ∧
      fderiv ℝ sqrtQLEconomy.v qlOnes (Pi.single 1 1) = √2 / 2 := by
  have hD := sqrtQL_v_differentiableAt.hasFDerivAt
  have e := fun h => sqrtQLEconomy.partial_v_of_walras sqrtQL_mono sqrtQL_omega_nonneg
    (fun _ => one_pos) sqrtQL_walras hD h
  rw [e 0, e 1]
  have h2 := Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have h2' : (0 : ℝ) < √2 := by positivity
  constructor <;>
    simp [QLEconomy.u, sqrtQLEconomy, sqrtQLStar] <;> field_simp <;> nlinarith

/-- **Definition 18.E.1** instance (MWG, p. 671). The Walrasian allocation of the square-root
economy is a marginal product allocation. -/
theorem definition_18_E_1_instance : sqrtQLEconomy.IsMarginalProduct qlOnes sqrtQLStar :=
  proposition_18_E_1_of_walras sqrtQLEconomy sqrtQL_mono sqrtQL_omega_nonneg
    (fun _ => one_pos) sqrtQL_walras sqrtQL_v_differentiableAt

/-- **Proposition 18.E.1** instance (MWG, p. 671). All hypotheses of `proposition_18_E_1` hold
for the square-root economy at `μ = (1, 1)` and `x* = sqrtQLStar` (with `y* = 1/2 > 0`), and
both sides of the equivalence are true. -/
theorem proposition_18_E_1_instance :
    (sqrtQLEconomy.IsMarginalProduct qlOnes sqrtQLStar ↔
      ∃ q, sqrtQLEconomy.IsWalrasEqm qlOnes q sqrtQLStar) ∧
      sqrtQLEconomy.IsMarginalProduct qlOnes sqrtQLStar := by
  have hint : ∀ h l, 0 < (sqrtQLStar h).1 l := by
    intro h l; fin_cases h <;> simp [sqrtQLStar]
  refine ⟨proposition_18_E_1 sqrtQLEconomy sqrtQL_concave sqrtQL_mono sqrtQL_omega_nonneg
    (fun _ => one_pos) sqrtQL_walras.1 hint (fun h => sqrtQL_differentiableAt h (hint h 0))
    sqrtQL_v_differentiableAt, definition_18_E_1_instance⟩

/-- **(18.E.2)** instance (MWG, p. 671). The Walrasian allocation of the square-root economy
solves (18.E.2) for `μ = (1, 1)` (its welfare `2√2` equals the bound of `sqrtQL_welfare_le`); so
the hypotheses of `exercise_18_E_2` and `claim_18_E_finite_walras_iff` are satisfiable. -/
theorem sqrtQL_optimal : sqrtQLEconomy.IsOptimal qlOnes sqrtQLStar := by
  have hw : sqrtQLEconomy.welfare qlOnes sqrtQLStar = 2 * √2 := by
    have h2 := Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have h2' : (0 : ℝ) < √2 := by positivity
    simp [QLEconomy.welfare, QLEconomy.u, Fin.sum_univ_two, sqrtQLEconomy, sqrtQLStar, qlOnes]
    field_simp
    nlinarith
  refine ⟨sqrtQL_walras.1, fun x' hx' => ?_⟩
  have hb := sqrtQL_welfare_le (μ := qlOnes) (fun _ => zero_le_one) hx'
  rw [show (qlOnes 0 + qlOnes 1) * qlOnes 0 = (2 : ℝ) by norm_num [qlOnes]] at hb
  rw [hw]
  exact hb

/-- **Exercise 18.E.1** instance (MWG, p. 671). In the square-root economy `v` is concave on
`ℝ²₊`. -/
theorem sqrtQL_v_concave : ConcaveOn ℝ (Set.Ici 0) sqrtQLEconomy.v :=
  (exercise_18_E_1 sqrtQLEconomy sqrtQL_concave sqrtQL_mono
    (fun h => ⟨fun _ => 1, fun _ => zero_le_one,
      sqrtQL_differentiableAt h (by norm_num)⟩) sqrtQL_omega_nonneg).1

/-- **Section 18.E** example (MWG, p. 672). The finite marginal contributions with one consumer
of each type: `Δ₀v(1, 1) = 2√2` and `Δ₁v(1, 1) = 2√2 - 2`. -/
theorem sqrtQL_deltaV :
    sqrtQLEconomy.deltaV qlOnes 0 = 2 * √2 ∧ sqrtQLEconomy.deltaV qlOnes 1 = 2 * √2 - 2 := by
  have hv11 : sqrtQLEconomy.v qlOnes = 2 * √2 := by
    rw [sqrtQL_v (μ := qlOnes) (fun _ => zero_le_one)]
    norm_num [qlOnes]
  have hnn : ∀ h, 0 ≤ qlOnes - Pi.single h 1 := by
    intro h k
    fin_cases h <;> fin_cases k <;> simp [qlOnes]
  unfold QLEconomy.deltaV
  rw [hv11, sqrtQL_v (hnn 0), sqrtQL_v (hnn 1)]
  constructor <;> norm_num [qlOnes]

/-- **Section 18.E** (MWG, p. 672), "typically `Δ_h v > ∂v/∂μ_h`" and
"`∑_h I_h Δ_h v > v(I)`", strictly, in the square-root economy with `I = (1, 1)`. -/
theorem example_18_E_finite_strict :
    (∀ h, fderiv ℝ sqrtQLEconomy.v qlOnes (Pi.single h 1) < sqrtQLEconomy.deltaV qlOnes h) ∧
      sqrtQLEconomy.v qlOnes < ∑ h, qlOnes h * sqrtQLEconomy.deltaV qlOnes h := by
  obtain ⟨p0, p1⟩ := sqrtQL_partial
  obtain ⟨d0, d1⟩ := sqrtQL_deltaV
  have hs : (4 / 3 : ℝ) < √2 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hs0 : 0 < √2 := by positivity
  have hv11 : sqrtQLEconomy.v qlOnes = 2 * √2 := by
    rw [sqrtQL_v (μ := qlOnes) (fun _ => zero_le_one)]
    norm_num [qlOnes]
  refine ⟨fun h => ?_, ?_⟩
  · fin_cases h
    · simp only [Fin.zero_eta, Fin.isValue]
      rw [p0, d0]; linarith
    · simp only [Fin.mk_one, Fin.isValue]
      rw [p1, d1]; linarith
  · rw [hv11, Fin.sum_univ_two, d0, d1]
    simp only [qlOnes]
    linarith

/-- **Section 18.E** (MWG, p. 672) instance: with one consumer of each type in the square-root
economy, no feasible allocation gives every consumer her full marginal contribution
`Δ_h v(1, 1)`. -/
theorem example_18_E_no_full_marginal :
    ¬ ∃ x, sqrtQLEconomy.IsFeasible qlOnes x ∧
      ∀ h, sqrtQLEconomy.deltaV qlOnes h ≤ sqrtQLEconomy.u h (x h) := by
  refine claim_18_E_no_full_marginal sqrtQLEconomy (fun _ => zero_le_one) ?_
    example_18_E_finite_strict.2
  refine ⟨2 * √((qlOnes 0 + qlOnes 1) * qlOnes 0), ?_⟩
  rintro s ⟨x, hx, rfl⟩
  exact sqrtQL_welfare_le (fun _ => zero_le_one) hx

/-- **Section 18.E** (MWG, p. 672) instance: "in a finite economy the Walrasian allocation is
typically not a marginal product allocation": in the square-root economy with `I = (1, 1)` each
consumer's Walrasian utility is strictly below her marginal contribution `Δ_h v(1, 1)`. -/
theorem example_18_E_walras_below_delta (h : Fin 2) :
    sqrtQLEconomy.u h (sqrtQLStar h) < sqrtQLEconomy.deltaV qlOnes h := by
  have hmp := definition_18_E_1_instance.2 h
  rw [hmp]
  exact example_18_E_finite_strict.1 h

/-- **Section 18.E** (MWG, p. 672) instance of `claim_18_E_deltaV_ge_partial` and
`claim_18_E_sum_deltaV_ge`: their hypotheses hold in the square-root economy at `I = (1, 1)`. -/
theorem example_18_E_finite_claims :
    (∀ h, fderiv ℝ sqrtQLEconomy.v qlOnes (Pi.single h 1) ≤ sqrtQLEconomy.deltaV qlOnes h) ∧
      sqrtQLEconomy.v qlOnes ≤ ∑ h, qlOnes h * sqrtQLEconomy.deltaV qlOnes h := by
  have hnn : ∀ h, 0 ≤ qlOnes - Pi.single h 1 := by
    intro h k
    fin_cases h <;> fin_cases k <;> simp [qlOnes]
  have hD := sqrtQL_v_differentiableAt.hasFDerivAt
  exact ⟨fun h => claim_18_E_deltaV_ge_partial sqrtQLEconomy sqrtQL_v_concave (hnn h) hD,
    claim_18_E_sum_deltaV_ge sqrtQLEconomy sqrtQL_v_concave hnn hD⟩

/-! ### Exercise 18.E.3: Leontief preferences -/

/-- **Exercise 18.E.3** (MWG, p. 685). Two types, two non-numeraire goods, L-shaped preferences
`ψ_h(y) = min(y₁, y₂)`; type 0 owns one unit of good 1, type 1 one unit of good 2 (no money). -/
noncomputable def leontiefQLEconomy : QLEconomy (Fin 2) 2 where
  ψ := fun _ y => min (y 0) (y 1)
  ω := ![((![1, 0] : Fin 2 → ℝ), (0 : ℝ)), (![0, 1], 0)]

/-- The Leontief `ψ_h` is concave on `ℝ²₊`. -/
theorem leontief_concave : ∀ h, ConcaveOn ℝ (Set.Ici 0) (leontiefQLEconomy.ψ h) := by
  intro h
  refine ⟨convex_Ici 0, fun y _ y' _ a b ha hb _ => ?_⟩
  simp only [leontiefQLEconomy, smul_eq_mul, Pi.add_apply, Pi.smul_apply]
  refine le_min ?_ ?_
  · nlinarith [mul_le_mul_of_nonneg_left (min_le_left (y 0) (y 1)) ha,
      mul_le_mul_of_nonneg_left (min_le_left (y' 0) (y' 1)) hb]
  · nlinarith [mul_le_mul_of_nonneg_left (min_le_right (y 0) (y 1)) ha,
      mul_le_mul_of_nonneg_left (min_le_right (y' 0) (y' 1)) hb]

/-- The Leontief `ψ_h` is nondecreasing. -/
theorem leontief_mono : ∀ h, MonotoneOn (leontiefQLEconomy.ψ h) (Set.Ici 0) := by
  intro h y _ y' _ hle
  exact min_le_min (hle 0) (hle 1)

/-- Every feasible allocation of the Leontief economy gives at most `min(μ₀, μ₁)`. -/
theorem leontief_welfare_le {μ : Fin 2 → ℝ} (hμ : 0 ≤ μ) {x : Fin 2 → (Fin 2 → ℝ) × ℝ}
    (hx : leontiefQLEconomy.IsFeasible μ x) :
    leontiefQLEconomy.welfare μ x ≤ min (μ 0) (μ 1) := by
  have hy0 := hx.2.1 0
  have hy1 := hx.2.1 1
  have hm := hx.2.2
  simp [Fin.sum_univ_two, leontiefQLEconomy] at hy0 hy1 hm
  have h0 : 0 ≤ μ 0 := hμ 0
  have h1 : 0 ≤ μ 1 := hμ 1
  simp only [QLEconomy.welfare, QLEconomy.u, Fin.sum_univ_two, leontiefQLEconomy]
  refine le_min ?_ ?_
  · nlinarith [mul_le_mul_of_nonneg_left (min_le_left ((x 0).1 0) ((x 0).1 1)) h0,
      mul_le_mul_of_nonneg_left (min_le_left ((x 1).1 0) ((x 1).1 1)) h1]
  · nlinarith [mul_le_mul_of_nonneg_left (min_le_right ((x 0).1 0) ((x 0).1 1)) h0,
      mul_le_mul_of_nonneg_left (min_le_right ((x 1).1 0) ((x 1).1 1)) h1]

/-- **Exercise 18.E.3** (MWG, p. 685). In the Leontief economy `v(μ) = min(μ₀, μ₁)` on `ℝ²₊`. -/
theorem leontief_v {μ : Fin 2 → ℝ} (hμ : 0 ≤ μ) : leontiefQLEconomy.v μ = min (μ 0) (μ 1) := by
  have h0 : 0 ≤ μ 0 := hμ 0
  have h1 : 0 ≤ μ 1 := hμ 1
  set c := min (μ 0) (μ 1) / (μ 0 + μ 1)
  have hc : 0 ≤ c := div_nonneg (le_min h0 h1) (add_nonneg h0 h1)
  have hSc : (μ 0 + μ 1) * c = min (μ 0) (μ 1) := by
    rcases (add_nonneg h0 h1).eq_or_lt with hS | hS
    · have e0 : μ 0 = 0 := by linarith
      have e1 : μ 1 = 0 := by linarith
      simp [e0, e1]
    · exact mul_div_cancel₀ _ hS.ne'
  let x : Fin 2 → (Fin 2 → ℝ) × ℝ := fun _ => (fun _ => c, 0)
  have hfeas : leontiefQLEconomy.IsFeasible μ x := by
    refine ⟨fun _ _ => hc, fun l => ?_, ?_⟩
    · fin_cases l <;> simp [x, Fin.sum_univ_two, leontiefQLEconomy] <;>
        nlinarith [min_le_left (μ 0) (μ 1), min_le_right (μ 0) (μ 1)]
    · simp [x, Fin.sum_univ_two, leontiefQLEconomy]
  have hval : leontiefQLEconomy.welfare μ x = min (μ 0) (μ 1) := by
    simp only [QLEconomy.welfare, QLEconomy.u, Fin.sum_univ_two, leontiefQLEconomy, x,
      min_self, add_zero]
    linarith
  refine IsGreatest.csSup_eq ⟨⟨x, hfeas, hval⟩, ?_⟩
  rintro s ⟨x', hx', rfl⟩
  exact leontief_welfare_le hμ hx'

/-- Along the `h`-th coordinate line through `(1, 1)`, `v = min(1 + t, 1)` (for `t ≥ -1`). -/
theorem leontief_line (h : Fin 2) {t : ℝ} (ht : -1 ≤ t) :
    leontiefQLEconomy.v (qlOnes + t • Pi.single h 1) = min (1 + t) 1 := by
  have hnn : 0 ≤ qlOnes + t • Pi.single h 1 := by
    intro k
    fin_cases h <;> fin_cases k <;> simp [qlOnes] <;> linarith
  rw [leontief_v hnn]
  fin_cases h <;> simp [qlOnes, min_comm]

/-- **Exercise 18.E.3** (MWG, p. 685). The marginal contribution of a trader of either type at
`μ = (1, 1)`, read as the loss from removing a marginal trader (the left partial derivative of
`v`), is `1`. -/
theorem exercise_18_E_3_left_deriv (h : Fin 2) :
    HasDerivWithinAt (fun t : ℝ => leontiefQLEconomy.v (qlOnes + t • Pi.single h 1)) 1
      (Set.Iic 0) 0 := by
  have hlin : HasDerivWithinAt (fun t : ℝ => 1 + t) 1 (Set.Iic 0) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_add 1).hasDerivWithinAt (s := Set.Iic 0)
  refine hlin.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (lt_mem_nhds (show (-1 : ℝ) < 0 by norm_num))] with t ht ht'
    rw [leontief_line h ht'.le, min_eq_left (by linarith [Set.mem_Iic.1 ht])]
  · rw [leontief_line h (by norm_num)]
    norm_num

/-- **Exercise 18.E.3** (MWG, p. 685). The right partial derivative of `v` at `(1, 1)` (the gain
from adding a marginal trader) is `0`. -/
theorem exercise_18_E_3_right_deriv (h : Fin 2) :
    HasDerivWithinAt (fun t : ℝ => leontiefQLEconomy.v (qlOnes + t • Pi.single h 1)) 0
      (Set.Ici 0) 0 := by
  have hc : HasDerivWithinAt (fun _ : ℝ => (1 : ℝ)) 0 (Set.Ici 0) 0 :=
    (hasDerivAt_const (0 : ℝ) (1 : ℝ)).hasDerivWithinAt
  refine hc.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with t ht
    rw [leontief_line h (by linarith [Set.mem_Ici.1 ht]),
      min_eq_right (by linarith [Set.mem_Ici.1 ht])]
  · rw [leontief_line h (by norm_num)]
    norm_num

/-- **Exercise 18.E.3** (MWG, p. 685). With L-shaped preferences `v` is not differentiable at
`(1, 1)` (left and right partial derivatives `1 ≠ 0`). -/
theorem exercise_18_E_3_not_differentiable :
    ¬ DifferentiableAt ℝ leontiefQLEconomy.v qlOnes := by
  intro hd
  have hφ := ql_hasDerivAt_line hd.hasFDerivAt (Pi.single (0 : Fin 2) (1 : ℝ))
  have e1 := UniqueDiffWithinAt.eq_deriv _ (uniqueDiffOn_Iic 0 0 (Set.mem_Iic.2 le_rfl))
    hφ.hasDerivWithinAt (exercise_18_E_3_left_deriv 0)
  have e2 := UniqueDiffWithinAt.eq_deriv _ (uniqueDiffOn_Ici 0 0 (Set.mem_Ici.2 le_rfl))
    hφ.hasDerivWithinAt (exercise_18_E_3_right_deriv 0)
  rw [e1] at e2
  exact one_ne_zero e2

/-- **Exercise 18.E.3** (MWG, p. 685). The finite marginal contribution `Δ_h v(1, 1)` is also
`1`. -/
theorem exercise_18_E_3_delta (h : Fin 2) : leontiefQLEconomy.deltaV qlOnes h = 1 := by
  have h1 := leontief_line h (t := -1) le_rfl
  rw [neg_one_smul, ← sub_eq_add_neg] at h1
  unfold QLEconomy.deltaV
  rw [h1, leontief_v (μ := qlOnes) (fun _ => zero_le_one)]
  norm_num [qlOnes]

/-- **Exercise 18.E.3** (MWG, p. 685). At every Walrasian equilibrium of the Leontief economy
with `μ = (1, 1)` and both prices positive, every trader gets strictly less than her marginal
contribution `1` (`exercise_18_E_3_left_deriv`, `exercise_18_E_3_delta`). Each type gets at
least the value of her endowment `q_h` (buying nothing), and the two utilities sum to at most
`v(1, 1) = 1`. -/
theorem exercise_18_E_3 {q : Fin 2 → ℝ} {x : Fin 2 → (Fin 2 → ℝ) × ℝ}
    (hW : leontiefQLEconomy.IsWalrasEqm qlOnes q x) (hq0 : 0 < q 0) (hq1 : 0 < q 1)
    (h : Fin 2) : leontiefQLEconomy.u h (x h) < 1 := by
  have hlow : ∀ k, qlPrice q (leontiefQLEconomy.ω k) ≤ leontiefQLEconomy.u k (x k) := by
    intro k
    have := (hW.2 k).2 (0, qlPrice q (leontiefQLEconomy.ω k)) le_rfl (by simp [qlPrice])
    simpa [QLEconomy.u, leontiefQLEconomy] using this
  have hsum := leontief_welfare_le (fun _ => zero_le_one) hW.1
  simp only [QLEconomy.welfare, Fin.sum_univ_two, one_mul, min_self] at hsum
  have p0 : qlPrice q (leontiefQLEconomy.ω 0) = q 0 := by
    simp [qlPrice, leontiefQLEconomy, dotProduct, Fin.sum_univ_two]
  have p1 : qlPrice q (leontiefQLEconomy.ω 1) = q 1 := by
    simp [qlPrice, leontiefQLEconomy, dotProduct, Fin.sum_univ_two]
  have l0 := hlow 0
  have l1 := hlow 1
  rw [p0] at l0
  rw [p1] at l1
  fin_cases h
  · simp only [Fin.zero_eta, Fin.isValue]; linarith
  · simp only [Fin.mk_one, Fin.isValue]; linarith

/-- **Exercise 18.E.3** (MWG, p. 685). The Walrasian equilibrium with prices `(1/2, 1/2)`: each
type consumes `(1/2, 1/2)` and gets utility `1/2 < 1`. -/
theorem exercise_18_E_3_eqm :
    leontiefQLEconomy.IsWalrasEqm qlOnes (fun _ => 1 / 2) (fun _ => (fun _ => 1 / 2, 0)) := by
  refine ⟨⟨fun _ _ => by norm_num, fun l => ?_, ?_⟩, fun h => ⟨?_, fun x' _ hb => ?_⟩⟩
  · fin_cases l <;> simp [Fin.sum_univ_two, leontiefQLEconomy, qlOnes]
  · simp [Fin.sum_univ_two, leontiefQLEconomy]
  · fin_cases h <;> simp [qlPrice, leontiefQLEconomy, dotProduct, Fin.sum_univ_two]
  · have hω : qlPrice (fun _ => (1 : ℝ) / 2) (leontiefQLEconomy.ω h) = 1 / 2 := by
      fin_cases h <;> simp [qlPrice, leontiefQLEconomy, dotProduct, Fin.sum_univ_two]
    rw [hω] at hb
    simp only [qlPrice, dotProduct, Fin.sum_univ_two] at hb
    simp only [QLEconomy.u, leontiefQLEconomy, min_self, add_zero]
    have := min_le_left (x'.1 0) (x'.1 1)
    have := min_le_right (x'.1 0) (x'.1 1)
    linarith

/-- **Exercise 18.E.3** (MWG, p. 685), boundary prices. `(1, 0)` with `x*₀ = ((1, 1), 0)`,
`x*₁ = 0` is also a Walrasian equilibrium, and there type 0 gets exactly her marginal
contribution `1`: positivity of both prices is needed for "every trader gets less". -/
theorem exercise_18_E_3_boundary :
    leontiefQLEconomy.IsWalrasEqm qlOnes ![1, 0] ![((fun _ => 1 : Fin 2 → ℝ), (0 : ℝ)), 0] ∧
      leontiefQLEconomy.u 0 (![((fun _ => 1 : Fin 2 → ℝ), (0 : ℝ)), 0] 0) = 1 := by
  refine ⟨⟨⟨fun h l => ?_, fun l => ?_, ?_⟩, fun h => ⟨?_, fun x' hx' hb => ?_⟩⟩, ?_⟩
  · fin_cases h <;> simp
  · fin_cases l <;> simp [Fin.sum_univ_two, leontiefQLEconomy, qlOnes]
  · simp [Fin.sum_univ_two, leontiefQLEconomy]
  · fin_cases h <;> simp [qlPrice, leontiefQLEconomy, dotProduct, Fin.sum_univ_two]
  · have := min_le_left (x'.1 0) (x'.1 1)
    fin_cases h <;>
      simp [qlPrice, leontiefQLEconomy, dotProduct, Fin.sum_univ_two, QLEconomy.u] at hb ⊢ <;>
      linarith
  · simp [QLEconomy.u, leontiefQLEconomy]

/-- **Exercise 18.E.3** hypotheses (MWG, p. 685): the Leontief economy satisfies the concavity,
monotonicity and endowment hypotheses of Proposition 18.E.1; what fails is the differentiability
of `v` (`exercise_18_E_3_not_differentiable`), and indeed the Walrasian utilities `1/2` differ
from both one-sided partial derivatives `1` and `0`. -/
theorem exercise_18_E_3_hypotheses :
    (∀ h, ConcaveOn ℝ (Set.Ici 0) (leontiefQLEconomy.ψ h)) ∧
      (∀ h, MonotoneOn (leontiefQLEconomy.ψ h) (Set.Ici 0)) ∧
      (∀ h, 0 ≤ (leontiefQLEconomy.ω h).1) ∧ ¬ DifferentiableAt ℝ leontiefQLEconomy.v qlOnes := by
  refine ⟨leontief_concave, leontief_mono, fun h l => ?_, exercise_18_E_3_not_differentiable⟩
  fin_cases h <;> fin_cases l <;> simp [leontiefQLEconomy]

/-! ### The Shapley value (p. 673) -/

/-- **Section 18.E** (MWG, p. 673). The TU game of a finite economy with consumers
`i : Fin n` of types `τ i`: the worth of a coalition `S` is `v` of its type profile. -/
noncomputable def qlShapleyGame {H : Type*} [Fintype H] [DecidableEq H] {n : ℕ}
    (E : QLEconomy H K) (τ : Fin n → H) :
    MWG.WelfareBargaining.Game n :=
  fun S => E.v (fun h => ((S.filter fun i => τ i = h).card : ℝ))

/-- **Section 18.E** (MWG, p. 673). The Shapley value of the economy's TU game distributes
exactly `v(I)`: `∑ᵢ Shᵢ = v(I)` (grouping consumers by type, `∑_h I_h Sh_h = v(I)` when equal
types get equal values). From Chapter 22's `shapley_pareto` and `v(0) = 0`. -/
theorem claim_18_E_shapley_sum {H : Type*} [Fintype H] [DecidableEq H] {n : ℕ}
    (E : QLEconomy H K) (τ : Fin n → H) :
    ∑ i, MWG.WelfareBargaining.shapley (qlShapleyGame E τ) i = E.v (qlTypeCount τ) := by
  rw [MWG.WelfareBargaining.shapley_pareto]
  · rfl
  · simp only [qlShapleyGame, Finset.filter_empty, Finset.card_empty, Nat.cast_zero]
    exact E.v_zero

end MWG.CoreFoundations
