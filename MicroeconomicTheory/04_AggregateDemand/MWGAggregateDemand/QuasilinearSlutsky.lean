/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGAggregateDemand.QuasilinearPair
import MWGAggregateDemand.MitiushinPolterovich
import MWGAggregateDemand.Representative
import MWGClassicalDemand.SARPTwoGoods

/-!
# Exercises 4.C.11(b) and 4.D.10: Slutsky matrices of the quasilinear pair

MWG, Exercise 4.C.11(b) (pp. 124-125) and Exercise 4.D.10 (p. 126). Two goods;
`u₁(x) = x₁ + 4√x₂`, `u₂(x) = 4√x₁ + x₂`; equal wealths `w/2`.

* `ql_uld_consumer1`, `ql_uld_consumer2`: each individual demand satisfies the ULD, corners
  included, by `mp_uld_on` (Proposition 4.C.3 on the convex set `{x ≥ 0 : x₂ > 0}`, resp.
  `{x ≥ 0 : x₁ > 0}`, where `σ(x) = √x₂/(x₁ + 2√x₂) < 4`).
* `exercise_4_C_11b_consumer1`, `exercise_4_C_11b_consumer2`: the individual Slutsky matrices,
  `v·S₁ v = -(8/p₂³)(p₂ v₁ - p₁ v₂)²` where consumer 1 is interior and `S₁ = 0` at the corner
  (and the mirror image for consumer 2).
* `exercise_4_C_11b_aggregate`: in each of the four open regions (each consumer interior or at
  a corner) aggregate demand is differentiable with `v·S v = κ (p₂ v₁ - p₁ v₂)²`, `κ < 0`; hence
  `dp·S(p, w) dp < 0` for `dp` not proportional to `p`. On the kinks between the regions
  aggregate demand is not differentiable.
* `exercise_4_C_11b_weakAxiom`: aggregate demand satisfies the ULD and the weak axiom
  everywhere, kinks included (Proposition 4.C.1).
* `exercise_4_D_10_positive`, `exercise_4_D_10_normative`: there is a positive representative
  consumer (the weak axiom implies the strong axiom for `L = 2`, MWG Chapter 3's Exercise 3.J.1
  and Proposition 3.J.1), but no normative representative consumer for any increasing social
  welfare function: at `p̄ = (1, 1)`, `w̄ = 12` (where `C(p̄, w̄)` is not positive semidefinite,
  Exercise 4.C.11(c)) a finite chain of revealed preferences of the representative leads from
  `x̄` to a bundle that is strictly worse than `x̄`, yet affords an aggregate bundle of the set
  `A`, which `A ⊆ B` forbids.
-/

namespace MWG.AggregateDemand

open MWG.ConsumerChoice MWG.ClassicalDemand Filter Topology

/-- The quasilinear utility `x_i + 4√x_j` on `ℝ²` (`u₁` for `(i, j) = (0, 1)`, `u₂` for
`(1, 0)`). -/
noncomputable def qlGen (i j : Fin 2) (x : Fin 2 → ℝ) : ℝ := x i + 4 * Real.sqrt (x j)

/-- The gradient of `qlGen i j` where `x_j > 0`. -/
noncomputable def qlGrad (i j : Fin 2) (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  Pi.single i 1 + Pi.single j (2 / Real.sqrt (x j))

/-- The Hessian of `qlGen i j` where `x_j > 0`: `v ↦ v_j (-1/(x_j √x_j)) e_j`. -/
noncomputable def qlHess (j : Fin 2) (x : Fin 2 → ℝ) : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) j).smulRight
    (Pi.single j (-(1 / (x j * Real.sqrt (x j)))) : Fin 2 → ℝ)

theorem qlHess_apply (j : Fin 2) (x v : Fin 2 → ℝ) :
    qlHess j x v = v j • (Pi.single j (-(1 / (x j * Real.sqrt (x j)))) : Fin 2 → ℝ) := by
  simp [qlHess]

theorem ql1_eq_qlGen : ql1 = qlGen 0 1 := rfl

theorem ql2_eq_qlGen : ql2 = qlGen 1 0 := by
  funext x
  simp only [ql2, qlGen]
  ring

/-- **Exercise 4.C.11** (MWG, p. 124), via Proposition 4.C.3: the quasilinear utility
`x_i + 4√x_j` satisfies the Mitiushin-Polterovich hypotheses on `{x ≥ 0 : x_j > 0}`, so a
single-valued demand with `x_j > 0` satisfying Walras' law satisfies the ULD. -/
theorem ql_uld (i j : Fin 2) {xf : DemandFunction 2}
    (hxf : ∀ p w, PWDomain p w → xf p w ∈ walrasianDemand (qlGen i j) p w)
    (hxj : ∀ p w, PWDomain p w → 0 < xf p w j)
    (huniq : ∀ p w, PWDomain p w → (walrasianDemand (qlGen i j) p w).Subsingleton)
    (hW : WalrasLaw xf) : UncompensatedLawOfDemand xf := by
  set K : Set (Fin 2 → ℝ) := {x | x ∈ nonnegOrthant 2 ∧ 0 < x j} with hKdef
  have hK : Convex ℝ K := by
    intro x hx y hy a b ha hb hab
    refine ⟨convex_nonnegOrthant 2 hx.1 hy.1 ha hb hab, ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases eq_or_lt_of_le ha with ha0 | ha0
    · rw [← ha0, zero_add] at hab
      rw [← ha0, hab]
      simpa using hy.2
    · exact add_pos_of_pos_of_nonneg (mul_pos ha0 hx.2) (mul_nonneg hb hy.2.le)
  have hu : ∀ x ∈ K, HasFDerivAt (qlGen i j) (dualityDotCLM (qlGrad i j x)) x := by
    intro x hx
    have hs := Real.sqrt_pos.mpr hx.2
    have h2 := (Real.hasDerivAt_sqrt hx.2.ne').comp_hasFDerivAt x
      (hasFDerivAt_apply (𝕜 := ℝ) j x)
    have h := (hasFDerivAt_apply (𝕜 := ℝ) i x).add (h2.const_mul 4)
    refine (h.congr_fderiv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
    · ext v
      simp [dualityDotCLM_apply, qlGrad, add_dotProduct, single_dotProduct]
      field_simp
      ring
    · simp [qlGen]
  have hG : ∀ x ∈ K, HasFDerivAt (qlGrad i j) (qlHess j x) x := by
    intro x hx
    have hs := Real.sqrt_pos.mpr hx.2
    have hd : HasDerivAt (fun s => 2 / Real.sqrt s) (-(1 / (x j * Real.sqrt (x j)))) (x j) := by
      have := (hasDerivAt_const (x j) (2 : ℝ)).div (Real.hasDerivAt_sqrt hx.2.ne') hs.ne'
      convert this using 1
      rw [Real.sq_sqrt hx.2.le]
      field_simp
      ring
    have hf := hd.comp_hasFDerivAt x (hasFDerivAt_apply (𝕜 := ℝ) j x)
    have hsg := (ContinuousLinearMap.single ℝ (fun _ : Fin 2 => ℝ) j).hasFDerivAt.comp x hf
    have h := (hasFDerivAt_const (Pi.single i (1 : ℝ) : Fin 2 → ℝ) x).add hsg
    refine (h.congr_fderiv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
    · ext v l
      by_cases hl : l = j
      · subst hl; simp [qlHess_apply]; ring
      · simp [qlHess_apply, hl]
    · simp [qlGrad, Function.comp_def]
  have hsymm : ∀ x ∈ K, ∀ v z, v ⬝ᵥ qlHess j x z = z ⬝ᵥ qlHess j x v := by
    intro x _ v z
    simp only [qlHess_apply, dotProduct_smul, dotProduct_single, smul_eq_mul]
    ring
  have hquad : ∀ x z, z ⬝ᵥ qlHess j x z = -(z j ^ 2 / (x j * Real.sqrt (x j))) := by
    intro x z
    simp only [qlHess_apply, dotProduct_smul, dotProduct_single, smul_eq_mul]
    ring
  have hnsd : ∀ x ∈ K, ∀ z, z ⬝ᵥ qlHess j x z ≤ 0 := by
    intro x hx z
    rw [hquad]
    have := Real.sqrt_pos.mpr hx.2
    have : 0 < x j * Real.sqrt (x j) := mul_pos hx.2 this
    have := div_nonneg (sq_nonneg (z j)) this.le
    linarith
  have hdot : ∀ x ∈ K, x ⬝ᵥ qlGrad i j x = x i + 2 * Real.sqrt (x j) := by
    intro x hx
    have hs := Real.sqrt_pos.mpr hx.2
    have hss := Real.sq_sqrt hx.2.le
    simp only [qlGrad, dotProduct_add, dotProduct_single, mul_one]
    field_simp
    linear_combination (-2 : ℝ) * hss
  have hpos : ∀ x ∈ K, 0 < x ⬝ᵥ qlGrad i j x := by
    intro x hx
    rw [hdot x hx]
    have := Real.sqrt_pos.mpr hx.2
    have := hx.1 i
    linarith
  have hσ : ∀ x ∈ K, -(x ⬝ᵥ qlHess j x x) < 4 * (x ⬝ᵥ qlGrad i j x) := by
    intro x hx
    rw [hquad, hdot x hx]
    have hs := Real.sqrt_pos.mpr hx.2
    have hss := Real.sq_sqrt hx.2.le
    have e : x j ^ 2 / (x j * Real.sqrt (x j)) = Real.sqrt (x j) := by
      field_simp
      nlinarith [hss]
    rw [neg_neg, e]
    have := hx.1 i
    linarith
  exact mp_uld_on hK hu hG hsymm hnsd hpos hσ hxf (fun p w hd => ⟨(hxf p w hd).1.1, hxj p w hd⟩)
    huniq hW

/-- A demand function that is the unique Walrasian demand is homogeneous of degree zero
(MWG Proposition 3.D.2(i)). -/
theorem homogeneousZero_of_singleton {L : ℕ} {u : (Fin L → ℝ) → ℝ} {xf : DemandFunction L}
    (h : ∀ p w, PWDomain p w → walrasianDemand u p w = {xf p w}) : HomogeneousZero xf := by
  intro p w α hd ha
  have h1 := h _ _ (pwDomain_smul hd ha)
  rw [proposition_3_D_2_i u p w ha, h p w hd] at h1
  exact (Set.singleton_eq_singleton_iff.mp h1).symm

/-- **Exercise 4.C.11(a)** (MWG, p. 124), consumer 1's demand at every `(p, W)`: it is the unique
Walrasian demand, has `x₂ > 0` and exhausts the budget. -/
theorem ql1_facts {x1 : DemandFunction 2}
    (hx1 : ∀ p w, PWDomain p w → x1 p w ∈ walrasianDemand ql1 p w) {p : Fin 2 → ℝ} {W : ℝ}
    (hd : PWDomain p W) :
    walrasianDemand ql1 p W = {x1 p W} ∧ 0 < x1 p W 1 ∧ p ⬝ᵥ x1 p W = W := by
  have h0 := hd.1 0
  have h1 := hd.1 1
  have hm := hx1 p W hd
  by_cases h : 4 * p 0 ^ 2 / p 1 ≤ W
  · have e := (exercise_4_C_11a_consumer1 hd.1).1 h
    rw [e, Set.mem_singleton_iff] at hm
    rw [e, hm, dotProduct_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    refine ⟨trivial, by positivity, ?_⟩
    field_simp
    ring
  · push Not at h
    have e := (exercise_4_C_11a_consumer1 hd.1).2 hd.2.le h
    rw [e, Set.mem_singleton_iff] at hm
    rw [e, hm, dotProduct_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    refine ⟨trivial, div_pos hd.2 h1, ?_⟩
    field_simp
    ring

/-- **Exercise 4.C.11(a)** (MWG, p. 124), consumer 2's demand at every `(p, W)`: it is the unique
Walrasian demand, has `x₁ > 0` and exhausts the budget. -/
theorem ql2_facts {x2 : DemandFunction 2}
    (hx2 : ∀ p w, PWDomain p w → x2 p w ∈ walrasianDemand ql2 p w) {p : Fin 2 → ℝ} {W : ℝ}
    (hd : PWDomain p W) :
    walrasianDemand ql2 p W = {x2 p W} ∧ 0 < x2 p W 0 ∧ p ⬝ᵥ x2 p W = W := by
  have h0 := hd.1 0
  have h1 := hd.1 1
  have hm := hx2 p W hd
  by_cases h : 4 * p 1 ^ 2 / p 0 ≤ W
  · have e := (exercise_4_C_11a_consumer2 hd.1).1 h
    rw [e, Set.mem_singleton_iff] at hm
    rw [e, hm, dotProduct_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    refine ⟨trivial, by positivity, ?_⟩
    field_simp
    ring
  · push Not at h
    have e := (exercise_4_C_11a_consumer2 hd.1).2 hd.2.le h
    rw [e, Set.mem_singleton_iff] at hm
    rw [e, hm, dotProduct_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    refine ⟨trivial, div_pos hd.2 h0, ?_⟩
    field_simp
    ring

/-- **Exercise 4.C.11** (MWG, p. 124). Consumer 1's demand satisfies the ULD (corners included). -/
theorem ql_uld_consumer1 {x1 : DemandFunction 2}
    (hx1 : ∀ p w, PWDomain p w → x1 p w ∈ walrasianDemand ql1 p w) :
    UncompensatedLawOfDemand x1 :=
  ql_uld 0 1 hx1 (fun _ _ hd => (ql1_facts hx1 hd).2.1)
    (fun _ _ hd => by rw [← ql1_eq_qlGen, (ql1_facts hx1 hd).1]; exact Set.subsingleton_singleton)
    fun _ _ hd => (ql1_facts hx1 hd).2.2

/-- **Exercise 4.C.11** (MWG, p. 124). Consumer 2's demand satisfies the ULD (corners included). -/
theorem ql_uld_consumer2 {x2 : DemandFunction 2}
    (hx2 : ∀ p w, PWDomain p w → x2 p w ∈ walrasianDemand ql2 p w) :
    UncompensatedLawOfDemand x2 :=
  ql_uld 1 0 (by rw [← ql2_eq_qlGen]; exact hx2) (fun _ _ hd => (ql2_facts hx2 hd).2.1)
    (fun _ _ hd => by rw [← ql2_eq_qlGen, (ql2_facts hx2 hd).1]; exact Set.subsingleton_singleton)
    fun _ _ hd => (ql2_facts hx2 hd).2.2

/-- **Exercise 4.C.11(b)** (MWG, p. 125), "conclude that aggregate demand satisfies the WA",
everywhere, including the kinks between the interior and corner regions: each individual demand
satisfies the ULD, so aggregate demand with equal shares satisfies the ULD and the weak axiom
(Proposition 4.C.1); it also satisfies Walras' law. -/
theorem exercise_4_C_11b_weakAxiom {x1 x2 : DemandFunction 2}
    (hx1 : ∀ p w, PWDomain p w → x1 p w ∈ walrasianDemand ql1 p w)
    (hx2 : ∀ p w, PWDomain p w → x2 p w ∈ walrasianDemand ql2 p w) :
    UncompensatedLawOfDemand (shareDemand ![x1, x2] ![1 / 2, 1 / 2]) ∧
      WeakAxiom (shareDemand ![x1, x2] ![1 / 2, 1 / 2]) ∧
      WalrasLaw (shareDemand ![x1, x2] ![1 / 2, 1 / 2]) := by
  have hα : ∀ i, 0 < (![1 / 2, 1 / 2] : Fin 2 → ℝ) i := by
    intro i; fin_cases i <;> norm_num
  have hα1 : ∑ i, (![1 / 2, 1 / 2] : Fin 2 → ℝ) i = 1 := by
    rw [Fin.sum_univ_two]; norm_num
  have hH : ∀ i, HomogeneousZero ((![x1, x2] : Fin 2 → DemandFunction 2) i) := by
    intro i; fin_cases i
    · exact homogeneousZero_of_singleton fun _ _ hd => (ql1_facts hx1 hd).1
    · exact homogeneousZero_of_singleton fun _ _ hd => (ql2_facts hx2 hd).1
  have hW : ∀ i, WalrasLaw ((![x1, x2] : Fin 2 → DemandFunction 2) i) := by
    intro i; fin_cases i
    · exact fun _ _ hd => (ql1_facts hx1 hd).2.2
    · exact fun _ _ hd => (ql2_facts hx2 hd).2.2
  have hU : ∀ i, UncompensatedLawOfDemand ((![x1, x2] : Fin 2 → DemandFunction 2) i) := by
    intro i; fin_cases i
    · exact ql_uld_consumer1 hx1
    · exact ql_uld_consumer2 hx2
  have hpos : ∀ i (p : Fin 2 → ℝ) w, PWDomain p w →
      0 < shareRule (![1 / 2, 1 / 2] : Fin 2 → ℝ) i p w :=
    fun i _ _ hd => mul_pos (hα i) hd.2
  obtain ⟨h1, h2⟩ := proposition_4_C_1 hα hα1 hH hW hU
  exact ⟨h1, h2, ruleDemand_walrasLaw hW (isWealthDistributionRule_shareRule hα1) hpos⟩

/-- **Exercise 4.D.10** (MWG, p. 126), first part. The aggregate demand of Exercise 4.C.11 has a
positive representative consumer: it satisfies Walras' law and the weak axiom, hence (`L = 2`,
MWG Exercise 3.J.1) the strong axiom, hence (MWG Proposition 3.J.1) it is rationalized by a
rational preference relation. -/
theorem exercise_4_D_10_positive {x1 x2 : DemandFunction 2}
    (hx1 : ∀ p w, PWDomain p w → x1 p w ∈ walrasianDemand ql1 p w)
    (hx2 : ∀ p w, PWDomain p w → x2 p w ∈ walrasianDemand ql2 p w) :
    ∃ r, Kreps.PreferenceProperties.Rational r ∧
      IsPositiveRepresentative r (shareDemand ![x1, x2] ![1 / 2, 1 / 2]) := by
  obtain ⟨-, hWA, hW⟩ := exercise_4_C_11b_weakAxiom hx1 hx2
  obtain ⟨r, hr, hrat⟩ := weakAxiom_rationalizable_two hW hWA
  refine ⟨r, hr, ⟨⟨fun x _ y _ => hr.1 x y, fun x _ y _ z _ => hr.2 x y z⟩, fun p w hd => ?_⟩⟩
  refine ⟨⟨fun l => ?_, (hW p w hd).le⟩, hrat p w hd⟩
  have hd' : PWDomain p (1 / 2 * w) := ⟨hd.1, by linarith [hd.2]⟩
  simp only [shareDemand, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Pi.add_apply]
  exact add_nonneg ((hx1 p _ hd').1.1 l) ((hx2 p _ hd').1.1 l)

/-! ### Exercise 4.C.11(b): the Slutsky matrices -/

/-- A derivative is determined by its values along lines: if `F` has derivative `D` at `(p, w)`
and `t ↦ F(p + t v, w + t c)` has derivative `g` at `0`, then `D(v, c) = g`. -/
theorem fderiv_eq_of_line {L : ℕ} {F : (Fin L → ℝ) × ℝ → Fin L → ℝ}
    {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)} {p : Fin L → ℝ} {w : ℝ}
    (hD : HasFDerivAt F D (p, w)) (v : Fin L → ℝ) (c : ℝ) {g : Fin L → ℝ}
    (hg : HasDerivAt (fun t : ℝ => F (p + t • v, w + t * c)) g 0) : D (v, c) = g := by
  have hl : HasDerivAt (fun t : ℝ => ((p + t • v, w + t * c) : (Fin L → ℝ) × ℝ)) (v, c) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => p + t • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add p
    have h2 : HasDerivAt (fun t : ℝ => w + t * c) c 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const c).const_add w
    exact h1.prodMk h2
  have := hD.comp_hasDerivAt_of_eq 0 hl (by simp)
  exact this.unique hg

/-- `d/dt (A + tB)/(C + tE)` at `0`. -/
theorem hasDerivAt_ratio_line (A B C E : ℝ) (hC : C ≠ 0) :
    HasDerivAt (fun t : ℝ => (A + t * B) / (C + t * E)) ((B * C - A * E) / C ^ 2) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => A + t * B) B 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const B).const_add A
  have h2 : HasDerivAt (fun t : ℝ => C + t * E) E 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const E).const_add C
  have := h1.div h2 (by simpa using hC)
  refine (this.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => rfl)
  simp

/-- `d/dt (A + tB)²/(C + tE)²` at `0`. -/
theorem hasDerivAt_sqratio_line (A B C E : ℝ) (hC : C ≠ 0) :
    HasDerivAt (fun t : ℝ => (A + t * B) ^ 2 / (C + t * E) ^ 2)
      (2 * A * B / C ^ 2 - 2 * A ^ 2 * E / C ^ 3) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => A + t * B) B 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const B).const_add A
  have h2 : HasDerivAt (fun t : ℝ => C + t * E) E 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const E).const_add C
  have := (h1.pow 2).div (h2.pow 2) (by simpa using pow_ne_zero 2 hC)
  refine (this.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => rfl)
  simp only [Pi.pow_apply, zero_mul, add_zero, Nat.cast_ofNat]
  field_simp
  ring

/-- Near a point where `0 < f` (continuous) and `p ≫ 0`, `w > 0`, these hold eventually. -/
theorem ql_eventually {p : Fin 2 → ℝ} {W : ℝ} (hd : PWDomain p W)
    {f : (Fin 2 → ℝ) × ℝ → ℝ} (hf : ContinuousAt f (p, W)) (hfp : 0 < f (p, W)) :
    ∀ᶠ q in 𝓝 ((p, W) : (Fin 2 → ℝ) × ℝ), PWDomain q.1 q.2 ∧ 0 < f q := by
  filter_upwards [(isOpen_pwDomain 2).mem_nhds hd, hf.eventually (lt_mem_nhds hfp)] with q hq h1
  exact ⟨hq, h1⟩

/-- Consumer 1's interior demand formula as a function of `(p, W)`. -/
noncomputable def qlF1 (q : (Fin 2 → ℝ) × ℝ) : Fin 2 → ℝ :=
  ![q.2 / q.1 0 - 4 * q.1 0 / q.1 1, 4 * q.1 0 ^ 2 / q.1 1 ^ 2]

/-- Consumer 1's corner demand formula. -/
noncomputable def qlC1 (q : (Fin 2 → ℝ) × ℝ) : Fin 2 → ℝ := ![0, q.2 / q.1 1]

/-- Consumer 2's interior demand formula. -/
noncomputable def qlF2 (q : (Fin 2 → ℝ) × ℝ) : Fin 2 → ℝ :=
  ![4 * q.1 1 ^ 2 / q.1 0 ^ 2, q.2 / q.1 1 - 4 * q.1 1 / q.1 0]

/-- Consumer 2's corner demand formula. -/
noncomputable def qlC2 (q : (Fin 2 → ℝ) × ℝ) : Fin 2 → ℝ := ![q.2 / q.1 0, 0]

/-- **Exercise 4.C.11(b)** (MWG, p. 125), consumer 1. Where consumer 1 is interior
(`W > 4p₁²/p₂`), demand is differentiable with
`D(v, c) = (c/p₁ - W v₁/p₁² - 4v₁/p₂ + 4p₁v₂/p₂², 8p₁v₁/p₂² - 8p₁²v₂/p₂³)` and
`v·S₁ v = -(8/p₂³)(p₂ v₁ - p₁ v₂)²`; at the corner (`0 < W < 4p₁²/p₂`)
`D(v, c) = (0, c/p₂ - W v₂/p₂²)` and `S₁ = 0`. -/
theorem exercise_4_C_11b_consumer1 {x1 : DemandFunction 2}
    (hx1 : ∀ p w, PWDomain p w → x1 p w ∈ walrasianDemand ql1 p w) {p : Fin 2 → ℝ} {W : ℝ}
    (hd : PWDomain p W) :
    (4 * p 0 ^ 2 / p 1 < W → ∃ D, HasFDerivAt (Function.uncurry x1) D (p, W) ∧
      (∀ v c, D (v, c) = ![c / p 0 - W * v 0 / p 0 ^ 2 - 4 * v 0 / p 1 + 4 * p 0 * v 1 / p 1 ^ 2,
        8 * p 0 * v 0 / p 1 ^ 2 - 8 * p 0 ^ 2 * v 1 / p 1 ^ 3]) ∧
      x1 p W = ![W / p 0 - 4 * p 0 / p 1, 4 * p 0 ^ 2 / p 1 ^ 2] ∧
      ∀ v, v ⬝ᵥ (slutskyMatrix D (x1 p W)).mulVec v =
        -(8 / p 1 ^ 3) * (p 1 * v 0 - p 0 * v 1) ^ 2) ∧
    (W < 4 * p 0 ^ 2 / p 1 → ∃ D, HasFDerivAt (Function.uncurry x1) D (p, W) ∧
      (∀ v c, D (v, c) = ![0, c / p 1 - W * v 1 / p 1 ^ 2]) ∧ x1 p W = ![0, W / p 1] ∧
      ∀ v, (slutskyMatrix D (x1 p W)).mulVec v = 0) := by
  have h0 := (hd.1 0).ne'
  have h1 := (hd.1 1).ne'
  constructor
  · intro hW
    have hev : Function.uncurry x1 =ᶠ[𝓝 (p, W)] qlF1 := by
      have hc : ContinuousAt (fun q : (Fin 2 → ℝ) × ℝ => q.2 - 4 * q.1 0 ^ 2 / q.1 1) (p, W) := by
        apply ContinuousAt.sub (by fun_prop)
        exact ContinuousAt.div (by fun_prop) (by fun_prop) h1
      filter_upwards [ql_eventually hd hc (by simp only; linarith)] with q hq
      have := hx1 q.1 q.2 hq.1
      rw [(exercise_4_C_11a_consumer1 hq.1.1).1 (by linarith [hq.2])] at this
      exact this
    have hdF : DifferentiableAt ℝ qlF1 (p, W) := by
      refine differentiableAt_pi.mpr fun l => ?_
      fin_cases l <;> simp only [qlF1, Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one] <;> fun_prop (disch := simp [h1])
    have hD := hdF.hasFDerivAt.congr_of_eventuallyEq hev
    have hxv : x1 p W = ![W / p 0 - 4 * p 0 / p 1, 4 * p 0 ^ 2 / p 1 ^ 2] := hev.eq_of_nhds
    have hDv : ∀ v c, fderiv ℝ qlF1 (p, W) (v, c) =
        ![c / p 0 - W * v 0 / p 0 ^ 2 - 4 * v 0 / p 1 + 4 * p 0 * v 1 / p 1 ^ 2,
          8 * p 0 * v 0 / p 1 ^ 2 - 8 * p 0 ^ 2 * v 1 / p 1 ^ 3] := by
      intro v c
      apply fderiv_eq_of_line hdF.hasFDerivAt
      refine hasDerivAt_pi.mpr fun l => ?_
      fin_cases l
      · have := (hasDerivAt_ratio_line W c (p 0) (v 0) h0).sub
          ((hasDerivAt_ratio_line (p 0) (v 0) (p 1) (v 1) h1).const_mul 4)
        convert this using 1
        · funext t
          simp [qlF1]
          ring
        · simp only [Fin.zero_eta, Matrix.cons_val_zero]
          field_simp
          ring
      · have := (hasDerivAt_sqratio_line (p 0) (v 0) (p 1) (v 1) h1).const_mul 4
        convert this using 1
        · funext t
          simp [qlF1]
          ring
        · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
          field_simp
          ring
    refine ⟨_, hD, hDv, hxv, fun v => ?_⟩
    rw [slutskyMatrix_mulVec, hDv, hxv, dotProduct_two, dotProduct_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    field_simp
    ring
  · intro hW
    have hev : Function.uncurry x1 =ᶠ[𝓝 (p, W)] qlC1 := by
      have hc : ContinuousAt (fun q : (Fin 2 → ℝ) × ℝ => 4 * q.1 0 ^ 2 / q.1 1 - q.2) (p, W) := by
        refine ContinuousAt.sub ?_ (by fun_prop)
        exact ContinuousAt.div (by fun_prop) (by fun_prop) h1
      filter_upwards [ql_eventually hd hc (by simp only; linarith)] with q hq
      have := hx1 q.1 q.2 hq.1
      rw [(exercise_4_C_11a_consumer1 hq.1.1).2 hq.1.2.le (by linarith [hq.2])] at this
      exact this
    have hdF : DifferentiableAt ℝ qlC1 (p, W) := by
      refine differentiableAt_pi.mpr fun l => ?_
      fin_cases l <;> simp only [qlC1, Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one] <;> fun_prop (disch := simp [h1])
    have hD := hdF.hasFDerivAt.congr_of_eventuallyEq hev
    have hxv : x1 p W = ![0, W / p 1] := hev.eq_of_nhds
    have hDv : ∀ v c, fderiv ℝ qlC1 (p, W) (v, c) = ![0, c / p 1 - W * v 1 / p 1 ^ 2] := by
      intro v c
      apply fderiv_eq_of_line hdF.hasFDerivAt
      refine hasDerivAt_pi.mpr fun l => ?_
      fin_cases l
      · simpa [qlC1] using hasDerivAt_const (0 : ℝ) (0 : ℝ)
      · have := hasDerivAt_ratio_line W c (p 1) (v 1) h1
        convert this using 1
        · funext t
          simp [qlC1]
        · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
          field_simp
    refine ⟨_, hD, hDv, hxv, fun v => ?_⟩
    rw [slutskyMatrix_mulVec, hDv, hxv, dotProduct_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    funext l
    fin_cases l
    · simp
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.zero_apply]
      field_simp
      ring

/-- **Exercise 4.C.11(b)** (MWG, p. 125), consumer 2 (the mirror image of consumer 1). Where
consumer 2 is interior (`W > 4p₂²/p₁`), `v·S₂ v = -(8/p₁³)(p₂ v₁ - p₁ v₂)²`; at the corner
(`0 < W < 4p₂²/p₁`) `S₂ = 0`. -/
theorem exercise_4_C_11b_consumer2 {x2 : DemandFunction 2}
    (hx2 : ∀ p w, PWDomain p w → x2 p w ∈ walrasianDemand ql2 p w) {p : Fin 2 → ℝ} {W : ℝ}
    (hd : PWDomain p W) :
    (4 * p 1 ^ 2 / p 0 < W → ∃ D, HasFDerivAt (Function.uncurry x2) D (p, W) ∧
      (∀ v c, D (v, c) = ![8 * p 1 * v 1 / p 0 ^ 2 - 8 * p 1 ^ 2 * v 0 / p 0 ^ 3,
        c / p 1 - W * v 1 / p 1 ^ 2 - 4 * v 1 / p 0 + 4 * p 1 * v 0 / p 0 ^ 2]) ∧
      x2 p W = ![4 * p 1 ^ 2 / p 0 ^ 2, W / p 1 - 4 * p 1 / p 0] ∧
      ∀ v, v ⬝ᵥ (slutskyMatrix D (x2 p W)).mulVec v =
        -(8 / p 0 ^ 3) * (p 1 * v 0 - p 0 * v 1) ^ 2) ∧
    (W < 4 * p 1 ^ 2 / p 0 → ∃ D, HasFDerivAt (Function.uncurry x2) D (p, W) ∧
      (∀ v c, D (v, c) = ![c / p 0 - W * v 0 / p 0 ^ 2, 0]) ∧ x2 p W = ![W / p 0, 0] ∧
      ∀ v, (slutskyMatrix D (x2 p W)).mulVec v = 0) := by
  have h0 := (hd.1 0).ne'
  have h1 := (hd.1 1).ne'
  constructor
  · intro hW
    have hev : Function.uncurry x2 =ᶠ[𝓝 (p, W)] qlF2 := by
      have hc : ContinuousAt (fun q : (Fin 2 → ℝ) × ℝ => q.2 - 4 * q.1 1 ^ 2 / q.1 0) (p, W) := by
        apply ContinuousAt.sub (by fun_prop)
        exact ContinuousAt.div (by fun_prop) (by fun_prop) h0
      filter_upwards [ql_eventually hd hc (by simp only; linarith)] with q hq
      have := hx2 q.1 q.2 hq.1
      rw [(exercise_4_C_11a_consumer2 hq.1.1).1 (by linarith [hq.2])] at this
      exact this
    have hdF : DifferentiableAt ℝ qlF2 (p, W) := by
      refine differentiableAt_pi.mpr fun l => ?_
      fin_cases l <;> simp only [qlF2, Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one] <;> fun_prop (disch := simp [h0])
    have hD := hdF.hasFDerivAt.congr_of_eventuallyEq hev
    have hxv : x2 p W = ![4 * p 1 ^ 2 / p 0 ^ 2, W / p 1 - 4 * p 1 / p 0] := hev.eq_of_nhds
    have hDv : ∀ v c, fderiv ℝ qlF2 (p, W) (v, c) =
        ![8 * p 1 * v 1 / p 0 ^ 2 - 8 * p 1 ^ 2 * v 0 / p 0 ^ 3,
          c / p 1 - W * v 1 / p 1 ^ 2 - 4 * v 1 / p 0 + 4 * p 1 * v 0 / p 0 ^ 2] := by
      intro v c
      apply fderiv_eq_of_line hdF.hasFDerivAt
      refine hasDerivAt_pi.mpr fun l => ?_
      fin_cases l
      · have := (hasDerivAt_sqratio_line (p 1) (v 1) (p 0) (v 0) h0).const_mul 4
        convert this using 1
        · funext t
          simp [qlF2]
          ring
        · simp only [Fin.zero_eta, Matrix.cons_val_zero]
          field_simp
          ring
      · have := (hasDerivAt_ratio_line W c (p 1) (v 1) h1).sub
          ((hasDerivAt_ratio_line (p 1) (v 1) (p 0) (v 0) h0).const_mul 4)
        convert this using 1
        · funext t
          simp [qlF2]
          ring
        · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
          field_simp
          ring
    refine ⟨_, hD, hDv, hxv, fun v => ?_⟩
    rw [slutskyMatrix_mulVec, hDv, hxv, dotProduct_two, dotProduct_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    field_simp
    ring
  · intro hW
    have hev : Function.uncurry x2 =ᶠ[𝓝 (p, W)] qlC2 := by
      have hc : ContinuousAt (fun q : (Fin 2 → ℝ) × ℝ => 4 * q.1 1 ^ 2 / q.1 0 - q.2) (p, W) := by
        refine ContinuousAt.sub ?_ (by fun_prop)
        exact ContinuousAt.div (by fun_prop) (by fun_prop) h0
      filter_upwards [ql_eventually hd hc (by simp only; linarith)] with q hq
      have := hx2 q.1 q.2 hq.1
      rw [(exercise_4_C_11a_consumer2 hq.1.1).2 hq.1.2.le (by linarith [hq.2])] at this
      exact this
    have hdF : DifferentiableAt ℝ qlC2 (p, W) := by
      refine differentiableAt_pi.mpr fun l => ?_
      fin_cases l <;> simp only [qlC2, Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one] <;> fun_prop (disch := simp [h0])
    have hD := hdF.hasFDerivAt.congr_of_eventuallyEq hev
    have hxv : x2 p W = ![W / p 0, 0] := hev.eq_of_nhds
    have hDv : ∀ v c, fderiv ℝ qlC2 (p, W) (v, c) = ![c / p 0 - W * v 0 / p 0 ^ 2, 0] := by
      intro v c
      apply fderiv_eq_of_line hdF.hasFDerivAt
      refine hasDerivAt_pi.mpr fun l => ?_
      fin_cases l
      · have := hasDerivAt_ratio_line W c (p 0) (v 0) h0
        convert this using 1
        · funext t
          simp [qlC2]
        · simp only [Fin.zero_eta, Matrix.cons_val_zero]
          field_simp
      · simpa [qlC2] using hasDerivAt_const (0 : ℝ) (0 : ℝ)
    refine ⟨_, hD, hDv, hxv, fun v => ?_⟩
    rw [slutskyMatrix_mulVec, hDv, hxv, dotProduct_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    funext l
    fin_cases l
    · simp only [Fin.zero_eta, Matrix.cons_val_zero, Pi.zero_apply]
      field_simp
      ring
    · simp

/-- The aggregate Slutsky matrix of the equal-share pair from the individual derivatives:
`S(p, w) v = D₁(v, ½ v·x) + D₂(v, ½ v·x)` with `x = x₁(p, w/2) + x₂(p, w/2)`. -/
theorem ql_agg_slutsky {x1 x2 : DemandFunction 2} {p : Fin 2 → ℝ} {w : ℝ}
    {D1 D2 : ((Fin 2 → ℝ) × ℝ) →L[ℝ] (Fin 2 → ℝ)}
    (h1 : HasFDerivAt (Function.uncurry x1) D1 (p, 1 / 2 * w))
    (h2 : HasFDerivAt (Function.uncurry x2) D2 (p, 1 / 2 * w)) :
    ∃ D, HasFDerivAt (Function.uncurry (shareDemand ![x1, x2] ![1 / 2, 1 / 2])) D (p, w) ∧
      shareDemand ![x1, x2] ![1 / 2, 1 / 2] p w = x1 p (1 / 2 * w) + x2 p (1 / 2 * w) ∧
      ∀ v, (slutskyMatrix D (shareDemand ![x1, x2] ![1 / 2, 1 / 2] p w)).mulVec v =
        D1 (v, 1 / 2 * (v ⬝ᵥ (x1 p (1 / 2 * w) + x2 p (1 / 2 * w)))) +
          D2 (v, 1 / 2 * (v ⬝ᵥ (x1 p (1 / 2 * w) + x2 p (1 / 2 * w)))) := by
  have hD : ∀ i, HasFDerivAt (Function.uncurry ((![x1, x2] : Fin 2 → DemandFunction 2) i))
      ((![D1, D2] : Fin 2 → ((Fin 2 → ℝ) × ℝ) →L[ℝ] (Fin 2 → ℝ)) i)
      (p, (![1 / 2, 1 / 2] : Fin 2 → ℝ) i * w) := by
    intro i; fin_cases i
    · exact h1
    · exact h2
  have hx : shareDemand ![x1, x2] ![1 / 2, 1 / 2] p w = x1 p (1 / 2 * w) + x2 p (1 / 2 * w) := by
    simp [shareDemand, Fin.sum_univ_two]
  refine ⟨_, hasFDerivAt_shareDemand hD, hx, fun v => ?_⟩
  rw [slutskyMatrix_mulVec, hx]
  simp [Fin.sum_univ_two, scaleWealthCLM_apply]

/-- A vector with `p₂ v₁ - p₁ v₂ = 0` is proportional to `p ≫ 0`. -/
theorem ql_prop_of_cross {p v : Fin 2 → ℝ} (hp : StrictlyPositive p)
    (h : p 1 * v 0 - p 0 * v 1 = 0) : v = (v 0 / p 0) • p := by
  have h0 := (hp 0).ne'
  funext l
  fin_cases l
  · simp only [Fin.zero_eta, Pi.smul_apply, smul_eq_mul]
    field_simp
  · simp only [Fin.mk_one, Pi.smul_apply, smul_eq_mul]
    field_simp
    linarith

/-- **Exercise 4.C.11(b)** (MWG, p. 125), the aggregate Slutsky matrix. In each of the four open
regions (consumer 1 interior iff `w/2 > 4p₁²/p₂`, consumer 2 interior iff `w/2 > 4p₂²/p₁`)
aggregate demand is differentiable and `v·S(p, w) v = κ (p₂ v₁ - p₁ v₂)²` with
`κ = -(6/p₁³ + 6/p₂³ + w/(4p₁²p₂²))` (both interior), `-8/p₂³`, `-8/p₁³` (one interior) and
`-w/(4p₁²p₂²)` (both at corners). -/
theorem exercise_4_C_11b_aggregate {x1 x2 : DemandFunction 2}
    (hx1 : ∀ p w, PWDomain p w → x1 p w ∈ walrasianDemand ql1 p w)
    (hx2 : ∀ p w, PWDomain p w → x2 p w ∈ walrasianDemand ql2 p w) {p : Fin 2 → ℝ} {w : ℝ}
    (hd : PWDomain p w) :
    (4 * p 0 ^ 2 / p 1 < w / 2 → 4 * p 1 ^ 2 / p 0 < w / 2 →
      ∃ D, HasFDerivAt (Function.uncurry (shareDemand ![x1, x2] ![1 / 2, 1 / 2])) D (p, w) ∧
        ∀ v, v ⬝ᵥ (slutskyMatrix D (shareDemand ![x1, x2] ![1 / 2, 1 / 2] p w)).mulVec v =
          -(6 / p 0 ^ 3 + 6 / p 1 ^ 3 + w / (4 * p 0 ^ 2 * p 1 ^ 2)) *
            (p 1 * v 0 - p 0 * v 1) ^ 2) ∧
    (4 * p 0 ^ 2 / p 1 < w / 2 → w / 2 < 4 * p 1 ^ 2 / p 0 →
      ∃ D, HasFDerivAt (Function.uncurry (shareDemand ![x1, x2] ![1 / 2, 1 / 2])) D (p, w) ∧
        ∀ v, v ⬝ᵥ (slutskyMatrix D (shareDemand ![x1, x2] ![1 / 2, 1 / 2] p w)).mulVec v =
          -(8 / p 1 ^ 3) * (p 1 * v 0 - p 0 * v 1) ^ 2) ∧
    (w / 2 < 4 * p 0 ^ 2 / p 1 → 4 * p 1 ^ 2 / p 0 < w / 2 →
      ∃ D, HasFDerivAt (Function.uncurry (shareDemand ![x1, x2] ![1 / 2, 1 / 2])) D (p, w) ∧
        ∀ v, v ⬝ᵥ (slutskyMatrix D (shareDemand ![x1, x2] ![1 / 2, 1 / 2] p w)).mulVec v =
          -(8 / p 0 ^ 3) * (p 1 * v 0 - p 0 * v 1) ^ 2) ∧
    (w / 2 < 4 * p 0 ^ 2 / p 1 → w / 2 < 4 * p 1 ^ 2 / p 0 →
      ∃ D, HasFDerivAt (Function.uncurry (shareDemand ![x1, x2] ![1 / 2, 1 / 2])) D (p, w) ∧
        ∀ v, v ⬝ᵥ (slutskyMatrix D (shareDemand ![x1, x2] ![1 / 2, 1 / 2] p w)).mulVec v =
          -(w / (4 * p 0 ^ 2 * p 1 ^ 2)) * (p 1 * v 0 - p 0 * v 1) ^ 2) := by
  have hdW : PWDomain p (1 / 2 * w) := ⟨hd.1, by linarith [hd.2]⟩
  have h0 := (hd.1 0).ne'
  have h1 := (hd.1 1).ne'
  have e : 1 / 2 * w = w / 2 := by ring
  have c1 := exercise_4_C_11b_consumer1 hx1 hdW
  have c2 := exercise_4_C_11b_consumer2 hx2 hdW
  rw [e] at c1 c2
  refine ⟨fun ha hb => ?_, fun ha hb => ?_, fun ha hb => ?_, fun ha hb => ?_⟩
  · obtain ⟨D1, hD1, hDv1, hxv1, -⟩ := c1.1 ha
    obtain ⟨D2, hD2, hDv2, hxv2, -⟩ := c2.1 hb
    rw [← e] at hD1 hD2 hxv1 hxv2
    obtain ⟨D, hD, -, hS⟩ := ql_agg_slutsky hD1 hD2
    refine ⟨D, hD, fun v => ?_⟩
    rw [hS, hDv1, hDv2, hxv1, hxv2]
    simp only [dotProduct_two, dotProduct_add, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    field_simp
    ring
  · obtain ⟨D1, hD1, hDv1, hxv1, -⟩ := c1.1 ha
    obtain ⟨D2, hD2, hDv2, hxv2, -⟩ := c2.2 hb
    rw [← e] at hD1 hD2 hxv1 hxv2
    obtain ⟨D, hD, -, hS⟩ := ql_agg_slutsky hD1 hD2
    refine ⟨D, hD, fun v => ?_⟩
    rw [hS, hDv1, hDv2, hxv1, hxv2]
    simp only [dotProduct_two, dotProduct_add, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    field_simp
    ring
  · obtain ⟨D1, hD1, hDv1, hxv1, -⟩ := c1.2 ha
    obtain ⟨D2, hD2, hDv2, hxv2, -⟩ := c2.1 hb
    rw [← e] at hD1 hD2 hxv1 hxv2
    obtain ⟨D, hD, -, hS⟩ := ql_agg_slutsky hD1 hD2
    refine ⟨D, hD, fun v => ?_⟩
    rw [hS, hDv1, hDv2, hxv1, hxv2]
    simp only [dotProduct_two, dotProduct_add, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    field_simp
    ring
  · obtain ⟨D1, hD1, hDv1, hxv1, -⟩ := c1.2 ha
    obtain ⟨D2, hD2, hDv2, hxv2, -⟩ := c2.2 hb
    rw [← e] at hD1 hD2 hxv1 hxv2
    obtain ⟨D, hD, -, hS⟩ := ql_agg_slutsky hD1 hD2
    refine ⟨D, hD, fun v => ?_⟩
    rw [hS, hDv1, hDv2, hxv1, hxv2]
    simp only [dotProduct_two, dotProduct_add, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    field_simp
    ring

/-- **Exercise 4.C.11(b)** (MWG, p. 125). Off the kinks (`w/2 ≠ 4p₁²/p₂`, `w/2 ≠ 4p₂²/p₁`)
aggregate demand is differentiable and `dp·S(p, w) dp < 0` for every `dp` not proportional to
`p`. -/
theorem exercise_4_C_11b_negative {x1 x2 : DemandFunction 2}
    (hx1 : ∀ p w, PWDomain p w → x1 p w ∈ walrasianDemand ql1 p w)
    (hx2 : ∀ p w, PWDomain p w → x2 p w ∈ walrasianDemand ql2 p w) {p : Fin 2 → ℝ} {w : ℝ}
    (hd : PWDomain p w) (h1 : w / 2 ≠ 4 * p 0 ^ 2 / p 1) (h2 : w / 2 ≠ 4 * p 1 ^ 2 / p 0) :
    ∃ D, HasFDerivAt (Function.uncurry (shareDemand ![x1, x2] ![1 / 2, 1 / 2])) D (p, w) ∧
      ∀ v : Fin 2 → ℝ, (∀ c : ℝ, v ≠ c • p) →
        v ⬝ᵥ (slutskyMatrix D (shareDemand ![x1, x2] ![1 / 2, 1 / 2] p w)).mulVec v < 0 := by
  have hp0 := hd.1 0
  have hp1 := hd.1 1
  have hw := hd.2
  have hz : ∀ v : Fin 2 → ℝ, (∀ c : ℝ, v ≠ c • p) → 0 < (p 1 * v 0 - p 0 * v 1) ^ 2 := by
    intro v hv
    have hne : p 1 * v 0 - p 0 * v 1 ≠ 0 := fun h => hv _ (ql_prop_of_cross hd.1 h)
    positivity
  have agg := exercise_4_C_11b_aggregate hx1 hx2 hd
  rcases lt_or_gt_of_ne h1 with ha | ha <;> rcases lt_or_gt_of_ne h2 with hb | hb
  · obtain ⟨D, hD, hq⟩ := agg.2.2.2 ha hb
    exact ⟨D, hD, fun v hv => by
      rw [hq]; exact mul_neg_of_neg_of_pos (neg_neg_of_pos (by positivity)) (hz v hv)⟩
  · obtain ⟨D, hD, hq⟩ := agg.2.2.1 ha hb
    exact ⟨D, hD, fun v hv => by
      rw [hq]; exact mul_neg_of_neg_of_pos (neg_neg_of_pos (by positivity)) (hz v hv)⟩
  · obtain ⟨D, hD, hq⟩ := agg.2.1 ha hb
    exact ⟨D, hD, fun v hv => by
      rw [hq]; exact mul_neg_of_neg_of_pos (neg_neg_of_pos (by positivity)) (hz v hv)⟩
  · obtain ⟨D, hD, hq⟩ := agg.1 ha hb
    exact ⟨D, hD, fun v hv => by
      rw [hq]; exact mul_neg_of_neg_of_pos (neg_neg_of_pos (by positivity)) (hz v hv)⟩

/-- **Exercise 4.C.11(c)** (MWG, p. 125), the conclusion: `C(p, w)` positive semidefinite is not
necessary for the weak axiom. At `p = (1, 1)` and `8 < w < 16`, `C(p, w)` is not positive
semidefinite (`exercise_4_C_11c`), yet aggregate demand satisfies the weak axiom
(`exercise_4_C_11b_weakAxiom`). -/
theorem exercise_4_C_11c_conclusion {x1 x2 : DemandFunction 2}
    (hx1 : ∀ p w, PWDomain p w → x1 p w ∈ walrasianDemand ql1 p w)
    (hx2 : ∀ p w, PWDomain p w → x2 p w ∈ walrasianDemand ql2 p w) {w : ℝ} (hw : 8 < w)
    (hw' : w < 16) :
    WeakAxiom (shareDemand ![x1, x2] ![1 / 2, 1 / 2]) ∧
      ∃ D1 D2 : ((Fin 2 → ℝ) × ℝ) →L[ℝ] (Fin 2 → ℝ),
        HasFDerivAt (Function.uncurry x1) D1 (![1, 1], 1 / 2 * w) ∧
        HasFDerivAt (Function.uncurry x2) D2 (![1, 1], 1 / 2 * w) ∧
        ¬ PosSemidefMWG (covMatrix ![1 / 2, 1 / 2] ![wealthJacobian D1, wealthJacobian D2]
          ![x1 ![1, 1] (1 / 2 * w), x2 ![1, 1] (1 / 2 * w)]) := by
  obtain ⟨D1, D2, h1, h2, -, hiff⟩ := exercise_4_C_11c hx1 hx2 hw
  exact ⟨(exercise_4_C_11b_weakAxiom hx1 hx2).2.1, D1, D2, h1, h2,
    fun h => absurd (hiff.mp h) (by linarith)⟩

/-- The aggregate demand of Exercise 4.C.11 where both consumers are interior. -/
noncomputable def qlAgg (q : Fin 2 → ℝ) (m : ℝ) : Fin 2 → ℝ :=
  ![m / (2 * q 0) - 4 * q 0 / q 1 + 4 * q 1 ^ 2 / q 0 ^ 2,
    4 * q 0 ^ 2 / q 1 ^ 2 + m / (2 * q 1) - 4 * q 1 / q 0]

/-- `√a = b` for `b ≥ 0` with `a = b²`. -/
theorem ql_sqrt_eq {a b : ℝ} (hb : 0 ≤ b) (h : a = b ^ 2) : Real.sqrt a = b := by
  rw [h, Real.sqrt_sq hb]

/-- **Exercise 4.D.10** (MWG, p. 126), second part. For the economy of Exercise 4.C.11 (equal
wealth shares) there is no normative representative consumer for any nondecreasing social welfare
function `W`. At `p̄ = (1, 1)`, `w̄ = 10` (where `C(p̄, w̄)` is not positive semidefinite) the
representative must rank `x̄ = x(p̄, w̄)` strictly above `x(p₁₂, w₁₂)` along a chain of twelve
revealed preferences (`p_k = (1, 1 + k/100)`), while optimal redistribution guarantees each
consumer her utility at `x̄` with the Hicksian bundles at `p₁₂`, which cost less than `w₁₂`, so
the social (= representative) utility at `(p₁₂, w₁₂)` is at least that at `(p̄, w̄)`. -/
theorem exercise_4_D_10_normative {x1 x2 : DemandFunction 2}
    (hx1 : ∀ p w, PWDomain p w → x1 p w ∈ walrasianDemand ql1 p w)
    (hx2 : ∀ p w, PWDomain p w → x2 p w ∈ walrasianDemand ql2 p w) :
    ¬ ∃ (W : SocialWelfareFunction 2) (r : (Fin 2 → ℝ) → (Fin 2 → ℝ) → Prop), Monotone W ∧
      IsNormativeRepresentative W ![ql1, ql2] (shareRule ![1 / 2, 1 / 2]) r
        (shareDemand ![x1, x2] ![1 / 2, 1 / 2]) := by
  rintro ⟨W, r, hWm, hpos, -, hopt, u, hu, hv⟩
  set X := shareDemand ![x1, x2] ![1 / 2, 1 / 2] with hX
  -- the representative's demand maximizes `u`
  have hdem : ∀ q m, PWDomain q m → X q m ∈ walrasianDemand u q m := by
    intro q m hd
    refine ⟨(hpos.2 q m hd).1, fun y hy => ?_⟩
    by_cases hyx : y = X q m
    · rw [hyx]
    · have hs := (hpos.2 q m hd).2 y hy hyx
      have h1 := (hu y hy.1 (X q m) (hpos.2 q m hd).1.1).not.mp hs.2
      push Not at h1
      exact h1.le
  have hstrict : ∀ q m q' m', PWDomain q m → PWDomain q' m' → q ⬝ᵥ X q' m' ≤ m →
      X q' m' ≠ X q m → u (X q' m') < u (X q m) := by
    intro q m q' m' hd hd' hle hne
    have hs := (hpos.2 q m hd).2 (X q' m') ⟨(hpos.2 q' m' hd').1.1, hle⟩ hne
    have h1 := (hu (X q' m') (hpos.2 q' m' hd').1.1 (X q m) (hpos.2 q m hd).1.1).not.mp hs.2
    push Not at h1
    exact h1
  have hform : ∀ t m : ℝ, 0 < t → 0 < m → 4 / t ≤ m / 2 → 4 * t ^ 2 ≤ m / 2 →
      X ![1, t] m = qlAgg ![1, t] m := by
    intro t m ht hm h1 h2
    have hd : PWDomain ![1, t] m := ⟨by intro l; fin_cases l <;> simp [ht], hm⟩
    rw [hX, exercise_4_C_11a hx1 hx2 hd (by simpa using h1) (by simpa using h2)]
    rfl
  have hstep : ∀ t m t' m' : ℝ, 0 < t → 0 < m → 0 < t' → 0 < m' → 4 / t' ≤ m' / 2 →
      4 * t' ^ 2 ≤ m' / 2 → ![1, t] ⬝ᵥ qlAgg ![1, t'] m' ≤ m →
      u (X ![1, t'] m') ≤ u (X ![1, t] m) := by
    intro t m t' m' ht hm ht' hm' h1 h2 hc
    have hd : PWDomain ![1, t] m := ⟨by intro l; fin_cases l <;> simp [ht], hm⟩
    have hd' : PWDomain ![1, t'] m' := ⟨by intro l; fin_cases l <;> simp [ht'], hm'⟩
    rw [← hform t' m' ht' hm' h1 h2] at hc
    exact (hdem _ _ hd).2 _ ⟨(hdem _ _ hd').1.1, hc⟩
  -- the chain of revealed preferences
  have h1 := hstep (1) (10) (101/100) (20097/2000) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [qlAgg, dotProduct_two])
  have h2 := hstep (101/100) (20097/2000) (51/50) (25239/2500) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [qlAgg, dotProduct_two])
  have h3 := hstep (51/50) (25239/2500) (103/100) (101413/10000) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [qlAgg, dotProduct_two])
  have h4 := hstep (103/100) (101413/10000) (26/25) (6366/625) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [qlAgg, dotProduct_two])
  have h5 := hstep (26/25) (6366/625) (21/20) (20457/2000) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [qlAgg, dotProduct_two])
  have h6 := hstep (21/20) (20457/2000) (53/50) (102701/10000) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [qlAgg, dotProduct_two])
  have h7 := hstep (53/50) (102701/10000) (107/100) (6444/625) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [qlAgg, dotProduct_two])
  have h8 := hstep (107/100) (6444/625) (27/25) (51747/5000) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [qlAgg, dotProduct_two])
  have h9 := hstep (27/25) (51747/5000) (109/100) (103871/10000) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [qlAgg, dotProduct_two])
  have h10 := hstep (109/100) (103871/10000) (11/10) (20847/2000) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [qlAgg, dotProduct_two])
  have h11 := hstep (11/10) (20847/2000) (111/100) (52293/5000) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [qlAgg, dotProduct_two])
  have h12 := hstep (111/100) (52293/5000) (28/25) (4197/400) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [qlAgg, dotProduct_two])
  -- the first step is strict
  have hs1 : u (X ![1, 101 / 100] (20097 / 2000)) < u (X ![1, 1] 10) := by
    have e0 := hform 1 10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have e1 := hform (101 / 100) (20097 / 2000) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
    apply hstrict _ _ _ _ ⟨by intro l; fin_cases l <;> simp, by norm_num⟩
      ⟨by intro l; fin_cases l <;> simp, by norm_num⟩
    · rw [e1]; norm_num [qlAgg, dotProduct_two]
    · rw [e0, e1]
      intro h
      have := congrFun h 0
      norm_num [qlAgg] at this
  -- optimal redistribution at `(p₁₂, w₁₂)`
  have hd12 : PWDomain ![1, 28 / 25] (4197 / 400) := ⟨by intro l; fin_cases l <;> simp, by norm_num⟩
  have hd0 : PWDomain ![1, 1] 10 := ⟨by intro l; fin_cases l <;> simp, by norm_num⟩
  have hdh : ∀ m : ℝ, 0 < m → PWDomain ![1, 28 / 25] m :=
    fun m hm => ⟨by intro l; fin_cases l <;> simp, hm⟩
  have hdh0 : PWDomain ![1, 1] (1 / 2 * 10) := ⟨by intro l; fin_cases l <;> simp, by norm_num⟩
  -- each consumer's utility at `x̄` is `9`
  have hu1 : indirectUtility ql1 ![1, 1] (1 / 2 * 10) = 9 := by
    rw [indirectUtility_eq_of_mem (hx1 _ _ hdh0)]
    have e := (exercise_4_C_11a_consumer1 hdh0.1 (W := 1 / 2 * 10)).1 (by norm_num)
    have hm := hx1 _ _ hdh0
    rw [e, Set.mem_singleton_iff] at hm
    rw [hm]
    simp only [ql1, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [ql_sqrt_eq (b := 2) (by norm_num) (by norm_num)]
    norm_num
  have hu2 : indirectUtility ql2 ![1, 1] (1 / 2 * 10) = 9 := by
    rw [indirectUtility_eq_of_mem (hx2 _ _ hdh0)]
    have e := (exercise_4_C_11a_consumer2 hdh0.1 (W := 1 / 2 * 10)).1 (by norm_num)
    have hm := hx2 _ _ hdh0
    rw [e, Set.mem_singleton_iff] at hm
    rw [hm]
    simp only [ql2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [ql_sqrt_eq (b := 2) (by norm_num) (by norm_num)]
    norm_num
  -- the Hicksian bundles at `p₁₂ = (1, 28/25)` reach utility `9` at cost `38/7` and `3164/625`
  have hv1 : 9 ≤ indirectUtility ql1 ![1, 28 / 25] (38 / 7) := by
    rw [indirectUtility_eq_of_mem (hx1 _ _ (hdh _ (by norm_num)))]
    have hy : (![13 / 7, 625 / 196] : Fin 2 → ℝ) ∈ budgetSet ![1, 28 / 25] (38 / 7) := by
      refine ⟨fun l => by fin_cases l <;> norm_num, ?_⟩
      rw [dotProduct_two]; norm_num
    have := (hx1 _ _ (hdh _ (by norm_num))).2 _ hy
    refine le_trans (le_of_eq ?_) this
    simp only [ql1, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [ql_sqrt_eq (b := 25 / 14) (by norm_num) (by norm_num)]
    norm_num
  have hv2 : 9 ≤ indirectUtility ql2 ![1, 28 / 25] (3164 / 625) := by
    rw [indirectUtility_eq_of_mem (hx2 _ _ (hdh _ (by norm_num)))]
    have hy : (![3136 / 625, 1 / 25] : Fin 2 → ℝ) ∈ budgetSet ![1, 28 / 25] (3164 / 625) := by
      refine ⟨fun l => by fin_cases l <;> norm_num, ?_⟩
      rw [dotProduct_two]; norm_num
    have := (hx2 _ _ (hdh _ (by norm_num))).2 _ hy
    refine le_trans (le_of_eq ?_) this
    simp only [ql2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [ql_sqrt_eq (b := 56 / 25) (by norm_num) (by norm_num)]
    norm_num
  have hfin : u (X ![1, 1] 10) ≤ u (X ![1, 28 / 25] (4197 / 400)) := by
    rw [← indirectUtility_eq_of_mem (hdem _ _ hd0), ← indirectUtility_eq_of_mem (hdem _ _ hd12),
      hv _ _ hd0, hv _ _ hd12]
    unfold socialIndirectUtility
    have hfeas : FeasibleDistribution (4197 / 400) (![38 / 7, 3164 / 625] : Fin 2 → ℝ) := by
      refine ⟨fun i => by fin_cases i <;> norm_num, ?_⟩
      rw [Fin.sum_univ_two]; norm_num
    refine le_trans (hWm fun i => ?_) ((hopt _ _ hd12).2 _ hfeas)
    fin_cases i
    · simp only [shareRule, Fin.zero_eta, Matrix.cons_val_zero]
      rw [hu1]; exact hv1
    · simp only [shareRule, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      rw [hu2]; exact hv2
  linarith [h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, hs1, hfin]

end MWG.AggregateDemand
