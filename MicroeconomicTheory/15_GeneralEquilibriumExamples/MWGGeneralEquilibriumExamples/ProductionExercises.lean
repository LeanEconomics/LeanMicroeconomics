/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGGeneralEquilibriumExamples.TwoByTwo
import MWGGeneralEquilibriumExamples.RobinsonExercises
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-!
# Exercises 15.D.7 and 15.D.9 (MWG p. 544)

* **Exercise 15.D.7**: `f₁ = 2√z₁₁ + √z₂₁`, `f₂ = √z₁₂ + 2√z₂₂`, `p = (1, 1)`, endowment
  `z̄ ≫ 0`. The unique equilibrium is `z₁ = (4z̄₁/5, z̄₂/5)`, `z₂ = (z̄₁/5, 4z̄₂/5)`,
  `w = (√5/(2√z̄₁), √5/(2√z̄₂))` (`exercise_15_D_7`); the same allocation is the unique solution
  of the revenue maximization problem (15.D.5) (`exercise_15_D_7_revenue`) and satisfies the
  first-order conditions (15.D.1)-(15.D.2), from which `factorEqm_iff_foc` recovers the equilibrium
  (`exercise_15_D_7_foc`).
* **Exercise 15.D.9** (Heckscher-Ohlin): as printed the claim is false: with linear (homogeneous,
  concave, increasing) utilities demand is not unique, and in a Leontief world with nonspecialized
  countries the factor-1-abundant country can import good 1 (`exercise_15_D_9_counterexample`).
  It holds when the countries' consumption vectors are proportional, e.g. when demand is
  unique (`exercise_15_D_9`, `exercise_15_D_9_unique_demand`).
-/

namespace MWG.GeneralEquilibriumExamples

open MWG.ConsumerChoice MWG.ClassicalDemand

/-! ### Exercise 15.D.7 -/

/-- **Exercise 15.D.7** (MWG, p. 544). The production functions `f₁(z) = 2√z₁ + √z₂` and
`f₂(z) = √z₁ + 2√z₂`, written `k₁₁√z₁ + k₂₁√z₂` with coefficients `k`. -/
noncomputable def ex15D7f : Fin 2 → (Fin 2 → ℝ) → ℝ :=
  fun j z => ![![2, 1], ![1, 2]] j 0 * Real.sqrt (z 0) + ![![2, 1], ![1, 2]] j 1 * Real.sqrt (z 1)

/-- The coefficients `k` of Exercise 15.D.7. -/
def ex15D7k : Fin 2 → Fin 2 → ℝ := ![![2, 1], ![1, 2]]

theorem ex15D7k_pos (j l : Fin 2) : 0 < ex15D7k j l := by
  fin_cases j <;> fin_cases l <;> norm_num [ex15D7k]

/-- Profit maximization in Exercise 15.D.7: at `w ≫ 0` (output price 1) firm `j` demands exactly
`z_ℓ = k_{jℓ}²/(4w_ℓ²)`. -/
theorem ex15D7_optimal_iff {w : Fin 2 → ℝ} (hw : StrictlyPositive w) (j : Fin 2)
    (z : Fin 2 → ℝ) : IsOptimalInput ex15D7f ![1, 1] w j z ↔
      z = fun l => ex15D7k j l ^ 2 / (4 * w l ^ 2) := by
  have hk := ex15D7k_pos j
  set zs : Fin 2 → ℝ := fun l => ex15D7k j l ^ 2 / (4 * w l ^ 2) with hzs
  have hone : (![1, 1] : Fin 2 → ℝ) j = 1 := by fin_cases j <;> rfl
  have hprof : ∀ v ∈ nonnegOrthant 2, (![1, 1] : Fin 2 → ℝ) j * ex15D7f j v - w ⬝ᵥ v =
      (ex15D7k j 0 * Real.sqrt (v 0) - w 0 * v 0) +
        (ex15D7k j 1 * Real.sqrt (v 1) - w 1 * v 1) := by
    intro v _
    rw [hone]
    simp only [ex15D7f, ex15D7k, dotProduct, Fin.sum_univ_two, one_mul]
    ring
  have hzsm : zs ∈ nonnegOrthant 2 := fun l => by simp only [hzs]; positivity
  have hb : ∀ l, ∀ v : ℝ, 0 ≤ v → ex15D7k j l * Real.sqrt v - w l * v ≤
      ex15D7k j l ^ 2 / (4 * w l) ∧
      (ex15D7k j l * Real.sqrt v - w l * v = ex15D7k j l ^ 2 / (4 * w l) ↔ v = zs l) :=
    fun l v hv => sqrt_firm_profit (hk l) (hw l) hv
  have hzsval : (![1, 1] : Fin 2 → ℝ) j * ex15D7f j zs - w ⬝ᵥ zs =
      ex15D7k j 0 ^ 2 / (4 * w 0) + ex15D7k j 1 ^ 2 / (4 * w 1) := by
    rw [hprof zs hzsm, ((hb 0 _ (hzsm 0)).2).2 rfl, ((hb 1 _ (hzsm 1)).2).2 rfl]
  constructor
  · rintro ⟨hz, hopt⟩
    have h1 := hopt zs hzsm
    rw [hprof z hz, hzsval] at h1
    have b0 := (hb 0 _ (hz 0)).1
    have b1 := (hb 1 _ (hz 1)).1
    funext l
    fin_cases l
    · exact ((hb 0 _ (hz 0)).2).1 (by linarith)
    · exact ((hb 1 _ (hz 1)).2).1 (by linarith)
  · rintro rfl
    refine ⟨hzsm, fun v hv => ?_⟩
    rw [hprof v hv, hzsval]
    linarith [(hb 0 _ (hv 0)).1, (hb 1 _ (hv 1)).1]

/-- **Exercise 15.D.7** (MWG, p. 544). The equilibrium factor allocation. -/
noncomputable def ex15D7alloc (zbar : Fin 2 → ℝ) : Fin 2 → Fin 2 → ℝ :=
  ![![4 * zbar 0 / 5, zbar 1 / 5], ![zbar 0 / 5, 4 * zbar 1 / 5]]

/-- **Exercise 15.D.7** (MWG, p. 544). The equilibrium factor prices. -/
noncomputable def ex15D7w (zbar : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![Real.sqrt 5 / (2 * Real.sqrt (zbar 0)), Real.sqrt 5 / (2 * Real.sqrt (zbar 1))]

/-- **Exercise 15.D.7** (MWG, p. 544). For `z̄ ≫ 0` and `p = (1, 1)` the unique factor market
equilibrium is `z₁* = (4z̄₁/5, z̄₂/5)`, `z₂* = (z̄₁/5, 4z̄₂/5)` with
`w* = (√5/(2√z̄₁), √5/(2√z̄₂))`. -/
theorem exercise_15_D_7 {zbar : Fin 2 → ℝ} (hz : StrictlyPositive zbar) (w : Fin 2 → ℝ)
    (z : Fin 2 → Fin 2 → ℝ) :
    IsFactorEqm ex15D7f ![1, 1] zbar w z ↔ w = ex15D7w zbar ∧ z = ex15D7alloc zbar := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs : ∀ l, Real.sqrt (zbar l) ^ 2 = zbar l := fun l => Real.sq_sqrt (hz l).le
  have hspos : ∀ l, 0 < Real.sqrt (zbar l) := fun l => Real.sqrt_pos.2 (hz l)
  have hwpos : StrictlyPositive (ex15D7w zbar) := fun l => by
    have h5p : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
    fin_cases l
    · exact div_pos h5p (mul_pos two_pos (hspos 0))
    · exact div_pos h5p (mul_pos two_pos (hspos 1))
  have hwsq : ∀ l, 4 * ex15D7w zbar l ^ 2 = 5 / zbar l := by
    intro l
    fin_cases l <;> simp only [ex15D7w, Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
      Matrix.cons_val_one] <;> (rw [div_pow, mul_pow, h5, hs]; field_simp; ring)
  constructor
  · rintro ⟨hw, hopt, hsum⟩
    have hz' : ∀ j, z j = fun l => ex15D7k j l ^ 2 / (4 * w l ^ 2) := fun j =>
      (ex15D7_optimal_iff hw j (z j)).1 (hopt j)
    -- market clearing gives `4 w_ℓ² = 5/z̄_ℓ`
    have hclear : ∀ l, 4 * w l ^ 2 = 5 / zbar l := by
      intro l
      have := congrFun hsum l
      rw [Finset.sum_apply, Fin.sum_univ_two, hz' 0, hz' 1] at this
      have hwl := hw l
      have hk : ex15D7k 0 l ^ 2 + ex15D7k 1 l ^ 2 = 5 := by
        fin_cases l <;> norm_num [ex15D7k]
      simp only at this
      rw [← add_div, hk] at this
      rw [eq_div_iff (hz l).ne', ← this]
      field_simp
    have hweq : w = ex15D7w zbar := by
      funext l
      have h1 := hclear l
      have h2 := hwsq l
      have hwl := hw l
      have hwl' := hwpos l
      nlinarith [sq_nonneg (w l - ex15D7w zbar l), sq_nonneg (w l + ex15D7w zbar l)]
    refine ⟨hweq, ?_⟩
    funext j l
    rw [hz' j, hweq]
    simp only
    rw [hwsq l]
    fin_cases j <;> fin_cases l <;> simp [ex15D7alloc, ex15D7k] <;> field_simp <;> ring
  · rintro ⟨rfl, rfl⟩
    refine ⟨hwpos, fun j => (ex15D7_optimal_iff hwpos j _).2 ?_, ?_⟩
    · funext l
      rw [hwsq l]
      fin_cases j <;> fin_cases l <;> simp [ex15D7alloc, ex15D7k] <;> field_simp <;> ring
    · funext l
      fin_cases l <;> simp [ex15D7alloc, Fin.sum_univ_two] <;> ring

/-- The Cauchy-Schwarz step of (15.D.5): `2√a + √b ≤ √5 √(a + b)`, with equality only if
`a = 4b`. -/
theorem two_sqrt_add_sqrt_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    2 * Real.sqrt a + Real.sqrt b ≤ Real.sqrt 5 * Real.sqrt (a + b) ∧
      (2 * Real.sqrt a + Real.sqrt b = Real.sqrt 5 * Real.sqrt (a + b) → a = 4 * b) := by
  have h5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have hsa := Real.sq_sqrt ha
  have hsb := Real.sq_sqrt hb
  have hsab := Real.sq_sqrt (add_nonneg ha hb)
  have n5 := Real.sqrt_nonneg 5
  have na := Real.sqrt_nonneg a
  have nb := Real.sqrt_nonneg b
  have nab := Real.sqrt_nonneg (a + b)
  have hsq : (Real.sqrt 5 * Real.sqrt (a + b)) ^ 2 - (2 * Real.sqrt a + Real.sqrt b) ^ 2 =
      (Real.sqrt a - 2 * Real.sqrt b) ^ 2 := by
    rw [mul_pow, h5, hsab]
    nlinarith [hsa, hsb]
  constructor
  · nlinarith [sq_nonneg (Real.sqrt a - 2 * Real.sqrt b), mul_nonneg n5 nab]
  · intro heq
    have h0 : (Real.sqrt a - 2 * Real.sqrt b) ^ 2 = 0 := by rw [← hsq, heq]; ring
    have h1 : Real.sqrt a = 2 * Real.sqrt b := by
      nlinarith [sq_nonneg (Real.sqrt a - 2 * Real.sqrt b)]
    rw [← hsa, ← hsb, h1]
    ring

/-- **Exercise 15.D.7** (MWG, p. 544), via (15.D.5): `z*` maximizes revenue `∑ⱼ fⱼ(zⱼ)` among
the allocations of `z̄`, and it is the only maximizer. -/
theorem exercise_15_D_7_revenue {zbar : Fin 2 → ℝ} (hz : StrictlyPositive zbar)
    {z : Fin 2 → Fin 2 → ℝ} (hzm : ∀ j, z j ∈ nonnegOrthant 2) (hsum : ∑ j, z j = zbar) :
    ∑ j, (1 : ℝ) * ex15D7f j (z j) ≤ ∑ j, (1 : ℝ) * ex15D7f j (ex15D7alloc zbar j) ∧
      (∑ j, (1 : ℝ) * ex15D7f j (z j) = ∑ j, (1 : ℝ) * ex15D7f j (ex15D7alloc zbar j) →
        z = ex15D7alloc zbar) := by
  have heqm := (exercise_15_D_7 hz _ _).2 ⟨rfl, rfl⟩
  have hle := factorEqm_revenue_max (p := ![1, 1]) heqm hzm hsum
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hle ⊢
  refine ⟨hle, fun heq => ?_⟩
  have s0 := congrFun hsum 0
  have s1 := congrFun hsum 1
  simp only [Finset.sum_apply, Fin.sum_univ_two] at s0 s1
  obtain ⟨c0, e0⟩ := two_sqrt_add_sqrt_le (hzm 0 0) (hzm 1 0)
  obtain ⟨c1, e1⟩ := two_sqrt_add_sqrt_le (hzm 1 1) (hzm 0 1)
  -- the value at `z*` is `√5(√z̄₁ + √z̄₂)`
  have hval : (1 : ℝ) * ex15D7f 0 (ex15D7alloc zbar 0) + 1 * ex15D7f 1 (ex15D7alloc zbar 1) =
      Real.sqrt 5 * Real.sqrt (zbar 0) + Real.sqrt 5 * Real.sqrt (zbar 1) := by
    have k0 : Real.sqrt (4 * zbar 0 / 5) = 2 * Real.sqrt (zbar 0 / 5) := by
      rw [show 4 * zbar 0 / 5 = 2 ^ 2 * (zbar 0 / 5) by ring, Real.sqrt_mul (by norm_num),
        Real.sqrt_sq (by norm_num)]
    have k1 : Real.sqrt (4 * zbar 1 / 5) = 2 * Real.sqrt (zbar 1 / 5) := by
      rw [show 4 * zbar 1 / 5 = 2 ^ 2 * (zbar 1 / 5) by ring, Real.sqrt_mul (by norm_num),
        Real.sqrt_sq (by norm_num)]
    have m0 : Real.sqrt 5 * Real.sqrt (zbar 0) = 5 * Real.sqrt (zbar 0 / 5) := by
      rw [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 5)]
      have : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
      field_simp
      rw [Real.sq_sqrt (by norm_num)]
      ring
    have m1 : Real.sqrt 5 * Real.sqrt (zbar 1) = 5 * Real.sqrt (zbar 1 / 5) := by
      rw [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 5)]
      have : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
      field_simp
      rw [Real.sq_sqrt (by norm_num)]
      ring
    simp only [ex15D7f, ex15D7alloc, Matrix.cons_val_zero, Matrix.cons_val_one, one_mul]
    rw [k0, k1, m0, m1]
    ring
  rw [hval] at heq
  have hv : ex15D7f 0 (z 0) + ex15D7f 1 (z 1) = (2 * Real.sqrt (z 0 0) + Real.sqrt (z 1 0)) +
      (2 * Real.sqrt (z 1 1) + Real.sqrt (z 0 1)) := by
    simp only [ex15D7f, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  simp only [one_mul] at heq
  rw [hv] at heq
  rw [s0] at c0 e0
  rw [add_comm (z 1 1), s1] at c1 e1
  have q0 := e0 (by linarith)
  have q1 := e1 (by linarith)
  funext j l
  fin_cases j <;> fin_cases l <;> simp [ex15D7alloc] <;> linarith

/-- A function `k₁√z₁ + k₂√z₂` (`k ≥ 0`) is concave on `ℝ²₊`. -/
theorem concaveOn_sqrt_sum {k0 k1 : ℝ} (hk0 : 0 ≤ k0) (hk1 : 0 ≤ k1) :
    ConcaveOn ℝ (nonnegOrthant 2) (fun z => k0 * Real.sqrt (z 0) + k1 * Real.sqrt (z 1)) := by
  refine ⟨convex_nonnegOrthant 2, fun x hx y hy a b ha hb hab => ?_⟩
  have h := Real.strictConcaveOn_sqrt.concaveOn.2
  have h0 := h (Set.mem_Ici.2 (hx 0)) (Set.mem_Ici.2 (hy 0)) ha hb hab
  have h1 := h (Set.mem_Ici.2 (hx 1)) (Set.mem_Ici.2 (hy 1)) ha hb hab
  simp only [smul_eq_mul] at h0 h1 ⊢
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  nlinarith [mul_le_mul_of_nonneg_left h0 hk0, mul_le_mul_of_nonneg_left h1 hk1]

/-- The derivative of `k₁√z₁ + k₂√z₂` at `(z₁, z₂)`. -/
noncomputable def sqrtSumDeriv (k0 k1 z0 z1 : ℝ) : (Fin 2 → ℝ) →L[ℝ] ℝ :=
  k0 • ((1 / (2 * Real.sqrt z0)) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ)
    (0 : Fin 2)) + k1 • ((1 / (2 * Real.sqrt z1)) •
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) (1 : Fin 2))

/-- The derivative of `k₁√z₁ + k₂√z₂` at `z ≫ 0`. -/
theorem hasFDerivAt_sqrt_sum (k0 k1 : ℝ) {z : Fin 2 → ℝ} (h0 : 0 < z 0) (h1 : 0 < z 1) :
    HasFDerivAt (fun z : Fin 2 → ℝ => k0 * Real.sqrt (z 0) + k1 * Real.sqrt (z 1))
      (sqrtSumDeriv k0 k1 (z 0) (z 1)) z := by
  have d0 := (Real.hasDerivAt_sqrt h0.ne').comp_hasFDerivAt z
    (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) z)
  have d1 := (Real.hasDerivAt_sqrt h1.ne').comp_hasFDerivAt z
    (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) z)
  exact (d0.const_mul k0).add (d1.const_mul k1)

/-- **Exercise 15.D.7** (MWG, p. 544), via (15.D.1)-(15.D.2): the production functions are concave
and differentiable at the interior allocation `z*`, where `pⱼ ∂fⱼ/∂z_{ℓj} = w*_ℓ`; by
`factorEqm_iff_foc` this recovers the equilibrium. -/
theorem exercise_15_D_7_foc {zbar : Fin 2 → ℝ} (hz : StrictlyPositive zbar) :
    (∀ j l, (![1, 1] : Fin 2 → ℝ) j * sqrtSumDeriv (ex15D7k j 0) (ex15D7k j 1)
      (ex15D7alloc zbar j 0) (ex15D7alloc zbar j 1) (Pi.single l 1) = ex15D7w zbar l) ∧
      IsFactorEqm ex15D7f ![1, 1] zbar (ex15D7w zbar) (ex15D7alloc zbar) := by
  have hint : ∀ j l, 0 < ex15D7alloc zbar j l := fun j l => by
    fin_cases j <;> fin_cases l <;> simp [ex15D7alloc] <;> linarith [hz 0, hz 1]
  have hwpos : StrictlyPositive (ex15D7w zbar) := fun l => by
    have h5p : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
    fin_cases l
    · exact div_pos h5p (mul_pos two_pos (Real.sqrt_pos.2 (hz 0)))
    · exact div_pos h5p (mul_pos two_pos (Real.sqrt_pos.2 (hz 1)))
  have h5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  -- the first-order conditions, checked by comparing squares of positive numbers
  have hfoc : ∀ j l, (![1, 1] : Fin 2 → ℝ) j * sqrtSumDeriv (ex15D7k j 0) (ex15D7k j 1)
      (ex15D7alloc zbar j 0) (ex15D7alloc zbar j 1) (Pi.single l 1) = ex15D7w zbar l := by
    intro j l
    have hsj := Real.sq_sqrt (hint j l).le
    have hsjp := Real.sqrt_pos.2 (hint j l)
    have hsz := Real.sq_sqrt (hz l).le
    have hszp := Real.sqrt_pos.2 (hz l)
    have hlhs : (![1, 1] : Fin 2 → ℝ) j * sqrtSumDeriv (ex15D7k j 0) (ex15D7k j 1)
        (ex15D7alloc zbar j 0) (ex15D7alloc zbar j 1) (Pi.single l 1) =
        ex15D7k j l / (2 * Real.sqrt (ex15D7alloc zbar j l)) := by
      fin_cases j <;> fin_cases l <;> simp [ex15D7k, sqrtSumDeriv] <;> ring
    rw [hlhs]
    have hkpos := ex15D7k_pos j l
    have hpos1 : 0 < ex15D7k j l / (2 * Real.sqrt (ex15D7alloc zbar j l)) := by positivity
    have hpos2 := hwpos l
    have hsq : (ex15D7k j l / (2 * Real.sqrt (ex15D7alloc zbar j l))) ^ 2 =
        ex15D7w zbar l ^ 2 := by
      rw [div_pow, mul_pow, hsj]
      fin_cases j <;> fin_cases l <;>
        simp [ex15D7k, ex15D7alloc, ex15D7w, div_pow, mul_pow, h5,
          Real.sq_sqrt (hz 0).le, Real.sq_sqrt (hz 1).le] <;>
        field_simp <;> ring
    nlinarith [sq_nonneg (ex15D7k j l / (2 * Real.sqrt (ex15D7alloc zbar j l)) - ex15D7w zbar l)]
  refine ⟨hfoc, (factorEqm_iff_foc (fun j => ?_) (fun j => by fin_cases j <;> norm_num) hwpos
    hint (fun j => ?_)).2 ⟨hfoc, ?_⟩⟩
  · exact concaveOn_sqrt_sum (ex15D7k_pos j 0).le (ex15D7k_pos j 1).le
  · exact hasFDerivAt_sqrt_sum _ _ (hint j 0) (hint j 1)
  · funext l
    fin_cases l <;> simp [ex15D7alloc, Fin.sum_univ_two] <;> ring

/-! ### Exercise 15.D.9: the Heckscher-Ohlin theorem -/

/-- With common unit input vectors `a`, endowment ratios and output ratios are ordered alike:
`z^A₁z^B₂ - z^B₁z^A₂ = |A|(q^A₁q^B₂ - q^A₂q^B₁)` for `z^k = ∑ⱼ q^k_j aⱼ`. -/
theorem endowment_output_identity (a : Fin 2 → Fin 2 → ℝ) (qA qB : Fin 2 → ℝ) :
    (qA 0 * a 0 0 + qA 1 * a 1 0) * (qB 0 * a 0 1 + qB 1 * a 1 1) -
      (qB 0 * a 0 0 + qB 1 * a 1 0) * (qA 0 * a 0 1 + qA 1 * a 1 1) =
    (a 0 0 * a 1 1 - a 1 0 * a 0 1) * (qA 0 * qB 1 - qA 1 * qB 0) := by
  ring

/-- **Exercise 15.D.9** (Heckscher-Ohlin; MWG, p. 544), corrected form. Two countries share the
2 × 2 technologies (with factor intensity), face output prices `p`, and are both diversified
(`qᵏ ≫ 0`, `c(wᵏ) = p`, `∑ⱼ qᵏⱼ aⱼ(wᵏ) = z̄ᵏ`); country A is relatively abundant in factor 1.
If the countries' consumption vectors are proportional (`xᵏ = λₖ d`; this is what identical
homothetic preferences give when demand is unique), each country's spending equals its income
`p·xᵏ = p·qᵏ`, and world markets clear, then country A exports good 1: `x^A₁ < q^A₁`. -/
theorem exercise_15_D_9 {M : TwoByTwo} (hM : M.IsModel) (hFI : M.FactorIntensity)
    {p wA wB zA zB qA qB xA xB d : Fin 2 → ℝ} (hwA : StrictlyPositive wA)
    (hwB : StrictlyPositive wB) (hcA : ∀ j, M.c j wA = p j) (hcB : ∀ j, M.c j wB = p j)
    (hqA : ∀ j, 0 < qA j) (hqB : ∀ j, 0 < qB j) (hzA : ∑ j, qA j • M.a j wA = zA)
    (hzB : ∑ j, qB j • M.a j wB = zB) (habund : zB 0 / zB 1 < zA 0 / zA 1) {lA lB : ℝ}
    (hlA : 0 < lA) (hlB : 0 < lB) (hxA : xA = lA • d) (hxB : xB = lB • d)
    (hbud : p ⬝ᵥ xA = p ⬝ᵥ qA) (hclear : xA + xB = qA + qB) : xA 0 < qA 0 := by
  have hww : wA = wB := TwoByTwo.factor_price_equalization hM hFI hwA hwB hcA
    (fun j => (hcB j))
  subst hww
  have hdet := hFI.det_pos hM hwA
  have a00 := hM.a_pos 0 wA 0 hwA
  have a01 := hM.a_pos 0 wA 1 hwA
  have a10 := hM.a_pos 1 wA 0 hwA
  have a11 := hM.a_pos 1 wA 1 hwA
  have zA0 := congrFun hzA 0
  have zA1 := congrFun hzA 1
  have zB0 := congrFun hzB 0
  have zB1 := congrFun hzB 1
  simp only [Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at zA0 zA1 zB0 zB1
  have hzA1 : 0 < zA 1 := by rw [← zA1]; nlinarith [hqA 0, hqA 1]
  have hzB1 : 0 < zB 1 := by rw [← zB1]; nlinarith [hqB 0, hqB 1]
  rw [div_lt_div_iff₀ hzB1 hzA1] at habund
  -- output ratios inherit the ordering
  have hq : qA 1 * qB 0 < qA 0 * qB 1 := by
    have := endowment_output_identity (fun j => M.a j wA) qA qB
    rw [zA0, zA1, zB0, zB1] at this
    nlinarith
  -- consumption is the share `s = lA/(lA + lB)` of world output
  have hp0 : 0 < p 0 := by rw [← hcA 0]; exact TwoByTwo.c_pos hM 0 hwA
  have hp1 : 0 < p 1 := by rw [← hcA 1]; exact TwoByTwo.c_pos hM 1 hwA
  have hc0 := congrFun hclear 0
  have hc1 := congrFun hclear 1
  rw [hxA, hxB] at hc0 hc1
  rw [hxA] at hbud
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hc0 hc1
  simp only [TwoByTwo.dot_two, Pi.smul_apply, smul_eq_mul] at hbud
  rw [hxA]
  simp only [Pi.smul_apply, smul_eq_mul]
  by_contra hge
  rw [not_lt] at hge
  -- then good 2 is consumed at most as produced, and the output ratios would be reversed
  have h1 : lA * d 1 ≤ qA 1 := by nlinarith
  have hd0 : (lA + lB) * d 0 = qA 0 + qB 0 := by linarith
  have hd1 : (lA + lB) * d 1 = qA 1 + qB 1 := by linarith
  have e0 : lB * qA 0 ≤ lA * qB 0 := by nlinarith
  have e1 : lA * qB 1 ≤ lB * qA 1 := by nlinarith
  have f0 := mul_le_mul_of_nonneg_right e0 (hqB 1).le
  have f1 := mul_le_mul_of_nonneg_right e1 (hqB 0).le
  have f2 := mul_lt_mul_of_pos_left hq hlB
  nlinarith

/-- Demand of a utility homogeneous of degree `r > 0` scales with wealth: if `x` is demanded at
`(p, I)` then `t x` is demanded at `(p, t I)`, `t > 0`. -/
theorem homogeneous_demand_scale {L : ℕ} {u : (Fin L → ℝ) → ℝ} {r : ℝ}
    (hu : ∀ x ∈ nonnegOrthant L, ∀ t : ℝ, 0 < t → u (t • x) = t ^ r * u x) {p : Fin L → ℝ}
    {I t : ℝ} (ht : 0 < t) {x : Fin L → ℝ} (hx : x ∈ walrasianDemand u p I) :
    t • x ∈ walrasianDemand u p (t * I) := by
  have htr : 0 < t ^ r := Real.rpow_pos_of_pos ht r
  refine ⟨⟨fun l => by simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg ht.le (hx.1.1 l),
    ?_⟩, fun y hy => ?_⟩
  · rw [dotProduct_smul, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left hx.1.2 ht.le
  · have hy' : t⁻¹ • y ∈ budgetSet p I := by
      refine ⟨fun l => by
        simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg (inv_nonneg.2 ht.le) (hy.1 l), ?_⟩
      rw [dotProduct_smul, smul_eq_mul]
      have := hy.2
      rw [inv_mul_le_iff₀ ht]
      exact this
    have h1 := hx.2 _ hy'
    have h2 := hu _ hy'.1 t ht
    rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul] at h2
    rw [h2, hu x hx.1.1 t ht]
    exact mul_le_mul_of_nonneg_left h1 htr.le

/-- **Exercise 15.D.9** (MWG, p. 544), with identical preferences represented by a utility that is
homogeneous of degree `r > 0` and has a unique demand (e.g. strictly quasiconcave), the
Heckscher-Ohlin conclusion holds. -/
theorem exercise_15_D_9_unique_demand {M : TwoByTwo} (hM : M.IsModel)
    (hFI : M.FactorIntensity) {p wA wB zA zB qA qB xA xB : Fin 2 → ℝ}
    (hwA : StrictlyPositive wA) (hwB : StrictlyPositive wB) (hcA : ∀ j, M.c j wA = p j)
    (hcB : ∀ j, M.c j wB = p j) (hqA : ∀ j, 0 < qA j) (hqB : ∀ j, 0 < qB j)
    (hzA : ∑ j, qA j • M.a j wA = zA) (hzB : ∑ j, qB j • M.a j wB = zB)
    (habund : zB 0 / zB 1 < zA 0 / zA 1) {u : (Fin 2 → ℝ) → ℝ} {r : ℝ}
    (hu : ∀ x ∈ nonnegOrthant 2, ∀ t : ℝ, 0 < t → u (t • x) = t ^ r * u x)
    (huniq : ∀ I, (walrasianDemand u p I).Subsingleton)
    (hxA : xA ∈ walrasianDemand u p (p ⬝ᵥ qA)) (hxB : xB ∈ walrasianDemand u p (p ⬝ᵥ qB))
    (hclear : xA + xB = qA + qB) : xA 0 < qA 0 := by
  have hp : StrictlyPositive p := fun j => by rw [← hcA j]; exact TwoByTwo.c_pos hM j hwA
  have hIA : 0 < p ⬝ᵥ qA := dotProduct_pos_of_strictlyPositive hp (fun j => (hqA j).le)
    (fun h => by have := congrFun h 0; simp at this; linarith [hqA 0])
  have hIB : 0 < p ⬝ᵥ qB := dotProduct_pos_of_strictlyPositive hp (fun j => (hqB j).le)
    (fun h => by have := congrFun h 0; simp at this; linarith [hqB 0])
  set t := p ⬝ᵥ qB / p ⬝ᵥ qA with htd
  have ht : 0 < t := div_pos hIB hIA
  have hscale := homogeneous_demand_scale hu ht hxA
  rw [htd, div_mul_cancel₀ _ hIA.ne'] at hscale
  have hxB' : xB = t • xA := huniq _ hxB hscale
  have hbud : p ⬝ᵥ xA = p ⬝ᵥ qA := by
    -- the demand of a strictly increasing direction exhausts wealth
    have hle := hxA.1.2
    by_contra hne
    have hlt : p ⬝ᵥ xA < p ⬝ᵥ qA := lt_of_le_of_ne hle hne
    -- spending of B is then also below income, so world spending is below world income
    have hltB : p ⬝ᵥ xB < p ⬝ᵥ qB := by
      rw [hxB', dotProduct_smul, smul_eq_mul, htd, div_mul_eq_mul_div, div_lt_iff₀ hIA]
      nlinarith
    have : p ⬝ᵥ (xA + xB) = p ⬝ᵥ (qA + qB) := by rw [hclear]
    rw [dotProduct_add, dotProduct_add] at this
    linarith
  exact exercise_15_D_9 hM hFI hwA hwB hcA hcB hqA hqB hzA hzB habund one_pos ht
    (one_smul ℝ xA).symm hxB' hbud hclear

/-- **Exercise 15.D.9** (MWG, p. 544): the claim as printed is false. In the Leontief model
(factor intensity holds), at `p = (3, 3)`, `w = (1, 1)`, country A with endowment `(5, 4)`
(factor-1 abundant) produces `(2, 1)` and country B with `(4, 5)` produces `(1, 2)`; both are
diversified. Consumers have the linear utility `x₁ + x₂` (homogeneous, concave, increasing), so
any bundle on the budget line is demanded: A consumes `(3, 0)` and B `(0, 3)`, world markets
clear, and country A imports good 1. -/
theorem exercise_15_D_9_counterexample :
    let p : Fin 2 → ℝ := ![3, 3]
    let w : Fin 2 → ℝ := ![1, 1]
    let qA : Fin 2 → ℝ := ![2, 1]
    let qB : Fin 2 → ℝ := ![1, 2]
    let xA : Fin 2 → ℝ := ![3, 0]
    let xB : Fin 2 → ℝ := ![0, 3]
    IsFactorEqm leontiefModel.f p ![5, 4] w (fun j => qA j • leontiefModel.a j w) ∧
      IsFactorEqm leontiefModel.f p ![4, 5] w (fun j => qB j • leontiefModel.a j w) ∧
      (∀ j, 0 < qA j) ∧ (∀ j, 0 < qB j) ∧ (4 : ℝ) / 5 < 5 / 4 ∧
      (∀ x ∈ nonnegOrthant 2, ∀ t : ℝ, 0 < t → linearUtility (t • x) = t * linearUtility x) ∧
      ConcaveOn ℝ (nonnegOrthant 2) linearUtility ∧
      xA ∈ walrasianDemand linearUtility p (p ⬝ᵥ qA) ∧
      xB ∈ walrasianDemand linearUtility p (p ⬝ᵥ qB) ∧ xA + xB = qA + qB ∧ qA 0 < xA 0 := by
  intro p w qA qB xA xB
  have hw : StrictlyPositive w := fun l => by fin_cases l <;> norm_num [w]
  have hc : ∀ j, p j = leontiefModel.c j w := by
    intro j; fin_cases j <;> norm_num [TwoByTwo.c, leontiefModel, TwoByTwo.dot_two, p, w]
  have hdem : ∀ x : Fin 2 → ℝ, x ∈ nonnegOrthant 2 → x 0 + x 1 = 3 →
      x ∈ walrasianDemand linearUtility p 9 := by
    intro x hx hs
    refine ⟨⟨hx, by
      rw [TwoByTwo.dot_two]; simp only [p, Matrix.cons_val_zero, Matrix.cons_val_one]; linarith⟩,
      fun y hy => ?_⟩
    have := hy.2
    simp only [p, TwoByTwo.dot_two, Matrix.cons_val_zero, Matrix.cons_val_one] at this
    simp only [linearUtility]
    linarith
  refine ⟨?_, ?_, fun j => by fin_cases j <;> norm_num [qA],
    fun j => by fin_cases j <;> norm_num [qB], by norm_num, ?_, ?_, ?_, ?_, ?_,
    by norm_num [qA, xA]⟩
  · refine (TwoByTwo.interior_eqm_iff (q := qA) leontiefModel_isModel hw
      (fun j => by fin_cases j <;> norm_num [qA])).2 ⟨hc, ?_⟩
    funext l
    fin_cases l <;> norm_num [leontiefModel, Fin.sum_univ_two, qA]
  · refine (TwoByTwo.interior_eqm_iff (q := qB) leontiefModel_isModel hw
      (fun j => by fin_cases j <;> norm_num [qB])).2 ⟨hc, ?_⟩
    funext l
    fin_cases l <;> norm_num [leontiefModel, Fin.sum_univ_two, qB]
  · intro x _ t _
    simp [linearUtility]
    ring
  · refine ⟨convex_nonnegOrthant 2, fun x _ y _ a b _ _ _ => ?_⟩
    simp [linearUtility]
    ring_nf
    rfl
  · have : p ⬝ᵥ qA = 9 := by norm_num [p, qA, TwoByTwo.dot_two]
    rw [this]
    exact hdem _ (fun l => by fin_cases l <;> norm_num [xA]) (by norm_num [xA])
  · have : p ⬝ᵥ qB = 9 := by norm_num [p, qB, TwoByTwo.dot_two]
    rw [this]
    exact hdem _ (fun l => by fin_cases l <;> norm_num [xB]) (by norm_num [xB])
  · funext l
    fin_cases l <;> norm_num [xA, xB, qA, qB]

end MWG.GeneralEquilibriumExamples

