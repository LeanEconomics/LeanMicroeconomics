/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGProduction.Nonsubstitution

/-!
# Exercises 5.AA.2-5.AA.5 (MWG, pp. 164-166)

* **Exercise 5.AA.2**: (a) in a productive Leontief model with `b ≫ 0` every plan `[I - A; -b]α` is
  efficient; (b) with `α ≫ 0` the supporting prices (wage `1`) are unique, `p = b(I - A)⁻¹`;
  (c) `p = Σ_k bAᵏ`, labour embodied directly and indirectly; (d) prices supporting the whole
  technology are componentwise below those of any other productive selection of techniques.
* **Exercise 5.AA.3**: (a) the production possibility set `4c₁ + 6c₂ ≤ 10`, (b) prices `(4, 6)`,
  (c) labour embodied, (e) the switch of techniques at `β = 4`.
* **Exercise 5.AA.4**: membership of `y₁, …, y₅`, efficiency of `(0, -5, 5, 0)`, inefficiency of
  `a₁`.
* **Exercise 5.AA.5**: (a)-(c) convexity, no free lunch, no free disposal; (d)-(e) inefficient
  activities (correction: `a₃` and `a₈` are both efficient); (f) the efficient set
  `cone(a₃, a₈) ∪ cone(a₇, a₈)`; (g)-(h) the linear program and its solution `412.5`.
-/

namespace MWG.Production

open MWG.ClassicalDemand MWG.ConsumerChoice Filter Topology

variable {n : ℕ}

open Matrix in
/-- For `A ≥ 0` productive, `T = (I - A)⁻¹` satisfies `T(I - A) = I`, `T ≥ 0` and `T_jj ≥ 1`. -/
theorem leontief_inverse_facts {A : Matrix (Fin n) (Fin n) ℝ} (hA : ∀ i j, 0 ≤ A i j)
    (hprod : Productive A) :
    (1 - A)⁻¹ * (1 - A) = 1 ∧ (1 - A) * (1 - A)⁻¹ = 1 ∧ (∀ i j, 0 ≤ (1 - A)⁻¹ i j) ∧
      ∀ j, 1 ≤ (1 - A)⁻¹ j j := by
  obtain ⟨-, hunit, -, hnn, -⟩ := proposition_5_AA_1_neumann hA hprod
  have hdet : IsUnit (1 - A).det := (Matrix.isUnit_iff_isUnit_det _).mp hunit
  have hl := Matrix.nonsing_inv_mul _ hdet
  have hr := Matrix.mul_nonsing_inv _ hdet
  refine ⟨hl, hr, hnn, fun j => ?_⟩
  have hT : (1 - A)⁻¹ = 1 + (1 - A)⁻¹ * A := by
    have := hl
    rw [Matrix.mul_sub, Matrix.mul_one] at this
    exact sub_eq_iff_eq_add.mp this
  have := congrFun (congrFun hT j) j
  rw [this, Matrix.add_apply, Matrix.one_apply_eq, Matrix.mul_apply]
  have : 0 ≤ ∑ k, (1 - A)⁻¹ j k * A k j :=
    Finset.sum_nonneg fun k _ => mul_nonneg (hnn j k) (hA k j)
  linarith

open Matrix in
/-- **Exercise 5.AA.2(a)** (MWG, p. 164). In a Leontief model with no substitution, `A ≥ 0`
productive and `b ≫ 0`, every plan `y = [I - A; -b]α` with `α ≥ 0` is efficient: it maximizes
profits (zero) at the prices `(b(I - A)⁻¹, 1) ≫ 0`. -/
theorem exercise_5_AA_2a {A : Matrix (Fin n) (Fin n) ℝ} (hA : ∀ i j, 0 ≤ A i j)
    (hprod : Productive A) {b : Fin n → ℝ} (hb : StrictlyPositive b) {α : Fin n → ℝ}
    (hα : 0 ≤ α) :
    extendVec ((1 - A) *ᵥ α) (-(b ⬝ᵥ α)) ∈
        supply (leontiefSet A b) (extendVec (b ᵥ* (1 - A)⁻¹) 1) ∧
      Efficient (leontiefSet A b) (extendVec ((1 - A) *ᵥ α) (-(b ⬝ᵥ α))) := by
  obtain ⟨hl, -, hnn, hdiag⟩ := leontief_inverse_facts hA hprod
  set pr := b ᵥ* (1 - A)⁻¹ with hpr
  have hdot : ∀ (u : Fin n → ℝ) (t : ℝ), extendVec pr 1 ⬝ᵥ extendVec u t = pr ⬝ᵥ u + t := by
    intro u t
    simp [extendVec, dotProduct, Fin.sum_univ_castSucc]
  have hzero : ∀ α' : Fin n → ℝ, pr ⬝ᵥ ((1 - A) *ᵥ α') = b ⬝ᵥ α' := by
    intro α'
    rw [Matrix.dotProduct_mulVec, hpr, Matrix.vecMul_vecMul, hl, Matrix.vecMul_one]
  have hprpos : StrictlyPositive pr := by
    intro j
    have : b j * 1 ≤ pr j := by
      simp only [hpr, Matrix.vecMul, dotProduct]
      calc b j * 1 ≤ b j * (1 - A)⁻¹ j j := mul_le_mul_of_nonneg_left (hdiag j) (hb j).le
        _ ≤ ∑ i, b i * (1 - A)⁻¹ i j := Finset.single_le_sum (f := fun i => b i * (1 - A)⁻¹ i j)
            (fun i _ => mul_nonneg (hb i).le (hnn i j)) (Finset.mem_univ j)
    linarith [hb j]
  have hsup : extendVec ((1 - A) *ᵥ α) (-(b ⬝ᵥ α)) ∈
      supply (leontiefSet A b) (extendVec pr 1) := by
    refine ⟨⟨α, hα, le_rfl⟩, ?_⟩
    rintro y' ⟨α', hα', hle⟩
    rw [← extendVec_inputsOf y'] at hle ⊢
    rw [hdot, hdot, hzero]
    have h1 : extendVec pr 1 ⬝ᵥ extendVec (-inputsOf y') (y' (Fin.last n)) ≤
        extendVec pr 1 ⬝ᵥ extendVec ((1 - A) *ᵥ α') (-(b ⬝ᵥ α')) :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hle i) (by
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp [extendVec]
        · simp only [extendVec, Fin.snoc_castSucc]; exact (hprpos j).le)
    rw [hdot, hdot, hzero] at h1
    linarith
  refine ⟨hsup, proposition_5_F_1 (fun i => ?_) hsup⟩
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [extendVec]
  · simp only [extendVec, Fin.snoc_castSucc]; exact hprpos j

open Matrix in
/-- **Exercise 5.AA.2(b)** (MWG, p. 164). If `α ≫ 0` and `[I - A; -b]α` maximizes profits at the
prices `(p, 1)` (primary factor price normalized to `1`), then `p = b(I - A)⁻¹`: the supporting
prices are unique. -/
theorem exercise_5_AA_2b {A : Matrix (Fin n) (Fin n) ℝ} (hA : ∀ i j, 0 ≤ A i j)
    (hprod : Productive A) {b α p : Fin n → ℝ} (hα : StrictlyPositive α)
    (hsup : extendVec ((1 - A) *ᵥ α) (-(b ⬝ᵥ α)) ∈ supply (leontiefSet A b) (extendVec p 1)) :
    p = b ᵥ* (1 - A)⁻¹ := by
  obtain ⟨-, hr, -, -⟩ := leontief_inverse_facts hA hprod
  have hdot : ∀ (u : Fin n → ℝ) (t : ℝ), extendVec p 1 ⬝ᵥ extendVec u t = p ⬝ᵥ u + t := by
    intro u t
    simp [extendVec, dotProduct, Fin.sum_univ_castSucc]
  -- profits `p(I - A)α' - bα'` are maximized at the interior point `α`
  have hcoef : ∀ j, (p ᵥ* (1 - A)) j = b j := by
    intro j
    have hprof : ∀ t : ℝ, -α j < t →
        (p ᵥ* (1 - A) - b) ⬝ᵥ (α + t • Pi.single j 1) ≤ (p ᵥ* (1 - A) - b) ⬝ᵥ α := by
      intro t ht
      have hmem : extendVec ((1 - A) *ᵥ (α + t • Pi.single j 1))
          (-(b ⬝ᵥ (α + t • Pi.single j 1))) ∈ leontiefSet A b := by
        refine ⟨α + t • Pi.single j 1, fun i => ?_, le_rfl⟩
        by_cases hij : i = j
        · subst hij; simp; linarith
        · simp [hij, (hα i).le]
      have := hsup.2 _ hmem
      rw [hdot, hdot, Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec] at this
      simp only [sub_dotProduct]
      linarith
    have h1 := hprof 1 (by linarith [hα j])
    have h2 := hprof (-(α j / 2)) (by linarith [hα j])
    simp only [dotProduct_add, dotProduct_smul, dotProduct_single, mul_one, smul_eq_mul,
      Pi.sub_apply] at h1 h2
    have := hα j
    nlinarith
  have hpv : p ᵥ* (1 - A) = b := funext hcoef
  rw [← hpv, Matrix.vecMul_vecMul, hr, Matrix.vecMul_one]

open Matrix in
/-- **Exercise 5.AA.2(c)** (MWG, p. 164). The prices `p = b(I - A)⁻¹ = Σ_k bAᵏ` are the amounts of
primary factor used directly (`b`) and indirectly (`bA + bA² + ⋯`) per unit of each good. -/
theorem exercise_5_AA_2c {A : Matrix (Fin n) (Fin n) ℝ} (hA : ∀ i j, 0 ≤ A i j)
    (hprod : Productive A) (b : Fin n → ℝ) :
    HasSum (fun k : ℕ => b ᵥ* (A ^ k)) (b ᵥ* (1 - A)⁻¹) := by
  obtain ⟨hsum, -, hinv, -, -⟩ := proposition_5_AA_1_neumann hA hprod
  rw [hinv]
  let g : Matrix (Fin n) (Fin n) ℝ →+ (Fin n → ℝ) :=
    { toFun := fun M => b ᵥ* M, map_zero' := Matrix.vecMul_zero b,
      map_add' := fun M N => Matrix.vecMul_add M N b }
  exact hsum.hasSum.map g (continuous_const.matrix_vecMul continuous_id)

open Matrix in
/-- **Exercise 5.AA.2(d)** (MWG, p. 164). Let `p` (with wage `1`) support the whole technology, so
every activity of another productive selection `(A', b')` earns at most zero profit,
`p(I - A') ≤ b'`. Then `p ≤ b'(I - A')⁻¹` componentwise: the prices of the technique selected by
the nonsubstitution theorem (`p = b(I - A)⁻¹`) are minimal. -/
theorem exercise_5_AA_2d {A' : Matrix (Fin n) (Fin n) ℝ} (hA' : ∀ i j, 0 ≤ A' i j)
    (hprod' : Productive A') {b' p : Fin n → ℝ} (hle : p ᵥ* (1 - A') ≤ b') :
    p ≤ b' ᵥ* (1 - A')⁻¹ := by
  obtain ⟨-, hr, hnn, -⟩ := leontief_inverse_facts hA' hprod'
  intro j
  have : p = (p ᵥ* (1 - A')) ᵥ* (1 - A')⁻¹ := by
    rw [Matrix.vecMul_vecMul, hr, Matrix.vecMul_one]
  rw [this]
  simp only [Matrix.vecMul, dotProduct]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hle i) (hnn i j)

/-! ### Exercise 5.AA.3 -/

/-- **Exercise 5.AA.3(a)-(c)** (MWG, p. 165). For `A = [[0, 1], [1/2, 0]]` (`a_{ℓk}` the amount
of good `ℓ` per unit of good `k`) and `b = (1, 2)`: (b) the zero-profit prices with wage `1`,
`p_k = Σ_ℓ p_ℓ a_{ℓk} + b_k`, are `p = (4, 6)`; (c) `4` is the labour embodied in one net unit of
good `1`; (a) with `10` units of labour, `c ≥ 0` is producible iff `4c₁ + 6c₂ ≤ 10`. -/
theorem exercise_5_AA_3 :
    let A : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1 / 2, 0]
    let b : Fin 2 → ℝ := ![1, 2]
    (∀ p : Fin 2 → ℝ, (p 0 = p 0 * A 0 0 + p 1 * A 1 0 + b 0 ∧
      p 1 = p 0 * A 0 1 + p 1 * A 1 1 + b 1) ↔ p = ![4, 6]) ∧
    b ⬝ᵥ ![2, 1] = 4 ∧ (1 - A).mulVec ![2, 1] = ![1, 0] ∧
    ∀ c : Fin 2 → ℝ, 0 ≤ c →
      ((∃ x : Fin 2 → ℝ, 0 ≤ x ∧ c ≤ (1 - A).mulVec x ∧ b ⬝ᵥ x ≤ 10) ↔ 4 * c 0 + 6 * c 1 ≤ 10) := by
  intro A b
  refine ⟨fun p => ?_, by simp [b, dotProduct]; norm_num, ?_, fun c hc => ?_⟩
  · simp only [A, b, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    constructor
    · rintro ⟨h0, h1⟩
      funext i; fin_cases i <;> simp <;> linarith
    · rintro rfl
      norm_num
  · funext i
    fin_cases i <;> norm_num [A, Matrix.mulVec, dotProduct]
  · constructor
    · rintro ⟨x, hx, hcx, hbx⟩
      have h0 := hcx 0
      have h1 := hcx 1
      have x0 : 0 ≤ x 0 := hx 0
      have x1 : 0 ≤ x 1 := hx 1
      simp [A, Matrix.mulVec, dotProduct] at h0 h1
      simp [b, dotProduct] at hbx
      linarith
    · intro h
      have c0 : 0 ≤ c 0 := hc 0
      have c1 : 0 ≤ c 1 := hc 1
      refine ⟨![2 * c 0 + 2 * c 1, c 0 + 2 * c 1], fun i => ?_, fun i => ?_, ?_⟩
      · fin_cases i <;> simp <;> linarith
      · fin_cases i <;> simp [A, Matrix.mulVec, dotProduct] <;> linarith
      · simp [b, dotProduct]; linarith

/-- **Exercise 5.AA.3(e)** (MWG, p. 165). With the second technique for good 2 (`a'₁₂ = 1/2`,
`b'₂ = β`), the zero-profit prices are `p₂ = (2 + 4β)/3` (against `p₂ = 6` with the original
technique); the techniques switch at `β = 4`, the new one being cheaper iff `β < 4`. -/
theorem exercise_5_AA_3e (β : ℝ) :
    (∀ p₁ p₂ : ℝ, (p₁ = p₂ / 2 + 1 ∧ p₂ = p₁ / 2 + β) ↔ (p₂ = (2 + 4 * β) / 3 ∧
      p₁ = (4 + 2 * β) / 3)) ∧ ((2 + 4 * β) / 3 < 6 ↔ β < 4) ∧ ((2 + 4 * β) / 3 = 6 ↔ β = 4) := by
  refine ⟨fun p₁ p₂ => ⟨fun ⟨h1, h2⟩ => ⟨by linarith, by linarith⟩,
    fun ⟨h1, h2⟩ => ⟨by linarith, by linarith⟩⟩, ⟨fun h => by linarith, fun h => by linarith⟩,
    ⟨fun h => by linarith, fun h => by subst h; norm_num⟩⟩

/-! ### Exercise 5.AA.4 -/

/-- The four activities of Exercise 5.AA.4. -/
def aa4 : Fin 4 → Fin 4 → ℝ := ![![1, -1, 0, 0], ![0, -1, 1, 0], ![0, 0, -1, 1], ![2, 0, 0, -1]]

theorem aa4_coords (lam : Fin 4 ⊕ Fin 4 → ℝ) :
    ∑ j, lam j • withDisposal aa4 j =
      ![lam (Sum.inl 0) + 2 * lam (Sum.inl 3) - lam (Sum.inr 0),
        -lam (Sum.inl 0) - lam (Sum.inl 1) - lam (Sum.inr 1),
        lam (Sum.inl 1) - lam (Sum.inl 2) - lam (Sum.inr 2),
        lam (Sum.inl 2) - lam (Sum.inl 3) - lam (Sum.inr 3)] := by
  rw [Fintype.sum_sum_type]
  funext i
  fin_cases i <;> simp [withDisposal, aa4, Fin.sum_univ_four] <;> ring

/-- **Exercise 5.AA.4(a)** (MWG, p. 165). With the disposal activities, `y₂ = 3a₁ + a₄`,
`y₃ = 3(a₂ + a₃ + a₄)` and `y₄ = 4(a₂ + a₃)` belong to `Y`, while `y₁ = (6, 0, 0, -2)` and
`y₅ = (0, -3, 4, 0)` do not. -/
theorem exercise_5_AA_4a :
    (![6, 0, 0, -2] : Fin 4 → ℝ) ∉ coneOf (withDisposal aa4) ∧
      (![5, -3, 0, -1] : Fin 4 → ℝ) ∈ coneOf (withDisposal aa4) ∧
      (![6, -3, 0, 0] : Fin 4 → ℝ) ∈ coneOf (withDisposal aa4) ∧
      (![0, -4, 0, 4] : Fin 4 → ℝ) ∈ coneOf (withDisposal aa4) ∧
      (![0, -3, 4, 0] : Fin 4 → ℝ) ∉ coneOf (withDisposal aa4) := by
  have hmem : ∀ (l : Fin 4 → ℝ), 0 ≤ l → ∑ j, (Sum.elim l 0 : Fin 4 ⊕ Fin 4 → ℝ) j •
      withDisposal aa4 j ∈ coneOf (withDisposal aa4) := fun l hl =>
    ⟨Sum.elim l 0, fun j => by rcases j with j | j; exacts [hl j, le_rfl], rfl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨lam, hlam, h⟩
    rw [aa4_coords] at h
    have h0 := congrFun h 0; have h1 := congrFun h 1
    have h2 := congrFun h 2; have h3 := congrFun h 3
    simp at h0 h1 h2 h3
    have := hlam (Sum.inl 0); have := hlam (Sum.inl 1); have := hlam (Sum.inl 2)
    have := hlam (Sum.inl 3); have := hlam (Sum.inr 0); have := hlam (Sum.inr 1)
    have := hlam (Sum.inr 2); have := hlam (Sum.inr 3)
    simp only [Pi.zero_apply] at *
    linarith
  · have := hmem ![3, 0, 0, 1] (fun i => by fin_cases i <;> simp)
    rw [aa4_coords] at this
    convert this using 1
    funext i; fin_cases i <;> norm_num
  · have := hmem ![0, 3, 3, 3] (fun i => by fin_cases i <;> simp)
    rw [aa4_coords] at this
    convert this using 1
    funext i; fin_cases i <;> norm_num
  · have := hmem ![0, 4, 4, 0] (fun i => by fin_cases i <;> simp)
    rw [aa4_coords] at this
    convert this using 1
    funext i; fin_cases i <;> simp
  · rintro ⟨lam, hlam, h⟩
    rw [aa4_coords] at h
    have h1 := congrFun h 1; have h2 := congrFun h 2
    simp at h1 h2
    have := hlam (Sum.inl 0); have := hlam (Sum.inl 1); have := hlam (Sum.inl 2)
    have := hlam (Sum.inr 1); have := hlam (Sum.inr 2)
    simp only [Pi.zero_apply] at *
    linarith

/-- **Exercise 5.AA.4(b)-(c)** (MWG, p. 165). `y = (0, -5, 5, 0) = 5a₂` is efficient: it maximizes
profits at `p = (1, 2, 2, 2) ≫ 0`. `a₁ = (1, -1, 0, 0)` is feasible but not efficient:
`a₂ + a₃ + a₄ = (2, -1, 0, 0) ≥ a₁`. -/
theorem exercise_5_AA_4bc :
    (![0, -5, 5, 0] : Fin 4 → ℝ) ∈ supply (coneOf (withDisposal aa4)) ![1, 2, 2, 2] ∧
      Efficient (coneOf (withDisposal aa4)) ![0, -5, 5, 0] ∧
      ¬ Efficient (coneOf (withDisposal aa4)) ![1, -1, 0, 0] := by
  have hpg : ∀ j, (![1, 2, 2, 2] : Fin 4 → ℝ) ⬝ᵥ withDisposal aa4 j ≤ 0 := by
    intro j
    rcases j with j | j <;> fin_cases j <;>
      simp [withDisposal, aa4, dotProduct, Fin.sum_univ_four, Pi.single_apply]
  have hsup : (![0, -5, 5, 0] : Fin 4 → ℝ) ∈ supply (coneOf (withDisposal aa4)) ![1, 2, 2, 2] := by
    rw [activity_supply_eq hpg]
    refine ⟨Sum.elim ![0, 5, 0, 0] 0, fun j => ?_, fun j hj => ?_, ?_⟩
    · rcases j with j | j <;> fin_cases j <;> simp
    · rcases j with j | j <;> fin_cases j <;>
        simp [withDisposal, aa4, dotProduct, Fin.sum_univ_four, Pi.single_apply] at hj ⊢
    · rw [aa4_coords]; funext i; fin_cases i <;> simp
  refine ⟨hsup, proposition_5_F_1 (fun i => by fin_cases i <;> simp) hsup, fun h => ?_⟩
  apply h.2 ⟨![2, -1, 0, 0], ⟨Sum.elim ![0, 1, 1, 1] 0, fun j => by
    rcases j with j | j <;> fin_cases j <;> simp, by rw [aa4_coords]; funext i; fin_cases i <;>
      simp⟩, fun i => by fin_cases i <;> simp, fun he => by
    have := congrFun he 0; simp at this⟩

end MWG.Production
