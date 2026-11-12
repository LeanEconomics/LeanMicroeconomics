/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGConsumerChoice.AppendixMDBordered
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Order.Filter.Finite

/-!
# Bordered determinantal tests (Theorem M.D.3, corrected)

MWG, Mathematical Appendix, Theorem M.D.3 (p. 938), with the subspace `{z : Bᵀz = 0}`.

* `bordered_det_ne_zero`, `bordered_sign_pos`: if `A` is negative definite on `{z : Cᵀz = 0}`
  and `C` has full column rank, the bordered matrix `[[A, C], [Cᵀ, 0]]` is nonsingular and
  `(-1)^n |·| > 0` (`n` the size of `A`). The sign is found by deforming `A` to `-I` through
  matrices negative definite on the subspace; at `-I` the determinant is `(-1)^n |CᵀC|`.
* `bordered_det_eq`: `|[[A, C], [Cᵀ, εI]]| = ε^S |A - ε⁻¹CCᵀ|` for `ε ≠ 0`.
* `theorem_M_D_3_i` (corrected): if the top `S × S` block of `B` is nonsingular, `M` is negative
  definite on `{z : Bᵀz = 0}` iff `(-1)^r |bordered_r| > 0` for `r = S+1, …, N`. Sufficiency:
  for large `λ` every leading minor of `M - λBBᵀ` has sign `(-1)^r` (by the identity above for
  `r > S`, and by `|λ⁻¹ₜMₜ - ₜB ₜBᵀ| → (-1)^r |ₜB ₜBᵀ|` for `r ≤ S`), so `M - λBBᵀ` is negative
  definite by Sylvester's criterion.
* `theorem_M_D_3_ii_forward`: the necessity half of Theorem M.D.3(ii) as printed (all `r > S`
  and all permutations), with no rank hypothesis.
-/

namespace MWG.ConsumerChoice

open Matrix Filter Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ℕ}

/-- The bordered matrix `[[A, C], [Cᵀ, 0]]`. -/
def bordered (A : Matrix ι ι ℝ) (C : Matrix ι (Fin S) ℝ) : Matrix (ι ⊕ Fin S) (ι ⊕ Fin S) ℝ :=
  fromBlocks A C Cᵀ 0

/-- A bordered matrix whose border has a nonzero kernel vector is singular. -/
theorem bordered_det_eq_zero_of_not_injective {A : Matrix ι ι ℝ} {C : Matrix ι (Fin S) ℝ}
    (hC : ¬ ∀ μ, C *ᵥ μ = 0 → μ = 0) : (bordered A C).det = 0 := by
  push Not at hC
  obtain ⟨μ, hμ, hμ0⟩ := hC
  rw [← exists_mulVec_eq_zero_iff]
  refine ⟨Sum.elim 0 μ, fun h => hμ0 (funext fun j => by simpa using congrFun h (Sum.inr j)),
    ?_⟩
  funext k
  rcases k with i | j
  · have := congrFun hμ i
    simpa [bordered, mulVec, dotProduct, Fintype.sum_sum_type] using this
  · simp [bordered, mulVec, dotProduct, Fintype.sum_sum_type]

/-- If `A` is negative definite on `{z : Cᵀz = 0}` and `C` is injective, the bordered matrix is
nonsingular. -/
theorem bordered_det_ne_zero {A : Matrix ι ι ℝ} {C : Matrix ι (Fin S) ℝ}
    (hA : ∀ z, Cᵀ *ᵥ z = 0 → z ≠ 0 → z ⬝ᵥ A *ᵥ z < 0) (hC : ∀ μ, C *ᵥ μ = 0 → μ = 0) :
    (bordered A C).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, h0⟩ := exists_mulVec_eq_zero_iff.mpr hdet
  set z : ι → ℝ := fun i => v (Sum.inl i)
  set μ : Fin S → ℝ := fun j => v (Sum.inr j)
  have h1 : A *ᵥ z + C *ᵥ μ = 0 := by
    funext i
    have := congrFun h0 (Sum.inl i)
    simpa [bordered, mulVec, dotProduct, Fintype.sum_sum_type, z, μ] using this
  have h2 : Cᵀ *ᵥ z = 0 := by
    funext j
    have := congrFun h0 (Sum.inr j)
    simpa [bordered, mulVec, dotProduct, Fintype.sum_sum_type, z, μ] using this
  have hz : z = 0 := by
    by_contra hz
    have hlt := hA z h2 hz
    have : z ⬝ᵥ A *ᵥ z = 0 := by
      rw [eq_neg_of_add_eq_zero_left h1, dotProduct_neg, dotProduct_mulVec, ← mulVec_transpose,
        h2, zero_dotProduct, neg_zero]
    linarith
  have hμ : μ = 0 := hC μ (by rw [hz, mulVec_zero, zero_add] at h1; exact h1)
  apply hv
  funext k
  rcases k with i | j
  · exact congrFun hz i
  · exact congrFun hμ j

omit [DecidableEq ι] in
/-- `CᵀC` is positive definite when `C` is injective. -/
theorem posDefMWG_transpose_mul {C : Matrix ι (Fin S) ℝ} (hC : ∀ μ, C *ᵥ μ = 0 → μ = 0) :
    PosDefMWG (Cᵀ * C) := by
  intro μ hμ
  rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  exact dotProduct_self_pos_of_ne_zero (fun h => hμ (hC μ h))

omit [DecidableEq ι] in
/-- `CCᵀ` is positive definite when `Cᵀ` is injective. -/
theorem posDefMWG_mul_transpose {C : Matrix ι (Fin S) ℝ} (hC : ∀ y, Cᵀ *ᵥ y = 0 → y = 0) :
    PosDefMWG (C * Cᵀ) := by
  intro y hy
  rw [← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose]
  exact dotProduct_self_pos_of_ne_zero (fun h => hy (hC y h))

/-- **Theorem M.D.3** (sign of the bordered determinant). If `A` (`n × n`) is negative definite on
`{z : Cᵀz = 0}` and `C` is injective, then `(-1)^n |[[A, C], [Cᵀ, 0]]| > 0`. -/
theorem bordered_sign_pos {A : Matrix ι ι ℝ} {C : Matrix ι (Fin S) ℝ}
    (hA : ∀ z, Cᵀ *ᵥ z = 0 → z ≠ 0 → z ⬝ᵥ A *ᵥ z < 0) (hC : ∀ μ, C *ᵥ μ = 0 → μ = 0) :
    0 < (-1) ^ Fintype.card ι * (bordered A C).det := by
  set f : ℝ → ℝ := fun s =>
    (-1) ^ Fintype.card ι * (bordered ((1 - s) • A - s • (1 : Matrix ι ι ℝ)) C).det with hf
  have hcont : Continuous f := by
    apply continuous_const.mul
    apply Continuous.matrix_det
    exact Continuous.matrix_fromBlocks
      (((continuous_const.sub continuous_id).smul continuous_const).sub
        (continuous_id.smul continuous_const)) continuous_const continuous_const continuous_const
  have hne : ∀ s ∈ Set.Icc (0 : ℝ) 1, f s ≠ 0 := by
    intro s hs
    have hdet := bordered_det_ne_zero (A := (1 - s) • A - s • (1 : Matrix ι ι ℝ)) (C := C)
      (fun z hz hz0 => by
        rw [sub_mulVec, smul_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul,
          dotProduct_smul, smul_eq_mul, smul_eq_mul]
        have h1 := hA z hz hz0
        have h2 := dotProduct_self_pos_of_ne_zero hz0
        rcases eq_or_lt_of_le hs.2 with h | h
        · rw [h]; simp; linarith
        · nlinarith [mul_nonneg hs.1 h2.le, mul_pos (sub_pos.mpr h) (neg_pos.mpr h1)]) hC
    simp only [hf]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hdet
  have h1 : 0 < f 1 := by
    have hU : IsUnit (-(1 : Matrix ι ι ℝ)).det := by
      rw [det_neg, det_one, mul_one]
      exact (isUnit_neg_one (α := ℝ)).pow _
    let _inst : Invertible (-(1 : Matrix ι ι ℝ)) := (-(1 : Matrix ι ι ℝ)).invertibleOfIsUnitDet hU
    have hinv : ⅟(-(1 : Matrix ι ι ℝ)) = -1 := by
      rw [invOf_eq_nonsing_inv]
      apply Matrix.inv_eq_right_inv
      rw [neg_mul_neg, Matrix.one_mul]
    simp only [hf, sub_self, zero_smul, one_smul, zero_sub, bordered]
    rw [det_fromBlocks₁₁, hinv, det_neg, det_one, mul_one]
    have e : (0 : Matrix (Fin S) (Fin S) ℝ) - Cᵀ * (-1 : Matrix ι ι ℝ) * C = Cᵀ * C := by
      rw [Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, sub_neg_eq_add, zero_add]
    rw [e, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
    norm_num
    exact (posDefMWG_transpose_mul hC).det_pos
  have h0 : f 0 = (-1) ^ Fintype.card ι * (bordered A C).det := by simp [hf]
  rw [← h0]
  by_contra hc
  push Not at hc
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc zero_le_one hcont.continuousOn
    (show (0 : ℝ) ∈ Set.Icc (f 0) (f 1) from ⟨hc, h1.le⟩)
  exact hne t ht hft

/-- `|[[A, C], [Cᵀ, εI]]| = ε^S |A - ε⁻¹CCᵀ|` for `ε ≠ 0`. -/
theorem bordered_det_eq {A : Matrix ι ι ℝ} {C : Matrix ι (Fin S) ℝ} {ε : ℝ} (hε : ε ≠ 0) :
    (fromBlocks A C Cᵀ (ε • (1 : Matrix (Fin S) (Fin S) ℝ))).det =
      ε ^ S * (A - ε⁻¹ • (C * Cᵀ)).det := by
  have hU : IsUnit (ε • (1 : Matrix (Fin S) (Fin S) ℝ)).det := by
    rw [det_smul, det_one, mul_one, Fintype.card_fin]
    exact isUnit_iff_ne_zero.mpr (pow_ne_zero _ hε)
  let _inst := (ε • (1 : Matrix (Fin S) (Fin S) ℝ)).invertibleOfIsUnitDet hU
  have hinv : ⅟(ε • (1 : Matrix (Fin S) (Fin S) ℝ)) = ε⁻¹ • 1 := by
    rw [invOf_eq_nonsing_inv]
    apply Matrix.inv_eq_right_inv
    rw [smul_mul_smul_comm, mul_inv_cancel₀ hε, one_mul, one_smul]
  rw [det_fromBlocks₂₂, hinv, det_smul, det_one, mul_one, Fintype.card_fin]
  congr 2
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]

/-- Extension by zero commutes with the border: `Bᵀẑ = (B_e)ᵀz`. -/
theorem transpose_mulVec_extend {m n : Type*} [Fintype m] [Fintype n] (B : Matrix n (Fin S) ℝ)
    {e : m → n} (he : Function.Injective e) (z : m → ℝ) :
    Bᵀ *ᵥ Function.extend e z 0 = (B.submatrix e id)ᵀ *ᵥ z := by
  funext j
  simp only [mulVec, dotProduct, transpose_apply, submatrix_apply, id]
  rw [show (∑ x, B x j * Function.extend e z 0 x) = ∑ x, Function.extend e z 0 x * B x j from
    Finset.sum_congr rfl fun _ _ => mul_comm _ _, sum_extend_mul he]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

/-- Restricting a quadratic form that is negative definite on `{z : Bᵀz = 0}` to a set of
coordinates gives a form negative definite on the corresponding subspace. -/
theorem negDef_on_ker_submatrix {m n : Type*} [Fintype m] [Fintype n] {M : Matrix n n ℝ}
    {B : Matrix n (Fin S) ℝ} (hM : ∀ z, Bᵀ *ᵥ z = 0 → z ≠ 0 → z ⬝ᵥ M *ᵥ z < 0)
    {e : m → n} (he : Function.Injective e) :
    ∀ z, (B.submatrix e id)ᵀ *ᵥ z = 0 → z ≠ 0 → z ⬝ᵥ (M.submatrix e e) *ᵥ z < 0 := by
  classical
  intro z hz hz0
  rw [quadratic_submatrix M he]
  apply hM
  · rw [transpose_mulVec_extend B he]; exact hz
  · intro h0
    apply hz0
    funext i
    have := congrFun h0 (e i)
    rwa [he.extend_apply] at this

/-- The leading rows of `B` from row `r ≥ S` contain the top block `B₁`: if `B₁` is nonsingular
the leading `r` rows have full column rank. -/
theorem leadingRows_injective {N r : ℕ} {B : Matrix (Fin N) (Fin S) ℝ} (hSN : S ≤ N)
    (hB : (B.submatrix (Fin.castLE hSN) id).det ≠ 0) (hrN : r ≤ N) (hSr : S ≤ r) :
    ∀ μ, (B.submatrix (Fin.castLE hrN) id) *ᵥ μ = 0 → μ = 0 := by
  intro μ hμ
  by_contra hne
  apply hB
  rw [← exists_mulVec_eq_zero_iff]
  refine ⟨μ, hne, funext fun i => ?_⟩
  have := congrFun hμ (Fin.castLE hSr i)
  simpa [mulVec, dotProduct] using this

/-- For `r ≤ S`, the leading `r` rows of `B` have full row rank when `B₁` is nonsingular. -/
theorem leadingRows_transpose_injective {N r : ℕ} {B : Matrix (Fin N) (Fin S) ℝ} (hSN : S ≤ N)
    (hB : (B.submatrix (Fin.castLE hSN) id).det ≠ 0) (hrN : r ≤ N) (hrS : r ≤ S) :
    ∀ y, (B.submatrix (Fin.castLE hrN) id)ᵀ *ᵥ y = 0 → y = 0 := by
  classical
  intro y hy
  have he : Function.Injective (Fin.castLE hrS) := Fin.castLE_injective hrS
  have hT : (B.submatrix (Fin.castLE hSN) id)ᵀ *ᵥ Function.extend (Fin.castLE hrS) y 0 = 0 := by
    rw [transpose_mulVec_extend _ he]
    exact hy
  have hdetT : ((B.submatrix (Fin.castLE hSN) id)ᵀ).det ≠ 0 := by rwa [det_transpose]
  by_contra hne
  apply hdetT
  rw [← exists_mulVec_eq_zero_iff]
  refine ⟨_, fun h0 => hne (funext fun i => ?_), hT⟩
  have := congrFun h0 (Fin.castLE hrS i)
  rwa [he.extend_apply] at this

/-- **Theorem M.D.3(i)** (MWG, p. 938), corrected. Let `M` be symmetric `N × N` and `B` an
`N × S` matrix whose top `S × S` block is nonsingular. Then `M` is negative definite on
`{z : Bᵀz = 0}` iff `(-1)^r |[[ₜMₜ, ₜB], [(ₜB)ᵀ, 0]]| > 0` for `r = S+1, …, N`. -/
theorem theorem_M_D_3_i {N : ℕ} {M : Matrix (Fin N) (Fin N) ℝ} (hM : M.IsSymm)
    (B : Matrix (Fin N) (Fin S) ℝ) (hSN : S ≤ N)
    (hB : (B.submatrix (Fin.castLE hSN) id).det ≠ 0) :
    (∀ z, Bᵀ *ᵥ z = 0 → z ≠ 0 → z ⬝ᵥ M *ᵥ z < 0) ↔
      ∀ r (h : r ≤ N), S < r → 0 < (-1) ^ r * (borderedMatrix M B r h).det := by
  constructor
  · intro hND r h hr
    have := bordered_sign_pos (A := leadingMinorMatrix M r h) (C := B.submatrix (Fin.castLE h) id)
      (negDef_on_ker_submatrix hND (Fin.castLE_injective h))
      (leadingRows_injective hSN hB h hr.le)
    simpa [bordered, borderedMatrix] using this
  · intro hsign
    -- every leading minor of `M - λBBᵀ` eventually has sign `(-1)^r`
    have hev : ∀ r ∈ Finset.Icc 1 N, ∀ᶠ lam : ℝ in atTop, ∀ h : r ≤ N,
        0 < (-1) ^ r * (leadingMinorMatrix (M - lam • (B * Bᵀ)) r h).det := by
      intro r hr
      have hrN : r ≤ N := (Finset.mem_Icc.mp hr).2
      set A := leadingMinorMatrix M r hrN
      set C := B.submatrix (Fin.castLE hrN) id
      have hsub : ∀ lam : ℝ,
          leadingMinorMatrix (M - lam • (B * Bᵀ)) r hrN = A - lam • (C * Cᵀ) := by
        intro lam
        ext i j
        simp [A, C, leadingMinorMatrix, Matrix.mul_apply]
      have hpos : ∀ᶠ lam : ℝ in atTop, 0 < lam := eventually_gt_atTop 0
      have hinv := tendsto_inv_atTop_zero (𝕜 := ℝ)
      rcases le_or_gt r S with hrS | hrS
      · set g : ℝ → ℝ := fun ε => (-1) ^ r * (ε • A - C * Cᵀ).det with hg
        have hgc : Continuous g := continuous_const.mul
          ((continuous_id.smul continuous_const).sub continuous_const).matrix_det
        have hg0 : 0 < g 0 := by
          simp only [hg, zero_smul, zero_sub, det_neg, Fintype.card_fin, ← mul_assoc, ← pow_add,
            ← two_mul, pow_mul]
          norm_num
          exact (posDefMWG_mul_transpose
            (leadingRows_transpose_injective hSN hB hrN hrS)).det_pos
        filter_upwards [hpos, hinv.eventually (hgc.continuousAt.eventually (lt_mem_nhds hg0))]
          with lam hlam hglam _
        rw [hsub]
        have e : A - lam • (C * Cᵀ) = lam • (lam⁻¹ • A - C * Cᵀ) := by
          rw [smul_sub, smul_smul, mul_inv_cancel₀ hlam.ne', one_smul]
        rw [e, det_smul, Fintype.card_fin]
        have : 0 < lam ^ r * g lam⁻¹ := mul_pos (pow_pos hlam r) hglam
        simp only [hg] at this
        linarith [show (-1) ^ r * (lam ^ r * (lam⁻¹ • A - C * Cᵀ).det) =
          lam ^ r * ((-1) ^ r * (lam⁻¹ • A - C * Cᵀ).det) by ring]
      · set k : ℝ → ℝ := fun ε =>
          (-1) ^ r * (fromBlocks A C Cᵀ (ε • (1 : Matrix (Fin S) (Fin S) ℝ))).det with hk
        have hkc : Continuous k := continuous_const.mul
          (Continuous.matrix_fromBlocks continuous_const continuous_const continuous_const
            (continuous_id.smul continuous_const)).matrix_det
        have hk0 : 0 < k 0 := by
          simpa [hk, borderedMatrix, A, C] using hsign r hrN hrS
        filter_upwards [hpos, hinv.eventually (hkc.continuousAt.eventually (lt_mem_nhds hk0))]
          with lam hlam hklam _
        rw [hsub]
        have e := bordered_det_eq (A := A) (C := C) (inv_ne_zero hlam.ne')
        rw [inv_inv] at e
        have hdet : (A - lam • (C * Cᵀ)).det =
            (fromBlocks A C Cᵀ (lam⁻¹ • (1 : Matrix (Fin S) (Fin S) ℝ))).det / lam⁻¹ ^ S := by
          rw [e]
          field_simp
        rw [hdet, mul_div_assoc']
        exact div_pos hklam (pow_pos (inv_pos.mpr hlam) S)
    obtain ⟨lam, hlam⟩ := ((eventually_all_finset _).mpr hev).exists
    have hsymm : (M - lam • (B * Bᵀ)).IsSymm := by
      ext i j
      simp [hM.apply i j, Matrix.mul_apply, mul_comm]
    have hND := (theorem_M_D_2_i hsymm).mpr (fun r h hr => hlam r (Finset.mem_Icc.mpr ⟨hr, h⟩) h)
    intro z hz hz0
    have := hND z hz0
    rwa [sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul, ← mulVec_mulVec, hz,
      mulVec_zero, dotProduct_zero, smul_zero, sub_zero] at this

/-- **Theorem M.D.3(ii)** (MWG, p. 938), necessity. If the symmetric `M` is negative
semidefinite on `{z : Bᵀz = 0}`, then `(-1)^r |[[ₜM^πₜ, ₜB^π], [(ₜB^π)ᵀ, 0]]| ≥ 0` for every
`r > S` and every permutation `π` (rows and columns of `M`, rows of `B`). -/
theorem theorem_M_D_3_ii_forward {N : ℕ} {M : Matrix (Fin N) (Fin N) ℝ}
    (B : Matrix (Fin N) (Fin S) ℝ) (hNSD : ∀ z, Bᵀ *ᵥ z = 0 → z ⬝ᵥ M *ᵥ z ≤ 0)
    (r : ℕ) (h : r ≤ N) (π : Equiv.Perm (Fin N)) :
    0 ≤ (-1) ^ r * (borderedMatrix (permuteMatrix M π) (B.submatrix π id) r h).det := by
  classical
  set e : Fin r → Fin N := π ∘ Fin.castLE h
  have he : Function.Injective e := π.injective.comp (Fin.castLE_injective h)
  set A := M.submatrix e e
  set C := B.submatrix e id
  have hbm : ∀ ε : ℝ, borderedMatrix (permuteMatrix M π) (B.submatrix π id) r h =
      bordered A C := fun _ => rfl
  rw [hbm 0]
  by_cases hC : ∀ μ, C *ᵥ μ = 0 → μ = 0
  · set k : ℝ → ℝ := fun ε => (-1) ^ r * (bordered (A - ε • (1 : Matrix (Fin r) (Fin r) ℝ)) C).det
      with hk
    have hkc : Continuous k := continuous_const.mul
      (Continuous.matrix_fromBlocks (continuous_const.sub (continuous_id.smul continuous_const))
        continuous_const continuous_const continuous_const).matrix_det
    have hkpos : ∀ ε : ℝ, 0 < ε → 0 < k ε := by
      intro ε hε
      have := bordered_sign_pos (A := A - ε • (1 : Matrix (Fin r) (Fin r) ℝ)) (C := C)
        (fun z hz hz0 => by
          rw [sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]
          have h1 : z ⬝ᵥ A *ᵥ z ≤ 0 := by
            rw [quadratic_submatrix M he]
            apply hNSD
            rw [transpose_mulVec_extend B he]
            exact hz
          nlinarith [dotProduct_self_pos_of_ne_zero hz0]) hC
      simpa [hk] using this
    have hk0 : k 0 = (-1) ^ r * (bordered A C).det := by simp [hk]
    rw [← hk0]
    apply ge_of_tendsto (hkc.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0)))
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (hkpos ε hε).le
  · rw [bordered_det_eq_zero_of_not_injective hC, mul_zero]

end MWG.ConsumerChoice
