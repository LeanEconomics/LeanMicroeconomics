/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGConsumerChoice.AppendixMDBorderedTests
import MWGConsumerChoice.AppendixMDSemidef
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.Data.Finset.Sum

/-!
# The semidefinite bordered test (Theorem M.D.3(ii), sufficiency)

MWG, Mathematical Appendix, Theorem M.D.3(ii) (p. 938). With `{z : Bᵀz = 0}` for the printed
`{z : Bz = 0}`, and `B` of rank `S` in the form "some `S` rows of `B` are linearly independent":
if `(-1)^r |[[ₜM^πₜ, ₜB^π], [(ₜB^π)ᵀ, 0]]| ≥ 0` for every `r = S+1, …, N` and every permutation
`π`, then the symmetric `M` is negative semidefinite on `{z : Bᵀz = 0}`.

* `det_add_diagonal_expansion`: `|H + diag d| = ∑_W (∏_{i ∉ W} dᵢ) |H_W|` (all `dᵢ ≠ 0`), from
  Mathlib's expansion of `det (1 + X • K)` in principal minors.
* `bordered_perturbation_expansion`: `(-1)^n |[[A - εI, C], [Cᵀ, 0]]| =
  ∑_U ε^{n-|U|} (-1)^{|U|} |[[A_U, C_U], [C_Uᵀ, 0]]|`, by letting the border diagonal tend to 0.
* With the rows reordered so that the first `S` rows of `B` are independent, every term is
  `≥ 0` and the term of those `S` rows is `> 0`, so corrected Theorem M.D.3(i) applies to
  `M - εI` for every `ε > 0`.
-/

namespace MWG.ConsumerChoice

open Matrix Polynomial Filter Topology

/-- The sum of all principal minors: `|I + K| = ∑_W |K_W|`. -/
theorem det_one_add_eq_sum_minors {n : Type*} [Fintype n] [DecidableEq n] (K : Matrix n n ℝ) :
    (1 + K).det = ∑ W : Finset n, (K.submatrix (Subtype.val : W → n) Subtype.val).det := by
  set P : ℝ[X] := det (1 + (X : ℝ[X]) • K.map C) with hP
  have heval : P.eval 1 = (1 + K).det := by
    rw [hP, ← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1
    ext a b
    by_cases hab : a = b
    · subst hab
      simp
    · simp [hab]
  have hdeg : P.natDegree < Fintype.card n + 1 := by
    have := natDegree_det_X_add_C_le K (1 : Matrix n n ℝ)
    rw [Matrix.map_one _ (map_zero C) (map_one C), add_comm] at this
    exact Nat.lt_succ_of_le this
  rw [← heval, eval_eq_sum_range' hdeg]
  simp only [one_pow, mul_one]
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (g := Finset.card)
    (t := Finset.range (Fintype.card n + 1))
    (fun W _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.card_le_univ W)))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hP, coeff_det_one_add_X_smul_eq_sum_minors, Finset.powersetCard_eq_filter,
    Finset.powerset_univ]

/-- **Expansion of a diagonally perturbed determinant.** For `dᵢ ≠ 0`,
`|H + diag d| = ∑_W (∏_{i ∉ W} dᵢ) |H_W|`. -/
theorem det_add_diagonal_expansion {n : Type*} [Fintype n] [DecidableEq n] (H : Matrix n n ℝ)
    {d : n → ℝ} (hd : ∀ i, d i ≠ 0) :
    (H + diagonal d).det =
      ∑ W : Finset n, (∏ i ∈ Wᶜ, d i) * (H.submatrix (Subtype.val : W → n) Subtype.val).det := by
  have hfac : H + diagonal d = diagonal d * (1 + diagonal (fun i => (d i)⁻¹) * H) := by
    rw [Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, diagonal_mul_diagonal]
    have : (fun i => d i * (d i)⁻¹) = fun _ => (1 : ℝ) := funext fun i => mul_inv_cancel₀ (hd i)
    rw [this, diagonal_one, Matrix.one_mul, add_comm]
  rw [hfac, det_mul, det_diagonal, det_one_add_eq_sum_minors, Finset.mul_sum]
  refine Finset.sum_congr rfl fun W _ => ?_
  have hsub : (diagonal (fun i => (d i)⁻¹) * H).submatrix (Subtype.val : W → n) Subtype.val =
      diagonal (fun i : W => (d i)⁻¹) * H.submatrix Subtype.val Subtype.val := by
    ext a b
    simp [diagonal_mul]
  rw [hsub, det_mul, det_diagonal, ← Finset.prod_mul_prod_compl W d, ← mul_assoc]
  congr 1
  rw [mul_comm (∏ i ∈ W, d i), mul_assoc]
  have : (∏ i ∈ W, d i) * ∏ i : W, (d i)⁻¹ = 1 := by
    rw [← Finset.prod_coe_sort W d, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun i _ => mul_inv_cancel₀ (hd i)
  rw [this, mul_one]

/-- The principal submatrix of a bordered matrix on `U ⊔ (all border indices)` is the bordered
matrix of the principal submatrix on `U`. -/
theorem det_bordered_submatrix_disjSum {ι : Type*} [DecidableEq ι] {S : ℕ}
    (A : Matrix ι ι ℝ) (C : Matrix ι (Fin S) ℝ) (U : Finset ι) :
    ((bordered A C).submatrix
      (Subtype.val : ↥(U.disjSum (Finset.univ : Finset (Fin S))) → ι ⊕ Fin S)
      Subtype.val).det =
      (bordered (A.submatrix (Subtype.val : U → ι) Subtype.val)
        (C.submatrix Subtype.val id)).det := by
  let f : U ⊕ Fin S → ↥(U.disjSum (Finset.univ : Finset (Fin S))) :=
    Sum.elim (fun u => ⟨Sum.inl u.1, Finset.inl_mem_disjSum.mpr u.2⟩)
      (fun j => ⟨Sum.inr j, Finset.inr_mem_disjSum.mpr (Finset.mem_univ j)⟩)
  have hf : Function.Bijective f := by
    constructor
    · rintro (a | a) (b | b) h <;> have h' := congrArg Subtype.val h
      · simp only [f, Sum.elim_inl, Sum.inl.injEq] at h'
        exact congrArg Sum.inl (Subtype.ext h')
      · simp [f] at h'
      · simp [f] at h'
      · simp only [f, Sum.elim_inr, Sum.inr.injEq] at h'
        rw [h']
    · rintro ⟨x | j, hx⟩
      · exact ⟨Sum.inl ⟨x, Finset.inl_mem_disjSum.mp hx⟩, rfl⟩
      · exact ⟨Sum.inr j, rfl⟩
  rw [← det_submatrix_equiv_self (Equiv.ofBijective f hf)]
  congr 1
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> rfl

/-- **Expansion of the perturbed bordered determinant.** For `ε ≠ 0`,
`|[[A - εI, C], [Cᵀ, 0]]| = ∑_U (-ε)^{n-|U|} |[[A_U, C_U], [C_Uᵀ, 0]]|`. -/
theorem bordered_perturbation_expansion {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ℕ}
    (A : Matrix ι ι ℝ) (C : Matrix ι (Fin S) ℝ) {ε : ℝ} (hε : ε ≠ 0) :
    (bordered (A - ε • (1 : Matrix ι ι ℝ)) C).det =
      ∑ U : Finset ι, (-ε) ^ (Fintype.card ι - U.card) *
        (bordered (A.submatrix (Subtype.val : U → ι) Subtype.val)
          (C.submatrix Subtype.val id)).det := by
  set H := bordered A C
  set d : ℝ → ι ⊕ Fin S → ℝ := fun δ => Sum.elim (fun _ => -ε) (fun _ => -δ) with hd
  have hdc : Continuous d := by
    apply continuous_pi
    rintro (i | j)
    · exact continuous_const
    · exact continuous_neg
  set F : ℝ → ℝ := fun δ => (H + diagonal (d δ)).det
  set G : ℝ → ℝ := fun δ => ∑ W : Finset (ι ⊕ Fin S),
    (∏ i ∈ Wᶜ, d δ i) * (H.submatrix (Subtype.val : W → _) Subtype.val).det
  have hFc : Continuous F := (continuous_const.add (Continuous.matrix_diagonal hdc)).matrix_det
  have hGc : Continuous G := continuous_finsetSum _ fun W _ =>
    (continuous_finsetProd _ fun i _ => (continuous_apply i).comp hdc).mul continuous_const
  have hFG : F = G := by
    apply Continuous.ext_on (dense_compl_singleton (0 : ℝ)) hFc hGc
    intro δ hδ
    apply det_add_diagonal_expansion
    rintro (i | j)
    · simpa [hd] using hε
    · simpa [hd] using hδ
  have hF0 : F 0 = (bordered (A - ε • (1 : Matrix ι ι ℝ)) C).det := by
    simp only [F]
    congr 1
    ext a b
    rcases a with a | a <;> rcases b with b | b <;>
      simp [H, hd, bordered, Matrix.one_apply, diagonal_apply, sub_eq_add_neg]
    split_ifs <;> simp_all
  rw [← hF0, hFG]
  simp only [G]
  -- only `W` containing every border index survive
  have hzero : ∀ W : Finset (ι ⊕ Fin S), W ∉ Finset.univ.image
      (fun U : Finset ι => U.disjSum (Finset.univ : Finset (Fin S))) →
      (∏ i ∈ Wᶜ, d 0 i) * (H.submatrix (Subtype.val : W → _) Subtype.val).det = 0 := by
    intro W hW
    have : ∃ j, Sum.inr j ∉ W := by
      by_contra hc
      push Not at hc
      apply hW
      refine Finset.mem_image.mpr ⟨Finset.univ.filter (fun a => Sum.inl a ∈ W),
        Finset.mem_univ _, ?_⟩
      ext x
      rcases x with a | j
      · simp
      · simp [hc j]
    obtain ⟨j, hj⟩ := this
    rw [Finset.prod_eq_zero (i := Sum.inr j) (Finset.mem_compl.mpr hj) (by simp [hd]), zero_mul]
  rw [← Finset.sum_subset (Finset.subset_univ _) (fun W _ hW => hzero W hW),
    Finset.sum_image (fun U _ V _ h => by
      ext a
      have := congrArg (fun W : Finset (ι ⊕ Fin S) => Sum.inl a ∈ W) h
      simpa using this)]
  refine Finset.sum_congr rfl fun U _ => ?_
  rw [det_bordered_submatrix_disjSum]
  congr 1
  have hc : (U.disjSum (Finset.univ : Finset (Fin S)))ᶜ = Uᶜ.map Function.Embedding.inl := by
    ext x
    rcases x with a | j <;> simp
  rw [hc, Finset.prod_map]
  simp [hd, Finset.card_compl]

/-- An injective `U × S` matrix has `S ≤ |U|`. -/
theorem card_le_of_mulVec_injective {U : Type*} [Fintype U] {S : ℕ} {C : Matrix U (Fin S) ℝ}
    (h : ∀ μ, C *ᵥ μ = 0 → μ = 0) : S ≤ Fintype.card U := by
  have hinj : Function.Injective C.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    exact fun μ hμ => h μ hμ
  have := LinearMap.finrank_le_finrank_of_injective hinj
  simpa using this

/-- A square (`|U| = S`) injective matrix has injective transpose. -/
theorem transpose_injective_of_card_eq {U : Type*} [Fintype U] {S : ℕ}
    {C : Matrix U (Fin S) ℝ} (h : ∀ μ, C *ᵥ μ = 0 → μ = 0) (hc : Fintype.card U = S) :
    ∀ y, Cᵀ *ᵥ y = 0 → y = 0 := by
  classical
  have hinj : Function.Injective C.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    exact fun μ hμ => h μ hμ
  have hsurj : Function.Surjective C.mulVecLin :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [hc])).mp hinj
  have hrank : C.rank = Fintype.card U := by
    rw [Matrix.rank, LinearMap.range_eq_top.mpr hsurj, finrank_top,
      Module.finrank_fintype_fun_eq_card]
  have hrankT : Cᵀ.rank = Fintype.card U := by rw [Matrix.rank_transpose, hrank]
  have hrn := LinearMap.finrank_range_add_finrank_ker Cᵀ.mulVecLin
  rw [← Matrix.rank, hrankT, Module.finrank_fintype_fun_eq_card] at hrn
  have hker : LinearMap.ker Cᵀ.mulVecLin = ⊥ :=
    Submodule.finrank_eq_zero.mp (by omega)
  intro y hy
  have : y ∈ LinearMap.ker Cᵀ.mulVecLin := hy
  rw [hker] at this
  exact this

/-- For a square injective border the bordered determinant has sign `(-1)^{|U|}`, whatever `A`. -/
theorem bordered_sign_pos_square {U : Type*} [Fintype U] [DecidableEq U] {S : ℕ}
    (A : Matrix U U ℝ) {C : Matrix U (Fin S) ℝ} (h : ∀ μ, C *ᵥ μ = 0 → μ = 0)
    (hc : Fintype.card U = S) : 0 < (-1) ^ Fintype.card U * (bordered A C).det :=
  bordered_sign_pos (fun z hz hz0 => absurd (transpose_injective_of_card_eq h hc z hz) hz0) h

/-- Reindexing the first block of a bordered matrix leaves its determinant unchanged. -/
theorem det_bordered_reindex {U V : Type*} [Fintype U] [DecidableEq U] [Fintype V]
    [DecidableEq V] {S : ℕ} (σ : V ≃ U) (A : Matrix U U ℝ) (C : Matrix U (Fin S) ℝ) :
    (bordered (A.submatrix σ σ) (C.submatrix σ id)).det = (bordered A C).det := by
  rw [← det_submatrix_equiv_self (Equiv.sumCongr σ (Equiv.refl (Fin S))) (bordered A C)]
  congr 1
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> rfl

/-- The printed hypothesis of Theorem M.D.3(ii) gives the sign of the bordered determinant for
every injective choice of rows `g`, indexed by any finite type. -/
theorem bordered_sign_of_printed {N S : ℕ} {M : Matrix (Fin N) (Fin N) ℝ}
    {B : Matrix (Fin N) (Fin S) ℝ}
    (hP : ∀ r (h : r ≤ N) (π : Equiv.Perm (Fin N)), S < r →
      0 ≤ (-1) ^ r * (borderedMatrix (permuteMatrix M π) (B.submatrix π id) r h).det)
    {U : Type*} [Fintype U] [DecidableEq U] {g : U → Fin N} (hg : Function.Injective g)
    (hU : S < Fintype.card U) :
    0 ≤ (-1) ^ Fintype.card U * (bordered (M.submatrix g g) (B.submatrix g id)).det := by
  set k := Fintype.card U
  set σ : Fin k ≃ U := (Fintype.equivFin U).symm
  have hk : k ≤ N := by simpa [k] using Fintype.card_le_of_injective g hg
  have hf : Function.Injective (g ∘ σ) := hg.comp σ.injective
  obtain ⟨π, hπ⟩ := exists_perm_extend hk (g ∘ σ) hf
  have := hP k hk π hU
  have e : borderedMatrix (permuteMatrix M π) (B.submatrix π id) k hk =
      bordered ((M.submatrix g g).submatrix σ σ) ((B.submatrix g id).submatrix σ id) := by
    ext a b
    rcases a with a | a <;> rcases b with b | b <;>
      simp [borderedMatrix, bordered, leadingMinorMatrix, permuteMatrix, hπ]
  rw [e, det_bordered_reindex] at this
  exact this

/-- **Theorem M.D.3(ii)** (MWG, p. 938), with `{z : Bᵀz = 0}`. Let `M` be symmetric and suppose
some `S` rows of `B` are linearly independent (`B` has rank `S`). Then `M` is negative
semidefinite on `{z : Bᵀz = 0}` iff `(-1)^r |[[ₜM^πₜ, ₜB^π], [(ₜB^π)ᵀ, 0]]| ≥ 0` for every
`r = S+1, …, N` and every permutation `π`. -/
theorem theorem_M_D_3_ii {N S : ℕ} {M : Matrix (Fin N) (Fin N) ℝ} (hM : M.IsSymm)
    (B : Matrix (Fin N) (Fin S) ℝ) {e₀ : Fin S → Fin N} (he₀ : Function.Injective e₀)
    (hB : (B.submatrix e₀ id).det ≠ 0) :
    (∀ z, Bᵀ *ᵥ z = 0 → z ⬝ᵥ M *ᵥ z ≤ 0) ↔
      ∀ r (h : r ≤ N) (π : Equiv.Perm (Fin N)), S < r →
        0 ≤ (-1) ^ r * (borderedMatrix (permuteMatrix M π) (B.submatrix π id) r h).det := by
  refine ⟨fun hNSD r h π _ => theorem_M_D_3_ii_forward B hNSD r h π, fun hP => ?_⟩
  have hSN : S ≤ N := by simpa using Fintype.card_le_of_injective e₀ he₀
  obtain ⟨π₀, hπ₀⟩ := exists_perm_extend hSN e₀ he₀
  set M' := permuteMatrix M π₀
  set B' := B.submatrix π₀ id
  have hB' : (B'.submatrix (Fin.castLE hSN) id).det ≠ 0 := by
    have e : B'.submatrix (Fin.castLE hSN) id = B.submatrix e₀ id := by
      ext i j
      simp [B', hπ₀]
    rwa [e]
  -- for every `ε > 0`, `M' - εI` is negative definite on `{z : B'ᵀz = 0}`
  have hND : ∀ ε : ℝ, 0 < ε → ∀ z, B'ᵀ *ᵥ z = 0 → z ≠ 0 →
      z ⬝ᵥ (M' - ε • (1 : Matrix (Fin N) (Fin N) ℝ)) *ᵥ z < 0 := by
    intro ε hε
    have hsymm : (M' - ε • (1 : Matrix (Fin N) (Fin N) ℝ)).IsSymm := by
      ext i j
      by_cases hij : i = j
      · subst hij; rfl
      · simp [M', permuteMatrix, hij, Ne.symm hij, hM.apply]
    apply (theorem_M_D_3_i hsymm B' hSN hB').mpr
    intro r h hr
    set e : Fin r → Fin N := π₀ ∘ Fin.castLE h
    have he : Function.Injective e := π₀.injective.comp (Fin.castLE_injective h)
    set A := M.submatrix e e
    set C := B.submatrix e id
    have hbm : borderedMatrix (M' - ε • (1 : Matrix (Fin N) (Fin N) ℝ)) B' r h =
        bordered (A - ε • (1 : Matrix (Fin r) (Fin r) ℝ)) C := by
      ext a b
      rcases a with a | a <;> rcases b with b | b <;>
        simp [borderedMatrix, bordered, leadingMinorMatrix, M', B', A, C, e, permuteMatrix,
          Matrix.one_apply, Fin.castLE_inj]
    rw [hbm, bordered_perturbation_expansion A C hε.ne', Finset.mul_sum]
    -- each term is `ε^{r-|U|} (-1)^{|U|} |bordered_U| ≥ 0`
    have hterm : ∀ U : Finset (Fin r),
        (-1) ^ r * ((-ε) ^ (Fintype.card (Fin r) - U.card) *
          (bordered (A.submatrix (Subtype.val : U → Fin r) Subtype.val)
            (C.submatrix Subtype.val id)).det) =
        ε ^ (r - U.card) * ((-1) ^ U.card *
          (bordered (A.submatrix (Subtype.val : U → Fin r) Subtype.val)
            (C.submatrix Subtype.val id)).det) := by
      intro U
      have hU : U.card ≤ r := by simpa using Finset.card_le_univ U
      rw [Fintype.card_fin, neg_pow]
      have : (-1 : ℝ) ^ r = (-1) ^ U.card * (-1) ^ (r - U.card) := by
        rw [← pow_add, Nat.add_sub_cancel' hU]
      rw [this]
      have h2 : ((-1 : ℝ) ^ (r - U.card)) * (-1) ^ (r - U.card) = 1 := by
        rw [← mul_pow]; norm_num
      linear_combination (ε ^ (r - U.card) * ((-1) ^ U.card *
        (bordered (A.submatrix (Subtype.val : U → Fin r) Subtype.val)
          (C.submatrix Subtype.val id)).det)) * h2
    simp only [hterm]
    have hnonneg : ∀ U : Finset (Fin r), 0 ≤ (-1) ^ U.card *
        (bordered (A.submatrix (Subtype.val : U → Fin r) Subtype.val)
          (C.submatrix Subtype.val id)).det := by
      intro U
      by_cases hinj : ∀ μ, (C.submatrix (Subtype.val : U → Fin r) id) *ᵥ μ = 0 → μ = 0
      · have hcard := card_le_of_mulVec_injective hinj
        rw [Fintype.card_coe] at hcard
        rcases eq_or_lt_of_le hcard with heq | hlt
        · have := bordered_sign_pos_square (A.submatrix (Subtype.val : U → Fin r) Subtype.val)
            hinj (by rw [Fintype.card_coe]; exact heq.symm)
          rw [Fintype.card_coe] at this
          exact this.le
        · have := bordered_sign_of_printed hP (g := e ∘ Subtype.val)
            (he.comp Subtype.val_injective) (by rw [Fintype.card_coe]; exact hlt)
          rw [Fintype.card_coe] at this
          exact this
      · rw [bordered_det_eq_zero_of_not_injective hinj, mul_zero]
    -- the term of the first `S` rows is positive
    set U₀ : Finset (Fin r) := Finset.univ.map (Fin.castLEEmb hr.le)
    have hU₀card : U₀.card = S := by simp [U₀]
    have hU₀inj : ∀ μ, (C.submatrix (Subtype.val : U₀ → Fin r) id) *ᵥ μ = 0 → μ = 0 := by
      intro μ hμ
      by_contra hne
      apply hB
      rw [← exists_mulVec_eq_zero_iff]
      refine ⟨μ, hne, funext fun i => ?_⟩
      have hmem : Fin.castLE hr.le i ∈ U₀ := Finset.mem_map_of_mem _ (Finset.mem_univ i)
      have := congrFun hμ ⟨Fin.castLE hr.le i, hmem⟩
      simpa [C, e, mulVec, dotProduct, hπ₀] using this
    have hU₀pos := bordered_sign_pos_square (A.submatrix (Subtype.val : U₀ → Fin r) Subtype.val)
      hU₀inj (by rw [Fintype.card_coe]; exact hU₀card)
    rw [Fintype.card_coe] at hU₀pos
    apply lt_of_lt_of_le (mul_pos (pow_pos hε (r - U₀.card)) hU₀pos)
    exact Finset.single_le_sum (f := fun U : Finset (Fin r) => ε ^ (r - U.card) *
      ((-1) ^ U.card * (bordered (A.submatrix (Subtype.val : U → Fin r) Subtype.val)
        (C.submatrix Subtype.val id)).det))
      (fun U _ => mul_nonneg (pow_nonneg hε.le _) (hnonneg U)) (Finset.mem_univ U₀)
  -- transfer back to `M`
  intro z hz
  set z' : Fin N → ℝ := fun i => z (π₀ i)
  have hz' : B'ᵀ *ᵥ z' = 0 := by
    funext j
    have := congrFun hz j
    simp only [mulVec, dotProduct, transpose_apply, Pi.zero_apply] at this ⊢
    rw [← this]
    exact Equiv.sum_comp π₀ (fun i => B i j * z i)
  have hq : z' ⬝ᵥ M' *ᵥ z' = z ⬝ᵥ M *ᵥ z := by
    simp only [dotProduct, mulVec, M', permuteMatrix, submatrix_apply, z']
    rw [← Equiv.sum_comp π₀ (fun i => z i * ∑ j, M i j * z j)]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    exact Equiv.sum_comp π₀ (fun j => M (π₀ i) j * z j)
  have hzz : z' ⬝ᵥ z' = z ⬝ᵥ z := by
    simp only [dotProduct, z']
    exact Equiv.sum_comp π₀ (fun i => z i * z i)
  by_cases hz0 : z' = 0
  · have : z = 0 := by
      funext i
      have := congrFun hz0 (π₀.symm i)
      simpa [z'] using this
    rw [this, mulVec_zero, dotProduct_zero]
  by_contra hc
  push Not at hc
  have hpos := dotProduct_self_pos_of_ne_zero hz0
  set ε := (z ⬝ᵥ M *ᵥ z) / (2 * (z' ⬝ᵥ z'))
  have hε : 0 < ε := div_pos hc (by linarith)
  have := hND ε hε z' hz' hz0
  rw [sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul, hq] at this
  have e2 : ε * (z' ⬝ᵥ z') = (z ⬝ᵥ M *ᵥ z) / 2 := by
    simp only [ε]
    field_simp
  linarith

end MWG.ConsumerChoice
