/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGConsumerChoice.MatrixDefiniteness
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.Basic.Complex.BigOperators

/-!
# Negative definite matrices: Theorem M.D.1, dominant diagonals, Theorem M.D.5(i)–(iv)

MWG, Mathematical Appendix, Section M.D, pp. 935–940.

* Characteristic values (roots of `|M - λI| = 0`, complex in general); those of a symmetric
  matrix are real (p. 935).
* Theorem M.D.1: (i) `M` is negative definite iff `M + Mᵀ` is (also for semidefiniteness);
  (ii) a symmetric `M` is negative definite iff all its characteristic values are negative;
  (iii) `M` is negative definite iff `M⁻¹` is; (iv) if `M` is negative definite and `K` is
  diagonal with positive entries, `KM` is stable (every characteristic value has negative real
  part). The book proves (iv) through a cited Lyapunov criterion; here it is proved directly.
* Footnote 9 (p. 938): `|-ₜMₜ| = (-1)^r |ₜMₜ|`.
* Example M.D.1 (p. 937), as statements about `2 × 2` symmetric matrices.
* Definitions M.D.2 (dominant diagonal) and M.D.3 (gross substitute sign pattern) and
  Theorem M.D.5(i)–(iv) (pp. 939–940).
-/

namespace MWG.ConsumerChoice

open Matrix

variable {n : Type*} [Fintype n]

/-- A nonzero real vector has positive squared length. -/
theorem dotProduct_self_pos_of_ne_zero {v : n → ℝ} (hv : v ≠ 0) : 0 < v ⬝ᵥ v := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hv (funext hc)
  apply lt_of_lt_of_le (mul_self_pos.mpr hi)
  exact Finset.single_le_sum (f := fun j => v j * v j) (fun j _ => mul_self_nonneg (v j))
    (Finset.mem_univ i)

/-- The quadratic forms of `M` and `Mᵀ` agree: `z·Mᵀz = z·Mz`. -/
theorem dotProduct_transpose_mulVec (M : Matrix n n ℝ) (z : n → ℝ) :
    z ⬝ᵥ Mᵀ.mulVec z = z ⬝ᵥ M.mulVec z := by
  rw [mulVec_transpose, dotProduct_comm, ← dotProduct_mulVec]

/-- **Theorem M.D.1(i)** (MWG, p. 936). `M` is negative definite iff the symmetric matrix
`M + Mᵀ` is negative definite. -/
theorem theorem_M_D_1_i (M : Matrix n n ℝ) : NegDef M ↔ NegDef (M + Mᵀ) := by
  have h : ∀ z : n → ℝ, z ⬝ᵥ (M + Mᵀ).mulVec z = 2 * (z ⬝ᵥ M.mulVec z) := by
    intro z
    rw [add_mulVec, dotProduct_add, dotProduct_transpose_mulVec]
    ring
  constructor
  · intro hM z hz
    rw [h]
    linarith [hM z hz]
  · intro hM z hz
    have := hM z hz
    rw [h] at this
    linarith

/-- **Theorem M.D.1(i)** (MWG, p. 936), semidefinite version (used in Exercise 2.F.9(a)). -/
theorem theorem_M_D_1_i_semidef (M : Matrix n n ℝ) : NegSemidef M ↔ NegSemidef (M + Mᵀ) := by
  have h : ∀ z : n → ℝ, z ⬝ᵥ (M + Mᵀ).mulVec z = 2 * (z ⬝ᵥ M.mulVec z) := by
    intro z
    rw [add_mulVec, dotProduct_add, dotProduct_transpose_mulVec]
    ring
  constructor
  · intro hM z
    rw [h]
    linarith [hM z]
  · intro hM z
    have := hM z
    rw [h] at this
    linarith

/-- **Section M.D** (MWG, p. 935). `μ ∈ ℂ` is a characteristic value (eigenvalue) of the real
matrix `M`: `|M - μI| = 0`. -/
def IsCharacteristicValue [DecidableEq n] (M : Matrix n n ℝ) (μ : ℂ) : Prop :=
  (M.map Complex.ofReal - μ • (1 : Matrix n n ℂ)).det = 0

/-- A real number is a characteristic value iff `|M - μI| = 0` over `ℝ`. -/
theorem isCharacteristicValue_ofReal_iff [DecidableEq n] (M : Matrix n n ℝ) (μ : ℝ) :
    IsCharacteristicValue M μ ↔ (M - μ • (1 : Matrix n n ℝ)).det = 0 := by
  have : M.map Complex.ofReal - (μ : ℂ) • (1 : Matrix n n ℂ) =
      (M - μ • (1 : Matrix n n ℝ)).map Complex.ofReal := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  rw [IsCharacteristicValue, this]
  rw [show ((M - μ • (1 : Matrix n n ℝ)).map Complex.ofReal).det =
    Complex.ofRealHom (M - μ • (1 : Matrix n n ℝ)).det from
      (RingHom.map_det Complex.ofRealHom _).symm]
  simp

/-- **Section M.D** (MWG, p. 935). The characteristic values of a symmetric real matrix are
real. -/
theorem isCharacteristicValue_real [DecidableEq n] {M : Matrix n n ℝ} (hM : M.IsSymm) {μ : ℂ}
    (hμ : IsCharacteristicValue M μ) : μ.im = 0 := by
  obtain ⟨z, hz, hzero⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hμ
  set A := M.map Complex.ofReal with hA
  have hH : A.IsHermitian := by
    ext i j
    simp [hA, Matrix.conjTranspose_apply, hM.apply i j]
  have heig : A *ᵥ z = μ • z := by
    rw [sub_mulVec, sub_eq_zero, smul_mulVec, one_mulVec] at hzero
    exact hzero
  have h1 : star z ⬝ᵥ A *ᵥ z = μ * (star z ⬝ᵥ z) := by
    rw [heig, dotProduct_smul, smul_eq_mul]
  have h2 := hH.star_dotProduct_mulVec_comm z z
  rw [h1, star_mul', star_dotProduct, star_star] at h2
  have hne : star z ⬝ᵥ z ≠ 0 := by
    have hre : (star z ⬝ᵥ z).re = ∑ i, Complex.normSq (z i) := by
      simp only [dotProduct, Complex.re_sum, Pi.star_apply, RCLike.star_def, Complex.mul_re,
        Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
      exact Finset.sum_congr rfl fun i _ => by ring
    obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hz (funext hc)
    have hpos : 0 < ∑ i, Complex.normSq (z i) :=
      lt_of_lt_of_le (Complex.normSq_pos.mpr hi) (Finset.single_le_sum
        (f := fun j => Complex.normSq (z j)) (fun j _ => Complex.normSq_nonneg _)
        (Finset.mem_univ i))
    intro h0
    rw [h0, Complex.zero_re] at hre
    linarith
  have hreal : star (star z ⬝ᵥ z) = star z ⬝ᵥ z := by
    simp only [dotProduct, star_sum, star_mul', Pi.star_apply, star_star]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have h3 : (star μ - μ) * (star z ⬝ᵥ z) = 0 := by
    rw [sub_mul, h2, hreal, sub_self]
  rcases mul_eq_zero.mp h3 with h | h
  · have := congrArg Complex.im h
    simp at this
    linarith
  · exact absurd h hne

/-- **Theorem M.D.1(ii)** (MWG, p. 936). A symmetric matrix is negative definite iff all of its
(real) characteristic values are negative. -/
theorem theorem_M_D_1_ii [DecidableEq n] {M : Matrix n n ℝ} (hM : M.IsSymm) :
    NegDef M ↔ ∀ μ : ℝ, (M - μ • (1 : Matrix n n ℝ)).det = 0 → μ < 0 := by
  constructor
  · intro h μ hμ
    obtain ⟨v, hv, hzero⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hμ
    rw [sub_mulVec, sub_eq_zero, smul_mulVec, one_mulVec] at hzero
    have := h v hv
    rw [hzero, dotProduct_smul, smul_eq_mul] at this
    have hpos : 0 < v ⬝ᵥ v := dotProduct_self_pos_of_ne_zero hv
    nlinarith
  · intro h
    have hneg : (-M).IsHermitian := by
      ext i j
      simp [Matrix.conjTranspose_apply, hM.apply i j]
    have hpd : (-M).PosDef := by
      rw [hneg.posDef_iff_eigenvalues_pos]
      intro i
      set v := hneg.eigenvectorBasis i
      have hv := hneg.mulVec_eigenvectorBasis i
      have hv0 : (⇑v : n → ℝ) ≠ 0 := by
        intro h0
        have := (hneg.eigenvectorBasis).orthonormal.ne_zero i
        apply this
        ext j
        simpa using congrFun h0 j
      have hdet : (M - (-hneg.eigenvalues i) • (1 : Matrix n n ℝ)).det = 0 := by
        rw [← Matrix.exists_mulVec_eq_zero_iff]
        refine ⟨⇑v, hv0, ?_⟩
        rw [sub_mulVec, smul_mulVec, one_mulVec]
        rw [neg_mulVec] at hv
        have : M *ᵥ ⇑v = -(hneg.eigenvalues i • ⇑v) := by rw [← hv, neg_neg]
        rw [this, neg_smul, sub_neg_eq_add, neg_add_cancel]
      have := h _ hdet
      linarith
    have hsymm : (-M).IsSymm := by
      ext i j
      simp [hM.apply i j]
    rw [← (posDefMWG_iff_posDef hsymm)] at hpd
    have := (posDefMWG_iff_neg (-M)).mp hpd
    rwa [neg_neg] at this

/-- **Theorem M.D.1(ii)** (MWG, p. 936), with characteristic values as complex roots: a
symmetric matrix is negative definite iff every characteristic value has negative real part
(all of them being real). -/
theorem theorem_M_D_1_ii_complex [DecidableEq n] {M : Matrix n n ℝ} (hM : M.IsSymm) :
    NegDef M ↔ ∀ μ : ℂ, IsCharacteristicValue M μ → μ.re < 0 := by
  rw [theorem_M_D_1_ii hM]
  constructor
  · intro h μ hμ
    have him := isCharacteristicValue_real hM hμ
    have hμ' : μ = (μ.re : ℂ) := Complex.ext rfl (by simp [him])
    rw [hμ', isCharacteristicValue_ofReal_iff] at hμ
    exact h _ hμ
  · intro h μ hμ
    have := h μ ((isCharacteristicValue_ofReal_iff M μ).mpr hμ)
    simpa using this

/-- A negative definite matrix is nonsingular. -/
theorem NegDef.det_ne_zero [DecidableEq n] {M : Matrix n n ℝ} (h : NegDef M) : M.det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hzero⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have := h v hv
  rw [hzero, dotProduct_zero] at this
  exact lt_irrefl _ this

/-- The forward half of Theorem M.D.1(iii). -/
theorem NegDef.inv [DecidableEq n] {M : Matrix n n ℝ} (h : NegDef M) : NegDef M⁻¹ := by
  have hdet := h.det_ne_zero
  have hU : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet
  intro z hz
  set y := M⁻¹ *ᵥ z with hy
  have hz' : M *ᵥ y = z := by rw [hy, mulVec_mulVec, mul_nonsing_inv _ hU, one_mulVec]
  have hy0 : y ≠ 0 := by
    intro h0
    rw [h0, mulVec_zero] at hz'
    exact hz hz'.symm
  calc z ⬝ᵥ y = (M *ᵥ y) ⬝ᵥ y := by rw [hz']
    _ = y ⬝ᵥ M *ᵥ y := dotProduct_comm _ _
    _ < 0 := h y hy0

/-- **Theorem M.D.1(iii)** (MWG, p. 936). `M` is negative definite iff `M⁻¹` is. -/
theorem theorem_M_D_1_iii [DecidableEq n] (M : Matrix n n ℝ) : NegDef M ↔ NegDef M⁻¹ := by
  refine ⟨NegDef.inv, fun h => ?_⟩
  have h1 := h.det_ne_zero
  rw [Matrix.det_nonsing_inv] at h1
  have hU : IsUnit M.det := isUnit_iff_ne_zero.mpr (by
    intro h0
    rw [h0, Ring.inverse_zero] at h1
    exact h1 rfl)
  have := h.inv
  rwa [Matrix.nonsing_inv_nonsing_inv _ hU] at this

/-- **Section M.D** (MWG, p. 936, footnote 7). A real matrix is stable if all its
characteristic values have negative real parts. -/
def Stable [DecidableEq n] (A : Matrix n n ℝ) : Prop :=
  ∀ μ : ℂ, IsCharacteristicValue A μ → μ.re < 0

/-- **Theorem M.D.1(iv)** (MWG, p. 936). If `M` is negative definite, then for every diagonal
matrix `K` with positive diagonal entries, `KM` is stable. -/
theorem theorem_M_D_1_iv [DecidableEq n] {M : Matrix n n ℝ} (hM : NegDef M) (k : n → ℝ)
    (hk : ∀ i, 0 < k i) : Stable (Matrix.diagonal k * M) := by
  intro μ hμ
  obtain ⟨z, hz, hzero⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hμ
  have heig : (Matrix.diagonal k * M).map Complex.ofReal *ᵥ z = μ • z := by
    rw [sub_mulVec, sub_eq_zero, smul_mulVec, one_mulVec] at hzero
    exact hzero
  have hrow : ∀ i, ∑ j, (M i j : ℂ) * z j = μ * z i / k i := by
    intro i
    have := congrFun heig i
    simp only [mulVec, dotProduct, Matrix.map_apply, Matrix.diagonal_mul, Complex.ofReal_mul,
      Pi.smul_apply, smul_eq_mul] at this
    have hki : (k i : ℂ) ≠ 0 := by exact_mod_cast (hk i).ne'
    rw [eq_div_iff hki, ← this, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  set a : n → ℝ := fun i => (z i).re
  set b : n → ℝ := fun i => (z i).im
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_contra hc
    push Not at hc
    apply hz
    funext i
    apply Complex.ext
    · simpa [a] using congrFun hc.1 i
    · simpa [b] using congrFun hc.2 i
  -- the real part of `z̄·Mz` is `a·Ma + b·Mb < 0`
  have hre : (∑ i, star (z i) * ∑ j, (M i j : ℂ) * z j).re =
      a ⬝ᵥ M *ᵥ a + b ⬝ᵥ M *ᵥ b := by
    simp only [Complex.re_sum, Finset.mul_sum, dotProduct, mulVec, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp [a, b, Complex.mul_re, Complex.mul_im]
  have hneg : a ⬝ᵥ M *ᵥ a + b ⬝ᵥ M *ᵥ b < 0 := by
    rcases hab with h | h
    · linarith [hM a h, hM.negSemidef b]
    · linarith [hM.negSemidef a, hM b h]
  -- and it equals `Re μ · ∑ |zᵢ|²/kᵢ`
  have hT : (∑ i, star (z i) * ∑ j, (M i j : ℂ) * z j) =
      μ * ((∑ i, Complex.normSq (z i) / k i : ℝ) : ℂ) := by
    simp only [hrow, Complex.ofReal_sum, Complex.ofReal_div, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.normSq_eq_conj_mul_self]
    simp only [RCLike.star_def]
    have hki : (k i : ℂ) ≠ 0 := by exact_mod_cast (hk i).ne'
    field_simp
  have hTpos : 0 < ∑ i, Complex.normSq (z i) / k i := by
    obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hz (funext hc)
    apply lt_of_lt_of_le (div_pos (Complex.normSq_pos.mpr hi) (hk i))
    exact Finset.single_le_sum (f := fun i => Complex.normSq (z i) / k i)
      (fun j _ => div_nonneg (Complex.normSq_nonneg _) (hk j).le) (Finset.mem_univ i)
  rw [hT, Complex.re_mul_ofReal] at hre
  rw [← hre] at hneg
  by_contra hc
  push Not at hc
  have := mul_nonneg hc hTpos.le
  linarith

/-- **Footnote 9** (MWG, p. 938). `|-A| = (-1)^r |A|` for an `r × r` matrix `A`. -/
theorem det_neg_eq_pow (r : ℕ) (A : Matrix (Fin r) (Fin r) ℝ) : (-A).det = (-1) ^ r * A.det := by
  rw [Matrix.det_neg, Fintype.card_fin]

/-! ### Example M.D.1: `2 × 2` symmetric matrices -/

/-- The quadratic form of a symmetric `2 × 2` matrix. -/
theorem quadratic_two_by_two (f11 f12 f22 : ℝ) (z : Fin 2 → ℝ) :
    z ⬝ᵥ (!![f11, f12; f12, f22]).mulVec z = f11 * z 0 ^ 2 + 2 * f12 * z 0 * z 1 + f22 * z 1 ^ 2
    := by
  simp [dotProduct, mulVec, Fin.sum_univ_two]
  ring

/-- **Example M.D.1** (MWG, p. 937). A symmetric `2 × 2` matrix `[f₁₁ f₁₂; f₁₂ f₂₂]` is negative
definite iff `f₁₁ < 0` and `f₁₁f₂₂ - f₁₂² > 0`. -/
theorem example_M_D_1_negDef (f11 f12 f22 : ℝ) :
    NegDef !![f11, f12; f12, f22] ↔ f11 < 0 ∧ 0 < f11 * f22 - f12 ^ 2 := by
  constructor
  · intro h
    have h1 := h ![1, 0] (by intro h0; simpa using congrFun h0 0)
    have h2 := h ![-f12, f11] (by
      intro h0
      have e1 := congrFun h0 1
      simp at e1
      have : f11 < 0 := by
        have := h1
        rw [quadratic_two_by_two] at this
        simpa using this
      linarith)
    rw [quadratic_two_by_two] at h1 h2
    norm_num at h1 h2
    refine ⟨h1, ?_⟩
    nlinarith
  · rintro ⟨h1, h2⟩ z hz
    rw [quadratic_two_by_two]
    have hz' : z 0 ≠ 0 ∨ z 1 ≠ 0 := by
      by_contra hc
      push Not at hc
      apply hz
      funext i
      fin_cases i
      · exact hc.1
      · exact hc.2
    -- f11 * Q = (f11 z0 + f12 z1)² + (f11 f22 - f12²) z1²
    have key : f11 * (f11 * z 0 ^ 2 + 2 * f12 * z 0 * z 1 + f22 * z 1 ^ 2) =
        (f11 * z 0 + f12 * z 1) ^ 2 + (f11 * f22 - f12 ^ 2) * z 1 ^ 2 := by ring
    have hpos : 0 < (f11 * z 0 + f12 * z 1) ^ 2 + (f11 * f22 - f12 ^ 2) * z 1 ^ 2 := by
      rcases hz' with h | h
      · by_cases h1' : z 1 = 0
        · rw [h1']
          have : f11 * z 0 ≠ 0 := mul_ne_zero h1.ne h
          simp only [mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
            zero_pow, mul_zero, add_zero]
          positivity
        · have := pow_pos (abs_pos.mpr h1') 2
          rw [sq_abs] at this
          nlinarith [sq_nonneg (f11 * z 0 + f12 * z 1)]
      · have := pow_pos (abs_pos.mpr h) 2
        rw [sq_abs] at this
        nlinarith [sq_nonneg (f11 * z 0 + f12 * z 1)]
    nlinarith

/-- **Example M.D.1** (MWG, p. 937). A symmetric `2 × 2` matrix is negative semidefinite iff
`f₁₁ ≤ 0`, `f₂₂ ≤ 0` and `f₁₁f₂₂ - f₁₂² ≥ 0`. -/
theorem example_M_D_1_negSemidef (f11 f12 f22 : ℝ) :
    NegSemidef !![f11, f12; f12, f22] ↔ f11 ≤ 0 ∧ f22 ≤ 0 ∧ 0 ≤ f11 * f22 - f12 ^ 2 := by
  constructor
  · intro h
    have h1 := h ![1, 0]
    have h2 := h ![0, 1]
    rw [quadratic_two_by_two] at h1 h2
    norm_num at h1 h2
    refine ⟨h1, h2, ?_⟩
    by_contra hc
    push Not at hc
    rcases lt_or_eq_of_le h1 with h1' | h1'
    · have h3 := h ![-f12, f11]
      rw [quadratic_two_by_two] at h3
      simp at h3
      nlinarith
    · rw [h1'] at hc
      have hf : f12 ≠ 0 := by
        intro h0
        rw [h0] at hc
        simp at hc
      have h3 := h ![(1 - f22) / (2 * f12), 1]
      rw [quadratic_two_by_two, h1'] at h3
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h3
      have e : 2 * f12 * ((1 - f22) / (2 * f12)) * 1 = 1 - f22 := by field_simp
      nlinarith
  · rintro ⟨h1, h2, h3⟩ z
    rw [quadratic_two_by_two]
    rcases lt_or_eq_of_le h1 with h1' | h1'
    · have key : f11 * (f11 * z 0 ^ 2 + 2 * f12 * z 0 * z 1 + f22 * z 1 ^ 2) =
          (f11 * z 0 + f12 * z 1) ^ 2 + (f11 * f22 - f12 ^ 2) * z 1 ^ 2 := by ring
      have : 0 ≤ f11 * (f11 * z 0 ^ 2 + 2 * f12 * z 0 * z 1 + f22 * z 1 ^ 2) := by
        rw [key]; positivity
      nlinarith
    · have hf : f12 = 0 := by
        rw [h1'] at h3
        nlinarith [sq_nonneg f12]
      rw [h1', hf]
      nlinarith [sq_nonneg (z 1)]

/-! ### Dominant diagonals and gross substitutes -/

/-- **Definition M.D.2** (MWG, p. 939). `M` has a dominant diagonal: there is `p ≫ 0` with
`|pᵢaᵢᵢ| > ∑_{j ≠ i} |pⱼaᵢⱼ|` for every `i`. -/
def DominantDiagonal [DecidableEq n] (M : Matrix n n ℝ) : Prop :=
  ∃ p : n → ℝ, (∀ i, 0 < p i) ∧
    ∀ i, ∑ j ∈ Finset.univ.erase i, |p j * M i j| < |p i * M i i|

/-- **Definition M.D.3** (MWG, p. 939). `M` has the gross substitute sign pattern: every
off-diagonal entry is positive. -/
def GrossSubstituteSign (M : Matrix n n ℝ) : Prop := ∀ i j, i ≠ j → 0 < M i j

/-- **Theorem M.D.5(i)** (MWG, p. 939). A matrix with a dominant diagonal is nonsingular. -/
theorem theorem_M_D_5_i [DecidableEq n] {M : Matrix n n ℝ} (h : DominantDiagonal M) :
    M.det ≠ 0 := by
  obtain ⟨p, hp, hdom⟩ := h
  have hD : (M * Matrix.diagonal p).det ≠ 0 := by
    apply det_ne_zero_of_sum_row_lt_diag
    intro k
    simp only [Matrix.mul_diagonal, Real.norm_eq_abs]
    have := hdom k
    simpa [mul_comm] using this
  rw [Matrix.det_mul, Matrix.det_diagonal] at hD
  exact left_ne_zero_of_mul hD

/-- **Theorem M.D.5(ii)** (MWG, p. 939). A symmetric matrix with a negative and dominant
diagonal is negative definite. -/
theorem theorem_M_D_5_ii [DecidableEq n] {M : Matrix n n ℝ} (hM : M.IsSymm)
    (hneg : ∀ i, M i i < 0) (hdom : DominantDiagonal M) : NegDef M := by
  rw [theorem_M_D_1_ii hM]
  intro μ hμ
  by_contra hc
  push Not at hc
  apply theorem_M_D_5_i (M := M - μ • 1) _ hμ
  obtain ⟨p, hp, hd⟩ := hdom
  refine ⟨p, hp, fun i => ?_⟩
  have hoff : ∀ j ∈ Finset.univ.erase i, (M - μ • (1 : Matrix n n ℝ)) i j = M i j := by
    intro j hj
    have : i ≠ j := fun h => (Finset.mem_erase.mp hj).1 h.symm
    simp [this]
  rw [Finset.sum_congr rfl fun j hj => by rw [hoff j hj]]
  have hii : (M - μ • (1 : Matrix n n ℝ)) i i = M i i - μ := by simp
  rw [hii]
  calc ∑ j ∈ Finset.univ.erase i, |p j * M i j| < |p i * M i i| := hd i
    _ ≤ |p i * (M i i - μ)| := by
      rw [abs_mul, abs_mul, abs_of_pos (hp i), abs_of_neg (hneg i),
        abs_of_neg (by linarith [hneg i])]
      nlinarith [hp i]

/-- **Theorem M.D.5(iii)** (MWG, p. 940). If `M` has the gross substitute sign pattern and
`Mp ≪ 0`, `Mᵀp ≪ 0` for some `p ≫ 0`, then `M` is negative definite. -/
theorem theorem_M_D_5_iii {M : Matrix n n ℝ} (hgs : GrossSubstituteSign M)
    {p : n → ℝ} (hp : ∀ i, 0 < p i) (h1 : ∀ i, (M *ᵥ p) i < 0) (h2 : ∀ i, (Mᵀ *ᵥ p) i < 0) :
    NegDef M := by
  classical
  rw [theorem_M_D_1_i]
  have hsplit : ∀ (f : n → ℝ) i, ∑ j, f j = f i + ∑ j ∈ Finset.univ.erase i, f j := by
    intro f i
    rw [Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have hdiag : ∀ i, M i i < 0 := by
    intro i
    have := h1 i
    simp only [mulVec, dotProduct] at this
    rw [hsplit _ i] at this
    have : 0 ≤ ∑ j ∈ Finset.univ.erase i, M i j * p j :=
      Finset.sum_nonneg fun j hj => mul_nonneg
        (hgs i j (fun h => (Finset.mem_erase.mp hj).1 h.symm)).le (hp j).le
    nlinarith [hp i]
  apply theorem_M_D_5_ii
  · ext i j
    simp [add_comm]
  · intro i
    simp only [Matrix.add_apply, Matrix.transpose_apply]
    linarith [hdiag i]
  · refine ⟨p, hp, fun i => ?_⟩
    have e1 := h1 i
    have e2 := h2 i
    simp only [mulVec, dotProduct, Matrix.transpose_apply] at e1 e2
    rw [hsplit _ i] at e1 e2
    have hoff : ∀ j ∈ Finset.univ.erase i, |p j * (M + Mᵀ) i j| = M i j * p j + M j i * p j := by
      intro j hj
      have hij : i ≠ j := fun h => (Finset.mem_erase.mp hj).1 h.symm
      simp only [Matrix.add_apply, Matrix.transpose_apply]
      rw [abs_of_pos (mul_pos (hp j) (add_pos (hgs i j hij) (hgs j i (Ne.symm hij))))]
      ring
    rw [Finset.sum_congr rfl hoff, Finset.sum_add_distrib]
    simp only [Matrix.add_apply, Matrix.transpose_apply]
    rw [abs_of_neg (mul_neg_of_pos_of_neg (hp i) (by linarith [hdiag i]))]
    linarith

/-- **Theorem M.D.5(iv)** (MWG, p. 940). If `M` has the gross substitute sign pattern and
`Mp = Mᵀp = 0` for some `p ≫ 0`, then deleting any row and the corresponding column gives a
negative definite matrix `M̂`. -/
theorem theorem_M_D_5_iv {N : ℕ} {M : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hgs : GrossSubstituteSign M) {p : Fin (N + 1) → ℝ} (hp : ∀ i, 0 < p i)
    (h1 : M *ᵥ p = 0) (h2 : Mᵀ *ᵥ p = 0) (k : Fin (N + 1)) :
    NegDef (M.submatrix k.succAbove k.succAbove) := by
  apply theorem_M_D_5_iii (p := fun i => p (k.succAbove i))
  · intro i j hij
    exact hgs _ _ (fun h => hij (Fin.succAbove_right_injective h))
  · exact fun i => hp _
  · intro i
    have := congrFun h1 (k.succAbove i)
    simp only [mulVec, dotProduct, Pi.zero_apply] at this
    rw [Fin.sum_univ_succAbove _ k] at this
    simp only [mulVec, dotProduct, Matrix.submatrix_apply]
    have hpos := mul_pos (hgs (k.succAbove i) k (Fin.succAbove_ne k i)) (hp k)
    linarith
  · intro i
    have := congrFun h2 (k.succAbove i)
    simp only [mulVec, dotProduct, Pi.zero_apply, Matrix.transpose_apply] at this
    rw [Fin.sum_univ_succAbove _ k] at this
    simp only [mulVec, dotProduct, Matrix.transpose_apply, Matrix.submatrix_apply]
    have hpos := mul_pos (hgs k (k.succAbove i) (Fin.succAbove_ne k i).symm) (hp k)
    linarith

end MWG.ConsumerChoice
