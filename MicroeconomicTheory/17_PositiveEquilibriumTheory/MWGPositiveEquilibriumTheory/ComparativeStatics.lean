/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.Figure17D1
import MWGClassicalDemand.AppendixME

/-!
# Comparative statics (MWG Section 17.G, pp. 616-620)

The system `ẑ(p; q) = 0` of `L - 1` equations (`p ∈ ℝ^{L-1}`, `p_L = 1`) with parameters
`q ∈ ℝ^N` is a map `ẑ : ℝ^{L-1} × ℝ^N → ℝ^{L-1}`; `D_p ẑ = ẑ' ∘ inl`, `D_q ẑ = ẑ' ∘ inr`.

* **(17.G.1)** (`eq_17_G_1`): if `ẑ` is strictly (e.g. continuously) differentiable at a regular
  solution `(p̄, q̄)`, the equilibrium price is locally a function `p(q)` with
  `Dp(q̄) = -[D_p ẑ]⁻¹ D_q ẑ` (Theorem M.E.1, Chapter 3's `theorem_M_E_1`). Any differentiable
  local solution satisfies `D_p ẑ ∘ Dp(q̄) = -D_q ẑ` (`eq_17_G_1_any`).
* **Proposition 17.G.2** (`proposition_17_G_2`): if `D_p ẑ` is negative definite then
  `(D_q ẑ dq)·(Dp(q̄) dq) ≥ 0` for every `dq` (the book prints `D_q ẑ` in the hypothesis and in the
  proof's first line, a misprint for `D_p ẑ`: corrections 35); the inverse of a negative definite
  matrix is negative definite (`cs_inv_nd`, Section M.D). With the existence of `p(·)`:
  `proposition_17_G_2_exists`. Instance: `proposition_17_G_2_instance`.
* p. 618: a shock that at fixed prices lowers only the excess demand of good 1 lowers its
  equilibrium price (`cs_single_market`).
* **Proposition 17.G.3** (`proposition_17_G_3`): if `D_p z(p̄; q̄)` (`L × L`) has negative diagonal
  and positive off-diagonal entries and `z` is homogeneous of degree zero, then `[D_p ẑ]⁻¹` has
  all entries negative. Matrix core (`cs_inv_neg`): a matrix `B` with positive off-diagonal
  entries and `Bw ≪ 0` for some `w ≫ 0` is nonsingular and `B⁻¹ ≪ 0`; it rests on the lemma
  `By ≥ 0`, `y ≠ 0` ⟹ `y ≪ 0` (`cs_neg_of_nonneg`), which replaces the book's appeal to the
  productive input-output matrix of Appendix 5.AA.
* pp. 618-619: with gross substitution, `D_q ẑ dq ≪ 0` gives `Dp(q̄) dq ≪ 0` (`cs_gs_shock`);
  the assumptions of 17.G.3 imply those of 17.G.2 (Exercise 17.F.12, `exercise_17_F_12`).
* **Footnote 53** (`footnote_17_53`): along a path `p(t)` of solutions of
  `ẑ(p; t) = tẑ(p; q̂) + (1 - t)ẑ(p; q̄) = 0` with the gross substitute pattern and
  `ẑ(·; q̂) ≪ ẑ(·; q̄)`, every price falls: `pₗ(q̂) < pₗ(q̄)`.
* The homotopy `ẑ(·, t) = (1 - t)ẑ(·; q̄) + tẑ(·; q̂)` (`csHomotopy`, p. 619) and its end points.
-/

namespace MWG.PositiveEquilibriumTheory

open MWG.ClassicalDemand Filter Topology

variable {n N : ℕ}

/-! ### Negative definite matrices -/

/-- A negative definite linear map (`v·Av < 0` for `v ≠ 0`) is injective, so `det A ≠ 0`. -/
theorem cs_det_ne_zero_of_nd (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (hnd : ∀ v, v ≠ 0 → v ⬝ᵥ A v < 0) : A.det ≠ 0 := by
  intro h0
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix'] at h0
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  rw [LinearMap.toMatrix'_mulVec] at hv
  have := hnd v hv0
  rw [show A v = 0 from hv, dotProduct_zero] at this
  exact lt_irrefl _ this

/-- **Section M.D** (MWG, used on p. 618). The inverse of a negative definite matrix is negative
definite: `w·A⁻¹w = (Av)·v < 0` for `w = Av ≠ 0`. -/
theorem cs_inv_nd {A : Matrix (Fin n) (Fin n) ℝ} (hnd : ∀ v, v ≠ 0 → v ⬝ᵥ A.mulVec v < 0) :
    IsUnit A.det ∧ ∀ w, w ≠ 0 → w ⬝ᵥ A⁻¹.mulVec w < 0 := by
  have hdet : A.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have := hnd v hv0
    rw [hv, dotProduct_zero] at this
    exact lt_irrefl _ this
  have hu : IsUnit A.det := isUnit_iff_ne_zero.2 hdet
  refine ⟨hu, fun w hw => ?_⟩
  set v := A⁻¹.mulVec w with hv
  have hAv : A.mulVec v = w := by rw [hv, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu,
    Matrix.one_mulVec]
  have hv0 : v ≠ 0 := by
    intro h; apply hw; rw [← hAv, h, Matrix.mulVec_zero]
  rw [← hAv, dotProduct_comm]
  exact hnd v hv0

/-! ### (17.G.1) -/

/-- **(17.G.1)** (MWG, p. 616). If `ẑ(p; q)` is strictly differentiable at `(p̄, q̄)` (e.g.
continuously differentiable), `ẑ(p̄; q̄) = 0` and the solution is regular (`|D_p ẑ| ≠ 0`), then
for `q` near `q̄` the equilibrium price vector near `p̄` is a function `p(q)` with
`Dp(q̄) = -[D_p ẑ(p̄; q̄)]⁻¹ D_q ẑ(p̄; q̄)`. -/
theorem eq_17_G_1 {zh : (Fin n → ℝ) × (Fin N → ℝ) → Fin n → ℝ}
    {f' : (Fin n → ℝ) × (Fin N → ℝ) →L[ℝ] (Fin n → ℝ)} {p : Fin n → ℝ} {q : Fin N → ℝ}
    (hf : HasStrictFDerivAt zh f' (p, q)) (h0 : zh (p, q) = 0)
    (hreg : (f'.comp (ContinuousLinearMap.inl ℝ (Fin n → ℝ) (Fin N → ℝ))).det ≠ 0) :
    ∃ η : (Fin N → ℝ) → Fin n → ℝ, LocallySolvable zh p q η ∧
      HasStrictFDerivAt η (-(f'.comp (ContinuousLinearMap.inl ℝ (Fin n → ℝ)
        (Fin N → ℝ))).inverse.comp (f'.comp (ContinuousLinearMap.inr ℝ (Fin n → ℝ)
          (Fin N → ℝ)))) q :=
  theorem_M_E_1 hf h0 ((isInvertible_iff_det_ne_zero _).2 hreg)

/-- **(17.G.1)** (MWG, p. 616), for any differentiable local solution: if `p(·)` is differentiable
at `q̄`, `p(q̄) = p̄` and `ẑ(p(q); q) = 0` near `q̄`, then `D_p ẑ ∘ Dp(q̄) + D_q ẑ = 0`. -/
theorem eq_17_G_1_any {zh : (Fin n → ℝ) × (Fin N → ℝ) → Fin n → ℝ}
    {f' : (Fin n → ℝ) × (Fin N → ℝ) →L[ℝ] (Fin n → ℝ)} {p : Fin n → ℝ} {q : Fin N → ℝ}
    (hf : HasFDerivAt zh f' (p, q)) {η : (Fin N → ℝ) → Fin n → ℝ}
    {η' : (Fin N → ℝ) →L[ℝ] (Fin n → ℝ)} (hη : HasFDerivAt η η' q) (hηq : η q = p)
    (hsol : ∀ᶠ q' in 𝓝 q, zh (η q', q') = 0) (dq : Fin N → ℝ) :
    f' (η' dq, 0) + f' (0, dq) = 0 := by
  have hf' : HasFDerivAt zh f' (η q, q) := by rw [hηq]; exact hf
  have hG : HasFDerivAt (fun q' => zh (η q', q'))
      (f'.comp (η'.prod (ContinuousLinearMap.id ℝ (Fin N → ℝ)))) q :=
    HasFDerivAt.comp (f := fun x => (η x, x)) q hf' (hη.prodMk (hasFDerivAt_id q))
  have h0 : HasFDerivAt (fun q' => zh (η q', q')) (0 : (Fin N → ℝ) →L[ℝ] (Fin n → ℝ)) q :=
    (hasFDerivAt_const (0 : Fin n → ℝ) q).congr_of_eventuallyEq hsol
  have h := congrArg (fun T : (Fin N → ℝ) →L[ℝ] (Fin n → ℝ) => T dq) (hG.unique h0)
  rw [← map_add, Prod.mk_add_mk, add_zero, zero_add]
  simpa using h

/-! ### Proposition 17.G.2 -/

/-- **Proposition 17.G.2** (MWG, p. 617). Suppose `ẑ(p̄; q̄) = 0`, `ẑ` is differentiable and
`D_p ẑ(p̄; q̄)` is negative definite (printed `D_q ẑ`, a misprint: corrections 35). Then for the
local solution `p(·)` (differentiable at `q̄`), `(D_q ẑ dq)·(Dp(q̄) dq) ≥ 0` for any `dq`
(17.G.3). -/
theorem proposition_17_G_2 {zh : (Fin n → ℝ) × (Fin N → ℝ) → Fin n → ℝ}
    {f' : (Fin n → ℝ) × (Fin N → ℝ) →L[ℝ] (Fin n → ℝ)} {p : Fin n → ℝ} {q : Fin N → ℝ}
    (hf : HasFDerivAt zh f' (p, q)) {η : (Fin N → ℝ) → Fin n → ℝ}
    {η' : (Fin N → ℝ) →L[ℝ] (Fin n → ℝ)} (hη : HasFDerivAt η η' q) (hηq : η q = p)
    (hsol : ∀ᶠ q' in 𝓝 q, zh (η q', q') = 0)
    (hnd : ∀ v, v ≠ 0 → v ⬝ᵥ f' (v, 0) < 0) (dq : Fin N → ℝ) :
    0 ≤ f' (0, dq) ⬝ᵥ η' dq := by
  have h := eq_17_G_1_any hf hη hηq hsol dq
  have he : f' (0, dq) = -f' (η' dq, 0) := by linear_combination (exp := 1) h
  rw [he, neg_dotProduct, dotProduct_comm]
  rcases eq_or_ne (η' dq) 0 with h0 | h0
  · simp [h0]
  · linarith [hnd _ h0]

/-- **Proposition 17.G.2** with **(17.G.1)** (MWG, pp. 616-617): if `ẑ` is strictly differentiable
at `(p̄, q̄)`, `ẑ(p̄; q̄) = 0` and `D_p ẑ` is negative definite, there is a local solution
function `p(·)` (Definition M.E.1) differentiable at `q̄`, and it satisfies (17.G.3). -/
theorem proposition_17_G_2_exists {zh : (Fin n → ℝ) × (Fin N → ℝ) → Fin n → ℝ}
    {f' : (Fin n → ℝ) × (Fin N → ℝ) →L[ℝ] (Fin n → ℝ)} {p : Fin n → ℝ} {q : Fin N → ℝ}
    (hf : HasStrictFDerivAt zh f' (p, q)) (h0 : zh (p, q) = 0)
    (hnd : ∀ v, v ≠ 0 → v ⬝ᵥ f' (v, 0) < 0) :
    ∃ η : (Fin N → ℝ) → Fin n → ℝ, ∃ η' : (Fin N → ℝ) →L[ℝ] (Fin n → ℝ),
      LocallySolvable zh p q η ∧ HasFDerivAt η η' q ∧ ∀ dq, 0 ≤ f' (0, dq) ⬝ᵥ η' dq := by
  have hreg : (f'.comp (ContinuousLinearMap.inl ℝ (Fin n → ℝ) (Fin N → ℝ))).det ≠ 0 :=
    cs_det_ne_zero_of_nd _ fun v hv => by simpa using hnd v hv
  obtain ⟨η, hloc, hd⟩ := eq_17_G_1 hf h0 hreg
  refine ⟨η, _, hloc, hd.hasFDerivAt, fun dq => ?_⟩
  obtain ⟨hηq, ε, hε, δ, hδ, hball⟩ := hloc
  have hsol : ∀ᶠ q' in 𝓝 q, zh (η q', q') = 0 := by
    filter_upwards [Metric.ball_mem_nhds q hδ] with q' hq'
    exact (hball q' hq').2.1
  exact proposition_17_G_2 hf.hasFDerivAt hd.hasFDerivAt hηq hsol hnd dq

/-- Instance of Proposition 17.G.2: `ẑ(p; q) = q - p` (`n = N = 1`) at `(0, 0)`: strictly
differentiable, `D_p ẑ = -1` negative definite; the solution is `p(q) = q`. -/
theorem proposition_17_G_2_instance :
    let zh : (Fin 1 → ℝ) × (Fin 1 → ℝ) → Fin 1 → ℝ := fun x => x.2 - x.1
    HasStrictFDerivAt zh (ContinuousLinearMap.snd ℝ (Fin 1 → ℝ) (Fin 1 → ℝ) -
      ContinuousLinearMap.fst ℝ (Fin 1 → ℝ) (Fin 1 → ℝ)) (0, 0) ∧ zh (0, 0) = 0 ∧
      ∀ v : Fin 1 → ℝ, v ≠ 0 → v ⬝ᵥ (ContinuousLinearMap.snd ℝ (Fin 1 → ℝ) (Fin 1 → ℝ) -
        ContinuousLinearMap.fst ℝ (Fin 1 → ℝ) (Fin 1 → ℝ)) (v, 0) < 0 := by
  intro zh
  refine ⟨(ContinuousLinearMap.snd ℝ (Fin 1 → ℝ) (Fin 1 → ℝ) -
    ContinuousLinearMap.fst ℝ (Fin 1 → ℝ) (Fin 1 → ℝ)).hasStrictFDerivAt, by simp [zh],
    fun v hv => ?_⟩
  have : (ContinuousLinearMap.snd ℝ (Fin 1 → ℝ) (Fin 1 → ℝ) -
      ContinuousLinearMap.fst ℝ (Fin 1 → ℝ) (Fin 1 → ℝ)) (v, 0) = -v := by simp
  rw [this, dotProduct_neg, neg_neg_iff_pos]
  exact isd_dot_self_pos hv

/-- **Section 17.G** (MWG, p. 618). Under Proposition 17.G.2, a shock that at fixed prices lowers
the excess demand of good `k` only (`D_q ẑ dq = -ε eᵏ`, `ε > 0`) lowers the equilibrium price of
good `k`: `(Dp(q̄) dq)ₖ < 0`. -/
theorem cs_single_market {zh : (Fin n → ℝ) × (Fin N → ℝ) → Fin n → ℝ}
    {f' : (Fin n → ℝ) × (Fin N → ℝ) →L[ℝ] (Fin n → ℝ)} {p : Fin n → ℝ} {q : Fin N → ℝ}
    (hf : HasFDerivAt zh f' (p, q)) {η : (Fin N → ℝ) → Fin n → ℝ}
    {η' : (Fin N → ℝ) →L[ℝ] (Fin n → ℝ)} (hη : HasFDerivAt η η' q) (hηq : η q = p)
    (hsol : ∀ᶠ q' in 𝓝 q, zh (η q', q') = 0)
    (hnd : ∀ v, v ≠ 0 → v ⬝ᵥ f' (v, 0) < 0) {dq : Fin N → ℝ} {k : Fin n} {ε : ℝ}
    (hε : 0 < ε) (hshock : f' (0, dq) = -ε • Pi.single k 1) : η' dq k < 0 := by
  have h := eq_17_G_1_any hf hη hηq hsol dq
  have he : f' (η' dq, 0) = ε • Pi.single k 1 := by
    rw [hshock] at h; rw [neg_smul] at h; linear_combination (exp := 1) h
  have hy0 : η' dq ≠ 0 := by
    intro h0
    rw [h0, Prod.mk_zero_zero, map_zero] at he
    have := congrFun he k
    simp at this
    exact hε.ne' this.symm
  have hq := hnd _ hy0
  rw [he, dotProduct_smul, dotProduct_single, mul_one, smul_eq_mul] at hq
  by_contra hk
  push Not at hk
  nlinarith

/-! ### Proposition 17.G.3 -/

/-- The key lemma: if `B` has positive off-diagonal entries and `Bw ≪ 0` for some `w ≫ 0`, then
`By ≥ 0` and `y ≠ 0` imply `y ≪ 0`. -/
theorem cs_neg_of_nonneg {m : ℕ} {B : Matrix (Fin m) (Fin m) ℝ} {w : Fin m → ℝ}
    (hw : ∀ i, 0 < w i) (hBw : ∀ i, B.mulVec w i < 0) (hoff : ∀ i j, i ≠ j → 0 < B i j)
    {y : Fin m → ℝ} (hy : ∀ i, 0 ≤ B.mulVec y i) (hy0 : y ≠ 0) : ∀ i, y i < 0 := by
  rcases isEmpty_or_nonempty (Fin m) with hE | hne
  · exact fun i => isEmptyElim i
  obtain ⟨k, -, hk⟩ := Finset.exists_max_image Finset.univ (fun j => y j / w j)
    Finset.univ_nonempty
  set μ := y k / w k with hμ
  have hle : ∀ j, y j ≤ μ * w j := fun j => by
    have := hk j (Finset.mem_univ j)
    rwa [div_le_iff₀ (hw j)] at this
  have hyk : y k = μ * w k := by rw [hμ]; field_simp [(hw k).ne']
  -- `(By)ₖ ≤ μ(Bw)ₖ`
  have hrow : B.mulVec y k ≤ μ * B.mulVec w k := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    by_cases hj : j = k
    · subst hj; rw [hyk]; ring_nf; exact le_refl _
    · have := mul_le_mul_of_nonneg_left (hle j) (hoff k j (Ne.symm hj)).le
      linarith
  have hμ0 : μ ≤ 0 := by
    by_contra hpos
    push Not at hpos
    have := mul_neg_of_pos_of_neg hpos (hBw k)
    linarith [hy k]
  intro i
  have hyi : y i ≤ 0 := (hle i).trans (mul_nonpos_of_nonpos_of_nonneg hμ0 (hw i).le)
  rcases hyi.lt_or_eq with h | h
  · exact h
  · exfalso
    apply hy0
    -- row `i`: `(By)ᵢ = ∑_{j ≠ i} Bᵢⱼ yⱼ ≤ 0`, with every term `≤ 0`
    have hterm : ∀ j, B i j * y j ≤ 0 := fun j => by
      by_cases hj : j = i
      · subst hj; rw [h, mul_zero]
      · exact mul_nonpos_of_nonneg_of_nonpos (hoff i j (Ne.symm hj)).le
          ((hle j).trans (mul_nonpos_of_nonpos_of_nonneg hμ0 (hw j).le))
    have hsum : ∑ j, B i j * y j = 0 := le_antisymm
      (Finset.sum_nonpos fun j _ => hterm j) (by simpa [Matrix.mulVec, dotProduct] using hy i)
    have hall := (Finset.sum_eq_zero_iff_of_nonpos fun j _ => hterm j).1 hsum
    funext j
    by_cases hj : j = i
    · subst hj; exact h
    · have := hall j (Finset.mem_univ j)
      rcases mul_eq_zero.1 this with h1 | h1
      · exact absurd h1 (hoff i j (Ne.symm hj)).ne'
      · exact h1

/-- **Proposition 17.G.3**, matrix form (MWG, p. 618). If `B` has positive off-diagonal entries
and `Bw ≪ 0` for some `w ≫ 0`, then `B` is nonsingular and every entry of `B⁻¹` is negative. -/
theorem cs_inv_neg {m : ℕ} {B : Matrix (Fin m) (Fin m) ℝ} {w : Fin m → ℝ}
    (hw : ∀ i, 0 < w i) (hBw : ∀ i, B.mulVec w i < 0) (hoff : ∀ i j, i ≠ j → 0 < B i j) :
    IsUnit B.det ∧ ∀ i j, B⁻¹ i j < 0 := by
  have hdet : B.det ≠ 0 := by
    intro h0
    obtain ⟨y, hy0, hy⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    rcases isEmpty_or_nonempty (Fin m) with hE | ⟨⟨i⟩⟩
    · exact hy0 (funext fun i => isEmptyElim i)
    have h1 := cs_neg_of_nonneg hw hBw hoff (fun j => by rw [hy]; rfl) hy0 i
    have h2 := cs_neg_of_nonneg hw hBw hoff (y := -y) (fun j => by
      rw [Matrix.mulVec_neg, hy, neg_zero]; rfl) (neg_ne_zero.2 hy0) i
    simp only [Pi.neg_apply, neg_neg_iff_pos] at h2
    linarith
  have hu : IsUnit B.det := isUnit_iff_ne_zero.2 hdet
  refine ⟨hu, fun i j => ?_⟩
  set y := B⁻¹.mulVec (Pi.single j 1) with hy
  have hBy : B.mulVec y = Pi.single j 1 := by
    rw [hy, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  have hy0 : y ≠ 0 := by
    intro h0
    have := congrFun hBy j
    rw [h0, Matrix.mulVec_zero] at this
    simp at this
  have := cs_neg_of_nonneg hw hBw hoff (fun k => by
    rw [hBy]; by_cases hk : k = j
    · subst hk; simp
    · simp [hk]) hy0 i
  simpa [hy, Matrix.mulVec, dotProduct, Pi.single_apply] using this

/-- **Proposition 17.G.3** (MWG, p. 618). Suppose `ẑ(p̄; q̄) = 0`, `z(·; q̄)` is differentiable at
`p̄ ≫ 0` and homogeneous of degree zero, and the `L × L` matrix `D_p z(p̄; q̄)` has negative
diagonal and positive off-diagonal entries. Then `D_p ẑ(p̄; q̄)` (delete the numeraire's row and
column) is nonsingular and `[D_p ẑ(p̄; q̄)]⁻¹` has all its entries negative. -/
theorem proposition_17_G_3 {z : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ} (hH : EDHomogeneous z)
    {p : Fin (n + 1) → ℝ} (hp : p ∈ posOrthant (n + 1))
    {D : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ)} (hd : HasFDerivAt z D p)
    (_hdiag : ∀ k, D (Pi.single k 1) k < 0)
    (hoff : ∀ k l, k ≠ l → 0 < D (Pi.single l 1) k) :
    IsUnit ((LinearMap.toMatrix' (D : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ))).submatrix
        (Fin.last n).succAbove (Fin.last n).succAbove).det ∧
      ∀ i j, ((LinearMap.toMatrix' (D : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ))).submatrix
        (Fin.last n).succAbove (Fin.last n).succAbove)⁻¹ i j < 0 := by
  set A := LinearMap.toMatrix' (D : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ)) with hA
  have hAp : A.mulVec p = 0 := by
    rw [hA, LinearMap.toMatrix'_mulVec]; exact euler_fderiv hH hp hd
  refine cs_inv_neg (w := fun j => p ((Fin.last n).succAbove j)) (fun j => hp _) (fun i => ?_)
    (fun i j hij => ?_)
  · have h := congrFun hAp ((Fin.last n).succAbove i)
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at h
    rw [Fin.sum_univ_succAbove _ (Fin.last n)] at h
    have hA1 : 0 < A ((Fin.last n).succAbove i) (Fin.last n) := by
      rw [hA, LinearMap.toMatrix'_apply]; exact hoff _ _ (Fin.succAbove_ne _ i)
    have hlast : 0 < A ((Fin.last n).succAbove i) (Fin.last n) * p (Fin.last n) :=
      mul_pos hA1 (hp _)
    simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply]
    linarith
  · simp only [Matrix.submatrix_apply, hA, LinearMap.toMatrix'_apply]
    exact hoff _ _ fun h => hij (Fin.succAbove_right_injective h)

/-- **Section 17.G** (MWG, pp. 618-619). With the hypotheses of Proposition 17.G.3 on
`B = D_p ẑ(p̄; q̄)` (positive off-diagonal entries, `B p̂ ≪ 0`): if `D_q ẑ dq ≪ 0` (the shock lowers
the excess demand of every one of the first `L - 1` goods), then `Dp(q̄) dq ≪ 0`: all the
equilibrium prices of the first `L - 1` goods fall relative to good `L`. -/
theorem cs_gs_shock {zh : (Fin n → ℝ) × (Fin N → ℝ) → Fin n → ℝ}
    {f' : (Fin n → ℝ) × (Fin N → ℝ) →L[ℝ] (Fin n → ℝ)} {p : Fin n → ℝ} {q : Fin N → ℝ}
    (hf : HasFDerivAt zh f' (p, q)) {η : (Fin N → ℝ) → Fin n → ℝ}
    {η' : (Fin N → ℝ) →L[ℝ] (Fin n → ℝ)} (hη : HasFDerivAt η η' q) (hηq : η q = p)
    (hsol : ∀ᶠ q' in 𝓝 q, zh (η q', q') = 0) {w : Fin n → ℝ} (hw : ∀ i, 0 < w i)
    (hBw : ∀ i, f' (w, 0) i < 0) (hoff : ∀ i j, i ≠ j → 0 < f' (Pi.single j 1, 0) i)
    {dq : Fin N → ℝ} (hshock : ∀ i, f' (0, dq) i < 0) : ∀ i, η' dq i < 0 := by
  set B := LinearMap.toMatrix' ((f'.comp (ContinuousLinearMap.inl ℝ (Fin n → ℝ)
    (Fin N → ℝ)) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) with hB
  have hBv : ∀ v, B.mulVec v = f' (v, 0) := fun v => by
    rw [hB, LinearMap.toMatrix'_mulVec]; rfl
  have h := eq_17_G_1_any hf hη hηq hsol dq
  have hy : ∀ i, 0 ≤ B.mulVec (η' dq) i := fun i => by
    rw [hBv]; have := congrFun h i; simp only [Pi.add_apply, Pi.zero_apply] at this
    linarith [hshock i]
  intro i
  have hy0 : η' dq ≠ 0 := by
    intro h0
    rw [h0, Prod.mk_zero_zero, map_zero, zero_add] at h
    have := hshock i
    rw [h] at this
    exact lt_irrefl _ this
  exact cs_neg_of_nonneg hw (fun i => by rw [hBv]; exact hBw i)
    (fun i j hij => by
      rw [hB, LinearMap.toMatrix'_apply]; exact hoff i j hij) hy hy0 i

/-! ### Footnote 53 and the homotopy -/

/-- **Footnote 53** (MWG, p. 619). Let `p(t)`, `t ∈ [0, 1]`, be a differentiable path of
solutions of `ẑ(p; t) = tẑ(p; q̂) + (1 - t)ẑ(p; q̄) = 0`, so that
`D_p ẑ(p(t); t) p'(t) = -(ẑ(p(t); q̂) - ẑ(p(t); q̄))`. If at every `t` the matrix `D_p ẑ(p(t); t)`
has positive off-diagonal entries and `D_p ẑ(p(t); t) w(t) ≪ 0` for some `w(t) ≫ 0` (gross
substitution with homogeneity, Proposition 17.G.3), and `ẑ(p; q̂) ≪ ẑ(p; q̄)` along the path, then
`pₗ(1) < pₗ(0)` for every `ℓ`: `pₗ(q̂) < pₗ(q̄)`. -/
theorem footnote_17_53 {P P' : ℝ → Fin n → ℝ} {B : ℝ → Matrix (Fin n) (Fin n) ℝ}
    {c w : ℝ → Fin n → ℝ} (hP : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt P (P' t) t)
    (hBP : ∀ t ∈ Set.Icc (0 : ℝ) 1, (B t).mulVec (P' t) = -c t)
    (hc : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ i, c t i < 0)
    (hw : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ i, 0 < w t i)
    (hBw : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ i, (B t).mulVec (w t) i < 0)
    (hoff : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ i j, i ≠ j → 0 < B t i j) (l : Fin n) :
    P 1 l < P 0 l := by
  have hneg : ∀ t ∈ Set.Icc (0 : ℝ) 1, P' t l < 0 := by
    intro t ht
    have hy0 : P' t ≠ 0 := by
      intro h0
      have := congrFun (hBP t ht) l
      rw [h0, Matrix.mulVec_zero] at this
      have := hc t ht l
      simp only [Pi.zero_apply, Pi.neg_apply] at *
      linarith
    exact cs_neg_of_nonneg (hw t ht) (hBw t ht) (hoff t ht) (fun i => by
      rw [hBP t ht]; simp only [Pi.neg_apply]; linarith [hc t ht i]) hy0 l
  have hcoord : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (fun s => P s l) (P' t l) t :=
    fun t ht => hasDerivAt_pi.1 (hP t ht) l
  have hanti : StrictAntiOn (fun s => P s l) (Set.Icc 0 1) :=
    strictAntiOn_of_deriv_neg (convex_Icc 0 1)
      (fun t ht => (hcoord t ht).continuousAt.continuousWithinAt)
      (fun t ht => by
        rw [interior_Icc] at ht
        rw [(hcoord t (Set.Ioo_subset_Icc_self ht)).deriv]
        exact hneg t (Set.Ioo_subset_Icc_self ht))
  exact hanti ⟨le_refl 0, zero_le_one⟩ ⟨zero_le_one, le_refl 1⟩ zero_lt_one

/-- **Section 17.G** (MWG, p. 619). The homotopy `ẑ(·, t) = (1 - t)ẑ(·; q̄) + tẑ(·; q̂)` from the
system before the shock to the system after it. -/
def csHomotopy (z0 z1 : (Fin n → ℝ) → Fin n → ℝ) (t : ℝ) (p : Fin n → ℝ) : Fin n → ℝ :=
  (1 - t) • z0 p + t • z1 p

/-- The homotopy starts at `ẑ(·; q̄)` and ends at `ẑ(·; q̂)` (p. 619), so its solution set
`E = {(t, p) : ẑ(p, t) = 0}` contains `(0, p̄)` and every `(1, p)` with `p` an equilibrium
after the shock. -/
theorem csHomotopy_ends (z0 z1 : (Fin n → ℝ) → Fin n → ℝ) :
    csHomotopy z0 z1 0 = z0 ∧ csHomotopy z0 z1 1 = z1 := by
  constructor <;> funext p <;> simp [csHomotopy]

end MWG.PositiveEquilibriumTheory
