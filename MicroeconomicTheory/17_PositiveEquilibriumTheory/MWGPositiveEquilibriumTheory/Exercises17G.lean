/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.ComparativeStaticsEconomy

/-!
# Exercises 17.G.1 and 17.G.2 (MWG p. 647)

* **Exercise 17.G.1** (`exercise_17_G_1`). With `p_L = 1`, consumer 1's excess demand for the
  first `L - 1` goods as a function of his endowments `ω̂₁` has the derivative
  `D_{ω̂₁} ẑ₁ = b̂ p̂ᵀ - I`, `b = D_{w₁}x₁(p̄, w₁)` (`exercise_17_G_1_deriv`). If demand satisfies
  Walras' law (`p·b = 1`) and is strictly normal (only `b_L > 0` is used), then
  `|D_{ω̂₁} ẑ₁| = (-1)^{L-1} b_L ≠ 0`, so `rank D_{ω̂₁} ẑ₁ = L - 1` (`exercise_17_G_1_det`);
  and since `D_p ẑ Dp = -D_{ω̂₁} ẑ` and the other consumers do not depend on `ω̂₁`,
  `rank Dp(ω̂₁) = L - 1` (`exercise_17_G_1_rank`).
* **Exercise 17.G.2** (`exercise_17_G_2`). An economy (from Proposition 17.G.1, `L = 3`) with
  `ẑ(p̄; ω̂₁) = 0`, `D_p ẑ` negative definite (it is `[[-1, 3], [-3, -1]]`) and
  `∂p₁/∂ω₁₁ = 1/30 > 0`. With two goods this is impossible (`exercise_17_G_2_two_goods`).
-/

namespace MWG.PositiveEquilibriumTheory

open MWG.ClassicalDemand MWG.GeneralEquilibriumExamples Filter Topology

variable {n N : ℕ}

/-- **Exercise 17.G.1**, the derivative (MWG, p. 647). Let `x(w)` be consumer 1's demand at the
fixed prices `p̄ = (q̄, 1)`, differentiable at `w̄ = p̄·(ω̂₁, ω_L)` with `D_w x = b`. Then
`ω̂ ↦ ẑ₁(p̄; ω̂) = x̂(p̄·(ω̂, ω_L)) - ω̂` has derivative `v ↦ b̂ (q̄·v) - v` at `ω̂₁`, i.e. the
matrix `b̂ p̂ᵀ - I`. -/
theorem exercise_17_G_1_deriv {q ω : Fin n → ℝ} {ωL : ℝ} {x : ℝ → Fin (n + 1) → ℝ}
    {b : Fin (n + 1) → ℝ}
    (hx : HasDerivAt x b (normPrice q ⬝ᵥ Fin.snoc (α := fun _ => ℝ) ω ωL)) :
    HasFDerivAt (fun ω' : Fin n → ℝ => fun l => x (normPrice q ⬝ᵥ
        Fin.snoc (α := fun _ => ℝ) ω' ωL) (Fin.castSucc l) - ω' l)
      (cseCLM (Matrix.diagonal (fun _ => -1) +
        Matrix.vecMulVec (fun l => b (Fin.castSucc l)) q)) ω := by
  have hw : ∀ ω' : Fin n → ℝ, normPrice q ⬝ᵥ Fin.snoc (α := fun _ => ℝ) ω' ωL =
      q ⬝ᵥ ω' + ωL := fun ω' => by
    rw [normPrice_dotProduct]
    simp [dotProduct]
  have hlin : HasFDerivAt (fun ω' : Fin n → ℝ => q ⬝ᵥ ω' + ωL) (pe_dotCLM q) ω := by
    have : (fun ω' : Fin n → ℝ => q ⬝ᵥ ω' + ωL) = fun ω' => pe_dotCLM q ω' + ωL := by
      funext ω'; rw [pe_dotCLM_apply, dotProduct_comm]
    rw [this]
    exact (pe_dotCLM q).hasFDerivAt.add_const _
  rw [hasFDerivAt_pi']
  intro l
  have hxl : HasDerivAt (fun w => x w (Fin.castSucc l)) (b (Fin.castSucc l))
      (q ⬝ᵥ ω + ωL) := by
    rw [← hw]; exact hasDerivAt_pi.1 hx _
  have h := (hxl.hasFDerivAt.comp ω hlin).sub (hasFDerivAt_apply l ω)
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun ω' => ?_)).congr_fderiv ?_
  · simp only [hw]; rfl
  · refine ContinuousLinearMap.ext fun v => ?_
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, cseCLM_apply]
    have hvm : (Matrix.vecMulVec (fun l => b (Fin.castSucc l)) q).mulVec v l =
        b (Fin.castSucc l) * (q ⬝ᵥ v) := by
      simp [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Finset.mul_sum, mul_assoc]
    change (ContinuousLinearMap.toSpanSingleton ℝ (b (Fin.castSucc l))) (pe_dotCLM q v) - v l =
      ((Matrix.diagonal fun _ => -1) + Matrix.vecMulVec (fun l => b (Fin.castSucc l)) q).mulVec
        v l
    rw [ContinuousLinearMap.toSpanSingleton_apply, pe_dotCLM_apply, Matrix.add_mulVec,
      Pi.add_apply, Matrix.mulVec_diagonal, hvm, dotProduct_comm, smul_eq_mul]
    ring

/-- **Exercise 17.G.1**, nonsingularity (MWG, p. 647). If demand exhausts wealth (`p̄·b = 1`,
from Walras' law) and good `L` is strictly normal (`b_L > 0`), then
`|b̂ p̂ᵀ - I| = (-1)^{L-1} b_L ≠ 0` and `rank D_{ω̂₁} ẑ₁ = L - 1`. -/
theorem exercise_17_G_1_det {q : Fin n → ℝ} {b : Fin (n + 1) → ℝ}
    (hwal : normPrice q ⬝ᵥ b = 1) (hbL : 0 < b (Fin.last n)) :
    (Matrix.diagonal (fun _ => -1) +
        Matrix.vecMulVec (fun l => b (Fin.castSucc l)) q).det = (-1) ^ n * b (Fin.last n) ∧
      (Matrix.diagonal (fun _ => -1) +
        Matrix.vecMulVec (fun l => b (Fin.castSucc l)) q).rank = n := by
  have hdet : (Matrix.diagonal (fun _ => -1) +
      Matrix.vecMulVec (fun l => b (Fin.castSucc l)) q).det = (-1) ^ n * b (Fin.last n) := by
    rw [det_diagonal_add_vecMulVec _ _ _ (fun _ => by norm_num)]
    rw [dotProduct, Fin.sum_univ_castSucc] at hwal
    simp only [cse_normPrice_castSucc, cse_normPrice_last, one_mul] at hwal
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, div_neg, div_one,
      mul_neg, Finset.sum_neg_distrib]
    congr 1
    linarith
  refine ⟨hdet, ?_⟩
  have hu : IsUnit (Matrix.diagonal (fun _ => -1) +
      Matrix.vecMulVec (fun l => b (Fin.castSucc l)) q).det := by
    rw [hdet]
    exact isUnit_iff_ne_zero.2 (mul_ne_zero (pow_ne_zero _ (by norm_num)) hbL.ne')
  rw [Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 hu), Fintype.card_fin]

/-- Walras' law along the wealth path gives `p̄·D_w x = 1`. -/
theorem exercise_17_G_1_walras {p b : Fin (n + 1) → ℝ} {x : ℝ → Fin (n + 1) → ℝ} {w : ℝ}
    (hx : HasDerivAt x b w) (hW : ∀ᶠ w' in 𝓝 w, p ⬝ᵥ x w' = w') : p ⬝ᵥ b = 1 := by
  have h1 : HasDerivAt (fun w' => p ⬝ᵥ x w') (p ⬝ᵥ b) w := by
    have := (pe_dotCLM p).hasFDerivAt.comp_hasDerivAt w hx
    convert this using 1
    · funext w'; simp [pe_dotCLM_apply, dotProduct_comm]
    · simp [pe_dotCLM_apply, dotProduct_comm]
  exact h1.unique ((hasDerivAt_id w).congr_of_eventuallyEq hW)

/-- **Exercise 17.G.1**, the rank of `Dp` (MWG, p. 647). If the system `ẑ(p; ω̂₁) = 0` is solved
near `ω̂₁` by a function `p(·)` differentiable at `ω̂₁`, and `D_{ω̂₁} ẑ` is nonsingular (it equals
`D_{ω̂₁} ẑ₁`, the other endowments being fixed), then `Dp(ω̂₁)` is nonsingular:
`rank Dp(ω̂₁) = L - 1`. -/
theorem exercise_17_G_1_rank {zh : (Fin n → ℝ) × (Fin n → ℝ) → Fin n → ℝ}
    {f' : (Fin n → ℝ) × (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)} {p ω : Fin n → ℝ}
    (hf : HasFDerivAt zh f' (p, ω)) {η : (Fin n → ℝ) → Fin n → ℝ}
    {η' : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)} (hη : HasFDerivAt η η' ω) (hηq : η ω = p)
    (hsol : ∀ᶠ ω' in 𝓝 ω, zh (η ω', ω') = 0)
    (hdet : (f'.comp (ContinuousLinearMap.inr ℝ (Fin n → ℝ) (Fin n → ℝ))).det ≠ 0) :
    η'.det ≠ 0 ∧ (LinearMap.toMatrix' (η' : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))).rank = n := by
  have hinj : Function.Injective η' := by
    intro v w hvw
    obtain ⟨e, he⟩ := (isInvertible_iff_det_ne_zero _).2 hdet
    have h1 := eq_17_G_1_any hf hη hηq hsol v
    have h2 := eq_17_G_1_any hf hη hηq hsol w
    have : f'.comp (ContinuousLinearMap.inr ℝ (Fin n → ℝ) (Fin n → ℝ)) v =
        f'.comp (ContinuousLinearMap.inr ℝ (Fin n → ℝ) (Fin n → ℝ)) w := by
      simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
        ContinuousLinearMap.inr_apply]
      rw [hvw] at h1
      linear_combination (exp := 1) h1 - h2
    rw [← he] at this
    exact e.injective this
  have hdet' : η'.det ≠ 0 := by
    intro h0
    rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix'] at h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    rw [LinearMap.toMatrix'_mulVec] at hv
    exact hv0 (hinj (by rw [show η' v = 0 from hv, map_zero]))
  refine ⟨hdet', ?_⟩
  have hu : IsUnit (LinearMap.toMatrix' (η' : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))).det := by
    rw [LinearMap.det_toMatrix']
    exact isUnit_iff_ne_zero.2 hdet'
  rw [Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 hu), Fintype.card_fin]

/-- **Exercise 17.G.1** (MWG, p. 647), assembled for the economy of Proposition 17.G.1: there
`D_{ω̂₁} ẑ = D_{ω̂₁} ẑ₁` is the Cobb-Douglas `cseM p̂` (nonsingular, `cseM_det`), so the solution
function has `rank Dp(ω̂₁) = L - 1`. -/
theorem exercise_17_G_1 {q ω : Fin n → ℝ} (hq : ∀ l, 0 < q l) (hω : ∀ l, 0 ≤ ω l)
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.det ≠ 0) :
    ∃ E' : ExchangeEconomy (Fin (n + 1)) (n + 1), ∃ η : (Fin n → ℝ) → Fin n → ℝ,
      ∃ η' : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ), LocallySolvable (cseZ E') q ω η ∧
        HasFDerivAt η η' ω ∧ (cseM q).rank = n ∧
        (LinearMap.toMatrix' (η' : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))).rank = n := by
  obtain ⟨E', -, -, -, -, f', hf', -, -, hfr, η, hloc, hηd⟩ := proposition_17_G_1 hq hω B hB
  have hMdet : (cseM q).det ≠ 0 := by
    rw [cseM_det hq]; exact div_ne_zero (pow_ne_zero _ (by norm_num)) (by positivity)
  have hmat : LinearMap.toMatrix' ((f'.comp (ContinuousLinearMap.inr ℝ (Fin n → ℝ)
      (Fin n → ℝ)) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) =
      cseM q := cse_toMatrix'_eq fun v => hfr v
  have hdet : (f'.comp (ContinuousLinearMap.inr ℝ (Fin n → ℝ) (Fin n → ℝ))).det ≠ 0 := by
    rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix', hmat]; exact hMdet
  obtain ⟨hηq, ε, hε, δ, hδ, hball⟩ := hloc
  have hsol : ∀ᶠ ω' in 𝓝 ω, cseZ E' (η ω', ω') = 0 := by
    filter_upwards [Metric.ball_mem_nhds ω hδ] with ω' hω'
    exact (hball ω' hω').2.1
  refine ⟨E', η, _, ⟨hηq, ε, hε, δ, hδ, hball⟩, hηd.hasFDerivAt, ?_,
    (exercise_17_G_1_rank hf'.hasFDerivAt hηd.hasFDerivAt hηq hsol hdet).2⟩
  rw [Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hMdet)),
    Fintype.card_fin]

/-! ### Exercise 17.G.2 -/

/-- The derivative `Dp(ω̂₁)` chosen for Exercise 17.G.2. -/
noncomputable def ex17G2B : Matrix (Fin 2) (Fin 2) ℝ := !![1 / 30, -1 / 6; 7 / 30, -1 / 6]

/-- The resulting `D_p ẑ = [[-1, 3], [-3, -1]]`, negative definite. -/
def ex17G2N : Matrix (Fin 2) (Fin 2) ℝ := !![-1, 3; -3, -1]

/-- **Exercise 17.G.2** (MWG, p. 647). There are economies (setting of Proposition 17.G.2, from
Proposition 17.G.1) with `ẑ(p̄; ω̂₁) = 0`, `D_p ẑ(p̄; ω̂₁)` negative definite, and
`∂p₁(ω̂₁)/∂ω₁₁ > 0`: here `L = 3`, `p̄ = (1, 1, 1)`, `ω̂₁ = (1, 1)`, `D_p ẑ = [[-1, 3], [-3, -1]]`
and `∂p₁/∂ω₁₁ = 1/30`. -/
theorem exercise_17_G_2 :
    ∃ E' : ExchangeEconomy (Fin 3) 3, cseZ E' (![1, 1], ![1, 1]) = 0 ∧
      ∃ f' : (Fin 2 → ℝ) × (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ),
        HasStrictFDerivAt (cseZ E') f' (![1, 1], ![1, 1]) ∧
        (∀ v, v ≠ 0 → v ⬝ᵥ f' (v, 0) < 0) ∧
        ∃ η : (Fin 2 → ℝ) → Fin 2 → ℝ, ∃ η' : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ),
          LocallySolvable (cseZ E') ![1, 1] ![1, 1] η ∧ HasStrictFDerivAt η η' ![1, 1] ∧
          0 < η' (Pi.single 0 1) 0 := by
  have hq : ∀ l : Fin 2, 0 < (![1, 1] : Fin 2 → ℝ) l := fun l => by fin_cases l <;> simp
  have hω : ∀ l : Fin 2, 0 ≤ (![1, 1] : Fin 2 → ℝ) l := fun l => (hq l).le
  have hBdet : ex17G2B.det ≠ 0 := by
    rw [Matrix.det_fin_two]; simp [ex17G2B]; norm_num
  obtain ⟨E', -, -, -, hz, f', hf', -, hfl, -, η, hloc, hηd⟩ :=
    proposition_17_G_1 hq hω ex17G2B hBdet
  have hM : cseM (![1, 1] : Fin 2 → ℝ) = -(ex17G2N * ex17G2B) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cseM, ex17G2N, ex17G2B] <;> norm_num
  have hu : IsUnit ex17G2B.det := isUnit_iff_ne_zero.2 hBdet
  have hN : -(cseM (![1, 1] : Fin 2 → ℝ) * ex17G2B⁻¹) = ex17G2N := by
    rw [hM, Matrix.neg_mul, neg_neg, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
  refine ⟨E', hz, f', hf', fun v hv => ?_, η, _, hloc, hηd, ?_⟩
  · rw [hfl, hN]
    have hv' : 0 < v 0 ^ 2 + v 1 ^ 2 := by
      by_contra h
      push Not at h
      apply hv
      funext i
      fin_cases i <;> simp <;> nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
    have : v ⬝ᵥ ex17G2N.mulVec v = -(v 0 ^ 2 + v 1 ^ 2) := by
      simp [ex17G2N, Matrix.mulVec, dotProduct, Fin.sum_univ_two]; ring
    rw [this]; linarith
  · rw [cseCLM_apply]
    simp [ex17G2B, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- With two goods (`L - 1 = 1`), Proposition 17.G.2's hypothesis `D_p ẑ < 0` and strict normality
(`D_{ω₁₁} ẑ = q b₁ - 1 < 0`, because `q b₁ = 1 - b₂ < 1`) force `∂p₁/∂ω₁₁ < 0`: Exercise 17.G.2
needs at least three goods. -/
theorem exercise_17_G_2_two_goods {a m d : ℝ} (ha : a < 0) (hm : m < 0) (hd : a * d = -m) :
    d < 0 := by
  by_contra h
  push Not at h
  nlinarith [mul_nonpos_of_nonpos_of_nonneg ha.le h]

end MWG.PositiveEquilibriumTheory
