/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.Regularity
import MWGConsumerChoice.Slutsky
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Price effects at a given price vector (MWG Section 17.E, pp. 598-600)

* **(17.E.1)** `Dz(p) p = 0` (homogeneity of degree zero, `eq_17_E_1`) and **(17.E.2)**
  `p·Dz(p) = -z(p)` (Walras' law, `eq_17_E_2`), entrywise (Exercise 17.E.1).
* **(17.E.3)** For consumers with differentiable demand functions `xᵢ(p, w)`, the aggregate
  excess demand `z(p) = ∑ᵢ (xᵢ(p, p·ωᵢ) - ωᵢ)` has
  `Dz(p) = ∑ᵢ [Sᵢ(p, p·ωᵢ) - D_w xᵢ(p, p·ωᵢ) zᵢ(p)ᵀ]` with `Sᵢ` the Slutsky matrix of
  Chapter 2 (`eq_17_E_3`, Exercise 17.E.2). The wealth-effect matrix `D_w xᵢ zᵢᵀ` has rank at most
  one (`rank_wealthEffectMatrix_le`), and exactly one when both vectors are nonzero.
* **Proposition 17.E.1**: with `I < L` consumers whose demand functions satisfy Walras' law and
  the weak axiom, at an equilibrium there is `dp ≠ 0` with `p·dp = 0` and `dp·Dz(p) dp ≤ 0`
  (`proposition_17_E_1`). The book's count "at most `I` of the `I + 1` vectors
  `p, z₁(p), …, z_I(p)` are linearly independent" needs `I ≥ 1`: with no consumers `p` alone is
  independent (we assume a nonempty set of consumers). Instance: one consumer who spends all
  wealth on good 1, two goods (`proposition_17_E_1_instance`).
* **Footnote 27**: a wealth-effect vector proportional to `eˡ` equals `(1/pₗ) eˡ`
  (`footnote_17_27`).
-/

namespace MWG.PositiveEquilibriumTheory

open MWG.ConsumerChoice Filter Topology

variable {L : ℕ}

/-- A linear map on `ℝ^L` in coordinates: `(D v)ₗ = ∑ₖ (D eᵏ)ₗ vₖ`. -/
theorem pe_clm_apply_eq_sum (D : (Fin L → ℝ) →L[ℝ] (Fin L → ℝ)) (v : Fin L → ℝ) (l : Fin L) :
    D v l = ∑ k, D (Pi.single k 1) l * v k := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  have : (Pi.single k (v k) : Fin L → ℝ) = v k • Pi.single k (1 : ℝ) := by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [this, map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]

/-- **(17.E.1)** (MWG, p. 599; Exercise 17.E.1). If `z` is homogeneous of degree zero and
differentiable at `p ≫ 0`, then `∑ₖ (∂zₗ/∂pₖ) pₖ = 0` for every `ℓ` (`Dz(p) p = 0`). -/
theorem eq_17_E_1 {z : (Fin L → ℝ) → Fin L → ℝ} (hH : EDHomogeneous z) {p : Fin L → ℝ}
    (hp : p ∈ posOrthant L) {D : (Fin L → ℝ) →L[ℝ] (Fin L → ℝ)} (hd : HasFDerivAt z D p)
    (l : Fin L) : ∑ k, D (Pi.single k 1) l * p k = 0 := by
  rw [← pe_clm_apply_eq_sum, euler_fderiv hH hp hd, Pi.zero_apply]

/-- **(17.E.2)** (MWG, p. 599; Exercise 17.E.1). If `z` satisfies Walras' law and is
differentiable at `p ≫ 0`, then `∑ₖ pₖ (∂zₖ/∂pₗ) = -zₗ(p)` for every `ℓ` (`p·Dz(p) = -z(p)`). -/
theorem eq_17_E_2 {z : (Fin L → ℝ) → Fin L → ℝ} (hW : EDWalrasLaw z) {p : Fin L → ℝ}
    (hp : p ∈ posOrthant L) {D : (Fin L → ℝ) →L[ℝ] (Fin L → ℝ)} (hd : HasFDerivAt z D p)
    (l : Fin L) : ∑ k, p k * D (Pi.single l 1) k = -z p l := by
  have h := walras_fderiv hW hp hd (Pi.single l 1)
  rw [single_dotProduct, one_mul] at h
  rw [← dotProduct]
  linarith

/-- **Exercise 17.E.1** (MWG, p. 645). Expressions (17.E.1) and (17.E.2). -/
theorem exercise_17_E_1 {z : (Fin L → ℝ) → Fin L → ℝ} (hH : EDHomogeneous z)
    (hW : EDWalrasLaw z) {p : Fin L → ℝ} (hp : p ∈ posOrthant L)
    {D : (Fin L → ℝ) →L[ℝ] (Fin L → ℝ)} (hd : HasFDerivAt z D p) :
    (∀ l, ∑ k, D (Pi.single k 1) l * p k = 0) ∧ (∀ l, ∑ k, p k * D (Pi.single l 1) k = -z p l) :=
  ⟨eq_17_E_1 hH hp hd, eq_17_E_2 hW hp hd⟩

/-- The linear functional `v ↦ v·ω`. -/
noncomputable def pe_dotCLM (ω : Fin L → ℝ) : (Fin L → ℝ) →L[ℝ] ℝ :=
  ∑ l, ω l • ContinuousLinearMap.proj l

theorem pe_dotCLM_apply (ω v : Fin L → ℝ) : pe_dotCLM ω v = v ⬝ᵥ ω := by
  simp [pe_dotCLM, dotProduct, mul_comm]

/-- The aggregate excess demand `z(p) = ∑ᵢ (xᵢ(p, p·ωᵢ) - ωᵢ)` of consumers with demand
functions `xᵢ` and endowments `ωᵢ` (MWG, p. 599). -/
def aggExcessDemand {ι : Type*} [Fintype ι] (x : ι → DemandFunction L) (ω : ι → Fin L → ℝ)
    (q : Fin L → ℝ) : Fin L → ℝ :=
  ∑ i, (x i q (q ⬝ᵥ ω i) - ω i)

/-- **(17.E.3)** (MWG, p. 599; Exercise 17.E.2). If each demand function `xᵢ` is differentiable
at `(p, p·ωᵢ)` with derivative `Dxᵢ`, then `z(p) = ∑ᵢ (xᵢ(p, p·ωᵢ) - ωᵢ)` is differentiable at
`p` and `Dz(p) = ∑ᵢ [Sᵢ(p, p·ωᵢ) - D_w xᵢ(p, p·ωᵢ) zᵢ(p)ᵀ]`, where `Sᵢ` is the Slutsky matrix
(2.F.10) and `zᵢ(p) = xᵢ(p, p·ωᵢ) - ωᵢ`. -/
theorem eq_17_E_3 {ι : Type*} [Fintype ι] (x : ι → DemandFunction L) (ω : ι → Fin L → ℝ)
    {p : Fin L → ℝ} (Dx : ι → ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ))
    (hx : ∀ i, HasFDerivAt (Function.uncurry (x i)) (Dx i) (p, p ⬝ᵥ ω i)) :
    ∃ D : (Fin L → ℝ) →L[ℝ] (Fin L → ℝ), HasFDerivAt (aggExcessDemand x ω) D p ∧
      ∀ v, D v = Matrix.mulVec (∑ i, (slutskyMatrix (Dx i) (x i p (p ⬝ᵥ ω i)) -
        Matrix.vecMulVec (wealthJacobian (Dx i)) (x i p (p ⬝ᵥ ω i) - ω i))) v := by
  have hin : ∀ i, HasFDerivAt (fun q : Fin L → ℝ => (q, q ⬝ᵥ ω i))
      ((ContinuousLinearMap.id ℝ (Fin L → ℝ)).prod (pe_dotCLM (ω i))) p := by
    intro i
    have h2 : HasFDerivAt (fun q : Fin L → ℝ => q ⬝ᵥ ω i) (pe_dotCLM (ω i)) p := by
      have : (fun q : Fin L → ℝ => q ⬝ᵥ ω i) = pe_dotCLM (ω i) := by
        funext q; rw [pe_dotCLM_apply]
      rw [this]
      exact (pe_dotCLM (ω i)).hasFDerivAt
    exact (hasFDerivAt_id p).prodMk h2
  have hi : ∀ i, HasFDerivAt (fun q => x i q (q ⬝ᵥ ω i) - ω i)
      ((Dx i).comp ((ContinuousLinearMap.id ℝ (Fin L → ℝ)).prod (pe_dotCLM (ω i)))) p := by
    intro i
    have := (hx i).comp p (hin i)
    exact this.sub_const (ω i)
  refine ⟨∑ i, (Dx i).comp ((ContinuousLinearMap.id ℝ (Fin L → ℝ)).prod (pe_dotCLM (ω i))),
    ?_, ?_⟩
  · have := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => hi i)
    simpa [aggExcessDemand] using this
  · intro v
    rw [Matrix.sum_mulVec, FunLike.coe_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.sub_mulVec, slutskyMatrix_mulVec]
    have hv : Matrix.mulVec (Matrix.vecMulVec (wealthJacobian (Dx i))
        (x i p (p ⬝ᵥ ω i) - ω i)) v =
        (v ⬝ᵥ (x i p (p ⬝ᵥ ω i) - ω i)) • Dx i (0, 1) := by
      funext l
      simp only [Matrix.mulVec, Matrix.vecMulVec, Matrix.of_apply, dotProduct, wealthJacobian,
        wealthEffect, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hv]
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_id', id_eq, pe_dotCLM_apply]
    have hsplit : ∀ a b : ℝ, Dx i (v, a) = Dx i (v, b) + (a - b) • Dx i (0, 1) := by
      intro a b
      rw [← map_smul, ← map_add]
      congr 1
      ext <;> simp
    rw [hsplit (v ⬝ᵥ ω i) (v ⬝ᵥ x i p (p ⬝ᵥ ω i)), dotProduct_sub]
    rw [dotProduct_comm v (x i p _), dotProduct_comm v (ω i), sub_smul, sub_smul]
    abel

/-- **Exercise 17.E.2** (MWG, p. 645). Expression (17.E.3). -/
theorem exercise_17_E_2 {ι : Type*} [Fintype ι] (x : ι → DemandFunction L)
    (ω : ι → Fin L → ℝ) {p : Fin L → ℝ} (Dx : ι → ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ))
    (hx : ∀ i, HasFDerivAt (Function.uncurry (x i)) (Dx i) (p, p ⬝ᵥ ω i)) :
    ∃ D : (Fin L → ℝ) →L[ℝ] (Fin L → ℝ), HasFDerivAt (aggExcessDemand x ω) D p ∧
      ∀ v, D v = Matrix.mulVec (∑ i, (slutskyMatrix (Dx i) (x i p (p ⬝ᵥ ω i)) -
        Matrix.vecMulVec (wealthJacobian (Dx i)) (x i p (p ⬝ᵥ ω i) - ω i))) v :=
  eq_17_E_3 x ω Dx hx

/-- **Section 17.E** (MWG, p. 599). The wealth-effect matrix `D_w xᵢ zᵢᵀ` has rank at most `1`. -/
theorem rank_wealthEffectMatrix_le (a b : Fin L → ℝ) : (Matrix.vecMulVec a b).rank ≤ 1 :=
  Matrix.rank_vecMulVec_le a b

/-- **Section 17.E** (MWG, p. 599). The wealth-effect matrix `D_w xᵢ zᵢᵀ` has rank exactly `1`
when `D_w xᵢ ≠ 0` and `zᵢ ≠ 0` (any two rows, or columns, are proportional). -/
theorem rank_wealthEffectMatrix_eq_one {a b : Fin L → ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (Matrix.vecMulVec a b).rank = 1 := by
  refine le_antisymm (Matrix.rank_vecMulVec_le a b) ?_
  obtain ⟨l, hl⟩ : ∃ l, a l ≠ 0 := by
    by_contra h; push Not at h; exact ha (funext h)
  obtain ⟨k, hk⟩ : ∃ k, b k ≠ 0 := by
    by_contra h; push Not at h; exact hb (funext h)
  rw [Nat.one_le_iff_ne_zero]
  intro h0
  have hr : LinearMap.range (Matrix.vecMulVec a b).mulVecLin = ⊥ :=
    Submodule.finrank_eq_zero.mp h0
  have hm : (Matrix.vecMulVec a b).mulVecLin (Pi.single k 1) ∈
      LinearMap.range (Matrix.vecMulVec a b).mulVecLin := LinearMap.mem_range_self _ _
  rw [hr, Submodule.mem_bot] at hm
  have := congrFun hm l
  simp [Matrix.vecMulVec, Matrix.mulVec] at this
  tauto

/-- The Walrasian budget is exhausted: `p·zᵢ(p) = 0` for a demand function satisfying Walras'
law, at `p ≫ 0`, `p·ωᵢ > 0`. -/
theorem pe_walras_indiv {x : DemandFunction L} (hW : WalrasLaw x) {p ω : Fin L → ℝ}
    (hp : StrictlyPositive p) (hw : 0 < p ⬝ᵥ ω) : p ⬝ᵥ (x p (p ⬝ᵥ ω) - ω) = 0 := by
  rw [dotProduct_sub, hW p _ ⟨hp, hw⟩, sub_self]

/-- **Proposition 17.E.1** (MWG, p. 600). Suppose there are `I < L` consumers (`I ≥ 1`) whose
differentiable demand functions satisfy Walras' law and the weak axiom. At an equilibrium price
vector `p ≫ 0` (with `p·ωᵢ > 0`) the aggregate excess demand is differentiable and there is a
direction of price change `dp ≠ 0` with `p·dp = 0` and `dp·Dz(p) dp ≤ 0`. -/
theorem proposition_17_E_1 {ι : Type*} [Fintype ι] [Nonempty ι] (hI : Fintype.card ι < L)
    (x : ι → DemandFunction L) (hW : ∀ i, WalrasLaw (x i)) (hWA : ∀ i, WeakAxiom (x i))
    (ω : ι → Fin L → ℝ) {p : Fin L → ℝ} (hp : StrictlyPositive p)
    (hw : ∀ i, 0 < p ⬝ᵥ ω i) (Dx : ι → ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ))
    (hx : ∀ i, HasFDerivAt (Function.uncurry (x i)) (Dx i) (p, p ⬝ᵥ ω i))
    (heq : aggExcessDemand x ω p = 0) :
    ∃ D : (Fin L → ℝ) →L[ℝ] (Fin L → ℝ), HasFDerivAt (aggExcessDemand x ω) D p ∧
      ∃ dp : Fin L → ℝ, dp ≠ 0 ∧ p ⬝ᵥ dp = 0 ∧ dp ⬝ᵥ D dp ≤ 0 := by
  classical
  obtain ⟨D, hD, hDv⟩ := eq_17_E_3 x ω Dx hx
  refine ⟨D, hD, ?_⟩
  set zi : ι → Fin L → ℝ := fun i => x i p (p ⬝ᵥ ω i) - ω i with hzi
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  let T : (Fin L → ℝ) →ₗ[ℝ] (ι → ℝ) :=
    { toFun := fun v i => if i = i₀ then p ⬝ᵥ v else zi i ⬝ᵥ v
      map_add' := by
        intro v w; funext i
        by_cases h : i = i₀ <;> simp [h, dotProduct_add]
      map_smul' := by
        intro c v; funext i
        by_cases h : i = i₀ <;> simp [h, dotProduct_smul] }
  have hker : LinearMap.ker T ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by simpa using hI)
  obtain ⟨dp, hdp, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hT : ∀ i, T dp i = 0 := fun i => by rw [LinearMap.mem_ker.mp hdp]; rfl
  have hpd : p ⬝ᵥ dp = 0 := by simpa [T] using hT i₀
  have hzo : ∀ i, i ≠ i₀ → zi i ⬝ᵥ dp = 0 := fun i h => by simpa [T, h] using hT i
  have hz0 : zi i₀ ⬝ᵥ dp = 0 := by
    have hsum : (∑ i, zi i) ⬝ᵥ dp = 0 := by
      have : ∑ i, zi i = 0 := heq
      rw [this, zero_dotProduct]
    rw [sum_dotProduct, ← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)] at hsum
    rw [Finset.sum_eq_zero (fun i hi => hzo i (Finset.ne_of_mem_erase hi)), add_zero] at hsum
    exact hsum
  have hzall : ∀ i, dp ⬝ᵥ zi i = 0 := by
    intro i
    rw [dotProduct_comm]
    by_cases h : i = i₀
    · subst h; exact hz0
    · exact hzo i h
  refine ⟨dp, hne, hpd, ?_⟩
  rw [hDv, Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_nonpos fun i _ => ?_
  rw [Matrix.sub_mulVec]
  have hv : Matrix.mulVec (Matrix.vecMulVec (wealthJacobian (Dx i)) (zi i)) dp =
      (dp ⬝ᵥ zi i) • wealthJacobian (Dx i) := by
    funext l
    simp only [Matrix.mulVec, Matrix.vecMulVec, Matrix.of_apply, dotProduct, Pi.smul_apply,
      smul_eq_mul]
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hv' : Matrix.mulVec (Matrix.vecMulVec (wealthJacobian (Dx i))
      (x i p (p ⬝ᵥ ω i) - ω i)) dp = 0 := by
    have := hv
    simp only [hzi] at this
    rw [this, show dp ⬝ᵥ (x i p (p ⬝ᵥ ω i) - ω i) = 0 from hzall i, zero_smul]
  rw [hv', sub_zero]
  exact proposition_2_F_2 (hW i) (hWA i) ⟨hp, hw i⟩ (hx i) dp

/-- **Footnote 27** (MWG, p. 601). If the wealth-effect vector is `α eˡ` and Walras' law holds
in the differentiated form `p·D_w x = 1`, then `α = 1/pₗ`. -/
theorem footnote_17_27 {p : Fin L → ℝ} {l : Fin L} (hp : p l ≠ 0) {α : ℝ}
    (h : p ⬝ᵥ (α • Pi.single l 1) = 1) : α = 1 / p l := by
  rw [dotProduct_smul, dotProduct_single, mul_one, smul_eq_mul] at h
  field_simp
  linarith

/-! ### An instance of Proposition 17.E.1 -/

/-- A demand function that spends all wealth on good `0`: `x(p, w) = (w/p₀) e⁰`. -/
noncomputable def pe_demandGood0 (L : ℕ) [NeZero L] : DemandFunction L :=
  fun p w => (w / p 0) • Pi.single 0 1

theorem pe_demandGood0_walras [NeZero L] : WalrasLaw (pe_demandGood0 L) := by
  intro p w hd
  simp only [pe_demandGood0, dotProduct_smul, dotProduct_single, mul_one, smul_eq_mul]
  field_simp [(hd.1 0).ne']

theorem pe_demandGood0_weakAxiom [NeZero L] : WeakAxiom (pe_demandGood0 L) := by
  intro p w p' w' hd hd' hle hne
  simp only [pe_demandGood0, dotProduct_smul, dotProduct_single, mul_one,
    smul_eq_mul] at hle ⊢
  have h0 := hd.1 0
  have h0' := hd'.1 0
  have hlt : w' / p' 0 ≠ w / p 0 := by
    intro h; apply hne; simp only [pe_demandGood0, h]
  have hle' : w' / p' 0 ≤ w / p 0 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ h0'] at hle
    rw [div_le_div_iff₀ h0' h0]
    linarith
  have hlt' : w' / p' 0 < w / p 0 := lt_of_le_of_ne hle' hlt
  rw [div_lt_div_iff₀ h0' h0] at hlt'
  rw [div_mul_eq_mul_div, lt_div_iff₀ h0]
  linarith

/-- **Proposition 17.E.1**, instance: two goods, one consumer spending all wealth on good `0`
with endowment `e⁰`; every `p ≫ 0` is an equilibrium and the conclusion holds. -/
theorem proposition_17_E_1_instance {p : Fin 2 → ℝ} (hp : StrictlyPositive p) :
    ∃ D : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ),
      HasFDerivAt (aggExcessDemand (fun _ : Unit => pe_demandGood0 2)
        (fun _ => Pi.single 0 1)) D p ∧
      ∃ dp : Fin 2 → ℝ, dp ≠ 0 ∧ p ⬝ᵥ dp = 0 ∧ dp ⬝ᵥ D dp ≤ 0 := by
  have h0 := hp 0
  have hw : 0 < p ⬝ᵥ (Pi.single 0 1 : Fin 2 → ℝ) := by
    rw [dotProduct_single, mul_one]; exact h0
  set w₀ := p ⬝ᵥ (Pi.single 0 1 : Fin 2 → ℝ)
  have hnum : HasFDerivAt (fun r : (Fin 2 → ℝ) × ℝ => r.2)
      (ContinuousLinearMap.snd ℝ (Fin 2 → ℝ) ℝ) (p, w₀) := hasFDerivAt_snd
  have hden : HasFDerivAt (fun r : (Fin 2 → ℝ) × ℝ => r.1 0)
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).comp
        (ContinuousLinearMap.fst ℝ (Fin 2 → ℝ) ℝ)) (p, w₀) :=
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).comp
      (ContinuousLinearMap.fst ℝ (Fin 2 → ℝ) ℝ)).hasFDerivAt
  have hinv := (hasFDerivAt_inv (𝕜 := ℝ) h0.ne').comp (p, w₀) hden
  have hq := (hnum.mul hinv).smul_const (Pi.single 0 1 : Fin 2 → ℝ)
  have hx := hq.congr_of_eventuallyEq (f₁ := Function.uncurry (pe_demandGood0 2))
    (Filter.Eventually.of_forall fun r => by
      simp [pe_demandGood0, Function.uncurry, div_eq_mul_inv])
  exact proposition_17_E_1 (ι := Unit) (by simp) (fun _ => pe_demandGood0 2)
    (fun _ => pe_demandGood0_walras) (fun _ => pe_demandGood0_weakAxiom) _ hp (fun _ => hw)
    (fun _ => _) (fun _ => hx) (by
      funext l
      simp only [aggExcessDemand, pe_demandGood0, dotProduct_single, mul_one,
        div_self h0.ne', one_smul, sub_self, Finset.sum_const, Finset.card_univ,
        Fintype.card_unit, one_smul, Pi.zero_apply])

end MWG.PositiveEquilibriumTheory
