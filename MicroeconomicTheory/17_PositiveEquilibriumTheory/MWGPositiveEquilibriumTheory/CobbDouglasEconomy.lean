/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.Regularity
import MWGClassicalDemand.UMPExamples
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Cobb-Douglas exchange economies: the concrete instance for Section 17.D

The worked example used by Section 17.D (and named by Exercise 17.D.8, p. 645 and the index
discussion on p. 597): consumers with Cobb-Douglas utility `uᵢ(x) = ∏ₗ xₗ^{aₗᵢ}` on `ℝ^L₊`.

* `cdDemand a p w = (aₗ/∑ₖ aₖ) w/pₗ` is the Walrasian demand of the Cobb-Douglas utility
  (`walrasianDemand_cobbDouglas`, from Kreps's `cobbDouglas_demand`); it is `C¹` in `(p, w)`
  (`contDiffOn_cdDemand`), the differentiability hypothesis of Section 17.D.
* `demandED x ω p = ∑ᵢ (xᵢ(p, p·ωᵢ) - ωᵢ)`, the excess demand built from demand functions; for
  Cobb-Douglas consumers it is the chapter's `excessDemand` of the exchange economy
  (`excessDemand_cdEconomy`) and satisfies (i)-(v) (`cdED_isStandard`), although Cobb-Douglas
  preferences are not strongly monotone on the boundary of `ℝ^L₊`.
* **Exercise 17.D.8** (`exercise_17_D_8`): in a one-consumer Cobb-Douglas economy
  `det Dẑ(p̂) = (∏ₗ -αₗ w/p̂ₗ²)(ω_L/w)` at every `p̂ ≫ 0` (`cd1_det`, by the matrix determinant
  lemma), so the unique equilibrium (`cd1_eqm_iff`) is regular with index `+1`; the economy is
  regular (`cd1_isRegularEconomy`). With (i)-(v) this is a worked instance of Proposition 17.D.1
  (`cd1_finite`) and of the index theorem in every dimension.
-/

namespace MWG.PositiveEquilibriumTheory

open Filter Topology MWG.ConsumerChoice MWG.ClassicalDemand MWG.GeneralEquilibriumExamples

variable {L : ℕ}

/-! ### Demand -/

/-- The Cobb-Douglas demand function `xₗ(p, w) = (aₗ/∑ₖ aₖ) · w/pₗ`. -/
noncomputable def cdDemand (a : Fin L → ℝ) (p : Fin L → ℝ) (w : ℝ) : Fin L → ℝ :=
  fun l => a l / (∑ k, a k) * (w / p l)

/-- The Cobb-Douglas utility `∏ₗ xₗ^{aₗ}` on `ℝ^L₊` (Kreps's `CobbDouglas`, extended). -/
noncomputable def cdUtility (a : Fin L → ℝ) : (Fin L → ℝ) → ℝ :=
  extendOrthant (Kreps.ConsumerDemand.CobbDouglas a)

/-- The Cobb-Douglas Walrasian demand: for `a ≫ 0`, `p ≫ 0`, `w ≥ 0`,
`x(p, w) = {cdDemand a p w}`. -/
theorem walrasianDemand_cobbDouglas [NeZero L] {a : Fin L → ℝ} (ha : ∀ l, 0 < a l)
    {p : Fin L → ℝ} (hp : ∀ l, 0 < p l) {w : ℝ} (hw : 0 ≤ w) :
    walrasianDemand (cdUtility a) p w = {cdDemand a p w} := by
  rw [cdUtility, walrasianDemand_extendOrthant _ hp hw,
    Kreps.ConsumerDemand.cobbDouglas_demand a ha, Set.image_singleton]
  congr 1
  funext l
  simp [Kreps.ConsumerDemand.CobbDouglasBundle, cdDemand, Real.coe_toNNReal w hw]

/-- Cobb-Douglas demand exhausts wealth: `p·x(p, w) = w`. -/
theorem dotProduct_cdDemand [NeZero L] {a : Fin L → ℝ} (ha : ∀ l, 0 < a l) {p : Fin L → ℝ}
    (hp : ∀ l, 0 < p l) (w : ℝ) : p ⬝ᵥ cdDemand a p w = w := by
  have hA : 0 < ∑ k, a k := Finset.sum_pos (fun k _ => ha k) Finset.univ_nonempty
  have hterm : ∀ l, p l * cdDemand a p w l = a l * (w / ∑ k, a k) := fun l => by
    have := (hp l).ne'
    simp only [cdDemand]
    field_simp
  simp only [dotProduct, hterm, ← Finset.sum_mul]
  field_simp

/-- Cobb-Douglas demand is homogeneous of degree zero in `(p, w)`. -/
theorem cdDemand_smul (a p : Fin L → ℝ) (w : ℝ) {α : ℝ} (hα : 0 < α) :
    cdDemand a (α • p) (α * w) = cdDemand a p w := by
  funext l
  simp [cdDemand, mul_div_mul_left _ _ hα.ne']

/-- Cobb-Douglas demand is `C¹` (indeed smooth) on `{p ≫ 0} × (0, ∞)`. -/
theorem contDiffOn_cdDemand (a : Fin L → ℝ) :
    ContDiffOn ℝ 1 (fun r : (Fin L → ℝ) × ℝ => cdDemand a r.1 r.2)
      (posOrthant L ×ˢ Set.Ioi 0) := by
  refine contDiffOn_pi.2 fun l => ?_
  simp only [cdDemand]
  refine contDiffOn_const.mul (contDiff_snd.contDiffOn.div ?_ fun r hr => (hr.1 l).ne')
  exact ((contDiff_apply ℝ ℝ l).comp contDiff_fst).contDiffOn

/-! ### Excess demand from demand functions -/

/-- `z(p; ω) = ∑ᵢ (xᵢ(p, p·ωᵢ) - ωᵢ)`: the aggregate excess demand of consumers with demand
functions `xᵢ(p, w)` and endowments `ωᵢ` (Definition 17.B.2, as a function of `ω`). -/
noncomputable def demandED {ι : Type*} [Fintype ι] (x : ι → (Fin L → ℝ) → ℝ → Fin L → ℝ)
    (ω : ι → Fin L → ℝ) (p : Fin L → ℝ) : Fin L → ℝ :=
  ∑ i, (x i p (p ⬝ᵥ ω i) - ω i)

/-- Wealth `p·ω ≥ 0` at `p ≫ 0`, `ω ≥ 0`. -/
theorem cd_wealth_nonneg {p ω : Fin L → ℝ} (hp : ∀ l, 0 < p l) (hω : ω ∈ nonnegOrthant L) :
    0 ≤ p ⬝ᵥ ω :=
  Finset.sum_nonneg fun l _ => mul_nonneg (hp l).le (hω l)

/-- The Cobb-Douglas exchange economy with exponents `aᵢ` and endowments `ωᵢ`. -/
noncomputable def cdEconomy {ι : Type*} (a ω : ι → Fin L → ℝ) : ExchangeEconomy ι L :=
  ExchangeEconomy.ofOrthant (fun i => cdUtility (a i)) ω

/-- The excess demand of the Cobb-Douglas economy is `demandED cdDemand` at `p ≫ 0`. -/
theorem excessDemand_cdEconomy [NeZero L] {ι : Type*} [Fintype ι] {a ω : ι → Fin L → ℝ}
    (ha : ∀ i l, 0 < a i l) (hω : ∀ i, ω i ∈ nonnegOrthant L) {p : Fin L → ℝ}
    (hp : p ∈ posOrthant L) :
    excessDemand (cdEconomy a ω) p = demandED (fun i => cdDemand (a i)) ω p := by
  unfold excessDemand demandED indivExcessDemand
  refine Finset.sum_congr rfl fun i _ => ?_
  have hw : 0 ≤ p ⬝ᵥ ω i := cd_wealth_nonneg hp (hω i)
  have hd : (cdEconomy a ω).demand i p = {cdDemand (a i) p (p ⬝ᵥ ω i)} :=
    walrasianDemand_cobbDouglas (ha i) hp hw
  rw [demandFn_eq _ hd]
  rfl

/-- **Section 17.B**, instance: the Cobb-Douglas excess demand satisfies (i)-(v) of Proposition
17.B.2 when `aᵢ ≫ 0`, `ωᵢ ≥ 0` and `∑ᵢ ωᵢ ≫ 0` (`L ≥ 1`, `I ≥ 1`). -/
theorem cdED_isStandard [NeZero L] {ι : Type*} [Fintype ι] {a ω : ι → Fin L → ℝ}
    (ha : ∀ i l, 0 < a i l) (hω : ∀ i, ω i ∈ nonnegOrthant L) (htot : ∀ l, 0 < ∑ i, ω i l) :
    IsStandardExcessDemand (demandED (fun i => cdDemand (a i)) ω) := by
  have hA : ∀ i, 0 < ∑ k, a i k := fun i =>
    Finset.sum_pos (fun k _ => ha i k) Finset.univ_nonempty
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine continuousOn_finsetSum _ fun i _ => ContinuousOn.sub ?_ continuousOn_const
    refine continuousOn_pi.2 fun l => ?_
    simp only [cdDemand]
    refine continuousOn_const.mul (ContinuousOn.div ?_ (continuous_apply l).continuousOn
      fun p hp => (hp l).ne')
    exact (continuous_id.dotProduct continuous_const).continuousOn
  · intro p hp α hα
    unfold demandED
    refine Finset.sum_congr rfl fun i _ => ?_
    change cdDemand (a i) (α • p) ((α • p) ⬝ᵥ ω i) - ω i = cdDemand (a i) p (p ⬝ᵥ ω i) - ω i
    rw [smul_dotProduct, smul_eq_mul, cdDemand_smul _ _ _ hα]
  · intro p hp
    simp only [demandED, dotProduct_sum, dotProduct_sub, dotProduct_cdDemand (ha _) hp, sub_self,
      Finset.sum_const_zero]
  · refine ⟨∑ l, ∑ i, ω i l + 1, add_pos_of_nonneg_of_pos
      (Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun i _ => hω i l) one_pos,
      fun p hp l => ?_⟩
    have hle : ∑ i, ω i l ≤ ∑ l, ∑ i, ω i l :=
      Finset.single_le_sum (f := fun l => ∑ i, ω i l)
        (fun k _ => Finset.sum_nonneg fun i _ => hω i k) (Finset.mem_univ l)
    have hx : ∀ i, 0 ≤ cdDemand (a i) p (p ⬝ᵥ ω i) l := fun i =>
      mul_nonneg (div_pos (ha i l) (hA i)).le
        (div_nonneg (cd_wealth_nonneg hp (hω i)) (hp l).le)
    have : -∑ i, ω i l ≤ demandED (fun i => cdDemand (a i)) ω p l := by
      simp only [demandED, Finset.sum_apply, Pi.sub_apply, Finset.sum_sub_distrib]
      linarith [Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => hx i]
    linarith
  · intro ps p hps hlim hp0 hpl M
    obtain ⟨l, hl⟩ := hpl
    have hnn := nonneg_of_tendsto_pos hps hlim
    set ωt : Fin L → ℝ := ∑ i, ω i
    have hωt : ∀ k, ωt k = ∑ i, ω i k := fun k => by simp [ωt, Finset.sum_apply]
    have hW : 0 < p ⬝ᵥ ωt := dotProduct_pos_of_ne_zero hnn hp0 fun k => by
      rw [hωt]; exact htot k
    set W := p ⬝ᵥ ωt
    -- the smallest budget share of good `l`
    have hι : (Finset.univ : Finset ι).Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty, Finset.univ_eq_empty_iff] at h
      have := htot l
      simp at this
    obtain ⟨i0, -, hi0⟩ := Finset.exists_min_image Finset.univ
      (fun i => a i l / ∑ k, a i k) hι
    set c := a i0 l / ∑ k, a i0 k
    have hc : 0 < c := div_pos (ha i0 l) (hA i0)
    set s := ∑ i, ω i l
    have hWlim : Tendsto (fun m => ps m ⬝ᵥ ωt) atTop (𝓝 W) :=
      (continuous_id.dotProduct continuous_const).continuousAt.tendsto.comp hlim
    have hl0 : Tendsto (fun m => ps m l) atTop (𝓝 0) := by
      rw [← hl]; exact ((continuous_apply l).tendsto p).comp hlim
    set δ := c * (W / 2) / (|M| + s + 1)
    have hδ : 0 < δ := by
      have : 0 ≤ s := Finset.sum_nonneg fun i _ => hω i l
      positivity
    filter_upwards [hWlim.eventually (lt_mem_nhds (half_lt_self hW)),
      hl0.eventually (gt_mem_nhds hδ)] with m hm1 hm2
    refine ⟨l, ?_⟩
    have hpm := hps m
    have hpl := hpm l
    have hterm : ∀ i, c * (ps m ⬝ᵥ ω i) / ps m l ≤ cdDemand (a i) (ps m) (ps m ⬝ᵥ ω i) l := by
      intro i
      have hwi : 0 ≤ ps m ⬝ᵥ ω i := cd_wealth_nonneg hpm (hω i)
      simp only [cdDemand]
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_right (hi0 i (Finset.mem_univ i)) (div_nonneg hwi hpl.le)
    have hsum : c * (ps m ⬝ᵥ ωt) / ps m l ≤
        ∑ i, cdDemand (a i) (ps m) (ps m ⬝ᵥ ω i) l := by
      have : ps m ⬝ᵥ ωt = ∑ i, ps m ⬝ᵥ ω i := by simp [ωt, dotProduct_sum]
      rw [this, Finset.mul_sum, Finset.sum_div]
      exact Finset.sum_le_sum fun i _ => hterm i
    have hbig : |M| + s + 1 < c * (ps m ⬝ᵥ ωt) / ps m l := by
      rw [lt_div_iff₀ hpl]
      have h1 : δ * (|M| + s + 1) = c * (W / 2) := by
        simp only [δ]
        have : 0 < |M| + s + 1 := by
          have : 0 ≤ s := Finset.sum_nonneg fun i _ => hω i l
          positivity
        field_simp
      have h2 : (|M| + s + 1) * ps m l < (|M| + s + 1) * δ := by
        have : 0 < |M| + s + 1 := by
          have : 0 ≤ s := Finset.sum_nonneg fun i _ => hω i l
          positivity
        exact mul_lt_mul_of_pos_left hm2 this
      have h3 : c * (W / 2) < c * (ps m ⬝ᵥ ωt) := mul_lt_mul_of_pos_left hm1 hc
      nlinarith
    have heq : demandED (fun i => cdDemand (a i)) ω (ps m) l =
        ∑ i, cdDemand (a i) (ps m) (ps m ⬝ᵥ ω i) l - s := by
      simp [demandED, Finset.sum_apply, Finset.sum_sub_distrib, s]
    rw [heq]
    linarith [le_abs_self M]

/-! ### One consumer: Exercise 17.D.8 -/

/-- The excess demand of a one-consumer Cobb-Douglas economy: `z(p) = x(p, p·ω) - ω`. -/
noncomputable def cd1ED (a ω : Fin L → ℝ) (p : Fin L → ℝ) : Fin L → ℝ :=
  cdDemand a p (p ⬝ᵥ ω) - ω

/-- The one-consumer economy is the case `I = 1` of `demandED`. -/
theorem cd1ED_eq (a ω : Fin L → ℝ) :
    cd1ED a ω = demandED (fun _ : Fin 1 => cdDemand a) (fun _ => ω) := by
  funext p
  simp [cd1ED, demandED]

/-- The one-consumer Cobb-Douglas excess demand satisfies (i)-(v) (`a ≫ 0`, `ω ≫ 0`). -/
theorem cd1ED_isStandard [NeZero L] {a ω : Fin L → ℝ} (ha : ∀ l, 0 < a l)
    (hω : ∀ l, 0 < ω l) : IsStandardExcessDemand (cd1ED a ω) := by
  rw [cd1ED_eq]
  exact cdED_isStandard (fun _ => ha) (fun _ l => (hω l).le) fun l => by simpa using hω l

variable {n : ℕ}

/-- The matrix determinant lemma for a diagonal matrix plus a rank-one matrix:
`det(diag d + u vᵀ) = (∏ₗ dₗ)(1 + ∑ₗ vₗ uₗ / dₗ)`. -/
theorem det_diagonal_add_vecMulVec (d u v : Fin n → ℝ) (hd : ∀ l, d l ≠ 0) :
    (Matrix.diagonal d + Matrix.vecMulVec u v).det =
      (∏ l, d l) * (1 + ∑ l, v l * (u l / d l)) := by
  have hfac : Matrix.diagonal d + Matrix.vecMulVec u v =
      Matrix.diagonal d * (1 + Matrix.vecMulVec (fun l => u l / d l) v) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.diagonal_mul, Matrix.vecMulVec_apply,
      Matrix.diagonal_apply, Matrix.one_apply]
    have := hd i
    split_ifs <;> (field_simp; try ring)
  rw [hfac, Matrix.det_mul, Matrix.det_diagonal, Matrix.vecMulVec_eq (ι := Unit),
    Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp [dotProduct]

/-- The wealth `(p̂, 1)·ω = ∑_{ℓ<L} p̂ₗ ωₗ + ω_L`. -/
theorem normPrice_dotProduct (q : Fin n → ℝ) (ω : Fin (n + 1) → ℝ) :
    normPrice q ⬝ᵥ ω = ∑ k, q k * ω (Fin.castSucc k) + ω (Fin.last n) := by
  simp [dotProduct, Fin.sum_univ_castSucc]

/-- The matrix of price effects `Dẑ(p̂)` of the one-consumer Cobb-Douglas economy:
`∂ẑₗ/∂p̂ₖ = αₗ ωₖ/p̂ₗ - δₗₖ αₗ w/p̂ₗ²` with `αₗ = aₗ/∑ a`, `w = (p̂, 1)·ω`. -/
noncomputable def cd1Jacobian (a ω : Fin (n + 1) → ℝ) (q : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (fun l => -(a (Fin.castSucc l) / (∑ k, a k)) * (normPrice q ⬝ᵥ ω) / q l ^ 2) +
    Matrix.vecMulVec (fun l => a (Fin.castSucc l) / (∑ k, a k) / q l)
      (fun k => ω (Fin.castSucc k))

/-- `ẑ` of the one-consumer Cobb-Douglas economy is differentiable at every `p̂ ≫ 0` with matrix
of price effects `cd1Jacobian`. -/
theorem cd1_hasFDerivAt (a ω : Fin (n + 1) → ℝ) {q : Fin n → ℝ} (hq : q ∈ posOrthant n) :
    HasFDerivAt (normED (cd1ED a ω))
      (LinearMap.toContinuousLinearMap (Matrix.toLin' (cd1Jacobian a ω q))) q := by
  set ω' : Fin n → ℝ := fun k => ω (Fin.castSucc k)
  have hform : normED (cd1ED a ω) = fun q : Fin n → ℝ => fun l =>
      a (Fin.castSucc l) / (∑ k, a k) * ((∑ k, q k * ω' k + ω (Fin.last n)) * (q l)⁻¹) - ω' l := by
    funext q l
    simp [normED, truncExcessDemand, cd1ED, cdDemand, normPrice_dotProduct, ω',
      div_eq_mul_inv]
  rw [hform]
  refine hasFDerivAt_pi'' fun l => ?_
  have hS : HasFDerivAt (fun q : Fin n → ℝ => ∑ k, q k * ω' k + ω (Fin.last n))
      (∑ k, ω' k • (ContinuousLinearMap.proj k : (Fin n → ℝ) →L[ℝ] ℝ)) q := by
    refine (HasFDerivAt.fun_sum fun k _ => ?_).add_const _
    exact (hasFDerivAt_apply k q).mul_const (ω' k)
  have hinv : HasFDerivAt (fun q : Fin n → ℝ => (q l)⁻¹)
      ((ContinuousLinearMap.toSpanSingleton ℝ (-(q l ^ 2)⁻¹)).comp
        (ContinuousLinearMap.proj l : (Fin n → ℝ) →L[ℝ] ℝ)) q :=
    (hasFDerivAt_inv (hq l).ne').comp q (hasFDerivAt_apply l q)
  have h := ((hS.mul hinv).const_mul (a (Fin.castSucc l) / (∑ k, a k))).sub_const (ω' l)
  have key : ∀ v : Fin n → ℝ, (cd1Jacobian a ω q).mulVec v l =
      a (Fin.castSucc l) / (∑ k, a k) * ((∑ k, q k * ω' k + ω (Fin.last n)) * (-(q l ^ 2)⁻¹ * v l) +
        (q l)⁻¹ * ∑ k, ω' k * v k) := by
    intro v
    have hql := (hq l).ne'
    rw [cd1Jacobian, Matrix.add_mulVec, Pi.add_apply, Matrix.mulVec_diagonal,
      normPrice_dotProduct]
    simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply]
    rw [show ∑ x, a (Fin.castSucc l) / (∑ k, a k) / q l * ω' x * v x =
      a (Fin.castSucc l) / (∑ k, a k) / q l * ∑ x, ω' x * v x by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring]
    field_simp
    ring
  convert h using 1
  ext v
  have hl : ((ContinuousLinearMap.proj l).comp
      (LinearMap.toContinuousLinearMap (Matrix.toLin' (cd1Jacobian a ω q)))) v =
      (cd1Jacobian a ω q).mulVec v l := rfl
  rw [hl, key v]
  simp
  ring

/-- **Exercise 17.D.8**, the determinant: at every `p̂ ≫ 0`,
`det Dẑ(p̂) = (∏ₗ (-αₗ w/p̂ₗ²)) · ω_L/w`. -/
theorem cd1_det {a ω : Fin (n + 1) → ℝ} (ha : ∀ l, 0 < a l) (hω : ∀ l, 0 < ω l)
    {q : Fin n → ℝ} (hq : q ∈ posOrthant n) :
    (cd1Jacobian a ω q).det = (∏ l, -(a (Fin.castSucc l) / (∑ k, a k)) *
      (normPrice q ⬝ᵥ ω) / q l ^ 2) * (ω (Fin.last n) / (normPrice q ⬝ᵥ ω)) := by
  have hA : 0 < ∑ k, a k := Finset.sum_pos (fun k _ => ha k) Finset.univ_nonempty
  have hw : 0 < normPrice q ⬝ᵥ ω := by
    rw [normPrice_dotProduct]
    have := Finset.sum_nonneg fun k (_ : k ∈ Finset.univ) =>
      (mul_pos (hq k) (hω (Fin.castSucc k))).le
    linarith [hω (Fin.last n)]
  rw [cd1Jacobian, det_diagonal_add_vecMulVec _ _ _ fun l =>
    div_ne_zero (mul_ne_zero (neg_ne_zero.2 (div_pos (ha _) hA).ne') hw.ne')
      (pow_pos (hq l) 2).ne']
  congr 1
  have hterm : ∀ l, ω (Fin.castSucc l) * (a (Fin.castSucc l) / (∑ k, a k) / q l /
      (-(a (Fin.castSucc l) / ∑ k, a k) * (normPrice q ⬝ᵥ ω) / q l ^ 2)) =
      -(q l * ω (Fin.castSucc l)) / (normPrice q ⬝ᵥ ω) := fun l => by
    have := (hq l).ne'
    have := (ha (Fin.castSucc l)).ne'
    field_simp
  simp only [hterm]
  rw [← Finset.sum_div, Finset.sum_neg_distrib]
  have hsum := normPrice_dotProduct q ω
  field_simp
  linarith

/-- The sign of `det Dẑ(p̂)` in the one-consumer Cobb-Douglas economy is `(-1)^{L-1}`. -/
theorem cd1_sign_det {a ω : Fin (n + 1) → ℝ} (ha : ∀ l, 0 < a l) (hω : ∀ l, 0 < ω l)
    {q : Fin n → ℝ} (hq : q ∈ posOrthant n) :
    ((SignType.sign (cd1Jacobian a ω q).det : SignType) : ℤ) = (-1) ^ n := by
  have hA : 0 < ∑ k, a k := Finset.sum_pos (fun k _ => ha k) Finset.univ_nonempty
  have hw : 0 < normPrice q ⬝ᵥ ω := by
    rw [normPrice_dotProduct]
    have := Finset.sum_nonneg fun k (_ : k ∈ Finset.univ) =>
      (mul_pos (hq k) (hω (Fin.castSucc k))).le
    linarith [hω (Fin.last n)]
  rw [cd1_det ha hω hq]
  have hneg : ∀ l, -(a (Fin.castSucc l) / ∑ k, a k) * (normPrice q ⬝ᵥ ω) / q l ^ 2 =
      -1 * (a (Fin.castSucc l) / (∑ k, a k) * (normPrice q ⬝ᵥ ω) / q l ^ 2) := fun l => by ring
  simp only [hneg, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  have hpos : 0 < (∏ l, a (Fin.castSucc l) / (∑ k, a k) * (normPrice q ⬝ᵥ ω) / q l ^ 2) *
      (ω (Fin.last n) / (normPrice q ⬝ᵥ ω)) := by
    refine mul_pos (Finset.prod_pos fun l _ => ?_) (div_pos (hω _) hw)
    have := hq l; have := ha (Fin.castSucc l); positivity
  rw [mul_assoc]
  rcases Nat.even_or_odd n with he | ho
  · rw [he.neg_one_pow, one_mul, sign_pos hpos, he.neg_one_pow]
    rfl
  · rw [ho.neg_one_pow, neg_one_mul, sign_neg (neg_neg_of_pos hpos), ho.neg_one_pow]
    rfl

/-- The normalized equilibria of the one-consumer Cobb-Douglas economy: `p̂ ≫ 0` is an equilibrium
iff `p̂ₗ = (αₗ/α_L)(ω_L/ωₗ)` for every `ℓ < L` (relative prices
`pₗ/p_L = (αₗ/ωₗ)/(α_L/ω_L)`). -/
theorem cd1_eqm_iff {a ω : Fin (n + 1) → ℝ} (ha : ∀ l, 0 < a l) (hω : ∀ l, 0 < ω l)
    {q : Fin n → ℝ} :
    IsNormEqm (cd1ED a ω) q ↔ ∀ l, q l = a (Fin.castSucc l) / a (Fin.last n) *
      (ω (Fin.last n) / ω (Fin.castSucc l)) := by
  have hA : 0 < ∑ k, a k := Finset.sum_pos (fun k _ => ha k) Finset.univ_nonempty
  constructor
  · rintro ⟨hp, hz⟩ l
    have hq := normPrice_mem_posOrthant.1 hp
    have hL := congrFun hz (Fin.last n)
    have hl := congrFun hz (Fin.castSucc l)
    simp only [cd1ED, cdDemand, Pi.sub_apply, normPrice_last, normPrice_castSucc,
      Pi.zero_apply, div_one] at hL hl
    have hql := (hq l).ne'
    have h1 := (ha (Fin.last n)).ne'
    have h2 := (hω (Fin.castSucc l)).ne'
    have hAne := hA.ne'
    have hw : normPrice q ⬝ᵥ ω = ω (Fin.last n) * (∑ k, a k) / a (Fin.last n) := by
      rw [sub_eq_zero] at hL
      field_simp at hL ⊢
      linarith
    have e1 : q l = a (Fin.castSucc l) / (∑ k, a k) * (normPrice q ⬝ᵥ ω) /
        ω (Fin.castSucc l) := by
      rw [sub_eq_zero] at hl
      field_simp at hl ⊢
      linarith
    rw [e1, hw]
    field_simp
  · intro h
    have hq : q ∈ posOrthant n := fun l => by
      rw [h l]; have := ha (Fin.castSucc l); have := ha (Fin.last n)
      have := hω (Fin.last n); have := hω (Fin.castSucc l); positivity
    have hp := normPrice_mem_posOrthant.2 hq
    -- the wealth
    have hw : normPrice q ⬝ᵥ ω = ω (Fin.last n) * (∑ k, a k) / a (Fin.last n) := by
      rw [dotProduct, Fin.sum_univ_castSucc]
      simp only [normPrice_castSucc, normPrice_last, one_mul, h]
      have hterm : ∀ k : Fin n, a (Fin.castSucc k) / a (Fin.last n) *
          (ω (Fin.last n) / ω (Fin.castSucc k)) * ω (Fin.castSucc k) =
          ω (Fin.last n) / a (Fin.last n) * a (Fin.castSucc k) := fun k => by
        have := (hω (Fin.castSucc k)).ne'
        have := (ha (Fin.last n)).ne'
        field_simp
      simp only [hterm, ← Finset.mul_sum]
      rw [Fin.sum_univ_castSucc (f := a)]
      have := (ha (Fin.last n)).ne'
      field_simp
    refine ⟨hp, funext fun k => ?_⟩
    refine Fin.lastCases ?_ (fun l => ?_) k
    · simp only [cd1ED, cdDemand, Pi.sub_apply, normPrice_last, hw, Pi.zero_apply]
      have := (ha (Fin.last n)).ne'
      field_simp
      ring
    · simp only [cd1ED, cdDemand, Pi.sub_apply, normPrice_castSucc, hw, Pi.zero_apply, h l]
      have := (ha (Fin.last n)).ne'
      have := (ha (Fin.castSucc l)).ne'
      have := (hω (Fin.castSucc l)).ne'
      have := (hω (Fin.last n)).ne'
      field_simp
      ring

/-- **Exercise 17.D.8** (MWG, p. 645). By explicit computation, the index of the equilibrium of a
one-consumer Cobb-Douglas pure exchange economy (`a ≫ 0`, `ω ≫ 0`) is `+1`: the equilibrium
exists, is unique and regular, and `index = (-1)^{L-1} sign |Dẑ| = (-1)^{L-1}(-1)^{L-1} = 1`. -/
theorem exercise_17_D_8 {a ω : Fin (n + 1) → ℝ} (ha : ∀ l, 0 < a l) (hω : ∀ l, 0 < ω l) :
    ∃! q, IsNormEqm (cd1ED a ω) q ∧ IsRegularEqm (cd1ED a ω) q ∧ eqmIndex (cd1ED a ω) q = 1 := by
  set q₀ : Fin n → ℝ := fun l => a (Fin.castSucc l) / a (Fin.last n) *
    (ω (Fin.last n) / ω (Fin.castSucc l))
  have heq : IsNormEqm (cd1ED a ω) q₀ := (cd1_eqm_iff ha hω).2 fun l => rfl
  have hq := normPrice_mem_posOrthant.1 heq.1
  have hD := cd1_hasFDerivAt a ω hq
  have hdet : (fderiv ℝ (normED (cd1ED a ω)) q₀).det = (cd1Jacobian a ω q₀).det := by
    rw [hD.fderiv, ContinuousLinearMap.det, LinearMap.coe_toContinuousLinearMap,
      ← LinearMap.det_toMatrix', LinearMap.toMatrix'_toLin']
  have hsign := cd1_sign_det ha hω hq
  have hne : (cd1Jacobian a ω q₀).det ≠ 0 := by
    intro h0
    rw [h0, sign_zero] at hsign
    rcases neg_one_pow_eq_or ℤ n with h | h <;> rw [h] at hsign <;> simp at hsign
  refine ⟨q₀, ⟨heq, ⟨heq, hD.differentiableAt, by rwa [hdet]⟩, ?_⟩, ?_⟩
  · rw [eqmIndex, hdet, hsign, ← pow_add, ← two_mul, pow_mul]
    simp
  · rintro q ⟨hq', -⟩
    funext l
    exact (cd1_eqm_iff ha hω).1 hq' l

/-- The one-consumer Cobb-Douglas economy is regular (Definition 17.D.1), every equilibrium
having index `+1`. -/
theorem cd1_isRegularEconomy {a ω : Fin (n + 1) → ℝ} (ha : ∀ l, 0 < a l) (hω : ∀ l, 0 < ω l) :
    IsRegularEconomy (cd1ED a ω) := by
  intro q hq
  obtain ⟨q₀, ⟨-, hreg, -⟩, huniq⟩ := exercise_17_D_8 ha hω
  have := (cd1_eqm_iff ha hω).1 hq
  have hq0 := (cd1_eqm_iff ha hω).1 hreg.1
  have : q = q₀ := funext fun l => by rw [this l, hq0 l]
  rw [this]
  exact hreg

/-- **Proposition 17.D.1**, instance: the one-consumer Cobb-Douglas economy satisfies (i)-(v)
and is regular, so it has finitely many normalized equilibria (in fact exactly one). -/
theorem cd1_finite {a ω : Fin (n + 1) → ℝ} (ha : ∀ l, 0 < a l) (hω : ∀ l, 0 < ω l) :
    {q | IsNormEqm (cd1ED a ω) q}.Finite :=
  proposition_17_D_1_finite (cd1ED_isStandard ha hω) (cd1_isRegularEconomy ha hω)

end MWG.PositiveEquilibriumTheory
