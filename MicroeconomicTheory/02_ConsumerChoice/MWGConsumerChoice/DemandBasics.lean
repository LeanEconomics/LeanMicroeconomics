/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGConsumerChoice.WalrasianBudget
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Data.Set.Card

/-!
# Walrasian demand: homogeneity, Walras' law and comparative-statics notation

MWG, Section 2.E, pp. 23–26, and Exercises 2.E.1 (p. 23) and 2.E.7 (p. 37).

* Walrasian demand correspondences and functions on the domain `p ≫ 0`, `w > 0`;
  homogeneity of degree zero (Definition 2.E.1) and Walras' law (Definition 2.E.2), with the
  single-valued case bridged to the singleton correspondence.
* `B_{αp,αw} = B_{p,w}` (p. 23); Walrasian budget sets determine `(p, w)` up to scale, so a
  homogeneous demand depends only on the budget set (the choice-structure remark, p. 24); no
  finite set (in particular no two- or three-element set) is a Walrasian budget set.
* Normalisations `p_ℓ = 1` and `w = 1` (p. 24).
* Notation for derivatives: a derivative `D` of `(p, w) ↦ x(p, w)` at `(p, w)` is a
  continuous linear map; `∂x_ℓ/∂p_k` and `∂x_ℓ/∂w` are its values at coordinate directions,
  `D_p x` and `D_w x` collect them (pp. 25–26), and `D(v, c) = D_p x · v + c D_w x`.
* Engel functions, wealth expansion paths, normal, inferior and Giffen goods (pp. 24–26).
* Exercise 2.E.1: the given demand is homogeneous of degree zero for every `β`, and satisfies
  Walras' law if and only if `β = 1`. Exercise 2.E.7.
-/

namespace MWG.ConsumerChoice

/-- **Section 2.D–2.E** (MWG, pp. 21, 23). The price–wealth domain `p ≫ 0`, `w > 0`. -/
def PWDomain {L : ℕ} (p : Fin L → ℝ) (w : ℝ) : Prop := StrictlyPositive p ∧ 0 < w

/-- **Section 2.E** (MWG, p. 23). A Walrasian demand correspondence `x(p, w)`. -/
abbrev DemandCorrespondence (L : ℕ) := (Fin L → ℝ) → ℝ → Set (Fin L → ℝ)

/-- **Section 2.E** (MWG, p. 23). A single-valued Walrasian demand function `x(p, w)`. -/
abbrev DemandFunction (L : ℕ) := (Fin L → ℝ) → ℝ → Fin L → ℝ

/-- **Definition 2.E.1** (MWG, p. 23). The demand correspondence is homogeneous of degree zero:
`x(αp, αw) = x(p, w)` for all `p ≫ 0`, `w > 0`, `α > 0`. -/
def HomogeneousZeroCorr {L : ℕ} (x : DemandCorrespondence L) : Prop :=
  ∀ p w α, PWDomain p w → 0 < α → x (α • p) (α * w) = x p w

/-- **Definition 2.E.2** (MWG, p. 23). Walras' law: `p·x = w` for every `x ∈ x(p, w)`,
`p ≫ 0`, `w > 0`. -/
def WalrasLawCorr {L : ℕ} (x : DemandCorrespondence L) : Prop :=
  ∀ p w, PWDomain p w → ∀ y ∈ x p w, p ⬝ᵥ y = w

/-- **Definition 2.E.1** (MWG, p. 23) for a demand function. -/
def HomogeneousZero {L : ℕ} (x : DemandFunction L) : Prop :=
  ∀ p w α, PWDomain p w → 0 < α → x (α • p) (α * w) = x p w

/-- **Definition 2.E.2** (MWG, p. 23) for a demand function. -/
def WalrasLaw {L : ℕ} (x : DemandFunction L) : Prop := ∀ p w, PWDomain p w → p ⬝ᵥ x p w = w

/-- The singleton correspondence of a demand function. -/
def toCorrespondence {L : ℕ} (x : DemandFunction L) : DemandCorrespondence L :=
  fun p w => {x p w}

/-- Homogeneity of a demand function is homogeneity of its singleton correspondence. -/
theorem homogeneousZero_iff_corr {L : ℕ} (x : DemandFunction L) :
    HomogeneousZero x ↔ HomogeneousZeroCorr (toCorrespondence x) := by
  constructor
  · intro h p w α hd ha
    simp only [toCorrespondence, h p w α hd ha]
  · intro h p w α hd ha
    have := h p w α hd ha
    simpa [toCorrespondence] using this

/-- Walras' law for a demand function is Walras' law for its singleton correspondence. -/
theorem walrasLaw_iff_corr {L : ℕ} (x : DemandFunction L) :
    WalrasLaw x ↔ WalrasLawCorr (toCorrespondence x) := by
  constructor
  · intro h p w hd y hy
    rw [Set.mem_singleton_iff.mp hy]
    exact h p w hd
  · intro h p w hd
    exact h p w hd _ rfl

/-- Scaling preserves the domain. -/
theorem pwDomain_smul {L : ℕ} {p : Fin L → ℝ} {w α : ℝ} (hd : PWDomain p w) (ha : 0 < α) :
    PWDomain (α • p) (α * w) :=
  ⟨fun l => by simpa using mul_pos ha (hd.1 l), mul_pos ha hd.2⟩

/-- **Section 2.E** (MWG, p. 23). A proportional change in prices and wealth leaves the budget
set unchanged: `B_{αp,αw} = B_{p,w}` for `α > 0`. -/
theorem budgetSet_smul {L : ℕ} (p : Fin L → ℝ) (w : ℝ) {α : ℝ} (ha : 0 < α) :
    budgetSet (α • p) (α * w) = budgetSet p w := by
  ext y
  simp only [budgetSet, Set.mem_ofPred_eq, smul_dotProduct, smul_eq_mul]
  constructor
  · rintro ⟨hy, hb⟩
    exact ⟨hy, le_of_mul_le_mul_left hb ha⟩
  · rintro ⟨hy, hb⟩
    exact ⟨hy, mul_le_mul_of_nonneg_left hb ha.le⟩

/-- The vertex `(w/p_ℓ) e_ℓ` is a budget point. -/
theorem vertex_mem_budgetSet {L : ℕ} {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w) (l : Fin L) :
    Pi.single l (w / p l) ∈ budgetSet p w := by
  refine ⟨fun k => ?_, ?_⟩
  · by_cases hk : k = l
    · subst hk
      simpa using div_nonneg hd.2.le (hd.1 k).le
    · simp [hk]
  · rw [dotProduct_single, mul_div_cancel₀ _ (hd.1 l).ne']

/-- Walrasian budget sets determine price–wealth pairs up to scale: `B_{p,w} = B_{p',w'}`
forces `(p', w') = (w'/w)(p, w)`. -/
theorem budgetSet_eq_imp_proportional {L : ℕ} {p p' : Fin L → ℝ} {w w' : ℝ}
    (hd : PWDomain p w) (hd' : PWDomain p' w') (h : budgetSet p w = budgetSet p' w') :
    p' = (w' / w) • p := by
  funext l
  have h1 : Pi.single l (w / p l) ∈ budgetSet p' w' := h ▸ vertex_mem_budgetSet hd l
  have h2 : Pi.single l (w' / p' l) ∈ budgetSet p w := h ▸ vertex_mem_budgetSet hd' l
  have b1 := h1.2
  have b2 := h2.2
  rw [dotProduct_single] at b1 b2
  have hp := hd.1 l
  have hp' := hd'.1 l
  have hw := hd.2
  have hw' := hd'.2
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [mul_div_assoc', div_le_iff₀ hp] at b1
  rw [mul_div_assoc', div_le_iff₀ hp'] at b2
  field_simp
  linarith

/-- **Section 2.E** (MWG, p. 24). Under homogeneity of degree zero, demand depends only on the
budget set: `B_{p,w} = B_{p',w'}` implies `x(p, w) = x(p', w')`. Hence `(𝓑^W, x(·))` is a
choice structure. -/
theorem demand_depends_only_on_budget {L : ℕ} {x : DemandFunction L} (hx : HomogeneousZero x)
    {p p' : Fin L → ℝ} {w w' : ℝ} (hd : PWDomain p w) (hd' : PWDomain p' w')
    (h : budgetSet p w = budgetSet p' w') : x p w = x p' w' := by
  have hp := budgetSet_eq_imp_proportional hd hd' h
  have ha : 0 < w' / w := div_pos hd'.2 hd.2
  have hw : w' = (w' / w) * w := by field_simp [hd.2.ne']
  calc x p w = x ((w' / w) • p) ((w' / w) * w) := (hx p w _ hd ha).symm
    _ = x p' w' := by rw [← hp, ← hw]

/-- **Section 2.E** (MWG, p. 24). The family of Walrasian budget sets
`𝓑^W = {B_{p,w} : p ≫ 0, w > 0}`. -/
def walrasianBudgetFamily (L : ℕ) : Set (Set (Fin L → ℝ)) :=
  {B | ∃ p w, PWDomain p w ∧ B = budgetSet p w}

/-- With at least one good, every Walrasian budget set is infinite. -/
theorem budgetSet_infinite {L : ℕ} {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w) (l : Fin L) :
    (budgetSet p w).Infinite := by
  have hpos : 0 < w / p l := div_pos hd.2 (hd.1 l)
  let f : ℕ → Fin L → ℝ := fun n => Pi.single l ((1 / ((n : ℝ) + 1)) * (w / p l))
  have hinj : Function.Injective f := by
    intro a b hab
    have := congrFun hab l
    simp only [f, Pi.single_eq_same] at this
    have h2 := mul_right_cancel₀ hpos.ne' this
    have ha : (0 : ℝ) < (a : ℝ) + 1 := by positivity
    have hb : (0 : ℝ) < (b : ℝ) + 1 := by positivity
    field_simp at h2
    exact_mod_cast (by linarith : (a : ℝ) = b)
  have hmem : ∀ n, f n ∈ budgetSet p w := by
    intro n
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have ht0 : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
    have ht1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one hn]
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    refine ⟨fun k => ?_, ?_⟩
    · by_cases hk : k = l
      · subst hk
        simpa [f] using mul_nonneg ht0 hpos.le
      · simp [f, hk]
    · simp only [f]
      rw [dotProduct_single]
      have : p l * (1 / ((n : ℝ) + 1) * (w / p l)) = 1 / ((n : ℝ) + 1) * w := by
        field_simp [(hd.1 l).ne']
      rw [this]
      nlinarith [hd.2]
  exact Set.infinite_of_injective_forall_mem hinj hmem

/-- **Section 2.E** (MWG, p. 24). With at least one good, `𝓑^W` contains no finite set; in
particular no two- or three-element subset of `X` is a Walrasian budget set. -/
theorem finite_not_mem_walrasianBudgetFamily {L : ℕ} (l : Fin L) {B : Set (Fin L → ℝ)}
    (hB : B.Finite) : B ∉ walrasianBudgetFamily L := by
  rintro ⟨p, w, hd, rfl⟩
  exact budgetSet_infinite hd l hB

/-- **Section 2.E** (MWG, p. 24). Normalisation `p_ℓ = 1`: under homogeneity of degree zero,
`x(p, w) = x(p/p_ℓ, w/p_ℓ)`. -/
theorem normalize_price {L : ℕ} {x : DemandFunction L} (hx : HomogeneousZero x)
    {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w) (l : Fin L) :
    x ((p l)⁻¹ • p) (w / p l) = x p w ∧ ((p l)⁻¹ • p) l = 1 := by
  have hp := hd.1 l
  refine ⟨?_, by simp [hp.ne']⟩
  rw [div_eq_inv_mul]
  exact hx p w _ hd (inv_pos.mpr hp)

/-- **Section 2.E** (MWG, p. 24). Normalisation `w = 1`: `x(p, w) = x(p/w, 1)`. -/
theorem normalize_wealth {L : ℕ} {x : DemandFunction L} (hx : HomogeneousZero x)
    {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w) : x (w⁻¹ • p) 1 = x p w := by
  have := hx p w w⁻¹ hd (inv_pos.mpr hd.2)
  rwa [inv_mul_cancel₀ hd.2.ne'] at this

/-! ### Derivative notation -/

/-- **Section 2.E** (MWG, p. 26). The price effect `∂x_ℓ/∂p_k` read off a derivative `D` of
`(p, w) ↦ x(p, w)`. -/
def priceEffect {L : ℕ} (D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)) (l k : Fin L) : ℝ :=
  D (Pi.single k 1, 0) l

/-- **Section 2.E** (MWG, p. 24). The wealth effect `∂x_ℓ/∂w` read off a derivative `D`. -/
def wealthEffect {L : ℕ} (D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)) (l : Fin L) : ℝ :=
  D (0, 1) l

/-- **Section 2.E** (MWG, p. 26). The matrix `D_p x(p, w)` of price effects. -/
def priceJacobian {L : ℕ} (D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)) :
    Matrix (Fin L) (Fin L) ℝ :=
  Matrix.of fun l k => priceEffect D l k

/-- **Section 2.E** (MWG, p. 25). The vector `D_w x(p, w)` of wealth effects. -/
def wealthJacobian {L : ℕ} (D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)) : Fin L → ℝ :=
  fun l => wealthEffect D l

/-- A direction `(v, c)` decomposes along the coordinate directions. -/
theorem prod_eq_sum_single {L : ℕ} (v : Fin L → ℝ) (c : ℝ) :
    ((v, c) : (Fin L → ℝ) × ℝ) =
      ∑ k, v k • ((Pi.single k 1, 0) : (Fin L → ℝ) × ℝ) + c • ((0, 1) : (Fin L → ℝ) × ℝ) := by
  ext
  · simp only [Prod.fst_add, Prod.fst_sum, Prod.smul_mk, smul_zero, add_zero]
    rw [Finset.sum_apply]
    simp [Pi.single_apply]
  · simp [Prod.snd_sum]

/-- The derivative in direction `(v, c)` is `D_p x · v + c · D_w x`, componentwise
`∑_k (∂x_ℓ/∂p_k) v_k + (∂x_ℓ/∂w) c`. -/
theorem deriv_apply_eq {L : ℕ} (D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)) (v : Fin L → ℝ)
    (c : ℝ) (l : Fin L) :
    D (v, c) l = ∑ k, priceEffect D l k * v k + wealthEffect D l * c := by
  rw [prod_eq_sum_single v c, map_add, map_sum]
  simp only [map_smul, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    priceEffect, wealthEffect]
  congr 1
  · exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  · ring

/-- Matrix form: `D(v, c) = D_p x · v + c · D_w x`. -/
theorem deriv_apply_eq_mulVec {L : ℕ} (D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ))
    (v : Fin L → ℝ) (c : ℝ) : D (v, c) = Matrix.mulVec (priceJacobian D) v + c • wealthJacobian D
 := by
  funext l
  rw [deriv_apply_eq]
  simp [Matrix.mulVec, dotProduct, priceJacobian, wealthJacobian, mul_comm]

/-! ### Comparative statics vocabulary -/

/-- **Section 2.E** (MWG, p. 24). The Engel function `w ↦ x(p̄, w)` at fixed prices. -/
def engelFunction {L : ℕ} (x : DemandFunction L) (p : Fin L → ℝ) : ℝ → Fin L → ℝ :=
  fun w => x p w

/-- **Section 2.E** (MWG, p. 24). The wealth expansion path `E_p̄ = {x(p̄, w) : w > 0}`. -/
def wealthExpansionPath {L : ℕ} (x : DemandFunction L) (p : Fin L → ℝ) : Set (Fin L → ℝ) :=
  {y | ∃ w, 0 < w ∧ y = x p w}

/-- **Section 2.E** (MWG, p. 25). Good `ℓ` is normal at `(p, w)`: `∂x_ℓ/∂w ≥ 0`. -/
def NormalAt {L : ℕ} (x : DemandFunction L) (p : Fin L → ℝ) (w : ℝ) (l : Fin L) : Prop :=
  0 ≤ wealthEffect (fderiv ℝ (Function.uncurry x) (p, w)) l

/-- **Section 2.E** (MWG, p. 25). Good `ℓ` is inferior at `(p, w)`: `∂x_ℓ/∂w < 0`. -/
def InferiorAt {L : ℕ} (x : DemandFunction L) (p : Fin L → ℝ) (w : ℝ) (l : Fin L) : Prop :=
  wealthEffect (fderiv ℝ (Function.uncurry x) (p, w)) l < 0

/-- **Section 2.E** (MWG, p. 25). Demand is normal: every good is normal at every `(p, w)`. -/
def NormalDemand {L : ℕ} (x : DemandFunction L) : Prop :=
  ∀ p w, PWDomain p w → ∀ l, NormalAt x p w l

/-- **Section 2.E** (MWG, p. 26). Good `ℓ` is a Giffen good at `(p, w)`: `∂x_ℓ/∂p_ℓ > 0`. -/
def GiffenAt {L : ℕ} (x : DemandFunction L) (p : Fin L → ℝ) (w : ℝ) (l : Fin L) : Prop :=
  0 < priceEffect (fderiv ℝ (Function.uncurry x) (p, w)) l l

/-- A good is inferior exactly when it is not normal. -/
theorem inferiorAt_iff_not_normalAt {L : ℕ} (x : DemandFunction L) (p : Fin L → ℝ) (w : ℝ)
    (l : Fin L) : InferiorAt x p w l ↔ ¬ NormalAt x p w l := not_le.symm

/-- Reading the effects off a known derivative. -/
theorem priceEffect_fderiv {L : ℕ} {x : DemandFunction L} {p : Fin L → ℝ} {w : ℝ}
    {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)} (hD : HasFDerivAt (Function.uncurry x) D (p, w)) :
    fderiv ℝ (Function.uncurry x) (p, w) = D := hD.fderiv

/-! ### Exercises -/

/-- **Exercise 2.E.1** (MWG, p. 23). The three-good demand function
`x₁ = p₂/(p₁+p₂+p₃) · w/p₁`, `x₂ = p₃/(p₁+p₂+p₃) · w/p₂`,
`x₃ = βp₁/(p₁+p₂+p₃) · w/p₃` (goods indexed `0, 1, 2`). -/
noncomputable def demand_2_E_1 (β : ℝ) : DemandFunction 3 := fun p w =>
  ![p 1 / (p 0 + p 1 + p 2) * (w / p 0), p 2 / (p 0 + p 1 + p 2) * (w / p 1),
    β * p 0 / (p 0 + p 1 + p 2) * (w / p 2)]

/-- **Exercise 2.E.1** (MWG, p. 23). The demand is homogeneous of degree zero for every `β`
(in particular for `β = 1` and for `β ∈ (0, 1)`). -/
theorem exercise_2_E_1_homogeneous (β : ℝ) : HomogeneousZero (demand_2_E_1 β) := by
  intro p w α hd ha
  have h0 := (hd.1 0).ne'
  have h1 := (hd.1 1).ne'
  have h2 := (hd.1 2).ne'
  have hP : p 0 + p 1 + p 2 ≠ 0 := by have := hd.1 0; have := hd.1 1; have := hd.1 2; positivity
  have hα := ha.ne'
  funext l
  fin_cases l <;> simp [demand_2_E_1] <;> field_simp

/-- Expenditure on the Exercise 2.E.1 demand: `p·x = w(p₂ + p₃ + βp₁)/(p₁+p₂+p₃)`. -/
theorem demand_2_E_1_expenditure (β : ℝ) {p : Fin 3 → ℝ} {w : ℝ} (hd : PWDomain p w) :
    p ⬝ᵥ demand_2_E_1 β p w = w * (p 1 + p 2 + β * p 0) / (p 0 + p 1 + p 2) := by
  have h0 := (hd.1 0).ne'
  have h1 := (hd.1 1).ne'
  have h2 := (hd.1 2).ne'
  have hP : p 0 + p 1 + p 2 ≠ 0 := by have := hd.1 0; have := hd.1 1; have := hd.1 2; positivity
  simp [dotProduct, Fin.sum_univ_three, demand_2_E_1]
  field_simp

/-- **Exercise 2.E.1** (MWG, p. 23). The demand satisfies Walras' law if and only if `β = 1`;
so it does for `β = 1` and does not for any `β ∈ (0, 1)`. -/
theorem exercise_2_E_1_walras_iff (β : ℝ) : WalrasLaw (demand_2_E_1 β) ↔ β = 1 := by
  constructor
  · intro h
    have hd : PWDomain (fun _ : Fin 3 => (1 : ℝ)) 1 := ⟨fun _ => one_pos, one_pos⟩
    have := h _ _ hd
    rw [demand_2_E_1_expenditure β hd] at this
    norm_num at this
    linarith
  · rintro rfl p w hd
    rw [demand_2_E_1_expenditure 1 hd]
    have hP : p 0 + p 1 + p 2 ≠ 0 := by
      have := hd.1 0; have := hd.1 1; have := hd.1 2; positivity
    field_simp
    ring

/-- **Exercise 2.E.7** (MWG, p. 37). In a two-good economy, Walras' law and
`x₁(p, w) = αw/p₁` force `x₂(p, w) = (1 - α)w/p₂`, and the demand is homogeneous of degree
zero. -/
theorem exercise_2_E_7 {x : DemandFunction 2} {α : ℝ} (hW : WalrasLaw x)
    (h1 : ∀ p w, PWDomain p w → x p w 0 = α * w / p 0) :
    (∀ p w, PWDomain p w → x p w 1 = (1 - α) * w / p 1) ∧ HomogeneousZero x := by
  have h2 : ∀ p w, PWDomain p w → x p w 1 = (1 - α) * w / p 1 := by
    intro p w hd
    have hw := hW p w hd
    simp only [dotProduct, Fin.sum_univ_two] at hw
    rw [h1 p w hd] at hw
    have hp0 := (hd.1 0).ne'
    have hp1 := (hd.1 1).ne'
    field_simp
    field_simp at hw
    linarith
  refine ⟨h2, fun p w a hd ha => ?_⟩
  have hd' := pwDomain_smul hd ha
  funext l
  fin_cases l
  · simp only [Fin.zero_eta]
    rw [h1 _ _ hd', h1 _ _ hd]
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp [ha.ne', (hd.1 0).ne']
  · simp only [Fin.mk_one]
    rw [h2 _ _ hd', h2 _ _ hd]
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp [ha.ne', (hd.1 1).ne']

end MWG.ConsumerChoice
