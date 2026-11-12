/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.ExpBasic
import MWGClassicalDemand.UMPExercises
import MWGClassicalDemand.UtilityExercises

/-!
# Exercises 3.E.5, 3.E.7, 3.E.9 and 3.E.10

MWG, Section 3.E, pp. 98-99.

* Exercise 3.E.5: for a utility homogeneous of degree one, `h(p, ū) = ū h(p, 1)` and
  `e(p, ū) = ū e(p, 1)` for `ū > 0 = u(0)`.
* Exercise 3.E.7: for the quasilinear utility `x_k + φ(x)` on `(-∞, ∞) × ℝ^{L-1}_+`, raising
  `ū` by `t` shifts the Hicksian demand by `t e_k`: the demands for the other goods do not depend
  on `ū`, and `e(p, ū + t) = e(p, ū) + p_k t`, i.e. `e(p, ū) = p_k ū + ψ(p)`.
* Exercise 3.E.9: using only the relations (3.E.1), the properties of Proposition 3.D.3 give
  those of Proposition 3.E.2 and conversely (homogeneity, monotonicity, concavity versus
  quasiconvexity), for abstract `e`, `v`; `equation_3_E_1_instance` shows the actual functions
  satisfy the hypotheses. Continuity is transferred in `ExpContinuity`.
* Exercise 3.E.10: using only (3.E.1)-(3.E.4), Proposition 3.D.2 gives Proposition 3.E.3 and
  conversely, for abstract correspondences (the printed "Proposition 3.E.4" in the first sentence
  is read as 3.E.3, as the text on p. 62 describes the exercise; Proposition 3.E.4 itself is
  `proposition_3_E_4`).
-/

namespace MWG.ClassicalDemand

open MWG.ConsumerChoice Kreps.PreferenceProperties

variable {L : ℕ}

open scoped Pointwise in
/-- **Exercise 3.E.5** (MWG, p. 98). If `u` is homogeneous of degree one on `ℝ^L_+`, then for
`ū > 0` the Hicksian demand is `h(p, ū) = ū h(p, 1)`. -/
theorem exercise_3_E_5_hicksian {u : (Fin L → ℝ) → ℝ} (hu : HomogeneousOneOn u)
    (p : Fin L → ℝ) {ub : ℝ} (hub : 0 < ub) :
    hicksianDemand u p ub = ub • hicksianDemand u p 1 := by
  have hK : ∀ x, x ∈ empConstraintSet u ub ↔ ub⁻¹ • x ∈ empConstraintSet u 1 := by
    intro x
    constructor
    · rintro ⟨hx, hux⟩
      refine ⟨fun l => mul_nonneg (inv_nonneg.mpr hub.le) (hx l), ?_⟩
      rw [hu x hx _ (inv_pos.mpr hub)]
      rw [le_inv_mul_iff₀ hub, mul_one]
      exact hux
    · rintro ⟨hx, hux⟩
      have hx' : x ∈ nonnegOrthant L := by
        intro l
        have := hx l
        simp only [Pi.smul_apply, smul_eq_mul] at this
        exact (mul_nonneg_iff_of_pos_left (inv_pos.mpr hub)).mp this
      refine ⟨hx', ?_⟩
      rw [hu x hx' _ (inv_pos.mpr hub), le_inv_mul_iff₀ hub, mul_one] at hux
      exact hux
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hub.ne']
  constructor
  · rintro ⟨hx, hmin⟩
    refine ⟨(hK x).mp hx, fun y hy => ?_⟩
    have h1 : ub • y ∈ empConstraintSet u ub := (hK _).mpr (by rwa [inv_smul_smul₀ hub.ne'])
    have := hmin _ h1
    rw [dotProduct_smul, smul_eq_mul] at this
    rw [dotProduct_smul, smul_eq_mul]
    calc ub⁻¹ * (p ⬝ᵥ x) ≤ ub⁻¹ * (ub * (p ⬝ᵥ y)) :=
          mul_le_mul_of_nonneg_left this (inv_nonneg.mpr hub.le)
      _ = p ⬝ᵥ y := by field_simp
  · rintro ⟨hx, hmin⟩
    refine ⟨(hK x).mpr hx, fun y hy => ?_⟩
    have := hmin (ub⁻¹ • y) ((hK y).mp hy)
    rw [dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul] at this
    exact le_of_mul_le_mul_left this (inv_pos.mpr hub)

open scoped Pointwise in
/-- **Exercise 3.E.5** (MWG, p. 98). If `u` is homogeneous of degree one on `ℝ^L_+`, then for
`ū > 0` the expenditure function is `e(p, ū) = ū e(p, 1)`. -/
theorem exercise_3_E_5_expenditure {u : (Fin L → ℝ) → ℝ} (hu : HomogeneousOneOn u)
    (p : Fin L → ℝ) {ub : ℝ} (hub : 0 < ub) :
    expenditure u p ub = ub * expenditure u p 1 := by
  have hK : empConstraintSet u ub = ub • empConstraintSet u 1 := by
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ hub.ne']
    constructor
    · rintro ⟨hx, hux⟩
      refine ⟨fun l => mul_nonneg (inv_nonneg.mpr hub.le) (hx l), ?_⟩
      rw [hu x hx _ (inv_pos.mpr hub), le_inv_mul_iff₀ hub, mul_one]
      exact hux
    · rintro ⟨hx, hux⟩
      have hx' : x ∈ nonnegOrthant L := by
        intro l
        have := hx l
        simp only [Pi.smul_apply, smul_eq_mul] at this
        exact (mul_nonneg_iff_of_pos_left (inv_pos.mpr hub)).mp this
      refine ⟨hx', ?_⟩
      rw [hu x hx' _ (inv_pos.mpr hub), le_inv_mul_iff₀ hub, mul_one] at hux
      exact hux
  unfold expenditure supportFn
  have himg : (fun x => p ⬝ᵥ x) '' (ub • empConstraintSet u 1) =
      ub • ((fun x => p ⬝ᵥ x) '' empConstraintSet u 1) := by
    rw [← Set.image_smul, ← Set.image_smul, Set.image_image, Set.image_image]
    simp only [dotProduct_smul, smul_eq_mul]
  rw [hK, himg, Real.sInf_smul_of_nonneg hub.le, smul_eq_mul]

/-- A homogeneous-of-degree-one utility has `u(0) = 0`. -/
theorem exp_homogeneousOneOn_zero {u : (Fin L → ℝ) → ℝ} (hu : HomogeneousOneOn u) : u 0 = 0 := by
  have := hu 0 (fun _ => le_rfl) 2 two_pos
  rw [smul_zero] at this
  linarith

/-- The EMP on a consumption set `X`: the minimizers of `p·x` on `{x ∈ X : u(x) ≥ ū}`. -/
def hicksianDemandOn (X : Set (Fin L → ℝ)) (u : (Fin L → ℝ) → ℝ) (p : Fin L → ℝ) (ub : ℝ) :
    Set (Fin L → ℝ) :=
  supportArgmin {x | x ∈ X ∧ ub ≤ u x} p

/-- **Exercise 3.E.7** (MWG, p. 98). For the quasilinear utility `u(x) = x_k + φ(x)` (`φ` not
depending on `x_k`) on `(-∞, ∞) × ℝ^{L-1}_+`, if `x ∈ h(p, ū)` then `x + t e_k ∈ h(p, ū + t)`:
the Hicksian demands for the goods `l ≠ k` do not depend on `ū`. -/
theorem exercise_3_E_7 {k : Fin L} {φ : (Fin L → ℝ) → ℝ}
    (hφ : ∀ x : Fin L → ℝ, ∀ t : ℝ, φ (x + t • unitVec k) = φ x) {p : Fin L → ℝ} {ub : ℝ}
    {x : Fin L → ℝ} (hx : x ∈ hicksianDemandOn (quasilinearDomain k) (fun y => y k + φ y) p ub)
    (t : ℝ) :
    x + t • unitVec k ∈
        hicksianDemandOn (quasilinearDomain k) (fun y => y k + φ y) p (ub + t) ∧
      ∀ l, l ≠ k → (x + t • unitVec k) l = x l := by
  have hval : ∀ y : Fin L → ℝ, ∀ s : ℝ,
      (y + s • unitVec k) k + φ (y + s • unitVec k) = y k + φ y + s := by
    intro y s
    rw [hφ]
    simp [unitVec]
    ring
  have hdom : ∀ y : Fin L → ℝ, ∀ s : ℝ, y ∈ quasilinearDomain k →
      y + s • unitVec k ∈ quasilinearDomain k := by
    intro y s hy l hl
    simp [unitVec, hl, hy l hl]
  have hcost : ∀ y : Fin L → ℝ, ∀ s : ℝ, p ⬝ᵥ (y + s • unitVec k) = p ⬝ᵥ y + s * p k := by
    intro y s
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul, unitVec, dotProduct_single, mul_one]
  refine ⟨⟨⟨hdom x t hx.1.1, ?_⟩, fun y hy => ?_⟩, fun l hl => ?_⟩
  · change ub + t ≤ (x + t • unitVec k) k + φ (x + t • unitVec k)
    rw [hval]
    have h1 : ub ≤ x k + φ x := hx.1.2
    linarith
  · have h2 : ub + t ≤ y k + φ y := hy.2
    have hy' : y + (-t) • unitVec k ∈ {z | z ∈ quasilinearDomain k ∧ ub ≤ z k + φ z} := by
      refine ⟨hdom y _ hy.1, ?_⟩
      rw [hval]
      linarith
    have := hx.2 _ hy'
    rw [hcost] at this
    rw [hcost]
    linarith
  · simp [unitVec, hl]

/-- **Exercise 3.E.7** (MWG, p. 98), the form of the expenditure function: if the EMP has a
solution at `(p, ū)`, then `e(p, ū + t) = e(p, ū) + p_k t` for every `t`, i.e.
`e(p, ū) = p_k ū + ψ(p)` with `ψ(p) = e(p, 0)`. -/
theorem exercise_3_E_7_expenditure {k : Fin L} {φ : (Fin L → ℝ) → ℝ}
    (hφ : ∀ x : Fin L → ℝ, ∀ t : ℝ, φ (x + t • unitVec k) = φ x) {p : Fin L → ℝ} {ub : ℝ}
    {x : Fin L → ℝ} (hx : x ∈ hicksianDemandOn (quasilinearDomain k) (fun y => y k + φ y) p ub)
    (t : ℝ) :
    supportFn {y | y ∈ quasilinearDomain k ∧ ub + t ≤ y k + φ y} p =
      supportFn {y | y ∈ quasilinearDomain k ∧ ub ≤ y k + φ y} p + p k * t := by
  have h1 := (exercise_3_E_7 hφ hx t).1
  rw [supportFn_eq_of_mem_argmin h1, supportFn_eq_of_mem_argmin hx, dotProduct_add,
    dotProduct_smul, smul_eq_mul, unitVec, dotProduct_single, mul_one]
  ring

/-- **Exercise 3.E.9** (MWG, p. 99), from Proposition 3.D.3 to Proposition 3.E.2, using only
(3.E.1). Abstract functions `E(p, ū)`, `V(p, w)` on `p ≫ 0`, `w > 0`, `ū ∈ U` with
`E(p, V(p, w)) = w`, `V(p, E(p, ū)) = ū`, `V(p, w) ∈ U` and `E(p, ū) > 0`. If `V` is
homogeneous of degree zero, strictly increasing in `w`, nonincreasing in `p` and quasiconvex,
then `E` is homogeneous of degree one in `p`, strictly increasing in `ū`, nondecreasing in
`p` and concave in `p`. -/
theorem exercise_3_E_9_forward {E V : (Fin L → ℝ) → ℝ → ℝ} {U : Set ℝ}
    (hEV : ∀ p w, StrictlyPositive p → 0 < w → E p (V p w) = w)
    (hVE : ∀ p ub, StrictlyPositive p → ub ∈ U → V p (E p ub) = ub)
    (hEpos : ∀ p ub, StrictlyPositive p → ub ∈ U → 0 < E p ub)
    (hV0 : ∀ p w (α : ℝ), StrictlyPositive p → 0 < w → 0 < α → V (α • p) (α * w) = V p w)
    (hVw : ∀ p w w', StrictlyPositive p → 0 < w → w < w' → V p w < V p w')
    (hVp : ∀ p p' w, StrictlyPositive p → p ≤ p' → 0 < w → V p' w ≤ V p w)
    (hVq : ∀ ub, Convex ℝ {z : (Fin L → ℝ) × ℝ | StrictlyPositive z.1 ∧ 0 < z.2 ∧ V z.1 z.2 ≤ ub}) :
    (∀ p ub (α : ℝ), StrictlyPositive p → ub ∈ U → 0 < α → E (α • p) ub = α * E p ub) ∧
      (∀ p ub ub', StrictlyPositive p → ub ∈ U → ub' ∈ U → ub < ub' → E p ub < E p ub') ∧
      (∀ p p' ub, StrictlyPositive p → p ≤ p' → ub ∈ U → E p ub ≤ E p' ub) ∧
      (∀ ub ∈ U, ConcaveOn ℝ {p : Fin L → ℝ | StrictlyPositive p} (fun p => E p ub)) := by
  have hpos : ∀ (p : Fin L → ℝ) (α : ℝ), StrictlyPositive p → 0 < α →
      StrictlyPositive (α • p) :=
    fun p α hp hα l => mul_pos hα (hp l)
  -- strict monotonicity in `w` makes `V p` injective and order-reflecting
  have hVle : ∀ p w w', StrictlyPositive p → 0 < w → 0 < w' → V p w ≤ V p w' → w ≤ w' := by
    intro p w w' hp hw hw' h
    by_contra hlt
    exact absurd h (not_le.mpr (hVw p w' w hp hw' (not_le.mp hlt)))
  refine ⟨fun p ub α hp hU hα => ?_, fun p ub ub' hp hU hU' hlt => ?_,
    fun p p' ub hp hpp hU => ?_, fun ub hU => ?_⟩
  · have hw := hEpos p ub hp hU
    have := hV0 p (E p ub) α hp hw hα
    rw [hVE p ub hp hU] at this
    calc E (α • p) ub = E (α • p) (V (α • p) (α * E p ub)) := by rw [this]
      _ = α * E p ub := hEV _ _ (hpos p α hp hα) (mul_pos hα hw)
  · by_contra hge
    rw [not_lt] at hge
    have h1 := hVle p (E p ub') (E p ub) hp (hEpos p ub' hp hU') (hEpos p ub hp hU)
    rcases hge.lt_or_eq with h | h
    · have := hVw p (E p ub') (E p ub) hp (hEpos p ub' hp hU') h
      rw [hVE p ub hp hU, hVE p ub' hp hU'] at this
      linarith
    · have := congrArg (V p) h
      rw [hVE p ub hp hU, hVE p ub' hp hU'] at this
      linarith
  · have hp' : StrictlyPositive p' := fun l => (hp l).trans_le (hpp l)
    have h1 := hVp p p' (E p' ub) hp hpp (hEpos p' ub hp' hU)
    rw [hVE p' ub hp' hU] at h1
    exact hVle p _ _ hp (hEpos p ub hp hU) (hEpos p' ub hp' hU) ((hVE p ub hp hU).trans_le h1)
  · refine ⟨fun p hp p' hp' a b ha hb hab => ?_, fun p hp p' hp' a b ha hb hab => ?_⟩
    · exact (fun l => by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        rcases ha.lt_or_eq with ha' | ha'
        · exact add_pos_of_pos_of_nonneg (mul_pos ha' (hp l)) (mul_nonneg hb (hp' l).le)
        · subst ha'
          simp only [zero_add] at hab
          subst hab
          simpa using hp' l)
    · have hm1 : (p, E p ub) ∈ {z : (Fin L → ℝ) × ℝ | StrictlyPositive z.1 ∧ 0 < z.2 ∧
          V z.1 z.2 ≤ ub} := ⟨hp, hEpos p ub hp hU, (hVE p ub hp hU).le⟩
      have hm2 : (p', E p' ub) ∈ {z : (Fin L → ℝ) × ℝ | StrictlyPositive z.1 ∧ 0 < z.2 ∧
          V z.1 z.2 ≤ ub} := ⟨hp', hEpos p' ub hp' hU, (hVE p' ub hp' hU).le⟩
      obtain ⟨hpp, hww, hv⟩ := hVq ub hm1 hm2 ha hb hab
      simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at hpp hww hv
      have := hVle _ _ _ hpp hww (hEpos _ ub hpp hU) (hv.trans (hVE _ ub hpp hU).ge)
      simpa [smul_eq_mul] using this

/-- **Exercise 3.E.9** (MWG, p. 99), from Proposition 3.E.2 to Proposition 3.D.3, using only
(3.E.1). If `E` is homogeneous of degree one and nondecreasing in `p`, strictly increasing in
`ū`, and concave in `p`, then `V` is homogeneous of degree zero, strictly increasing in `w`,
nonincreasing in `p`, and quasiconvex. -/
theorem exercise_3_E_9_backward {E V : (Fin L → ℝ) → ℝ → ℝ} {U : Set ℝ}
    (hEV : ∀ p w, StrictlyPositive p → 0 < w → E p (V p w) = w)
    (hVE : ∀ p ub, StrictlyPositive p → ub ∈ U → V p (E p ub) = ub)
    (hVU : ∀ p w, StrictlyPositive p → 0 < w → V p w ∈ U)
    (hE1 : ∀ p ub (α : ℝ), StrictlyPositive p → ub ∈ U → 0 < α → E (α • p) ub = α * E p ub)
    (hEu : ∀ p ub ub', StrictlyPositive p → ub ∈ U → ub' ∈ U → ub < ub' → E p ub < E p ub')
    (hEp : ∀ p p' ub, StrictlyPositive p → p ≤ p' → ub ∈ U → E p ub ≤ E p' ub)
    (hEc : ∀ ub ∈ U, ConcaveOn ℝ {p : Fin L → ℝ | StrictlyPositive p} (fun p => E p ub)) :
    (∀ p w (α : ℝ), StrictlyPositive p → 0 < w → 0 < α → V (α • p) (α * w) = V p w) ∧
      (∀ p w w', StrictlyPositive p → 0 < w → w < w' → V p w < V p w') ∧
      (∀ p p' w, StrictlyPositive p → p ≤ p' → 0 < w → V p' w ≤ V p w) ∧
      (∀ ub ∈ U, Convex ℝ {z : (Fin L → ℝ) × ℝ | StrictlyPositive z.1 ∧ 0 < z.2 ∧
        V z.1 z.2 ≤ ub}) := by
  have hpos : ∀ (p : Fin L → ℝ) (α : ℝ), StrictlyPositive p → 0 < α →
      StrictlyPositive (α • p) :=
    fun p α hp hα l => mul_pos hα (hp l)
  have hEle : ∀ p ub ub', StrictlyPositive p → ub ∈ U → ub' ∈ U → E p ub ≤ E p ub' →
      ub ≤ ub' := by
    intro p ub ub' hp hU hU' h
    by_contra hlt
    exact absurd h (not_le.mpr (hEu p ub' ub hp hU' hU (not_le.mp hlt)))
  -- `V(p, w) ≤ ū ⟺ w ≤ E(p, ū)`
  have hsub : ∀ p w ub, StrictlyPositive p → 0 < w → ub ∈ U → (V p w ≤ ub ↔ w ≤ E p ub) := by
    intro p w ub hp hw hU
    constructor
    · intro h
      rcases h.lt_or_eq with h' | h'
      · have := hEu p _ _ hp (hVU p w hp hw) hU h'
        rw [hEV p w hp hw] at this
        exact this.le
      · rw [← h', hEV p w hp hw]
    · intro h
      have := hEle p (V p w) ub hp (hVU p w hp hw) hU (by rwa [hEV p w hp hw])
      exact this
  refine ⟨fun p w α hp hw hα => ?_, fun p w w' hp hw hww => ?_,
    fun p p' w hp hpp hw => ?_, fun ub hU => ?_⟩
  · have h1 := hE1 p (V p w) α hp (hVU p w hp hw) hα
    rw [hEV p w hp hw] at h1
    have := congrArg (V (α • p)) h1
    rw [hVE _ _ (hpos p α hp hα) (hVU p w hp hw)] at this
    exact this.symm
  · have hw' : 0 < w' := hw.trans hww
    by_contra hge
    rw [not_lt] at hge
    have := (hsub p w' (V p w) hp hw' (hVU p w hp hw)).mp hge
    rw [hEV p w hp hw] at this
    linarith
  · have hp' : StrictlyPositive p' := fun l => (hp l).trans_le (hpp l)
    rw [hsub p' w _ hp' hw (hVU p w hp hw)]
    have := hEp p p' (V p w) hp hpp (hVU p w hp hw)
    rw [hEV p w hp hw] at this
    exact this
  · intro z hz z' hz' a b ha hb hab
    obtain ⟨hzp, hzw, hzv⟩ := hz
    obtain ⟨hzp', hzw', hzv'⟩ := hz'
    have hc := (hEc ub hU).2 hzp hzp' ha hb hab
    have hpz : StrictlyPositive (a • z.1 + b • z'.1) := (hEc ub hU).1 hzp hzp' ha hb hab
    have hwz : 0 < a * z.2 + b * z'.2 := by
      rcases ha.lt_or_eq with ha' | ha'
      · exact add_pos_of_pos_of_nonneg (mul_pos ha' hzw) (mul_nonneg hb hzw'.le)
      · subst ha'
        simp only [zero_add] at hab
        subst hab
        simpa using hzw'
    refine ⟨hpz, hwz, ?_⟩
    simp only [Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    rw [hsub _ _ ub hpz hwz hU]
    have h1 := (hsub z.1 z.2 ub hzp hzw hU).mp hzv
    have h2 := (hsub z'.1 z'.2 ub hzp' hzw' hU).mp hzv'
    simp only [smul_eq_mul] at hc
    nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]

/-- **Exercise 3.E.9** (MWG, p. 99): the actual expenditure and indirect utility functions
satisfy the relations used above, with `U = {ū : u(0) < ū, ū attainable}`. -/
theorem equation_3_E_1_instance {u : (Fin L → ℝ) → ℝ} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hrep : RepresentsOn (nonnegOrthant L) u r) (hu : ContinuousOn u (nonnegOrthant L))
    (hlns : LocallyNonsatiated (nonnegOrthant L) r) :
    let U := {ub : ℝ | u 0 < ub ∧ ∃ x ∈ nonnegOrthant L, ub ≤ u x}
    (∀ p w, StrictlyPositive p → 0 < w →
        expenditure u p (indirectUtility u p w) = w) ∧
      (∀ p ub, StrictlyPositive p → ub ∈ U → indirectUtility u p (expenditure u p ub) = ub) ∧
      (∀ p w, StrictlyPositive p → 0 < w → indirectUtility u p w ∈ U) ∧
      (∀ p ub, StrictlyPositive p → ub ∈ U → 0 < expenditure u p ub) := by
  intro U
  refine ⟨fun p w hp hw => equation_3_E_1_left hrep hu hlns hp hw.le,
    fun p ub hp hU => equation_3_E_1_right hu hp hU.1 hU.2, fun p w hp hw => ?_,
    fun p ub hp hU => ?_⟩
  · obtain ⟨x, hx⟩ := proposition_3_D_1 hu hp hw.le
    refine ⟨?_, x, hx.1.1, (indirectUtility_eq_of_mem hx).le⟩
    exact (exp_indirectUtility_ge_zero hu hp le_rfl).trans_lt
      (proposition_3_D_3_ii_wealth hrep hu hlns hp le_rfl hw)
  · obtain ⟨y, hy⟩ := exercise_3_E_3 hu hp hU.2
    have hy0 : y ≠ 0 := by
      rintro rfl
      linarith [hy.1.2, hU.1]
    rw [expenditure_eq_of_mem hy]
    exact exp_dotProduct_pos hp hy.1.1 hy0

/-- **Exercise 3.E.10** (MWG, p. 99), from Proposition 3.D.2 to Proposition 3.E.3, using only
the relations (3.E.1) and (3.E.4). For abstract correspondences `X(p, w)`, `H(p, ū)` with
`H(p, ū) = X(p, E(p, ū))`, utility `u` with `u(x) = V(p, w)` on `X(p, w)`,
`V(p, E(p, ū)) = ū` and `E` homogeneous of degree one in `p`: if `X` is homogeneous of degree
zero and convex-valued, then `H` is homogeneous of degree zero in `p`, has no excess utility,
and is convex-valued. -/
theorem exercise_3_E_10_forward {X H : (Fin L → ℝ) → ℝ → Set (Fin L → ℝ)}
    {E V : (Fin L → ℝ) → ℝ → ℝ} {u : (Fin L → ℝ) → ℝ} {U : Set ℝ}
    (hHX : ∀ p ub, StrictlyPositive p → ub ∈ U → H p ub = X p (E p ub))
    (hXV : ∀ p w x, StrictlyPositive p → x ∈ X p w → u x = V p w)
    (hVE : ∀ p ub, StrictlyPositive p → ub ∈ U → V p (E p ub) = ub)
    (hE1 : ∀ p ub (α : ℝ), StrictlyPositive p → ub ∈ U → 0 < α → E (α • p) ub = α * E p ub)
    (hX0 : ∀ p w (α : ℝ), 0 < α → X (α • p) (α * w) = X p w)
    (hXc : ∀ p w, Convex ℝ (X p w)) :
    (∀ p ub (α : ℝ), StrictlyPositive p → ub ∈ U → 0 < α → H (α • p) ub = H p ub) ∧
      (∀ p ub x, StrictlyPositive p → ub ∈ U → x ∈ H p ub → u x = ub) ∧
      (∀ p ub, StrictlyPositive p → ub ∈ U → Convex ℝ (H p ub)) := by
  refine ⟨fun p ub α hp hU hα => ?_, fun p ub x hp hU hx => ?_, fun p ub hp hU => ?_⟩
  · have hαp : StrictlyPositive (α • p) := fun l => mul_pos hα (hp l)
    rw [hHX _ _ hαp hU, hHX _ _ hp hU, hE1 p ub α hp hU hα, hX0 p _ α hα]
  · rw [hHX _ _ hp hU] at hx
    rw [hXV p _ x hp hx, hVE p ub hp hU]
  · rw [hHX _ _ hp hU]
    exact hXc _ _

/-- **Exercise 3.E.10** (MWG, p. 99), from Proposition 3.E.3 to Proposition 3.D.2, using only
(3.E.1) and (3.E.4): with `X(p, w) = H(p, V(p, w))`, `E(p, V(p, w)) = w`, `p·x = E(p, ū)` on
`H(p, ū)` and `V` homogeneous of degree zero, if `H` is homogeneous of degree zero in `p` and
convex-valued, then `X` is homogeneous of degree zero, satisfies Walras' law and is
convex-valued. -/
theorem exercise_3_E_10_backward {X H : (Fin L → ℝ) → ℝ → Set (Fin L → ℝ)}
    {E V : (Fin L → ℝ) → ℝ → ℝ}
    (hXH : ∀ p w, StrictlyPositive p → 0 < w → X p w = H p (V p w))
    (hEV : ∀ p w, StrictlyPositive p → 0 < w → E p (V p w) = w)
    (hHE : ∀ p ub x, x ∈ H p ub → p ⬝ᵥ x = E p ub)
    (hV0 : ∀ p w (α : ℝ), StrictlyPositive p → 0 < w → 0 < α → V (α • p) (α * w) = V p w)
    (hH0 : ∀ p ub (α : ℝ), 0 < α → H (α • p) ub = H p ub)
    (hHc : ∀ p ub, Convex ℝ (H p ub)) :
    (∀ p w (α : ℝ), StrictlyPositive p → 0 < w → 0 < α → X (α • p) (α * w) = X p w) ∧
      (∀ p w x, StrictlyPositive p → 0 < w → x ∈ X p w → p ⬝ᵥ x = w) ∧
      (∀ p w, StrictlyPositive p → 0 < w → Convex ℝ (X p w)) := by
  refine ⟨fun p w α hp hw hα => ?_, fun p w x hp hw hx => ?_, fun p w hp hw => ?_⟩
  · have hαp : StrictlyPositive (α • p) := fun l => mul_pos hα (hp l)
    rw [hXH _ _ hαp (mul_pos hα hw), hXH _ _ hp hw, hV0 p w α hp hw hα, hH0 _ _ α hα]
  · rw [hXH _ _ hp hw] at hx
    rw [hHE _ _ x hx, hEV p w hp hw]
  · rw [hXH _ _ hp hw]
    exact hHc _ _

end MWG.ClassicalDemand
