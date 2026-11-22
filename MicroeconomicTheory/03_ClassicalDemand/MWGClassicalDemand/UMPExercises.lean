/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.UMPExamples

/-!
# Exercises on the utility maximization problem

MWG, Exercises 3.D.3, 3.D.4(a)-(b) and 3.D.8, pp. 97-98.

* Exercise 3.D.3(a): a utility homogeneous of degree one gives demand and indirect utility
  homogeneous of degree one in wealth, `x(p, w) = w x̃(p)`, `v(p, w) = w ṽ(p)`, a straight-line
  wealth expansion path and unit wealth elasticities. No differentiability or strict
  quasiconcavity is needed for the set-valued statements.
* Exercise 3.D.3(b): if `v(p, ·)` is homogeneous of degree one, then `u(αx) = αu(x)` whenever `x`
  and `αx` are both demanded at some price-wealth pairs (the remaining step, that under the
  book's smoothness assumptions every bundle is demanded, is not formalized).
* Exercise 3.D.4(a)-(b): with a quasilinear utility `x₁ + φ(x₂, ..., x_L)` on
  `(-∞, ∞) × ℝ^{L-1}_+` and `p₁ = 1`, wealth changes only translate demand along the numeraire
  axis (demand for goods `2, ..., L` is independent of wealth, the wealth effect on good 1 is
  one), and `v(p, w) = w + v(p, 0)`.
* Exercise 3.D.8: `w ∂v/∂w = -p·∇_p v(p, w)` wherever `v` is differentiable.
-/

namespace MWG.ClassicalDemand

open MWG.ConsumerChoice Kreps.PreferenceProperties Filter Topology

variable {L : ℕ}

/-- `u` is homogeneous of degree one on `ℝ^L_+`: `u(αx) = αu(x)` for `α > 0`. -/
def HomogeneousOneOn (u : (Fin L → ℝ) → ℝ) : Prop :=
  ∀ x ∈ nonnegOrthant L, ∀ α : ℝ, 0 < α → u (α • x) = α * u x

/-- Scaling a bundle by `α > 0` scales budget membership with wealth. -/
theorem smul_mem_budgetSet_iff {p : Fin L → ℝ} {w α : ℝ} (ha : 0 < α) (x : Fin L → ℝ) :
    α • x ∈ budgetSet p (α * w) ↔ x ∈ budgetSet p w := by
  constructor
  · rintro ⟨hx, hb⟩
    refine ⟨fun l => ?_, ?_⟩
    · have := hx l
      simp only [Pi.smul_apply, smul_eq_mul] at this
      exact nonneg_of_mul_nonneg_right (by linarith) ha
    · rw [dotProduct_smul, smul_eq_mul] at hb
      exact le_of_mul_le_mul_left hb ha
  · rintro ⟨hx, hb⟩
    refine ⟨fun l => mul_nonneg ha.le (hx l), ?_⟩
    rw [dotProduct_smul, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left hb ha.le

open scoped Pointwise in
/-- **Exercise 3.D.3(a)** (MWG, p. 97). If `u` is homogeneous of degree one, Walrasian demand is
homogeneous of degree one in wealth: `x(p, αw) = α x(p, w)` for `α > 0`. -/
theorem exercise_3_D_3a_demand {u : (Fin L → ℝ) → ℝ} (hu : HomogeneousOneOn u)
    (p : Fin L → ℝ) (w : ℝ) {α : ℝ} (ha : 0 < α) :
    walrasianDemand u p (α * w) = α • walrasianDemand u p w := by
  ext y
  constructor
  · rintro ⟨hy, hmax⟩
    refine ⟨α⁻¹ • y, ⟨?_, fun z hz => ?_⟩, ?_⟩
    · change α⁻¹ • y ∈ budgetSet p w
      rw [← smul_mem_budgetSet_iff ha, smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
      exact hy
    · have hz' := (smul_mem_budgetSet_iff ha z).mpr hz
      have h1 := hmax _ hz'
      have hy0 : α⁻¹ • y ∈ nonnegOrthant L := fun l => by
        simpa using mul_nonneg (inv_pos.mpr ha).le (hy.1 l)
      have hyy : y = α • (α⁻¹ • y) := by rw [smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
      rw [hu z hz.1 α ha, hyy, hu _ hy0 α ha] at h1
      exact le_of_mul_le_mul_left h1 ha
    · change α • (α⁻¹ • y) = y
      rw [smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
  · rintro ⟨x, ⟨hx, hmax⟩, rfl⟩
    refine ⟨(smul_mem_budgetSet_iff ha x).mpr hx, fun z hz => ?_⟩
    have hz0 : α⁻¹ • z ∈ budgetSet p w := by
      rw [← smul_mem_budgetSet_iff ha, smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
      exact hz
    have h1 := hmax _ hz0
    have hzz : z = α • (α⁻¹ • z) := by rw [smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
    rw [hzz, hu _ hz0.1 α ha, hu x hx.1 α ha]
    exact mul_le_mul_of_nonneg_left h1 ha.le

/-- **Exercise 3.D.3(a)** (MWG, p. 97). If `u` is homogeneous of degree one and the UMP has a
solution, the indirect utility is homogeneous of degree one in wealth: `v(p, αw) = α v(p, w)`.
-/
theorem exercise_3_D_3a_indirect {u : (Fin L → ℝ) → ℝ} (hu : HomogeneousOneOn u)
    {p : Fin L → ℝ} {w : ℝ} (hne : (walrasianDemand u p w).Nonempty) {α : ℝ} (ha : 0 < α) :
    indirectUtility u p (α * w) = α * indirectUtility u p w := by
  obtain ⟨x, hx⟩ := hne
  have hx' : α • x ∈ walrasianDemand u p (α * w) := by
    rw [exercise_3_D_3a_demand hu p w ha]
    exact ⟨x, hx, rfl⟩
  rw [indirectUtility_eq_of_mem hx', indirectUtility_eq_of_mem hx, hu x hx.1.1 α ha]

open scoped Pointwise in
/-- **Exercise 3.D.3(a)** (MWG, p. 97). Hence `x(p, w) = w x̃(p)` with `x̃(p) = x(p, 1)` and
`v(p, w) = w ṽ(p)` with `ṽ(p) = v(p, 1)`, for `w > 0`. -/
theorem exercise_3_D_3a_forms {u : (Fin L → ℝ) → ℝ} (hu : HomogeneousOneOn u)
    {p : Fin L → ℝ} (hne : (walrasianDemand u p 1).Nonempty) {w : ℝ} (hw : 0 < w) :
    walrasianDemand u p w = w • walrasianDemand u p 1 ∧
      indirectUtility u p w = w * indirectUtility u p 1 := by
  have := exercise_3_D_3a_demand hu p 1 hw
  have h2 := exercise_3_D_3a_indirect hu hne hw
  rw [mul_one] at this h2
  exact ⟨this, h2⟩

/-- **Exercise 3.D.3(a)** (MWG, p. 97). For a demand function selected from a homogeneous of
degree one utility with single-valued demand, the wealth expansion path is a ray through the
origin: `x(p, w) = w x(p, 1)` for all `w > 0`. -/
theorem exercise_3_D_3a_ray {u : (Fin L → ℝ) → ℝ} (hu : HomogeneousOneOn u)
    {x : DemandFunction L} {p : Fin L → ℝ} (hsel : ∀ w, 0 < w → x p w ∈ walrasianDemand u p w)
    (huniq : ∀ w, 0 < w → (walrasianDemand u p w).Subsingleton) {w : ℝ} (hw : 0 < w) :
    x p w = w • x p 1 := by
  have h := exercise_3_D_3a_demand hu p 1 hw
  rw [mul_one] at h
  have hmem : w • x p 1 ∈ walrasianDemand u p w := by
    rw [h]
    exact ⟨x p 1, hsel 1 one_pos, rfl⟩
  exact huniq w hw (hsel w hw) hmem

/-- **Exercise 3.D.3(a)** (MWG, p. 97). On such a ray the wealth elasticity of every good with
`x_l(p, 1) ≠ 0` is one: if `x(p, w) = w x̃` near `w`, then `(∂x_l/∂w)(w/x_l) = 1`. -/
theorem exercise_3_D_3a_elasticity {xt : Fin L → ℝ} {l : Fin L} (hl : xt l ≠ 0) {w : ℝ}
    (hw : w ≠ 0) :
    HasDerivAt (fun w' : ℝ => w' * xt l) (xt l) w ∧ xt l * (w / (w * xt l)) = 1 := by
  refine ⟨by simpa using (hasDerivAt_id w).mul_const (xt l), ?_⟩
  field_simp

/-- **Exercise 3.D.3(b)** (MWG, p. 97). If `v(p, ·)` is homogeneous of degree one in wealth at
the relevant prices, then `u(αx) = αu(x)` whenever `x` is demanded at `(p, w)` and `αx` is
demanded at `(p', w')`. -/
theorem exercise_3_D_3b {u : (Fin L → ℝ) → ℝ} (hcont : ContinuousOn u (nonnegOrthant L))
    (hv : ∀ p w α, StrictlyPositive p → 0 < w → 0 < α →
      indirectUtility u p (α * w) = α * indirectUtility u p w)
    {x : Fin L → ℝ} {p p' : Fin L → ℝ} {w w' α : ℝ} (hp : StrictlyPositive p)
    (hp' : StrictlyPositive p') (hw : 0 < w) (hw' : 0 < w') (ha : 0 < α)
    (hx : x ∈ walrasianDemand u p w) (hax : α • x ∈ walrasianDemand u p' w') :
    u (α • x) = α * u x := by
  apply le_antisymm
  · have hb : α • x ∈ budgetSet p (α * w) := (smul_mem_budgetSet_iff ha x).mpr hx.1
    have := le_indirectUtility hcont hp hb
    rw [hv p w α hp hw ha, indirectUtility_eq_of_mem hx] at this
    exact this
  · have hb : α⁻¹ • (α • x) ∈ budgetSet p' (α⁻¹ * w') :=
      (smul_mem_budgetSet_iff (inv_pos.mpr ha) _).mpr hax.1
    rw [smul_smul, inv_mul_cancel₀ ha.ne', one_smul] at hb
    have := le_indirectUtility hcont hp' hb
    rw [hv p' w' α⁻¹ hp' hw' (inv_pos.mpr ha), indirectUtility_eq_of_mem hax] at this
    calc α * u x ≤ α * (α⁻¹ * u (α • x)) := mul_le_mul_of_nonneg_left this ha.le
      _ = u (α • x) := by rw [← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]

/-- The numeraire unit vector `e₁` (commodity `0`). -/
theorem unitVec_zero_apply {n : ℕ} (l : Fin (n + 1)) :
    unitVec (0 : Fin (n + 1)) l = if l = 0 then 1 else 0 := by
  simp [unitVec, Pi.single_apply]

/-- **Exercise 3.D.4(a)** (MWG, p. 97). Quasilinear utility `u(x) = x₁ + φ(x₂, ..., x_L)` on
`(-∞, ∞) × ℝ^{L-1}_+` (`φ` ignores the numeraire) with `p₁ = 1`: raising wealth by `t`
translates the whole demand correspondence by `t e₁`. -/
theorem exercise_3_D_4a {n : ℕ} {φ : (Fin (n + 1) → ℝ) → ℝ}
    (hφ : ∀ x : Fin (n + 1) → ℝ, ∀ t : ℝ, φ (x + t • unitVec 0) = φ x)
    {p : Fin (n + 1) → ℝ} (hp1 : p 0 = 1) (w t : ℝ) :
    walrasianDemandOn (quasilinearDomain 0) (fun x => x 0 + φ x) p (w + t) =
      (fun x => x + t • unitVec 0) '' walrasianDemandOn (quasilinearDomain 0)
        (fun x => x 0 + φ x) p w := by
  have hdot : ∀ y : Fin (n + 1) → ℝ, ∀ s : ℝ, p ⬝ᵥ (y + s • unitVec 0) = p ⬝ᵥ y + s := by
    intro y s
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
    simp [unitVec, hp1]
  have hdom : ∀ y : Fin (n + 1) → ℝ, ∀ s : ℝ,
      y + s • unitVec 0 ∈ quasilinearDomain (0 : Fin (n + 1)) ↔
        y ∈ quasilinearDomain (0 : Fin (n + 1)) := by
    intro y s
    constructor
    · intro h l hl
      have := h l hl
      simpa [unitVec, Pi.single_apply, hl] using this
    · intro h l hl
      simpa [unitVec, Pi.single_apply, hl] using h l hl
  have hu : ∀ y : Fin (n + 1) → ℝ, ∀ s : ℝ,
      (y + s • unitVec 0 : Fin (n + 1) → ℝ) 0 + φ (y + s • unitVec 0) = y 0 + φ y + s := by
    intro y s
    rw [hφ]
    simp only [unitVec, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
    ring
  ext y
  constructor
  · rintro ⟨⟨hyX, hyb⟩, hmax⟩
    refine ⟨y + (-t) • unitVec 0, ⟨⟨(hdom y _).mpr hyX, ?_⟩, fun z hz => ?_⟩, ?_⟩
    · rw [hdot]
      linarith
    · have := hmax (z + t • unitVec 0) ⟨(hdom z t).mpr hz.1, by rw [hdot]; linarith [hz.2]⟩
      simp only at this ⊢
      rw [hu] at this
      rw [hu]
      linarith
    · simp only
      rw [add_assoc, ← add_smul, neg_add_cancel, zero_smul, add_zero]
  · rintro ⟨x, ⟨⟨hxX, hxb⟩, hmax⟩, rfl⟩
    refine ⟨⟨(hdom x t).mpr hxX, by rw [hdot]; linarith⟩, fun z hz => ?_⟩
    have := hmax (z + (-t) • unitVec 0) ⟨(hdom z _).mpr hz.1, by rw [hdot]; linarith [hz.2]⟩
    simp only at this ⊢
    rw [hu] at this
    rw [hu]
    linarith

/-- **Exercise 3.D.4(a)** (MWG, p. 97). Consequently the demand for goods `2, ..., L` does not
depend on wealth when demand is single-valued, and the wealth effect on good 1 is one:
`x₁(p, w + t) = x₁(p, w) + t`. -/
theorem exercise_3_D_4a_independent {n : ℕ} {φ : (Fin (n + 1) → ℝ) → ℝ}
    (hφ : ∀ x : Fin (n + 1) → ℝ, ∀ t : ℝ, φ (x + t • unitVec 0) = φ x)
    {p : Fin (n + 1) → ℝ} (hp1 : p 0 = 1) {w t : ℝ} {x x' : Fin (n + 1) → ℝ}
    (hx : x ∈ walrasianDemandOn (quasilinearDomain 0) (fun x => x 0 + φ x) p w)
    (hx' : x' ∈ walrasianDemandOn (quasilinearDomain 0) (fun x => x 0 + φ x) p (w + t))
    (huniq : (walrasianDemandOn (quasilinearDomain 0) (fun x => x 0 + φ x) p
      (w + t)).Subsingleton) :
    (∀ l, l ≠ 0 → x' l = x l) ∧ x' 0 = x 0 + t := by
  have hmem : x + t • unitVec 0 ∈
      walrasianDemandOn (quasilinearDomain 0) (fun x => x 0 + φ x) p (w + t) := by
    rw [exercise_3_D_4a hφ hp1 w t]
    exact ⟨x, hx, rfl⟩
  have heq := huniq hx' hmem
  refine ⟨fun l hl => ?_, ?_⟩
  · rw [heq]
    simp [unitVec, hl]
  · rw [heq]
    simp [unitVec]

/-- **Exercise 3.D.4(b)** (MWG, p. 97). With quasilinear utility and `p₁ = 1`, the indirect
utility has the form `v(p, w) = w + v(p, 0)` whenever the UMP has a solution. -/
theorem exercise_3_D_4b {n : ℕ} {φ : (Fin (n + 1) → ℝ) → ℝ}
    (hφ : ∀ x : Fin (n + 1) → ℝ, ∀ t : ℝ, φ (x + t • unitVec 0) = φ x)
    {p : Fin (n + 1) → ℝ} (hp1 : p 0 = 1) {w : ℝ}
    (hne : (walrasianDemandOn (quasilinearDomain 0) (fun x => x 0 + φ x) p w).Nonempty) :
    indirectUtilityOn (quasilinearDomain 0) (fun x => x 0 + φ x) p w =
      w + indirectUtilityOn (quasilinearDomain 0) (fun x => x 0 + φ x) p 0 := by
  obtain ⟨x, hx⟩ := hne
  have h := exercise_3_D_4a hφ hp1 0 w
  rw [zero_add] at h
  rw [h] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  rw [indirectUtilityOn_eq_of_mem (by rw [h]; exact ⟨y, hy, rfl⟩),
    indirectUtilityOn_eq_of_mem hy, hφ]
  simp [unitVec]
  ring

/-- **Exercise 3.D.8** (MWG, p. 98). Wherever the indirect utility function is differentiable,
`w ∂v/∂w = -p·∇_p v(p, w)`, a consequence of homogeneity of degree zero. -/
theorem exercise_3_D_8 (u : (Fin L → ℝ) → ℝ) {p : Fin L → ℝ} {w : ℝ}
    {D : ((Fin L → ℝ) × ℝ) →L[ℝ] ℝ}
    (hv : HasFDerivAt (fun q : (Fin L → ℝ) × ℝ => indirectUtility u q.1 q.2) D (p, w)) :
    w * D (0, 1) = -∑ l, p l * D (Pi.single l 1, 0) := by
  -- along the ray `t ↦ (tp, tw)` the indirect utility is constant
  have hpath : HasDerivAt (fun t : ℝ => ((t • p, t * w) : (Fin L → ℝ) × ℝ)) (p, w) 1 := by
    refine HasDerivAt.prodMk ?_ ?_
    · simpa using (hasDerivAt_id (1 : ℝ)).smul_const p
    · simpa using (hasDerivAt_id (1 : ℝ)).mul_const w
  have hv' : HasFDerivAt (fun q : (Fin L → ℝ) × ℝ => indirectUtility u q.1 q.2) D
      ((1 : ℝ) • p, (1 : ℝ) * w) := by simpa using hv
  have hcomp := hv'.comp_hasDerivAt (1 : ℝ) hpath
  have hconst : HasDerivAt (fun t : ℝ => indirectUtility u (t • p) (t * w)) 0 1 := by
    apply (hasDerivAt_const (1 : ℝ) (indirectUtility u p w)).congr_of_eventuallyEq
    filter_upwards [lt_mem_nhds (show (0 : ℝ) < 1 from one_pos)] with t ht
    exact proposition_3_D_3_i u p w ht
  have hzero : D (p, w) = 0 := hcomp.unique hconst
  have hdec : ((p, w) : (Fin L → ℝ) × ℝ) =
      ∑ l, p l • ((Pi.single l 1, 0) : (Fin L → ℝ) × ℝ) + w • ((0, 1) : (Fin L → ℝ) × ℝ) := by
    ext l
    · simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
    · simp [Prod.snd_sum]
  rw [hdec, map_add, map_sum] at hzero
  simp only [map_smul, smul_eq_mul] at hzero
  linarith

end MWG.ClassicalDemand
