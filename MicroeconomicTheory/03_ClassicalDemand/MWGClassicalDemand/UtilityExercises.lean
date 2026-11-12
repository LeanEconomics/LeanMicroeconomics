/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.UMPExercises

/-!
# Exercises on preference and utility

MWG, Exercises 3.C.5 and 3.C.6(a), pp. 96-97.

* Exercise 3.C.5(a): a continuous, monotone `≿` on `ℝ^L_+` (`L ≥ 1`) is homothetic iff it has a
  utility homogeneous of degree one (the diagonal utility of Proposition 3.C.1 is one).
* Exercise 3.C.5(b), the "if" direction: a utility `x₁ + φ(x₂, ..., x_L)` gives quasilinear
  preferences. The "only if" direction is open.
* The cardinality remark: both special forms are destroyed by increasing transformations.
* Exercise 3.C.6(a): at `ρ = 1` the CES utility is linear.
-/

namespace MWG.ClassicalDemand

open MWG.ConsumerChoice Kreps.PreferenceProperties

variable {L : ℕ}

/-- Under monotonicity, indifferent diagonal bundles have equal coordinates. -/
theorem diagonal_eq_of_indifferent {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hm : PrefMonotone (nonnegOrthant L) r) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : Indifferent r (fun _ : Fin L => a) (fun _ => b)) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exact absurd h.1 (hm _ (fun _ => ha) _ (fun _ => hb) fun _ => hab).2
  · exact hab
  · exact absurd h.2 (hm _ (fun _ => hb) _ (fun _ => ha) fun _ => hab).2

/-- **Exercise 3.C.5(a)** (MWG, p. 96), "only if". A continuous, rational, monotone and
homothetic `≿` on `ℝ^L_+` (`L ≥ 1`) has a continuous utility homogeneous of degree one. -/
theorem exercise_3_C_5a_only_if (hL : 0 < L) {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hr : RationalOn (nonnegOrthant L) r) (hc : PrefContinuous (nonnegOrthant L) r)
    (hm : PrefMonotone (nonnegOrthant L) r) (hh : Homothetic (nonnegOrthant L) r) :
    ∃ u : (Fin L → ℝ) → ℝ, Continuous u ∧ RepresentsOn (nonnegOrthant L) u r ∧
      HomogeneousOneOn u := by
  obtain ⟨u, hu, hrep, hdiag⟩ := proposition_3_C_1_monotone hL hr hc hm
  refine ⟨u, hu, hrep, fun x hx α ha => ?_⟩
  have hax : α • x ∈ nonnegOrthant L := fun l => mul_nonneg ha.le (hx l)
  have h1 := hh x hx _ (fun _ => (hdiag x hx).1) ((hdiag x hx).2.symm) α ha.le
  have h2 := (hdiag _ hax).2
  have hmem1 : (α • fun _ : Fin L => u x) ∈ nonnegOrthant L :=
    fun _ => mul_nonneg ha.le (hdiag x hx).1
  have hmem2 : (fun _ : Fin L => u (α • x)) ∈ nonnegOrthant L := fun _ => (hdiag _ hax).1
  have hind : Indifferent r (fun _ : Fin L => u (α • x)) (fun _ => α * u x) := by
    have e : (α • fun _ : Fin L => u x) = fun _ => α * u x := rfl
    rw [← e]
    exact ⟨hr.2 _ hmem2 _ hax _ hmem1 h2.1 h1.1, hr.2 _ hmem1 _ hax _ hmem2 h1.2 h2.2⟩
  exact diagonal_eq_of_indifferent hm (hdiag _ hax).1 (mul_nonneg ha.le (hdiag x hx).1) hind

/-- **Exercise 3.C.5(a)** (MWG, p. 96), "if". A preference represented on `ℝ^L_+` by a utility
homogeneous of degree one is homothetic. -/
theorem exercise_3_C_5a_if {u : (Fin L → ℝ) → ℝ} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hrep : RepresentsOn (nonnegOrthant L) u r) (hu : HomogeneousOneOn u) :
    Homothetic (nonnegOrthant L) r := by
  intro x hx y hy hxy α ha
  have hax : α • x ∈ nonnegOrthant L := fun l => mul_nonneg ha (hx l)
  have hay : α • y ∈ nonnegOrthant L := fun l => mul_nonneg ha (hy l)
  rw [hrep.indifferent_iff hax hay]
  have hxy' := (hrep.indifferent_iff hx hy).mp hxy
  rcases ha.lt_or_eq with ha | ha
  · rw [hu x hx α ha, hu y hy α ha, hxy']
  · subst ha
    simp

/-- **Exercise 3.C.5(b)** (MWG, p. 96), "if". A utility `x_k + φ(x)` with `φ` independent of
the numeraire `x_k` represents a preference that is quasilinear with respect to good `k`. -/
theorem exercise_3_C_5b_if {k : Fin L} {φ : (Fin L → ℝ) → ℝ}
    (hφ : ∀ x : Fin L → ℝ, ∀ t : ℝ, φ (x + t • unitVec k) = φ x) :
    QuasilinearWrt k (utilityPref fun x => x k + φ x) := by
  have hval : ∀ x : Fin L → ℝ, ∀ t : ℝ,
      (x + t • unitVec k) k + φ (x + t • unitVec k) = x k + φ x + t := by
    intro x t
    rw [hφ]
    simp only [unitVec, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
    ring
  refine ⟨fun x _ y _ hxy α => ?_, fun x _ α hα => ?_⟩
  · simp only [Indifferent, utilityPref] at hxy ⊢
    rw [hval x α, hval y α]
    exact ⟨by linarith [hxy.1], by linarith [hxy.2]⟩
  · simp only [Strict, utilityPref]
    rw [hval x α]
    exact ⟨by linarith, by linarith⟩

/-- **Exercise 3.C.5, cardinality** (MWG, p. 96). Homogeneity of degree one is cardinal: on
`ℝ¹_+`, `u(x) = x` is homogeneous of degree one but its increasing transformation `u³`, which
represents the same preferences, is not. -/
theorem exercise_3_C_5_cardinal_homogeneous :
    HomogeneousOneOn (fun x : Fin 1 → ℝ => x 0) ∧
      ¬ HomogeneousOneOn (fun x : Fin 1 → ℝ => x 0 ^ 3) := by
  refine ⟨fun x _ α _ => rfl, fun h => ?_⟩
  have := h (fun _ => 1) (fun _ => zero_le_one) 2 two_pos
  norm_num at this

/-- **Exercise 3.C.5, cardinality** (MWG, p. 96). The quasilinear form is cardinal: `x₁ + x₂`
has it, but its increasing transformation `(x₁ + x₂)³` is not of the form `x₁ + φ(x₂)`. -/
theorem exercise_3_C_5_cardinal_quasilinear :
    ¬ ∃ φ : ℝ → ℝ, ∀ x : Fin 2 → ℝ, (x 0 + x 1) ^ 3 = x 0 + φ (x 1) := by
  rintro ⟨φ, hφ⟩
  have h1 := hφ ![0, 1]
  have h2 := hφ ![1, 1]
  simp at h1 h2
  linarith

/-- **Exercise 3.C.6(a)** (MWG, p. 97). At `ρ = 1` the CES utility `(α₁x₁^ρ + α₂x₂^ρ)^{1/ρ}` is the
linear utility `α₁x₁ + α₂x₂`, so its indifference curves are lines. -/
theorem exercise_3_C_6a (a₁ a₂ : ℝ) (x : Fin 2 → ℝ) :
    (a₁ * x 0 ^ (1 : ℝ) + a₂ * x 1 ^ (1 : ℝ)) ^ (1 / (1 : ℝ)) = a₁ * x 0 + a₂ * x 1 := by
  simp

end MWG.ClassicalDemand
