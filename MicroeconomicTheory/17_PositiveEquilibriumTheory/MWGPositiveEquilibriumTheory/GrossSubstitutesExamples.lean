/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.GrossSubstitutes

/-!
# Examples of the weak axiom and gross substitution (MWG Section 17.F, pp. 611-613, 645)

* **Example 17.F.1** (`example_17_F_1`): four goods, consumer 1 trading only goods 1-2 and
  consumer 2 only goods 3-4 (each excess demand homogeneous with Walras' law in its block). If both
  excess demands are nonzero at some `p'`, the aggregate excess demand violates the weak axiom; the
  verification for large `α` is **Exercise 17.F.2** (`exercise_17_F_2`). The instance `ex17F1Z`
  (two Cobb-Douglas consumers, so homothetic) has the weak gross substitute property
  (`ex17F1Z_weakGS`) but not the gross substitute property (`ex17F1Z_not_GS`): the book's
  "compatible with ... gross substitution" holds only in the weak sense.
* **p. 613 and footnote 48**: gross substitution does not imply the weak axiom. Adding to `ex17F1Z`
  a small Cobb-Douglas consumer with `ω ≫ 0` gives a gross substitute excess demand `gsNotWAZ`
  that violates the weak axiom (`gs_not_weakAxiom`); hence a constant returns economy whose
  consumers have gross substitute excess demand can have two equilibria (`footnote_17_48`).
* **Exercise 17.F.3** (`exercise_17_F_3`) and **Exercise 17.F.4** (`exercise_17_F_4`): consumers
  who spend all wealth on one good (`cornerED`); aggregate weak gross substitutes, and a violation
  of the weak axiom with `ω₁ = e₁`, `ω₂ = e₂`.
* **Example 17.F.2**, Cobb-Douglas (`example_17_F_2_cd`): `zₗ` responds to `pₖ` exactly through
  `ωₖ`: positively if `ωₖ > 0`, not at all if `ωₖ = 0`.
* **p. 612**, the differential version: a gross substitute excess demand (`gsCubicZ`) with
  `∂z₂/∂p₁ = 0` at `(1, 1)` (`gs_partial_not_pos`).
* **Footnote 45**: `c - (I - A)α` and `g(α) - α` (`g` increasing) have the weak gross substitute
  property (`footnote_17_45_io`, `footnote_17_45_fixed`).
-/

namespace MWG.PositiveEquilibriumTheory

open MWG.ConsumerChoice Filter Topology

/-! ### Example 17.F.1 and Exercise 17.F.2 -/

/-- **Example 17.F.1** (MWG, p. 611), the choice of `(p̂₁, p̂₂)`: if `p₁a + p₂b = 0` with `p ≫ 0`
and `(a, b) ≠ 0`, there are `r₁, r₂ > 0` with `r₁a + r₂b < 0`. -/
theorem ex17F1_dir {a b p0 p1 : ℝ} (hp0 : 0 < p0) (hp1 : 0 < p1) (hw : p0 * a + p1 * b = 0)
    (hne : a ≠ 0 ∨ b ≠ 0) : ∃ r0 r1 : ℝ, 0 < r0 ∧ 0 < r1 ∧ r0 * a + r1 * b < 0 := by
  rcases lt_trichotomy a 0 with ha | ha | ha
  · have hb : 0 < b := by nlinarith
    refine ⟨1, -a / (2 * b), one_pos, div_pos (by linarith) (by linarith), ?_⟩
    field_simp
    linarith
  · subst ha
    have hb : b = 0 := by
      rcases mul_eq_zero.1 (by linarith : p1 * b = 0) with h | h
      · linarith
      · exact h
    exact absurd hne (by simp [hb])
  · have hb : b < 0 := by nlinarith
    refine ⟨-b / (2 * a), 1, div_pos (by linarith) (by linarith), one_pos, ?_⟩
    field_simp
    linarith

/-- A dot product on `ℝ⁴`. -/
theorem ex17F1_dot4 (p v : Fin 4 → ℝ) :
    p ⬝ᵥ v = p 0 * v 0 + p 1 * v 1 + p 2 * v 2 + p 3 * v 3 := by
  simp [dotProduct, Fin.sum_univ_four]

/-- **Example 17.F.1** (MWG, p. 611), hypotheses: consumer 1's excess demand `z¹` depends only on
`(p₁, p₂)` and is zero in goods 3-4; consumer 2's `z²` depends only on `(p₃, p₄)` and is zero in
goods 1-2; both are homogeneous of degree zero and satisfy Walras' law in their goods. -/
structure TwoBlockED (z1 z2 : (Fin 4 → ℝ) → Fin 4 → ℝ) : Prop where
  /-- `z¹` depends only on `p₁, p₂`. -/
  dep1 : ∀ p q : Fin 4 → ℝ, p 0 = q 0 → p 1 = q 1 → z1 p = z1 q
  /-- `z²` depends only on `p₃, p₄`. -/
  dep2 : ∀ p q : Fin 4 → ℝ, p 2 = q 2 → p 3 = q 3 → z2 p = z2 q
  /-- `z¹₃ = z¹₄ = 0`. -/
  zero1 : ∀ p, z1 p 2 = 0 ∧ z1 p 3 = 0
  /-- `z²₁ = z²₂ = 0`. -/
  zero2 : ∀ p, z2 p 0 = 0 ∧ z2 p 1 = 0
  /-- Homogeneity of degree zero. -/
  hom1 : EDHomogeneous z1
  /-- Homogeneity of degree zero. -/
  hom2 : EDHomogeneous z2
  /-- Walras' law for consumer 1. -/
  walras1 : ∀ p ∈ posOrthant 4, p 0 * z1 p 0 + p 1 * z1 p 1 = 0
  /-- Walras' law for consumer 2. -/
  walras2 : ∀ p ∈ posOrthant 4, p 2 * z2 p 2 + p 3 * z2 p 3 = 0

/-- **Exercise 17.F.2** (MWG, p. 645). The verification of Example 17.F.1: given `p' ≫ 0` and
`p̂ ≫ 0` with `p̂₁z¹₁(p') + p̂₂z¹₂(p') < 0` and `p̂₃z²₃(p') + p̂₄z²₄(p') < 0`, for some (every
sufficiently large) `α > 0` the vectors `q = (p'₁, p'₂, αp̂₃, αp̂₄)`, `q' = (αp̂₁, αp̂₂, p'₃, p'₄)`
satisfy `q·z(q') < 0` and `q'·z(q) < 0`. -/
theorem exercise_17_F_2 {z1 z2 : (Fin 4 → ℝ) → Fin 4 → ℝ} (h : TwoBlockED z1 z2)
    {p' r : Fin 4 → ℝ} (hr : r ∈ posOrthant 4)
    (hc1 : r 0 * z1 p' 0 + r 1 * z1 p' 1 < 0) (hc2 : r 2 * z2 p' 2 + r 3 * z2 p' 3 < 0) :
    ∃ α : ℝ, 0 < α ∧
      ![p' 0, p' 1, α * r 2, α * r 3] ⬝ᵥ (z1 + z2) ![α * r 0, α * r 1, p' 2, p' 3] < 0 ∧
      ![α * r 0, α * r 1, p' 2, p' 3] ⬝ᵥ (z1 + z2) ![p' 0, p' 1, α * r 2, α * r 3] < 0 := by
  set c1 := r 0 * z1 p' 0 + r 1 * z1 p' 1
  set c2 := r 2 * z2 p' 2 + r 3 * z2 p' 3
  set R1 : Fin 4 → ℝ := ![r 0, r 1, 1, 1]
  set R2 : Fin 4 → ℝ := ![1, 1, r 2, r 3]
  set K1 := p' 0 * z1 R1 0 + p' 1 * z1 R1 1
  set K2 := p' 2 * z2 R2 2 + p' 3 * z2 R2 3
  set α := (|K1| + |K2| + 1) * (1 / -c1 + 1 / -c2) with hα
  have hc1' : 0 < -c1 := by linarith
  have hc2' : 0 < -c2 := by linarith
  have hαpos : 0 < α := by positivity
  have hR1 : R1 ∈ posOrthant 4 := by
    intro l; fin_cases l <;> simp [R1, hr 0, hr 1]
  have hR2 : R2 ∈ posOrthant 4 := by
    intro l; fin_cases l <;> simp [R2, hr 2, hr 3]
  have e1 : z1 ![α * r 0, α * r 1, p' 2, p' 3] = z1 R1 := by
    rw [← h.hom1 R1 hR1 α hαpos]
    exact h.dep1 _ _ (by simp [R1]) (by simp [R1])
  have e2 : z2 ![α * r 0, α * r 1, p' 2, p' 3] = z2 p' := h.dep2 _ _ (by simp) (by simp)
  have e3 : z1 ![p' 0, p' 1, α * r 2, α * r 3] = z1 p' := h.dep1 _ _ (by simp) (by simp)
  have e4 : z2 ![p' 0, p' 1, α * r 2, α * r 3] = z2 R2 := by
    rw [← h.hom2 R2 hR2 α hαpos]
    exact h.dep2 _ _ (by simp [R2]) (by simp [R2])
  have hbig1 : |K1| + |K2| + 1 ≤ α * -c2 := by
    rw [hα, mul_assoc]
    have : 1 ≤ (1 / -c1 + 1 / -c2) * -c2 := by
      rw [add_mul, one_div_mul_cancel hc2'.ne']
      have : 0 ≤ 1 / -c1 * -c2 := by positivity
      linarith
    nlinarith [abs_nonneg K1, abs_nonneg K2]
  have hbig2 : |K1| + |K2| + 1 ≤ α * -c1 := by
    rw [hα, mul_assoc]
    have : 1 ≤ (1 / -c1 + 1 / -c2) * -c1 := by
      rw [add_mul, one_div_mul_cancel hc1'.ne']
      have : 0 ≤ 1 / -c2 * -c1 := by positivity
      linarith
    nlinarith [abs_nonneg K1, abs_nonneg K2]
  refine ⟨α, hαpos, ?_, ?_⟩
  · rw [ex17F1_dot4]
    simp only [Pi.add_apply, e1, e2, (h.zero1 R1).1, (h.zero1 R1).2, (h.zero2 p').1,
      (h.zero2 p').2]
    simp only [Matrix.cons_val, add_zero, zero_add]
    have : p' 0 * z1 R1 0 + p' 1 * z1 R1 1 + α * r 2 * z2 p' 2 + α * r 3 * z2 p' 3 =
        K1 + α * c2 := by ring
    linarith [le_abs_self K1, abs_nonneg K2, mul_neg α c2]
  · rw [ex17F1_dot4]
    simp only [Pi.add_apply, e3, e4, (h.zero1 p').1, (h.zero1 p').2, (h.zero2 R2).1,
      (h.zero2 R2).2]
    simp only [Matrix.cons_val, add_zero, zero_add]
    have : α * r 0 * z1 p' 0 + α * r 1 * z1 p' 1 + p' 2 * z2 R2 2 + p' 3 * z2 R2 3 =
        α * c1 + K2 := by ring
    linarith [le_abs_self K2, abs_nonneg K1, mul_neg α c1]

/-- **Example 17.F.1** (MWG, p. 611). If the excess demands of the two consumers are both nonzero
at some `p' ≫ 0`, the aggregate excess demand `z¹ + z²` does not satisfy the weak axiom. -/
theorem example_17_F_1 {z1 z2 : (Fin 4 → ℝ) → Fin 4 → ℝ} (h : TwoBlockED z1 z2)
    {p' : Fin 4 → ℝ} (hp' : p' ∈ posOrthant 4) (h1 : z1 p' ≠ 0) (h2 : z2 p' ≠ 0) :
    ¬ WeakAxiomED (z1 + z2) := by
  have hne1 : z1 p' 0 ≠ 0 ∨ z1 p' 1 ≠ 0 := by
    by_contra hc
    push Not at hc
    apply h1
    funext l
    fin_cases l
    · exact hc.1
    · exact hc.2
    · exact (h.zero1 p').1
    · exact (h.zero1 p').2
  have hne2 : z2 p' 2 ≠ 0 ∨ z2 p' 3 ≠ 0 := by
    by_contra hc
    push Not at hc
    apply h2
    funext l
    fin_cases l
    · exact (h.zero2 p').1
    · exact (h.zero2 p').2
    · exact hc.1
    · exact hc.2
  obtain ⟨r0, r1, hr0, hr1, hc1⟩ := ex17F1_dir (hp' 0) (hp' 1) (h.walras1 p' hp') hne1
  obtain ⟨r2, r3, hr2, hr3, hc2⟩ := ex17F1_dir (hp' 2) (hp' 3) (h.walras2 p' hp') hne2
  have hr : ![r0, r1, r2, r3] ∈ posOrthant 4 := by
    intro l; fin_cases l <;> simp [hr0, hr1, hr2, hr3]
  obtain ⟨α, hα, hq, hq'⟩ := exercise_17_F_2 h (r := ![r0, r1, r2, r3]) hr
    (by simpa using hc1) (by simpa using hc2)
  simp only [Matrix.cons_val] at hq hq'
  set q : Fin 4 → ℝ := ![p' 0, p' 1, α * r2, α * r3]
  set q' : Fin 4 → ℝ := ![α * r0, α * r1, p' 2, p' 3]
  have hqpos : q ∈ posOrthant 4 := by
    intro l; fin_cases l <;> simp [q, hp' 0, hp' 1, mul_pos hα hr2, mul_pos hα hr3]
  have hq'pos : q' ∈ posOrthant 4 := by
    intro l; fin_cases l <;> simp [q', hp' 2, hp' 3, mul_pos hα hr0, mul_pos hα hr1]
  have hWq' : q' ⬝ᵥ (z1 + z2) q' = 0 := by
    rw [ex17F1_dot4]
    simp only [Pi.add_apply, (h.zero1 q').1, (h.zero1 q').2, (h.zero2 q').1, (h.zero2 q').2]
    have := h.walras1 q' hq'pos
    have := h.walras2 q' hq'pos
    linarith
  intro hWA
  have hne : (z1 + z2) q ≠ (z1 + z2) q' := fun heq => by
    rw [heq, hWq'] at hq'
    exact lt_irrefl _ hq'
  have := hWA q hqpos q' hq'pos hne hq.le
  linarith

/-- **Example 17.F.1** (MWG, p. 611), instance: consumer 1 with Cobb-Douglas shares `(½, ½)` over
goods 1-2 and endowment `(1, 1, 0, 0)`, consumer 2 likewise over goods 3-4 with endowment
`(0, 0, 1, 1)`: `z¹(p) = ((p₂ - p₁)/2p₁, (p₁ - p₂)/2p₂, 0, 0)` (homothetic preferences). -/
noncomputable def ex17F1Z1 (p : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![(p 1 - p 0) / (2 * p 0), (p 0 - p 1) / (2 * p 1), 0, 0]

/-- **Example 17.F.1**, instance: consumer 2's excess demand. -/
noncomputable def ex17F1Z2 (p : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![0, 0, (p 3 - p 2) / (2 * p 2), (p 2 - p 3) / (2 * p 3)]

/-- **Example 17.F.1**, instance: the aggregate excess demand. -/
noncomputable def ex17F1Z : (Fin 4 → ℝ) → Fin 4 → ℝ := ex17F1Z1 + ex17F1Z2

/-- `z¹` is the Cobb-Douglas excess demand `x(p, p·ω₁) - ω₁` with shares `(1, 1, 0, 0)` and
`ω₁ = (1, 1, 0, 0)`. -/
theorem ex17F1Z1_eq_cd {p : Fin 4 → ℝ} (hp : p ∈ posOrthant 4) :
    ex17F1Z1 p = cdDemand ![1, 1, 0, 0] p (p ⬝ᵥ ![1, 1, 0, 0]) - ![1, 1, 0, 0] := by
  have h0 := (hp 0).ne'
  have h1 := (hp 1).ne'
  have hw : p ⬝ᵥ ![1, 1, 0, 0] = p 0 + p 1 := by rw [ex17F1_dot4]; simp
  rw [hw]
  funext l
  fin_cases l <;> simp [ex17F1Z1, cdDemand, Fin.sum_univ_four] <;> field_simp <;> ring

/-- The instance satisfies the hypotheses of Example 17.F.1. -/
theorem ex17F1Z_twoBlock : TwoBlockED ex17F1Z1 ex17F1Z2 := by
  refine ⟨fun p q h0 h1 => by simp [ex17F1Z1, h0, h1], fun p q h2 h3 => by
    simp [ex17F1Z2, h2, h3], fun p => by simp [ex17F1Z1], fun p => by simp [ex17F1Z2],
    fun p hp α hα => ?_, fun p hp α hα => ?_, fun p hp => ?_, fun p hp => ?_⟩
  · have := (hp 0).ne'; have := (hp 1).ne'; have := hα.ne'
    funext l; fin_cases l <;> simp [ex17F1Z1] <;> field_simp
  · have := (hp 2).ne'; have := (hp 3).ne'; have := hα.ne'
    funext l; fin_cases l <;> simp [ex17F1Z2] <;> field_simp
  · have := (hp 0).ne'; have := (hp 1).ne'
    simp [ex17F1Z1]; field_simp; ring
  · have := (hp 2).ne'; have := (hp 3).ne'
    simp [ex17F1Z2]; field_simp; ring

/-- **Example 17.F.1**, instance: at `p' = (1, 2, 1, 2)` both excess demands are nonzero, so the
aggregate excess demand violates the weak axiom. -/
theorem ex17F1Z_not_weakAxiom : ¬ WeakAxiomED ex17F1Z := by
  refine example_17_F_1 ex17F1Z_twoBlock (p' := ![1, 2, 1, 2]) ?_ ?_ ?_
  · intro l; fin_cases l <;> simp
  · intro h; have := congrFun h 0; norm_num [ex17F1Z1] at this
  · intro h; have := congrFun h 2; norm_num [ex17F1Z2] at this

/-- The (weak) gross substitute check for one coordinate: if `p ≤ p'` and `p'ₖ = pₖ`, then
`(p_j - p_k)/(2p_k)` does not decrease. -/
theorem ex17F1_coord_mono {a b a' b' : ℝ} (hb : 0 < b) (hbb : b' = b) (haa : a ≤ a') :
    (a - b) / (2 * b) ≤ (a' - b') / (2 * b') := by
  subst hbb
  exact div_le_div_of_nonneg_right (by linarith) (by linarith)

/-- **Example 17.F.1**, instance: `ex17F1Z` has the weak gross substitute property. -/
theorem ex17F1Z_weakGS : WeakGrossSubstitute ex17F1Z := by
  intro p hp p' hp' l hl he k hk
  have hle : ∀ j, p j ≤ p' j := fun j => by
    by_cases hj : j = l
    · subst hj; exact hl.le
    · rw [he j hj]
  have hkk := he k hk
  have c0 : ∀ q, ex17F1Z q 0 = (q 1 - q 0) / (2 * q 0) := fun q => by
    simp [ex17F1Z, ex17F1Z1, ex17F1Z2]
  have c1 : ∀ q, ex17F1Z q 1 = (q 0 - q 1) / (2 * q 1) := fun q => by
    simp [ex17F1Z, ex17F1Z1, ex17F1Z2]
  have c2 : ∀ q, ex17F1Z q 2 = (q 3 - q 2) / (2 * q 2) := fun q => by
    simp [ex17F1Z, ex17F1Z1, ex17F1Z2]
  have c3 : ∀ q, ex17F1Z q 3 = (q 2 - q 3) / (2 * q 3) := fun q => by
    simp [ex17F1Z, ex17F1Z1, ex17F1Z2]
  rcases (by decide : ∀ k : Fin 4, k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) k with rfl | rfl | rfl | rfl
  · rw [c0, c0]; exact ex17F1_coord_mono (hp 0) hkk (hle 1)
  · rw [c1, c1]; exact ex17F1_coord_mono (hp 1) hkk (hle 0)
  · rw [c2, c2]; exact ex17F1_coord_mono (hp 2) hkk (hle 3)
  · rw [c3, c3]; exact ex17F1_coord_mono (hp 3) hkk (hle 2)

/-- **Example 17.F.1** (MWG, p. 611), correction: the example is not compatible with the (strict)
gross substitute property of Definition 17.F.2. Raising `p₃` leaves `z₁` unchanged, since
consumer 1's excess demand does not depend on `p₃` and consumer 2 does not trade good 1. -/
theorem example_17_F_1_not_GS {z1 z2 : (Fin 4 → ℝ) → Fin 4 → ℝ} (h : TwoBlockED z1 z2) :
    ¬ GrossSubstitute (z1 + z2) := by
  intro hGS
  have hp : (fun _ => (1 : ℝ)) ∈ posOrthant 4 := fun _ => one_pos
  have hp' : ![1, 1, 2, 1] ∈ posOrthant 4 := by intro l; fin_cases l <;> simp
  have := hGS _ hp ![1, 1, 2, 1] hp' 2 (by simp) (fun k hk => by fin_cases k <;> simp_all) 0
    (by decide)
  simp only [Pi.add_apply, (h.zero2 _).1] at this
  rw [h.dep1 ![1, 1, 2, 1] (fun _ => 1) (by simp) (by simp)] at this
  exact lt_irrefl _ this

/-- The instance is not a gross substitute excess demand. -/
theorem ex17F1Z_not_GS : ¬ GrossSubstitute ex17F1Z :=
  example_17_F_1_not_GS ex17F1Z_twoBlock

/-! ### Gross substitution does not imply the weak axiom (p. 613, footnote 48) -/

/-- **Section 17.F** (MWG, p. 613; footnote 48). `ex17F1Z` plus a third consumer with Cobb-Douglas
shares `(1, 1, 1, 1)` and endowment `(1/100)(1, 1, 1, 1)`. -/
noncomputable def gsNotWAZ : (Fin 4 → ℝ) → Fin 4 → ℝ :=
  cd1ED (fun _ => 1) (fun _ => 1 / 100) + ex17F1Z

/-- `gsNotWAZ` has the gross substitute property. -/
theorem gsNotWAZ_GS : GrossSubstitute gsNotWAZ :=
  (cd1_grossSubstitute (fun _ => one_pos) (fun _ => by norm_num)).add ex17F1Z_weakGS

/-- **Section 17.F** (MWG, p. 613). "The GS property does not imply the WA": `gsNotWAZ` has the
gross substitute property, yet at `q = (1, 2, 2, 8)`, `q' = (2, 8, 1, 2)` its values differ while
`q·z(q') < 0` and `q'·z(q) < 0`. -/
theorem gs_not_weakAxiom : GrossSubstitute gsNotWAZ ∧
    gsNotWAZ ![1, 2, 2, 8] ≠ gsNotWAZ ![2, 8, 1, 2] ∧
    ![1, 2, 2, 8] ⬝ᵥ gsNotWAZ ![2, 8, 1, 2] < 0 ∧ ![2, 8, 1, 2] ⬝ᵥ gsNotWAZ ![1, 2, 2, 8] < 0 ∧
    ¬ WeakAxiomED gsNotWAZ := by
  have v1 : gsNotWAZ ![2, 8, 1, 2] =
      ![1 / 160 + 3 / 2, -19 / 3200 - 3 / 8, 9 / 400 + 1 / 2, 1 / 160 - 1 / 4] := by
    funext k
    fin_cases k <;>
      norm_num [gsNotWAZ, ex17F1Z, ex17F1Z1, ex17F1Z2, cd1ED, cdDemand, dotProduct,
        Fin.sum_univ_four]
  have v2 : gsNotWAZ ![1, 2, 2, 8] =
      ![9 / 400 + 1 / 2, 1 / 160 - 1 / 4, 1 / 160 + 3 / 2, -19 / 3200 - 3 / 8] := by
    funext k
    fin_cases k <;>
      norm_num [gsNotWAZ, ex17F1Z, ex17F1Z1, ex17F1Z2, cd1ED, cdDemand, dotProduct,
        Fin.sum_univ_four]
  have h1 : ![1, 2, 2, 8] ⬝ᵥ gsNotWAZ ![2, 8, 1, 2] < 0 := by
    rw [v1, ex17F1_dot4]; norm_num
  have h2 : ![2, 8, 1, 2] ⬝ᵥ gsNotWAZ ![1, 2, 2, 8] < 0 := by
    rw [v2, ex17F1_dot4]; norm_num
  have hne : gsNotWAZ ![1, 2, 2, 8] ≠ gsNotWAZ ![2, 8, 1, 2] := by
    rw [v1, v2]
    intro h
    have := congrFun h 0
    norm_num at this
  refine ⟨gsNotWAZ_GS, hne, h1, h2, fun hWA => ?_⟩
  have hq : ![(1 : ℝ), 2, 2, 8] ∈ posOrthant 4 := by intro l; fin_cases l <;> simp
  have hq' : ![(2 : ℝ), 8, 1, 2] ∈ posOrthant 4 := by intro l; fin_cases l <;> simp
  have := hWA _ hq _ hq' hne h1.le
  linarith

/-- `gsNotWAZ` satisfies Walras' law. -/
theorem gsNotWAZ_walras : EDWalrasLaw gsNotWAZ := by
  intro p hp
  have hcd := (cd1ED_isStandard (a := fun _ : Fin 4 => (1 : ℝ)) (ω := fun _ => 1 / 100)
    (fun _ => one_pos) (fun _ => by norm_num)).walras p hp
  have h1 := ex17F1Z_twoBlock.walras1 p hp
  have h2 := ex17F1Z_twoBlock.walras2 p hp
  simp only [gsNotWAZ, ex17F1Z, Pi.add_apply, dotProduct_add] at hcd ⊢
  rw [hcd, ex17F1_dot4, ex17F1_dot4]
  simp only [(ex17F1Z_twoBlock.zero1 p).1, (ex17F1Z_twoBlock.zero1 p).2,
    (ex17F1Z_twoBlock.zero2 p).1, (ex17F1Z_twoBlock.zero2 p).2]
  linarith

/-- **Footnote 48** (MWG, p. 613). In a constant returns economy, gross substitution of the
consumers' excess demand does not imply uniqueness: for the closed convex cone
`Y* = {y : q·y ≤ 0, q'·y ≤ 0}`, both `q` and `q'` are equilibrium price vectors of `gsNotWAZ`
(Proposition 17.F.1), with different excess demands, so they are not proportional. -/
theorem footnote_17_48 :
    IsCRConvexTech (starTech ![1, 2, 2, 8] ![2, 8, 1, 2]) ∧
      IsCREqmPrice gsNotWAZ (starTech ![1, 2, 2, 8] ![2, 8, 1, 2]) ![1, 2, 2, 8] ∧
      IsCREqmPrice gsNotWAZ (starTech ![1, 2, 2, 8] ![2, 8, 1, 2]) ![2, 8, 1, 2] ∧
      ¬ ∃ α : ℝ, 0 < α ∧ ![(2 : ℝ), 8, 1, 2] = α • ![1, 2, 2, 8] := by
  obtain ⟨-, hne, h1, h2, -⟩ := gs_not_weakAxiom
  have hq : ![(1 : ℝ), 2, 2, 8] ∈ posOrthant 4 := by intro l; fin_cases l <;> simp
  have hq' : ![(2 : ℝ), 8, 1, 2] ∈ posOrthant 4 := by intro l; fin_cases l <;> simp
  obtain ⟨e1, e2⟩ := wa_violation_two_eqm gsNotWAZ_walras hq hq' h1.le h2.le
  refine ⟨(starTech_isCR _ _).1, e1, e2, fun ⟨α, hα, heq⟩ => ?_⟩
  have h0 := congrFun heq 0
  have h1' := congrFun heq 1
  simp at h0 h1'
  linarith

/-! ### Exercises 17.F.3 and 17.F.4: consumers who spend everything on one good -/

/-- **Exercise 17.F.4** (MWG, p. 645). The aggregate excess demand of consumers `i` who spend all
their wealth `p·ωᵢ` on one good `g(i)`: `z(p) = ∑ᵢ [(p·ωᵢ/p_{g(i)}) e^{g(i)} - ωᵢ]`. -/
noncomputable def cornerED {ι : Type*} [Fintype ι] {L : ℕ} (g : ι → Fin L)
    (ω : ι → Fin L → ℝ) (p : Fin L → ℝ) : Fin L → ℝ :=
  ∑ i, ((p ⬝ᵥ ω i / p (g i)) • Pi.single (g i) (1 : ℝ) - ω i)

/-- **Exercise 17.F.4** (MWG, p. 645). If every consumer spends all his wealth on one good, the
aggregate excess demand has the weak gross substitute property (endowments `ωᵢ ≥ 0`). -/
theorem exercise_17_F_4 {ι : Type*} [Fintype ι] {L : ℕ} (g : ι → Fin L)
    {ω : ι → Fin L → ℝ} (hω : ∀ i l, 0 ≤ ω i l) : WeakGrossSubstitute (cornerED g ω) := by
  intro p hp p' hp' l hl he k hk
  simp only [cornerED, Finset.sum_apply]
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_le_sub_iff_right]
  have hw : p ⬝ᵥ ω i ≤ p' ⬝ᵥ ω i := by
    refine Finset.sum_le_sum fun j _ => ?_
    by_cases hj : j = l
    · subst hj; exact mul_le_mul_of_nonneg_right hl.le (hω i j)
    · rw [he j hj]
  by_cases hgk : g i = k
  · subst hgk
    simp only [Pi.single_eq_same, mul_one, he (g i) hk]
    exact div_le_div_of_nonneg_right hw (hp (g i)).le
  · simp [Pi.single_eq_of_ne' hgk]

/-- **Exercise 17.F.3** (MWG, p. 645). Four goods; consumer 1 spends all his wealth on good 3,
consumer 2 on good 4; endowments `ω₁ = (1, 0, 0, 0)` and `ω₂ = (0, 1, 0, 0)`
(`ω₁₁ = 1, ω₂₁ = 0, ω₁₂ = 0, ω₂₂ = 1`). Then `z(p) = (-1, -1, p₁/p₃, p₂/p₄)` violates the weak
axiom at `p = (1, 1, 1, 1)`, `p' = (1, 3, 2, 2)`. -/
theorem exercise_17_F_3 :
    ¬ WeakAxiomED (cornerED (ι := Fin 2) ![2, 3] ![![1, 0, 0, 0], ![0, 1, 0, 0]]) := by
  intro hWA
  have hp : (fun _ => (1 : ℝ)) ∈ posOrthant 4 := fun _ => one_pos
  have hp' : ![(1 : ℝ), 3, 2, 2] ∈ posOrthant 4 := by intro l; fin_cases l <;> simp
  have v1 : cornerED (ι := Fin 2) ![2, 3] ![![1, 0, 0, 0], ![0, 1, 0, 0]] (fun _ => 1) =
      ![-1, -1, 1, 1] := by
    funext k
    fin_cases k <;>
      norm_num [cornerED, Fin.sum_univ_two, dotProduct, Fin.sum_univ_four, Pi.single_apply]
  have v2 : cornerED (ι := Fin 2) ![2, 3] ![![1, 0, 0, 0], ![0, 1, 0, 0]] ![1, 3, 2, 2] =
      ![-1, -1, 1 / 2, 3 / 2] := by
    funext k
    fin_cases k <;>
      norm_num [cornerED, Fin.sum_univ_two, dotProduct, Fin.sum_univ_four, Pi.single_apply]
  have hne : cornerED (ι := Fin 2) ![2, 3] ![![1, 0, 0, 0], ![0, 1, 0, 0]] (fun _ => 1) ≠
      cornerED (ι := Fin 2) ![2, 3] ![![1, 0, 0, 0], ![0, 1, 0, 0]] ![1, 3, 2, 2] := by
    rw [v1, v2]
    intro h
    have := congrFun h 2
    norm_num at this
  have hle : (fun _ => (1 : ℝ)) ⬝ᵥ
      cornerED (ι := Fin 2) ![2, 3] ![![1, 0, 0, 0], ![0, 1, 0, 0]] ![1, 3, 2, 2] ≤ 0 := by
    rw [v2, ex17F1_dot4]; norm_num
  have := hWA _ hp _ hp' hne hle
  rw [v1, ex17F1_dot4] at this
  norm_num at this

/-! ### Example 17.F.2: Cobb-Douglas as the borderline case -/

/-- **Example 17.F.2** (MWG, pp. 612-613). For one Cobb-Douglas consumer,
`zₗ(p) = αₗ(p·ω)/pₗ - ωₗ`: if only `pₖ` changes (to `p'ₖ`), then for `ℓ ≠ k`
`zₗ(p') - zₗ(p) = (αₗ/∑α)(p'ₖ - pₖ)ωₖ/pₗ`, so `zₗ` responds positively to an increase in `pₖ` iff
`ωₖ > 0`, and does not respond if `ωₖ = 0`. -/
theorem example_17_F_2_cd {L : ℕ} (a ω : Fin L → ℝ) {p p' : Fin L → ℝ} {k : Fin L}
    (he : ∀ j, j ≠ k → p' j = p j) {l : Fin L} (hlk : l ≠ k) :
    cd1ED a ω p' l - cd1ED a ω p l = a l / (∑ j, a j) * ((p' k - p k) * ω k / p l) := by
  have hw : p' ⬝ᵥ ω = p ⬝ᵥ ω + (p' k - p k) * ω k := by
    simp only [dotProduct]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ k),
      Finset.sum_congr rfl fun j hj => by rw [he j (Finset.ne_of_mem_erase hj)]]
    ring
  simp only [cd1ED, cdDemand, Pi.sub_apply, he l hlk, hw]
  ring

/-- **Section 17.F** (MWG, p. 613). The weak axiom does not imply gross substitution: one
Cobb-Douglas consumer with `a = (1, 1)` and `ω = (1, 0)` satisfies the weak axiom, but raising
`p₂` leaves `z₁` unchanged (`ω₂ = 0`, Example 17.F.2). -/
theorem wa_not_gs : WeakAxiomED (cd1ED ![1, 1] ![1, 0]) ∧
    ¬ GrossSubstitute (cd1ED ![1, 1] ![1, 0]) := by
  refine ⟨cd1_weakAxiom (fun l => by fin_cases l <;> simp)
    (fun l => by fin_cases l <;> simp), fun hGS => ?_⟩
  have hp : ![(1 : ℝ), 1] ∈ posOrthant 2 := by intro l; fin_cases l <;> simp
  have hp' : ![(1 : ℝ), 2] ∈ posOrthant 2 := by intro l; fin_cases l <;> simp
  have he : ∀ j, j ≠ 1 → ![(1 : ℝ), 2] j = ![1, 1] j := fun j hj => by
    fin_cases j
    · rfl
    · exact absurd rfl hj
  have h := hGS _ hp _ hp' 1 (by simp) he 0 (by decide)
  have hd := example_17_F_2_cd ![1, 1] ![1, 0] he (l := 0) (by decide)
  simp at hd
  linarith

/-! ### The differential version: zero cross effects are possible -/

/-- **Section 17.F** (MWG, p. 612). A two-good gross substitute excess demand:
with `r = p₂/p₁` and `h(r) = (r - 1)³ + 1`, `z(p) = (r h(r), -h(r))`. -/
noncomputable def gsCubicZ (p : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![(p 1 / p 0) * ((p 1 / p 0 - 1) ^ 3 + 1), -((p 1 / p 0 - 1) ^ 3 + 1)]

/-- `h(r) = (r - 1)³ + 1` is strictly increasing. -/
theorem gsCubic_h_strictMono : StrictMono fun r : ℝ => (r - 1) ^ 3 + 1 := by
  intro r s hrs
  have := Odd.strictMono_pow (R := ℝ) (by decide : Odd 3) (sub_lt_sub_right hrs 1)
  simpa using this

/-- `h(r) > 0` for `r > 0`. -/
theorem gsCubic_h_pos {r : ℝ} (hr : 0 < r) : 0 < (r - 1) ^ 3 + 1 := by
  have h := Odd.strictMono_pow (R := ℝ) (by decide : Odd 3) (show (-1 : ℝ) < r - 1 by linarith)
  norm_num at h
  linarith

/-- **Section 17.F** (MWG, p. 612). `gsCubicZ` is homogeneous of degree zero, satisfies Walras'
law and has the gross substitute property. -/
theorem gsCubicZ_props : EDHomogeneous gsCubicZ ∧ EDWalrasLaw gsCubicZ ∧
    GrossSubstitute gsCubicZ := by
  refine ⟨fun p hp α hα => ?_, fun p hp => ?_, ?_⟩
  · have h0 := (hp 0).ne'
    have hα' := hα.ne'
    have : (α • p) 1 / (α • p) 0 = p 1 / p 0 := by
      simp only [Pi.smul_apply, smul_eq_mul]; field_simp
    simp only [gsCubicZ, this]
  · have h0 := (hp 0).ne'
    simp [gsCubicZ, dotProduct, Fin.sum_univ_two]
    field_simp
    ring
  · intro p hp p' hp' l hl he k hk
    rcases (by decide : ∀ j : Fin 2, j = 0 ∨ j = 1) l with rfl | rfl <;>
      rcases (by decide : ∀ j : Fin 2, j = 0 ∨ j = 1) k with rfl | rfl
    · exact absurd rfl hk
    · -- raising `p₁` lowers `r`, so `z₂ = -h(r)` rises
      have h1 := he 1 (by decide)
      change -((p 1 / p 0 - 1) ^ 3 + 1) < -((p' 1 / p' 0 - 1) ^ 3 + 1)
      rw [h1, neg_lt_neg_iff]
      exact gsCubic_h_strictMono (div_lt_div_of_pos_left (hp 1) (hp 0) hl)
    · -- raising `p₂` raises `r`, so `z₁ = r h(r)` rises
      have h0 := he 0 (by decide)
      change p 1 / p 0 * ((p 1 / p 0 - 1) ^ 3 + 1) < p' 1 / p' 0 * ((p' 1 / p' 0 - 1) ^ 3 + 1)
      rw [h0]
      set r := p 1 / p 0
      set s := p' 1 / p 0
      have hr : 0 < r := div_pos (hp 1) (hp 0)
      have hrs : r < s := div_lt_div_of_pos_right hl (hp 0)
      have hhr := gsCubic_h_pos hr
      have hh := gsCubic_h_strictMono hrs
      simp only at hh
      nlinarith
    · exact absurd rfl hk

/-- **Section 17.F** (MWG, p. 612), correction: gross substitution does not force
`∂zₖ/∂pₗ > 0`. For `gsCubicZ`, `∂z₂/∂p₁ = 0` at `p = (1, 1)`: the derivative of
`t ↦ z₂(t, 1)` at `t = 1` is `0`. -/
theorem gs_partial_not_pos : HasDerivAt (fun t : ℝ => gsCubicZ ![t, 1] 1) 0 1 := by
  have hf : (fun t : ℝ => gsCubicZ ![t, 1] 1) = fun t => -((t⁻¹ - 1) ^ 3 + 1) := by
    funext t
    simp [gsCubicZ, one_div]
  rw [hf]
  have h := ((((hasDerivAt_inv (one_ne_zero (α := ℝ))).sub_const 1).pow 3).add_const 1).neg
  convert h using 1
  norm_num

/-! ### Footnote 45 -/

/-- **Footnote 45** (MWG, p. 612). For an input-output matrix `A` (nonnegative off-diagonal entries)
and `c`, the function `α ↦ c - (I - A)α` has the weak gross substitute property: raising the other
coordinates of `α` does not lower its `k`-th coordinate. -/
theorem footnote_17_45_io {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ k l, k ≠ l → 0 ≤ A k l) (c : Fin n → ℝ) {α α' : Fin n → ℝ} (hle : α ≤ α')
    {k : Fin n} (hk : α k = α' k) :
    (c - Matrix.mulVec (1 - A) α : Fin n → ℝ) k ≤ (c - Matrix.mulVec (1 - A) α' : Fin n → ℝ) k :=
    by
  simp only [Pi.sub_apply, Matrix.sub_mulVec, Matrix.one_mulVec, hk, sub_le_sub_iff_left,
    sub_le_sub_iff_left]
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_le_sum fun l _ => ?_
  by_cases hl : l = k
  · subst hl; rw [hk]
  · exact mul_le_mul_of_nonneg_left (hle l) (hA k l (Ne.symm hl))

/-- **Footnote 45** (MWG, p. 612). If `g : ℝ^N → ℝ^N` is increasing (`α ≥ α'` implies
`g(α) ≥ g(α')`), then `g(α) - α` has the weak gross substitute property. -/
theorem footnote_17_45_fixed {n : ℕ} {g : (Fin n → ℝ) → Fin n → ℝ} (hg : Monotone g)
    {α α' : Fin n → ℝ} (hle : α ≤ α') {k : Fin n} (hk : α k = α' k) :
    (g α - α) k ≤ (g α' - α') k := by
  simp only [Pi.sub_apply, hk, sub_le_sub_iff_right]
  exact hg hle k

end MWG.PositiveEquilibriumTheory
