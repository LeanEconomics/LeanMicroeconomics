/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.UMPExercises

/-!
# Sufficiency of the Kuhn-Tucker conditions; Exercises 3.D.3(b) and 3.D.4(c)

MWG, Section 3.D, small type p. 55, and Exercises 3.D.3(b), 3.D.4(c), p. 97.

* Small type, p. 55: if `u` is quasiconcave and monotone on `ℝ^L_+` and `∇u(x*) ≠ 0`, a budget-
  exhausting `x*` satisfying (3.D.1) solves the UMP (`p ≫ 0`, `w > 0`; `u` continuous on
  `ℝ^L_+`, as assumed throughout Section 3.D).
* Exercise 3.D.3(b): a continuous quasiconcave utility with `∇u(x) ≫ 0` on `ℝ^L_{++}` whose
  indirect utility is homogeneous of degree one in wealth is homogeneous of degree one. Every
  `x ≫ 0` is demanded at the supporting prices `∇u(x)`.
* Exercise 3.D.4(c): with `u = x₁ + η(x₂)` on `ℝ²_+`, `η` concave and `x̂₂` maximizing
  `η(x₂) - p₂x₂` on `x₂ ≥ 0`, demand is `(w - p₂x̂₂, x̂₂)` when `w ≥ p₂x̂₂` and `(0, w/p₂)`
  otherwise: the nonnegativity constraint on the numeraire is irrelevant iff `w ≥ p₂x̂₂`.
-/

namespace MWG.ClassicalDemand

open Filter Topology MWG.ConsumerChoice

variable {L : ℕ}

/-- Along a segment inside `ℝ^L_+` from `y`, a utility continuous on `ℝ^L_+` tends to `u(y)`. -/
theorem tendsto_along_orthant {u : (Fin L → ℝ) → ℝ} (hcont : ContinuousOn u (nonnegOrthant L))
    {y v : Fin L → ℝ} (hy : y ∈ nonnegOrthant L)
    (hmem : ∀ᶠ t in 𝓝[>] (0 : ℝ), y + t • v ∈ nonnegOrthant L) :
    Tendsto (fun t : ℝ => u (y + t • v)) (𝓝[>] 0) (𝓝 (u y)) := by
  have hpath : Tendsto (fun t : ℝ => y + t • v) (𝓝[>] 0) (𝓝[nonnegOrthant L] y) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, hmem⟩
    have : Continuous (fun t : ℝ => y + t • v) := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  exact (hcont y hy).tendsto.comp hpath

/-- A quasiconcave `u` differentiable at `x ∈ ℝ^L_+` has `∇u(x)·(y - x) > 0` whenever
`u(y) > u(x)` and some good with `∂u(x)/∂x_l > 0` is consumed at `y`. -/
theorem quasiconcave_gradient_pos {u : (Fin L → ℝ) → ℝ} {u' : (Fin L → ℝ) →L[ℝ] ℝ}
    (hq : QuasiconcaveOn ℝ (nonnegOrthant L) u) (hcont : ContinuousOn u (nonnegOrthant L))
    {x y : Fin L → ℝ} (hx : x ∈ nonnegOrthant L) (hy : y ∈ nonnegOrthant L)
    (hu : HasFDerivAt u u' x) (hlt : u x < u y) {l : Fin L} (hyl : 0 < y l)
    (hgl : 0 < u' (Pi.single l 1)) : 0 < u' (y - x) := by
  have hnn := theorem_M_C_3_necessity hq hx hy hu hlt.le
  rcases hnn.lt_or_eq with h | h
  · exact h
  exfalso
  have hmem : ∀ᶠ t in 𝓝[>] (0 : ℝ), y + t • (-(Pi.single l 1 : Fin L → ℝ)) ∈ nonnegOrthant L := by
    filter_upwards [Ioo_mem_nhdsGT hyl] with t ht k
    by_cases hk : k = l
    · subst hk; simp; linarith [ht.2]
    · simp [hk, hy k]
  have hlim := tendsto_along_orthant hcont hy hmem
  obtain ⟨t, ⟨ht, htm⟩, ht0⟩ := ((hlim.eventually (lt_mem_nhds hlt)).and hmem |>.and
    self_mem_nhdsWithin).exists
  have hge := theorem_M_C_3_necessity hq hx htm hu ht.le
  have : y + t • (-(Pi.single l 1 : Fin L → ℝ)) - x = (y - x) - t • Pi.single l 1 := by
    rw [smul_neg]; abel
  rw [this, map_sub, ← h, map_smul, smul_eq_mul] at hge
  have ht0' : (0 : ℝ) < t := ht0
  nlinarith

/-- Monotonicity and continuity on `ℝ^L_+` make `u` weakly increasing there. -/
theorem utility_mono_of_strict {u : (Fin L → ℝ) → ℝ} (hcont : ContinuousOn u (nonnegOrthant L))
    (hmono : ∀ x ∈ nonnegOrthant L, ∀ y ∈ nonnegOrthant L, (∀ l, x l < y l) → u x < u y)
    {x y : Fin L → ℝ} (hx : x ∈ nonnegOrthant L) (hy : y ∈ nonnegOrthant L) (hxy : x ≤ y) :
    u x ≤ u y := by
  have hmem : ∀ᶠ t in 𝓝[>] (0 : ℝ), y + t • (fun _ => (1 : ℝ)) ∈ nonnegOrthant L := by
    filter_upwards [self_mem_nhdsWithin] with t ht k
    have ht' : (0 : ℝ) < t := ht
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one]
    linarith [hy k]
  apply ge_of_tendsto (tendsto_along_orthant hcont hy hmem)
  filter_upwards [hmem, self_mem_nhdsWithin] with t htm ht
  have ht' : (0 : ℝ) < t := ht
  refine (hmono x hx _ htm fun k => ?_).le
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one]
  linarith [hxy k]

/-- **Section 3.D, small type** (MWG, p. 55), under the book's hypotheses. Let `u` be continuous,
quasiconcave and monotone on `ℝ^L_+`, differentiable at `x*` with `∇u(x*) ≠ 0`, and
`w > 0` (`p ≫ 0` is not needed). If `x*` exhausts the budget and satisfies the Kuhn-Tucker
conditions (3.D.1) with
some `λ ≥ 0`, then `x*` solves the UMP. -/
theorem ump_kuhn_tucker_sufficient_quasiconcave {u : (Fin L → ℝ) → ℝ}
    {u' : (Fin L → ℝ) →L[ℝ] ℝ} (hq : QuasiconcaveOn ℝ (nonnegOrthant L) u)
    (hcont : ContinuousOn u (nonnegOrthant L))
    (hmono : ∀ x ∈ nonnegOrthant L, ∀ y ∈ nonnegOrthant L, (∀ l, x l < y l) → u x < u y)
    {p : Fin L → ℝ} {w : ℝ} (hw : 0 < w) {x : Fin L → ℝ}
    (hx : x ∈ budgetSet p w) (hbind : p ⬝ᵥ x = w) (hu : HasFDerivAt u u' x) (hne : u' ≠ 0)
    {lam : ℝ} (hlam : 0 ≤ lam)
    (hfoc : ∀ l, gradientVec u' l ≤ lam * p l ∧ (0 < x l → gradientVec u' l = lam * p l)) :
    x ∈ walrasianDemand u p w := by
  set g := gradientVec u' with hg
  -- the gradient is nonnegative
  have hg0 : ∀ l, 0 ≤ g l := by
    intro l
    apply mc_le_deriv_of_slope (mc_line_hasDerivAt hu (Pi.single l 1))
    intro t ht0 _
    have hmem : x + t • (Pi.single l 1 : Fin L → ℝ) ∈ nonnegOrthant L := fun k => by
      by_cases hk : k = l
      · subst hk; simp; linarith [hx.1 k]
      · simp [hk, hx.1 k]
    have hle := utility_mono_of_strict hcont hmono hx.1 hmem fun k => by
      by_cases hk : k = l
      · subst hk; simp; linarith
      · simp [hk]
    simp only [zero_smul, add_zero]
    exact div_nonneg (by linarith) ht0.le
  -- the multiplier is positive
  have hlampos : 0 < lam := by
    rcases hlam.lt_or_eq with h | h
    · exact h
    · exfalso
      apply hne
      ext v
      rw [fderiv_apply_eq_gradient_dot, zero_apply]
      have hzero : ∀ l, g l = 0 := by
        intro l
        have h1 := (hfoc l).1
        rw [← h, zero_mul] at h1
        exact le_antisymm h1 (hg0 l)
      have : g = 0 := funext hzero
      rw [← hg, this, zero_dotProduct]
  refine ⟨hx, fun y hy => ?_⟩
  by_contra hlt
  push Not at hlt
  have h1 : g ⬝ᵥ y ≤ lam * (p ⬝ᵥ y) := by
    rw [dotProduct, dotProduct, Finset.mul_sum]
    refine Finset.sum_le_sum fun l _ => ?_
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hfoc l).1 (hy.1 l)
  have h2 : g ⬝ᵥ x = lam * (p ⬝ᵥ x) := by
    rw [dotProduct, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rcases (hx.1 l).lt_or_eq with hl | hl
    · rw [(hfoc l).2 hl, mul_assoc]
    · rw [← hl]; simp
  have hnn := theorem_M_C_3_necessity hq hx.1 hy.1 hu hlt.le
  rw [fderiv_apply_eq_gradient_dot, dotProduct_sub] at hnn
  have h3 : lam * (p ⬝ᵥ y) ≤ lam * w := mul_le_mul_of_nonneg_left hy.2 hlam
  -- `g·y = λw > 0`, so some good with positive marginal utility is consumed at `y`
  have hgy : 0 < g ⬝ᵥ y := by rw [hbind] at h2; nlinarith
  obtain ⟨l, -, hl⟩ : ∃ l ∈ Finset.univ, 0 < g l * y l := by
    by_contra hall
    push Not at hall
    have : g ⬝ᵥ y ≤ 0 := Finset.sum_nonpos fun l hl => hall l hl
    linarith
  have hyl : 0 < y l := by
    by_contra h; push Not at h; nlinarith [hg0 l, hy.1 l]
  have hgl : 0 < g l := by
    by_contra h; push Not at h; nlinarith [hy.1 l]
  have hpos := quasiconcave_gradient_pos hq hcont hx.1 hy.1 hu hlt hyl hgl
  rw [fderiv_apply_eq_gradient_dot, dotProduct_sub] at hpos
  rw [hbind] at h2
  linarith

/-- **Exercise 3.D.3(b), supporting prices.** If `u` is continuous and quasiconcave on `ℝ^L_+`
and differentiable at `x ≫ 0` with `∇u(x) ≫ 0`, then `x` is demanded at `p = ∇u(x)`,
`w = p·x`. -/
theorem demanded_at_supporting_prices {u : (Fin L → ℝ) → ℝ} {u' : (Fin L → ℝ) →L[ℝ] ℝ}
    (hq : QuasiconcaveOn ℝ (nonnegOrthant L) u) (hcont : ContinuousOn u (nonnegOrthant L))
    {x : Fin L → ℝ} (hx : ∀ l, 0 < x l) (hu : HasFDerivAt u u' x)
    (hg : ∀ l, 0 < gradientVec u' l) :
    x ∈ walrasianDemand u (gradientVec u') (gradientVec u' ⬝ᵥ x) := by
  have hx0 : x ∈ nonnegOrthant L := fun l => (hx l).le
  refine ⟨⟨hx0, le_rfl⟩, fun y hy => ?_⟩
  by_contra hlt
  push Not at hlt
  have hpy : 0 < gradientVec u' ⬝ᵥ y ∨ y = 0 := by
    by_cases h : y = 0
    · exact Or.inr h
    · left
      obtain ⟨l, hl⟩ : ∃ l, y l ≠ 0 := by
        by_contra hall; push Not at hall; exact h (funext hall)
      have hyl : 0 < y l := lt_of_le_of_ne (hy.1 l) (Ne.symm hl)
      have := Finset.single_le_sum (f := fun k => gradientVec u' k * y k)
        (fun k _ => mul_nonneg (hg k).le (hy.1 k)) (Finset.mem_univ l)
      exact lt_of_lt_of_le (mul_pos (hg l) hyl) this
  rcases hpy with hpy | rfl
  · obtain ⟨l, -, hl⟩ : ∃ l ∈ Finset.univ, 0 < gradientVec u' l * y l := by
      by_contra hall
      push Not at hall
      have : gradientVec u' ⬝ᵥ y ≤ 0 := Finset.sum_nonpos fun l hl => hall l hl
      linarith
    have hyl : 0 < y l := by
      by_contra h; push Not at h; nlinarith [hg l, hy.1 l]
    have hpos := quasiconcave_gradient_pos hq hcont hx0 hy.1 hu hlt hyl (hg l)
    rw [fderiv_apply_eq_gradient_dot, dotProduct_sub] at hpos
    linarith [hy.2]
  · rcases Nat.eq_zero_or_pos L with hL | hL
    · subst hL
      exact lt_irrefl _ (by rwa [Subsingleton.elim x 0] at hlt)
    · have hnn := theorem_M_C_3_necessity hq hx0 hy.1 hu hlt.le
      rw [fderiv_apply_eq_gradient_dot, zero_sub, dotProduct_neg] at hnn
      have : 0 < gradientVec u' ⬝ᵥ x :=
        Finset.sum_pos (fun l _ => mul_pos (hg l) (hx l)) ⟨⟨0, hL⟩, Finset.mem_univ _⟩
      linarith

/-- **Exercise 3.D.3(b)** (MWG, p. 97). Let `u` be continuous and quasiconcave on `ℝ^L_+`,
differentiable at every `x ≫ 0` with `∇u(x) ≫ 0`. If the indirect utility is homogeneous of
degree one in wealth, then `u` is homogeneous of degree one on `ℝ^L_+`. -/
theorem exercise_3_D_3b_full {u : (Fin L → ℝ) → ℝ} {u' : (Fin L → ℝ) → (Fin L → ℝ) →L[ℝ] ℝ}
    (hq : QuasiconcaveOn ℝ (nonnegOrthant L) u) (hcont : ContinuousOn u (nonnegOrthant L))
    (hdiff : ∀ x, (∀ l, 0 < x l) → HasFDerivAt u (u' x) x)
    (hgpos : ∀ x, (∀ l, 0 < x l) → ∀ l, 0 < gradientVec (u' x) l)
    (hv : ∀ p w α, StrictlyPositive p → 0 < w → 0 < α →
      indirectUtility u p (α * w) = α * indirectUtility u p w) :
    HomogeneousOneOn u := by
  rcases Nat.eq_zero_or_pos L with hL | hL
  · subst hL
    intro x _ α ha
    have hval : ∀ w : ℝ, 0 ≤ w → indirectUtility u (0 : Fin 0 → ℝ) w = u 0 := by
      intro w hw
      apply indirectUtility_eq_of_mem
      refine ⟨⟨fun l => l.elim0, by simp [hw]⟩, fun y _ => ?_⟩
      rw [Subsingleton.elim y 0]
    have h := hv 0 1 2 (fun l => l.elim0) one_pos two_pos
    rw [hval _ (by norm_num), hval _ one_pos.le] at h
    have h0 : u 0 = 0 := by linarith
    rw [Subsingleton.elim (α • x) 0, Subsingleton.elim x 0, h0, mul_zero]
  have hw : ∀ z, (∀ l, 0 < z l) → 0 < gradientVec (u' z) ⬝ᵥ z := fun z hz =>
    Finset.sum_pos (fun l _ => mul_pos (hgpos z hz l) (hz l)) ⟨⟨0, hL⟩, Finset.mem_univ _⟩
  have hint : ∀ x, (∀ l, 0 < x l) → ∀ α : ℝ, 0 < α → u (α • x) = α * u x := by
    intro x hx α ha
    have hax : ∀ l, 0 < (α • x) l := fun l => by simpa using mul_pos ha (hx l)
    exact exercise_3_D_3b hcont hv (fun l => hgpos x hx l) (fun l => hgpos _ hax l) (hw x hx)
      (hw _ hax) ha (demanded_at_supporting_prices hq hcont hx (hdiff x hx) (hgpos x hx))
      (demanded_at_supporting_prices hq hcont hax (hdiff _ hax) (hgpos _ hax))
  intro x hx α ha
  set one : Fin L → ℝ := fun _ => 1 with hone
  have hm1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), x + t • one ∈ nonnegOrthant L := by
    filter_upwards [self_mem_nhdsWithin] with t ht k
    have ht' : (0 : ℝ) < t := ht
    simp only [hone, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one]
    linarith [hx k]
  have hax : α • x ∈ nonnegOrthant L := fun l => by simpa using mul_nonneg ha.le (hx l)
  have hm2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), α • x + t • (α • one) ∈ nonnegOrthant L := by
    filter_upwards [self_mem_nhdsWithin] with t ht k
    have ht' : (0 : ℝ) < t := ht
    simp only [hone, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one]
    nlinarith [mul_nonneg ha.le (hx k), mul_pos ht' ha]
  have hl1 := (tendsto_along_orthant hcont hx hm1).const_mul α
  have hl2 := tendsto_along_orthant hcont hax hm2
  refine tendsto_nhds_unique hl2 (hl1.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : (0 : ℝ) < t := ht
  have hpos : ∀ l, 0 < (x + t • one) l := fun l => by
    simp only [hone, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one]; linarith [hx l]
  rw [← hint _ hpos α ha]
  congr 1
  rw [smul_add, smul_comm]

/-- A concave function is nondecreasing to the left of a maximizer. -/
theorem concave_mono_left_of_max {h : ℝ → ℝ} (hh : ConcaveOn ℝ (Set.Ici 0) h) {xh a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hbx : b ≤ xh) (hmax : ∀ t, 0 ≤ t → h t ≤ h xh) : h a ≤ h b := by
  rcases hbx.lt_or_eq with hlt | heq
  · set θ := (xh - b) / (xh - a) with hθ
    have hxa : 0 < xh - a := by linarith
    have hθ0 : 0 ≤ θ := div_nonneg (by linarith) hxa.le
    have hθ1 : θ ≤ 1 := by rw [div_le_one hxa]; linarith
    have hb : θ • a + (1 - θ) • xh = b := by
      simp only [smul_eq_mul]
      rw [hθ]; field_simp; ring
    have := hh.2 (x := a) (y := xh) (Set.mem_Ici.mpr ha) (Set.mem_Ici.mpr (by linarith)) hθ0
      (show (0 : ℝ) ≤ 1 - θ by linarith) (by ring)
    rw [hb] at this
    simp only [smul_eq_mul] at this
    have hm := hmax a ha
    nlinarith
  · rw [heq]; exact hmax a ha

/-- **Exercise 3.D.4(c)** (MWG, p. 97). Quasilinear utility `x₁ + η(x₂)` on `ℝ²_+`, prices
`(1, p₂)`, `η` concave on `ℝ_+`, `x̂₂ ≥ 0` maximizing `η(x₂) - p₂x₂`. If `w ≥ p₂x̂₂` the bundle
`(w - p₂x̂₂, x̂₂)` (the solution without the nonnegativity constraint on `x₁`) is demanded. -/
theorem exercise_3_D_4c_high {η : ℝ → ℝ} {p₂ xh w : ℝ}
    (hxh : 0 ≤ xh) (hmax : ∀ t, 0 ≤ t → η t - p₂ * t ≤ η xh - p₂ * xh) (hw : p₂ * xh ≤ w) :
    ![w - p₂ * xh, xh] ∈ walrasianDemand (fun x => x 0 + η (x 1)) ![1, p₂] w := by
  refine ⟨⟨fun l => ?_, ?_⟩, fun y hy => ?_⟩
  · fin_cases l <;> simp <;> linarith
  · simp [dotProduct, Fin.sum_univ_two]
  · have hb := hy.2
    simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      one_mul] at hb
    have := hmax (y 1) (hy.1 1)
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    linarith

/-- **Exercise 3.D.4(c)** (MWG, p. 97). If `0 ≤ w < p₂x̂₂` (with `p₂ > 0`), the nonnegativity
constraint binds: the corner `(0, w/p₂)` is demanded. -/
theorem exercise_3_D_4c_low {η : ℝ → ℝ} (hη : ConcaveOn ℝ (Set.Ici 0) η) {p₂ xh w : ℝ}
    (hp₂ : 0 < p₂) (hmax : ∀ t, 0 ≤ t → η t - p₂ * t ≤ η xh - p₂ * xh) (hw0 : 0 ≤ w)
    (hw : w < p₂ * xh) :
    ![0, w / p₂] ∈ walrasianDemand (fun x => x 0 + η (x 1)) ![1, p₂] w := by
  have hh : ConcaveOn ℝ (Set.Ici 0) (fun t => η t - p₂ * t) :=
    hη.sub (convexOn_id (convex_Ici 0) |>.smul hp₂.le)
  refine ⟨⟨fun l => ?_, ?_⟩, fun y hy => ?_⟩
  · fin_cases l
    · simp
    · simpa using div_nonneg hw0 hp₂.le
  · simp [dotProduct, Fin.sum_univ_two, mul_div_cancel₀ _ hp₂.ne']
  · have hb := hy.2
    simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      one_mul] at hb
    have hy1 : y 1 ≤ w / p₂ := by
      rw [le_div_iff₀ hp₂]; nlinarith [hy.1 0]
    have hwx : w / p₂ ≤ xh := by rw [div_le_iff₀ hp₂]; linarith
    have := concave_mono_left_of_max hh (hy.1 1) hy1 hwx hmax
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this ⊢
    rw [mul_div_cancel₀ _ hp₂.ne'] at this
    linarith

/-- **Exercise 3.D.4(c)** (MWG, p. 97). The unconstrained solution `(w - p₂x̂₂, x̂₂)` lies in
`ℝ²_+` (so the nonnegativity constraint on the numeraire is irrelevant) iff `w ≥ p₂x̂₂`. -/
theorem exercise_3_D_4c_irrelevant {p₂ xh w : ℝ} (hxh : 0 ≤ xh) :
    (![w - p₂ * xh, xh] : Fin 2 → ℝ) ∈ nonnegOrthant 2 ↔ p₂ * xh ≤ w := by
  constructor
  · intro h
    have := h 0
    simp at this
    linarith
  · intro h l
    fin_cases l <;> simp <;> linarith

end MWG.ClassicalDemand
