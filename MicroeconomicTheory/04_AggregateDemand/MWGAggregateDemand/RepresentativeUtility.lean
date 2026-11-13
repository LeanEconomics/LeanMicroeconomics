/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGAggregateDemand.Representative
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
import Mathlib.Topology.Order.Compact

/-!
# Exercise 4.D.4(a): properties of the representative utility

MWG, Exercise 4.D.4(a) (p. 125). For `u(x) = sup {W(u₁(x₁), …, u_I(x_I)) : xᵢ ≥ 0, ∑ᵢ xᵢ ≤ x}`
(`repUtility`), with the supremum bounded:

* `exercise_4_D_4a_monotone`: `W` nondecreasing gives `u` nondecreasing (monotone);
* `exercise_4_D_4a_concave`: `W` nondecreasing and concave and every `uᵢ` concave give `u`
  concave, hence quasiconcave (`exercise_4_D_4a_quasiconcave`) and continuous on `ℝ^L_{++}`
  (`exercise_4_D_4a_continuous`).

* `exercise_4_D_4a_continuousOn`: `W` and the `uᵢ` continuous give `u` continuous on all of
  `ℝ^L_+`, boundary included (distributions are `θᵢ ⊙ x` with `θ` in the compact set
  `shareSimplex`, and a maximum over a compact set of a continuous function is continuous).
-/

namespace MWG.AggregateDemand

open MWG.ConsumerChoice MWG.ClassicalDemand
open scoped Pointwise

variable {L I : ℕ}

/-- The values `W(u₁(x₁), …)` over the bundle distributions of `x`. -/
def splitValues (W : SocialWelfareFunction I) (us : Fin I → (Fin L → ℝ) → ℝ) (x : Fin L → ℝ) :
    Set ℝ :=
  {t | ∃ ys : Fin I → Fin L → ℝ, (∀ i, ys i ∈ nonnegOrthant L) ∧ ∑ i, ys i ≤ x ∧
    t = W fun i => us i (ys i)}

theorem repUtility_eq (W : SocialWelfareFunction I) (us : Fin I → (Fin L → ℝ) → ℝ)
    (x : Fin L → ℝ) : repUtility W us x = sSup (splitValues W us x) := rfl

theorem splitValues_nonempty (W : SocialWelfareFunction I) (us : Fin I → (Fin L → ℝ) → ℝ)
    {x : Fin L → ℝ} (hx : x ∈ nonnegOrthant L) : (splitValues W us x).Nonempty :=
  ⟨_, fun _ => 0, fun _ _ => le_rfl, fun l => by simpa using hx l, rfl⟩

/-- **Exercise 4.D.4(a)** (MWG, p. 125). If `x ≤ x'` (and the supremum at `x'` is finite), every
distribution of `x` is a distribution of `x'`, so `u(x) ≤ u(x')`. -/
theorem exercise_4_D_4a_monotone (W : SocialWelfareFunction I) (us : Fin I → (Fin L → ℝ) → ℝ)
    {x x' : Fin L → ℝ} (hx : x ∈ nonnegOrthant L) (hxx : x ≤ x')
    (hb : BddAbove (splitValues W us x')) : repUtility W us x ≤ repUtility W us x' := by
  rw [repUtility_eq, repUtility_eq]
  apply csSup_le_csSup hb (splitValues_nonempty W us hx)
  rintro _ ⟨ys, hys, hsum, rfl⟩
  exact ⟨ys, hys, hsum.trans hxx, rfl⟩

/-- **Exercise 4.D.4(a)** (MWG, p. 125). If `W` is nondecreasing and concave, every `uᵢ` is
concave on `ℝ^L_+`, and the suprema are finite, then `u` is concave on `ℝ^L_+`. -/
theorem exercise_4_D_4a_concave {W : SocialWelfareFunction I} (hWm : Monotone W)
    (hWc : ConcaveOn ℝ Set.univ W) {us : Fin I → (Fin L → ℝ) → ℝ}
    (hui : ∀ i, ConcaveOn ℝ (nonnegOrthant L) (us i))
    (hbdd : ∀ x ∈ nonnegOrthant L, BddAbove (splitValues W us x)) :
    ConcaveOn ℝ (nonnegOrthant L) (repUtility W us) := by
  refine ⟨convex_nonnegOrthant L, fun x hx y hy a b ha hb hab => ?_⟩
  have hmix : a • x + b • y ∈ nonnegOrthant L := convex_nonnegOrthant L hx hy ha hb hab
  have hS : ∀ t ∈ a • splitValues W us x + b • splitValues W us y,
      t ≤ repUtility W us (a • x + b • y) := by
    rintro _ ⟨_, ⟨_, ⟨ys, hys, hsy, rfl⟩, rfl⟩, _, ⟨_, ⟨zs, hzs, hsz, rfl⟩, rfl⟩, rfl⟩
    have hsplit : (fun i => a • ys i + b • zs i) ∈ {ws : Fin I → Fin L → ℝ |
        (∀ i, ws i ∈ nonnegOrthant L) ∧ ∑ i, ws i ≤ a • x + b • y} := by
      refine ⟨fun i => convex_nonnegOrthant L (hys i) (hzs i) ha hb hab, ?_⟩
      rw [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum]
      intro l
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left (hsy l) ha)
        (mul_le_mul_of_nonneg_left (hsz l) hb)
    have h1 : (a • W fun i => us i (ys i)) + b • W (fun i => us i (zs i)) ≤
        W (a • (fun i => us i (ys i)) + b • fun i => us i (zs i)) :=
      hWc.2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab
    have h2 : W (a • (fun i => us i (ys i)) + b • fun i => us i (zs i)) ≤
        W fun i => us i (a • ys i + b • zs i) :=
      hWm fun i => (hui i).2 (hys i) (hzs i) ha hb hab
    have h3 : (W fun i => us i (a • ys i + b • zs i)) ≤ repUtility W us (a • x + b • y) :=
      le_csSup (hbdd _ hmix) ⟨_, hsplit.1, hsplit.2, rfl⟩
    simp only [smul_eq_mul] at h1 ⊢
    linarith
  have hne := ((splitValues_nonempty W us hx).smul_set (a := a)).add
    ((splitValues_nonempty W us hy).smul_set (a := b))
  have hle := csSup_le hne hS
  rw [csSup_add ((splitValues_nonempty W us hx).smul_set) ((hbdd x hx).smul_of_nonneg ha)
    ((splitValues_nonempty W us hy).smul_set) ((hbdd y hy).smul_of_nonneg hb),
    Real.sSup_smul_of_nonneg ha, Real.sSup_smul_of_nonneg hb] at hle
  exact hle

/-- **Exercise 4.D.4(a)** (MWG, p. 125). Under the hypotheses of `exercise_4_D_4a_concave`, `u`
is quasiconcave. -/
theorem exercise_4_D_4a_quasiconcave {W : SocialWelfareFunction I} (hWm : Monotone W)
    (hWc : ConcaveOn ℝ Set.univ W) {us : Fin I → (Fin L → ℝ) → ℝ}
    (hui : ∀ i, ConcaveOn ℝ (nonnegOrthant L) (us i))
    (hbdd : ∀ x ∈ nonnegOrthant L, BddAbove (splitValues W us x)) :
    QuasiconcaveOn ℝ (nonnegOrthant L) (repUtility W us) :=
  (exercise_4_D_4a_concave hWm hWc hui hbdd).quasiconcaveOn

/-- **Exercise 4.D.4(a)** (MWG, p. 125). Under the hypotheses of `exercise_4_D_4a_concave`, `u`
is continuous on the interior `ℝ^L_{++}` of the consumption set. -/
theorem exercise_4_D_4a_continuous {W : SocialWelfareFunction I} (hWm : Monotone W)
    (hWc : ConcaveOn ℝ Set.univ W) {us : Fin I → (Fin L → ℝ) → ℝ}
    (hui : ∀ i, ConcaveOn ℝ (nonnegOrthant L) (us i))
    (hbdd : ∀ x ∈ nonnegOrthant L, BddAbove (splitValues W us x)) :
    ContinuousOn (repUtility W us) (interior (nonnegOrthant L)) :=
  (exercise_4_D_4a_concave hWm hWc hui hbdd).continuousOn_interior

/-- The shares `θ` with `θᵢ ≥ 0` and `∑ᵢ θᵢ ≤ 1` (coordinatewise): every distribution of
`x ≥ 0` is `yᵢ = θᵢ ⊙ x` for such `θ`. -/
def shareSimplex (I L : ℕ) : Set (Fin I → Fin L → ℝ) :=
  {θ | (∀ i l, 0 ≤ θ i l) ∧ ∀ l, ∑ i, θ i l ≤ 1}

theorem isCompact_shareSimplex (I L : ℕ) : IsCompact (shareSimplex I L) := by
  apply (isCompact_Icc (a := (0 : Fin I → Fin L → ℝ)) (b := fun _ _ => 1)).of_isClosed_subset
  · have h1 : IsClosed {θ : Fin I → Fin L → ℝ | ∀ i l, 0 ≤ θ i l} := by
      have : {θ : Fin I → Fin L → ℝ | ∀ i l, 0 ≤ θ i l} =
          ⋂ i, ⋂ l, {θ : Fin I → Fin L → ℝ | 0 ≤ θ i l} := by
        ext θ; simp
      rw [this]
      exact isClosed_iInter fun i => isClosed_iInter fun l =>
        isClosed_le continuous_const ((continuous_apply l).comp (continuous_apply i))
    have h2 : IsClosed {θ : Fin I → Fin L → ℝ | ∀ l, ∑ i, θ i l ≤ 1} := by
      have : {θ : Fin I → Fin L → ℝ | ∀ l, ∑ i, θ i l ≤ 1} =
          ⋂ l, {θ : Fin I → Fin L → ℝ | ∑ i, θ i l ≤ 1} := by
        ext θ; simp
      rw [this]
      exact isClosed_iInter fun l => isClosed_le (continuous_finsetSum _ fun i _ =>
        (continuous_apply l).comp (continuous_apply i)) continuous_const
    exact h1.inter h2
  · rintro θ ⟨h0, h1⟩
    refine ⟨fun i l => h0 i l, fun i l => ?_⟩
    calc θ i l ≤ ∑ j, θ j l :=
          Finset.single_le_sum (f := fun j => θ j l) (fun j _ => h0 j l) (Finset.mem_univ i)
      _ ≤ 1 := h1 l

/-- The distributions of `x ≥ 0` are exactly `yᵢ = θᵢ ⊙ x`, `θ ∈ shareSimplex`. -/
theorem splitValues_eq_image (W : SocialWelfareFunction I) (us : Fin I → (Fin L → ℝ) → ℝ)
    {x : Fin L → ℝ} (hx : x ∈ nonnegOrthant L) :
    splitValues W us x = (fun θ : Fin I → Fin L → ℝ =>
      W fun i => us i fun l => max (θ i l) 0 * x l) '' shareSimplex I L := by
  ext t
  constructor
  · rintro ⟨ys, hys, hsum, rfl⟩
    have hle : ∀ i l, ys i l ≤ x l := fun i l => by
      have := hsum l
      simp only [Finset.sum_apply] at this
      exact (Finset.single_le_sum (f := fun j => ys j l) (fun j _ => hys j l)
        (Finset.mem_univ i)).trans this
    refine ⟨fun i l => if x l = 0 then 0 else ys i l / x l, ⟨fun i l => ?_, fun l => ?_⟩, ?_⟩
    · beta_reduce
      split_ifs with h
      · exact le_rfl
      · exact div_nonneg (hys i l) (hx l)
    · beta_reduce
      split_ifs with h
      · simp
      · have hxl : 0 < x l := lt_of_le_of_ne (hx l) (Ne.symm h)
        rw [← Finset.sum_div, div_le_one hxl]
        have := hsum l
        simpa only [Finset.sum_apply] using this
    · beta_reduce
      congr 1
      funext i
      congr 1
      funext l
      split_ifs with h
      · rw [max_self, zero_mul]
        exact le_antisymm (hys i l) (h ▸ hle i l)
      · have hxl : 0 < x l := lt_of_le_of_ne (hx l) (Ne.symm h)
        rw [max_eq_left (div_nonneg (hys i l) hxl.le), div_mul_cancel₀ _ hxl.ne']
  · rintro ⟨θ, ⟨h0, h1⟩, rfl⟩
    refine ⟨fun i l => max (θ i l) 0 * x l, fun i l => mul_nonneg (le_max_right _ _) (hx l),
      fun l => ?_, rfl⟩
    simp only [Finset.sum_apply]
    simp only [max_eq_left (h0 _ l)]
    rw [← Finset.sum_mul]
    exact mul_le_of_le_one_left (hx l) (h1 l)

/-- **Exercise 4.D.4(a)** (MWG, p. 125), continuity up to the boundary. If `W` is continuous and
every `uᵢ` is continuous on `ℝ^L_+`, then `u(x) = max {W(u₁(x₁), …) : xᵢ ≥ 0, ∑ᵢ xᵢ ≤ x}` is
continuous on all of `ℝ^L_+`, boundary included: writing the distributions as `xᵢ = θᵢ ⊙ x` with
`θ` in a fixed compact set, `u` is the maximum of a jointly continuous function over a compact
set. -/
theorem exercise_4_D_4a_continuousOn {W : SocialWelfareFunction I} (hWc : Continuous W)
    {us : Fin I → (Fin L → ℝ) → ℝ} (hui : ∀ i, ContinuousOn (us i) (nonnegOrthant L)) :
    ContinuousOn (repUtility W us) (nonnegOrthant L) := by
  set f : nonnegOrthant L → (Fin I → Fin L → ℝ) → ℝ := fun x θ =>
    W fun i => us i fun l => max (θ i l) 0 * (x : Fin L → ℝ) l with hf
  have hfc : Continuous (Function.uncurry f) := by
    apply hWc.comp
    refine continuous_pi fun i => ?_
    have hg : Continuous fun z : nonnegOrthant L × (Fin I → Fin L → ℝ) =>
        (fun l => max (z.2 i l) 0 * (z.1 : Fin L → ℝ) l : Fin L → ℝ) := by
      refine continuous_pi fun l => ?_
      exact (((continuous_apply l).comp ((continuous_apply i).comp continuous_snd)).max
        continuous_const).mul ((continuous_apply l).comp (continuous_subtype_val.comp
          continuous_fst))
    exact (hui i).comp_continuous hg fun z l => mul_nonneg (le_max_right _ _) (z.1.2 l)
  have hc := IsCompact.continuous_sSup (f := f) (isCompact_shareSimplex I L) hfc
  rw [continuousOn_iff_continuous_domRestrict]
  convert hc using 1
  funext x
  simp only [Set.domRestrict_apply, repUtility_eq, splitValues_eq_image W us x.2, f]

end MWG.AggregateDemand
