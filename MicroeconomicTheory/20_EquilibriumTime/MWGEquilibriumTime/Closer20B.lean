/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGEquilibriumTime.Closer20G
import Mathlib.Topology.Order.IntermediateValue

/-!
# The additive form is cardinal: uniqueness (MWG Exercise 20.B.5, p. 783)

MWG, Chapter 20, Exercise 20.B.5: "Show also that the additively separable form of `V(·)` is a
cardinal property." The module `Utility` proves that positive affine transformations of `u`
preserve the form and that an ordinal transformation can destroy it. Here is the uniqueness
half: if `V(c) = ∑_t δ^t u(c_t)` and `W(c) = ∑_t δ^t w(c_t)` (one good, the same discount
factor `0 < δ < 1`, `u` and `w` continuous on `ℝ_+`, `u` strictly increasing) rank nonnegative
bounded streams in the same way, then `w = α u + β` on `ℝ_+` with `α > 0`
(`exercise_20_B_5_unique`).

Proof. Streams `(x, y, 0, 0, ...)` and `(z, z, 0, 0, ...)` are indifferent under `V` exactly when
`(1 + δ) u(z) = u(x) + δ u(y)`; so under `W` too, and `w` satisfies the weighted Jensen equation
with weight `λ = 1/(1 + δ)` in the `u`-scale (`additive_jensen`). A continuous solution of that
equation is affine in `u` on every interval: the set where `w` agrees with the affine
interpolation is closed, and the intermediate value theorem puts a point of it into every gap
(`affine_of_weighted_jensen`).
-/

namespace MWG.EquilibriumTime

/-- The one-good stream `(x, y, 0, 0, ...)`. -/
def twoDateStream (x y : ℝ) : ℕ → Fin 1 → ℝ :=
  fun t => if t = 0 then fun _ => x else if t = 1 then fun _ => y else 0

/-- Discounted utility of `(x, y, 0, 0, ...)`: that of the zero stream `(0, 0, 0, ...)` plus
`(u(x) - u(0)) + δ (u(y) - u(0))`. -/
theorem twoDate_value {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (u : ℝ → ℝ) (x y : ℝ) :
    discountedUtility δ (fun z => u (z 0)) (twoDateStream x y)
      = discountedUtility δ (fun z => u (z 0)) (twoDateStream 0 0) + (u x - u 0)
        + δ * (u y - u 0) := by
  have hs : Summable fun t => δ ^ t * (fun z : Fin 1 → ℝ => u (z 0)) (twoDateStream 0 0 t) :=
    ((summable_geometric_of_lt_one hδ0 hδ1).mul_right (u 0)).congr fun t => by
      simp only [twoDateStream]
      split_ifs <;> simp
  have hcc : ∀ τ, 2 ≤ τ → twoDateStream x y τ = twoDateStream 0 0 τ := fun τ hτ => by
    simp only [twoDateStream, show τ ≠ 0 by omega, show τ ≠ 1 by omega, ↓reduceIte]
  have := (discountedUtility_finite_change (u := fun z : Fin 1 → ℝ => u (z 0)) hcc hs).2
  have hsum : ∑ τ ∈ Finset.range 2, δ ^ τ * ((fun z : Fin 1 → ℝ => u (z 0))
      (twoDateStream x y τ) - (fun z : Fin 1 → ℝ => u (z 0)) (twoDateStream 0 0 τ))
      = (u x - u 0) + δ * (u y - u 0) := by
    simp [Finset.sum_range_succ, twoDateStream]
  rw [this, hsum]
  ring

/-- The two-date streams are nonnegative and bounded. -/
theorem twoDate_props {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    NonnegStream (twoDateStream x y) ∧ BoundedStream (twoDateStream x y) := by
  refine ⟨fun t i => ?_, ⟨max x y, fun t i => ?_⟩⟩
  · simp only [twoDateStream, Pi.zero_apply]
    split_ifs <;> simp [hx, hy]
  · simp only [twoDateStream]
    split_ifs
    · rw [abs_of_nonneg hx]; exact le_max_left _ _
    · rw [abs_of_nonneg hy]; exact le_max_right _ _
    · simp [le_max_of_le_left hx]

/-- Two additive utilities `V`, `W` with the same discount factor that rank nonnegative bounded
one-good streams alike. -/
def SameRanking (δ : ℝ) (u w : ℝ → ℝ) : Prop :=
  ∀ c c' : ℕ → Fin 1 → ℝ, NonnegStream c → NonnegStream c' → BoundedStream c →
    BoundedStream c' →
    (discountedUtility δ (fun z => u (z 0)) c ≤ discountedUtility δ (fun z => u (z 0)) c' ↔
      discountedUtility δ (fun z => w (z 0)) c ≤ discountedUtility δ (fun z => w (z 0)) c')

/-- A proved instance of `SameRanking`: `w = 2u + 3`. -/
theorem sameRanking_affine {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) {u : ℝ → ℝ} {M : ℝ}
    (hM : ∀ x, 0 ≤ x → |u x| ≤ M) : SameRanking δ u (fun x => 2 * u x + 3) := by
  intro c c' hc hc' _ _
  have hs : ∀ d : ℕ → Fin 1 → ℝ, NonnegStream d →
      Summable fun t => δ ^ t * (fun z : Fin 1 → ℝ => u (z 0)) (d t) :=
    fun d hd => summable_discounted hδ0 hδ1 (fun t => hM _ (hd t 0))
  exact (exercise_20_B_5_affine (u := fun z : Fin 1 → ℝ => u (z 0)) (a := 2) (b := 3) hδ0 hδ1
    two_pos (hs c' hc') (hs c hc)).symm

/-- Indifference transfers: if `(1 + δ) u(z) = u(x) + δ u(y)` then
`(1 + δ) w(z) = w(x) + δ w(y)`, for `x, y, z ≥ 0`. -/
theorem additive_jensen {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) {u w : ℝ → ℝ}
    (hrep : SameRanking δ u w) {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (h : (1 + δ) * u z = u x + δ * u y) : (1 + δ) * w z = w x + δ * w y := by
  obtain ⟨n1, b1⟩ := twoDate_props hx hy
  obtain ⟨n2, b2⟩ := twoDate_props hz hz
  have hV : discountedUtility δ (fun z => u (z 0)) (twoDateStream x y)
      = discountedUtility δ (fun z => u (z 0)) (twoDateStream z z) := by
    rw [twoDate_value hδ0 hδ1 u x y, twoDate_value hδ0 hδ1 u z z]; linarith
  have h1 := (hrep _ _ n1 n2 b1 b2).1 hV.le
  have h2 := (hrep _ _ n2 n1 b2 b1).1 hV.ge
  rw [twoDate_value hδ0 hδ1 w x y, twoDate_value hδ0 hδ1 w z z] at h1 h2
  linarith

/-- A function `w` that is continuous on `[a, b]` and satisfies the weighted Jensen equation in
the scale of a continuous strictly increasing `u` (`u(z) = λ u(x) + (1 - λ) u(y)` implies
`w(z) = λ w(x) + (1 - λ) w(y)`, `0 < λ < 1`) is affine in `u` on `[a, b]`. -/
theorem affine_of_weighted_jensen {u w : ℝ → ℝ} {a b lam : ℝ} (hab : a < b) (hlam0 : 0 < lam)
    (hlam1 : lam < 1) (hu : ContinuousOn u (Set.Icc a b)) (hw : ContinuousOn w (Set.Icc a b))
    (hmono : StrictMonoOn u (Set.Icc a b))
    (hj : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, ∀ z ∈ Set.Icc a b,
      u z = lam * u x + (1 - lam) * u y → w z = lam * w x + (1 - lam) * w y) :
    ∀ x ∈ Set.Icc a b, w x = w a + (w b - w a) / (u b - u a) * (u x - u a) := by
  have hua : u a < u b := hmono (Set.left_mem_Icc.2 hab.le) (Set.right_mem_Icc.2 hab.le) hab
  set K := (w b - w a) / (u b - u a) with hK
  set f : ℝ → ℝ := fun x => w x - (w a + K * (u x - u a)) with hf
  have hfc : ContinuousOn f (Set.Icc a b) :=
    hw.sub (continuousOn_const.add (continuousOn_const.mul (hu.sub continuousOn_const)))
  have hfa : f a = 0 := by simp [hf]
  have hfb : f b = 0 := by
    simp only [hf, hK]
    rw [div_mul_cancel₀ _ (sub_ne_zero.2 hua.ne')]
    ring
  have hfj : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, ∀ z ∈ Set.Icc a b,
      u z = lam * u x + (1 - lam) * u y → f z = lam * f x + (1 - lam) * f y := by
    intro x hx y hy z hz huz
    simp only [hf]
    rw [hj x hx y hy z hz huz, huz]
    ring
  intro z0 hz0
  by_contra hne
  have hne' : f z0 ≠ 0 := fun h => hne (by simp only [hf] at h; linarith)
  -- the last zero of `f` below `z0` and the first one above
  set S1 := Set.Icc a z0 ∩ f ⁻¹' {0} with hS1
  set S2 := Set.Icc z0 b ∩ f ⁻¹' {0} with hS2
  have hS1c : IsClosed S1 :=
    (hfc.mono (Set.Icc_subset_Icc le_rfl hz0.2)).preimage_isClosed_of_isClosed
      isClosed_Icc isClosed_singleton
  have hS2c : IsClosed S2 :=
    (hfc.mono (Set.Icc_subset_Icc hz0.1 le_rfl)).preimage_isClosed_of_isClosed
      isClosed_Icc isClosed_singleton
  have hS1n : S1.Nonempty := ⟨a, ⟨le_rfl, hz0.1⟩, hfa⟩
  have hS2n : S2.Nonempty := ⟨b, ⟨hz0.2, le_rfl⟩, hfb⟩
  have hS1b : BddAbove S1 := ⟨z0, fun x hx => hx.1.2⟩
  have hS2b : BddBelow S2 := ⟨z0, fun x hx => hx.1.1⟩
  set c := sSup S1 with hc
  set d := sInf S2 with hd
  have hcS : c ∈ S1 := hS1c.csSup_mem hS1n hS1b
  have hdS : d ∈ S2 := hS2c.csInf_mem hS2n hS2b
  have hcz : c < z0 := lt_of_le_of_ne hcS.1.2 fun h => hne' (h ▸ hcS.2)
  have hzd : z0 < d := lt_of_le_of_ne hdS.1.1 fun h => hne' (h.symm ▸ hdS.2)
  have hcab : c ∈ Set.Icc a b := ⟨hcS.1.1, hcS.1.2.trans hz0.2⟩
  have hdab : d ∈ Set.Icc a b := ⟨hz0.1.trans hdS.1.1, hdS.1.2⟩
  have hucd : u c < u d := hmono hcab hdab (hcz.trans hzd)
  -- a point of the gap where `f` vanishes
  have hsub : Set.Icc c d ⊆ Set.Icc a b := Set.Icc_subset_Icc hcab.1 hdab.2
  obtain ⟨m, hm, hum⟩ := intermediate_value_Icc (hcz.trans hzd).le (hu.mono hsub)
    (show lam * u c + (1 - lam) * u d ∈ Set.Icc (u c) (u d) by
      constructor <;> nlinarith)
  have hmc : c < m := lt_of_le_of_ne hm.1 fun h => by
    rw [← h] at hum; nlinarith
  have hmd : m < d := lt_of_le_of_ne hm.2 fun h => by
    rw [h] at hum; nlinarith
  have hfm : f m = 0 := by
    rw [hfj c hcab d hdab m (hsub hm) hum, hcS.2, hdS.2]; ring
  rcases le_total m z0 with hmz | hmz
  · have : m ≤ c := le_csSup hS1b ⟨⟨(hsub hm).1, hmz⟩, hfm⟩
    linarith
  · have : d ≤ m := csInf_le hS2b ⟨⟨hmz, (hsub hm).2⟩, hfm⟩
    linarith

/-- **Exercise 20.B.5**, uniqueness (MWG, p. 783): the additive form is cardinal. If
`V(c) = ∑_t δ^t u(c_t)` and `W(c) = ∑_t δ^t w(c_t)` rank nonnegative bounded one-good streams
alike, with `0 < δ < 1`, `u` and `w` continuous on `ℝ_+` and `u` strictly increasing, then
`w = α u + β` on `ℝ_+` for some `α > 0`. -/
theorem exercise_20_B_5_unique {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) {u w : ℝ → ℝ}
    (hu : ContinuousOn u (Set.Ici 0)) (hw : ContinuousOn w (Set.Ici 0))
    (hmono : StrictMonoOn u (Set.Ici 0)) (hrep : SameRanking δ u w) :
    ∃ α : ℝ, 0 < α ∧ ∃ β : ℝ, ∀ x, 0 ≤ x → w x = α * u x + β := by
  set lam := 1 / (1 + δ) with hlam
  have hlam0 : 0 < lam := by rw [hlam]; positivity
  have hlam1 : lam < 1 := by rw [hlam, div_lt_one (by linarith)]; linarith
  have hj : ∀ x, 0 ≤ x → ∀ y, 0 ≤ y → ∀ z, 0 ≤ z →
      u z = lam * u x + (1 - lam) * u y → w z = lam * w x + (1 - lam) * w y := by
    intro x hx y hy z hz h
    have h' : (1 + δ) * u z = u x + δ * u y := by
      rw [h, hlam]; field_simp; ring
    have := additive_jensen hδ0.le hδ1 hrep hx hy hz h'
    rw [hlam]; field_simp; linarith
  have hu01 : u 0 < u 1 := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 zero_le_one) one_pos
  -- `w` is strictly increasing between `0` and `1`
  have hw01 : w 0 < w 1 := by
    obtain ⟨n0, b0⟩ := twoDate_props (le_refl (0 : ℝ)) (le_refl (0 : ℝ))
    obtain ⟨n1, b1⟩ := twoDate_props zero_le_one (le_refl (0 : ℝ))
    have hV : ¬ discountedUtility δ (fun z => u (z 0)) (twoDateStream 1 0)
        ≤ discountedUtility δ (fun z => u (z 0)) (twoDateStream 0 0) := by
      rw [twoDate_value hδ0.le hδ1 u 1 0]; linarith
    have hW := mt (hrep _ _ n1 n0 b1 b0).2 hV
    rw [twoDate_value hδ0.le hδ1 w 1 0] at hW
    linarith
  set α := (w 1 - w 0) / (u 1 - u 0) with hα
  refine ⟨α, div_pos (by linarith) (by linarith), w 0 - α * u 0, fun x hx => ?_⟩
  set b := max x 1 with hb
  have hb1 : 1 ≤ b := le_max_right _ _
  have hsub : Set.Icc 0 b ⊆ Set.Ici 0 := fun z hz => Set.mem_Ici.2 hz.1
  have haff := affine_of_weighted_jensen (by linarith : (0 : ℝ) < b) hlam0 hlam1 (hu.mono hsub)
    (hw.mono hsub) (hmono.mono hsub) (fun x hx y hy z hz => hj x hx.1 y hy.1 z hz.1)
  have h1 := haff 1 ⟨zero_le_one, hb1⟩
  have hx' := haff x ⟨hx, le_max_left _ _⟩
  set K := (w b - w 0) / (u b - u 0) with hK
  have hKα : K = α := by
    rw [hα, eq_div_iff (by linarith)]; linarith
  rw [hx', hKα]; ring

end MWG.EquilibriumTime
