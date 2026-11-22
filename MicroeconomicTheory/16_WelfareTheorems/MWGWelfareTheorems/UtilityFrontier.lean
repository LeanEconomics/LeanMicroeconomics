/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGWelfareTheorems.SocialWelfare

/-!
# The boundary of the utility possibility set (MWG Exercise 16.E.1(b)-(c), p. 576)

* **Exercise 16.E.1(b)**: with `Xᵢ = ℝ^L₊` and continuous, strongly monotone utilities, the utility
  vector of a feasible allocation that is not Pareto optimal lies in the interior of `U`; hence a
  boundary point of `U` that belongs to `U'` is the utility vector only of Pareto optima. The
  hint's claim `U' = U ∩ ℝ^I₊` (for `uᵢ(0) = 0`, free disposal and `J ≥ 1`) is proved too. The
  book's further assumption `0 ∈ Yⱼ` is not needed.
* **Exercise 16.E.1(c)**: in a pure exchange economy with `Xᵢ = ℝ^L₊`, continuous (rational)
  preferences and `ω̄ ≫ 0`, no feasible allocation makes every consumer strictly better off than
  at a price quasiequilibrium with transfers. Local nonsatiation is not needed.
-/

namespace MWG.WelfareTheorems

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.Production Kreps.PreferenceProperties
open MWG.CompetitiveMarkets (Allocation)
open Filter Topology

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {L : ℕ}

/-- Strong monotonicity of a utility on `ℝ^L₊` gives weak monotonicity. -/
theorem utility_mono_of_strongMono {u : (Fin L → ℝ) → ℝ}
    (h : PrefStronglyMonotone (nonnegOrthant L) (utilityPref u)) {x y : Fin L → ℝ}
    (hx : x ∈ nonnegOrthant L) (hxy : x ≤ y) : u x ≤ u y := by
  by_cases heq : y = x
  · rw [heq]
  · exact (h x hx y (fun l => (hx l).trans (hxy l)) hxy heq).1

/-- **Exercise 16.E.1(b)** (MWG, p. 576). With `Xᵢ = ℝ^L₊` and utilities that are continuous and
strongly monotone on `ℝ^L₊`, if a feasible allocation is not Pareto optimal, its utility vector is
in the interior of the utility possibility set `U`. -/
theorem exercise_16_E_1b_interior {u : ι → (Fin L → ℝ) → ℝ} {Y : κ → Set (Fin L → ℝ)}
    {ω : Fin L → ℝ} (hcont : ∀ i, ContinuousOn (u i) (nonnegOrthant L))
    (hmono : ∀ i, PrefStronglyMonotone (nonnegOrthant L) (utilityPref (u i)))
    {a : Allocation ι κ L}
    (ha : (PrefEconomy.ofUtility (fun _ => nonnegOrthant L) u Y ω).IsFeasible a)
    (hno : ¬ (PrefEconomy.ofUtility (fun _ => nonnegOrthant L) u Y ω).IsParetoOptimal a) :
    (fun i => u i (a.x i)) ∈
      interior (utilityPossibilitySet (PrefEconomy.ofUtility (fun _ => nonnegOrthant L) u Y ω)
        u) := by
  classical
  have hno' := hno
  simp only [PrefEconomy.IsParetoOptimal, not_and, not_not] at hno'
  obtain ⟨a', ⟨⟨hx', hy'⟩, hc'⟩, hle, k, hk⟩ := hno' ha
  have hle' : ∀ i, u i (a.x i) ≤ u i (a'.x i) := hle
  have hlt : u k (a.x k) < u k (a'.x k) := not_le.mp hk.2
  have hxX : ∀ i, a.x i ∈ nonnegOrthant L := ha.1.1
  have hx'X : ∀ i, a'.x i ∈ nonnegOrthant L := hx'
  -- consumer `k` holds some good in positive quantity
  obtain ⟨l, hl⟩ : ∃ l, 0 < a'.x k l := by
    by_contra hall
    push Not at hall
    have h0 : a'.x k = 0 := funext fun l => le_antisymm (hall l) (hx'X k l)
    have := utility_mono_of_strongMono (hmono k) (x := 0) (y := a.x k) (fun _ => le_rfl)
      (fun l => hxX k l)
    rw [h0] at hlt
    linarith
  obtain ⟨δ, hδ, hmem, hs⟩ := exists_strict_sub_single (rationalOn_utilityPref _ (u k))
    (prefContinuous_utilityPref (hcont k)) (hx'X k) (hxX k) hk hl
  have hδlt : u k (a.x k) < u k (a'.x k - Pi.single l δ) := not_le.mp hs.2
  set n : ℝ := ((Fintype.card ι : ℕ) : ℝ) with hn
  have hn0 : 0 < n := by
    rw [hn]; exact_mod_cast Fintype.card_pos_iff.mpr ⟨k⟩
  set g : Fin L → ℝ := Pi.single l (δ / n) with hg
  have hg0 : ∀ m, 0 ≤ g m := fun m => by
    by_cases hm : m = l
    · subst hm; rw [hg, Pi.single_eq_same]; positivity
    · simp [hg, hm]
  set x'' : ι → Fin L → ℝ := fun i => a'.x i + g - if i = k then Pi.single l δ else 0 with hx''
  have hx''X : ∀ i, x'' i ∈ nonnegOrthant L := by
    intro i m
    by_cases hik : i = k
    · subst hik
      simp only [hx'', ↓reduceIte, Pi.sub_apply, Pi.add_apply]
      have h1 := hmem m
      simp only [Pi.sub_apply] at h1
      linarith [hg0 m]
    · simp only [hx'', hik, ↓reduceIte, Pi.sub_apply, Pi.add_apply, Pi.zero_apply, sub_zero]
      linarith [hg0 m, hx'X i m]
  have hbetter : ∀ i, u i (a.x i) < u i (x'' i) := by
    intro i
    by_cases hik : i = k
    · subst hik
      refine lt_of_lt_of_le hδlt (utility_mono_of_strongMono (hmono i) hmem fun m => ?_)
      simp only [hx'', ↓reduceIte, Pi.sub_apply, Pi.add_apply]
      linarith [hg0 m]
    · have hge : a'.x i ≤ x'' i := fun m => by
        simp only [hx'', hik, ↓reduceIte, Pi.sub_apply, Pi.add_apply, Pi.zero_apply, sub_zero]
        linarith [hg0 m]
      have hne : x'' i ≠ a'.x i := by
        intro heq
        have := congrFun heq l
        simp only [hx'', hik, ↓reduceIte, Pi.sub_apply, Pi.add_apply, Pi.zero_apply, sub_zero,
          hg, Pi.single_eq_same] at this
        have : 0 < δ / n := div_pos hδ hn0
        linarith
      exact lt_of_le_of_lt (hle' i) (not_le.mp (hmono i _ (hx'X i) _ (hx''X i) hge hne).2)
  have hcg : (Fintype.card ι) • g = Pi.single l δ := by
    funext m
    by_cases hm : m = l
    · subst hm
      simp only [hg, Pi.smul_apply, Pi.single_eq_same, nsmul_eq_mul]
      rw [hn] at hn0 ⊢
      field_simp
    · simp [hg, hm]
  have hsum : ∑ i, x'' i = ∑ i, a'.x i := by
    simp only [hx'', Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, hcg, add_sub_cancel_right]
  have hfeas : (PrefEconomy.ofUtility (fun _ => nonnegOrthant L) u Y ω).IsFeasible
      ⟨x'', a'.y⟩ := ⟨⟨hx''X, hy'⟩, hsum.trans hc'⟩
  set O : Set (ι → ℝ) := {w | ∀ i, w i < u i (x'' i)} with hO
  have hOopen : IsOpen O := by
    have : O = ⋂ i, {w : ι → ℝ | w i < u i (x'' i)} := by ext w; simp [hO]
    rw [this]
    exact isOpen_iInter_of_finite fun i => isOpen_lt (continuous_apply i) continuous_const
  refine interior_maximal ?_ hOopen hbetter
  intro w hw
  exact ⟨⟨x'', a'.y⟩, hfeas, fun i => (hw i).le⟩

/-- **Exercise 16.E.1(b)** (MWG, p. 576). Under the assumptions of `exercise_16_E_1b_interior`,
every feasible allocation whose utility vector is a boundary point of `U` (in `U'` by
construction) is Pareto optimal. -/
theorem exercise_16_E_1b {u : ι → (Fin L → ℝ) → ℝ} {Y : κ → Set (Fin L → ℝ)}
    {ω : Fin L → ℝ} (hcont : ∀ i, ContinuousOn (u i) (nonnegOrthant L))
    (hmono : ∀ i, PrefStronglyMonotone (nonnegOrthant L) (utilityPref (u i)))
    {a : Allocation ι κ L}
    (ha : (PrefEconomy.ofUtility (fun _ => nonnegOrthant L) u Y ω).IsFeasible a)
    (hb : (fun i => u i (a.x i)) ∈
      frontier (utilityPossibilitySet (PrefEconomy.ofUtility (fun _ => nonnegOrthant L) u Y ω)
        u)) :
    (PrefEconomy.ofUtility (fun _ => nonnegOrthant L) u Y ω).IsParetoOptimal a := by
  by_contra hno
  exact hb.2 (exercise_16_E_1b_interior hcont hmono ha hno)

/-- **Exercise 16.E.1(b)**, hint (MWG, p. 576). With `Xᵢ = ℝ^L₊`, continuous strongly monotone
utilities normalized by `uᵢ(0) = 0`, free disposal in every `Yⱼ` and at least one firm,
`U' = U ∩ ℝ^I₊`. -/
theorem exercise_16_E_1b_hint [Nonempty κ] {u : ι → (Fin L → ℝ) → ℝ}
    {Y : κ → Set (Fin L → ℝ)} {ω : Fin L → ℝ}
    (hcont : ∀ i, ContinuousOn (u i) (nonnegOrthant L))
    (hmono : ∀ i, PrefStronglyMonotone (nonnegOrthant L) (utilityPref (u i)))
    (hu0 : ∀ i, u i 0 = 0)
    (hfd : ∀ j, ∀ y ∈ Y j, ∀ d ∈ nonnegOrthant L, y - d ∈ Y j) :
    achievedUtilitySet (PrefEconomy.ofUtility (fun _ => nonnegOrthant L) u Y ω) u =
      utilityPossibilitySet (PrefEconomy.ofUtility (fun _ => nonnegOrthant L) u Y ω) u ∩
        {v | ∀ i, 0 ≤ v i} := by
  classical
  ext v
  constructor
  · rintro ⟨a, ha, hv⟩
    refine ⟨⟨a, ha, fun i => (hv i).le⟩, fun i => ?_⟩
    rw [hv i, ← hu0 i]
    exact utility_mono_of_strongMono (hmono i) (x := 0) (fun _ => le_rfl) (fun l => ha.1.1 i l)
  · rintro ⟨⟨a, ha, hv⟩, hv0⟩
    have hxX : ∀ i, a.x i ∈ nonnegOrthant L := ha.1.1
    -- scale every bundle down to the exact utility level
    have hscale : ∀ i, ∃ t ∈ Set.Icc (0 : ℝ) 1, u i (t • a.x i) = v i := by
      intro i
      have hc : ContinuousOn (fun t : ℝ => u i (t • a.x i)) (Set.Icc 0 1) :=
        (hcont i).comp (continuous_id.smul continuous_const).continuousOn fun t ht l => by
          simp only [Pi.smul_apply, smul_eq_mul]
          exact mul_nonneg ht.1 (hxX i l)
      have hivt := intermediate_value_Icc (zero_le_one' ℝ) hc
      have hmemI : v i ∈ Set.Icc (u i ((0 : ℝ) • a.x i)) (u i ((1 : ℝ) • a.x i)) := by
        rw [zero_smul, one_smul, hu0]
        exact ⟨hv0 i, hv i⟩
      obtain ⟨t, ht, htv⟩ := hivt hmemI
      exact ⟨t, ht, htv⟩
    choose t ht htv using hscale
    set x' : ι → Fin L → ℝ := fun i => t i • a.x i with hx'
    set D : Fin L → ℝ := ∑ i, (a.x i - x' i) with hD
    have hD0 : D ∈ nonnegOrthant L := fun l => by
      simp only [hD, Finset.sum_apply, Pi.sub_apply, hx', Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_nonneg fun i _ => by nlinarith [(ht i).2, hxX i l]
    obtain ⟨j₀⟩ := ‹Nonempty κ›
    set y' : κ → Fin L → ℝ := fun j => if j = j₀ then a.y j - D else a.y j with hy'
    refine ⟨⟨x', y'⟩, ⟨⟨fun i l => ?_, fun j => ?_⟩, ?_⟩, fun i => (htv i).symm⟩
    · simp only [hx', Pi.smul_apply, smul_eq_mul]
      exact mul_nonneg (ht i).1 (hxX i l)
    · by_cases hj : j = j₀
      · subst hj
        simp only [hy', ↓reduceIte]
        exact hfd j _ (ha.1.2 j) D hD0
      · simp only [hy', hj, ↓reduceIte]
        exact ha.1.2 j
    · change ∑ i, x' i = ω + ∑ j, y' j
      have h1 : ∑ i, x' i = ∑ i, a.x i - D := by
        rw [hD, Finset.sum_sub_distrib, sub_sub_cancel]
      have h2 : ∑ j, y' j = ∑ j, a.y j - D := by
        rw [Finset.sum_congr rfl fun j _ => (show y' j = a.y j - if j = j₀ then D else 0 by
          by_cases hj : j = j₀ <;> simp [hy', hj]), Finset.sum_sub_distrib,
          Finset.sum_ite_eq' Finset.univ j₀ (fun _ => D)]
        simp
      have hc : ∑ i, a.x i = ω + ∑ j, a.y j := ha.2
      rw [h1, h2, hc, add_sub_assoc]

/-- **Exercise 16.E.1(c)** (MWG, p. 576). In a pure exchange economy (`J ≥ 1`, `I ≥ 1`) with
`Xᵢ = ℝ^L₊`, rational continuous preferences and `ω̄ ≫ 0`, no feasible allocation makes every
consumer strictly better off than at a price quasiequilibrium with transfers (the utility vector
of the quasiequilibrium is not interior to `U`). Some consumer has `wᵢ > 0` and then Proposition
16.D.2 applies to her. -/
theorem exercise_16_E_1c [Nonempty ι] [Nonempty κ] {E : PrefEconomy ι κ L}
    (hpe : E.IsPureExchange) (hX : ∀ i, E.X i = nonnegOrthant L)
    (hr : ∀ i, RationalOn (E.X i) (E.pref i)) (hc : ∀ i, PrefContinuous (E.X i) (E.pref i))
    (hω : ∀ l, 0 < E.ω l) {a : Allocation ι κ L} {p : Fin L → ℝ} {w : ι → ℝ}
    (h : E.IsPriceQuasiEqmWithTransfers a p w) :
    ¬ ∃ a', E.IsFeasible a' ∧ ∀ i, Strict (E.pref i) (a'.x i) (a.x i) := by
  rintro ⟨a', ⟨⟨hx', hy'⟩, hc'⟩, hs⟩
  obtain ⟨j₀⟩ := ‹Nonempty κ›
  have hp : ∀ l, 0 ≤ p l := footnote_9 (hpe j₀ ▸ h.2.2.1 j₀)
  have hprof : ∀ j, p ⬝ᵥ a.y j = 0 := fun j => by
    have hmax := hpe j ▸ h.2.2.1 j
    have h1 := hmax.2 0 (fun _ => le_rfl)
    rw [dotProduct_zero] at h1
    have h2 : p ⬝ᵥ a.y j ≤ 0 :=
      Finset.sum_nonpos fun l _ => mul_nonpos_of_nonneg_of_nonpos (hp l) (hmax.1 l)
    linarith
  have hsumw : ∑ i, w i = p ⬝ᵥ E.ω := by
    rw [h.2.1, Finset.sum_eq_zero fun j _ => hprof j, add_zero]
  have hpos : 0 < p ⬝ᵥ E.ω := dotProduct_pos_of_nonneg_ne_zero hp h.1 hω
  obtain ⟨i₁, hi₁⟩ : ∃ i, 0 < w i := by
    by_contra hall
    push Not at hall
    have := Finset.sum_nonpos fun i (_ : i ∈ Finset.univ) => hall i
    linarith
  have hgt : w i₁ < p ⬝ᵥ a'.x i₁ :=
    proposition_16_D_2 (hX i₁ ▸ convex_nonnegOrthant L) (hr i₁) (hc i₁) (h.2.2.2.1 i₁).1
      (h.2.2.2.1 i₁).2 (x' := 0) (by rw [hX i₁]; exact fun _ => le_rfl)
      (by rw [dotProduct_zero]; exact hi₁) _ (hx' i₁) (hs i₁)
  have hge : ∀ i, w i ≤ p ⬝ᵥ a'.x i := fun i => (h.2.2.2.1 i).2 _ (hx' i) (hs i)
  have h1 : ∑ i, w i < ∑ i, p ⬝ᵥ a'.x i :=
    Finset.sum_lt_sum (fun i _ => hge i) ⟨i₁, Finset.mem_univ _, hgt⟩
  have h2 : ∑ i, p ⬝ᵥ a'.x i ≤ p ⬝ᵥ E.ω := by
    rw [← dotProduct_finset_sum, hc', dotProduct_add, dotProduct_finset_sum]
    have : ∑ j, p ⬝ᵥ a'.y j ≤ 0 := Finset.sum_nonpos fun j _ =>
      Finset.sum_nonpos fun l _ => mul_nonpos_of_nonneg_of_nonpos (hp l)
        ((hpe j ▸ hy' j : a'.y j ∈ nonposOrthant L) l)
    linarith
  linarith

end MWG.WelfareTheorems
