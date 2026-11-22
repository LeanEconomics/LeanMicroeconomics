/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGWelfareTheorems.FritzJohn

/-!
# First-order conditions for Pareto optimality (MWG Section 16.F, pp. 561-566)

The setting of Section 16.F: `Xᵢ = ℝ^L₊`, utilities `uᵢ` with `∇uᵢ ≫ 0`, `uᵢ(0) = 0`, production
sets `Yⱼ = {y : Fⱼ(y) ≤ 0}` with `∇Fⱼ ≫ 0` and `Fⱼ(0) ≤ 0`. Departure: the book takes the `uᵢ`
twice continuously differentiable on `ℝ^L₊`; we take functions on `ℝ^L` and assume exactly the
differentiability each statement uses (often only at the allocation in question).

* With `∇u ≫ 0` everywhere, `u` is strongly monotone (p. 562), and with `∇F ≫ 0` the set
  `{F ≤ 0}` has free disposal (footnote 17).
* Problem (16.F.1) (`Problem16F1`); **Exercise 16.F.1**: its solutions are Pareto optimal, and
  every Pareto optimum solves it for the utility levels it gives (with continuous, strongly
  monotone utilities and `J ≥ 1`).
* **Exercise 16.F.2**: the Kuhn-Tucker conditions (16.F.2)-(16.F.3), with `δ₁ = 1`, at every
  solution of (16.F.1) (`J ≥ 1`, `L ≥ 1`), derived from the Fritz John conditions; footnote 18's
  constraint qualification claim is replaced by a direct argument covering solutions with
  `x₁ = 0`.
* **Exercise 16.F.3**: at interior solutions, (16.F.2)-(16.F.3) give (16.F.4)-(16.F.6).
* The correspondences of (16.F.2)-(16.F.3) with (16.F.10)-(16.F.11) and (16.F.13)-(16.F.14).
* p. 565: with quasiconcave `uᵢ` and convex `Fⱼ`, the first-order conditions make the allocation a
  price equilibrium with transfers at `p = μ` (and conversely by the first welfare theorem).
* **Proposition 16.F.1**: with concave `uᵢ` and convex `Fⱼ`, every Pareto optimum maximizes
  `∑ᵢ λᵢ uᵢ(xᵢ)` subject to the resource and technology constraints, with `λᵢ = δᵢ` the reciprocal
  of `i`'s marginal utility of wealth at the supporting prices (when `δᵢ > 0`; `δᵢ = 0` only for
  consumers with `xᵢ = 0`).
-/

namespace MWG.WelfareTheorems

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.Production Kreps.PreferenceProperties
open MWG.CompetitiveMarkets (Allocation)
open Filter Topology

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {L : ℕ}

/-- A linear functional on `ℝ^L` applied to `d` is `∑ₗ dₗ ∂ₗ`. -/
theorem clm_apply_eq_sum_partials (φ : (Fin L → ℝ) →L[ℝ] ℝ) (d : Fin L → ℝ) :
    φ d = ∑ l, φ (Pi.single l 1) * d l :=
  strongDual_apply_eq_sum φ d

/-- A positive gradient gives a positive derivative in every direction `d ≥ 0`, `d ≠ 0`. -/
theorem clm_pos_of_partials_pos {φ : (Fin L → ℝ) →L[ℝ] ℝ} (hφ : ∀ l, 0 < φ (Pi.single l 1))
    {d : Fin L → ℝ} (hd : ∀ l, 0 ≤ d l) (hne : d ≠ 0) : 0 < φ d := by
  rw [clm_apply_eq_sum_partials]
  obtain ⟨l, hl⟩ : ∃ l, d l ≠ 0 := by
    by_contra h; push Not at h; exact hne (funext h)
  exact lt_of_lt_of_le (mul_pos (hφ l) (lt_of_le_of_ne (hd l) (Ne.symm hl)))
    (Finset.single_le_sum (f := fun k => φ (Pi.single k 1) * d k)
      (fun k _ => mul_nonneg (hφ k).le (hd k)) (Finset.mem_univ l))

/-- **Section 16.F** (MWG, p. 562). A function on `ℝ^L` with `∇u ≫ 0` everywhere is strictly
increasing: `x ≤ y`, `x ≠ y` imply `u(x) < u(y)` (hence the preference is strongly monotone). -/
theorem strictMono_of_grad_pos {u : (Fin L → ℝ) → ℝ} {u' : (Fin L → ℝ) → (Fin L → ℝ) →L[ℝ] ℝ}
    (hu : ∀ x, HasFDerivAt u (u' x) x) (hpos : ∀ x l, 0 < u' x (Pi.single l 1))
    {x y : Fin L → ℝ} (hxy : x ≤ y) (hne : x ≠ y) : u x < u y := by
  set d := y - x with hd
  have hd0 : ∀ l, 0 ≤ d l := fun l => by simp [hd, hxy l]
  have hdne : d ≠ 0 := fun h => hne (by rw [sub_eq_zero] at h; exact h.symm)
  set g : ℝ → ℝ := fun t => u (x + t • d) with hg
  have hgd : ∀ t, HasDerivAt g (u' (x + t • d) d) t := fun t => mc_line_hasDerivAt_at (hu _)
  have hmono : StrictMonoOn g (Set.Icc 0 1) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc 0 1)
      (fun t _ => (hgd t).continuousAt.continuousWithinAt) fun t _ => ?_
    rw [(hgd t).deriv]
    exact clm_pos_of_partials_pos (hpos _) hd0 hdne
  have := hmono ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_lt_one
  simpa [hg, hd] using this

/-- **Footnote 17** (MWG, p. 562). With `∇F ≫ 0` everywhere, `F` is nondecreasing, so
`{F ≤ 0}` satisfies free disposal. -/
theorem mono_of_grad_pos {F : (Fin L → ℝ) → ℝ} {F' : (Fin L → ℝ) → (Fin L → ℝ) →L[ℝ] ℝ}
    (hF : ∀ y, HasFDerivAt F (F' y) y) (hpos : ∀ y l, 0 < F' y (Pi.single l 1))
    {x y : Fin L → ℝ} (hxy : x ≤ y) : F x ≤ F y := by
  by_cases h : x = y
  · rw [h]
  · exact (strictMono_of_grad_pos hF hpos hxy h).le

/-- **Problem (16.F.1)** (MWG, p. 562), its constraint set: utility requirements `uᵢ(xᵢ) ≥ ūᵢ`
for `i ≠ i₀`, resource constraints `∑ᵢ x_{ℓi} ≤ ω̄ₗ + ∑ⱼ y_{ℓj}`, technology `Fⱼ(yⱼ) ≤ 0` and
`xᵢ ≥ 0`. -/
def Problem16F1 (u : ι → (Fin L → ℝ) → ℝ) (F : κ → (Fin L → ℝ) → ℝ) (ω : Fin L → ℝ) (i₀ : ι)
    (ub : ι → ℝ) : Set ((ι → Fin L → ℝ) × (κ → Fin L → ℝ)) :=
  {v | (∀ i, i ≠ i₀ → ub i ≤ u i (v.1 i)) ∧ (∀ l, ∑ i, v.1 i l ≤ ω l + ∑ j, v.2 j l) ∧
    (∀ j, F j (v.2 j) ≤ 0) ∧ ∀ i l, 0 ≤ v.1 i l}

/-- **Problem (16.F.1)** (MWG, p. 562): `v` maximizes `u_{i₀}(x_{i₀})` on the constraint set. -/
def IsSolution16F1 (u : ι → (Fin L → ℝ) → ℝ) (F : κ → (Fin L → ℝ) → ℝ) (ω : Fin L → ℝ)
    (i₀ : ι) (ub : ι → ℝ) (v : (ι → Fin L → ℝ) × (κ → Fin L → ℝ)) : Prop :=
  v ∈ Problem16F1 u F ω i₀ ub ∧ ∀ v' ∈ Problem16F1 u F ω i₀ ub, u i₀ (v'.1 i₀) ≤ u i₀ (v.1 i₀)

/-- **Section 16.F** (MWG, p. 562). The economy of Section 16.F: `Xᵢ = ℝ^L₊`, utilities `uᵢ`,
production sets `{Fⱼ ≤ 0}`. -/
def economy16F (u : ι → (Fin L → ℝ) → ℝ) (F : κ → (Fin L → ℝ) → ℝ) (ω : Fin L → ℝ) :
    PrefEconomy ι κ L :=
  PrefEconomy.ofUtility (fun _ => nonnegOrthant L) u (fun j => {y | F j y ≤ 0}) ω

/-- Giving `δ` more of good `l` to consumer `i₀` keeps a point of (16.F.1) feasible after the same
amount is freed by another consumer or by slack. -/
theorem single_nonneg_add {x : Fin L → ℝ} (hx : ∀ l, 0 ≤ x l) (l : Fin L) {δ : ℝ}
    (hδ : 0 ≤ δ) : ∀ m, 0 ≤ (x + (Pi.single l δ : Fin L → ℝ)) m := fun m => by
  by_cases hm : m = l
  · subst hm; simp only [Pi.add_apply, Pi.single_eq_same]; linarith [hx m]
  · simp only [Pi.add_apply, Pi.single_eq_of_ne hm, add_zero]; exact hx m

/-- **Section 16.F** (MWG, p. 563). With strongly monotone `u_{i₀}`, every solution of (16.F.1)
has binding resource constraints. -/
theorem solution16F1_resources_bind {u : ι → (Fin L → ℝ) → ℝ}
    {F : κ → (Fin L → ℝ) → ℝ} {ω : Fin L → ℝ} {i₀ : ι} {ub : ι → ℝ}
    (hmono : PrefStronglyMonotone (nonnegOrthant L) (utilityPref (u i₀)))
    {v : (ι → Fin L → ℝ) × (κ → Fin L → ℝ)} (hv : IsSolution16F1 u F ω i₀ ub v) :
    ∀ l, ∑ i, v.1 i l = ω l + ∑ j, v.2 j l := by
  classical
  intro l
  by_contra hne
  have hlt : ∑ i, v.1 i l < ω l + ∑ j, v.2 j l := lt_of_le_of_ne (hv.1.2.1 l) hne
  set δ := ω l + ∑ j, v.2 j l - ∑ i, v.1 i l with hδ
  have hδ0 : 0 < δ := by linarith
  set x' : ι → Fin L → ℝ := Function.update v.1 i₀ (v.1 i₀ + Pi.single l δ) with hx'
  have hx'i₀ : x' i₀ = v.1 i₀ + Pi.single l δ := by simp [hx']
  have hmem : (x', v.2) ∈ Problem16F1 u F ω i₀ ub := by
    refine ⟨fun i hi => ?_, fun m => ?_, hv.1.2.2.1, fun i m => ?_⟩
    · simpa [hx', hi] using hv.1.1 i hi
    · have hsum : ∑ i, x' i m = ∑ i, v.1 i m + (Pi.single l δ : Fin L → ℝ) m := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀),
          ← Finset.add_sum_erase _ (fun i => v.1 i m) (Finset.mem_univ i₀), hx'i₀]
        have : ∑ i ∈ Finset.univ.erase i₀, x' i m = ∑ i ∈ Finset.univ.erase i₀, v.1 i m :=
          Finset.sum_congr rfl fun i hi => by simp [hx', Finset.ne_of_mem_erase hi]
        rw [this, Pi.add_apply]; ring
      rw [hsum]
      by_cases hm : m = l
      · subst hm; simp [hδ]
      · simpa [hm] using hv.1.2.1 m
    · change 0 ≤ x' i m
      by_cases hi : i = i₀
      · rw [hi, hx'i₀]; exact single_nonneg_add (hv.1.2.2.2 i₀) l hδ0.le m
      · simpa [hx', hi] using hv.1.2.2.2 i m
  have hgt : u i₀ (v.1 i₀) < u i₀ (x' i₀) := by
    rw [hx'i₀]
    refine not_le.mp (hmono _ (hv.1.2.2.2 i₀) _ (single_nonneg_add (hv.1.2.2.2 i₀) l hδ0.le)
      (fun m => ?_) ?_).2
    · by_cases hm : m = l
      · subst hm; simp; linarith
      · simp [hm]
    · intro h
      have := congrFun h l
      simp at this
      linarith
  exact absurd (hv.2 _ hmem) (not_le.mpr hgt)

/-- **Exercise 16.F.1** (MWG, p. 562), first part. With utilities continuous and strongly monotone
on `ℝ^L₊`, every solution of (16.F.1) is a Pareto optimal allocation of the economy of Section
16.F (resource constraints bind, so (16.B.1) holds). -/
theorem exercise_16_F_1_i {u : ι → (Fin L → ℝ) → ℝ} {F : κ → (Fin L → ℝ) → ℝ}
    {ω : Fin L → ℝ} {i₀ : ι} {ub : ι → ℝ} (hcont : ∀ i, ContinuousOn (u i) (nonnegOrthant L))
    (hmono : ∀ i, PrefStronglyMonotone (nonnegOrthant L) (utilityPref (u i)))
    {v : (ι → Fin L → ℝ) × (κ → Fin L → ℝ)} (hv : IsSolution16F1 u F ω i₀ ub v) :
    (economy16F u F ω).IsParetoOptimal ⟨v.1, v.2⟩ := by
  classical
  have hbind := solution16F1_resources_bind (hmono i₀) hv
  have hfeas : (economy16F u F ω).IsFeasible ⟨v.1, v.2⟩ :=
    ⟨⟨fun i => hv.1.2.2.2 i, fun j => hv.1.2.2.1 j⟩, funext fun l => by
      simpa [Finset.sum_apply, economy16F, PrefEconomy.ofUtility] using hbind l⟩
  refine ⟨hfeas, ?_⟩
  rintro ⟨a', ⟨⟨hx', hy'⟩, hc'⟩, hle, k, hk⟩
  have hle' : ∀ i, u i (v.1 i) ≤ u i (a'.x i) := hle
  have hlt : u k (v.1 k) < u k (a'.x k) := not_le.mp hk.2
  have hx'X : ∀ i, a'.x i ∈ nonnegOrthant L := hx'
  -- `(x', y')` satisfies the constraints of (16.F.1)
  have hcons : ∀ x'' : ι → Fin L → ℝ, (∀ i, x'' i ∈ nonnegOrthant L) →
      ∑ i, x'' i = ∑ i, a'.x i → (∀ i, i ≠ i₀ → u i (v.1 i) ≤ u i (x'' i)) →
      (x'', a'.y) ∈ Problem16F1 u F ω i₀ ub := by
    intro x'' hx'' hsum hu
    refine ⟨fun i hi => (hv.1.1 i hi).trans (hu i hi), fun l => ?_, hy', fun i l => hx'' i l⟩
    have := congrFun (hsum.trans hc') l
    simp only [Finset.sum_apply, Pi.add_apply, economy16F, PrefEconomy.ofUtility] at this
    rw [this]
  by_cases hk0 : k = i₀
  · subst hk0
    have := hv.2 _ (hcons a'.x hx'X rfl fun i _ => hle' i)
    linarith
  -- move a little of a good from `k` to `i₀`
  obtain ⟨l, hl⟩ : ∃ l, 0 < a'.x k l := by
    by_contra hall
    push Not at hall
    have h0 : a'.x k = 0 := funext fun l => le_antisymm (hall l) (hx'X k l)
    have := utility_mono_of_strongMono (hmono k) (x := 0) (y := v.1 k) (fun _ => le_rfl)
      (fun l => hv.1.2.2.2 k l)
    rw [h0] at hlt
    linarith
  obtain ⟨δ, hδ, hmem, hs⟩ := exists_strict_sub_single (rationalOn_utilityPref _ (u k))
    (prefContinuous_utilityPref (hcont k)) (hx'X k) (fun m => hv.1.2.2.2 k m) hk hl
  set x'' : ι → Fin L → ℝ := fun i =>
    if i = i₀ then a'.x i + Pi.single l δ else if i = k then a'.x i - Pi.single l δ else a'.x i
    with hx''
  have hx''i₀ : x'' i₀ = a'.x i₀ + Pi.single l δ := by simp [hx'']
  have hx''k : x'' k = a'.x k - Pi.single l δ := by simp [hx'', hk0]
  have hx''X : ∀ i, x'' i ∈ nonnegOrthant L := by
    intro i
    by_cases h1 : i = i₀
    · subst h1; rw [hx''i₀]; exact single_nonneg_add (hx'X _) l hδ.le
    · by_cases h2 : i = k
      · subst h2; rw [hx''k]; exact hmem
      · simpa [hx'', h1, h2] using hx'X i
  have hsum : ∑ i, x'' i = ∑ i, a'.x i := by
    have : ∀ i, x'' i = a'.x i + (if i = i₀ then Pi.single l δ else 0) -
        (if i = k then Pi.single l δ else 0) := fun i => by
      by_cases h1 : i = i₀
      · subst h1; simp [hx'', Ne.symm hk0]
      · by_cases h2 : i = k
        · subst h2; simp [hx'', h1]
        · simp [hx'', h1, h2]
    simp only [this, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte, add_sub_cancel_right]
  have hu : ∀ i, i ≠ i₀ → u i (v.1 i) ≤ u i (x'' i) := by
    intro i hi
    by_cases h2 : i = k
    · subst h2; rw [hx''k]; exact hs.1
    · simpa [hx'', hi, h2] using hle' i
  have hopt := hv.2 _ (hcons x'' hx''X hsum hu)
  have hgt : u i₀ (a'.x i₀) < u i₀ (x'' i₀) := by
    rw [hx''i₀]
    refine not_le.mp (hmono i₀ _ (hx'X i₀) _ (single_nonneg_add (hx'X i₀) l hδ.le)
      (fun m => ?_) ?_).2
    · by_cases hm : m = l
      · subst hm; simp; linarith
      · simp [hm]
    · intro h
      have := congrFun h l
      simp at this
      linarith
  linarith [hle' i₀]

/-- **Exercise 16.F.1** (MWG, p. 562), second part. With `F` nondecreasing (free disposal, e.g.
`∇F ≫ 0`) and at least one firm, every Pareto optimal allocation solves (16.F.1) for the utility
levels `ūᵢ = uᵢ(xᵢ)` it gives. -/
theorem exercise_16_F_1_ii [Nonempty κ] {u : ι → (Fin L → ℝ) → ℝ}
    {F : κ → (Fin L → ℝ) → ℝ} {ω : Fin L → ℝ} {i₀ : ι}
    (hFmono : ∀ j x y, x ≤ y → F j x ≤ F j y) {a : Allocation ι κ L}
    (hpo : (economy16F u F ω).IsParetoOptimal a) :
    IsSolution16F1 u F ω i₀ (fun i => u i (a.x i)) (a.x, a.y) := by
  classical
  obtain ⟨⟨⟨hx, hy⟩, hc⟩, hno⟩ := hpo
  refine ⟨⟨fun i _ => le_rfl, fun l => ?_, hy, fun i l => hx i l⟩, ?_⟩
  · have := congrFun hc l
    simp only [Finset.sum_apply, Pi.add_apply] at this
    exact this.le
  rintro v' ⟨hu', hres, hF', hnn⟩
  by_contra hgt
  push Not at hgt
  -- dispose of the slack with one firm
  obtain ⟨j₀⟩ := ‹Nonempty κ›
  set D : Fin L → ℝ := ω + ∑ j, v'.2 j - ∑ i, v'.1 i with hD
  have hD0 : ∀ l, 0 ≤ D l := fun l => by
    simp only [hD, Pi.sub_apply, Pi.add_apply, Finset.sum_apply]; linarith [hres l]
  set y'' : κ → Fin L → ℝ := fun j => if j = j₀ then v'.2 j - D else v'.2 j with hy''
  apply hno
  refine ⟨⟨v'.1, y''⟩, ⟨⟨fun i l => hnn i l, fun j => ?_⟩, ?_⟩, fun i => ?_, i₀, ?_⟩
  · by_cases hj : j = j₀
    · subst hj
      change F j (y'' j) ≤ 0
      simp only [hy'', ↓reduceIte]
      exact (hFmono j _ _ fun l => by simp; linarith [hD0 l]).trans (hF' j)
    · change F j (y'' j) ≤ 0
      simp only [hy'', hj, ↓reduceIte]
      exact hF' j
  · change ∑ i, v'.1 i = ω + ∑ j, y'' j
    have : ∑ j, y'' j = ∑ j, v'.2 j - D := by
      rw [Finset.sum_congr rfl fun j _ => (show y'' j = v'.2 j - if j = j₀ then D else 0 by
        by_cases hj : j = j₀ <;> simp [hy'', hj]), Finset.sum_sub_distrib,
        Finset.sum_ite_eq' Finset.univ j₀ (fun _ => D)]
      simp
    rw [this, hD]
    abel
  · by_cases hi : i = i₀
    · subst hi; exact hgt.le
    · exact hu' i hi
  · exact ⟨hgt.le, not_le.mpr hgt⟩

/-! ## Exercise 16.F.2: the Kuhn-Tucker conditions (16.F.2)-(16.F.3) -/

/-- The coordinate projection `v ↦ xᵢ` on `ℝ^{LI} × ℝ^{LJ}`. -/
def projX (i : ι) : ((ι → Fin L → ℝ) × (κ → Fin L → ℝ)) →L[ℝ] (Fin L → ℝ) :=
  (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ _ _)

/-- The coordinate projection `v ↦ yⱼ` on `ℝ^{LI} × ℝ^{LJ}`. -/
def projY (j : κ) : ((ι → Fin L → ℝ) × (κ → Fin L → ℝ)) →L[ℝ] (Fin L → ℝ) :=
  (ContinuousLinearMap.proj j).comp (ContinuousLinearMap.snd ℝ _ _)

/-- The linear part `∑ᵢ x_{ℓi} - ∑ⱼ y_{ℓj}` of the resource constraint for good `ℓ`. -/
def resLin (l : Fin L) : ((ι → Fin L → ℝ) × (κ → Fin L → ℝ)) →L[ℝ] ℝ :=
  ∑ i : ι, (ContinuousLinearMap.proj l).comp (projX (κ := κ) i) -
    ∑ j : κ, (ContinuousLinearMap.proj l).comp (projY (ι := ι) j)

/-- **Exercise 16.F.2** (MWG, p. 576; (16.F.2)-(16.F.3), p. 563). Let `(x, y)` solve (16.F.1), with
every `uᵢ` differentiable at `xᵢ` with `∇uᵢ(xᵢ) ≫ 0` and every `Fⱼ` differentiable at `yⱼ` with
`∇Fⱼ(yⱼ) ≫ 0` (`J ≥ 1`, `L ≥ 1`). Then there are multipliers `δ ≥ 0` with `δ_{i₀} = 1`, `μ ≥ 0`,
`γ ≥ 0` such that `δᵢ ∂uᵢ/∂x_{ℓi} - μₗ ≤ 0`, with equality if `x_{ℓi} > 0` (16.F.2),
`μₗ - γⱼ ∂Fⱼ/∂y_{ℓj} = 0` (16.F.3), and complementary slackness holds. -/
theorem exercise_16_F_2 [Nonempty κ] (hL : 0 < L) {u : ι → (Fin L → ℝ) → ℝ}
    {F : κ → (Fin L → ℝ) → ℝ} {ω : Fin L → ℝ} {i₀ : ι} {ub : ι → ℝ}
    {v : (ι → Fin L → ℝ) × (κ → Fin L → ℝ)} (hv : IsSolution16F1 u F ω i₀ ub v)
    {u' : ι → (Fin L → ℝ) →L[ℝ] ℝ} {F' : κ → (Fin L → ℝ) →L[ℝ] ℝ}
    (hu : ∀ i, HasFDerivAt (u i) (u' i) (v.1 i)) (hF : ∀ j, HasFDerivAt (F j) (F' j) (v.2 j))
    (hupos : ∀ i l, 0 < u' i (Pi.single l 1)) (hFpos : ∀ j l, 0 < F' j (Pi.single l 1)) :
    ∃ (δ : ι → ℝ) (μ : Fin L → ℝ) (γ : κ → ℝ), δ i₀ = 1 ∧ (∀ i, 0 ≤ δ i) ∧ (∀ l, 0 ≤ μ l) ∧
      (∀ j, 0 ≤ γ j) ∧ (∀ i l, δ i * u' i (Pi.single l 1) - μ l ≤ 0) ∧
      (∀ i l, 0 < v.1 i l → δ i * u' i (Pi.single l 1) - μ l = 0) ∧
      (∀ j l, μ l - γ j * F' j (Pi.single l 1) = 0) ∧
      (∀ i, i ≠ i₀ → δ i * (u i (v.1 i) - ub i) = 0) ∧
      (∀ l, μ l * (ω l + ∑ j, v.2 j l - ∑ i, v.1 i l) = 0) ∧
      (∀ j, γ j * F j (v.2 j) = 0) := by
  classical
  -- the constraints of (16.F.1) as `gₖ ≤ 0`
  let g : ({i // i ≠ i₀} ⊕ Fin L ⊕ κ ⊕ (ι × Fin L)) → (ι → Fin L → ℝ) × (κ → Fin L → ℝ) → ℝ :=
    fun k w => match k with
    | Sum.inl i => ub i.1 - u i.1 (w.1 i.1)
    | Sum.inr (Sum.inl l) => resLin l w - ω l
    | Sum.inr (Sum.inr (Sum.inl j)) => F j (w.2 j)
    | Sum.inr (Sum.inr (Sum.inr il)) => -(w.1 il.1 il.2)
  let g' : ({i // i ≠ i₀} ⊕ Fin L ⊕ κ ⊕ (ι × Fin L)) →
      ((ι → Fin L → ℝ) × (κ → Fin L → ℝ)) →L[ℝ] ℝ :=
    fun k => match k with
    | Sum.inl i => -((u' i.1).comp (projX i.1))
    | Sum.inr (Sum.inl l) => resLin l
    | Sum.inr (Sum.inr (Sum.inl j)) => (F' j).comp (projY j)
    | Sum.inr (Sum.inr (Sum.inr il)) => -((ContinuousLinearMap.proj il.2).comp (projX il.1))
  have hres : ∀ (l : Fin L) (w : (ι → Fin L → ℝ) × (κ → Fin L → ℝ)),
      resLin l w = ∑ i, w.1 i l - ∑ j, w.2 j l := by
    intro l w
    simp [resLin, projX, projY]
  have hset : {w | ∀ k, g k w ≤ 0} = Problem16F1 u F ω i₀ ub := by
    ext w
    constructor
    · intro h
      refine ⟨fun i hi => ?_, fun l => ?_, fun j => h (Sum.inr (Sum.inr (Sum.inl j))),
        fun i l => ?_⟩
      · have := h (Sum.inl ⟨i, hi⟩); simp only [g] at this; linarith
      · have := h (Sum.inr (Sum.inl l)); simp only [g, hres] at this; linarith
      · have := h (Sum.inr (Sum.inr (Sum.inr (i, l)))); simp only [g] at this; linarith
    · rintro ⟨h1, h2, h3, h4⟩ k
      rcases k with i | l | j | il
      · simp only [g]; linarith [h1 i.1 i.2]
      · simp only [g, hres]; linarith [h2 l]
      · exact h3 j
      · simp only [g]; linarith [h4 il.1 il.2]
  have hz : ∀ k, g k v ≤ 0 := by
    have := hv.1; rw [← hset] at this; exact this
  have hmax : IsLocalMaxOn (fun w : (ι → Fin L → ℝ) × (κ → Fin L → ℝ) => u i₀ (w.1 i₀))
      {w | ∀ k, g k w ≤ 0} v := by
    rw [hset]
    exact Filter.eventually_of_mem self_mem_nhdsWithin fun w hw => hv.2 w hw
  have hf : HasFDerivAt (fun w : (ι → Fin L → ℝ) × (κ → Fin L → ℝ) => u i₀ (w.1 i₀))
      ((u' i₀).comp (projX i₀)) v := (hu i₀).comp v (projX i₀).hasFDerivAt
  have hg : ∀ k, HasFDerivAt (g k) (g' k) v := by
    intro k
    rcases k with i | l | j | il
    · exact (hasFDerivAt_const _ _).sub ((hu i.1).comp v (projX i.1).hasFDerivAt) |>.congr_fderiv
        (by simp [g'])
    · exact (resLin l).hasFDerivAt.sub_const (ω l)
    · exact (hF j).comp v (projY j).hasFDerivAt
    · exact ((ContinuousLinearMap.proj il.2).comp (projX il.1)).hasFDerivAt.neg
  obtain ⟨l0, lam, hl0, hlam, hne, hcs, heq⟩ := fritz_john hz hmax hf hg
  -- the multipliers
  set δh : ι → ℝ := fun i => if h : i = i₀ then l0 else lam (Sum.inl ⟨i, h⟩) with hδh
  set μ : Fin L → ℝ := fun l => lam (Sum.inr (Sum.inl l)) with hμ
  set γ : κ → ℝ := fun j => lam (Sum.inr (Sum.inr (Sum.inl j))) with hγ
  set ν : ι → Fin L → ℝ := fun i l => lam (Sum.inr (Sum.inr (Sum.inr (i, l)))) with hν
  -- evaluating the multiplier identity in the coordinate directions
  set a : ι → Fin L → ℝ := fun i l => u' i (Pi.single l 1) with ha
  set b : κ → Fin L → ℝ := fun j l => F' j (Pi.single l 1) with hb
  have hpx : ∀ (i i' : ι) (l : Fin L), projX (κ := κ) i'
      ((Pi.single i (Pi.single l 1) : ι → Fin L → ℝ), (0 : κ → Fin L → ℝ)) =
      if i' = i then Pi.single l 1 else 0 := fun i i' l => by
    simp only [projX, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.proj_apply, Pi.single_apply]
  have hpy0 : ∀ (i : ι) (j : κ) (l : Fin L), projY (ι := ι) j
      ((Pi.single i (Pi.single l 1) : ι → Fin L → ℝ), (0 : κ → Fin L → ℝ)) = 0 := by
    intro i j l
    simp [projY]
  have hpx0 : ∀ (i : ι) (j : κ) (l : Fin L), projX (κ := κ) i
      ((0 : ι → Fin L → ℝ), (Pi.single j (Pi.single l 1) : κ → Fin L → ℝ)) = 0 := by
    intro i j l
    simp [projX]
  have hpy : ∀ (j j' : κ) (l : Fin L), projY (ι := ι) j'
      ((0 : ι → Fin L → ℝ), (Pi.single j (Pi.single l 1) : κ → Fin L → ℝ)) =
      if j' = j then Pi.single l 1 else 0 := fun j j' l => by
    simp only [projY, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd',
      ContinuousLinearMap.proj_apply, Pi.single_apply]
  have hsingle : ∀ (l l' : Fin L), (Pi.single l (1 : ℝ) : Fin L → ℝ) l' =
      if l' = l then 1 else 0 := fun l l' => Pi.single_apply l 1 l'
  have hdx : ∀ i l, δh i * a i l - μ l = -ν i l := by
    intro i l
    have h := congrArg (fun φ : ((ι → Fin L → ℝ) × (κ → Fin L → ℝ)) →L[ℝ] ℝ =>
      φ ((Pi.single i (Pi.single l 1) : ι → Fin L → ℝ), (0 : κ → Fin L → ℝ))) heq
    rw [sum_apply, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type] at h
    simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, g', ContinuousLinearMap.comp_apply,
      neg_apply, hpx, hpy0, hres, map_zero, mul_zero,
      Finset.sum_const_zero, zero_add] at h
    -- the four sums
    have e1 : ∑ x : {i // i ≠ i₀}, lam (Sum.inl x) * -(u' x.1 (if x.1 = i then Pi.single l 1
        else 0)) = if h : i = i₀ then 0 else -(lam (Sum.inl ⟨i, h⟩) * a i l) := by
      split_ifs with hi
      · exact Finset.sum_eq_zero fun x _ => by
          have : x.1 ≠ i := fun h' => x.2 (h'.trans hi)
          simp [this]
      · rw [Finset.sum_eq_single ⟨i, hi⟩]
        · simp [ha]
        · intro x _ hx
          have : x.1 ≠ i := fun h' => hx (Subtype.ext h')
          simp [this]
        · simp
    have hinner : ∀ x, ∑ x_1, (Pi.single i (Pi.single l 1) : ι → Fin L → ℝ) x_1 x =
        if x = l then 1 else 0 := by
      intro x
      rw [Finset.sum_eq_single i (fun b _ hb => by simp [hb]) (by simp)]
      simp [Pi.single_apply]
    have e2 : ∑ x : Fin L, lam (Sum.inr (Sum.inl x)) *
        (∑ x_1, (Pi.single i (Pi.single l 1) : ι → Fin L → ℝ) x_1 x -
          ∑ x_1 : κ, (0 : κ → Fin L → ℝ) x_1 x) = μ l := by
      simp only [hinner, Pi.zero_apply, Finset.sum_const_zero, sub_zero, mul_ite, mul_one,
        mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, hμ]
    have e3 : ∑ x : ι × Fin L, lam (Sum.inr (Sum.inr (Sum.inr x))) *
        -(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin L => ℝ) x.2
          (if x.1 = i then Pi.single l 1 else 0)) = -ν i l := by
      rw [Finset.sum_eq_single (i, l)]
      · simp [hν]
      · rintro ⟨i', l'⟩ _ hne
        by_cases hi : i' = i
        · subst hi
          have : l' ≠ l := fun h' => hne (by rw [h'])
          simp [this]
        · simp [hi]
      · simp
    rw [e1, e2, e3] at h
    by_cases hi : i = i₀
    · subst hi
      simp only [↓reduceIte, ↓reduceDIte, hδh] at h ⊢
      simp only [ha]
      linarith
    · have hi' : i₀ ≠ i := Ne.symm hi
      simp only [hi', hi, ↓reduceIte, ↓reduceDIte, map_zero, mul_zero, hδh] at h ⊢
      simp only [ha]
      linarith
  have hdy : ∀ j l, γ j * b j l - μ l = 0 := by
    intro j l
    have h := congrArg (fun φ : ((ι → Fin L → ℝ) × (κ → Fin L → ℝ)) →L[ℝ] ℝ =>
      φ ((0 : ι → Fin L → ℝ), (Pi.single j (Pi.single l 1) : κ → Fin L → ℝ))) heq
    rw [sum_apply, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type] at h
    simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, g', ContinuousLinearMap.comp_apply,
      neg_apply, hpx0, hpy, hres, map_zero, mul_zero,
      Finset.sum_const_zero, zero_add, add_zero, neg_zero] at h
    have hinner : ∀ x, ∑ x_1, (Pi.single j (Pi.single l 1) : κ → Fin L → ℝ) x_1 x =
        if x = l then 1 else 0 := by
      intro x
      rw [Finset.sum_eq_single j (fun b _ hb => by simp [hb]) (by simp)]
      simp [Pi.single_apply]
    have e2 : ∑ x : Fin L, lam (Sum.inr (Sum.inl x)) *
        (∑ x_1 : ι, (0 : ι → Fin L → ℝ) x_1 x -
          ∑ x_1, (Pi.single j (Pi.single l 1) : κ → Fin L → ℝ) x_1 x) = -μ l := by
      simp only [hinner, Pi.zero_apply, Finset.sum_const_zero, zero_sub, mul_neg, mul_ite,
        mul_one, mul_zero, Finset.sum_neg_distrib, Finset.sum_ite_eq', Finset.mem_univ,
        ↓reduceIte, hμ]
    have e4 : ∑ x : κ, lam (Sum.inr (Sum.inr (Sum.inl x))) *
        (F' x) (if x = j then Pi.single l 1 else 0) = γ j * b j l := by
      rw [Finset.sum_eq_single j (fun b _ hb => by simp [hb]) (by simp)]
      simp [hγ, hb]
    rw [e2, e4] at h
    linarith
  -- complementary slackness, multiplier by multiplier
  have hcsU : ∀ i (h : i ≠ i₀), lam (Sum.inl ⟨i, h⟩) * (ub i - u i (v.1 i)) = 0 :=
    fun i h => hcs (Sum.inl ⟨i, h⟩)
  have hcsR : ∀ l, μ l * (∑ i, v.1 i l - ∑ j, v.2 j l - ω l) = 0 := fun l => by
    have := hcs (Sum.inr (Sum.inl l)); simp only [g, hres] at this; exact this
  have hcsF : ∀ j, γ j * F j (v.2 j) = 0 := fun j => hcs (Sum.inr (Sum.inr (Sum.inl j)))
  have hcsN : ∀ i l, ν i l * v.1 i l = 0 := fun i l => by
    have := hcs (Sum.inr (Sum.inr (Sum.inr (i, l)))); simp only [g] at this
    have h2 : ν i l * -v.1 i l = 0 := this
    linarith
  have hδh0 : ∀ i, 0 ≤ δh i := fun i => by
    simp only [hδh]; split_ifs
    · exact hl0
    · exact hlam _
  have hμ0 : ∀ l, 0 ≤ μ l := fun l => hlam _
  have hγ0 : ∀ j, 0 ≤ γ j := fun j => hlam _
  have hν0 : ∀ i l, 0 ≤ ν i l := fun i l => hlam _
  have ha0 : ∀ i l, 0 < a i l := fun i l => hupos i l
  have hb0 : ∀ j l, 0 < b j l := fun j l => hFpos j l
  have hνz : ∀ i l, 0 < v.1 i l → ν i l = 0 := fun i l hx => by
    rcases mul_eq_zero.mp (hcsN i l) with h | h
    · exact h
    · linarith
  rcases hl0.lt_or_eq with hl0pos | hl0z
  · -- `λ₀ > 0`: normalize
    refine ⟨fun i => δh i / l0, fun l => μ l / l0, fun j => γ j / l0, ?_, fun i => ?_,
      fun l => ?_, fun j => ?_, fun i l => ?_, fun i l hx => ?_, fun j l => ?_, fun i hi => ?_,
      fun l => ?_, fun j => ?_⟩
    · simp [hδh, hl0pos.ne']
    · exact div_nonneg (hδh0 i) hl0
    · exact div_nonneg (hμ0 l) hl0
    · exact div_nonneg (hγ0 j) hl0
    · have h1 := hdx i l
      have h2 : δh i / l0 * a i l - μ l / l0 = -ν i l / l0 := by
        field_simp; linarith
      change δh i / l0 * a i l - μ l / l0 ≤ 0
      rw [h2]
      exact div_nonpos_of_nonpos_of_nonneg (by linarith [hν0 i l]) hl0
    · have h1 := hdx i l
      rw [hνz i l hx] at h1
      change δh i / l0 * a i l - μ l / l0 = 0
      field_simp; linarith
    · have h1 := hdy j l
      change μ l / l0 - γ j / l0 * b j l = 0
      field_simp; linarith
    · have h1 := hcsU i hi
      have hδi : δh i = lam (Sum.inl ⟨i, hi⟩) := by simp [hδh, hi]
      change δh i / l0 * (u i (v.1 i) - ub i) = 0
      rw [hδi]
      field_simp; linarith
    · have h1 := hcsR l
      change μ l / l0 * (ω l + ∑ j, v.2 j l - ∑ i, v.1 i l) = 0
      field_simp; linarith
    · change γ j / l0 * F j (v.2 j) = 0
      rw [div_mul_eq_mul_div, hcsF j, zero_div]
  · -- `λ₀ = 0`: the prices are strictly positive and consumer `i₀` consumes nothing
    subst hl0z
    have hμne : ∃ l, μ l ≠ 0 := by
      by_contra hall
      push Not at hall
      have hγz : ∀ j, γ j = 0 := fun j => by
        have := hdy j ⟨0, hL⟩
        rw [hall] at this
        rcases mul_eq_zero.mp (by linarith : γ j * b j ⟨0, hL⟩ = 0) with h | h
        · exact h
        · exact absurd h (hb0 j _).ne'
      have hδz : ∀ i, δh i = 0 ∧ ∀ l, ν i l = 0 := fun i => by
        refine ⟨?_, fun l => ?_⟩
        · have := hdx i ⟨0, hL⟩
          rw [hall] at this
          have h1 := mul_nonneg (hδh0 i) (ha0 i ⟨0, hL⟩).le
          have h2 : δh i * a i ⟨0, hL⟩ = 0 := by linarith [hν0 i ⟨0, hL⟩]
          rcases mul_eq_zero.mp h2 with h | h
          · exact h
          · exact absurd h (ha0 i _).ne'
        · have := hdx i l
          rw [hall] at this
          have h1 := mul_nonneg (hδh0 i) (ha0 i l).le
          linarith [hν0 i l]
      rcases hne with h | ⟨k, hk⟩
      · exact h rfl
      · rcases k with i | l | j | il
        · have := (hδz i.1).1
          simp only [hδh, i.2, ↓reduceDIte] at this
          exact hk this
        · exact hk (hall l)
        · exact hk (hγz j)
        · exact hk ((hδz il.1).2 il.2)
    obtain ⟨l₁, hl₁⟩ := hμne
    obtain ⟨j₀⟩ := ‹Nonempty κ›
    have hγj₀ : 0 < γ j₀ := by
      have h1 := hdy j₀ l₁
      have h2 : 0 < μ l₁ := lt_of_le_of_ne (hμ0 l₁) (Ne.symm hl₁)
      by_contra h
      have : γ j₀ = 0 := le_antisymm (not_lt.mp h) (hγ0 j₀)
      rw [this] at h1
      linarith
    have hμpos : ∀ l, 0 < μ l := fun l => by
      have := hdy j₀ l
      nlinarith [mul_pos hγj₀ (hb0 j₀ l)]
    have hx₀ : ∀ l, v.1 i₀ l = 0 := fun l => by
      by_contra hne
      have hx : 0 < v.1 i₀ l := lt_of_le_of_ne (hv.1.2.2.2 i₀ l) (Ne.symm hne)
      have := hdx i₀ l
      rw [hνz i₀ l hx] at this
      simp only [hδh, ↓reduceDIte, zero_mul, zero_sub, neg_eq_zero, neg_zero] at this
      linarith [hμpos l]
    set t := ∑ l, a i₀ l / μ l with ht
    have ht0 : 0 ≤ t := Finset.sum_nonneg fun l _ => (div_pos (ha0 i₀ l) (hμpos l)).le
    have hat : ∀ l, a i₀ l ≤ t * μ l := fun l => by
      have h1 : a i₀ l / μ l ≤ t := Finset.single_le_sum
        (f := fun l => a i₀ l / μ l) (fun l _ => (div_pos (ha0 i₀ l) (hμpos l)).le)
        (Finset.mem_univ l)
      rwa [div_le_iff₀ (hμpos l)] at h1
    refine ⟨fun i => if i = i₀ then 1 else t * δh i, fun l => t * μ l, fun j => t * γ j,
      by simp, fun i => ?_, fun l => mul_nonneg ht0 (hμ0 l), fun j => mul_nonneg ht0 (hγ0 j),
      fun i l => ?_, fun i l hx => ?_, fun j l => ?_, fun i hi => ?_, fun l => ?_, fun j => ?_⟩
    · change 0 ≤ if i = i₀ then 1 else t * δh i
      split_ifs
      · exact zero_le_one
      · exact mul_nonneg ht0 (hδh0 i)
    · change (if i = i₀ then 1 else t * δh i) * a i l - t * μ l ≤ 0
      split_ifs with hi
      · subst hi; linarith [hat l]
      · have := hdx i l
        nlinarith [mul_nonneg ht0 (hν0 i l)]
    · change (if i = i₀ then 1 else t * δh i) * a i l - t * μ l = 0
      split_ifs with hi
      · subst hi; linarith [hx₀ l]
      · have h1 := hdx i l
        rw [hνz i l hx] at h1
        have : t * (δh i * a i l - μ l) = 0 := by rw [h1]; ring
        linarith
    · change t * μ l - t * γ j * b j l = 0
      have h1 := hdy j l
      have : t * (γ j * b j l - μ l) = 0 := by rw [h1]; ring
      linarith
    · simp only [hi, ↓reduceIte]
      have h1 := hcsU i hi
      have hδi : δh i = lam (Sum.inl ⟨i, hi⟩) := by simp [hδh, hi]
      rw [hδi]
      have : t * (lam (Sum.inl ⟨i, hi⟩) * (ub i - u i (v.1 i))) = 0 := by rw [h1, mul_zero]
      linarith
    · have h1 := hcsR l
      have : t * (μ l * (∑ i, v.1 i l - ∑ j, v.2 j l - ω l)) = 0 := by rw [h1, mul_zero]
      linarith
    · rw [mul_assoc, hcsF j, mul_zero]


end MWG.WelfareTheorems
