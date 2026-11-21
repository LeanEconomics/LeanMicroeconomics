/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGCompetitiveMarkets.WelfareTheorems
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Inverse demand, industry marginal cost and the central authority (MWG Section 10.C)

MWG, pp. 321-322 (Figures 10.C.5-10.C.6, footnotes 11-12) and Exercises 10.C.3-10.C.4
(pp. 344-345).

* **Exercise 10.C.4**: the central authority allocating `x` units of good `ℓ` to maximize
  `∑ uᵢ`. Its value `γ(x)` (`grossBenefit`, defined as a supremum) is attained exactly at the
  allocations satisfying the first-order conditions (a); `γ` is differentiable at `x > 0` with
  `γ'(x) = P(x) = φᵢ'(xᵢ*)` for every active consumer (b); consumers facing `P(x)` demand `x` in
  aggregate, so `P` is the inverse of aggregate demand (c).
* **Exercise 10.C.3**: the central authority minimizing the cost `C(q)` of producing `q`
  (`minCost`, an infimum), for convex costs with `c' > 0`. (a) First-order conditions,
  necessary and sufficient; (b) `C'(q) = cⱼ'(qⱼ*)` for active firms; (c) firms maximizing profit
  at `p = C'(q)` produce `q` in aggregate (with strictly convex costs, uniquely), so `C'` is the
  inverse of the industry supply function (footnotes 11-12, Figure 10.C.5).
* `invDemand` (`P = x⁻¹`, Figure 10.C.6) and `invSupply` (`C' = q⁻¹`) with their monotonicity.
-/

namespace MWG.CompetitiveMarkets

open Filter Topology

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-! ## The consumption side -/

/-- `maxᵢ φᵢ'(0)`, the largest marginal benefit at zero consumption. -/
noncomputable def maxMB [Nonempty ι] (C : ι → QLConsumer) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i => (C i).dφ 0

theorem le_maxMB [Nonempty ι] (C : ι → QLConsumer) (i : ι) : (C i).dφ 0 ≤ maxMB C :=
  Finset.le_sup' (fun i => (C i).dφ 0) (Finset.mem_univ i)

theorem exists_eq_maxMB [Nonempty ι] (C : ι → QLConsumer) : ∃ i, (C i).dφ 0 = maxMB C := by
  obtain ⟨i, -, h⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => (C i).dφ 0)
  exact ⟨i, h.symm⟩

theorem maxMB_pos [Nonempty ι] (C : ι → QLConsumer) : 0 < maxMB C := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact ((C i).dφ_pos 0 le_rfl).trans_le (le_maxMB C i)

/-- Positive aggregate demand means some consumer has `p < φᵢ'(0)`. -/
theorem exists_lt_of_aggDemand_pos (C : ι → QLConsumer) {p : ℝ} (hp : 0 < p)
    (h : 0 < aggDemand C p) : ∃ i, p < (C i).dφ 0 := by
  by_contra hno
  push Not at hno
  rw [(aggDemand_eq_zero_iff C hp).2 hno] at h
  exact lt_irrefl 0 h

/-- **Supergradient of the gross benefit.** If `x` satisfies the consumers' first-order
conditions at `μ`, then `∑ φᵢ(yᵢ) ≤ ∑ φᵢ(xᵢ) + μ (∑ yᵢ - ∑ xᵢ)` for all `y ≥ 0`. -/
theorem foc_benefit_le {C : ι → QLConsumer} {x : ι → ℝ} {μ : ℝ}
    (hx : ∀ i, IsFOCSol (C i).dφ μ (x i)) {y : ι → ℝ} (hy : ∀ i, 0 ≤ y i) :
    ∑ i, (C i).φ (y i) ≤ ∑ i, (C i).φ (x i) + μ * (∑ i, y i - ∑ i, x i) := by
  have h : ∀ i, (C i).φ (y i) ≤ (C i).φ (x i) + μ * (y i - x i) := by
    intro i
    have ht := (C i).tangent_le (hx i).1 (hy i)
    rcases eq_or_lt_of_le (hx i).1 with h0 | hpos
    · rw [← h0] at ht ⊢
      have := (hx i).2.1
      rw [← h0] at this
      nlinarith [hy i]
    · rw [(hx i).2.2 hpos] at ht
      exact ht
  calc ∑ i, (C i).φ (y i) ≤ ∑ i, ((C i).φ (x i) + μ * (y i - x i)) :=
        Finset.sum_le_sum fun i _ => h i
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]

/-- The values `∑ φᵢ(yᵢ)` of the allocations `y ≥ 0` of `X` units of good `ℓ`. -/
def benefitSet (C : ι → QLConsumer) (X : ℝ) : Set ℝ :=
  {s | ∃ y : ι → ℝ, (∀ i, 0 ≤ y i) ∧ ∑ i, y i = X ∧ s = ∑ i, (C i).φ (y i)}

/-- **Exercise 10.C.4** (MWG, p. 345). The value function `γ(x)` of the central authority's
problem `max ∑ uᵢ` over allocations of `x` units of good `ℓ` (the numeraire being fixed). -/
noncomputable def grossBenefit (C : ι → QLConsumer) (X : ℝ) : ℝ := sSup (benefitSet C X)

/-- An allocation satisfying the first-order conditions attains `γ`. -/
theorem grossBenefit_isGreatest {C : ι → QLConsumer} {x : ι → ℝ} {μ : ℝ}
    (hx : ∀ i, IsFOCSol (C i).dφ μ (x i)) :
    IsGreatest (benefitSet C (∑ i, x i)) (∑ i, (C i).φ (x i)) := by
  refine ⟨⟨x, fun i => (hx i).1, rfl, rfl⟩, ?_⟩
  rintro s ⟨y, hy, hs, rfl⟩
  have := foc_benefit_le hx hy
  rw [hs, sub_self, mul_zero, add_zero] at this
  exact this

theorem grossBenefit_eq_of_foc {C : ι → QLConsumer} {x : ι → ℝ} {μ : ℝ}
    (hx : ∀ i, IsFOCSol (C i).dφ μ (x i)) :
    grossBenefit C (∑ i, x i) = ∑ i, (C i).φ (x i) :=
  (grossBenefit_isGreatest hx).csSup_eq

/-- The price at which aggregate demand equals a given `X ≥ 0` exists (intermediate value
theorem). -/
theorem exists_invDemand [Nonempty ι] (C : ι → QLConsumer) (X : ℝ) :
    ∃ μ, 0 ≤ X → 0 < μ ∧ aggDemand C μ = X ∧ (X = 0 → μ = maxMB C) := by
  by_cases hX : 0 ≤ X
  · rcases eq_or_lt_of_le hX with h0 | hpos
    · refine ⟨maxMB C, fun _ => ⟨maxMB_pos C, ?_, fun _ => rfl⟩⟩
      rw [← h0]
      exact (aggDemand_eq_zero_iff C (maxMB_pos C)).2 fun i => le_maxMB C i
    · obtain ⟨i₀⟩ := ‹Nonempty ι›
      set lo := (C i₀).dφ X with hlo
      have hlo0 : 0 < lo := (C i₀).dφ_pos X hX
      have hdlo : (C i₀).demand lo = X := (C i₀).demand_eq ⟨hX, le_rfl, fun _ => rfl⟩
      have hge : X ≤ aggDemand C lo := by
        rw [← hdlo]
        exact Finset.single_le_sum (f := fun i => (C i).demand lo)
          (fun i _ => (C i).demand_nonneg hlo0) (Finset.mem_univ i₀)
      have hlohi : lo ≤ maxMB C :=
        ((C i₀).dφ_antitone (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hX) hX).trans (le_maxMB C i₀)
      have hhi : aggDemand C (maxMB C) = 0 :=
        (aggDemand_eq_zero_iff C (maxMB_pos C)).2 fun i => le_maxMB C i
      obtain ⟨μ, hμ, hμX⟩ := intermediate_value_Icc' hlohi
        ((aggDemand_continuousOn C).mono fun p hp => hlo0.trans_le hp.1)
        ⟨by rw [hhi]; exact hX, hge⟩
      exact ⟨μ, fun _ => ⟨hlo0.trans_le hμ.1, hμX, fun h => absurd h hpos.ne'⟩⟩
  · exact ⟨0, fun h => absurd h hX⟩

/-- **Inverse demand function** `P(x) = x⁻¹(x)` (MWG, p. 321, Figure 10.C.6), with
`P(0) = maxᵢ φᵢ'(0)`. -/
noncomputable def invDemand [Nonempty ι] (C : ι → QLConsumer) (X : ℝ) : ℝ :=
  Classical.choose (exists_invDemand C X)

theorem invDemand_spec [Nonempty ι] (C : ι → QLConsumer) {X : ℝ} (hX : 0 ≤ X) :
    0 < invDemand C X ∧ aggDemand C (invDemand C X) = X ∧ (X = 0 → invDemand C X = maxMB C) :=
  Classical.choose_spec (exists_invDemand C X) hX

theorem invDemand_pos [Nonempty ι] (C : ι → QLConsumer) {X : ℝ} (hX : 0 ≤ X) :
    0 < invDemand C X := (invDemand_spec C hX).1

/-- **(MWG, p. 345, Exercise 10.C.4(c))** Aggregate demand at `P(x)` is `x`. -/
theorem aggDemand_invDemand [Nonempty ι] (C : ι → QLConsumer) {X : ℝ} (hX : 0 ≤ X) :
    aggDemand C (invDemand C X) = X := (invDemand_spec C hX).2.1

/-- For `x > 0`, `P(x)` is the unique price with aggregate demand `x`. -/
theorem invDemand_unique [Nonempty ι] (C : ι → QLConsumer) {X μ : ℝ} (hX : 0 < X)
    (hμ : 0 < μ) (h : aggDemand C μ = X) : invDemand C X = μ := by
  have hP := invDemand_spec C hX.le
  have key : ∀ p₁ p₂, 0 < p₁ → p₁ < p₂ → aggDemand C p₁ = X → aggDemand C p₂ = X → False := by
    intro p₁ p₂ hp₁ h₁₂ e₁ e₂
    have := aggDemand_strictAnti C hp₁ h₁₂ (exists_lt_of_aggDemand_pos C hp₁ (e₁ ▸ hX))
    linarith
  rcases lt_trichotomy (invDemand C X) μ with hlt | heq | hgt
  · exact (key _ _ hP.1 hlt hP.2.1 h).elim
  · exact heq
  · exact (key _ _ hμ hgt h hP.2.1).elim

/-- **Figure 10.C.6** (MWG, p. 322). `P` inverts aggregate demand: `P(x(p)) = p` for
`0 < p < maxᵢ φᵢ'(0)`. -/
theorem invDemand_aggDemand [Nonempty ι] (C : ι → QLConsumer) {p : ℝ} (hp : 0 < p)
    (hpm : p < maxMB C) : invDemand C (aggDemand C p) = p := by
  obtain ⟨i, hi⟩ := exists_eq_maxMB C
  have hpos : 0 < aggDemand C p :=
    Finset.sum_pos' (fun k _ => (C k).demand_nonneg hp)
      ⟨i, Finset.mem_univ i, ((C i).demand_pos_iff hp).2 (hi ▸ hpm)⟩
  exact invDemand_unique C hpos hp rfl

theorem invDemand_le_maxMB [Nonempty ι] (C : ι → QLConsumer) {X : ℝ} (hX : 0 ≤ X) :
    invDemand C X ≤ maxMB C := by
  rcases eq_or_lt_of_le hX with h0 | hpos
  · exact le_of_eq ((invDemand_spec C hX).2.2 h0.symm)
  · obtain ⟨i, hi⟩ := exists_lt_of_aggDemand_pos C (invDemand_pos C hX)
      ((aggDemand_invDemand C hX).symm ▸ hpos)
    exact hi.le.trans (le_maxMB C i)

/-- **(MWG, p. 322)** The inverse demand function is strictly decreasing on `x ≥ 0`. -/
theorem invDemand_strictAntiOn [Nonempty ι] (C : ι → QLConsumer) :
    StrictAntiOn (invDemand C) (Set.Ici 0) := by
  intro X₁ h₁ X₂ h₂ h₁₂
  have h₁' : (0 : ℝ) ≤ X₁ := h₁
  have h₂' : (0 : ℝ) ≤ X₂ := h₂
  refine lt_of_le_of_ne ?_ fun heq => ?_
  · by_contra hlt
    push Not at hlt
    have := aggDemand_antitoneOn C (invDemand_pos C h₁') (invDemand_pos C h₂') hlt.le
    rw [aggDemand_invDemand C h₁', aggDemand_invDemand C h₂'] at this
    linarith
  · have e₁ := aggDemand_invDemand C h₁'
    have e₂ := aggDemand_invDemand C h₂'
    rw [heq] at e₂
    linarith

theorem invDemand_antitoneOn [Nonempty ι] (C : ι → QLConsumer) :
    AntitoneOn (invDemand C) (Set.Ici 0) :=
  (invDemand_strictAntiOn C).antitoneOn

/-- The optimal allocation of `X` units: each consumer's demand at `P(X)`. -/
noncomputable def optAlloc [Nonempty ι] (C : ι → QLConsumer) (X : ℝ) (i : ι) : ℝ :=
  (C i).demand (invDemand C X)

theorem optAlloc_foc [Nonempty ι] (C : ι → QLConsumer) {X : ℝ} (hX : 0 ≤ X) (i : ι) :
    IsFOCSol (C i).dφ (invDemand C X) (optAlloc C X i) :=
  (C i).demand_spec (invDemand_pos C hX)

theorem optAlloc_sum [Nonempty ι] (C : ι → QLConsumer) {X : ℝ} (hX : 0 ≤ X) :
    ∑ i, optAlloc C X i = X := aggDemand_invDemand C hX

/-- `γ(X) = ∑ φᵢ(xᵢ*(X))`. -/
theorem grossBenefit_eq [Nonempty ι] (C : ι → QLConsumer) {X : ℝ} (hX : 0 ≤ X) :
    grossBenefit C X = ∑ i, (C i).φ (optAlloc C X i) := by
  have := grossBenefit_eq_of_foc (optAlloc_foc C hX)
  rwa [optAlloc_sum C hX] at this

theorem grossBenefit_zero [Nonempty ι] (C : ι → QLConsumer) : grossBenefit C 0 = 0 := by
  have h := grossBenefit_eq_of_foc (C := C) (x := fun _ => 0) (μ := maxMB C)
    (fun i => ⟨le_rfl, le_maxMB C i, fun h => absurd h (lt_irrefl 0)⟩)
  simp only [Finset.sum_const_zero] at h
  rw [h]
  simp [QLConsumer.φ_zero]

/-- **Exercise 10.C.4(a)** (MWG, p. 345). An allocation `y ≥ 0` of `x` units solves the central
authority's problem iff it satisfies the first-order conditions: for some `μ`,
`φᵢ'(yᵢ) ≤ μ` with equality if `yᵢ > 0`. -/
theorem exercise_10_C_4a [Nonempty ι] (C : ι → QLConsumer) {y : ι → ℝ} (hy : ∀ i, 0 ≤ y i) :
    IsGreatest (benefitSet C (∑ i, y i)) (∑ i, (C i).φ (y i)) ↔
      ∃ μ, ∀ i, IsFOCSol (C i).dφ μ (y i) := by
  refine ⟨fun hmax => ?_, fun ⟨μ, hμ⟩ => grossBenefit_isGreatest hμ⟩
  have hX : 0 ≤ ∑ i, y i := Finset.sum_nonneg fun i _ => hy i
  set x := optAlloc C (∑ i, y i) with hx
  have hfoc := optAlloc_foc C hX
  have hsum := optAlloc_sum C hX
  -- `y = x` by strict concavity
  have hxy : y = x := by
    by_contra hne
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
    have hval : ∑ k, (C k).φ (y k) = ∑ k, (C k).φ (x k) := by
      refine le_antisymm ?_ (hmax.2 ⟨x, fun k => (hfoc k).1, hsum, rfl⟩)
      have := foc_benefit_le hfoc hy
      rw [hsum, sub_self, mul_zero, add_zero] at this
      exact this
    set m : ι → ℝ := fun k => (1 / 2 : ℝ) • y k + (1 / 2 : ℝ) • x k with hm
    have hm0 : ∀ k, 0 ≤ m k := fun k => by
      simp only [hm, smul_eq_mul]; linarith [hy k, (hfoc k).1]
    have hsum' : ∑ k, x k = ∑ k, y k := hsum
    have hms : ∑ k, m k = ∑ k, y k := by
      simp only [hm, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [hsum']; ring
    have hle := hmax.2 ⟨m, hm0, hms, rfl⟩
    have hge : ∀ k, (1 / 2 : ℝ) * (C k).φ (y k) + (1 / 2 : ℝ) * (C k).φ (x k) ≤ (C k).φ (m k) :=
      fun k => by
        simpa [smul_eq_mul, hm] using (C k).strictConcave.concaveOn.2 (Set.mem_Ici.2 (hy k))
          (Set.mem_Ici.2 (hfoc k).1) (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    have hgt : (1 / 2 : ℝ) * (C i).φ (y i) + (1 / 2 : ℝ) * (C i).φ (x i) < (C i).φ (m i) := by
      simpa [smul_eq_mul, hm] using (C i).strictConcave.2 (Set.mem_Ici.2 (hy i))
        (Set.mem_Ici.2 (hfoc i).1) hi (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    have := Finset.sum_lt_sum (fun k _ => hge k) ⟨i, Finset.mem_univ i, hgt⟩
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at this
    linarith
  refine ⟨invDemand C (∑ i, y i), fun i => ?_⟩
  have : y i = x i := congrFun hxy i
  rw [this]
  exact hfoc i

/-- **Exercise 10.C.4(b)** (MWG, p. 345). For `x > 0` the value `γ` of the central authority's
problem is differentiable with `γ'(x) = P(x)`, and `P(x) = φᵢ'(xᵢ*)` for every consumer with
`xᵢ* > 0`. -/
theorem exercise_10_C_4b [Nonempty ι] (C : ι → QLConsumer) {X : ℝ} (hX : 0 < X) :
    HasDerivAt (grossBenefit C) (invDemand C X) X ∧
      ∀ i, 0 < optAlloc C X i → invDemand C X = (C i).dφ (optAlloc C X i) := by
  classical
  have hX0 := hX.le
  have hfoc := optAlloc_foc C hX0
  refine ⟨?_, fun i hi => ((hfoc i).2.2 hi).symm⟩
  obtain ⟨i₀, hi₀⟩ := exists_pos_of_sum_pos ((optAlloc_sum C hX0).symm ▸ hX)
  set a := optAlloc C X i₀ with ha
  set d := invDemand C X with hd
  have hda : (C i₀).dφ a = d := (hfoc i₀).2.2 hi₀
  set g : ℝ → ℝ := fun y => (C i₀).φ (a + (y - X)) with hg
  have hgd : HasDerivAt g d X := by
    have h1 : HasDerivAt (fun y : ℝ => a + (y - X)) 1 X :=
      ((hasDerivAt_id X).sub_const X).const_add a
    have h2 : HasDerivAt (C i₀).φ ((C i₀).dφ a) (a + (X - X)) := by
      rw [sub_self, add_zero]; exact foc_hasDerivAt (C i₀).hasDeriv hi₀
    have := h2.comp X h1
    rw [mul_one, hda] at this
    exact this
  have hgX : g X = (C i₀).φ a := by simp [hg]
  have hbdd : ∀ Y, 0 ≤ Y → BddAbove (benefitSet C Y) := fun Y hY =>
    ⟨_, fun s hs => (grossBenefit_isGreatest (optAlloc_foc C hY)).2
      (by rwa [optAlloc_sum C hY])⟩
  refine hasDerivAt_of_sandwich (e₂ := fun _ => 0) (remainder_isLittleO hgd)
    (Asymptotics.isLittleO_zero _ _) ?_
  have hnear : ∀ᶠ y in 𝓝 X, X - a < y := lt_mem_nhds (by linarith)
  filter_upwards [hnear] with y hy
  have ha' : a ≤ X := by
    rw [← optAlloc_sum C hX0]
    exact Finset.single_le_sum (f := optAlloc C X) (fun k _ => (hfoc k).1) (Finset.mem_univ i₀)
  have hy0 : 0 ≤ y := by linarith
  constructor
  · -- lower bound: move `y - X` to consumer `i₀`
    have hmem : ∑ k, (C k).φ (Function.update (optAlloc C X) i₀ (a + (y - X)) k) ∈
        benefitSet C y := by
      refine ⟨_, fun k => ?_, ?_, rfl⟩
      · by_cases hk : k = i₀
        · subst hk; simp only [Function.update_self]; linarith
        · simp only [Function.update_of_ne hk]; exact (hfoc k).1
      · rw [sum_update_id, optAlloc_sum C hX0]; ring
    have hle := le_csSup (hbdd y hy0) hmem
    rw [sum_update_apply (fun k => (C k).φ)] at hle
    rw [grossBenefit_eq C hX0]
    simp only [hgX] at *
    unfold grossBenefit
    simp only [hg] at *
    linarith
  · -- upper bound: the supergradient at `X`
    have := foc_benefit_le hfoc (fun k => (optAlloc_foc C hy0 k).1)
    rw [optAlloc_sum C hy0, optAlloc_sum C hX0] at this
    rw [grossBenefit_eq C hy0, grossBenefit_eq C hX0]
    linarith

/-- **Exercise 10.C.4(c)** (MWG, p. 345). If every consumer maximizes utility facing the price
`P(x)`, aggregate demand is exactly `x`: `P` is the inverse of the aggregate demand function. -/
theorem exercise_10_C_4c [Nonempty ι] (C : ι → QLConsumer) {X : ℝ} (hX : 0 ≤ X) :
    aggDemand C (invDemand C X) = X ∧
      ∀ p, 0 < p → p < maxMB C → invDemand C (aggDemand C p) = p :=
  ⟨aggDemand_invDemand C hX, fun _ hp hpm => invDemand_aggDemand C hp hpm⟩

/-! ## The production side: Exercise 10.C.3 -/

/-- The costs `∑ cⱼ(qⱼ)` of the plans `q ≥ 0` with `∑ qⱼ ≥ Q`. -/
def costSet (F : κ → QLFirm) (Q : ℝ) : Set ℝ :=
  {s | ∃ q : κ → ℝ, (∀ j, 0 ≤ q j) ∧ Q ≤ ∑ j, q j ∧ s = ∑ j, (F j).c (q j)}

/-- **Exercise 10.C.3** (MWG, p. 344; footnote 11, p. 321). The central authority's minimized
cost of producing at least `Q`: `C(Q) = min {∑ cⱼ(qⱼ) : q ≥ 0, ∑ qⱼ ≥ Q}`. -/
noncomputable def minCost (F : κ → QLFirm) (Q : ℝ) : ℝ := sInf (costSet F Q)

/-- The firms' first-order conditions at the common marginal cost `μ`. -/
def IsCostFOC (F : κ → QLFirm) (μ : ℝ) (q : κ → ℝ) : Prop :=
  ∀ j, 0 ≤ q j ∧ μ ≤ (F j).dc (q j) ∧ (0 < q j → μ = (F j).dc (q j))

/-- **Subgradient of the cost.** At plans satisfying the first-order conditions with `μ ≥ 0`,
`∑ cⱼ(q'ⱼ) ≥ ∑ cⱼ(qⱼ) + μ (∑ q'ⱼ - ∑ qⱼ)` for all `q' ≥ 0`. -/
theorem foc_cost_ge {F : κ → QLFirm} {μ : ℝ} {q : κ → ℝ} (hq : IsCostFOC F μ q)
    {q' : κ → ℝ} (hq' : ∀ j, 0 ≤ q' j) :
    ∑ j, (F j).c (q j) + μ * (∑ j, q' j - ∑ j, q j) ≤ ∑ j, (F j).c (q' j) := by
  have h : ∀ j, (F j).c (q j) + μ * (q' j - q j) ≤ (F j).c (q' j) := by
    intro j
    have ht := (F j).le_tangent (hq j).1 (hq' j)
    rcases eq_or_lt_of_le (hq j).1 with h0 | hpos
    · rw [← h0] at ht ⊢
      have := (hq j).2.1
      rw [← h0] at this
      nlinarith [hq' j]
    · rw [← (hq j).2.2 hpos] at ht
      exact ht
  calc ∑ j, (F j).c (q j) + μ * (∑ j, q' j - ∑ j, q j)
      = ∑ j, ((F j).c (q j) + μ * (q' j - q j)) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
    _ ≤ _ := Finset.sum_le_sum fun j _ => h j

/-- Costs are bounded below by `∑ cⱼ(0)`. -/
theorem costSet_lower (F : κ → QLFirm) {Q s : ℝ} (hs : s ∈ costSet F Q) :
    ∑ j, (F j).c 0 ≤ s := by
  obtain ⟨q, hq, -, rfl⟩ := hs
  exact Finset.sum_le_sum fun j _ => (F j).c_strictMono.monotoneOn (Set.mem_Ici.2 le_rfl)
    (Set.mem_Ici.2 (hq j)) (hq j)

/-- Plans satisfying the first-order conditions with `μ ≥ 0` minimize cost. -/
theorem minCost_isLeast {F : κ → QLFirm} {μ : ℝ} (hμ : 0 ≤ μ) {q : κ → ℝ}
    (hq : IsCostFOC F μ q) : IsLeast (costSet F (∑ j, q j)) (∑ j, (F j).c (q j)) := by
  refine ⟨⟨q, fun j => (hq j).1, le_rfl, rfl⟩, ?_⟩
  rintro s ⟨q', hq', hs, rfl⟩
  have := foc_cost_ge hq hq'
  nlinarith

theorem minCost_eq_of_foc {F : κ → QLFirm} {μ : ℝ} (hμ : 0 ≤ μ) {q : κ → ℝ}
    (hq : IsCostFOC F μ q) : minCost F (∑ j, q j) = ∑ j, (F j).c (q j) :=
  (minCost_isLeast hμ hq).csInf_eq

/-- **Exercise 10.C.3(a)** (MWG, p. 344): necessity. If `q ≥ 0` minimizes the cost of producing
at least `Q > 0`, then the constraint binds (`c' > 0`) and there is `μ > 0` with
`μ ≤ cⱼ'(qⱼ)`, equality if `qⱼ > 0`. -/
theorem exercise_10_C_3a (F : κ → QLFirm) {Q : ℝ} (hQ : 0 < Q) {q : κ → ℝ}
    (hq : ∀ j, 0 ≤ q j) (hsum : Q ≤ ∑ j, q j)
    (hmin : ∀ q' : κ → ℝ, (∀ j, 0 ≤ q' j) → Q ≤ ∑ j, q' j →
      ∑ j, (F j).c (q j) ≤ ∑ j, (F j).c (q' j)) :
    ∑ j, q j = Q ∧ ∃ μ, 0 < μ ∧ IsCostFOC F μ q := by
  classical
  -- the constraint binds
  have hbind : ∑ j, q j = Q := by
    by_contra hne
    have hlt : Q < ∑ j, q j := lt_of_le_of_ne hsum (Ne.symm hne)
    obtain ⟨j, hj⟩ := exists_pos_of_sum_pos (hQ.trans hlt)
    set t := min (q j) (∑ k, q k - Q) with ht
    have ht0 : 0 < t := lt_min hj (by linarith)
    have := hmin (Function.update q j (q j - t))
      (fun k => by
        by_cases hk : k = j
        · subst hk; simp only [Function.update_self]; linarith [min_le_left (q k) (∑ k, q k - Q)]
        · simp only [Function.update_of_ne hk]; exact hq k)
      (by rw [sum_update_id]; linarith [min_le_right (q j) (∑ k, q k - Q)])
    rw [sum_update_apply (fun k => (F k).c)] at this
    have := (F j).c_strictMono (Set.mem_Ici.2 (by linarith [min_le_left (q j) (∑ k, q k - Q)]))
      (Set.mem_Ici.2 (hq j)) (by linarith : q j - t < q j)
    linarith
  refine ⟨hbind, ?_⟩
  -- shifting output from an active firm `j` to `k` cannot lower cost
  have hA : ∀ j k, 0 < q j → (F j).dc (q j) ≤ (F k).dc (q k) := by
    intro j k hj
    by_cases hjk : k = j
    · subst hjk; exact le_rfl
    have hpert : ∀ t, 0 ≤ t → t ≤ q j →
        (F j).c (q j) + (F k).c (q k) ≤ (F j).c (q j - t) + (F k).c (q k + t) := by
      intro t ht htq
      have := hmin (Function.update (Function.update q j (q j - t)) k (q k + t))
        (fun l => by
          by_cases hl : l = k
          · subst hl; simp only [Function.update_self]; linarith [hq l]
          · simp only [Function.update_of_ne hl]
            by_cases hl' : l = j
            · subst hl'; simp only [Function.update_self]; linarith
            · simp only [Function.update_of_ne hl']; exact hq l)
        (by
          rw [sum_update_id, sum_update_id, Function.update_of_ne hjk]
          linarith)
      rw [sum_update_apply (fun l => (F l).c), sum_update_apply (fun l => (F l).c),
        Function.update_of_ne hjk] at this
      linarith
    have hd : HasDerivWithinAt (fun t => -((F j).c (q j - t) + (F k).c (q k + t)))
        (-(-(F j).dc (q j) + (F k).dc (q k))) (Set.Ici 0) 0 := by
      have h1 : HasDerivAt (fun t => (F j).c (q j - t)) (-(F j).dc (q j)) 0 :=
        HasDerivAt.comp_const_sub (q j) 0 (by simpa using foc_hasDerivAt (F j).hasDeriv hj)
      exact (h1.hasDerivWithinAt.add (hasDerivWithinAt_shift ((F k).hasDeriv _ (hq k))
        (hq k))).neg
    have := foc_local_necessary hd (by
      filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT hj] with t ht ht'
      have := hpert t (le_of_lt ht) ht'.2.le
      simp only [sub_zero, add_zero]
      linarith)
    linarith
  obtain ⟨j₀, hj₀⟩ := exists_pos_of_sum_pos (hbind ▸ hQ)
  refine ⟨(F j₀).dc (q j₀), (F j₀).dc_pos _ (hq j₀), fun k => ⟨hq k, hA j₀ k hj₀, fun hk => ?_⟩⟩
  exact le_antisymm (hA j₀ k hj₀) (hA k j₀ hk)

/-- **Exercise 10.C.3(a)** (MWG, p. 344): sufficiency. Plans with `∑ qⱼ = Q` satisfying the
first-order conditions minimize cost. -/
theorem exercise_10_C_3a_sufficient {F : κ → QLFirm} {μ : ℝ} (hμ : 0 ≤ μ) {q : κ → ℝ}
    (hq : IsCostFOC F μ q) : minCost F (∑ j, q j) = ∑ j, (F j).c (q j) :=
  minCost_eq_of_foc hμ hq

/-- **Exercise 10.C.3(b)** (MWG, p. 344). At a cost-minimizing plan for `Q > 0` (first-order
conditions with multiplier `μ`), `C` is differentiable with `C'(Q) = μ = cⱼ'(qⱼ*)` for every
active firm. -/
theorem exercise_10_C_3b {F : κ → QLFirm} {μ : ℝ} (hμ : 0 ≤ μ) {q : κ → ℝ}
    (hq : IsCostFOC F μ q) (hQ : 0 < ∑ j, q j) :
    HasDerivAt (minCost F) μ (∑ j, q j) ∧ ∀ j, 0 < q j → μ = (F j).dc (q j) := by
  classical
  refine ⟨?_, fun j hj => (hq j).2.2 hj⟩
  set Q := ∑ j, q j with hQdef
  obtain ⟨j₀, hj₀⟩ := exists_pos_of_sum_pos hQ
  set a := q j₀ with ha
  have hda : (F j₀).dc a = μ := ((hq j₀).2.2 hj₀).symm
  set g : ℝ → ℝ := fun y => (F j₀).c (a + (y - Q)) with hg
  have hgd : HasDerivAt g μ Q := by
    have h1 : HasDerivAt (fun y : ℝ => a + (y - Q)) 1 Q :=
      ((hasDerivAt_id Q).sub_const Q).const_add a
    have h2 : HasDerivAt (F j₀).c ((F j₀).dc a) (a + (Q - Q)) := by
      rw [sub_self, add_zero]; exact foc_hasDerivAt (F j₀).hasDeriv hj₀
    have := h2.comp Q h1
    rw [mul_one, hda] at this
    exact this
  have hgQ : g Q = (F j₀).c a := by simp [hg]
  have hmin := minCost_eq_of_foc hμ hq
  refine hasDerivAt_of_sandwich (e₁ := fun _ => 0) (Asymptotics.isLittleO_zero _ _)
    (remainder_isLittleO hgd) ?_
  have hnear : ∀ᶠ y in 𝓝 Q, Q - a < y := lt_mem_nhds (by linarith)
  filter_upwards [hnear] with y hy
  have hmem : ∑ k, (F k).c (Function.update q j₀ (a + (y - Q)) k) ∈ costSet F y := by
    refine ⟨_, fun k => ?_, ?_, rfl⟩
    · by_cases hk : k = j₀
      · subst hk; simp only [Function.update_self]; linarith
      · simp only [Function.update_of_ne hk]; exact (hq k).1
    · rw [sum_update_id]; linarith
  constructor
  · -- lower bound: the subgradient
    have hlow : ∑ k, (F k).c (q k) + μ * (y - Q) ≤ minCost F y := by
      refine le_csInf ⟨_, hmem⟩ ?_
      rintro s ⟨q', hq', hs, rfl⟩
      have := foc_cost_ge hq hq'
      nlinarith
    rw [hmin]
    linarith
  · -- upper bound: produce the change at firm `j₀`
    have hup := csInf_le ⟨_, fun s hs => costSet_lower F hs⟩ hmem
    rw [sum_update_apply (fun k => (F k).c)] at hup
    change minCost F y ≤ _ at hup
    rw [hmin]
    simp only [hg] at *
    linarith

omit [Fintype κ] in
/-- **Exercise 10.C.3(c)** (MWG, p. 344). Facing `p = C'(Q) = μ`, every firm's cost-minimizing
output `qⱼ*` maximizes its profit, so these choices produce `Q` in aggregate. -/
theorem exercise_10_C_3c {F : κ → QLFirm} {μ : ℝ} {q : κ → ℝ} (hq : IsCostFOC F μ q) (j : κ)
    (q' : ℝ) (hq' : 0 ≤ q') : μ * q' - (F j).c q' ≤ μ * q j - (F j).c (q j) :=
  ((F j).max_iff (hq j).1).2 (hq j).2 q' hq'

/-! ## Industry supply and the industry marginal cost (Figure 10.C.5) -/

/-- `minⱼ cⱼ'(0)`. -/
noncomputable def minMC [Nonempty κ] (F : κ → QLFirmStrict) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty fun j => (F j).dc 0

theorem minMC_le [Nonempty κ] (F : κ → QLFirmStrict) (j : κ) : minMC F ≤ (F j).dc 0 :=
  Finset.inf'_le (fun j => (F j).dc 0) (Finset.mem_univ j)

theorem exists_eq_minMC [Nonempty κ] (F : κ → QLFirmStrict) : ∃ j, (F j).dc 0 = minMC F := by
  obtain ⟨j, -, h⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (fun j => (F j).dc 0)
  exact ⟨j, h.symm⟩

theorem minMC_pos [Nonempty κ] (F : κ → QLFirmStrict) : 0 < minMC F := by
  obtain ⟨j, hj⟩ := exists_eq_minMC F
  rw [← hj]
  exact (F j).toQLFirm.dc_pos 0 le_rfl

theorem exists_lt_of_aggSupply_pos (F : κ → QLFirmStrict) {p : ℝ}
    (h : 0 < aggSupply F p) : ∃ j, (F j).dc 0 < p := by
  by_contra hno
  push Not at hno
  rw [(aggSupply_eq_zero_iff F p).2 hno] at h
  exact lt_irrefl 0 h

/-- The price at which industry supply equals a given `Q ≥ 0` exists. -/
theorem exists_invSupply [Nonempty κ] (F : κ → QLFirmStrict) (Q : ℝ) :
    ∃ μ, 0 ≤ Q → minMC F ≤ μ ∧ aggSupply F μ = Q ∧ (Q = 0 → μ = minMC F) := by
  by_cases hQ : 0 ≤ Q
  · rcases eq_or_lt_of_le hQ with h0 | hpos
    · refine ⟨minMC F, fun _ => ⟨le_rfl, ?_, fun _ => rfl⟩⟩
      rw [← h0]
      exact (aggSupply_eq_zero_iff F _).2 fun j => minMC_le F j
    · obtain ⟨j₀⟩ := ‹Nonempty κ›
      set hi := (F j₀).dc Q with hhi
      have hshi : (F j₀).supply hi = Q := (F j₀).supply_eq ⟨hQ, le_rfl, fun _ => rfl⟩
      have hge : Q ≤ aggSupply F hi := by
        rw [← hshi]
        exact Finset.single_le_sum (f := fun j => (F j).supply hi)
          (fun j _ => (F j).supply_nonneg hi) (Finset.mem_univ j₀)
      have hlohi : minMC F ≤ hi := (minMC_le F j₀).trans
        ((F j₀).dc_strictMono.monotoneOn (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hQ) hQ)
      have hlo : aggSupply F (minMC F) = 0 :=
        (aggSupply_eq_zero_iff F _).2 fun j => minMC_le F j
      obtain ⟨μ, hμ, hμQ⟩ := intermediate_value_Icc hlohi
        (aggSupply_continuous F).continuousOn ⟨by rw [hlo]; exact hQ, hge⟩
      exact ⟨μ, fun _ => ⟨hμ.1, hμQ, fun h => absurd h hpos.ne'⟩⟩
  · exact ⟨0, fun h => absurd h hQ⟩

/-- **The inverse industry supply function** `q⁻¹(Q)` (MWG, p. 321), with `q⁻¹(0) = minⱼ cⱼ'(0)`;
by `invSupply_hasDerivAt` it is the industry marginal cost `C'(Q)`. -/
noncomputable def invSupply [Nonempty κ] (F : κ → QLFirmStrict) (Q : ℝ) : ℝ :=
  Classical.choose (exists_invSupply F Q)

theorem invSupply_spec [Nonempty κ] (F : κ → QLFirmStrict) {Q : ℝ} (hQ : 0 ≤ Q) :
    minMC F ≤ invSupply F Q ∧ aggSupply F (invSupply F Q) = Q ∧
      (Q = 0 → invSupply F Q = minMC F) :=
  Classical.choose_spec (exists_invSupply F Q) hQ

theorem aggSupply_invSupply [Nonempty κ] (F : κ → QLFirmStrict) {Q : ℝ} (hQ : 0 ≤ Q) :
    aggSupply F (invSupply F Q) = Q := (invSupply_spec F hQ).2.1

theorem invSupply_pos [Nonempty κ] (F : κ → QLFirmStrict) {Q : ℝ} (hQ : 0 ≤ Q) :
    0 < invSupply F Q := (minMC_pos F).trans_le (invSupply_spec F hQ).1

/-- For `Q > 0`, `q⁻¹(Q)` is the unique price with industry supply `Q`. -/
theorem invSupply_unique [Nonempty κ] (F : κ → QLFirmStrict) {Q μ : ℝ} (hQ : 0 < Q)
    (h : aggSupply F μ = Q) : invSupply F Q = μ := by
  have hP := invSupply_spec F hQ.le
  have key : ∀ p₁ p₂, p₁ < p₂ → aggSupply F p₁ = Q → aggSupply F p₂ = Q → False := by
    intro p₁ p₂ h₁₂ e₁ e₂
    have := aggSupply_strictMono F h₁₂ (exists_lt_of_aggSupply_pos F (e₂ ▸ hQ))
    linarith
  rcases lt_trichotomy (invSupply F Q) μ with hlt | heq | hgt
  · exact (key _ _ hlt hP.2.1 h).elim
  · exact heq
  · exact (key _ _ hgt h hP.2.1).elim

/-- **(MWG, p. 321)** `q⁻¹(q(p)) = p` for `p > minⱼ cⱼ'(0)`. -/
theorem invSupply_aggSupply [Nonempty κ] (F : κ → QLFirmStrict) {p : ℝ} (hp : minMC F < p) :
    invSupply F (aggSupply F p) = p := by
  obtain ⟨j, hj⟩ := exists_eq_minMC F
  have hpos : 0 < aggSupply F p :=
    Finset.sum_pos' (fun k _ => (F k).supply_nonneg p)
      ⟨j, Finset.mem_univ j, ((F j).supply_pos_iff p).2 (hj ▸ hp)⟩
  exact invSupply_unique F hpos rfl

/-- The industry marginal cost is strictly increasing on `Q ≥ 0`. -/
theorem invSupply_strictMonoOn [Nonempty κ] (F : κ → QLFirmStrict) :
    StrictMonoOn (invSupply F) (Set.Ici 0) := by
  intro Q₁ h₁ Q₂ h₂ h₁₂
  have h₁' : (0 : ℝ) ≤ Q₁ := h₁
  have h₂' : (0 : ℝ) ≤ Q₂ := h₂
  refine lt_of_le_of_ne ?_ fun heq => ?_
  · by_contra hlt
    push Not at hlt
    have := aggSupply_monotone F hlt.le
    rw [aggSupply_invSupply F h₁', aggSupply_invSupply F h₂'] at this
    linarith
  · have e₁ := aggSupply_invSupply F h₁'
    have e₂ := aggSupply_invSupply F h₂'
    rw [heq] at e₁
    linarith

theorem invSupply_monotoneOn [Nonempty κ] (F : κ → QLFirmStrict) :
    MonotoneOn (invSupply F) (Set.Ici 0) := (invSupply_strictMonoOn F).monotoneOn

/-- The cost-minimizing plan for `Q`: each firm's supply at `q⁻¹(Q)`. -/
noncomputable def optPlan [Nonempty κ] (F : κ → QLFirmStrict) (Q : ℝ) (j : κ) : ℝ :=
  (F j).supply (invSupply F Q)

theorem optPlan_foc [Nonempty κ] (F : κ → QLFirmStrict) (Q : ℝ) :
    IsCostFOC (fun j => (F j).toQLFirm) (invSupply F Q) (optPlan F Q) :=
  fun j => (F j).supply_foc _

theorem optPlan_sum [Nonempty κ] (F : κ → QLFirmStrict) {Q : ℝ} (hQ : 0 ≤ Q) :
    ∑ j, optPlan F Q j = Q := aggSupply_invSupply F hQ

/-- `C(Q) = ∑ cⱼ(qⱼ*(Q))`. -/
theorem minCost_eq [Nonempty κ] (F : κ → QLFirmStrict) {Q : ℝ} (hQ : 0 ≤ Q) :
    minCost (fun j => (F j).toQLFirm) Q = ∑ j, (F j).c (optPlan F Q j) := by
  have := minCost_eq_of_foc (invSupply_pos F hQ).le (optPlan_foc F Q)
  rwa [optPlan_sum F hQ] at this

/-- **Footnotes 11-12, Figure 10.C.5** (MWG, p. 321). The industry marginal cost `C'(Q)` (the
derivative of the central authority's cost function) equals the inverse of the industry supply
function: `C' = q⁻¹` on `Q > 0`. -/
theorem invSupply_hasDerivAt [Nonempty κ] (F : κ → QLFirmStrict) {Q : ℝ} (hQ : 0 < Q) :
    HasDerivAt (minCost fun j => (F j).toQLFirm) (invSupply F Q) Q := by
  have h := (exercise_10_C_3b (invSupply_pos F hQ.le).le (optPlan_foc F Q)
    (by rw [optPlan_sum F hQ.le]; exact hQ)).1
  rwa [optPlan_sum F hQ.le] at h

/-- **Exercise 10.C.3(c)** (MWG, p. 344), strictly convex case: facing `p = C'(Q)` firms supply
exactly `Q` in aggregate, so `C'` is the inverse of the industry supply function. -/
theorem exercise_10_C_3c_strict [Nonempty κ] (F : κ → QLFirmStrict) {Q : ℝ} (hQ : 0 < Q) :
    HasDerivAt (minCost fun j => (F j).toQLFirm) (invSupply F Q) Q ∧
      aggSupply F (invSupply F Q) = Q :=
  ⟨invSupply_hasDerivAt F hQ, aggSupply_invSupply F hQ.le⟩

theorem minCost_zero [Nonempty κ] (F : κ → QLFirmStrict) :
    minCost (fun j => (F j).toQLFirm) 0 = ∑ j, (F j).c 0 := by
  have := minCost_eq F (le_refl (0 : ℝ))
  rw [this]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h0 : optPlan F 0 j = 0 := by
    have hs := optPlan_sum F (le_refl (0 : ℝ))
    exact (Finset.sum_eq_zero_iff_of_nonneg fun k _ => (F k).supply_nonneg _).1 hs j
      (Finset.mem_univ j)
  rw [h0]

end MWG.CompetitiveMarkets
