/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGCompetitiveMarkets.CentralAuthority
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Welfare analysis in the partial equilibrium model (MWG Section 10.E, pp. 328-334)

* pp. 328-329 and footnote 17: with optimal lump-sum redistribution of the numeraire, welfare
  rises iff Marshallian aggregate surplus rises, for every (strictly increasing) social welfare
  function (`welfare_lt_iff_surplus_lt`); for the utilitarian `W = ∑ uᵢ` no transfers are
  needed. The potential Pareto improvement criterion (p. 334).
* (10.E.2)-(10.E.4) (p. 330): `dS = [P(x) - C'(x)] dx` along changes keeping the allocations
  optimal.
* (10.E.5) (p. 330): `S(x) = S₀ + ∫₀ˣ [P(s) - C'(s)] ds`, with `S₀ = -∑ cⱼ(0)` (zero when
  `cⱼ(0) = 0`), for the aggregate surplus at optimal distribution (`aggSurplus`).
* Footnote 19 (p. 331): `S` is concave, `S' = P - C'`, and `x* > 0` maximizes `S` iff
  `P(x*) = C'(x*)`, the competitive aggregate.
* Example 10.E.1 (pp. 331-333): the deadweight loss `S*(t) - S*(0) = ∫_{x*(0)}^{x*(t)} [P - C']`
  is negative (`deadweight_loss_neg`); consumer surplus (10.E.7)-(10.E.9), producer surplus
  (10.E.10)-(10.E.12), via envelope theorems `CS'(p) = -x(p)`, `Π'(p) = q(p)`.
* **Exercise 10.E.2** (p. 346): `∫₀^{x(p)} [P(s) - p] ds = ∫_p^∞ x(s) ds`.
-/

namespace MWG.CompetitiveMarkets

open Filter Topology MeasureTheory

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-! ## Social welfare and aggregate surplus (pp. 328-329) -/

/-- The utility vectors attainable by redistributing the numeraire when aggregate surplus plus
the numeraire endowment equals `s` (expression (10.D.1)). -/
def redistributionSet (s : ℝ) : Set (ι → ℝ) := {u | ∑ i, u i ≤ s}

/-- **(MWG, pp. 328-329)** With a central authority redistributing the numeraire to maximize a
social welfare function `W` that is strictly increasing (raising every utility raises `W`), the
maximized welfare is higher iff `ω_m + S` is higher: changes in welfare are measured by changes
in Marshallian aggregate surplus, for any such `W`. -/
theorem welfare_lt_iff_surplus_lt [Nonempty ι] (W : (ι → ℝ) → ℝ)
    (hW : ∀ u v : ι → ℝ, (∀ i, u i < v i) → W u < W v) {s₀ s₁ V₀ V₁ : ℝ}
    (h₀ : IsGreatest (W '' redistributionSet s₀) V₀)
    (h₁ : IsGreatest (W '' redistributionSet s₁) V₁) : V₀ < V₁ ↔ s₀ < s₁ := by
  constructor
  · intro hlt
    by_contra hle
    push Not at hle
    obtain ⟨u, hu, rfl⟩ := h₁.1
    have : W u ≤ V₀ := h₀.2 ⟨u, (show ∑ i, u i ≤ s₀ from le_trans hu hle), rfl⟩
    linarith
  · intro hlt
    obtain ⟨u, hu, rfl⟩ := h₀.1
    have hn : (0 : ℝ) < (Fintype.card ι : ℝ) := Nat.cast_pos.2 Fintype.card_pos
    set n : ℝ := (Fintype.card ι : ℝ)
    set δ := (s₁ - s₀) / n
    have hδ : 0 < δ := div_pos (by linarith) hn
    have hmem : (fun i => u i + δ) ∈ redistributionSet (ι := ι) s₁ := by
      change ∑ i, (u i + δ) ≤ s₁
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have : (Fintype.card ι : ℝ) * δ = s₁ - s₀ := by
        change n * ((s₁ - s₀) / n) = _; field_simp
      have hu' : ∑ i, u i ≤ s₀ := hu
      linarith
    exact (hW u _ fun i => by linarith).trans_le (h₁.2 ⟨_, hmem, rfl⟩)

/-- **Footnote 17** (MWG, p. 329). For the utilitarian `W = ∑ uᵢ` the maximized welfare is `s`
itself, attained by any distribution that wastes nothing: no transfers are necessary. -/
theorem footnote_10_E_17 (s : ℝ) {u : ι → ℝ} (hu : ∑ i, u i = s) :
    IsGreatest ((fun v : ι → ℝ => ∑ i, v i) '' redistributionSet s) s :=
  ⟨⟨u, hu.le, hu⟩, by rintro _ ⟨v, hv, rfl⟩; exact hv⟩

/-- **Potential Pareto improvement** (MWG, p. 334). Starting from utilities `u⁰` with no waste,
some redistribution of the numeraire after a change makes every consumer strictly better off
iff the new value of `ω_m + S` exceeds `∑ u⁰ᵢ`, i.e. iff aggregate surplus increases. -/
theorem potential_pareto_iff [Nonempty ι] (u₀ : ι → ℝ) (s₁ : ℝ) :
    (∃ u ∈ redistributionSet (ι := ι) s₁, ∀ i, u₀ i < u i) ↔ ∑ i, u₀ i < s₁ := by
  constructor
  · rintro ⟨u, hu, hlt⟩
    exact (Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ => hlt i).trans_le hu
  · intro hlt
    have hn : (0 : ℝ) < (Fintype.card ι : ℝ) := Nat.cast_pos.2 Fintype.card_pos
    set n : ℝ := (Fintype.card ι : ℝ)
    set δ := (s₁ - ∑ i, u₀ i) / n
    have hδ : 0 < δ := div_pos (by linarith) hn
    refine ⟨fun i => u₀ i + δ, ?_, fun i => by linarith⟩
    change ∑ i, (u₀ i + δ) ≤ s₁
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have : (Fintype.card ι : ℝ) * δ = s₁ - ∑ i, u₀ i := by
      change n * ((s₁ - ∑ i, u₀ i) / n) = _; field_simp
    linarith

/-! ## Differential changes (10.E.2)-(10.E.4) -/

/-- **(10.E.2)-(10.E.4)** (MWG, p. 330). If consumption is distributed optimally
(`φᵢ'(xᵢ) = P` for all `i`) and production too (`cⱼ'(qⱼ) = C'` for all `j`), then along a
differential change `(dx, dq)` with `∑ dxᵢ = ∑ dqⱼ = dx` the aggregate surplus changes at rate
`[P - C'] dx`. -/
theorem eq_10_E_4 (C : ι → QLConsumer) (F : κ → QLFirm) {x : ι → ℝ} {q : κ → ℝ}
    (hx : ∀ i, 0 < x i) (hq : ∀ j, 0 < q j) {P MC : ℝ} (hP : ∀ i, (C i).dφ (x i) = P)
    (hMC : ∀ j, (F j).dc (q j) = MC) (dx : ι → ℝ) (dq : κ → ℝ) (hd : ∑ j, dq j = ∑ i, dx i) :
    HasDerivAt (fun t => qlSurplus (fun i => (C i).φ) (fun j => (F j).c)
      (fun i => x i + t * dx i) (fun j => q j + t * dq j)) ((P - MC) * ∑ i, dx i) 0 := by
  have hφ : ∀ i, HasDerivAt (fun t => (C i).φ (x i + t * dx i)) ((C i).dφ (x i) * dx i) 0 := by
    intro i
    have h1 : HasDerivAt (fun t : ℝ => x i + t * dx i) (dx i) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (dx i)).const_add (x i)
    have h2 : HasDerivAt (C i).φ ((C i).dφ (x i)) (x i + 0 * dx i) := by
      rw [zero_mul, add_zero]; exact foc_hasDerivAt (C i).hasDeriv (hx i)
    exact h2.comp 0 h1
  have hc : ∀ j, HasDerivAt (fun t => (F j).c (q j + t * dq j)) ((F j).dc (q j) * dq j) 0 := by
    intro j
    have h1 : HasDerivAt (fun t : ℝ => q j + t * dq j) (dq j) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (dq j)).const_add (q j)
    have h2 : HasDerivAt (F j).c ((F j).dc (q j)) (q j + 0 * dq j) := by
      rw [zero_mul, add_zero]; exact foc_hasDerivAt (F j).hasDeriv (hq j)
    exact h2.comp 0 h1
  have h := (HasDerivAt.sum (u := Finset.univ) fun i _ => hφ i).sub
    (HasDerivAt.sum (u := Finset.univ) fun j _ => hc j)
  simp only [hP, hMC, ← Finset.mul_sum, hd] at h
  convert h using 1
  · ext t; simp [qlSurplus]
  · ring

/-! ## Aggregate surplus at optimal distribution (10.E.5) -/

/-- **(10.E.5)** (MWG, p. 330). Aggregate surplus at aggregate consumption `x` when consumption
and production are distributed optimally: `S(x) = γ(x) - C(x)`. -/
noncomputable def aggSurplus (C : ι → QLConsumer) (F : κ → QLFirmStrict) (X : ℝ) : ℝ :=
  grossBenefit C X - minCost (fun j => (F j).toQLFirm) X

/-- `γ` is continuous from the right at `0`: `0 ≤ γ(h) ≤ maxᵢ φᵢ'(0) · h`. -/
theorem grossBenefit_continuousWithinAt_zero [Nonempty ι] (C : ι → QLConsumer) :
    ContinuousWithinAt (grossBenefit C) (Set.Ici 0) 0 := by
  have hlow : ∀ h ∈ Set.Ici (0 : ℝ), 0 ≤ grossBenefit C h := by
    intro h hh
    rw [grossBenefit_eq C hh]
    exact Finset.sum_nonneg fun i _ => by
      have := (C i).φ_strictMono.monotoneOn (Set.mem_Ici.2 le_rfl)
        (Set.mem_Ici.2 (optAlloc_foc C hh i).1) (optAlloc_foc C hh i).1
      rwa [(C i).φ_zero] at this
  have hup : ∀ h ∈ Set.Ici (0 : ℝ), grossBenefit C h ≤ maxMB C * h := by
    intro h hh
    have := foc_benefit_le (C := C) (x := fun _ => 0) (μ := maxMB C)
      (fun i => ⟨le_rfl, le_maxMB C i, fun h => absurd h (lt_irrefl 0)⟩)
      (fun i => (optAlloc_foc C hh i).1)
    rw [optAlloc_sum C hh] at this
    rw [grossBenefit_eq C hh]
    simpa [QLConsumer.φ_zero] using this
  rw [ContinuousWithinAt, grossBenefit_zero]
  have ht : Tendsto (fun h => maxMB C * h) (𝓝[Set.Ici 0] 0) (𝓝 0) := by
    have : Tendsto (fun h => maxMB C * h) (𝓝 (0 : ℝ)) (𝓝 (maxMB C * 0)) :=
      (continuous_const.mul continuous_id).continuousAt
    rw [mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
    (eventually_nhdsWithin_of_forall hlow) (eventually_nhdsWithin_of_forall hup)

/-- `C` is continuous from the right at `0`. -/
theorem minCost_continuousWithinAt_zero [Nonempty κ] (F : κ → QLFirmStrict) :
    ContinuousWithinAt (minCost fun j => (F j).toQLFirm) (Set.Ici 0) 0 := by
  classical
  obtain ⟨j₀⟩ := ‹Nonempty κ›
  have hlow : ∀ h ∈ Set.Ici (0 : ℝ),
      minCost (fun j => (F j).toQLFirm) 0 ≤ minCost (fun j => (F j).toQLFirm) h := by
    intro h hh
    rw [minCost_zero, minCost_eq F hh]
    exact Finset.sum_le_sum fun j _ => (F j).toQLFirm.c_strictMono.monotoneOn
      (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 ((F j).supply_nonneg _)) ((F j).supply_nonneg _)
  have hup : ∀ h ∈ Set.Ici (0 : ℝ), minCost (fun j => (F j).toQLFirm) h ≤
      minCost (fun j => (F j).toQLFirm) 0 + ((F j₀).c h - (F j₀).c 0) := by
    intro h hh
    have hmem : ∑ k, (F k).c (Function.update (fun _ => (0 : ℝ)) j₀ h k) ∈
        costSet (fun j => (F j).toQLFirm) h := by
      refine ⟨_, fun k => ?_, ?_, rfl⟩
      · by_cases hk : k = j₀
        · subst hk; simp only [Function.update_self]; exact hh
        · simp only [Function.update_of_ne hk]; exact le_rfl
      · rw [sum_update_id]; simp
    have := csInf_le ⟨_, fun s hs => costSet_lower _ hs⟩ hmem
    rw [sum_update_apply (fun k => (F k).c)] at this
    rw [minCost_zero]
    exact this
  have hc : Tendsto (fun h => minCost (fun j => (F j).toQLFirm) 0 + ((F j₀).c h - (F j₀).c 0))
      (𝓝[Set.Ici 0] 0) (𝓝 (minCost (fun j => (F j).toQLFirm) 0)) := by
    have := ((F j₀).toQLFirm.c_continuousOn 0 (Set.mem_Ici.2 le_rfl)).sub
      (continuousWithinAt_const (b := (F j₀).c 0))
    have h2 := (this.const_add (minCost (fun j => (F j).toQLFirm) 0)).tendsto
    convert h2 using 2
    simp
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hc
    (eventually_nhdsWithin_of_forall hlow) (eventually_nhdsWithin_of_forall hup)

theorem aggSurplus_hasDerivAt [Nonempty ι] [Nonempty κ] (C : ι → QLConsumer)
    (F : κ → QLFirmStrict) {X : ℝ} (hX : 0 < X) :
    HasDerivAt (aggSurplus C F) (invDemand C X - invSupply F X) X :=
  (exercise_10_C_4b C hX).1.sub (invSupply_hasDerivAt F hX)

theorem aggSurplus_continuousOn [Nonempty ι] [Nonempty κ] (C : ι → QLConsumer)
    (F : κ → QLFirmStrict) : ContinuousOn (aggSurplus C F) (Set.Ici 0) := by
  intro X hX
  rcases eq_or_lt_of_le (Set.mem_Ici.1 hX) with h0 | hpos
  · subst h0
    exact (grossBenefit_continuousWithinAt_zero C).sub (minCost_continuousWithinAt_zero F)
  · exact (aggSurplus_hasDerivAt C F hpos).continuousAt.continuousWithinAt

theorem invDemand_intervalIntegrable [Nonempty ι] (C : ι → QLConsumer) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) : IntervalIntegrable (invDemand C) volume a b :=
  ((invDemand_antitoneOn C).mono fun _ hy =>
    Set.mem_Ici.2 (le_trans (le_min ha hb) hy.1)).intervalIntegrable

theorem invSupply_intervalIntegrable [Nonempty κ] (F : κ → QLFirmStrict) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) : IntervalIntegrable (invSupply F) volume a b :=
  ((invSupply_monotoneOn F).mono fun _ hy =>
    Set.mem_Ici.2 (le_trans (le_min ha hb) hy.1)).intervalIntegrable

/-- **(10.E.5)** (MWG, p. 330). `S(x) = S₀ + ∫₀ˣ [P(s) - C'(s)] ds`, with
`S₀ = S(0) = -∑ⱼ cⱼ(0)`. -/
theorem eq_10_E_5 [Nonempty ι] [Nonempty κ] (C : ι → QLConsumer) (F : κ → QLFirmStrict)
    {X : ℝ} (hX : 0 ≤ X) :
    aggSurplus C F X = aggSurplus C F 0 + ∫ s in (0 : ℝ)..X, (invDemand C s - invSupply F s) ∧
      aggSurplus C F 0 = -∑ j, (F j).c 0 := by
  refine ⟨?_, by simp [aggSurplus, grossBenefit_zero, minCost_zero]⟩
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hX
    ((aggSurplus_continuousOn C F).mono Set.Icc_subset_Ici_self)
    (fun x hx => aggSurplus_hasDerivAt C F hx.1)
    ((invDemand_intervalIntegrable C le_rfl hX).sub (invSupply_intervalIntegrable F le_rfl hX))]
  ring

/-- `S₀ = 0` when every `cⱼ(0) = 0` (MWG, p. 331). -/
theorem aggSurplus_zero_of_cost_zero [Nonempty ι] [Nonempty κ] (C : ι → QLConsumer)
    (F : κ → QLFirmStrict) (h0 : ∀ j, (F j).c 0 = 0) : aggSurplus C F 0 = 0 := by
  rw [(eq_10_E_5 C F le_rfl).2]
  simp [h0]

/-- `γ(x) = ∫₀ˣ P(s) ds`: the area under the inverse demand curve. -/
theorem grossBenefit_eq_integral [Nonempty ι] (C : ι → QLConsumer) {X : ℝ} (hX : 0 ≤ X) :
    grossBenefit C X = ∫ s in (0 : ℝ)..X, invDemand C s := by
  have hcont : ContinuousOn (grossBenefit C) (Set.Icc 0 X) := by
    intro y hy
    rcases eq_or_lt_of_le hy.1 with h0 | hpos
    · subst h0
      exact (grossBenefit_continuousWithinAt_zero C).mono Set.Icc_subset_Ici_self
    · exact (exercise_10_C_4b C hpos).1.continuousAt.continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hX hcont
    (fun x hx => (exercise_10_C_4b C hx.1).1) (invDemand_intervalIntegrable C le_rfl hX),
    grossBenefit_zero, sub_zero]

/-- `C(q) = C(0) + ∫₀^q C'(s) ds`. -/
theorem minCost_eq_integral [Nonempty κ] (F : κ → QLFirmStrict) {Q : ℝ} (hQ : 0 ≤ Q) :
    minCost (fun j => (F j).toQLFirm) Q =
      minCost (fun j => (F j).toQLFirm) 0 + ∫ s in (0 : ℝ)..Q, invSupply F s := by
  have hcont : ContinuousOn (minCost fun j => (F j).toQLFirm) (Set.Icc 0 Q) := by
    intro y hy
    rcases eq_or_lt_of_le hy.1 with h0 | hpos
    · subst h0
      exact (minCost_continuousWithinAt_zero F).mono Set.Icc_subset_Ici_self
    · exact (invSupply_hasDerivAt F hpos).continuousAt.continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hQ hcont
    (fun x hx => invSupply_hasDerivAt F hx.1) (invSupply_intervalIntegrable F le_rfl hQ)]
  ring

/-- **Footnote 19** (MWG, p. 331). `S` is concave on `x ≥ 0`. -/
theorem footnote_10_E_19_concave [Nonempty ι] [Nonempty κ] (C : ι → QLConsumer)
    (F : κ → QLFirmStrict) : ConcaveOn ℝ (Set.Ici 0) (aggSurplus C F) := by
  refine AntitoneOn.concaveOn_of_deriv (convex_Ici 0) (aggSurplus_continuousOn C F) ?_ ?_
  · rw [interior_Ici]
    exact fun x hx => (aggSurplus_hasDerivAt C F hx).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]
    intro x hx y hy hxy
    rw [(aggSurplus_hasDerivAt C F hx).deriv, (aggSurplus_hasDerivAt C F hy).deriv]
    have h1 := invDemand_antitoneOn C (Set.mem_Ici.2 (le_of_lt hx)) (Set.mem_Ici.2
      (le_of_lt hy)) hxy
    have h2 := invSupply_monotoneOn F (Set.mem_Ici.2 (le_of_lt hx)) (Set.mem_Ici.2
      (le_of_lt hy)) hxy
    linarith

/-- **Footnote 19** (MWG, p. 331). `x* > 0` maximizes aggregate surplus on `x ≥ 0` iff
`S'(x*) = P(x*) - C'(x*) = 0`. -/
theorem footnote_10_E_19 [Nonempty ι] [Nonempty κ] (C : ι → QLConsumer) (F : κ → QLFirmStrict)
    {X : ℝ} (hX : 0 < X) :
    (∀ y, 0 ≤ y → aggSurplus C F y ≤ aggSurplus C F X) ↔ invDemand C X = invSupply F X := by
  have hd := aggSurplus_hasDerivAt C F hX
  constructor
  · intro hmax
    have hloc : IsLocalMax (aggSurplus C F) X := by
      filter_upwards [Ioi_mem_nhds hX] with y hy
      exact hmax y (le_of_lt hy)
    have := hloc.hasDerivAt_eq_zero hd
    linarith
  · intro heq y hy
    have hcont := aggSurplus_continuousOn C F
    rcases le_total y X with hyX | hXy
    · have hmono : MonotoneOn (aggSurplus C F) (Set.Icc 0 X) := by
        refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 X)
          (hcont.mono Set.Icc_subset_Ici_self)
          (fun z hz => by
            rw [interior_Icc] at hz
            exact (aggSurplus_hasDerivAt C F hz.1).hasDerivWithinAt) ?_
        intro z hz
        rw [interior_Icc] at hz
        have h1 := invDemand_antitoneOn C (Set.mem_Ici.2 hz.1.le) (Set.mem_Ici.2 hX.le) hz.2.le
        have h2 := invSupply_monotoneOn F (Set.mem_Ici.2 hz.1.le) (Set.mem_Ici.2 hX.le) hz.2.le
        linarith
      exact hmono ⟨hy, hyX⟩ ⟨hX.le, le_rfl⟩ hyX
    · have hanti : AntitoneOn (aggSurplus C F) (Set.Ici X) := by
        refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici X)
          (hcont.mono fun z hz => Set.mem_Ici.2 (hX.le.trans hz))
          (fun z hz => by
            rw [interior_Ici] at hz
            exact (aggSurplus_hasDerivAt C F (hX.trans hz)).hasDerivWithinAt) ?_
        intro z hz
        rw [interior_Ici] at hz
        have h1 := invDemand_antitoneOn C (Set.mem_Ici.2 hX.le)
          (Set.mem_Ici.2 (hX.trans hz).le) hz.le
        have h2 := invSupply_monotoneOn F (Set.mem_Ici.2 hX.le)
          (Set.mem_Ici.2 (hX.trans hz).le) hz.le
        linarith
      exact hanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hXy) hXy

/-- **(MWG, p. 331)** The competitive aggregate `x* = x(p*) = q(p*) > 0` satisfies
`P(x*) = p* = C'(x*)`, so it maximizes aggregate surplus. -/
theorem competitive_maximizes_surplus [Nonempty ι] [Nonempty κ] (C : ι → QLConsumer)
    (F : κ → QLFirmStrict) {p : ℝ} (hp : 0 < p) (hX : 0 < aggDemand C p)
    (hclear : aggDemand C p = aggSupply F p) :
    invDemand C (aggDemand C p) = p ∧ invSupply F (aggDemand C p) = p ∧
      ∀ y, 0 ≤ y → aggSurplus C F y ≤ aggSurplus C F (aggDemand C p) := by
  have h1 := invDemand_unique C hX hp rfl
  have h2 := invSupply_unique F hX hclear.symm
  exact ⟨h1, h2, (footnote_10_E_19 C F hX).2 (h1.trans h2.symm)⟩

/-- **Example 10.E.1** (MWG, p. 332), (10.E.6). If aggregate consumption falls from the
competitive level `x₀` (where `P(x₀) = C'(x₀)`) to `x₁ < x₀`, the change in aggregate surplus
is `∫_{x₀}^{x₁} [P - C'] < 0`: the deadweight loss. -/
theorem deadweight_loss_neg [Nonempty ι] [Nonempty κ] (C : ι → QLConsumer)
    (F : κ → QLFirmStrict) {X₀ X₁ : ℝ} (h₁ : 0 ≤ X₁) (h₁₀ : X₁ < X₀)
    (heq : invDemand C X₀ = invSupply F X₀) :
    aggSurplus C F X₁ - aggSurplus C F X₀ =
        ∫ s in X₀..X₁, (invDemand C s - invSupply F s) ∧
      aggSurplus C F X₁ - aggSurplus C F X₀ < 0 := by
  have h₀ : 0 ≤ X₀ := h₁.trans h₁₀.le
  have hint : ∀ a b, 0 ≤ a → 0 ≤ b →
      IntervalIntegrable (fun s => invDemand C s - invSupply F s) volume a b :=
    fun a b ha hb => (invDemand_intervalIntegrable C ha hb).sub
      (invSupply_intervalIntegrable F ha hb)
  have hdiff : aggSurplus C F X₁ - aggSurplus C F X₀ =
      ∫ s in X₀..X₁, (invDemand C s - invSupply F s) := by
    rw [(eq_10_E_5 C F h₁).1, (eq_10_E_5 C F h₀).1, add_sub_add_left_eq_sub,
      intervalIntegral.integral_interval_sub_left (hint 0 X₁ le_rfl h₁) (hint 0 X₀ le_rfl h₀)]
  refine ⟨hdiff, ?_⟩
  rw [hdiff, intervalIntegral.integral_symm, neg_lt_zero]
  refine intervalIntegral.intervalIntegral_pos_of_pos_on (hint X₁ X₀ h₁ h₀) (fun s hs => ?_) h₁₀
  have hs0 : 0 ≤ s := h₁.trans hs.1.le
  have hP := invDemand_strictAntiOn C (Set.mem_Ici.2 hs0) (Set.mem_Ici.2 h₀) hs.2
  have hC := invSupply_monotoneOn F (Set.mem_Ici.2 hs0) (Set.mem_Ici.2 h₀) hs.2.le
  linarith

/-! ## Consumer and producer surplus -/

/-- **(MWG, p. 332)** Aggregate consumer surplus at effective price `p̂`:
`CS(p̂) = ∑ φᵢ(xᵢ(p̂)) - p̂ x(p̂)`. -/
noncomputable def consumerSurplus (C : ι → QLConsumer) (p : ℝ) : ℝ :=
  ∑ i, (C i).φ ((C i).demand p) - p * aggDemand C p

/-- **(MWG, p. 333)** Aggregate producer surplus (profit) at effective price `p̂`:
`Π(p̂) = p̂ q(p̂) - ∑ cⱼ(qⱼ(p̂))`. -/
noncomputable def producerSurplus (F : κ → QLFirmStrict) (p : ℝ) : ℝ :=
  p * aggSupply F p - ∑ j, (F j).c ((F j).supply p)

/-- Envelope theorem for a consumer's surplus: `d/dp [φ(x(p)) - p x(p)] = -x(p)` at `p > 0`. -/
theorem QLConsumer.surplus_hasDerivAt (C : QLConsumer) {p : ℝ} (hp : 0 < p) :
    HasDerivAt (fun r => C.φ (C.demand r) - r * C.demand r) (-C.demand p) p := by
  have hcont := C.demand_continuousAt hp
  have hlo : (fun r => C.demand r - C.demand p) =o[𝓝 p] (fun _ => (1 : ℝ)) :=
    (Asymptotics.isLittleO_one_iff ℝ).2 (tendsto_sub_nhds_zero_iff.2 hcont)
  have h₂ : (fun r => -((r - p) * (C.demand r - C.demand p))) =o[𝓝 p] fun r => r - p := by
    have := (Asymptotics.isBigO_refl (fun r => r - p) (𝓝 p)).mul_isLittleO hlo
    simpa using this.neg_left
  refine hasDerivAt_of_sandwich (e₁ := fun _ => 0) (Asymptotics.isLittleO_zero _ _) h₂ ?_
  filter_upwards [Ioi_mem_nhds hp] with r hr
  have h1 := C.demand_max hr (C.demand p) (C.demand_nonneg hp)
  have h2 := C.demand_max hp (C.demand r) (C.demand_nonneg hr)
  constructor <;> nlinarith

/-- Envelope theorem for a firm's profit: `d/dp [p q(p) - c(q(p))] = q(p)`. -/
theorem QLFirmStrict.profit_hasDerivAt (F : QLFirmStrict) (p : ℝ) :
    HasDerivAt (fun r => r * F.supply r - F.c (F.supply r)) (F.supply p) p := by
  have hcont := F.supply_continuous.continuousAt (x := p)
  have hlo : (fun r => F.supply r - F.supply p) =o[𝓝 p] (fun _ => (1 : ℝ)) :=
    (Asymptotics.isLittleO_one_iff ℝ).2 (tendsto_sub_nhds_zero_iff.2 hcont)
  have h₂ : (fun r => (r - p) * (F.supply r - F.supply p)) =o[𝓝 p] fun r => r - p := by
    simpa using (Asymptotics.isBigO_refl (fun r => r - p) (𝓝 p)).mul_isLittleO hlo
  refine hasDerivAt_of_sandwich (e₁ := fun _ => 0) (Asymptotics.isLittleO_zero _ _) h₂ ?_
  refine Filter.Eventually.of_forall fun r => ?_
  have h1 := F.supply_max r (F.supply p) (F.supply_nonneg p)
  have h2 := F.supply_max p (F.supply r) (F.supply_nonneg r)
  constructor <;> nlinarith

/-- **Envelope theorem** (MWG, p. 333): `CS'(p) = -x(p)` for `p > 0`. -/
theorem consumerSurplus_hasDerivAt (C : ι → QLConsumer) {p : ℝ} (hp : 0 < p) :
    HasDerivAt (consumerSurplus C) (-aggDemand C p) p := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun i _ => (C i).surplus_hasDerivAt hp
  have heq : (fun r => ∑ i ∈ Finset.univ, ((C i).φ ((C i).demand r) - r * (C i).demand r)) =
      consumerSurplus C := by
    ext r
    simp [consumerSurplus, aggDemand, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [heq] at h
  simpa [aggDemand, Finset.sum_neg_distrib] using h

/-- **Envelope theorem** (MWG, p. 333): `Π'(p) = q(p)`. -/
theorem producerSurplus_hasDerivAt (F : κ → QLFirmStrict) (p : ℝ) :
    HasDerivAt (producerSurplus F) (aggSupply F p) p := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun j _ => (F j).profit_hasDerivAt p
  have heq : (fun r => ∑ j ∈ Finset.univ, (r * (F j).supply r - (F j).c ((F j).supply r))) =
      producerSurplus F := by
    ext r
    simp [producerSurplus, aggSupply, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [heq] at h
  simpa [aggSupply] using h

theorem consumerSurplus_eq_zero [Nonempty ι] (C : ι → QLConsumer) {p : ℝ}
    (hp : maxMB C ≤ p) : consumerSurplus C p = 0 := by
  have hp0 : 0 < p := (maxMB_pos C).trans_le hp
  have h0 : ∀ i, (C i).demand p = 0 := fun i =>
    ((C i).demand_eq_zero_iff hp0).2 ((le_maxMB C i).trans hp)
  simp [consumerSurplus, aggDemand, h0, QLConsumer.φ_zero]

/-- **(10.E.9)** (MWG, p. 333). `CS(p') - CS(p) = -∫_p^{p'} x(s) ds` for `0 < p ≤ p'`. -/
theorem eq_10_E_9 (C : ι → QLConsumer) {p p' : ℝ} (hp : 0 < p) (hpp : p ≤ p') :
    consumerSurplus C p' - consumerSurplus C p = -∫ s in p..p', aggDemand C s := by
  have hint : IntervalIntegrable (aggDemand C) volume p p' :=
    ((aggDemand_antitoneOn C).mono fun y hy =>
      Set.mem_Ioi.2 (hp.trans_le (le_trans (le_min le_rfl hpp) hy.1))).intervalIntegrable
  rw [← intervalIntegral.integral_neg, intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hpp
    (fun x hx => (consumerSurplus_hasDerivAt C (hp.trans_le hx.1)).continuousAt.continuousWithinAt)
    (fun x hx => consumerSurplus_hasDerivAt C (hp.trans hx.1)) hint.neg]

/-- **(10.E.8)** (MWG, p. 333). `CS(p) = ∫_p^∞ x(s) ds` for `p > 0` (the integrand vanishes above
`maxᵢ φᵢ'(0)`). -/
theorem eq_10_E_8 [Nonempty ι] (C : ι → QLConsumer) {p : ℝ} (hp : 0 < p) :
    consumerSurplus C p = ∫ s in Set.Ioi p, aggDemand C s := by
  set M := max p (maxMB C) with hM
  have hpM : p ≤ M := le_max_left _ _
  have hMM : maxMB C ≤ M := le_max_right _ _
  have h1 := eq_10_E_9 C hp hpM
  rw [consumerSurplus_eq_zero C hMM] at h1
  have h2 : ∫ s in Set.Ioi p, aggDemand C s = ∫ s in Set.Ioc p M, aggDemand C s := by
    refine (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      Set.Ioc_subset_Ioi_self fun s hs => ?_)
    have hsM : M < s := by
      by_contra hle; push Not at hle; exact hs.2 ⟨hs.1, hle⟩
    exact (aggDemand_eq_zero_iff C (hp.trans hs.1)).2 fun i =>
      (le_maxMB C i).trans (hMM.trans hsM.le)
  rw [h2, ← intervalIntegral.integral_of_le hpM]
  linarith

/-- **(10.E.7)** (MWG, p. 332). `CS(p) = ∫₀^{x(p)} [P(s) - p] ds` for `p > 0`: consumption at
`p` is distributed optimally, so `∑ φᵢ(xᵢ(p)) = γ(x(p)) = ∫₀^{x(p)} P`. -/
theorem eq_10_E_7 [Nonempty ι] (C : ι → QLConsumer) {p : ℝ} (hp : 0 < p) :
    consumerSurplus C p = ∫ s in (0 : ℝ)..aggDemand C p, (invDemand C s - p) := by
  have hX := aggDemand_nonneg C hp
  have hγ : ∑ i, (C i).φ ((C i).demand p) = grossBenefit C (aggDemand C p) :=
    (grossBenefit_eq_of_foc (x := fun i => (C i).demand p) fun i => (C i).demand_spec hp).symm
  rw [intervalIntegral.integral_sub (invDemand_intervalIntegrable C le_rfl hX)
    intervalIntegrable_const, intervalIntegral.integral_const, ← grossBenefit_eq_integral C hX,
    ← hγ, consumerSurplus]
  simp [smul_eq_mul]
  ring

/-- **Exercise 10.E.2** (MWG, pp. 346-347). `∫₀^{x(p̂)} [P(s) - p̂] ds = ∫_{p̂}^∞ x(s) ds`
(proved through the common value `CS(p̂)`, by the fundamental theorem of calculus and the
envelope theorem rather than by a change of variables). -/
theorem exercise_10_E_2 [Nonempty ι] (C : ι → QLConsumer) {p : ℝ} (hp : 0 < p) :
    ∫ s in (0 : ℝ)..aggDemand C p, (invDemand C s - p) = ∫ s in Set.Ioi p, aggDemand C s := by
  rw [← eq_10_E_7 C hp, eq_10_E_8 C hp]

/-- `Π(p) = -∑ cⱼ(0)` when `p ≤ minⱼ cⱼ'(0)` (no firm is active). -/
theorem producerSurplus_eq_of_le [Nonempty κ] (F : κ → QLFirmStrict) {p : ℝ}
    (hp : p ≤ minMC F) : producerSurplus F p = -∑ j, (F j).c 0 := by
  have h0 : ∀ j, (F j).supply p = 0 := fun j =>
    ((F j).supply_eq_zero_iff p).2 (hp.trans (minMC_le F j))
  simp [producerSurplus, aggSupply, h0]

/-- **(10.E.11)** (MWG, p. 333). `Π(p) = Π₀ + ∫₀^p q(s) ds` with `Π₀ = -∑ cⱼ(0)` (zero when
`cⱼ(0) = 0`), for `p ≥ 0`. -/
theorem eq_10_E_11 [Nonempty κ] (F : κ → QLFirmStrict) {p : ℝ} (hp : 0 ≤ p) :
    producerSurplus F p = -∑ j, (F j).c 0 + ∫ s in (0 : ℝ)..p, aggSupply F s := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hp
    (fun x _ => (producerSurplus_hasDerivAt F x).continuousAt.continuousWithinAt)
    (fun x _ => producerSurplus_hasDerivAt F x)
    ((aggSupply_continuous F).intervalIntegrable 0 p),
    producerSurplus_eq_of_le F (minMC_pos F).le]
  ring

/-- **(10.E.12)** (MWG, p. 333). `Π(p') - Π(p) = ∫_p^{p'} q(s) ds`. -/
theorem eq_10_E_12 (F : κ → QLFirmStrict) {p p' : ℝ} (hpp : p ≤ p') :
    producerSurplus F p' - producerSurplus F p = ∫ s in p..p', aggSupply F s := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hpp
    (fun x _ => (producerSurplus_hasDerivAt F x).continuousAt.continuousWithinAt)
    (fun x _ => producerSurplus_hasDerivAt F x)
    ((aggSupply_continuous F).intervalIntegrable p p')]

/-- **(10.E.10)** (MWG, p. 333). `Π(p) = Π₀ + ∫₀^{q(p)} [p - C'(s)] ds` for `p ≥ 0`: production at
`p` is distributed optimally, so `∑ cⱼ(qⱼ(p)) = C(q(p)) = C(0) + ∫₀^{q(p)} C'`. -/
theorem eq_10_E_10 [Nonempty κ] (F : κ → QLFirmStrict) {p : ℝ} (hp : 0 ≤ p) :
    producerSurplus F p = -∑ j, (F j).c 0 + ∫ s in (0 : ℝ)..aggSupply F p, (p - invSupply F s) := by
  have hQ := aggSupply_nonneg F p
  have hC : ∑ j, (F j).c ((F j).supply p) = minCost (fun j => (F j).toQLFirm) (aggSupply F p) :=
    (minCost_eq_of_foc (F := fun j => (F j).toQLFirm) hp
      (fun j => (F j).supply_foc p)).symm
  rw [intervalIntegral.integral_sub intervalIntegrable_const
    (invSupply_intervalIntegrable F le_rfl hQ), intervalIntegral.integral_const,
    producerSurplus, hC, minCost_eq_integral F hQ, minCost_zero]
  simp [smul_eq_mul]
  ring

end MWG.CompetitiveMarkets
