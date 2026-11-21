/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGCompetitiveMarkets.Surplus
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Comparative statics of a sales tax (MWG Example 10.C.1, pp. 323-324; Example 10.E.1)

With a per-unit tax `t` paid by consumers, the equilibrium producer price `p*(t)` solves
`x(p*(t) + t) = q(p*(t))` (10.C.7). For the quasilinear model with strictly convex costs:

* `taxPrice` exists and is unique for `t ∈ (-minⱼ cⱼ'(0), maxᵢ φᵢ'(0) - minⱼ cⱼ'(0))` (taxes
  and small subsidies), with positive trade.
* Monotone comparative statics (p. 323): `p*(t)` strictly decreases, the consumer price
  `p*(t) + t` weakly increases and the quantity traded decreases as `t` increases.
* (10.C.8): `p*` is differentiable with `p*'(t) = -x'/(x' - q')` whenever aggregate demand and
  supply are differentiable at the relevant prices with `x' < 0 ≤ q'`; hence `-1 ≤ p*'(t) < 0`;
  `p*'(t) = -1` when `q' = 0`. The formula in terms of `φᵢ''`, `cⱼ''` (p. 324) and its
  derivation through the implicit function theorem (**Exercise 10.C.5**).
* Example 10.E.1: the deadweight loss `S*(t) - S*(0) < 0` for `t > 0`, the decomposition
  `S = CS + Π + tax revenue`.
* **Exercise 10.C.6** (specific versus ad valorem taxes and who pays) and **Exercise 10.C.7**
  (constant-elasticity incidence).
-/

namespace MWG.CompetitiveMarkets

open Filter Topology MeasureTheory

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- A function antitone on a neighbourhood of `a` whose image is a neighbourhood of `f a` is
continuous at `a`. -/
theorem continuousAt_of_antitoneOn_of_image_mem_nhds {f : ℝ → ℝ} {s : Set ℝ} {a : ℝ}
    (h : AntitoneOn f s) (hs : s ∈ 𝓝 a) (hfs : f '' s ∈ 𝓝 (f a)) : ContinuousAt f a := by
  have hm : MonotoneOn (fun x => -f x) s := fun x hx y hy hxy => neg_le_neg (h hx hy hxy)
  have himg : (fun x => -f x) '' s ∈ 𝓝 (-f a) := by
    have : (fun x => -f x) '' s = Neg.neg ⁻¹' (f '' s) := by
      ext y
      simp only [Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, by ring⟩
      · rintro ⟨x, hx, hxy⟩; exact ⟨x, hx, by rw [hxy, neg_neg]⟩
    rw [this]
    exact continuous_neg.continuousAt.preimage_mem_nhds (by rwa [neg_neg])
  have h2 := (continuousAt_of_monotoneOn_of_image_mem_nhds hm hs himg).neg
  convert h2 using 1
  funext x
  simp

/-- **The inverse demand function is continuous** on `x > 0`. -/
theorem invDemand_continuousAt [Nonempty ι] (C : ι → QLConsumer) {X : ℝ} (hX : 0 < X) :
    ContinuousAt (invDemand C) X := by
  refine continuousAt_of_antitoneOn_of_image_mem_nhds
    ((invDemand_antitoneOn C).mono Set.Ioi_subset_Ici_self) (Ioi_mem_nhds hX) ?_
  have hP0 := invDemand_pos C hX.le
  have hPm : invDemand C X < maxMB C := by
    obtain ⟨i, hi⟩ := exists_lt_of_aggDemand_pos C hP0 ((aggDemand_invDemand C hX.le).symm ▸ hX)
    exact hi.trans_le (le_maxMB C i)
  refine Filter.mem_of_superset (Ioo_mem_nhds hP0 hPm) fun p hp => ?_
  obtain ⟨i, hi⟩ := exists_eq_maxMB C
  have hpos : 0 < aggDemand C p := Finset.sum_pos' (fun k _ => (C k).demand_nonneg hp.1)
    ⟨i, Finset.mem_univ i, ((C i).demand_pos_iff hp.1).2 (hi ▸ hp.2)⟩
  exact ⟨aggDemand C p, hpos, invDemand_aggDemand C hp.1 hp.2⟩

/-- **Derivative of the inverse demand function**: `P'(x) = 1/x'(P(x))` when `x'(P(x)) ≠ 0`. -/
theorem invDemand_hasDerivAt [Nonempty ι] (C : ι → QLConsumer) {X d : ℝ} (hX : 0 < X)
    (hd : HasDerivAt (aggDemand C) d (invDemand C X)) (hd0 : d ≠ 0) :
    HasDerivAt (invDemand C) d⁻¹ X := by
  refine HasDerivAt.of_local_left_inverse (invDemand_continuousAt C hX) hd hd0 ?_
  filter_upwards [Ioi_mem_nhds hX] with y hy
  exact aggDemand_invDemand C (le_of_lt hy)

/-! ## The equilibrium with a tax -/

/-- Existence and uniqueness of the producer price with a tax `t` paid by consumers, for
`-minⱼ cⱼ'(0) < t < maxᵢ φᵢ'(0) - minⱼ cⱼ'(0)` (10.C.7). -/
theorem exists_taxPrice [Nonempty ι] [Nonempty κ] (C : ι → QLConsumer) (F : κ → QLFirmStrict)
    (t : ℝ) : ∃ p, (-minMC F < t ∧ t < maxMB C - minMC F) →
      minMC F < p ∧ p + t < maxMB C ∧ aggDemand C (p + t) = aggSupply F p := by
  by_cases ht : -minMC F < t ∧ t < maxMB C - minMC F
  · obtain ⟨ht1, ht2⟩ := ht
    set lo := minMC F
    set hi := maxMB C - t
    have hlohi : lo < hi := by simp only [hi]; linarith
    have hZcont : ContinuousOn (fun p => aggDemand C (p + t) - aggSupply F p) (Set.Icc lo hi) := by
      refine ContinuousOn.sub ?_ (aggSupply_continuous F).continuousOn
      exact (aggDemand_continuousOn C).comp (continuousOn_id.add continuousOn_const)
        fun p hp => Set.mem_Ioi.2 (by linarith [hp.1])
    have hZlo : 0 < aggDemand C (lo + t) - aggSupply F lo := by
      have hq : aggSupply F lo = 0 := (aggSupply_eq_zero_iff F lo).2 fun j => minMC_le F j
      obtain ⟨i, hi⟩ := exists_eq_maxMB C
      have hx : 0 < aggDemand C (lo + t) := Finset.sum_pos'
        (fun k _ => (C k).demand_nonneg (by linarith))
        ⟨i, Finset.mem_univ i, ((C i).demand_pos_iff (by linarith)).2 (by rw [hi]; linarith)⟩
      linarith
    have hZhi : aggDemand C (hi + t) - aggSupply F hi < 0 := by
      have hx : aggDemand C (hi + t) = 0 := by
        refine (aggDemand_eq_zero_iff C (by simp only [hi]; linarith [maxMB_pos C])).2
          fun i => ?_
        simp only [hi, sub_add_cancel]; exact le_maxMB C i
      obtain ⟨j, hj⟩ := exists_eq_minMC F
      have hq : 0 < aggSupply F hi := Finset.sum_pos' (fun k _ => (F k).supply_nonneg _)
        ⟨j, Finset.mem_univ j, ((F j).supply_pos_iff _).2 (by rw [hj]; exact hlohi)⟩
      linarith
    obtain ⟨p, hp, hpZ⟩ := intermediate_value_Icc' hlohi.le hZcont ⟨hZhi.le, hZlo.le⟩
    refine ⟨p, fun _ => ⟨lt_of_le_of_ne hp.1 fun h => ?_, lt_of_le_of_ne ?_ fun h => ?_, ?_⟩⟩
    · rw [← h] at hpZ; linarith
    · have := hp.2; simp only [hi] at this; linarith
    · have : p = hi := by simp only [hi]; linarith
      rw [this] at hpZ; linarith
    · linarith [hpZ]
  · exact ⟨0, fun h => absurd h ht⟩

/-- **The producer price `p*(t)` with a per-unit tax `t` on consumers** (MWG, p. 323). -/
noncomputable def taxPrice [Nonempty ι] [Nonempty κ] (C : ι → QLConsumer)
    (F : κ → QLFirmStrict) (t : ℝ) : ℝ :=
  Classical.choose (exists_taxPrice C F t)

/-- The admissible tax range `(-minⱼ cⱼ'(0), maxᵢ φᵢ'(0) - minⱼ cⱼ'(0))`. -/
def taxRange [Nonempty ι] [Nonempty κ] (C : ι → QLConsumer) (F : κ → QLFirmStrict) : Set ℝ :=
  Set.Ioo (-minMC F) (maxMB C - minMC F)

theorem taxPrice_spec [Nonempty ι] [Nonempty κ] (C : ι → QLConsumer) (F : κ → QLFirmStrict)
    {t : ℝ} (ht : t ∈ taxRange C F) :
    minMC F < taxPrice C F t ∧ taxPrice C F t + t < maxMB C ∧
      aggDemand C (taxPrice C F t + t) = aggSupply F (taxPrice C F t) :=
  Classical.choose_spec (exists_taxPrice C F t) ht

/-- **(10.C.7)** uniquely determines `p*(t)`: any price with positive consumer price clearing
the market equals `p*(t)`. -/
theorem taxPrice_unique [Nonempty ι] [Nonempty κ] (C : ι → QLConsumer) (F : κ → QLFirmStrict)
    {t p : ℝ} (ht : t ∈ taxRange C F) (hpt : 0 < p + t)
    (h : aggDemand C (p + t) = aggSupply F p) : taxPrice C F t = p := by
  obtain ⟨h1, h2, h3⟩ := taxPrice_spec C F ht
  have ht1 : -minMC F < t := ht.1
  have hp : minMC F < p := by
    by_contra hle
    push Not at hle
    have hq := (aggSupply_eq_zero_iff F p).2 fun j => hle.trans (minMC_le F j)
    rw [hq] at h
    have := (aggDemand_eq_zero_iff C hpt).1 h
    obtain ⟨i, hi⟩ := exists_eq_maxMB C
    have := this i
    rw [hi] at this
    linarith [ht.2]
  have key : ∀ p₁ p₂, minMC F < p₁ → p₁ < p₂ → 0 < p₁ + t →
      aggDemand C (p₁ + t) = aggSupply F p₁ → aggDemand C (p₂ + t) = aggSupply F p₂ → False := by
    intro p₁ p₂ hp₁ h₁₂ hpt₁ e₁ e₂
    obtain ⟨j, hj⟩ := exists_eq_minMC F
    have hs := aggSupply_strictMono F h₁₂ ⟨j, by rw [hj]; linarith⟩
    have hd := aggDemand_antitoneOn C hpt₁ (show (0 : ℝ) < p₂ + t by linarith)
      (by linarith : p₁ + t ≤ p₂ + t)
    linarith
  rcases lt_trichotomy (taxPrice C F t) p with hlt | heq | hgt
  · exact (key _ _ h1 hlt (by linarith [(minMC_pos F)]) h3 h).elim
  · exact heq
  · exact (key _ _ hp hgt hpt h h3).elim

/-- The equilibrium aggregate quantity `x*(t)`. -/
noncomputable def taxQuantity [Nonempty ι] [Nonempty κ] (C : ι → QLConsumer)
    (F : κ → QLFirmStrict) (t : ℝ) : ℝ := aggSupply F (taxPrice C F t)

theorem taxQuantity_pos [Nonempty ι] [Nonempty κ] (C : ι → QLConsumer) (F : κ → QLFirmStrict)
    {t : ℝ} (ht : t ∈ taxRange C F) : 0 < taxQuantity C F t := by
  obtain ⟨j, hj⟩ := exists_eq_minMC F
  exact Finset.sum_pos' (fun k _ => (F k).supply_nonneg _)
    ⟨j, Finset.mem_univ j, ((F j).supply_pos_iff _).2 (hj ▸ (taxPrice_spec C F ht).1)⟩

/-- **Example 10.C.1** (MWG, p. 323): monotone comparative statics. For taxes `t₁ < t₂` in the
admissible range, the producer price strictly falls, the consumer price weakly rises and the
quantity traded falls. -/
theorem example_10_C_1_monotone [Nonempty ι] [Nonempty κ] (C : ι → QLConsumer)
    (F : κ → QLFirmStrict) {t₁ t₂ : ℝ} (h₁ : t₁ ∈ taxRange C F) (h₂ : t₂ ∈ taxRange C F)
    (h₁₂ : t₁ < t₂) :
    taxPrice C F t₂ < taxPrice C F t₁ ∧
      taxPrice C F t₁ + t₁ ≤ taxPrice C F t₂ + t₂ ∧
      taxQuantity C F t₂ < taxQuantity C F t₁ := by
  obtain ⟨a1, b1, e1⟩ := taxPrice_spec C F h₁
  obtain ⟨a2, b2, e2⟩ := taxPrice_spec C F h₂
  have ht1 : -minMC F < t₁ := h₁.1
  have ht2 : -minMC F < t₂ := h₂.1
  set p₁ := taxPrice C F t₁
  set p₂ := taxPrice C F t₂
  have hm := minMC_pos F
  obtain ⟨j, hj⟩ := exists_eq_minMC F
  obtain ⟨i, hi⟩ := exists_eq_maxMB C
  have hp : p₂ < p₁ := by
    by_contra hle
    push Not at hle
    have hs := aggSupply_monotone F hle
    have hd := aggDemand_strictAnti C (by linarith : 0 < p₁ + t₁)
      (by linarith : p₁ + t₁ < p₂ + t₂) ⟨i, by rw [hi]; exact b1⟩
    linarith
  have hs := aggSupply_strictMono F hp ⟨j, by rw [hj]; exact a1⟩
  refine ⟨hp, ?_, hs⟩
  by_contra hlt
  push Not at hlt
  have hd := aggDemand_antitoneOn C (show (0 : ℝ) < p₂ + t₂ by linarith)
    (show (0 : ℝ) < p₁ + t₁ by linarith) hlt.le
  linarith

/-- `τ(p) = P(q(p)) - p`: the tax at which `p` is the producer price; `p*` is its inverse. -/
theorem taxPrice_left_inverse [Nonempty ι] [Nonempty κ] (C : ι → QLConsumer)
    (F : κ → QLFirmStrict) {t : ℝ} (ht : t ∈ taxRange C F) :
    invDemand C (aggSupply F (taxPrice C F t)) - taxPrice C F t = t := by
  obtain ⟨a, b, e⟩ := taxPrice_spec C F ht
  rw [← e, invDemand_aggDemand C (by linarith [ht.1]) b]
  ring

/-- `p*` is continuous on the admissible range. -/
theorem taxPrice_continuousAt [Nonempty ι] [Nonempty κ] (C : ι → QLConsumer)
    (F : κ → QLFirmStrict) {t : ℝ} (ht : t ∈ taxRange C F) :
    ContinuousAt (taxPrice C F) t := by
  have hopen : IsOpen (taxRange C F) := isOpen_Ioo
  refine continuousAt_of_antitoneOn_of_image_mem_nhds
    (fun a ha b hb hab => ?_) (hopen.mem_nhds ht) ?_
  · rcases eq_or_lt_of_le hab with h | h
    · rw [h]
    · exact (example_10_C_1_monotone C F ha hb h).1.le
  · -- for `p` near `p*(t)`, `τ(p)` is admissible and `p*(τ(p)) = p`
    set p₀ := taxPrice C F t
    obtain ⟨a0, b0, e0⟩ := taxPrice_spec C F ht
    have hq0 : 0 < aggSupply F p₀ := taxQuantity_pos C F ht
    have hτ : ContinuousAt (fun p => invDemand C (aggSupply F p) - p) p₀ :=
      ((invDemand_continuousAt C hq0).comp (aggSupply_continuous F).continuousAt).sub
        continuousAt_id
    have hτ0 : (fun p => invDemand C (aggSupply F p) - p) p₀ = t := taxPrice_left_inverse C F ht
    have hev : ∀ᶠ p in 𝓝 p₀, invDemand C (aggSupply F p) - p ∈ taxRange C F :=
      hτ.preimage_mem_nhds (by
        have e : invDemand C (aggSupply F p₀) - p₀ = t := hτ0
        rw [e]; exact hopen.mem_nhds ht)
    obtain ⟨j, hj⟩ := exists_eq_minMC F
    filter_upwards [hev, Ioi_mem_nhds a0] with p hp hpm
    refine ⟨_, hp, taxPrice_unique C F hp ?_ ?_⟩
    · have hqp : 0 ≤ aggSupply F p := aggSupply_nonneg F p
      simp only [add_sub_cancel]
      exact invDemand_pos C hqp
    · have hqp : 0 < aggSupply F p := Finset.sum_pos' (fun k _ => (F k).supply_nonneg _)
        ⟨j, Finset.mem_univ j, ((F j).supply_pos_iff _).2 (hj ▸ hpm)⟩
      simp only [add_sub_cancel]
      exact aggDemand_invDemand C hqp.le

/-- **(10.C.8)** (MWG, p. 323). If aggregate demand has derivative `x' < 0` at `p*(t) + t` and
aggregate supply derivative `q' ≥ 0` at `p*(t)`, then `p*` is differentiable at `t` with
`p*'(t) = -x'/(x' - q')`. -/
theorem eq_10_C_8 [Nonempty ι] [Nonempty κ] (C : ι → QLConsumer) (F : κ → QLFirmStrict)
    {t x' q' : ℝ} (ht : t ∈ taxRange C F)
    (hx : HasDerivAt (aggDemand C) x' (taxPrice C F t + t)) (hx0 : x' < 0)
    (hq : HasDerivAt (aggSupply F) q' (taxPrice C F t)) (hq0 : 0 ≤ q') :
    HasDerivAt (taxPrice C F) (-x' / (x' - q')) t := by
  obtain ⟨a, b, e⟩ := taxPrice_spec C F ht
  set p₀ := taxPrice C F t
  have hq0' : 0 < aggSupply F p₀ := taxQuantity_pos C F ht
  have hP : invDemand C (aggSupply F p₀) = p₀ + t := by
    rw [← e]; exact invDemand_aggDemand C (by linarith [ht.1]) b
  have hPd : HasDerivAt (invDemand C) x'⁻¹ (aggSupply F p₀) :=
    invDemand_hasDerivAt C hq0' (by rw [hP]; exact hx) hx0.ne
  have hτ : HasDerivAt (fun p => invDemand C (aggSupply F p) - p) (x'⁻¹ * q' - 1) p₀ :=
    (hPd.comp p₀ hq).sub (hasDerivAt_id p₀)
  have hτ0 : x'⁻¹ * q' - 1 ≠ 0 := by
    have : x'⁻¹ * q' ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (inv_lt_zero.2 hx0).le hq0
    linarith
  have h := HasDerivAt.of_local_left_inverse (taxPrice_continuousAt C F ht) hτ hτ0
    (by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      exact taxPrice_left_inverse C F hs)
  have e2 : -x' / (x' - q') = (x'⁻¹ * q' - 1)⁻¹ := by
    have h1 : x' ≠ 0 := hx0.ne
    have h2 : x' - q' ≠ 0 := by linarith
    have h3 : x'⁻¹ * q' - 1 = (q' - x') / x' := by field_simp
    rw [h3, inv_div, div_eq_div_iff h2 (by linarith : q' - x' ≠ 0)]
    ring
  rw [e2]
  exact h

/-- **Example 10.C.1** (MWG, p. 323). `-1 ≤ p*'(t) < 0`; `p*'(t) = -1` when `q' = 0`. -/
theorem example_10_C_1_bounds {x' q' : ℝ} (hx0 : x' < 0) (hq0 : 0 ≤ q') :
    -1 ≤ -x' / (x' - q') ∧ -x' / (x' - q') < 0 ∧ (q' = 0 → -x' / (x' - q') = -1) := by
  have hden : x' - q' < 0 := by linarith
  refine ⟨?_, div_neg_of_pos_of_neg (by linarith) hden, fun h => ?_⟩
  · rw [le_div_iff_of_neg hden]
    linarith
  · rw [h, sub_zero, neg_div, div_self hx0.ne]

/-- **(MWG, p. 324)** `p*'(0)` in terms of `φᵢ''` and `cⱼ''`: when every consumer and firm is
active at `t = 0` and every `cⱼ'' > 0`,
`p*'(0) = -∑ᵢ[φᵢ'']⁻¹ / (∑ᵢ[φᵢ'']⁻¹ - ∑ⱼ[cⱼ'']⁻¹)`. -/
theorem example_10_C_1_formula [Nonempty ι] [Nonempty κ] (C : ι → QLConsumer)
    (F : κ → QLFirmStrict) (h0 : (0 : ℝ) ∈ taxRange C F)
    (hxa : ∀ i, taxPrice C F 0 < (C i).dφ 0) (hqa : ∀ j, (F j).dc 0 < taxPrice C F 0)
    (hc2 : ∀ j, 0 < (F j).d2c ((F j).supply (taxPrice C F 0))) :
    HasDerivAt (taxPrice C F)
      (-(∑ i, ((C i).d2φ ((C i).demand (taxPrice C F 0)))⁻¹) /
        (∑ i, ((C i).d2φ ((C i).demand (taxPrice C F 0)))⁻¹ -
          ∑ j, ((F j).d2c ((F j).supply (taxPrice C F 0)))⁻¹)) 0 := by
  set p₀ := taxPrice C F 0
  have hp0 : 0 < p₀ := (minMC_pos F).trans (taxPrice_spec C F h0).1
  have hx : HasDerivAt (aggDemand C) (∑ i, ((C i).d2φ ((C i).demand p₀))⁻¹) (p₀ + 0) := by
    rw [add_zero]
    have := HasDerivAt.fun_sum (u := Finset.univ) fun i _ => (C i).demand_hasDerivAt hp0 (hxa i)
    exact this
  have hq : HasDerivAt (aggSupply F) (∑ j, ((F j).d2c ((F j).supply p₀))⁻¹) p₀ :=
    HasDerivAt.fun_sum (u := Finset.univ) fun j _ => (F j).supply_hasDerivAt (hqa j) (hc2 j)
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hx0 : ∑ i, ((C i).d2φ ((C i).demand p₀))⁻¹ < 0 :=
    Finset.sum_neg (fun k _ => (C k).demand_deriv_neg hp0) Finset.univ_nonempty
  have hq0 : 0 ≤ ∑ j, ((F j).d2c ((F j).supply p₀))⁻¹ :=
    Finset.sum_nonneg fun j _ => (inv_pos.2 (hc2 j)).le
  exact eq_10_C_8 C F h0 hx hx0 hq hq0

/-- **Exercise 10.C.5** (MWG, p. 345). Differentiating the equilibrium system (10.C.4)-(10.C.6)
with `p̂ᵢ = p + t`, `p̂ⱼ = p`: if differentiable paths `xᵢ(t)`, `qⱼ(t)`, `p(t)` satisfy
`φᵢ'(xᵢ(t)) = p(t) + t`, `cⱼ'(qⱼ(t)) = p(t)` and `∑ xᵢ(t) = ∑ qⱼ(t)` near `t₀`, then
`p'(t₀) = -∑[φᵢ'']⁻¹ / (∑[φᵢ'']⁻¹ - ∑[cⱼ'']⁻¹)`. -/
theorem exercise_10_C_5 [Nonempty ι] (dφ d2φ : ι → ℝ → ℝ) (dc d2c : κ → ℝ → ℝ)
    (x : ι → ℝ → ℝ) (q : κ → ℝ → ℝ) (p : ℝ → ℝ) {t₀ p' : ℝ} (x' : ι → ℝ) (q' : κ → ℝ)
    (hdφ : ∀ i, HasDerivAt (dφ i) (d2φ i (x i t₀)) (x i t₀))
    (hdc : ∀ j, HasDerivAt (dc j) (d2c j (q j t₀)) (q j t₀))
    (hneg : ∀ i, d2φ i (x i t₀) < 0) (hpos : ∀ j, 0 < d2c j (q j t₀))
    (hx : ∀ i, HasDerivAt (x i) (x' i) t₀) (hq : ∀ j, HasDerivAt (q j) (q' j) t₀)
    (hp : HasDerivAt p p' t₀)
    (e4 : ∀ᶠ t in 𝓝 t₀, ∀ i, dφ i (x i t) = p t + t)
    (e5 : ∀ᶠ t in 𝓝 t₀, ∀ j, dc j (q j t) = p t)
    (e6 : ∀ᶠ t in 𝓝 t₀, ∑ i, x i t = ∑ j, q j t) :
    p' = -(∑ i, (d2φ i (x i t₀))⁻¹) / (∑ i, (d2φ i (x i t₀))⁻¹ - ∑ j, (d2c j (q j t₀))⁻¹) := by
  have hxi : ∀ i, x' i = (p' + 1) / d2φ i (x i t₀) := by
    intro i
    have h1 := (hdφ i).comp t₀ (hx i)
    have h2 : HasDerivAt (fun t => p t + t) (p' + 1) t₀ := hp.add (hasDerivAt_id t₀)
    have h3 := h1.congr_of_eventuallyEq (by filter_upwards [e4] with t ht; exact (ht i).symm)
    have := h3.unique h2
    rw [eq_div_iff (hneg i).ne]
    linarith
  have hqj : ∀ j, q' j = p' / d2c j (q j t₀) := by
    intro j
    have h1 := (hdc j).comp t₀ (hq j)
    have h3 := h1.congr_of_eventuallyEq (by filter_upwards [e5] with t ht; exact (ht j).symm)
    have := h3.unique hp
    rw [eq_div_iff (hpos j).ne']
    linarith
  have hsum : ∑ i, x' i = ∑ j, q' j := by
    have h1 := HasDerivAt.fun_sum (u := Finset.univ) fun i _ => hx i
    have h2 := HasDerivAt.fun_sum (u := Finset.univ) fun j _ => hq j
    exact (h1.congr_of_eventuallyEq (by filter_upwards [e6] with t ht; exact ht.symm)).unique h2
  simp only [hxi, hqj, div_eq_mul_inv, ← Finset.mul_sum] at hsum
  have hA : ∑ i, (d2φ i (x i t₀))⁻¹ < 0 :=
    Finset.sum_neg (fun i _ => inv_lt_zero.2 (hneg i)) Finset.univ_nonempty
  have hB : 0 ≤ ∑ j, (d2c j (q j t₀))⁻¹ := Finset.sum_nonneg fun j _ => (inv_pos.2 (hpos j)).le
  have hden : ∑ i, (d2φ i (x i t₀))⁻¹ - ∑ j, (d2c j (q j t₀))⁻¹ ≠ 0 := by linarith
  rw [eq_div_iff hden]
  linarith

/-! ## Example 10.E.1: welfare effects of the tax -/

/-- **Example 10.E.1** (MWG, p. 332), (10.E.6). For a tax `t > 0` in the admissible range,
aggregate surplus falls: `S*(t) - S*(0) = ∫_{x*(0)}^{x*(t)} [P - C'] < 0`. -/
theorem example_10_E_1 [Nonempty ι] [Nonempty κ] (C : ι → QLConsumer) (F : κ → QLFirmStrict)
    {t : ℝ} (h0 : (0 : ℝ) ∈ taxRange C F) (ht : t ∈ taxRange C F) (htpos : 0 < t) :
    aggSurplus C F (taxQuantity C F t) - aggSurplus C F (taxQuantity C F 0) =
        ∫ s in taxQuantity C F 0..taxQuantity C F t, (invDemand C s - invSupply F s) ∧
      aggSurplus C F (taxQuantity C F t) - aggSurplus C F (taxQuantity C F 0) < 0 := by
  have hlt := (example_10_C_1_monotone C F h0 ht htpos).2.2
  obtain ⟨a, b, e⟩ := taxPrice_spec C F h0
  have hX0 := taxQuantity_pos C F h0
  rw [add_zero] at b e
  have heq : invDemand C (taxQuantity C F 0) = invSupply F (taxQuantity C F 0) := by
    unfold taxQuantity
    rw [invSupply_aggSupply F a, ← e, invDemand_aggDemand C ((minMC_pos F).trans a) b]
  exact deadweight_loss_neg C F (taxQuantity_pos C F ht).le hlt heq

/-- **Example 10.E.1** (MWG, pp. 332-333). Aggregate surplus at the taxed equilibrium splits
into consumer surplus at the consumer price, producer surplus at the producer price, and tax
revenue `t x*(t)`. -/
theorem example_10_E_1_decomposition [Nonempty ι] [Nonempty κ] (C : ι → QLConsumer)
    (F : κ → QLFirmStrict) {t : ℝ} (ht : t ∈ taxRange C F) :
    aggSurplus C F (taxQuantity C F t) =
      consumerSurplus C (taxPrice C F t + t) + producerSurplus F (taxPrice C F t) +
        t * taxQuantity C F t := by
  obtain ⟨a, b, e⟩ := taxPrice_spec C F ht
  set p := taxPrice C F t
  have hp : 0 < p := (minMC_pos F).trans a
  have hpt : 0 < p + t := by linarith [ht.1]
  have hγ : grossBenefit C (taxQuantity C F t) = ∑ i, (C i).φ ((C i).demand (p + t)) := by
    have := grossBenefit_eq_of_foc (x := fun i => (C i).demand (p + t))
      fun i => (C i).demand_spec hpt
    unfold taxQuantity
    rw [← e]
    exact this
  have hC : minCost (fun j => (F j).toQLFirm) (taxQuantity C F t) =
      ∑ j, (F j).c ((F j).supply p) :=
    minCost_eq_of_foc (F := fun j => (F j).toQLFirm) hp.le fun j => (F j).supply_foc p
  rw [aggSurplus, hγ, hC, consumerSurplus, producerSurplus, e]
  unfold taxQuantity
  ring

/-- **(MWG, p. 332)** `S*'(0) = 0`: the first-order welfare effect of a small tax is zero, when
`p*` is differentiable at `0` and supply is differentiable at `p*(0)`. -/
theorem example_10_E_1_first_order [Nonempty ι] [Nonempty κ] (C : ι → QLConsumer)
    (F : κ → QLFirmStrict) (h0 : (0 : ℝ) ∈ taxRange C F) {d q' : ℝ}
    (hp : HasDerivAt (taxPrice C F) d 0) (hq : HasDerivAt (aggSupply F) q' (taxPrice C F 0)) :
    HasDerivAt (fun t => aggSurplus C F (taxQuantity C F t)) 0 0 := by
  obtain ⟨a, b, e⟩ := taxPrice_spec C F h0
  have hX0 := taxQuantity_pos C F h0
  have hS := aggSurplus_hasDerivAt C F hX0
  have hx : HasDerivAt (taxQuantity C F) (q' * d) 0 := hq.comp 0 hp
  rw [add_zero] at b e
  have heq : invDemand C (taxQuantity C F 0) = invSupply F (taxQuantity C F 0) := by
    unfold taxQuantity
    rw [invSupply_aggSupply F a, ← e, invDemand_aggDemand C ((minMC_pos F).trans a) b]
  have := hS.comp 0 hx
  rw [heq, sub_self, zero_mul] at this
  exact this

/-! ## Exercise 10.C.6: who pays the tax -/

/-- **Exercise 10.C.6(a)** (MWG, p. 345). With a specific tax `t`, the equilibrium consumer cost
and quantity are the same whether consumers pay (`D(p + t) = S(p)`, cost `p + t`) or producers
pay (`D(p') = S(p' - t)`, cost `p'`). -/
theorem exercise_10_C_6a (D S : ℝ → ℝ) (t c Q : ℝ) :
    (∃ p, D (p + t) = S p ∧ c = p + t ∧ Q = D (p + t)) ↔
      (∃ p', D p' = S (p' - t) ∧ c = p' ∧ Q = D p') := by
  constructor
  · rintro ⟨p, h1, h2, h3⟩
    exact ⟨p + t, by rw [h1, add_sub_cancel_right], h2, h3⟩
  · rintro ⟨p', h1, h2, h3⟩
    exact ⟨p' - t, by rw [sub_add_cancel, h1], by rw [h2]; ring, by rw [h3, sub_add_cancel]⟩

/-- **Exercise 10.C.6(b)** (MWG, p. 345). With an ad valorem tax `τ ∈ (0, 1)`: if consumers pay
(`D(p(1 + τ)) = S(p)`, consumer cost `c₁ = p(1 + τ)`) and if producers pay (the government
takes `τ` times the amount the seller receives: `D(p') = S(p'(1 - τ))`, consumer cost `c₂ = p'`),
then with `D` nonincreasing and `S` strictly increasing on positive prices, `c₁ < c₂`:
collecting from producers leads to a higher cost to consumers. -/
theorem exercise_10_C_6b (D S : ℝ → ℝ) (hD : AntitoneOn D (Set.Ioi 0))
    (hS : StrictMonoOn S (Set.Ioi 0)) {τ p p' : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) (hp : 0 < p)
    (hp' : 0 < p') (h₁ : D (p * (1 + τ)) = S p) (h₂ : D p' = S (p' * (1 - τ))) :
    p * (1 + τ) < p' := by
  by_contra hle
  push Not at hle
  have hs : p' * (1 - τ) < p := by
    have : p' * (1 - τ) ≤ p * (1 + τ) * (1 - τ) := mul_le_mul_of_nonneg_right hle (by linarith)
    nlinarith [mul_pos hp (mul_pos hτ0 hτ0)]
  have h1 := hS (Set.mem_Ioi.2 (by nlinarith)) (Set.mem_Ioi.2 hp) hs
  have h2 := hD (Set.mem_Ioi.2 hp') (Set.mem_Ioi.2 (by positivity)) hle
  linarith

/-- **Exercise 10.C.6(b)**, special case (MWG, p. 345). With perfectly inelastic supply
(`S` constant) and strictly decreasing demand, the collection method is irrelevant. -/
theorem exercise_10_C_6b_inelastic (D : ℝ → ℝ) (hD : StrictAntiOn D (Set.Ioi 0)) (s₀ : ℝ)
    {τ p p' : ℝ} (hτ0 : 0 < τ) (hp : 0 < p) (hp' : 0 < p') (h₁ : D (p * (1 + τ)) = s₀)
    (h₂ : D p' = s₀) : p * (1 + τ) = p' :=
  hD.injOn (Set.mem_Ioi.2 (by positivity)) (Set.mem_Ioi.2 hp') (h₁.trans h₂.symm)

/-- **Exercise 10.C.6(b)**: a producer-collected ad valorem rate `τ` is equivalent to the
consumer-collected rate `τ/(1 - τ)`. -/
theorem exercise_10_C_6b_equivalent (D S : ℝ → ℝ) {τ p' : ℝ} (hτ1 : τ < 1) :
    D p' = S (p' * (1 - τ)) ↔
      D (p' * (1 - τ) * (1 + τ / (1 - τ))) = S (p' * (1 - τ)) := by
  have h : p' * (1 - τ) * (1 + τ / (1 - τ)) = p' := by
    field_simp [show (1 - τ) ≠ 0 by linarith]
    ring
  rw [h]

/-! ## Exercise 10.C.7: constant elasticities -/

/-- **Exercise 10.C.7** (MWG, p. 345). With `x(p) = Ap^ε` (`A > 0`, `ε < 0`), `q(p) = αp^γ`
(`α > 0`, `γ ≥ 0`) and an ad valorem tax `κ = 1 + τ` on consumers, the equilibrium producer
price is `p*(κ) = (A/α)^{1/(γ-ε)} κ^{ε/(γ-ε)}`: it solves `A(κp)^ε = αp^γ`, and is the only
positive solution. -/
theorem exercise_10_C_7_price {A ε α γ κ : ℝ} (hA : 0 < A) (hε : ε < 0) (hα : 0 < α)
    (hγ : 0 ≤ γ) (hκ : 0 < κ) {p : ℝ} (hp : 0 < p) :
    A * (κ * p) ^ ε = α * p ^ γ ↔
      p = (A / α) ^ (1 / (γ - ε)) * κ ^ (ε / (γ - ε)) := by
  have hd : 0 < γ - ε := by linarith
  have key : A * (κ * p) ^ ε = α * p ^ γ ↔ p ^ (γ - ε) = A / α * κ ^ ε := by
    rw [Real.mul_rpow hκ.le hp.le, Real.rpow_sub hp]
    constructor
    · intro h
      field_simp
      have h1 : 0 < p ^ ε := Real.rpow_pos_of_pos hp ε
      nlinarith [h]
    · intro h
      have h1 : 0 < p ^ ε := Real.rpow_pos_of_pos hp ε
      field_simp at h
      nlinarith [h]
  rw [key]
  have hrhs : 0 < A / α * κ ^ ε := mul_pos (div_pos hA hα) (Real.rpow_pos_of_pos hκ ε)
  constructor
  · intro h
    have := congrArg (fun z => z ^ (1 / (γ - ε))) h
    rw [← Real.rpow_mul hp.le, mul_one_div_cancel hd.ne', Real.rpow_one,
      Real.mul_rpow (div_pos hA hα).le (Real.rpow_pos_of_pos hκ ε).le,
      ← Real.rpow_mul hκ.le] at this
    rw [this]
    congr 2
    ring
  · intro h
    rw [h, Real.mul_rpow (Real.rpow_pos_of_pos (div_pos hA hα) _).le
      (Real.rpow_pos_of_pos hκ _).le, ← Real.rpow_mul (div_pos hA hα).le,
      ← Real.rpow_mul hκ.le]
    rw [one_div_mul_cancel hd.ne', Real.rpow_one]
    congr 2
    field_simp

/-- **Exercise 10.C.7** (MWG, p. 345). The elasticity of `p*` with respect to `κ` is
`ε/(γ - ε)`: `κ p*'(κ)/p*(κ) = ε/(γ - ε)`; that of the consumer cost `κp*` is `γ/(γ - ε)`. -/
theorem exercise_10_C_7_elasticity {A ε α γ κ : ℝ} (hA : 0 < A) (hε : ε < 0) (hα : 0 < α)
    (hγ : 0 ≤ γ) (hκ : 0 < κ) :
    let pstar : ℝ → ℝ := fun k => (A / α) ^ (1 / (γ - ε)) * k ^ (ε / (γ - ε))
    HasDerivAt pstar ((A / α) ^ (1 / (γ - ε)) * (ε / (γ - ε) * κ ^ (ε / (γ - ε) - 1))) κ ∧
      κ * ((A / α) ^ (1 / (γ - ε)) * (ε / (γ - ε) * κ ^ (ε / (γ - ε) - 1))) / pstar κ =
        ε / (γ - ε) ∧
      ε / (γ - ε) + 1 = γ / (γ - ε) := by
  intro pstar
  have hd : 0 < γ - ε := by linarith
  have hK : 0 < (A / α) ^ (1 / (γ - ε)) := Real.rpow_pos_of_pos (div_pos hA hα) _
  refine ⟨(Real.hasDerivAt_rpow_const (Or.inl hκ.ne')).const_mul _, ?_, ?_⟩
  · simp only [pstar]
    rw [Real.rpow_sub hκ, Real.rpow_one]
    have : 0 < κ ^ (ε / (γ - ε)) := Real.rpow_pos_of_pos hκ _
    field_simp
  · field_simp
    ring

/-- **Exercise 10.C.7** (MWG, p. 345): the polar cases and limits. With `γ = 0` (perfectly
inelastic supply) the producer price falls one-for-one (`ε/(γ - ε) = -1`) and the consumer cost
is unaffected; with `ε = 0` the producer price is unaffected and consumers bear the whole tax;
as `ε → -∞` the elasticity tends to `-1` (producers bear the tax) and as `γ → ∞` it tends to
`0` (consumers bear it). -/
theorem exercise_10_C_7_limits {ε γ : ℝ} (hε : ε < 0) :
    ε / (0 - ε) = -1 ∧ 0 / (γ - 0) = (0 : ℝ) ∧
      Tendsto (fun e : ℝ => e / (γ - e)) atBot (𝓝 (-1)) ∧
      Tendsto (fun g : ℝ => ε / (g - ε)) atTop (𝓝 0) := by
  refine ⟨by rw [zero_sub, div_neg, div_self hε.ne], by simp, ?_, ?_⟩
  · have h1 : Tendsto (fun e : ℝ => -1 + γ / (γ - e)) atBot (𝓝 (-1 + 0)) := by
      refine tendsto_const_nhds.add (Tendsto.div_atTop tendsto_const_nhds ?_)
      exact tendsto_atTop_add_const_left _ γ (tendsto_neg_atBot_atTop)
    rw [add_zero] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_lt_atBot (γ)] with e he
    field_simp [show γ - e ≠ 0 by linarith]
    ring
  · exact Tendsto.div_atTop tendsto_const_nhds (tendsto_atTop_add_const_right _ (-ε) tendsto_id
      |>.congr fun g => by simp only [id]; ring)

/-- A concrete instance of Example 10.C.1: one consumer `φ(x) = 2(1 - e^{-x})` and one firm
`c(q) = q + q²/2`. The tax-price function is differentiable at `0` with `-1 ≤ p*'(0) < 0`
(non-vacuity of `example_10_C_1_formula`). -/
theorem example_10_C_1_instance :
    ∃ d, HasDerivAt (taxPrice (fun _ : Fin 1 => expConsumer 2 two_pos)
      (fun _ : Fin 1 => quadFirm 1 1 one_pos one_pos)) d 0 ∧ -1 ≤ d ∧ d < 0 := by
  set C := fun _ : Fin 1 => expConsumer 2 two_pos
  set F := fun _ : Fin 1 => quadFirm 1 1 one_pos one_pos
  have hM : maxMB C = 2 := by
    simp [maxMB, C, expConsumer, Finset.sup'_const]
  have hm : minMC F = 1 := by
    simp [minMC, F, quadFirm, quadFirmBase, QLFirmStrict.dc, Finset.inf'_const]
  have h0 : (0 : ℝ) ∈ taxRange C F := by
    simp only [taxRange, hM, hm, Set.mem_Ioo]; norm_num
  obtain ⟨a, b, -⟩ := taxPrice_spec C F h0
  rw [hm] at a
  rw [hM, add_zero] at b
  have hd : ∀ i, (C i).dφ 0 = 2 := fun _ => by simp [C, expConsumer]
  have hdc : ∀ j, (F j).dc 0 = 1 := fun _ => by
    simp [F, quadFirm, quadFirmBase, QLFirmStrict.dc]
  have h := example_10_C_1_formula C F h0
    (fun i => by rw [hd i]; exact b)
    (fun j => by rw [hdc j]; exact a)
    (fun _ => by simp [F, quadFirm, quadFirmBase, QLFirmStrict.d2c])
  refine ⟨_, h, ?_⟩
  have hx0 : ∑ i, ((C i).d2φ ((C i).demand (taxPrice C F 0)))⁻¹ < 0 :=
    Finset.sum_neg (fun k _ => (C k).demand_deriv_neg ((minMC_pos F).trans
      (by rw [hm]; exact a))) Finset.univ_nonempty
  have hq0 : 0 ≤ ∑ j, ((F j).d2c ((F j).supply (taxPrice C F 0)))⁻¹ :=
    Finset.sum_nonneg fun j _ => by simp [F, quadFirm, quadFirmBase, QLFirmStrict.d2c]
  exact ⟨(example_10_C_1_bounds hx0 hq0).1, (example_10_C_1_bounds hx0 hq0).2.1⟩

end MWG.CompetitiveMarkets
