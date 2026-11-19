/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGChoiceUnderUncertainty.MoneyLotteries
import UtilityForMoney.EqualProbabilityRisk
import Mathlib.Analysis.Convex.Deriv

/-!
# Risk aversion, certainty equivalents and probability premia

MWG, Section 6.C, pp. 185-187: Definition 6.C.1 (risk aversion, risk neutrality, strict risk
aversion), Jensen's inequality (6.C.2), Definition 6.C.2 (certainty equivalent `c(F, u)` and
probability premium `π(x, ε, u)`), Figures 6.C.2-6.C.3, Proposition 6.C.1, footnote 16 and
Exercise 6.C.3.

Lotteries are the money lotteries of `MoneyLotteries` on a convex set `S` of monetary amounts.
The expected-utility preference of a Bernoulli utility `u` is `euPref u`. Throughout, `u` is
continuous on `S` and increasing (strictly, `StrictMonoOn`), MWG's maintained assumptions
(p. 185). The probability premium is the explicit solution `probPremium u x ε` of (6.C.4).
For (iv) ⇒ (ii) of Proposition 6.C.1 the midpoint inequality is upgraded to concavity by
continuity (Kreps's `midpoint_gap_nonneg`).
-/

namespace MWG.ChoiceUnderUncertainty

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

/-- The expected-utility preference of a Bernoulli utility `u`: `F ≿ G` iff
`∫ u dF ≥ ∫ u dG`. -/
def euPref (u : ℝ → ℝ) (μ ν : Measure ℝ) : Prop := ∫ x, u x ∂ν ≤ ∫ x, u x ∂μ

/-- **Definition 6.C.1** (MWG, p. 185). A decision maker is a risk averter if for every
lottery `F` the degenerate lottery at `∫ x dF` is at least as good as `F`. -/
def RiskAverter (S : Set ℝ) (r : Measure ℝ → Measure ℝ → Prop) : Prop :=
  ∀ μ, IsMoneyLottery S μ → r (Measure.dirac (∫ x, x ∂μ)) μ

/-- **Definition 6.C.1** (MWG, p. 185). Risk neutrality: always indifferent between `F` and
the degenerate lottery at its mean. -/
def RiskNeutral (S : Set ℝ) (r : Measure ℝ → Measure ℝ → Prop) : Prop :=
  ∀ μ, IsMoneyLottery S μ → r (Measure.dirac (∫ x, x ∂μ)) μ ∧ r μ (Measure.dirac (∫ x, x ∂μ))

/-- **Definition 6.C.1** (MWG, p. 185). Strict risk aversion: risk aversion, with indifference
only when `F` is degenerate. -/
def StrictlyRiskAverse (S : Set ℝ) (r : Measure ℝ → Measure ℝ → Prop) : Prop :=
  RiskAverter S r ∧ ∀ μ, IsMoneyLottery S μ → r μ (Measure.dirac (∫ x, x ∂μ)) →
    μ = Measure.dirac (∫ x, x ∂μ)

/-- **(6.C.2)** (MWG, p. 185). An expected utility maximizer is risk averse iff Jensen's
inequality `∫ u dF ≤ u(∫ x dF)` holds for all `F`. -/
theorem riskAverter_iff_jensen (S : Set ℝ) (u : ℝ → ℝ) :
    RiskAverter S (euPref u) ↔ ∀ μ, IsMoneyLottery S μ → ∫ x, u x ∂μ ≤ u (∫ x, x ∂μ) := by
  simp only [RiskAverter, euPref, integral_dirac]

/-- Jensen's inequality for a money lottery and a concave, continuous Bernoulli utility. -/
theorem jensen_moneyLottery {S : Set ℝ} {u : ℝ → ℝ} (hc : ConcaveOn ℝ S u)
    (hu : ContinuousOn u S) {μ : Measure ℝ} (hμ : IsMoneyLottery S μ) :
    ∫ x, u x ∂μ ≤ u (∫ x, x ∂μ) := by
  have := hμ.1
  obtain ⟨a, b, hS, hae⟩ := hμ.ae_mem
  exact (hc.subset hS (convex_Icc a b)).le_map_integral (hu.mono hS) isClosed_Icc hae
    hμ.integrable_id (hμ.integrable hu)

/-- The mean of the binary lottery `p x + (1 - p) y`. -/
theorem mean_binLot (p x y : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∫ z, z ∂(binLot p x y) = p * x + (1 - p) * y :=
  integral_binLot p x y id hp0 hp1

/-- **Proposition 6.C.1**, (i) ⇔ (ii) (MWG, p. 187). For a continuous Bernoulli utility on a
convex `S`, the expected utility maximizer is risk averse iff `u` is concave. -/
theorem proposition_6_C_1_i_ii {S : Set ℝ} (hS : Convex ℝ S) {u : ℝ → ℝ}
    (hu : ContinuousOn u S) : RiskAverter S (euPref u) ↔ ConcaveOn ℝ S u := by
  rw [riskAverter_iff_jensen]
  refine ⟨fun h => ⟨hS, fun x hx y hy a b ha hb hab => ?_⟩,
    fun hc μ hμ => jensen_moneyLottery hc hu hμ⟩
  have hb' : b = 1 - a := by linarith
  subst hb'
  have := h _ (binLot_isMoneyLottery hS hx hy a ha (by linarith))
  rw [integral_binLot _ _ _ _ ha (by linarith), mean_binLot _ _ _ ha (by linarith)] at this
  simpa only [smul_eq_mul] using this

/-- **Definition 6.C.2(i)** (MWG, p. 186). `c` is the certainty equivalent of `F`:
`u(c) = ∫ u dF` (6.C.3). -/
def IsCertaintyEquivalent (S : Set ℝ) (u : ℝ → ℝ) (μ : Measure ℝ) (c : ℝ) : Prop :=
  c ∈ S ∧ u c = ∫ x, u x ∂μ

/-- **Definition 6.C.2(i)** (MWG, p. 186). A continuous Bernoulli utility gives every money
lottery a certainty equivalent. -/
theorem certaintyEquivalent_exists {S : Set ℝ} {u : ℝ → ℝ} (hu : ContinuousOn u S)
    {μ : Measure ℝ} (hμ : IsMoneyLottery S μ) : ∃ c, IsCertaintyEquivalent S u μ c := by
  have := hμ.1
  obtain ⟨a, b, hS, hae, hm⟩ := hμ.mean_mem
  have hne : (Icc a b).Nonempty := ⟨_, hm⟩
  obtain ⟨p, hp, hpmin⟩ := isCompact_Icc.exists_isMinOn hne (hu.mono hS)
  obtain ⟨q, hq, hqmax⟩ := isCompact_Icc.exists_isMaxOn hne (hu.mono hS)
  have hlo : u p ≤ ∫ x, u x ∂μ := by
    calc u p = ∫ _, u p ∂μ := by simp
      _ ≤ ∫ x, u x ∂μ := integral_mono_ae (integrable_const _) (hμ.integrable hu)
          (hae.mono fun x hx => hpmin hx)
  have hhi : ∫ x, u x ∂μ ≤ u q := by
    calc ∫ x, u x ∂μ ≤ ∫ _, u q ∂μ := integral_mono_ae (hμ.integrable hu) (integrable_const _)
          (hae.mono fun x hx => hqmax hx)
      _ = u q := by simp
  have hsub : uIcc p q ⊆ Icc a b := (ordConnected_Icc).uIcc_subset hp hq
  obtain ⟨c, hc, hce⟩ := intermediate_value_uIcc ((hu.mono hS).mono hsub)
    ⟨(min_le_left _ _).trans hlo, hhi.trans (le_max_right _ _)⟩
  exact ⟨c, hS (hsub hc), hce⟩

/-- **Definition 6.C.2(i)** (MWG, p. 186). For an increasing Bernoulli utility the certainty
equivalent is unique. -/
theorem certaintyEquivalent_unique {S : Set ℝ} {u : ℝ → ℝ} (hi : StrictMonoOn u S)
    {μ : Measure ℝ} {c d : ℝ} (hc : IsCertaintyEquivalent S u μ c)
    (hd : IsCertaintyEquivalent S u μ d) : c = d :=
  hi.injOn hc.1 hd.1 (hc.2.trans hd.2.symm)

/-- **Definition 6.C.2(ii)** (MWG, p. 186). The probability premium `π(x, ε, u)`, the excess
winning probability over fair odds solving (6.C.4). -/
noncomputable def probPremium (u : ℝ → ℝ) (x ε : ℝ) : ℝ :=
  (2 * u x - u (x + ε) - u (x - ε)) / (2 * (u (x + ε) - u (x - ε)))

/-- **(6.C.4)** (MWG, p. 186). `u(x) = (1/2 + π) u(x + ε) + (1/2 - π) u(x - ε)`, and `π` is the
unique such number. -/
theorem probPremium_spec (u : ℝ → ℝ) (x ε : ℝ) (h : u (x - ε) < u (x + ε)) :
    u x = (1 / 2 + probPremium u x ε) * u (x + ε) + (1 / 2 - probPremium u x ε) * u (x - ε) ∧
    ∀ q, u x = (1 / 2 + q) * u (x + ε) + (1 / 2 - q) * u (x - ε) → q = probPremium u x ε := by
  have hd : 2 * (u (x + ε) - u (x - ε)) ≠ 0 := by linarith
  have hd' : u (x + ε) - u (x - ε) ≠ 0 := by linarith
  constructor
  · unfold probPremium
    field_simp
    ring
  · intro q hq
    unfold probPremium
    rw [eq_div_iff hd]
    linarith

/-- **Figure 6.C.3(b)** (MWG, p. 187). The mean of the premium gamble is
`(1/2 + π)(x + ε) + (1/2 - π)(x - ε) = x + 2επ`. -/
theorem figure_6_C_3b (x ε q : ℝ) :
    (1 / 2 + q) * (x + ε) + (1 / 2 - q) * (x - ε) = x + 2 * ε * q := by ring

/-- **Figure 6.C.2(a)** (MWG, p. 186). For a strictly concave `u` the gamble between `1` and `3`
dollars has utility `u(1)/2 + u(3)/2 < u(2)`. -/
theorem figure_6_C_2a {u : ℝ → ℝ} {S : Set ℝ} (hc : StrictConcaveOn ℝ S u) (h1 : (1 : ℝ) ∈ S)
    (h3 : (3 : ℝ) ∈ S) : u 1 / 2 + u 3 / 2 < u 2 := by
  have := hc.2 h1 h3 (by norm_num : (1 : ℝ) ≠ 3) (show (0 : ℝ) < 1 / 2 by norm_num)
    (show (0 : ℝ) < 1 / 2 by norm_num) (by norm_num)
  norm_num at this
  linarith

/-- **Figure 6.C.2(b)** (MWG, p. 186). For a linear (affine) `u`, `u(1)/2 + u(3)/2 = u(2)`. -/
theorem figure_6_C_2b (α β : ℝ) :
    (fun x : ℝ => α * x + β) 1 / 2 + (fun x : ℝ => α * x + β) 3 / 2 = (fun x => α * x + β) 2 :=
  by ring

/-- **Proposition 6.C.1**, (ii) ⇔ (iii) (MWG, p. 187). For a continuous, increasing Bernoulli
utility, `u` is concave iff `c(F, u) ≤ ∫ x dF` for every `F`. -/
theorem proposition_6_C_1_ii_iii {S : Set ℝ} (hS : Convex ℝ S) {u : ℝ → ℝ}
    (hu : ContinuousOn u S) (hi : StrictMonoOn u S) :
    ConcaveOn ℝ S u ↔ ∀ μ c, IsMoneyLottery S μ → IsCertaintyEquivalent S u μ c →
      c ≤ ∫ x, x ∂μ := by
  constructor
  · intro hc μ c hμ hce
    have hj := jensen_moneyLottery hc hu hμ
    rw [← hce.2] at hj
    exact (hi.le_iff_le hce.1 hμ.mean_mem_S).mp hj
  · intro h
    rw [← proposition_6_C_1_i_ii hS hu, riskAverter_iff_jensen]
    intro μ hμ
    obtain ⟨c, hce⟩ := certaintyEquivalent_exists hu hμ
    rw [← hce.2]
    exact (hi.le_iff_le hce.1 hμ.mean_mem_S).mpr (h μ c hμ hce)

/-- **(iii)** and the chain on p. 187: `c(F, u) ≤ ∫ x dF` iff `u(c(F, u)) ≤ u(∫ x dF)` iff
`∫ u dF ≤ u(∫ x dF)`. -/
theorem certaintyEquivalent_le_mean_iff {S : Set ℝ} {u : ℝ → ℝ} (hi : StrictMonoOn u S)
    {μ : Measure ℝ} (hμ : IsMoneyLottery S μ) {c : ℝ} (hce : IsCertaintyEquivalent S u μ c) :
    c ≤ ∫ x, x ∂μ ↔ ∫ x, u x ∂μ ≤ u (∫ x, x ∂μ) := by
  rw [← hce.2]
  exact (hi.le_iff_le hce.1 hμ.mean_mem_S).symm

/-- Midpoint concavity and continuity on a convex set give concavity. -/
theorem concaveOn_of_midpoint {S : Set ℝ} (hS : Convex ℝ S) {u : ℝ → ℝ}
    (hu : ContinuousOn u S) (hm : ∀ x ∈ S, ∀ y ∈ S, (u x + u y) / 2 ≤ u ((x + y) / 2)) :
    ConcaveOn ℝ S u := by
  refine ⟨hS, fun x hx y hy a b ha hb hab => ?_⟩
  -- the gap along the segment from `y` (t = 0) to `x` (t = 1)
  let p : ℝ → ℝ := fun t => t * x + (1 - t) * y
  have hp (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : p t ∈ S := by
    have := hS hx hy ht.1 (sub_nonneg.mpr ht.2) (by ring)
    simpa [p, smul_eq_mul] using this
  let f : ℝ → ℝ := fun t => u (p t) - (t * u x + (1 - t) * u y)
  have hfc : ContinuousOn f (Icc 0 1) := by
    have hpc : ContinuousOn p (Icc 0 1) := by fun_prop
    exact (hu.comp hpc fun t ht => hp t ht).sub (by fun_prop)
  have hfm : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, (f s + f t) / 2 ≤ f ((s + t) / 2) := by
    intro s hs t ht
    have hmid := hm (p s) (hp s hs) (p t) (hp t ht)
    have he : (p s + p t) / 2 = p ((s + t) / 2) := by simp only [p]; ring
    rw [he] at hmid
    simp only [f]
    linarith
  have h0 : f 0 = 0 := by simp [f, p]
  have h1 : f 1 = 0 := by simp [f, p]
  have := Kreps.UtilityForMoney.midpoint_gap_nonneg f hfc hfm h0 h1 a ⟨ha, by linarith⟩
  have hb' : b = 1 - a := by linarith
  subst hb'
  simp only [f, p, smul_eq_mul] at this ⊢
  linarith

/-- **Proposition 6.C.1**, (ii) ⇔ (iv) (MWG, p. 187; Exercise 6.C.3, p. 210). For a
continuous, increasing Bernoulli utility, `u` is concave iff `π(x, ε, u) ≥ 0` for all `x` and
`ε > 0` (with `x ± ε ∈ S`). -/
theorem proposition_6_C_1_ii_iv {S : Set ℝ} (hS : Convex ℝ S) {u : ℝ → ℝ}
    (hu : ContinuousOn u S) (hi : StrictMonoOn u S) :
    ConcaveOn ℝ S u ↔ ∀ x ε, 0 < ε → x - ε ∈ S → x + ε ∈ S → 0 ≤ probPremium u x ε := by
  constructor
  · intro hc x ε hε h1 h2
    have hlt : u (x - ε) < u (x + ε) := hi h1 h2 (by linarith)
    have hmid := hc.2 h2 h1 (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (by norm_num)
    simp only [smul_eq_mul] at hmid
    have he : 1 / 2 * (x + ε) + 1 / 2 * (x - ε) = x := by ring
    rw [he] at hmid
    unfold probPremium
    apply div_nonneg <;> linarith
  · intro h
    apply concaveOn_of_midpoint hS hu
    intro x hx y hy
    rcases lt_trichotomy x y with hxy | hxy | hxy
    · have hε : 0 < (y - x) / 2 := by linarith
      have h1 : (x + y) / 2 - (y - x) / 2 = x := by ring
      have h2 : (x + y) / 2 + (y - x) / 2 = y := by ring
      have hp := h ((x + y) / 2) ((y - x) / 2) hε (by rw [h1]; exact hx) (by rw [h2]; exact hy)
      unfold probPremium at hp
      rw [h1, h2] at hp
      have hlt : u x < u y := hi hx hy hxy
      have := (div_nonneg_iff.mp hp)
      rcases this with ⟨hn, _⟩ | ⟨_, hd⟩
      · linarith
      · linarith
    · subst hxy; simp
    · have hε : 0 < (x - y) / 2 := by linarith
      have h1 : (x + y) / 2 - (x - y) / 2 = y := by ring
      have h2 : (x + y) / 2 + (x - y) / 2 = x := by ring
      have hp := h ((x + y) / 2) ((x - y) / 2) hε (by rw [h1]; exact hy) (by rw [h2]; exact hx)
      unfold probPremium at hp
      rw [h1, h2] at hp
      have hlt : u y < u x := hi hy hx hxy
      rcases div_nonneg_iff.mp hp with ⟨hn, _⟩ | ⟨_, hd⟩
      · linarith
      · linarith

/-- **Proposition 6.C.1** (MWG, p. 187). For an expected utility maximizer with a continuous,
increasing Bernoulli utility on a convex set of monetary amounts, the following are
equivalent: (i) risk aversion; (ii) concavity of `u`; (iii) `c(F, u) ≤ ∫ x dF` for all `F`;
(iv) `π(x, ε, u) ≥ 0` for all `x, ε`. -/
theorem proposition_6_C_1 {S : Set ℝ} (hS : Convex ℝ S) {u : ℝ → ℝ} (hu : ContinuousOn u S)
    (hi : StrictMonoOn u S) :
    List.TFAE [RiskAverter S (euPref u), ConcaveOn ℝ S u,
      ∀ μ c, IsMoneyLottery S μ → IsCertaintyEquivalent S u μ c → c ≤ ∫ x, x ∂μ,
      ∀ x ε, 0 < ε → x - ε ∈ S → x + ε ∈ S → 0 ≤ probPremium u x ε] := by
  tfae_have 1 ↔ 2 := proposition_6_C_1_i_ii hS hu
  tfae_have 2 ↔ 3 := proposition_6_C_1_ii_iii hS hu hi
  tfae_have 2 ↔ 4 := proposition_6_C_1_ii_iv hS hu hi
  tfae_finish

/-- **Exercise 6.C.3** (MWG, p. 210). The four conditions of Proposition 6.C.1 are equivalent;
in particular (iv) gives `u(x/2 + y/2) ≥ u(x)/2 + u(y)/2`, which with continuity is
sufficient for concavity. -/
theorem exercise_6_C_3 {S : Set ℝ} (hS : Convex ℝ S) {u : ℝ → ℝ} (hu : ContinuousOn u S)
    (hi : StrictMonoOn u S) :
    (RiskAverter S (euPref u) → ∀ x ε, 0 < ε → x - ε ∈ S → x + ε ∈ S →
      0 ≤ probPremium u x ε) ∧
    ((∀ x ε, 0 < ε → x - ε ∈ S → x + ε ∈ S → 0 ≤ probPremium u x ε) →
      ∀ x ∈ S, ∀ y ∈ S, (u x + u y) / 2 ≤ u ((x + y) / 2)) := by
  constructor
  · intro h
    exact (proposition_6_C_1_ii_iv hS hu hi).mp ((proposition_6_C_1_i_ii hS hu).mp h)
  · intro h x hx y hy
    have hc := (proposition_6_C_1_ii_iv hS hu hi).mpr h
    have := hc.2 hx hy (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (by norm_num)
    simp only [smul_eq_mul] at this
    have e : 1 / 2 * x + 1 / 2 * y = (x + y) / 2 := by ring
    rw [e] at this
    linarith

/-- A probability measure under which the identity is almost surely constant is degenerate. -/
theorem eq_dirac_of_ae_eq_const {μ : Measure ℝ} [IsProbabilityMeasure μ] {c : ℝ}
    (h : (fun x : ℝ => x) =ᵐ[μ] fun _ => c) : μ = Measure.dirac c := by
  have hne : μ {x | x ≠ c} = 0 := by
    have := h
    rw [Filter.EventuallyEq, ae_iff] at this
    simpa using this
  ext s hs
  rw [Measure.dirac_apply' _ hs]
  by_cases hc : c ∈ s
  · rw [indicator_of_mem hc]
    apply le_antisymm prob_le_one
    have hsub : sᶜ ⊆ {x | x ≠ c} := fun x hx hxc => hx (hxc ▸ hc)
    have h0 : μ sᶜ = 0 := measure_mono_null hsub hne
    rw [prob_compl_eq_zero_iff hs] at h0
    rw [h0]
  · rw [indicator_of_notMem hc]
    exact measure_mono_null (fun x hx => show x ≠ c from fun hxc => hc (hxc ▸ hx)) hne

/-- **p. 186**. Strict risk aversion is equivalent to strict concavity of `u`. -/
theorem strictlyRiskAverse_iff {S : Set ℝ} (hS : Convex ℝ S) {u : ℝ → ℝ}
    (hu : ContinuousOn u S) : StrictlyRiskAverse S (euPref u) ↔ StrictConcaveOn ℝ S u := by
  constructor
  · rintro ⟨hra, hstr⟩
    have hc := (proposition_6_C_1_i_ii hS hu).mp hra
    refine ⟨hS, fun x hx y hy hxy a b ha hb hab => ?_⟩
    have hb' : b = 1 - a := by linarith
    subst hb'
    have hμ := binLot_isMoneyLottery hS hx hy a ha.le (by linarith)
    have hle := hc.2 hx hy ha.le hb.le hab
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact hlt
    · exfalso
      have hind : euPref u (binLot a x y) (Measure.dirac (∫ z, z ∂(binLot a x y))) := by
        simp only [euPref, integral_dirac, integral_binLot _ _ _ _ ha.le (by linarith : a ≤ 1)]
        simp only [smul_eq_mul] at heq
        exact heq.ge
      have hdeg := hstr _ hμ hind
      rw [mean_binLot _ _ _ ha.le (by linarith)] at hdeg
      have hval : binLot a x y {x} = Measure.dirac (a * x + (1 - a) * y) {x} := by rw [← hdeg]
      have hL : binLot a x y {x} = ENNReal.ofReal a := by
        simp [binLot, Measure.dirac_apply' _ (measurableSet_singleton x), Ne.symm hxy]
      rw [hL, Measure.dirac_apply' _ (measurableSet_singleton x)] at hval
      by_cases hm : a * x + (1 - a) * y = x
      · have : (1 - a) * (y - x) = 0 := by linarith
        rcases mul_eq_zero.mp this with h | h
        · linarith
        · exact hxy (by linarith)
      · rw [indicator_of_notMem (by simpa using hm)] at hval
        rw [ENNReal.ofReal_eq_zero] at hval
        linarith
  · intro hsc
    have hc := hsc.concaveOn
    refine ⟨(proposition_6_C_1_i_ii hS hu).mpr hc, fun μ hμ hind => ?_⟩
    have := hμ.1
    obtain ⟨a, b, hSab, hae⟩ := hμ.ae_mem
    have hstrict := (hsc.subset hSab (convex_Icc a b)).ae_eq_const_or_lt_map_average
      (hu.mono hSab) isClosed_Icc hae hμ.integrable_id (hμ.integrable hu)
    simp only [average_eq_integral] at hstrict
    rcases hstrict with hconst | hlt
    · exact eq_dirac_of_ae_eq_const hconst
    · exfalso
      simp only [euPref, integral_dirac] at hind
      exact absurd hind (not_le.mpr hlt)

/-- **p. 186**. Risk neutrality is equivalent to `u` being linear (affine) on `S`. -/
theorem riskNeutral_iff_affine {S : Set ℝ} (hS : Convex ℝ S) {u : ℝ → ℝ}
    (hu : ContinuousOn u S) :
    RiskNeutral S (euPref u) ↔ ConcaveOn ℝ S u ∧ ConvexOn ℝ S u := by
  constructor
  · intro h
    refine ⟨(proposition_6_C_1_i_ii hS hu).mp fun μ hμ => (h μ hμ).1,
      ⟨hS, fun x hx y hy a b ha hb hab => ?_⟩⟩
    have hb' : b = 1 - a := by linarith
    subst hb'
    have := (h _ (binLot_isMoneyLottery hS hx hy a ha (by linarith))).2
    simp only [euPref, integral_dirac, integral_binLot _ _ _ _ ha (by linarith : a ≤ 1)] at this
    simpa only [smul_eq_mul] using this
  · rintro ⟨hc, hv⟩ μ hμ
    have := hμ.1
    obtain ⟨a, b, hSab, hae⟩ := hμ.ae_mem
    refine ⟨(proposition_6_C_1_i_ii hS hu).mpr hc μ hμ, ?_⟩
    simp only [euPref, integral_dirac]
    exact (hv.subset hSab (convex_Icc a b)).map_integral_le (hu.mono hSab) isClosed_Icc hae
      hμ.integrable_id (hμ.integrable hu)

/-- **Footnote 16** (MWG, p. 187). For a twice differentiable `u` on an open convex set,
concavity is equivalent to `u''(x) ≤ 0` for all `x`. -/
theorem footnote_6_16 {S : Set ℝ} (hS : Convex ℝ S) (ho : IsOpen S) {u : ℝ → ℝ}
    (h1 : ∀ x ∈ S, DifferentiableAt ℝ u x) (h2 : ∀ x ∈ S, DifferentiableAt ℝ (deriv u) x) :
    ConcaveOn ℝ S u ↔ ∀ x ∈ S, deriv (deriv u) x ≤ 0 := by
  constructor
  · intro hc x hx
    have hant := hc.antitoneOn_deriv h1
    have := hant.derivWithin_nonpos (x := x)
    rwa [derivWithin_of_isOpen ho hx] at this
  · intro h
    have hint : interior S = S := ho.interior_eq
    apply concaveOn_of_deriv2_nonpos hS
      (fun x hx => (h1 x hx).continuousAt.continuousWithinAt)
    · rw [hint]; exact fun x hx => (h1 x hx).differentiableWithinAt
    · rw [hint]; exact fun x hx => (h2 x hx).differentiableWithinAt
    · rw [hint]; intro x hx
      simpa only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply,
        Function.id_comp] using h x hx

end MWG.ChoiceUnderUncertainty
