/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import Mathlib.Probability.CDF
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import MWGChoiceUnderUncertainty.ExpectedUtilityTheorem

/-!
# Lotteries over monetary outcomes

MWG, Section 6.C, pp. 183-185: money lotteries as distribution functions, the linear structure
of distribution functions, Figure 6.C.1, the expected utility form (6.C.1), the
St. Petersburg-Menger paradox and footnote 14.

A money lottery on a set `S ⊆ ℝ` of monetary amounts is a Borel probability measure `μ` on `ℝ`
concentrated on a compact interval `[a, b] ⊆ S` (`IsMoneyLottery`); its distribution function
is Mathlib's `cdf μ`, `F(x) = μ(-∞, x]`. MWG leaves the integrability of `u` and of `x`
unspecified; concentration on a compact interval guarantees that every expectation
`∫ u dF` of a continuous `u` exists (Section 6.D imposes exactly this, `F(0) = 0` and
`F(x̄) = 1`). The text's statement that the expected utility theorem yields (6.C.1),
`U(F) = ∫ u dF`, on all distributions is false under MWG's axioms: `atomicMass`, the total mass
of the atoms, is affine, so its preference is rational, continuous and satisfies independence,
but it has no Bernoulli utility (`expectedUtility_6_C_1_counterexample`).
-/

namespace MWG.ChoiceUnderUncertainty

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

/-- A money lottery on `S`: a probability measure on `ℝ` concentrated on a compact interval
contained in `S`. -/
def IsMoneyLottery (S : Set ℝ) (μ : Measure ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ ∃ a b, Icc a b ⊆ S ∧ μ (Icc a b)ᶜ = 0

/-- A money lottery is concentrated on its interval almost surely. -/
theorem IsMoneyLottery.ae_mem {S : Set ℝ} {μ : Measure ℝ} (h : IsMoneyLottery S μ) :
    ∃ a b, Icc a b ⊆ S ∧ ∀ᵐ x ∂μ, x ∈ Icc a b := by
  obtain ⟨-, a, b, hS, h0⟩ := h
  exact ⟨a, b, hS, measure_eq_zero_iff_ae_notMem.mp h0 |>.mono fun x hx => by simpa using hx⟩

/-- A function continuous on `S` is integrable for every money lottery on `S`. -/
theorem IsMoneyLottery.integrable {S : Set ℝ} {μ : Measure ℝ} (h : IsMoneyLottery S μ)
    {u : ℝ → ℝ} (hu : ContinuousOn u S) : Integrable u μ := by
  have := h.1
  obtain ⟨a, b, hS, h0⟩ := h.2
  have hr : μ.restrict (Icc a b) = μ := Measure.restrict_eq_self_of_ae_mem
    (measure_eq_zero_iff_ae_notMem.mp h0 |>.mono fun x hx => by simpa using hx)
  have hi : IntegrableOn u (Icc a b) μ := (hu.mono hS).integrableOn_compact isCompact_Icc
  rw [IntegrableOn, hr] at hi
  exact hi

/-- The identity (the monetary amount) is integrable for every money lottery. -/
theorem IsMoneyLottery.integrable_id {S : Set ℝ} {μ : Measure ℝ} (h : IsMoneyLottery S μ) :
    Integrable (fun x : ℝ => x) μ := by
  obtain ⟨hp, a, b, -, h0⟩ := h
  exact IsMoneyLottery.integrable (S := Icc a b) ⟨hp, a, b, le_rfl, h0⟩ continuousOn_id

/-- The mean of a money lottery lies in its interval, hence in `S`. -/
theorem IsMoneyLottery.mean_mem {S : Set ℝ} {μ : Measure ℝ} (h : IsMoneyLottery S μ) :
    ∃ a b, Icc a b ⊆ S ∧ (∀ᵐ x ∂μ, x ∈ Icc a b) ∧ ∫ x, x ∂μ ∈ Icc a b := by
  have := h.1
  obtain ⟨a, b, hS, hae⟩ := h.ae_mem
  refine ⟨a, b, hS, hae, ?_, ?_⟩
  · calc a = ∫ _, a ∂μ := by simp
      _ ≤ ∫ x, x ∂μ := integral_mono_ae (integrable_const a) h.integrable_id
          (hae.mono fun x hx => hx.1)
  · calc ∫ x, x ∂μ ≤ ∫ _, b ∂μ := integral_mono_ae h.integrable_id (integrable_const b)
          (hae.mono fun x hx => hx.2)
      _ = b := by simp

/-- The mean of a money lottery on `S` lies in `S`. -/
theorem IsMoneyLottery.mean_mem_S {S : Set ℝ} {μ : Measure ℝ} (h : IsMoneyLottery S μ) :
    ∫ x, x ∂μ ∈ S := by
  obtain ⟨a, b, hS, -, hm⟩ := h.mean_mem
  exact hS hm

/-- The binary lottery paying `x` with probability `p` and `y` with probability `1 - p`. -/
noncomputable def binLot (p x y : ℝ) : Measure ℝ :=
  ENNReal.ofReal p • Measure.dirac x + ENNReal.ofReal (1 - p) • Measure.dirac y

/-- Expectations under a binary lottery. -/
theorem integral_binLot (p x y : ℝ) (f : ℝ → ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∫ z, f z ∂(binLot p x y) = p * f x + (1 - p) * f y := by
  unfold binLot
  rw [integral_add_measure, integral_smul_measure, integral_smul_measure, integral_dirac,
    integral_dirac, ENNReal.toReal_ofReal hp0, ENNReal.toReal_ofReal (by linarith)]
  · simp [smul_eq_mul]
  · exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  · exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

/-- A binary lottery is a probability measure. -/
theorem binLot_isProbabilityMeasure (p x y : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (binLot p x y) := by
  constructor
  simp only [binLot, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add hp0 (by linarith)]
  simp

/-- A binary lottery with prizes in a convex `S` is a money lottery on `S`. -/
theorem binLot_isMoneyLottery {S : Set ℝ} (hS : Convex ℝ S) {x y : ℝ} (hx : x ∈ S) (hy : y ∈ S)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : IsMoneyLottery S (binLot p x y) := by
  refine ⟨binLot_isProbabilityMeasure p x y hp0 hp1, min x y, max x y,
    hS.ordConnected.uIcc_subset hx hy, ?_⟩
  simp only [binLot, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  rw [Measure.dirac_apply' _ (measurableSet_Icc.compl),
    Measure.dirac_apply' _ (measurableSet_Icc.compl)]
  simp

/-- The degenerate lottery at `x` is a money lottery on any `S ∋ x`. -/
theorem dirac_isMoneyLottery {S : Set ℝ} {x : ℝ} (hx : x ∈ S) :
    IsMoneyLottery S (Measure.dirac x) := by
  refine ⟨inferInstance, x, x, by simpa using hx, ?_⟩
  rw [Measure.dirac_apply' _ (measurableSet_Icc.compl)]
  simp

/-- The mixture `αF + (1 - α)G` of two lotteries. -/
noncomputable def mixM (a : ℝ) (μ ν : Measure ℝ) : Measure ℝ :=
  ENNReal.ofReal a • μ + ENNReal.ofReal (1 - a) • ν

/-- A mixture of probability measures is a probability measure. -/
theorem mixM_isProbabilityMeasure {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) {μ ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : IsProbabilityMeasure (mixM a μ ν) := by
  constructor
  simp only [mixM, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add ha0 (by linarith)]
  simp

/-- The measure of a set under a mixture of probability measures. -/
theorem mixM_real {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) {μ ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (s : Set ℝ) :
    (mixM a μ ν).real s = a * μ.real s + (1 - a) * ν.real s := by
  simp only [mixM, measureReal_def, Measure.coe_add, Measure.coe_smul, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)), ENNReal.toReal_mul,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal ha0, ENNReal.toReal_ofReal (by linarith)]

/-- **p. 183**. Distribution functions preserve the linear structure of lotteries: the
distribution of the mixture `αF + (1 - α)G` is `αF(x) + (1 - α)G(x)`. -/
theorem cdf_mixM {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) {μ ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (x : ℝ) :
    cdf (mixM a μ ν) x = a * cdf μ x + (1 - a) * cdf ν x := by
  have := mixM_isProbabilityMeasure ha0 ha1 (μ := μ) (ν := ν)
  rw [cdf_eq_real, cdf_eq_real, cdf_eq_real, mixM_real ha0 ha1]

/-- The lottery of Figure 6.C.1: `1`, `4`, `6` dollars with probabilities `1/4`, `1/2`,
`1/4`. -/
noncomputable def figure_6_C_1_lottery : Measure ℝ :=
  ENNReal.ofReal (1 / 4) • Measure.dirac 1 + ENNReal.ofReal (1 / 2) • Measure.dirac 4 +
    ENNReal.ofReal (1 / 4) • Measure.dirac 6

/-- **Figure 6.C.1** (MWG, p. 184). The distribution function of the lottery is `0` on
`x < 1`, `1/4` on `[1,4)`, `3/4` on `[4,6)` and `1` on `x ≥ 6`. -/
theorem figure_6_C_1 (x : ℝ) :
    figure_6_C_1_lottery.real (Iic x) =
      if x < 1 then 0 else if x < 4 then 1 / 4 else if x < 6 then 3 / 4 else 1 := by
  have hd (c : ℝ) : (Measure.dirac c) (Iic x) = if c ≤ x then 1 else 0 := by
    rw [Measure.dirac_apply' _ measurableSet_Iic]
    by_cases h : c ≤ x <;> simp [h]
  simp only [figure_6_C_1_lottery, measureReal_def, Measure.coe_add, Measure.coe_smul,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, hd]
  split_ifs <;> first
    | (exfalso; linarith)
    | (simp only [mul_one, mul_zero, add_zero]
       rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
       try rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
       rw [ENNReal.toReal_ofReal (by norm_num)]; norm_num)
    | simp

/-- **p. 185** (St. Petersburg-Menger paradox). If `u(x_m) > 2^m` for every `m`, the lottery
paying `x_m` with probability `1/2^m` (`m ≥ 1`) has infinite expected utility: the partial sums
`∑_{m=1}^{N} u(x_m)/2^m` tend to `+∞`. -/
theorem stPetersburg (u : ℝ → ℝ) (x : ℕ → ℝ) (hx : ∀ m, (2 : ℝ) ^ m < u (x m)) :
    Tendsto (fun N => ∑ m ∈ Finset.Icc 1 N, u (x m) * (1 / 2) ^ m) atTop atTop := by
  have hterm (m : ℕ) : 1 < u (x m) * (1 / 2) ^ m := by
    have h2 : (0 : ℝ) < (1 / 2) ^ m := by positivity
    have : (2 : ℝ) ^ m * (1 / 2) ^ m = 1 := by rw [← mul_pow]; norm_num
    nlinarith [hx m]
  refine tendsto_atTop_mono (f := fun N : ℕ => (N : ℝ)) (fun N => ?_) tendsto_natCast_atTop_atTop
  calc (N : ℝ) = ∑ m ∈ Finset.Icc 1 N, (1 : ℝ) := by simp
    _ ≤ _ := Finset.sum_le_sum fun m _ => (hterm m).le

/-- **p. 185**. The St. Petersburg probabilities `1/2^m`, `m ≥ 1`, sum to one. -/
theorem stPetersburg_probabilities : HasSum (fun m : ℕ => (1 / 2 : ℝ) ^ (m + 1)) 1 := by
  have := hasSum_geometric_two' (1 : ℝ)
  convert this using 1
  ext m
  rw [pow_succ]
  field_simp
  rw [← mul_pow]
  norm_num

/-- For a concave function on the line that is bounded below, `u x ≤ u y` for all `x, y`. -/
theorem concave_bddBelow_le {u : ℝ → ℝ} (hc : ConcaveOn ℝ univ u) {m : ℝ}
    (hlow : ∀ z, m ≤ u z) (x y : ℝ) : u x ≤ u y := by
  by_contra hlt
  have hlt : u y < u x := lt_of_not_ge hlt
  have hd : 0 < u x - u y := by linarith
  obtain ⟨t, ht0, ht⟩ : ∃ t : ℝ, 0 < t ∧ u y - t * (u x - u y) < m := by
    refine ⟨(u y - m + 1) / (u x - u y) + 1, ?_, ?_⟩
    · have : 0 ≤ (u y - m + 1) / (u x - u y) :=
        div_nonneg (by linarith [hlow y]) hd.le
      linarith
    · rw [add_mul, div_mul_cancel₀ _ hd.ne']
      linarith
  have h1t : (1 : ℝ) + t ≠ 0 := by linarith
  have h1t' : (0 : ℝ) < 1 + t := by linarith
  set z := y + t * (y - x)
  have hy : (t / (1 + t)) • x + (1 / (1 + t)) • z = y := by
    simp only [smul_eq_mul, z]; field_simp; ring
  have hconc := hc.2 (mem_univ x) (mem_univ z) (show 0 ≤ t / (1 + t) by positivity)
    (show 0 ≤ 1 / (1 + t) by positivity)
    (by rw [← add_div, div_eq_one_iff_eq h1t]; ring)
  rw [hy] at hconc
  simp only [smul_eq_mul] at hconc
  have h1 : u z ≤ u y - t * (u x - u y) := by
    field_simp at hconc
    nlinarith
  linarith [hlow z]

/-- **Footnote 14** (MWG, p. 185). A concave function on `(-∞, ∞)` that is bounded below is
constant; so a nonconstant Bernoulli utility on the whole line cannot be both concave and
bounded (above and below). -/
theorem footnote_6_14 {u : ℝ → ℝ} (hc : ConcaveOn ℝ univ u) (hb : BddBelow (range u)) :
    ∀ x y, u x = u y := by
  obtain ⟨m, hm⟩ := hb
  have hlow (z : ℝ) : m ≤ u z := hm ⟨z, rfl⟩
  exact fun x y => le_antisymm (concave_bddBelow_le hc hlow x y) (concave_bddBelow_le hc hlow y x)

/-- MWG's continuity axiom (Definition 6.B.3) for a preference on the money lotteries on `S`:
`{α ∈ [0,1] : αF + (1 - α)G ≿ H}` and `{α ∈ [0,1] : H ≿ αF + (1 - α)G}` are closed. -/
def MoneyContinuous (S : Set ℝ) (r : Measure ℝ → Measure ℝ → Prop) : Prop :=
  ∀ μ ν η, IsMoneyLottery S μ → IsMoneyLottery S ν → IsMoneyLottery S η →
    IsClosed {a : Kreps.ChoiceUnderUncertainty.Weight | r (mixM a.val μ ν) η} ∧
    IsClosed {a : Kreps.ChoiceUnderUncertainty.Weight | r η (mixM a.val μ ν)}

/-- MWG's independence axiom (Definition 6.B.4) for a preference on the money lotteries on
`S`. -/
def MoneyIndependence (S : Set ℝ) (r : Measure ℝ → Measure ℝ → Prop) : Prop :=
  ∀ μ ν η, IsMoneyLottery S μ → IsMoneyLottery S ν → IsMoneyLottery S η →
    ∀ a : ℝ, 0 < a → a < 1 → (r μ ν ↔ r (mixM a μ η) (mixM a ν η))

/-- Completeness and transitivity on the money lotteries on `S`. -/
def MoneyRational (S : Set ℝ) (r : Measure ℝ → Measure ℝ → Prop) : Prop :=
  (∀ μ ν, IsMoneyLottery S μ → IsMoneyLottery S ν → r μ ν ∨ r ν μ) ∧
  ∀ μ ν η, IsMoneyLottery S μ → IsMoneyLottery S ν → IsMoneyLottery S η →
    r μ ν → r ν η → r μ η

/-- The total mass `∑_x F({x})` of the atoms of a lottery. -/
noncomputable def atomicMass (μ : Measure ℝ) : ℝ := (∑' x : ℝ, μ {x}).toReal

/-- The atoms of a probability measure have total mass at most one. -/
theorem tsum_atoms_le_one (μ : Measure ℝ) [IsProbabilityMeasure μ] : ∑' x : ℝ, μ {x} ≤ 1 :=
  (tsum_meas_le_meas_iUnion_of_disjoint μ (fun x => measurableSet_singleton x)
    (fun _ _ hxy => Set.disjoint_singleton.mpr hxy)).trans prob_le_one

/-- The atomic mass is affine in mixtures. -/
theorem atomicMass_mixM {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    atomicMass (mixM a μ ν) = a * atomicMass μ + (1 - a) * atomicMass ν := by
  have h1 := tsum_atoms_le_one μ
  have h2 := tsum_atoms_le_one ν
  have hμ : ∑' x : ℝ, μ {x} ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top h1
  have hν : ∑' x : ℝ, ν {x} ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top h2
  unfold atomicMass mixM
  simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left,
    ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hμ)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hν),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal ha0,
    ENNReal.toReal_ofReal (by linarith)]

/-- A degenerate lottery has atomic mass one. -/
theorem atomicMass_dirac (x : ℝ) : atomicMass (Measure.dirac x) = 1 := by
  unfold atomicMass
  have : (fun y : ℝ => Measure.dirac x {y}) = fun y => if y = x then 1 else 0 := by
    ext y
    rw [Measure.dirac_apply' _ (measurableSet_singleton y)]
    by_cases h : y = x
    · simp [h]
    · simp [h, Ne.symm h]
  rw [this, tsum_ite_eq]
  simp

/-- The uniform lottery on `[0,1]`. -/
noncomputable def uniform01 : Measure ℝ := volume.restrict (Icc 0 1)

/-- The uniform lottery on `[0,1]` is a money lottery on every `S ⊇ [0,1]`. -/
theorem uniform01_isMoneyLottery {S : Set ℝ} (hS : Icc 0 1 ⊆ S) :
    IsMoneyLottery S uniform01 := by
  refine ⟨⟨by simp [uniform01]⟩, 0, 1, hS, ?_⟩
  rw [uniform01, Measure.restrict_apply measurableSet_Icc.compl]
  simp

/-- The uniform lottery has no atoms. -/
theorem atomicMass_uniform01 : atomicMass uniform01 = 0 := by
  unfold atomicMass
  have : (fun y : ℝ => uniform01 {y}) = fun _ => 0 := by
    ext y
    exact le_antisymm ((Measure.restrict_apply_le _ _).trans_eq Real.volume_singleton) bot_le
  rw [this]
  simp

/-- **p. 184, (6.C.1)**: correction. MWG's axioms on general distributions do not yield the
integral form `U(F) = ∫ u dF`. The preference ranking lotteries by the total mass of their
atoms is rational, continuous and satisfies independence on all money lotteries, yet no
Bernoulli utility `u` represents it by `∫ u dF`. -/
theorem expectedUtility_6_C_1_counterexample :
    let r : Measure ℝ → Measure ℝ → Prop := fun μ ν => atomicMass ν ≤ atomicMass μ
    MoneyRational univ r ∧ MoneyContinuous univ r ∧ MoneyIndependence univ r ∧
      ¬∃ u : ℝ → ℝ, ∀ μ ν, IsMoneyLottery univ μ → IsMoneyLottery univ ν →
        (r μ ν ↔ ∫ x, u x ∂ν ≤ ∫ x, u x ∂μ) := by
  intro r
  refine ⟨⟨fun μ ν _ _ => le_total _ _, fun μ ν η _ _ _ h1 h2 => h2.trans h1⟩, ?_, ?_, ?_⟩
  · intro μ ν η hμ hν _
    have := hμ.1; have := hν.1
    have hc : Continuous fun a : Kreps.ChoiceUnderUncertainty.Weight =>
        atomicMass (mixM a.val μ ν) := by
      have : (fun a : Kreps.ChoiceUnderUncertainty.Weight => atomicMass (mixM a.val μ ν)) =
          fun a => a.val * atomicMass μ + (1 - a.val) * atomicMass ν :=
        funext fun a => atomicMass_mixM a.property.1 a.property.2 μ ν
      rw [this]; fun_prop
    exact ⟨isClosed_le continuous_const hc, isClosed_le hc continuous_const⟩
  · intro μ ν η hμ hν hη a ha0 ha1
    have := hμ.1; have := hν.1; have := hη.1
    change atomicMass ν ≤ atomicMass μ ↔ atomicMass (mixM a ν η) ≤ atomicMass (mixM a μ η)
    rw [atomicMass_mixM ha0.le ha1.le, atomicMass_mixM ha0.le ha1.le]
    constructor
    · intro h; nlinarith
    · intro h; nlinarith
  · rintro ⟨u, hu⟩
    have hconst (x y : ℝ) : u x = u y := by
      have h := hu (Measure.dirac x) (Measure.dirac y) (dirac_isMoneyLottery (mem_univ x))
        (dirac_isMoneyLottery (mem_univ y))
      have h' := hu (Measure.dirac y) (Measure.dirac x) (dirac_isMoneyLottery (mem_univ y))
        (dirac_isMoneyLottery (mem_univ x))
      simp only [r, atomicMass_dirac, le_refl, true_iff, integral_dirac] at h h'
      exact le_antisymm h' h
    have h := hu uniform01 (Measure.dirac 0) (uniform01_isMoneyLottery (subset_univ _))
      (dirac_isMoneyLottery (mem_univ 0))
    have hint : ∫ x, u x ∂uniform01 = u 0 := by
      have : IsProbabilityMeasure uniform01 := (uniform01_isMoneyLottery (subset_univ _)).1
      rw [show (fun x => u x) = fun _ => u 0 from funext fun x => hconst x 0]
      simp
    simp only [r, atomicMass_dirac, atomicMass_uniform01, integral_dirac, hint, le_refl,
      iff_true] at h
    norm_num at h

end MWG.ChoiceUnderUncertainty
