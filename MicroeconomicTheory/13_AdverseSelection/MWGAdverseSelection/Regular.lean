/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGAdverseSelection.Continuity

/-!
# The adverse selection model with increasing `r`

MWG, Section 13.B, pp. 441-444.

From p. 441 on, MWG assume `r(θ) ≤ θ` on `[θ̲, θ̄]`, `r` strictly increasing and `F` with a
positive density. Here we collect what this gives for `Θ(w) = {θ : r(θ) ≤ w}` and for the set `W*`
of competitive equilibrium wages:

* below `r(θ̲)` nobody accepts employment and no wage is an equilibrium wage (footnote 7);
* at `w = r(θ̲)` only the null set `{θ̲}` accepts, and `r(θ̲) ∈ W*` iff `r(θ̲) = θ̲`
  (Figure 13.B.2);
* if `r` is also continuous, `Θ(w)` has positive probability for every `w > r(θ̲)`, and then
  `w ∈ W*` iff the firm's profit `Π(w) = ∫_{Θ(w)} (θ - w) dF` is zero;
* `exists_isGreatest_eqWages`: `W*` is nonempty and has a largest element (the book's
  `w* = Max W*`, p. 443).
-/

namespace MWG.AdverseSelection

open MeasureTheory Filter Topology

/-- Only the part of `Θ(w)` in `[θ̲, θ̄]` matters for probabilities. -/
theorem measure_acceptSet_inter {μ : Measure ℝ} {θl θh : ℝ} (hd : TypeDist μ θl θh) (S : Set ℝ) :
    μ (S ∩ Set.Icc θl θh) = μ S := by
  refine measure_congr ?_
  filter_upwards [hd.ae_mem] with θ hθ
  simp only [Set.mem_inter_iff, eq_iff_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, hθ⟩⟩

/-- If `S` contains `[θ̲, θ̄]` then `E[θ | θ ∈ S] = E[θ]`. -/
theorem condMean_of_superset {μ : Measure ℝ} {θl θh : ℝ} (hd : TypeDist μ θl θh) {S : Set ℝ}
    (hS : Set.Icc θl θh ⊆ S) : condMean μ θl θh S = meanType μ := by
  have := hd.prob
  have hSae : ∀ᵐ θ ∂μ, θ ∈ S := hd.ae_mem.mono fun _ h => hS h
  have h1 : μ S = 1 := by
    rw [← measure_acceptSet_inter hd, Set.inter_eq_right.2 hS]
    have : μ (Set.Icc θl θh) = μ Set.univ := measure_congr (by
      filter_upwards [hd.ae_mem] with θ hθ; simp [hθ])
    rw [this, measure_univ]
  have hint : ∫ θ in S, θ ∂μ = ∫ θ, θ ∂μ :=
    setIntegral_eq_integral_of_ae_compl_eq_zero (hSae.mono fun _ h hc => absurd h hc)
  simp only [condMean, h1, zero_lt_one, ↓reduceIte, hint, ENNReal.toReal_one, div_one,
    meanType]

/-- A wage at which (almost) every hired type has `θ < w` makes a strict loss. -/
theorem firmProfit_neg_of_ae_lt {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ} (hd : TypeDist μ θl θh)
    (hr : Measurable r) {w : ℝ} (hpos : 0 < μ (acceptSet r w))
    (hlt : ∀ᵐ θ ∂μ, θ ∈ acceptSet r w → θ < w) : firmProfit μ r w < 0 := by
  have := hd.prob
  rw [firmProfit_eq_setIntegral hr, ← neg_pos, ← integral_neg]
  refine setIntegral_pos_of_ae_pos (measurableSet_acceptSet hr w) hpos
    (hlt.mono fun θ hθ hm => by linarith [hθ hm]) ?_
  exact (hd.integrable_id.sub (integrable_const w)).neg.integrableOn

/-- **Footnote 7** (MWG, p. 441). Below `r(θ̲)` no type in `[θ̲, θ̄]` accepts employment. -/
theorem acceptSet_inter_eq_empty {θl θh : ℝ} {r : ℝ → ℝ} (hmono : MonotoneOn r (Set.Icc θl θh))
    {w : ℝ} (hw : w < r θl) : acceptSet r w ∩ Set.Icc θl θh = ∅ := by
  ext θ
  simp only [acceptSet, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
    not_and]
  intro h hθ
  have hl : θl ∈ Set.Icc θl θh := ⟨le_rfl, hθ.1.trans hθ.2⟩
  linarith [hmono hl hθ hθ.1]

/-- **Figure 13.B.2** (MWG, pp. 441-442). At `w = r(θ̲)` only the type `θ̲` accepts. -/
theorem acceptSet_inter_eq_singleton {θl θh : ℝ} {r : ℝ → ℝ} (hlt : θl < θh)
    (hmono : StrictMonoOn r (Set.Icc θl θh)) : acceptSet r (r θl) ∩ Set.Icc θl θh = {θl} := by
  ext θ
  simp only [acceptSet, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h, hθ⟩
    have hl : θl ∈ Set.Icc θl θh := ⟨le_rfl, hlt.le⟩
    by_contra hne
    have := hmono hl hθ (lt_of_le_of_ne hθ.1 (Ne.symm hne))
    linarith
  · rintro rfl; exact ⟨le_rfl, le_rfl, hlt.le⟩

/-- **Section 13.B** (MWG, p. 441). With `r` continuous and positive density, every wage above
`r(θ̲)` attracts a set of workers of positive probability. -/
theorem measure_acceptSet_pos {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ} (hd : TypeDist μ θl θh)
    (hden : HasPosDensity μ θl θh) (hcont : ContinuousOn r (Set.Icc θl θh)) {w : ℝ}
    (hw : r θl < w) : 0 < μ (acceptSet r w) := by
  have hl : θl ∈ Set.Icc θl θh := ⟨le_rfl, hd.lt.le⟩
  have hev : ∀ᶠ θ in 𝓝[≥] θl, r θ < w := by
    have := (hcont θl hl).eventually (Iio_mem_nhds hw)
    rwa [nhdsWithin_Icc_eq_nhdsGE hd.lt] at this
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGE_iff_exists_Icc_subset.1 hev
  set v := min u θh
  have hv : θl < v := lt_min hu hd.lt
  refine (hden.pos θl v le_rfl hv (min_le_right _ _)).trans_le (measure_mono ?_)
  intro θ hθ
  exact le_of_lt (show r θ < w from hsub ⟨hθ.1, hθ.2.trans (min_le_left _ _)⟩)

/-- **Footnote 7** (MWG, p. 441). No wage below `r(θ̲)` is a competitive equilibrium wage. -/
theorem not_mem_eqWages_of_lt {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ} (hd : TypeDist μ θl θh)
    (hmono : MonotoneOn r (Set.Icc θl θh)) (hrθ : ∀ θ ∈ Set.Icc θl θh, r θ ≤ θ) {w : ℝ}
    (hw : w < r θl) : w ∉ eqWages μ θl θh r := by
  rw [mem_eqWages_iff]
  have hempty := acceptSet_inter_eq_empty hmono hw
  have h0 : μ (acceptSet r w) = 0 := by
    rw [← measure_acceptSet_inter hd, hempty, measure_empty]
  have hl : θl ∈ Set.Icc θl θh := ⟨le_rfl, hd.lt.le⟩
  simp only [condMean, h0, lt_self_iff_false, ↓reduceIte, hempty, Set.not_nonempty_empty]
  intro h
  linarith [hd.meanType_mem.1, hrθ θl hl]

/-- **Figure 13.B.2** (MWG, p. 442). `r(θ̲) ∈ W*` iff `r(θ̲) = θ̲`. -/
theorem mem_eqWages_rl_iff {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ} (hd : TypeDist μ θl θh)
    (hmono : StrictMonoOn r (Set.Icc θl θh)) (hden : HasPosDensity μ θl θh) :
    r θl ∈ eqWages μ θl θh r ↔ r θl = θl := by
  rw [mem_eqWages_iff]
  have hs := acceptSet_inter_eq_singleton hd.lt hmono
  have h0 : μ (acceptSet r (r θl)) = 0 := by
    rw [← measure_acceptSet_inter hd, hs, hden.noAtom]
  simp only [condMean, h0, lt_self_iff_false, ↓reduceIte, hs, Set.singleton_nonempty]

/-- At `w = r(θ̲)` the firm's profit is zero. -/
theorem firmProfit_rl {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ} (hd : TypeDist μ θl θh)
    (hmono : StrictMonoOn r (Set.Icc θl θh)) (hden : HasPosDensity μ θl θh) (hr : Measurable r) :
    firmProfit μ r (r θl) = 0 := by
  refine firmProfit_of_null hr ?_
  rw [← measure_acceptSet_inter hd, acceptSet_inter_eq_singleton hd.lt hmono, hden.noAtom]

/-- Below `r(θ̲)` the firm's profit is zero. -/
theorem firmProfit_of_lt {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ} (hd : TypeDist μ θl θh)
    (hmono : MonotoneOn r (Set.Icc θl θh)) (hr : Measurable r) {w : ℝ} (hw : w < r θl) :
    firmProfit μ r w = 0 := by
  refine firmProfit_of_null hr ?_
  rw [← measure_acceptSet_inter hd, acceptSet_inter_eq_empty hmono hw, measure_empty]

/-- **Section 13.B** (MWG, p. 444). A firm offering `w = 0` never makes a loss: `Π(0) ≥ 0`
(types are nonnegative). -/
theorem firmProfit_zero_nonneg {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ} (hd : TypeDist μ θl θh)
    (hr : Measurable r) : 0 ≤ firmProfit μ r 0 := by
  rw [firmProfit_eq_setIntegral hr]
  exact setIntegral_nonneg_of_ae_restrict
    (ae_restrict_of_ae (hd.ae_mem.mono fun θ hθ =>
      show (0 : ℝ) ≤ θ - 0 by linarith [hd.nonneg, hθ.1]))

/-- The regular adverse selection model of p. 441, plus continuity of `r`: `F` has a positive
density on `[θ̲, θ̄]`, `r` is measurable, continuous and strictly increasing there, and
`r(θ) ≤ θ`. -/
structure RegularModel (μ : Measure ℝ) (θl θh : ℝ) (r : ℝ → ℝ) : Prop where
  dist : TypeDist μ θl θh
  dens : HasPosDensity μ θl θh
  meas : Measurable r
  mono : StrictMonoOn r (Set.Icc θl θh)
  cont : ContinuousOn r (Set.Icc θl θh)
  le : ∀ θ ∈ Set.Icc θl θh, r θ ≤ θ

/-- The profit is continuous in the regular model. -/
theorem RegularModel.continuous {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ}
    (h : RegularModel μ θl θh r) : Continuous (firmProfit μ r) :=
  continuous_firmProfit h.dist h.dens.noAtom h.meas h.mono.injOn

/-- In the regular model, `w > r(θ̲)` is an equilibrium wage iff `Π(w) = 0`. -/
theorem RegularModel.mem_eqWages_iff {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ}
    (h : RegularModel μ θl θh r) {w : ℝ} (hw : r θl < w) :
    w ∈ eqWages μ θl θh r ↔ firmProfit μ r w = 0 :=
  mem_eqWages_iff_profit h.dist h.meas (measure_acceptSet_pos h.dist h.dens h.cont hw)

/-- **Section 13.B** (MWG, p. 444). If `w*` is the largest equilibrium wage then
`E[θ | r(θ) ≤ w] < w`, i.e. `Π(w) < 0`, for every `w > w*` (the book's continuity argument,
via the intermediate value theorem). -/
theorem RegularModel.firmProfit_neg_of_gt_max {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ}
    (h : RegularModel μ θl θh r) {ws : ℝ} (hmax : IsGreatest (eqWages μ θl θh r) ws) {w : ℝ}
    (hw : ws < w) : firmProfit μ r w < 0 := by
  have hl : θl ∈ Set.Icc θl θh := ⟨le_rfl, h.dist.lt.le⟩
  have hws : r θl ≤ ws := by
    by_contra hlt
    exact not_mem_eqWages_of_lt h.dist h.mono.monotoneOn h.le (not_le.1 hlt) hmax.1
  have hrw : r θl < w := hws.trans_lt hw
  have hne : firmProfit μ r w ≠ 0 := by
    intro h0
    exact absurd (hmax.2 ((h.mem_eqWages_iff hrw).2 h0)) (not_le.2 hw)
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · exact hneg
  · exfalso
    set b := max w θh + 1
    have hwb : w ≤ b := by simp only [b]; linarith [le_max_left w θh]
    have hbθ : θh < b := by simp only [b]; linarith [le_max_right w θh]
    have hb : firmProfit μ r b < 0 :=
      firmProfit_neg_of_gt h.dist h.meas hbθ
        (measure_acceptSet_pos h.dist h.dens h.cont (hrw.trans_le hwb))
    obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc' hwb h.continuous.continuousOn
      ⟨hb.le, hpos.le⟩
    have hcm : c ∈ eqWages μ θl θh r :=
      (h.mem_eqWages_iff (hrw.trans_le hc.1)).2 hc0
    exact absurd (hmax.2 hcm) (not_le.2 (hw.trans_le hc.1))

/-- Between `r(θ̲)` and `θ̲` every hire is profitable. -/
theorem RegularModel.firmProfit_pos_of_lt_θl {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ}
    (h : RegularModel μ θl θh r) {w : ℝ} (hw1 : r θl < w) (hw2 : w < θl) :
    0 < firmProfit μ r w := by
  have := h.dist.prob
  rw [firmProfit_eq_setIntegral h.meas]
  refine setIntegral_pos_of_ae_pos (measurableSet_acceptSet h.meas w)
    (measure_acceptSet_pos h.dist h.dens h.cont hw1)
    (h.dist.ae_mem.mono fun θ hθ _ => by linarith [hθ.1]) ?_
  exact (h.dist.integrable_id.sub (integrable_const w)).integrableOn

/-- **Section 13.B** (MWG, p. 443). In the regular model the set `W*` of competitive equilibrium
wages is nonempty and has a largest element `w* = Max W*`. -/
theorem RegularModel.exists_isGreatest_eqWages {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ}
    (h : RegularModel μ θl θh r) : ∃ ws, IsGreatest (eqWages μ θl θh r) ws := by
  have hl : θl ∈ Set.Icc θl θh := ⟨le_rfl, h.dist.lt.le⟩
  have hrl := h.le θl hl
  set b := θh + 1
  have hbθ : θh < b := by simp only [b]; linarith
  -- the zero set of the profit between `a` and `b`
  have key : ∀ a, r θl ≤ a → a ≤ b → (a = r θl → r θl = θl) →
      (∃ w ∈ Set.Icc a b, firmProfit μ r w = 0) →
      (∀ w ∈ eqWages μ θl θh r, w < a → r θl = θl ∧ w = r θl ∧ a = r θl) →
      ∃ ws, IsGreatest (eqWages μ θl θh r) ws := by
    intro a ha hab haeq hne hlow
    have hcpt : IsCompact {w | w ∈ Set.Icc a b ∧ firmProfit μ r w = 0} :=
      isCompact_Icc.inter_right (isClosed_eq h.continuous continuous_const)
    obtain ⟨c, ⟨hc, hc0⟩, hcmax⟩ := hcpt.exists_isGreatest hne
    refine ⟨c, ?_, ?_⟩
    · rcases eq_or_lt_of_le (ha.trans hc.1) with heq | hlt
      · rw [← heq]; exact (mem_eqWages_rl_iff h.dist h.mono h.dens).2 (haeq (le_antisymm
          (heq ▸ hc.1) ha) )
      · exact (h.mem_eqWages_iff hlt).2 hc0
    · intro w hw
      by_cases hwa : w < a
      · obtain ⟨_, -, ha'⟩ := hlow w hw hwa
        linarith [hc.1]
      · have hwr : r θl ≤ w := ha.trans (not_lt.1 hwa)
        rcases eq_or_lt_of_le hwr with heq | hlt
        · linarith [hc.1, ha, heq]
        · have h0 := (h.mem_eqWages_iff hlt).1 hw
          have hwb : w ≤ b := by
            by_contra hgt
            exact absurd h0 (firmProfit_neg_of_gt h.dist h.meas (hbθ.trans (not_le.1 hgt))
              (measure_acceptSet_pos h.dist h.dens h.cont hlt)).ne
          exact hcmax ⟨⟨not_lt.1 hwa, hwb⟩, h0⟩
  have hb : firmProfit μ r b < 0 :=
    firmProfit_neg_of_gt h.dist h.meas hbθ
      (measure_acceptSet_pos h.dist h.dens h.cont (by linarith [h.dist.lt]))
  rcases eq_or_lt_of_le hrl with heq | hlt
  · refine key (r θl) le_rfl (by linarith [h.dist.lt]) (fun _ => heq)
      ⟨r θl, ⟨le_rfl, by linarith [h.dist.lt]⟩,
      firmProfit_rl h.dist h.mono h.dens h.meas⟩ ?_
    intro w hw hwa
    exact absurd hw (not_mem_eqWages_of_lt h.dist h.mono.monotoneOn h.le hwa)
  · set a := (r θl + θl) / 2
    have ha1 : r θl < a := by simp only [a]; linarith
    have ha2 : a < θl := by simp only [a]; linarith
    have hpa := h.firmProfit_pos_of_lt_θl ha1 ha2
    have hab : a ≤ b := by linarith [h.dist.lt]
    obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc' hab h.continuous.continuousOn ⟨hb.le, hpa.le⟩
    refine key a ha1.le hab (fun h' => absurd h' ha1.ne') ⟨c, hc, hc0⟩ ?_
    intro w hw hwa
    exfalso
    rcases lt_trichotomy w (r θl) with h1 | h1 | h1
    · exact not_mem_eqWages_of_lt h.dist h.mono.monotoneOn h.le h1 hw
    · rw [h1] at hw
      exact hlt.ne ((mem_eqWages_rl_iff h.dist h.mono h.dens).1 hw)
    · have h0 := (h.mem_eqWages_iff h1).1 hw
      exact (h.firmProfit_pos_of_lt_θl h1 (hwa.trans ha2)).ne' h0

end MWG.AdverseSelection
