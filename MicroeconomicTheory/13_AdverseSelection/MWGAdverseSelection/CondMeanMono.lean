/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGAdverseSelection.Regular

/-!
# Monotonicity of `E[θ | r(θ) ≤ w]`

MWG, Section 13.B, p. 441: "It is increasing in the level `w` for wages between `r(θ̲)` and
`r(θ̄)`".

* `condMean_mono_of_sep`, `condMean_lt_of_sep`: enlarging a set by points lying (strictly)
  above all its points raises (strictly) the conditional mean.
* `condMean_acceptSet_mono`: for `r` nondecreasing on `[θ̲, θ̄]`, `w ↦ E[θ | r(θ) ≤ w]` is
  nondecreasing on `[r(θ̲), ∞)` (no density or continuity needed).
* `RegularModel.condMean_acceptSet_strictMono`: in the model of p. 441 (with `r` continuous,
  correction 2) it is strictly increasing on `[r(θ̲), r(θ̄)]`.
-/

namespace MWG.AdverseSelection

open MeasureTheory

/-- Every conditional mean is at least `θ̲`. -/
theorem condMean_ge {μ : Measure ℝ} {θl θh : ℝ} (hd : TypeDist μ θl θh) (S : Set ℝ) :
    θl ≤ condMean μ θl θh S := by
  have := hd.prob
  unfold condMean
  split_ifs with hpos hne
  · have ha : 0 < (μ S).toReal := ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _)
    rw [le_div_iff₀ ha]
    have hle : ∫ θ in S, θl ∂μ ≤ ∫ θ in S, θ ∂μ :=
      integral_mono_ae (integrable_const θl).integrableOn hd.integrable_id.integrableOn
        (ae_restrict_of_ae (hd.ae_mem.mono fun θ hθ => hθ.1))
    rw [setIntegral_const, smul_eq_mul, Measure.real] at hle
    linarith
  · exact le_rfl
  · exact hd.meanType_mem.1

/-- Adding to a set `S` of positive probability points that lie above all points of `S` (within
`[θ̲, θ̄]`) does not lower the conditional mean. -/
theorem condMean_mono_of_sep {μ : Measure ℝ} {θl θh : ℝ} (hd : TypeDist μ θl θh) {S S' : Set ℝ}
    (hS : MeasurableSet S) (hS' : MeasurableSet S') (hsub : S ⊆ S') (hpos : 0 < μ S)
    (hsep : ∀ θ ∈ S ∩ Set.Icc θl θh, ∀ θ' ∈ (S' \ S) ∩ Set.Icc θl θh, θ ≤ θ') :
    condMean μ θl θh S ≤ condMean μ θl θh S' := by
  have := hd.prob
  have hpos' : 0 < μ S' := hpos.trans_le (measure_mono hsub)
  have hD : MeasurableSet (S' \ S) := hS'.diff hS
  have ha : 0 < (μ S).toReal := ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _)
  have hb : 0 ≤ (μ (S' \ S)).toReal := ENNReal.toReal_nonneg
  have hmeas : (μ S').toReal = (μ S).toReal + (μ (S' \ S)).toReal := by
    conv_lhs => rw [← Set.union_sdiff_cancel hsub]
    rw [measure_union Set.disjoint_sdiff_right hD,
      ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  have hint : ∫ θ in S', θ ∂μ = (∫ θ in S, θ ∂μ) + ∫ θ in S' \ S, θ ∂μ := by
    conv_lhs => rw [← Set.union_sdiff_cancel hsub]
    exact setIntegral_union Set.disjoint_sdiff_right hD hd.integrable_id.integrableOn
      hd.integrable_id.integrableOn
  set m := (∫ θ in S, θ ∂μ) / (μ S).toReal with hmdef
  have hm : ∫ θ in S, θ ∂μ = m * (μ S).toReal := by rw [hmdef, div_mul_cancel₀ _ ha.ne']
  have h1 : ∀ θ' ∈ (S' \ S) ∩ Set.Icc θl θh, m ≤ θ' := by
    intro θ' hθ'
    have hle : ∫ θ in S, θ ∂μ ≤ ∫ θ in S, θ' ∂μ :=
      integral_mono_ae hd.integrable_id.integrableOn (integrable_const θ').integrableOn
        ((ae_restrict_iff' hS).2 (hd.ae_mem.mono fun θ hθ hθS => hsep θ ⟨hθS, hθ⟩ θ' hθ'))
    rw [setIntegral_const, smul_eq_mul, Measure.real] at hle
    rw [hmdef, div_le_iff₀ ha]
    linarith
  have h2 : ∫ θ in S' \ S, m ∂μ ≤ ∫ θ in S' \ S, θ ∂μ :=
    integral_mono_ae (integrable_const m).integrableOn hd.integrable_id.integrableOn
      ((ae_restrict_iff' hD).2 (hd.ae_mem.mono fun θ hθ hθD => h1 θ ⟨hθD, hθ⟩))
  rw [setIntegral_const, smul_eq_mul, Measure.real] at h2
  have hcS : condMean μ θl θh S = m := by simp only [condMean, hpos, ↓reduceIte, hmdef]
  have hcS' : condMean μ θl θh S' = (∫ θ in S', θ ∂μ) / (μ S').toReal := by
    simp only [condMean, hpos', ↓reduceIte]
  rw [hcS, hcS', le_div_iff₀ (by rw [hmeas]; linarith), hint, hmeas]
  nlinarith

/-- The strict version: if the added points lie strictly above all points of `S` and have
positive probability, the conditional mean rises strictly. -/
theorem condMean_lt_of_sep {μ : Measure ℝ} {θl θh : ℝ} (hd : TypeDist μ θl θh) {S S' : Set ℝ}
    (hS : MeasurableSet S) (hS' : MeasurableSet S') (hsub : S ⊆ S') (hpos : 0 < μ S)
    (hposD : 0 < μ (S' \ S))
    (hsep : ∀ θ ∈ S ∩ Set.Icc θl θh, ∀ θ' ∈ (S' \ S) ∩ Set.Icc θl θh, θ < θ') :
    condMean μ θl θh S < condMean μ θl θh S' := by
  have := hd.prob
  have hpos' : 0 < μ S' := hpos.trans_le (measure_mono hsub)
  have hD : MeasurableSet (S' \ S) := hS'.diff hS
  have ha : 0 < (μ S).toReal := ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _)
  have hb : 0 < (μ (S' \ S)).toReal := ENNReal.toReal_pos hposD.ne' (measure_ne_top _ _)
  have hmeas : (μ S').toReal = (μ S).toReal + (μ (S' \ S)).toReal := by
    conv_lhs => rw [← Set.union_sdiff_cancel hsub]
    rw [measure_union Set.disjoint_sdiff_right hD,
      ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  have hint : ∫ θ in S', θ ∂μ = (∫ θ in S, θ ∂μ) + ∫ θ in S' \ S, θ ∂μ := by
    conv_lhs => rw [← Set.union_sdiff_cancel hsub]
    exact setIntegral_union Set.disjoint_sdiff_right hD hd.integrable_id.integrableOn
      hd.integrable_id.integrableOn
  set m := (∫ θ in S, θ ∂μ) / (μ S).toReal with hmdef
  have hm : ∫ θ in S, θ ∂μ = m * (μ S).toReal := by rw [hmdef, div_mul_cancel₀ _ ha.ne']
  have h1 : ∀ θ' ∈ (S' \ S) ∩ Set.Icc θl θh, m < θ' := by
    intro θ' hθ'
    have hlt : 0 < ∫ θ in S, (θ' - θ) ∂μ :=
      setIntegral_pos_of_ae_pos hS hpos
        (hd.ae_mem.mono fun θ hθ hθS => sub_pos.2 (hsep θ ⟨hθS, hθ⟩ θ' hθ'))
        ((integrable_const θ').sub hd.integrable_id).integrableOn
    rw [integral_sub (integrable_const θ').integrableOn hd.integrable_id.integrableOn,
      setIntegral_const, smul_eq_mul, Measure.real] at hlt
    rw [hmdef, div_lt_iff₀ ha]
    linarith
  have h2 : 0 < ∫ θ in S' \ S, (θ - m) ∂μ :=
    setIntegral_pos_of_ae_pos hD hposD
      (hd.ae_mem.mono fun θ hθ hθD => sub_pos.2 (h1 θ ⟨hθD, hθ⟩))
      (hd.integrable_id.sub (integrable_const m)).integrableOn
  rw [integral_sub hd.integrable_id.integrableOn (integrable_const m).integrableOn,
    setIntegral_const, smul_eq_mul, Measure.real] at h2
  have hcS : condMean μ θl θh S = m := by simp only [condMean, hpos, ↓reduceIte, hmdef]
  have hcS' : condMean μ θl θh S' = (∫ θ in S', θ ∂μ) / (μ S').toReal := by
    simp only [condMean, hpos', ↓reduceIte]
  rw [hcS, hcS', lt_div_iff₀ (by rw [hmeas]; linarith), hint, hmeas]
  nlinarith

/-- **Section 13.B** (MWG, p. 441). For `r` nondecreasing on `[θ̲, θ̄]`, `E[θ | r(θ) ≤ w]` is
nondecreasing in `w ≥ r(θ̲)`. Neither a density nor continuity of `r` is needed. -/
theorem condMean_acceptSet_mono {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ}
    (hd : TypeDist μ θl θh) (hr : Measurable r) (hmono : MonotoneOn r (Set.Icc θl θh))
    {w w' : ℝ} (hw : r θl ≤ w) (hww : w ≤ w') :
    condMean μ θl θh (acceptSet r w) ≤ condMean μ θl θh (acceptSet r w') := by
  rcases eq_zero_or_pos (μ (acceptSet r w)) with h0 | hpos
  · have hne : (acceptSet r w ∩ Set.Icc θl θh).Nonempty := ⟨θl, hw, le_rfl, hd.lt.le⟩
    have hc : condMean μ θl θh (acceptSet r w) = θl := by
      simp only [condMean, h0, lt_irrefl, ↓reduceIte, hne]
    rw [hc]
    exact condMean_ge hd _
  · refine condMean_mono_of_sep hd (measurableSet_acceptSet hr w)
      (measurableSet_acceptSet hr w') (fun θ hθ => le_trans hθ hww) hpos ?_
    rintro θ ⟨hθ, hθI⟩ θ' ⟨⟨_, hθ'⟩, hθ'I⟩
    by_contra hlt
    rw [not_le] at hlt
    exact hθ' (le_trans (hmono hθ'I hθI hlt.le) hθ)

/-- **Section 13.B** (MWG, p. 441). In the model of p. 441 (`r` strictly increasing and, as in
correction 2, continuous; positive density), `E[θ | r(θ) ≤ w]` is strictly increasing in `w`
on `[r(θ̲), r(θ̄)]`. -/
theorem RegularModel.condMean_acceptSet_strictMono {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ}
    (h : RegularModel μ θl θh r) {w w' : ℝ} (hw : r θl ≤ w) (hww : w < w')
    (hw' : w' ≤ r θh) :
    condMean μ θl θh (acceptSet r w) < condMean μ θl θh (acceptSet r w') := by
  have hd := h.dist
  have := hd.prob
  have hI : Set.Icc (r θl) (r θh) ⊆ r '' Set.Icc θl θh :=
    intermediate_value_Icc hd.lt.le h.cont
  obtain ⟨θ1, hθ1I, hθ1⟩ := hI ⟨hw, hww.le.trans hw'⟩
  obtain ⟨θ2, hθ2I, hθ2⟩ := hI ⟨hw.trans hww.le, hw'⟩
  have h12 : θ1 < θ2 := by
    by_contra hle
    rw [not_lt] at hle
    have := h.mono.monotoneOn hθ2I hθ1I hle
    linarith
  set c := (θ1 + θ2) / 2 with hc
  have hsubD : Set.Icc c θ2 ⊆ acceptSet r w' \ acceptSet r w := by
    intro θ hθ
    have hθI : θ ∈ Set.Icc θl θh := ⟨by linarith [hθ1I.1, hθ.1, hc], hθ.2.trans hθ2I.2⟩
    refine ⟨?_, ?_⟩
    · change r θ ≤ w'
      rw [← hθ2]; exact h.mono.monotoneOn hθI hθ2I hθ.2
    · change ¬ r θ ≤ w
      rw [← hθ1, not_le]; exact h.mono hθ1I hθI (by linarith [hθ.1, hc])
  have hposD : 0 < μ (acceptSet r w' \ acceptSet r w) :=
    (h.dens.pos c θ2 (by linarith [hθ1I.1, hc]) (by linarith [hc]) hθ2I.2).trans_le
      (measure_mono hsubD)
  have hS' : MeasurableSet (acceptSet r w') := measurableSet_acceptSet h.meas w'
  rcases eq_zero_or_pos (μ (acceptSet r w)) with h0 | hpos
  · have hne : (acceptSet r w ∩ Set.Icc θl θh).Nonempty := ⟨θl, hw, le_rfl, hd.lt.le⟩
    have hc : condMean μ θl θh (acceptSet r w) = θl := by
      simp only [condMean, h0, lt_irrefl, ↓reduceIte, hne]
    rw [hc]
    have hpos' : 0 < μ (acceptSet r w') := hposD.trans_le (measure_mono Set.sdiff_subset)
    have hae : ∀ᵐ θ ∂μ, θ ≠ θl := by
      rw [ae_iff]; simpa using h.dens.noAtom θl
    have hlt : 0 < ∫ θ in acceptSet r w', (θ - θl) ∂μ :=
      setIntegral_pos_of_ae_pos hS' hpos'
        ((hd.ae_mem.and hae).mono fun θ hθ _ => sub_pos.2 (lt_of_le_of_ne hθ.1.1 hθ.2.symm))
        (hd.integrable_id.sub (integrable_const θl)).integrableOn
    rw [integral_sub hd.integrable_id.integrableOn (integrable_const θl).integrableOn,
      setIntegral_const, smul_eq_mul, Measure.real] at hlt
    have ha : 0 < (μ (acceptSet r w')).toReal := ENNReal.toReal_pos hpos'.ne' (measure_ne_top _ _)
    simp only [condMean, hpos', ↓reduceIte]
    rw [lt_div_iff₀ ha]
    linarith
  · refine condMean_lt_of_sep hd (measurableSet_acceptSet h.meas w) hS'
      (fun θ hθ => le_trans hθ hww.le) hpos hposD ?_
    rintro θ ⟨hθ, hθI⟩ θ' ⟨⟨_, hθ'⟩, hθ'I⟩
    by_contra hle
    rw [not_lt] at hle
    exact hθ' (le_trans (h.mono.monotoneOn hθ'I hθI hle) hθ)

end MWG.AdverseSelection
