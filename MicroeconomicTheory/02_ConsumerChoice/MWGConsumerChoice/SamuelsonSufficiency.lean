/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGConsumerChoice.Slutsky
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Topology.Order.Monotone

/-!
# Negative definiteness off the price ray implies the weak axiom

MWG, Section 2.F, p. 35 (small type), citing Samuelson (1947) and Kihlstrom, Mas-Colell and
Sonnenschein (1976): if a demand function satisfying Walras' law and homogeneity of degree zero
has `v·S(p, w)v < 0` whenever `v ≠ αp`, then it satisfies the weak axiom.

Precise form proved here: demand is differentiable at every `p ≫ 0`, `w > 0`, takes values in
`ℝ^L_+`, and the condition holds at every `(p, w)`. Proof: for a compensated change from
`(p, w)` to `p'` (not proportional to `p`), put `Δ = p' - p`, `x̄ = x(p, w)` and
`φ(t) = Δ·[x(p + tΔ, w + tΔ·x̄) - x̄]`. Then `φ(0) = 0` and
`φ'(t) = Δ·S(t)Δ - (Δ·D_w x(t)) φ(t)`, so `φ' < 0` wherever `φ = 0`; hence `φ(1) < 0`, which is
the strict compensated law of demand, and Proposition 2.F.1 gives the weak axiom.
-/

namespace MWG.ConsumerChoice

open Filter Topology Set

/-- A function on `[0, 1]` that vanishes at `0` and has negative derivative at each of its zeros
is negative at `1`. -/
theorem neg_at_one_of_deriv_neg_at_zeros {φ : ℝ → ℝ} (h0 : φ 0 = 0)
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, ∃ d, HasDerivAt φ d t ∧ (φ t = 0 → d < 0)) : φ 1 < 0 := by
  have hcont : ContinuousOn φ (Icc 0 1) :=
    fun t ht => (hd t ht).choose_spec.1.continuousAt.continuousWithinAt
  -- negative just to the right of `0`
  obtain ⟨d0, hd0, hd0neg⟩ := hd 0 ⟨le_rfl, zero_le_one⟩
  have hd0' := hd0neg h0
  have hslope := (hasDerivAt_iff_tendsto_slope.mp hd0).mono_left
    (nhdsWithin_mono _ fun t (ht : 0 < t) => ne_of_gt ht)
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), φ t < 0 := by
    filter_upwards [hslope.eventually (gt_mem_nhds hd0'), self_mem_nhdsWithin] with t ht htpos
    rw [slope_def_field, h0, sub_zero, sub_zero] at ht
    have ht' : (0 : ℝ) < t := htpos
    by_contra hc
    push Not at hc
    have := div_nonneg hc ht'.le
    linarith
  obtain ⟨ε, hε, hεsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  have hε' : (0 : ℝ) < ε := hε
  by_contra hcon
  push Not at hcon
  set δ := min (ε / 2) 1 with hδ
  have hδpos : 0 < δ := lt_min (by linarith) one_pos
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδε : δ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  set T := Icc δ 1 ∩ φ ⁻¹' Ici 0 with hT
  have hTclosed : IsClosed T :=
    (hcont.mono (Icc_subset_Icc hδpos.le le_rfl)).preimage_isClosed_of_isClosed isClosed_Icc
      isClosed_Ici
  have hTne : T.Nonempty := ⟨1, ⟨hδ1, le_rfl⟩, hcon⟩
  have hTbdd : BddBelow T := ⟨δ, fun t ht => ht.1.1⟩
  set t0 := sInf T
  have ht0 : t0 ∈ T := hTclosed.csInf_mem hTne hTbdd
  have ht0pos : 0 < t0 := lt_of_lt_of_le hδpos ht0.1.1
  -- `φ < 0` on `(0, t0)`
  have hneg : ∀ t ∈ Ioo 0 t0, φ t < 0 := by
    intro t ht
    by_cases htε : t < ε
    · exact hεsub ⟨ht.1, htε⟩
    · by_contra hc
      push Not at hc
      have hmem : t ∈ T := ⟨⟨by linarith, ht.2.le.trans ht0.1.2⟩, hc⟩
      exact absurd (csInf_le hTbdd hmem) (not_le.mpr ht.2)
  obtain ⟨d, hdt, hdneg⟩ := hd t0 ⟨ht0pos.le, ht0.1.2⟩
  have hleft : ∀ᶠ t in 𝓝[<] t0, t ∈ Ioo 0 t0 := Ioo_mem_nhdsLT ht0pos
  have hφ0 : φ t0 = 0 := by
    apply le_antisymm _ ht0.2
    apply le_of_tendsto (hdt.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio t0)))
    filter_upwards [hleft] with t ht
    exact (hneg t ht).le
  have hdlt := hdneg hφ0
  have hsl := (hasDerivAt_iff_tendsto_slope.mp hdt).mono_left
    (nhdsWithin_mono (s := Iio t0) _ fun t (ht : t < t0) => ne_of_lt ht)
  have : 0 ≤ d := by
    apply ge_of_tendsto hsl
    filter_upwards [hleft] with t ht
    rw [slope_def_field, hφ0, sub_zero]
    exact (div_pos_of_neg_of_neg (hneg t ht) (by linarith [ht.2])).le
  linarith

/-- **Section 2.F** (MWG, p. 35, small type; Samuelson 1947, Kihlstrom, Mas-Colell and
Sonnenschein 1976). Let `x` be homogeneous of degree zero, satisfy Walras' law, take values in
`ℝ^L_+` and be differentiable at every `p ≫ 0`, `w > 0`. If `v·S(p, w)v < 0` for every `(p, w)`
and every `v` not proportional to `p`, then `x` satisfies the weak axiom. -/
theorem samuelson_sufficiency {L : ℕ} {x : DemandFunction L} (hH : HomogeneousZero x)
    (hW : WalrasLaw x) (hX : ValuesInOrthant x)
    (hdiff : ∀ p w, PWDomain p w → DifferentiableAt ℝ (Function.uncurry x) (p, w))
    (hS : ∀ p w, PWDomain p w → ∀ v : Fin L → ℝ, (∀ α : ℝ, v ≠ α • p) →
      v ⬝ᵥ Matrix.mulVec (slutskyMatrix (fderiv ℝ (Function.uncurry x) (p, w)) (x p w)) v < 0) :
    WeakAxiom x := by
  apply proposition_2_F_1_ii hW hX
  intro p w p' hd hp' hw'
  set xb := x p w with hxb
  have hWx : p ⬝ᵥ xb = w := hW p w hd
  by_cases hprop : ∃ α : ℝ, p' = α • p
  · -- proportional prices: demand does not change
    obtain ⟨α, rfl⟩ := hprop
    obtain ⟨l⟩ : Nonempty (Fin L) := by
      by_contra hL
      rw [not_nonempty_iff] at hL
      have : p ⬝ᵥ x p w = 0 := by simp [dotProduct]
      linarith [hW p w hd, hd.2]
    have hα : 0 < α := by
      have := hp' l
      simp only [Pi.smul_apply, smul_eq_mul] at this
      exact pos_of_mul_pos_left this (hd.1 l).le
    have hcw : compensatedWealth x p w (α • p) = α * w := by
      simp [compensatedWealth, smul_dotProduct, hW p w hd]
    rw [hcw, hH p w α hd hα, sub_self, dotProduct_zero]
    exact ⟨le_rfl, fun h => absurd rfl h⟩
  push Not at hprop
  set Δ := p' - p with hΔ
  set c := Δ ⬝ᵥ xb with hc
  have hdomt : ∀ t ∈ Icc (0 : ℝ) 1, PWDomain (p + t • Δ) (w + t * c) := by
    intro t ht
    refine ⟨fun l => ?_, ?_⟩
    · have h1 := hd.1 l
      have h2 := hp' l
      simp only [hΔ, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      rcases eq_or_lt_of_le ht.2 with h | h
      · rw [h]; linarith
      · nlinarith [mul_nonneg ht.1 h2.le, mul_pos (sub_pos.mpr h) h1]
    · have e1 : w + 1 * c = compensatedWealth x p w p' := by
        simp only [compensatedWealth, hc, hΔ, sub_dotProduct, hWx]
        ring
      have : w + t * c = (1 - t) * w + t * (w + 1 * c) := by ring
      rw [this, e1]
      rcases eq_or_lt_of_le ht.2 with h | h
      · rw [h]; simpa using hw'
      · nlinarith [mul_nonneg ht.1 hw'.le, mul_pos (sub_pos.mpr h) hd.2]
  -- `Δ` is never proportional to the current prices
  have hnp : ∀ t ∈ Icc (0 : ℝ) 1, ∀ β : ℝ, Δ ≠ β • (p + t • Δ) := by
    intro t _ β hβ
    have hne : 1 - β * t ≠ 0 := by
      intro h0
      have : β • p = 0 := by
        have e : (1 - β * t) • Δ = β • p := by
          rw [sub_smul, one_smul, mul_smul]
          nth_rewrite 1 [hβ]
          rw [smul_add]
          abel
        rw [h0, zero_smul] at e
        exact e.symm
      have hβ0 : β = 0 := by
        rcases smul_eq_zero.mp this with h | h
        · exact h
        · exfalso
          obtain ⟨l⟩ : Nonempty (Fin L) := by
            by_contra hL
            rw [not_nonempty_iff] at hL
            exact hprop 1 (funext fun i => (hL.false i).elim)
          have := hd.1 l
          rw [h] at this
          exact lt_irrefl _ this
      rw [hβ0, zero_mul, sub_zero] at h0
      exact one_ne_zero h0
    apply hprop (1 + β / (1 - β * t))
    have e : (1 - β * t) • Δ = β • p := by
      rw [sub_smul, one_smul, mul_smul]
      nth_rewrite 1 [hβ]
      rw [smul_add]
      abel
    have hΔ' : Δ = (β / (1 - β * t)) • p := by
      rw [div_eq_inv_mul, mul_smul, ← e, smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [add_smul, one_smul, ← hΔ', hΔ, add_sub_cancel]
  -- the function `φ`
  set φ : ℝ → ℝ := fun t => Δ ⬝ᵥ (x (p + t • Δ) (w + t * c) - xb) with hφ
  have hφ0 : φ 0 = 0 := by simp [hφ, hxb]
  have hderiv : ∀ t ∈ Icc (0 : ℝ) 1, ∃ d, HasDerivAt φ d t ∧ (φ t = 0 → d < 0) := by
    intro t ht
    set D := fderiv ℝ (Function.uncurry x) (p + t • Δ, w + t * c)
    have hD : HasFDerivAt (Function.uncurry x) D (p + t • Δ, w + t * c) :=
      (hdiff _ _ (hdomt t ht)).hasFDerivAt
    have hline := hasDerivAt_pi.mp (hasDerivAt_line (x := x) (p := p) (v := Δ) (w := w)
      (c := c) (t₀ := t) hD)
    have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun l _ => (hline l).const_mul (Δ l))
    refine ⟨Δ ⬝ᵥ D (Δ, c), ?_, fun hzero => ?_⟩
    · have := hsum.sub_const (Δ ⬝ᵥ xb)
      convert this using 1
      · funext s
        simp only [hφ, dotProduct_sub]
        rfl
      · simp [dotProduct]
    · -- at a zero of `φ`, the derivative is `Δ·SΔ`
      have hxt : Δ ⬝ᵥ x (p + t • Δ) (w + t * c) = c := by
        have := hzero
        simp only [hφ, dotProduct_sub] at this
        linarith
      have hSΔ := hS _ _ (hdomt t ht) Δ (hnp t ht)
      rw [slutskyMatrix_mulVec, hxt] at hSΔ
      exact hSΔ
  have hneg := neg_at_one_of_deriv_neg_at_zeros hφ0 hderiv
  have hp1 : p + (1 : ℝ) • Δ = p' := by rw [one_smul, hΔ, add_sub_cancel]
  have hw1 : w + 1 * c = compensatedWealth x p w p' := by
    simp only [compensatedWealth, hc, hΔ, sub_dotProduct, hWx]
    ring
  simp only [hφ, hp1, hw1] at hneg
  exact ⟨hneg.le, fun _ => hneg⟩

end MWG.ConsumerChoice
