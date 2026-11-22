/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.TatonnementLocal
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-!
# Newton price dynamics (MWG Section 17.H, pp. 624-625)

**(17.H.2)**: the market agent adjusts prices so that every excess demand decreases in proportion,
`Dẑ(p(t))(dp/dt) = -λẑ(p(t))` (`IsNewtonPath`), i.e. `dp/dt = -λ[Dẑ(p)]⁻¹ẑ(p)`.

* Along every Newton trajectory `ẑ(p(t)) = e^{-λt}ẑ(p(0))` (`newton_exp`).
* p. 625: "If `Dẑ(p*)` is nonsingular, then (17.H.2) always succeeds in restoring equilibrium after
  a small disturbance" (`newton_restores`): if `ẑ(p*) = 0` and `ẑ` is strictly differentiable at
  `p*` with invertible derivative, every Newton trajectory starting close enough to `p*` converges
  to `p*`. The proof follows the trajectory through the local inverse of `ẑ` (inverse function
  theorem): `p(t) = ẑ⁻¹(e^{-λt}ẑ(p(0)))`.
* Instance: `ẑ(q) = q - q*`, with the trajectory `q* + e^{-λt}(q(0) - q*)` (`newton_instance`).
-/

namespace MWG.PositiveEquilibriumTheory

open Filter Topology Set

variable {n : ℕ}

/-- **(17.H.2)** (MWG, p. 624). `q` (with derivative `q'`) is a trajectory of the Newton
dynamics for `ẑ` with rate `λ`: for `t ≥ 0`, `ẑ` is differentiable at `q(t)` and
`Dẑ(q(t)) q'(t) = -λ ẑ(q(t))`. -/
def IsNewtonPath (zh : (Fin n → ℝ) → Fin n → ℝ) (lam : ℝ) (q q' : ℝ → Fin n → ℝ) : Prop :=
  ∀ t, 0 ≤ t → HasDerivWithinAt q (q' t) (Ici 0) t ∧ DifferentiableAt ℝ zh (q t) ∧
    fderiv ℝ zh (q t) (q' t) = -lam • zh (q t)

/-- **(17.H.2)** (MWG, p. 624). Along a Newton trajectory every excess demand decays at the rate
`λ`: `ẑ(q(t)) = e^{-λt} ẑ(q(0))`. -/
theorem newton_exp {zh : (Fin n → ℝ) → Fin n → ℝ} {lam : ℝ} {q q' : ℝ → Fin n → ℝ}
    (h : IsNewtonPath zh lam q q') {t : ℝ} (ht : 0 ≤ t) :
    zh (q t) = Real.exp (-lam * t) • zh (q 0) := by
  set w : ℝ → Fin n → ℝ := fun s => Real.exp (lam * s) • zh (q s) with hw
  have hwd : ∀ s, 0 ≤ s → HasDerivWithinAt w 0 (Ici 0) s := by
    intro s hs
    obtain ⟨hq, hd, hN⟩ := h s hs
    have hz := hd.hasFDerivAt.comp_hasDerivWithinAt s hq
    have he : HasDerivWithinAt (fun s => Real.exp (lam * s)) (Real.exp (lam * s) * lam)
        (Ici 0) s := by
      have := ((hasDerivAt_id s).const_mul lam).exp
      simpa using this.hasDerivWithinAt
    have := he.smul hz
    have hfun : ((fun s => Real.exp (lam * s)) • zh ∘ q) = w := by
      funext y; simp [hw]
    rw [hfun] at this
    convert this using 1
    rw [hN, smul_smul, Function.comp_apply, ← add_smul,
      show Real.exp (lam * s) * -lam + Real.exp (lam * s) * lam = 0 by ring, zero_smul]
  have hcont : ContinuousOn w (Icc 0 t) := fun s hs =>
    (hwd s hs.1).continuousWithinAt.mono fun y hy => hy.1
  have hconst := constant_of_has_deriv_right_zero hcont (fun s hs =>
    (hwd s hs.1).mono fun y (hy : s ≤ y) => hs.1.trans hy) t ⟨ht, le_rfl⟩
  simp only [hw, mul_zero, Real.exp_zero, one_smul] at hconst
  rw [← hconst, smul_smul, ← Real.exp_add]
  simp

/-- **Section 17.H** (MWG, p. 625). If `ẑ(p*) = 0` and `ẑ` is strictly differentiable at `p*`
with nonsingular derivative `Dẑ(p*)`, the Newton dynamics (17.H.2) (`λ > 0`) restore equilibrium
after a small disturbance: every Newton trajectory starting close enough to `p*` converges to
`p*`. -/
theorem newton_restores {zh : (Fin n → ℝ) → Fin n → ℝ} {lam : ℝ} (hlam : 0 < lam)
    {qs : Fin n → ℝ} (h0 : zh qs = 0) {D : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ)}
    (hD : HasStrictFDerivAt zh (D : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) qs) :
    ∃ ε > 0, ∀ q q' : ℝ → Fin n → ℝ, IsNewtonPath zh lam q q' → dist (q 0) qs < ε →
      Tendsto q atTop (𝓝 qs) := by
  set φ := hD.toOpenPartialHomeomorph zh with hφ
  have hφc : ∀ x, φ x = zh x := fun x => rfl
  have hqsU : qs ∈ φ.source := hD.mem_toOpenPartialHomeomorph_source
  have h0V : (0 : Fin n → ℝ) ∈ φ.target := by
    have := hD.image_mem_toOpenPartialHomeomorph_target
    rwa [h0] at this
  have hsymm0 : φ.symm 0 = qs := by
    have := φ.left_inv hqsU
    rwa [hφc, h0] at this
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 φ.open_target 0 h0V
  have hev1 : ∀ᶠ x in 𝓝 qs, x ∈ φ.source := φ.open_source.mem_nhds hqsU
  have hev : ∀ᶠ x in 𝓝 qs, x ∈ φ.source ∧ zh x ∈ Metric.ball (0 : Fin n → ℝ) r :=
    hev1.and
      (hD.continuousAt.eventually (by rw [h0]; exact Metric.ball_mem_nhds 0 hr))
  obtain ⟨ε, hε, hεball⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨ε, hε, fun q q' hq hq0 => ?_⟩
  obtain ⟨hx0U, hx0r⟩ := hεball hq0
  set w : ℝ → Fin n → ℝ := fun t => Real.exp (-lam * t) • zh (q 0) with hw
  have hwV : ∀ t, 0 ≤ t → w t ∈ φ.target := by
    intro t ht
    refine hball ?_
    rw [Metric.mem_ball, dist_zero_right] at hx0r ⊢
    rw [hw, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have : Real.exp (-lam * t) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    nlinarith [norm_nonneg (zh (q 0)), Real.exp_pos (-lam * t)]
  set γ : ℝ → Fin n → ℝ := fun t => φ.symm (w t) with hγ
  have hwc : Continuous w := by
    rw [hw]; fun_prop
  have hγc : ContinuousOn γ (Ici 0) :=
    φ.continuousOn_symm.comp hwc.continuousOn fun t ht => hwV t ht
  have hqc : ContinuousOn q (Ici 0) := fun t ht => (hq t ht).1.continuousWithinAt
  have hzq : ∀ t, 0 ≤ t → zh (q t) = w t := fun t ht => newton_exp hq ht
  -- the trajectory follows the local inverse
  have hfollow : ∀ t, 0 ≤ t → q t = γ t := by
    intro T hT
    have hsub := IsClosed.Icc_subset_of_forall_mem_nhdsWithin (a := 0) (b := T)
      (s := {t | q t = γ t}) ?_ ?_ ?_
    · exact hsub ⟨hT, le_rfl⟩
    · have hpair : ContinuousOn (fun t => (q t, γ t)) (Icc 0 T) :=
        ((hqc.mono fun y hy => hy.1).prodMk (hγc.mono fun y hy => hy.1))
      have := hpair.preimage_isClosed_of_isClosed isClosed_Icc isClosed_diagonal
      rw [inter_comm]
      exact this
    · change q 0 = γ 0
      simp only [hγ, hw, mul_zero, Real.exp_zero, one_smul]
      rw [← hφc, φ.left_inv hx0U]
    · intro x hx
      have hx0 : 0 ≤ x := hx.2.1
      have hxU : q x ∈ φ.source := by
        rw [show q x = γ x from hx.1]
        exact φ.map_target (hwV x hx0)
      have hev2 : ∀ᶠ s in 𝓝[Ici 0] x, q s ∈ φ.source :=
        (hqc x hx0).eventually (φ.open_source.mem_nhds hxU)
      have hev3 : ∀ᶠ s in 𝓝[>] x, q s ∈ φ.source :=
        nhdsWithin_mono x (fun y (hy : x < y) => (show (0 : ℝ) ≤ y from hx0.trans hy.le))
          hev2
      filter_upwards [hev3, self_mem_nhdsWithin] with s hs hsx
      have hs0 : 0 ≤ s := hx0.trans (le_of_lt hsx)
      change q s = γ s
      rw [hγ]
      simp only
      rw [← hzq s hs0, ← hφc, φ.left_inv hs]
  have hwlim : Tendsto w atTop (𝓝 0) := by
    have : Tendsto (fun t => -lam * t) atTop atBot :=
      tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.2 hlam)
    simpa [hw] using (Real.tendsto_exp_atBot.comp this).smul_const (zh (q 0))
  have hγlim : Tendsto γ atTop (𝓝 qs) := by
    rw [← hsymm0]
    exact (φ.continuousAt_symm h0V).tendsto.comp hwlim
  refine hγlim.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with t ht
  exact (hfollow t ht).symm

/-- **Section 17.H**, instance of (17.H.2): for `ẑ(q) = q - q*` (`Dẑ = I`), the trajectory
`q(t) = q* + e^{-λt}(q(0) - q*)` is a Newton trajectory, and `ẑ` satisfies the hypotheses of
`newton_restores`. -/
theorem newton_instance (qs q0 : Fin n → ℝ) (lam : ℝ) :
    IsNewtonPath (fun x => x - qs) lam (fun t => qs + Real.exp (-lam * t) • (q0 - qs))
      (fun t => (-lam * Real.exp (-lam * t)) • (q0 - qs)) ∧
    HasStrictFDerivAt (fun x : Fin n → ℝ => x - qs)
      ((ContinuousLinearEquiv.refl ℝ (Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))) qs := by
  have hlin : ∀ x : Fin n → ℝ, HasFDerivAt (fun x : Fin n → ℝ => x - qs)
      (ContinuousLinearMap.id ℝ (Fin n → ℝ)) x := fun x => (hasFDerivAt_id x).sub_const qs
  refine ⟨fun t _ => ⟨?_, (hlin _).differentiableAt, ?_⟩, ?_⟩
  · have he : HasDerivAt (fun t => Real.exp (-lam * t)) (Real.exp (-lam * t) * (-lam)) t := by
      have := ((hasDerivAt_id t).const_mul (-lam)).exp
      simpa using this
    have := (he.smul_const (q0 - qs)).const_add qs
    convert this.hasDerivWithinAt using 1
    rw [mul_comm]
  · rw [(hlin _).fderiv]
    simp [smul_smul]
  · exact (hasStrictFDerivAt_id qs).sub_const qs

end MWG.PositiveEquilibriumTheory
