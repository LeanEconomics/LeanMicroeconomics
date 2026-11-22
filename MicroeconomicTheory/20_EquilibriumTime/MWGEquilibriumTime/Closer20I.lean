/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGEquilibriumTime.Nonequilibrium
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Global tâtonnement stability of the short-run equilibrium (MWG Section 20.I, p. 778)

MWG, Chapter 20, Section 20.I, p. 778: with the marginal utilities of wealth `λ_i` fixed, the
matrix of short-run price effects is negative definite, so "the short-run equilibrium is unique
and globally tâtonnement stable". Uniqueness is `unique_zero_of_negDef` (module
`Nonequilibrium`). Here is global stability for the tâtonnement `dp/dt = z(p)` of Section 17.H.

* `tatonnement_global_stable`: if `z` is continuous, `z(p*) = 0` and
  `(p - p*) · z(p) < 0` for every `p ≠ p*`, every solution of `dp/dt = z(p)` converges to `p*`
  as `t → ∞`. The Lyapunov function `V(t) = ‖p(t) - p*‖²` is nonincreasing; if its limit were
  positive, the trajectory would stay in a compact shell on which `(p - p*) · z(p)` is bounded
  away from zero, and `V` would decrease without bound.
* `tatonnement_global_stable_negDef`: the hypothesis of the book, a differentiable excess demand
  with negative definite derivative everywhere, implies the sign condition (by
  `unique_zero_of_negDef`), hence global stability.
* A proved instance: `z(p) = p* - p` with its explicit trajectories
  (`tatonnement_linear_instance`).
-/

open Filter Topology

namespace MWG.EquilibriumTime

variable {L : ℕ}

/-- The squared Euclidean distance as a dot product. -/
theorem sq_le_dotProduct_self (v : Fin L → ℝ) (l : Fin L) : v l ^ 2 ≤ v ⬝ᵥ v := by
  simp only [dotProduct, ← sq]
  exact Finset.single_le_sum (fun k _ => sq_nonneg (v k)) (Finset.mem_univ l)

/-- **Global tâtonnement stability** (MWG, p. 778, with Section 17.H): for a continuous excess
demand `z` with `z(p*) = 0` and `(p - p*) · z(p) < 0` for every `p ≠ p*`, every solution of the
tâtonnement `dp/dt = z(p)` converges to `p*`. -/
theorem tatonnement_global_stable {z : (Fin L → ℝ) → Fin L → ℝ} (hz : Continuous z)
    {pstar : Fin L → ℝ} (hsign : ∀ p, p ≠ pstar → (p - pstar) ⬝ᵥ z p < 0)
    {P : ℝ → Fin L → ℝ} (hP : ∀ t, HasDerivAt P (z (P t)) t) :
    Tendsto P atTop (𝓝 pstar) := by
  set V : ℝ → ℝ := fun t => (P t - pstar) ⬝ᵥ (P t - pstar) with hV
  have hV0 : ∀ t, 0 ≤ V t := fun t => by
    simp only [hV, dotProduct, ← sq]; exact Finset.sum_nonneg fun l _ => sq_nonneg _
  have hVd : ∀ t, HasDerivAt V (2 * ((P t - pstar) ⬝ᵥ z (P t))) t := by
    intro t
    have hc := hasDerivAt_pi.1 (hP t)
    have : HasDerivAt V (∑ l, 2 * ((P t l - pstar l) * z (P t) l)) t := by
      simp only [hV, dotProduct, Pi.sub_apply]
      refine HasDerivAt.fun_sum fun l _ => ?_
      have h1 := (hc l).sub_const (pstar l)
      convert h1.mul h1 using 1
      ring
    convert this using 1
    simp only [dotProduct, Pi.sub_apply, Finset.mul_sum]
  have hdiff : Differentiable ℝ V := fun t => (hVd t).differentiableAt
  have hanti : Antitone V := antitone_of_deriv_nonpos hdiff fun t => by
    rw [(hVd t).deriv]
    by_cases h : P t = pstar
    · simp [h]
    · linarith [hsign _ h]
  have hbdd : BddBelow (Set.range V) := ⟨0, by rintro _ ⟨t, rfl⟩; exact hV0 t⟩
  set Vinf := ⨅ t, V t with hVinf
  have hlim : Tendsto V atTop (𝓝 Vinf) := tendsto_atTop_ciInf hanti hbdd
  have hVinf0 : 0 ≤ Vinf := le_ciInf hV0
  have hle : ∀ t, Vinf ≤ V t := fun t => ciInf_le hbdd t
  -- the limit is zero
  have hzero : Vinf = 0 := by
    by_contra hne
    have hpos : 0 < Vinf := lt_of_le_of_ne hVinf0 (Ne.symm hne)
    -- the compact shell `Vinf ≤ ‖p - p*‖² ≤ V 0`
    set g : (Fin L → ℝ) → ℝ := fun p => (p - pstar) ⬝ᵥ (p - pstar) with hg
    have hgc : Continuous g := by
      simp only [hg, dotProduct]; fun_prop
    set K := g ⁻¹' Set.Icc Vinf (V 0) with hK
    set c := V 0 + 1 with hc
    have hKbox : K ⊆ Set.Icc (pstar - fun _ => c) (pstar + fun _ => c) := by
      intro p hp
      have hp2 : g p ≤ V 0 := hp.2
      have hb : ∀ l, |p l - pstar l| ≤ c := fun l => by
        have h1 := sq_le_dotProduct_self (p - pstar) l
        simp only [Pi.sub_apply] at h1
        have h2 : (p l - pstar l) ^ 2 ≤ V 0 := h1.trans hp2
        rcases le_or_gt |p l - pstar l| 1 with h | h
        · linarith [hV0 0]
        · have : |p l - pstar l| ≤ (p l - pstar l) ^ 2 := by
            rw [← sq_abs]; nlinarith [abs_nonneg (p l - pstar l)]
          linarith
      exact ⟨fun l => by have := (abs_le.1 (hb l)).1; simp only [Pi.sub_apply]; linarith,
        fun l => by have := (abs_le.1 (hb l)).2; simp only [Pi.add_apply]; linarith⟩
    have hKc : IsCompact K :=
      isCompact_Icc.of_isClosed_subset (isClosed_Icc.preimage hgc) hKbox
    have hKn : K.Nonempty := ⟨P 0, hle 0, le_rfl⟩
    set h : (Fin L → ℝ) → ℝ := fun p => (p - pstar) ⬝ᵥ z p with hh
    have hhc : Continuous h := by
      simp only [hh, dotProduct]; fun_prop
    obtain ⟨q, hqK, hqmax⟩ := hKc.exists_isMaxOn hKn hhc.continuousOn
    have hq : h q < 0 := by
      refine hsign q fun hqe => ?_
      have := hqK.1
      simp only [hg, hqe, sub_self, dotProduct_zero] at this
      linarith
    -- along the trajectory `V' ≤ 2 h(q) < 0`
    have hmem : ∀ t, 0 ≤ t → P t ∈ K := fun t ht => ⟨hle t, hanti ht⟩
    set m := h q with hm
    have hW : ∀ t, 0 ≤ t → V t ≤ V 0 + 2 * m * t := by
      have hd : ∀ t, HasDerivAt (fun t => V t - 2 * m * t) (2 * h (P t) - 2 * m) t :=
        fun t => by
          have := (hVd t).sub ((hasDerivAt_id' t).const_mul (2 * m))
          rw [mul_one] at this
          exact this
      have hWanti : AntitoneOn (fun t => V t - 2 * m * t) (Set.Ici 0) := by
        refine antitoneOn_of_deriv_nonpos (convex_Ici 0)
          (fun t _ => (hd t).continuousAt.continuousWithinAt)
          (fun t _ => (hd t).differentiableAt.differentiableWithinAt) fun t ht => ?_
        rw [interior_Ici] at ht
        rw [(hd t).deriv]
        have := hqmax (hmem t (le_of_lt ht))
        simp only [Set.mem_ofPred_eq] at this
        linarith
      intro t ht
      have := hWanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 ht) ht
      simp only [mul_zero, sub_zero] at this
      linarith
    have ht := hW (-(V 0 + 1) / (2 * m))
      (div_nonneg_of_nonpos (by linarith [hV0 0]) (by linarith))
    have hm0 : m ≠ 0 := ne_of_lt hq
    have : 2 * m * (-(V 0 + 1) / (2 * m)) = -(V 0 + 1) := by
      field_simp
    linarith [hV0 (-(V 0 + 1) / (2 * m))]
  -- conclude coordinatewise
  rw [hzero] at hlim
  refine tendsto_pi_nhds.2 fun l => ?_
  have hsq : Tendsto (fun t => Real.sqrt (V t)) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hlim
    rw [Real.sqrt_zero] at this
    exact this
  refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ => norm_nonneg _)
    (fun t => ?_) hsq)
  rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
  have := sq_le_dotProduct_self (P t - pstar) l
  simp only [Pi.sub_apply] at this
  exact Real.sqrt_le_sqrt this

/-- **Global tâtonnement stability, the book's hypothesis** (MWG, p. 778): if the short-run
excess demand `z` is differentiable with a negative definite derivative everywhere and
`z(p*) = 0`, every solution of `dp/dt = z(p)` converges to `p*`. -/
theorem tatonnement_global_stable_negDef {z : (Fin L → ℝ) → Fin L → ℝ}
    {Dz : (Fin L → ℝ) → (Fin L → ℝ) →L[ℝ] (Fin L → ℝ)} (hDz : ∀ x, HasFDerivAt z (Dz x) x)
    (hneg : ∀ x v, v ≠ 0 → v ⬝ᵥ Dz x v < 0) {pstar : Fin L → ℝ} (hzero : z pstar = 0)
    {P : ℝ → Fin L → ℝ} (hP : ∀ t, HasDerivAt P (z (P t)) t) :
    Tendsto P atTop (𝓝 pstar) := by
  refine tatonnement_global_stable (continuous_iff_continuousAt.2 fun x =>
    (hDz x).continuousAt) (fun p hp => ?_) hP
  have := unique_zero_of_negDef convex_univ (fun x _ => hDz x) (fun x _ => hneg x)
    (Set.mem_univ p) (Set.mem_univ pstar) hp
  rwa [hzero, sub_zero] at this

/-- A proved instance: the linear excess demand `z(p) = p* - p`, whose derivative `-I` is
negative definite, and its trajectories `p(t) = p* + e^{-t} (p₀ - p*)`, which converge to `p*`. -/
theorem tatonnement_linear_instance (pstar p₀ : Fin L → ℝ) :
    (∀ t, HasDerivAt (fun s => pstar + Real.exp (-s) • (p₀ - pstar))
      (pstar - (pstar + Real.exp (-t) • (p₀ - pstar))) t) ∧
      Tendsto (fun s => pstar + Real.exp (-s) • (p₀ - pstar)) atTop (𝓝 pstar) := by
  refine ⟨fun t => ?_, ?_⟩
  · have h := ((Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)).smul_const (p₀ - pstar)
    have := h.const_add pstar
    exact this.congr_deriv (by rw [mul_neg_one, neg_smul]; abel)
  · have := tatonnement_global_stable_negDef (z := fun p => pstar - p)
      (Dz := fun _ => -ContinuousLinearMap.id ℝ (Fin L → ℝ))
      (fun x => (hasFDerivAt_id x).const_sub pstar)
      (fun x v hv => by
        change v ⬝ᵥ (-v) < 0
        rw [dotProduct_neg, neg_lt_zero]
        obtain ⟨l, hl⟩ := Function.ne_iff.1 hv
        exact lt_of_lt_of_le (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hl)))
          (sq_le_dotProduct_self v l))
      (sub_self pstar) (P := fun s => pstar + Real.exp (-s) • (p₀ - pstar)) (fun t => ?_)
    · exact this
    · have h := ((Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)).smul_const (p₀ - pstar)
      have := h.const_add pstar
      exact this.congr_deriv (by rw [mul_neg_one, neg_smul]; abel)

end MWG.EquilibriumTime
