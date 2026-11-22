/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGAggregateDemand.Hildenbrand
import MWGAggregateDemand.LawOfDemand
import MWGAggregateDemand.QuasilinearSlutsky
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Hildenbrand's law of demand: the strict part

MWG, Section 4.C, Proposition 4.C.4 (p. 113), the differentiable case of the book's proof, and
Exercise 4.C.10 (p. 124), "conclude that aggregate demand satisfies the WA".

The book's proof differentiates `x(p) = ∫₀^w̄ x̃(p, w) dw` under the integral sign and uses that
`v·S(p, w) v < 0` unless `v` is proportional to `p` (the hypothesis that correction 4 shows is
needed). Here the derivative is not taken under the integral: for `v = p' - p` and
`p_t = p + t v`, `v·[x̃(p', w) - x̃(p, w)] = ∫₀¹ v·D_p x̃(p_t, w) v dt` for each `w`, the double
integral is swapped (Fubini), and for each `t` the book's computation applies:
`∫₀^w̄ v·D_p x̃ v dw = ∫₀^w̄ v·S v dw - ½ (v·x̃(p_t, w̄))²`.

Price derivatives are directional (`Dp p w v`, the derivative of `t ↦ x̃(p + t v, w)` at `0`) and
the wealth derivative is `Dw p w`; their quadratic forms are assumed continuous on
`ℝ^L_{++} × [0, w̄]` (the book's "differentiable case").

* `hild_ray_slutsky`: on the price ray the Slutsky form vanishes, `v·S v = 0` for `v = c p`
  (Walras' law).
* `proposition_4_C_4_strict`: under these hypotheses, `(p' - p)·[x(p') - x(p)] < 0` for all
  `p ≠ p'`, so aggregate demand satisfies the ULD including its strict part.
* `cobbDouglasHalf_hildenbrand`: the hypotheses hold for the Cobb-Douglas demand
  `x̃(p, w) = (w/(2p₁), w/(2p₂))`.
* `exercise_4_C_10_weakAxiom`: the aggregate demand as a function of mean wealth `m` (wealth
  uniform on `[0, 2m]`), `X(p, m) = (1/2m) ∫₀^{2m} x̃(p, w) dw`, is homogeneous of degree zero,
  satisfies Walras' law and the ULD, hence the weak axiom.
-/

namespace MWG.AggregateDemand

open MWG.ConsumerChoice MWG.ClassicalDemand MeasureTheory Filter Topology

variable {L : ℕ}

/-- **Proposition 4.C.4** (MWG, p. 113), the ray. If `x̃` satisfies Walras' law, `w > 0`, the
derivative of `t ↦ x̃(q + t v, w)` at `0` is `d` for `v = c q`, and `D_w x̃(q, w) = e`, then
`v·d + (v·e)(x̃(q, w)·v) = 0`: the Slutsky form vanishes on the price ray. -/
theorem hild_ray_slutsky {x : DemandFunction L} (hW : WalrasLaw x) {q : Fin L → ℝ}
    (hq : StrictlyPositive q) {w : ℝ} (hw : 0 < w) (c : ℝ) {d e : Fin L → ℝ}
    (hp : HasDerivAt (fun t : ℝ => x (q + t • (c • q)) w) d 0) (hdw : HasDerivAt (x q) e w) :
    (c • q) ⬝ᵥ d + ((c • q) ⬝ᵥ e) * (x q w ⬝ᵥ (c • q)) = 0 := by
  have hqx : q ⬝ᵥ x q w = w := hW q w ⟨hq, hw⟩
  -- `q·e = 1`
  have hqe : q ⬝ᵥ e = 1 := by
    have h1 : HasDerivAt (fun s => q ⬝ᵥ x q s) (q ⬝ᵥ e) w := by
      have := (dualityDotCLM q).hasFDerivAt.comp_hasDerivAt w hdw
      simpa [Function.comp_def, dualityDotCLM_apply] using this
    have hev : (fun s => q ⬝ᵥ x q s) =ᶠ[𝓝 w] id := by
      filter_upwards [Ioi_mem_nhds hw] with s hs
      exact hW q s ⟨hq, hs⟩
    exact h1.unique ((hasDerivAt_id w).congr_of_eventuallyEq hev)
  -- `(c q)·x̃(q, w) + q·d = 0`
  have hqd : (c • q) ⬝ᵥ x q w + q ⬝ᵥ d = 0 := by
    have h1 : HasDerivAt (fun s : ℝ => q + s • (c • q)) (c • q) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (c • q)).const_add q
    have hc1 := hasDerivAt_pi.mp h1
    have hc2 := hasDerivAt_pi.mp hp
    have hs := HasDerivAt.sum (u := Finset.univ) fun l _ => (hc1 l).mul (hc2 l)
    have hf : HasDerivAt (fun s : ℝ => (q + s • (c • q)) ⬝ᵥ x (q + s • (c • q)) w)
        ((c • q) ⬝ᵥ x q w + q ⬝ᵥ d) 0 := by
      convert hs using 1
      · funext s
        simp only [dotProduct, Finset.sum_apply, Pi.mul_apply]
      · simp only [dotProduct, zero_smul, add_zero, ← Finset.sum_add_distrib]
    have hev : (fun s : ℝ => (q + s • (c • q)) ⬝ᵥ x (q + s • (c • q)) w) =ᶠ[𝓝 0]
        fun _ => w := by
      have hcont : Continuous fun s : ℝ => 1 + s * c := by fun_prop
      filter_upwards [hcont.continuousAt.eventually (lt_mem_nhds (show (0 : ℝ) < 1 + 0 * c by
        simp))] with s hs
      have heq : q + s • (c • q) = (1 + s * c) • q := by
        rw [smul_smul, add_smul, one_smul]
      rw [heq]
      exact hW _ w ⟨fun l => by simpa using mul_pos hs (hq l), hw⟩
    have := hf.unique ((hasDerivAt_const (0 : ℝ) w).congr_of_eventuallyEq hev)
    exact this
  simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul] at hqd ⊢
  rw [hqe, dotProduct_comm (x q w) q, hqx] at *
  have : q ⬝ᵥ d = -(c * w) := by linarith
  rw [this]
  ring

/-- **Proposition 4.C.4** (MWG, p. 113), the strict part, in the book's differentiable case.
Let `x̃` satisfy Walras' law with `x̃(p, 0) = 0`; let `t ↦ x̃(p + t v, w)` have derivative
`Dp p w v` at `0` and `w ↦ x̃(p, w)` derivative `Dw p w`, for `p ≫ 0`, `w ∈ [0, w̄]`, with
`v·Dp v` and `v·Dw` continuous on `ℝ^L_{++} × [0, w̄]`; and let the Slutsky form be negative off
the price ray: `v·S(p, w) v = v·Dp p w v + (v·Dw p w)(x̃(p, w)·v) < 0` for `w ∈ (0, w̄]` and `v`
not proportional to `p` (the book's extra hypothesis). Then
`(p' - p)·[x(p') - x(p)] < 0` for all `p ≠ p'`, `x(p) = ∫₀^w̄ x̃(p, w) dw`. -/
theorem proposition_4_C_4_strict {x : DemandFunction L} (hW : WalrasLaw x) {wb : ℝ}
    (hwb : 0 < wb) (h0 : ∀ p, StrictlyPositive p → x p 0 = 0)
    {Dp : (Fin L → ℝ) → ℝ → (Fin L → ℝ) → Fin L → ℝ} {Dw : (Fin L → ℝ) → ℝ → Fin L → ℝ}
    (hDp : ∀ p, StrictlyPositive p → ∀ w ∈ Set.Icc 0 wb, ∀ v,
      HasDerivAt (fun t : ℝ => x (p + t • v) w) (Dp p w v) 0)
    (hDw : ∀ p, StrictlyPositive p → ∀ w ∈ Set.Icc 0 wb, HasDerivAt (x p) (Dw p w) w)
    (hcp : ∀ v, ContinuousOn (fun z : (Fin L → ℝ) × ℝ => v ⬝ᵥ Dp z.1 z.2 v)
      ({p | StrictlyPositive p} ×ˢ Set.Icc 0 wb))
    (hcw : ∀ v, ContinuousOn (fun z : (Fin L → ℝ) × ℝ => v ⬝ᵥ Dw z.1 z.2)
      ({p | StrictlyPositive p} ×ˢ Set.Icc 0 wb))
    (hS : ∀ p, StrictlyPositive p → ∀ w ∈ Set.Ioc 0 wb, ∀ v, (∀ c : ℝ, v ≠ c • p) →
      v ⬝ᵥ Dp p w v + (v ⬝ᵥ Dw p w) * (x p w ⬝ᵥ v) < 0)
    {p p' : Fin L → ℝ} (hp : StrictlyPositive p) (hp' : StrictlyPositive p') (hne : p' ≠ p) :
    (p' - p) ⬝ᵥ (hildenbrandDemand x wb p' - hildenbrandDemand x wb p) < 0 := by
  set v := p' - p with hv
  have hv0 : v ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨P, hP⟩ : ∃ P : ℝ → Fin L → ℝ, P = fun t => p + t • v := ⟨_, rfl⟩
  have hPpos : ∀ t ∈ Set.Icc (0 : ℝ) 1, StrictlyPositive (P t) := by
    intro t ht l
    have e : P t l = (1 - t) * p l + t * p' l := by
      simp only [hP, hv, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      ring
    rw [e]
    rcases eq_or_lt_of_le ht.1 with h0 | h0
    · rw [← h0]; simpa using hp l
    · exact add_pos_of_nonneg_of_pos (mul_nonneg (by linarith [ht.2]) (hp l).le)
        (mul_pos h0 (hp' l))
  have hP0 : P 0 = p := by simp [hP]
  have hP1 : P 1 = p' := by simp [hP, hv]
  have hPc : Continuous P := by rw [hP]; fun_prop
  -- continuity of the integrand
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ → ℝ, g = fun t w => v ⬝ᵥ Dp (P t) w v := ⟨_, rfl⟩
  have hgc : ContinuousOn (fun z : ℝ × ℝ => g z.1 z.2) (Set.Icc 0 1 ×ˢ Set.Icc 0 wb) := by
    have hm : Set.MapsTo (fun z : ℝ × ℝ => (P z.1, z.2)) (Set.Icc 0 1 ×ˢ Set.Icc 0 wb)
        ({p | StrictlyPositive p} ×ˢ Set.Icc 0 wb) :=
      fun z hz => ⟨hPpos z.1 hz.1, hz.2⟩
    have := (hcp v).comp ((hPc.comp continuous_fst).prodMk continuous_snd).continuousOn hm
    rw [hg]
    exact this
  -- the derivative along the price path
  have hderiv : ∀ w ∈ Set.Icc 0 wb, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun s => v ⬝ᵥ x (P s) w) (g t w) t := by
    intro w hw t ht
    have h := hDp (P t) (hPpos t ht) w hw v
    have h' : HasDerivAt (fun s : ℝ => x (P t + (s - t) • v) w) (Dp (P t) w v) t :=
      HasDerivAt.comp_sub_const t t (by simpa using h)
    have hfun : (fun s : ℝ => x (P t + (s - t) • v) w) = fun s => x (P s) w := by
      funext s
      congr 1
      rw [hP]
      simp only [sub_smul]
      abel
    rw [hfun] at h'
    have := (dualityDotCLM v).hasFDerivAt.comp_hasDerivAt t h'
    rw [hg]
    simpa [Function.comp_def, dualityDotCLM_apply] using this
  have hFTC : ∀ w ∈ Set.Icc 0 wb, v ⬝ᵥ x p' w - v ⬝ᵥ x p w = ∫ t in (0 : ℝ)..1, g t w := by
    intro w hw
    have hc : ContinuousOn (fun t => g t w) (Set.uIcc 0 1) := by
      rw [Set.uIcc_of_le zero_le_one]
      have hm : Set.MapsTo (fun t : ℝ => (t, w)) (Set.Icc 0 1) (Set.Icc 0 1 ×ˢ Set.Icc 0 wb) :=
        fun t ht => ⟨ht, hw⟩
      exact hgc.comp (continuous_id.prodMk continuous_const).continuousOn hm
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hderiv w hw t
      (by rwa [Set.uIcc_of_le zero_le_one] at ht)) hc.intervalIntegrable, hP0, hP1]
  -- integrability in `w`
  have hxc : ∀ q, StrictlyPositive q → ContinuousOn (x q) (Set.Icc 0 wb) :=
    fun q hq w hw => (hDw q hq w hw).continuousAt.continuousWithinAt
  have hint : ∀ q, StrictlyPositive q → ∀ l, IntegrableOn (fun w => x q w l) (Set.Ioc 0 wb) := by
    intro q hq l
    exact (((continuous_apply l).comp_continuousOn (hxc q hq)).integrableOn_Icc).mono_set
      Set.Ioc_subset_Icc_self
  have hintd : ∀ q, StrictlyPositive q → IntegrableOn (fun w => v ⬝ᵥ x q w) (Set.Ioc 0 wb) := by
    intro q hq
    simp only [dotProduct]
    exact integrable_finsetSum _ fun l _ => (hint q hq l).const_mul (v l)
  -- the left side as a double integral
  have hLHS : (p' - p) ⬝ᵥ (hildenbrandDemand x wb p' - hildenbrandDemand x wb p) =
      ∫ w in Set.Ioc 0 wb, ∫ t in Set.Ioc (0 : ℝ) 1, g t w := by
    rw [← hv, dotProduct_sub, ← integral_dot_hildenbrand (hint p' hp'),
      ← integral_dot_hildenbrand (hint p hp), ← integral_sub (hintd p' hp') (hintd p hp)]
    refine setIntegral_congr_fun measurableSet_Ioc fun w hw => ?_
    rw [hFTC w (Set.Ioc_subset_Icc_self hw), intervalIntegral.integral_of_le zero_le_one]
  -- Fubini
  have hprod : Integrable (Function.uncurry fun w t => g t w)
      ((volume.restrict (Set.Ioc 0 wb)).prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    have hc : ContinuousOn (Function.uncurry fun w t => g t w)
        (Set.Icc 0 wb ×ˢ Set.Icc (0 : ℝ) 1) :=
      hgc.comp continuous_swap.continuousOn fun z hz => ⟨hz.2, hz.1⟩
    exact (hc.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self)
  have hswap := integral_integral_swap hprod
  obtain ⟨I, hI⟩ : ∃ I : ℝ → ℝ, I = fun t => ∫ w in Set.Ioc 0 wb, g t w := ⟨_, rfl⟩
  have hIint : IntegrableOn I (Set.Ioc (0 : ℝ) 1) := by
    rw [hI]; exact hprod.integral_prod_right
  -- for each `t`, `I(t) < 0`
  have hIneg : ∀ t ∈ Set.Icc (0 : ℝ) 1, I t < 0 := by
    intro t ht
    set q := P t with hq
    have hqp := hPpos t ht
    set φ : ℝ → ℝ := fun w => v ⬝ᵥ x q w with hφ
    set φ' : ℝ → ℝ := fun w => v ⬝ᵥ Dw q w with hφ'
    have hφd : ∀ w ∈ Set.uIcc 0 wb, HasDerivAt φ (φ' w) w := by
      intro w hw
      rw [Set.uIcc_of_le hwb.le] at hw
      have := (dualityDotCLM v).hasFDerivAt.comp_hasDerivAt w (hDw q hqp w hw)
      simpa [Function.comp_def, dualityDotCLM_apply, φ, φ'] using this
    have hφ'c : ContinuousOn φ' (Set.Icc 0 wb) :=
      (hcw v).comp (continuous_const.prodMk continuous_id).continuousOn fun w hw => ⟨hqp, hw⟩
    have hφc : ContinuousOn φ (Set.Icc 0 wb) := fun w hw =>
      (hφd w (by rwa [Set.uIcc_of_le hwb.le])).continuousAt.continuousWithinAt
    have hmean := hildenbrand_mean_income_effect hφd (by rwa [Set.uIcc_of_le hwb.le])
      (by simp [φ, h0 q hqp])
    set A : ℝ → ℝ := fun w => v ⬝ᵥ Dp q w v + (v ⬝ᵥ Dw q w) * (x q w ⬝ᵥ v) with hA
    have hAc : ContinuousOn A (Set.Icc 0 wb) := by
      have h1 : ContinuousOn (fun w => v ⬝ᵥ Dp q w v) (Set.Icc 0 wb) :=
        (hcp v).comp (continuous_const.prodMk continuous_id).continuousOn fun w hw => ⟨hqp, hw⟩
      have h2 : ContinuousOn (fun w => x q w ⬝ᵥ v) (Set.Icc 0 wb) := by
        simp only [dotProduct]
        exact continuousOn_finsetSum _ fun l _ =>
          ((continuous_apply l).comp_continuousOn (hxc q hqp)).mul continuousOn_const
      exact h1.add (hφ'c.mul h2)
    have hsplit : ∀ w, g t w = A w - φ' w * φ w := by
      intro w
      simp only [hg, A, φ, φ', ← hq, dotProduct_comm (x q w) v]
      ring
    have hIeq : I t = (∫ w in (0 : ℝ)..wb, A w) - φ wb ^ 2 / 2 := by
      calc I t = ∫ w in Set.Ioc 0 wb, (A w - φ' w * φ w) := by
            simp only [hI]
            exact setIntegral_congr_fun measurableSet_Ioc fun w _ => hsplit w
        _ = (∫ w in Set.Ioc 0 wb, A w) - ∫ w in Set.Ioc 0 wb, φ' w * φ w :=
            integral_sub (hAc.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
              ((hφ'c.mul hφc).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
        _ = _ := by
            rw [← hmean, intervalIntegral.integral_of_le hwb.le,
              intervalIntegral.integral_of_le hwb.le]
    rw [hIeq]
    by_cases hray : ∃ c : ℝ, v = c • q
    · -- on the ray the Slutsky term vanishes and the mean income effect is `-(c w̄)²/2 < 0`
      obtain ⟨c, hc⟩ := hray
      have hc0 : c ≠ 0 := by
        rintro rfl
        exact hv0 (by rw [hc, zero_smul])
      have hA0 : ∫ w in (0 : ℝ)..wb, A w = 0 := by
        rw [intervalIntegral.integral_of_le hwb.le]
        rw [setIntegral_congr_fun measurableSet_Ioc (g := fun _ => (0 : ℝ)) fun w hw => ?_]
        · simp
        · have hw' : w ∈ Set.Icc 0 wb := Set.Ioc_subset_Icc_self hw
          simp only [A]
          rw [hc]
          exact hild_ray_slutsky hW hqp hw.1 c (hc ▸ hDp q hqp w hw' v) (hDw q hqp w hw')
      have hφwb : φ wb = c * wb := by
        simp only [φ, hc, smul_dotProduct, smul_eq_mul, hW q wb ⟨hqp, hwb⟩]
      rw [hA0, hφwb]
      have : 0 < (c * wb) ^ 2 := by positivity
      linarith
    · push Not at hray
      have hneg : ∫ w in (0 : ℝ)..wb, -A w > 0 := by
        apply intervalIntegral.intervalIntegral_pos_of_pos_on
          (hAc.neg.intervalIntegrable_of_Icc hwb.le) _ hwb
        intro w hw
        have := hS q hqp w (Set.Ioo_subset_Ioc_self hw) v (fun c h => hray c h)
        simp only [A, Pi.neg_apply] at this ⊢
        linarith
      rw [intervalIntegral.integral_neg] at hneg
      nlinarith [sq_nonneg (φ wb)]
  rw [hLHS, hswap]
  have hpos : 0 < ∫ t in (0 : ℝ)..1, -I t := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on _ _ zero_lt_one
    · exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr hIint).neg
    · intro t ht
      linarith [hIneg t (Set.Ioo_subset_Icc_self ht)]
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_of_le zero_le_one] at hpos
  have hlt : ∫ t in Set.Ioc (0 : ℝ) 1, I t < 0 := by linarith
  simpa [hI] using hlt

/-! ### The hypotheses hold for Cobb-Douglas demand -/

/-- The Cobb-Douglas demand `x̃(p, w) = (w/(2p₁), w/(2p₂))` (utility `x₁ x₂`). -/
noncomputable def cdHalf : DemandFunction 2 := fun p w => ![w / (2 * p 0), w / (2 * p 1)]

/-- Its directional price derivative. -/
noncomputable def cdHalfDp (p : Fin 2 → ℝ) (w : ℝ) (v : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![-(w * v 0) / (2 * p 0 ^ 2), -(w * v 1) / (2 * p 1 ^ 2)]

/-- Its wealth derivative. -/
noncomputable def cdHalfDw (p : Fin 2 → ℝ) (_w : ℝ) : Fin 2 → ℝ := ![1 / (2 * p 0), 1 / (2 * p 1)]

/-- **Proposition 4.C.4** (MWG, p. 113): the hypotheses of `proposition_4_C_4_strict` and
`exercise_4_C_10_weakAxiom` hold for the Cobb-Douglas demand `x̃(p, w) = (w/(2p₁), w/(2p₂))`,
whose Slutsky form is `v·S v = -(w/4)(v₁/p₁ - v₂/p₂)²`, negative off the price ray. -/
theorem cdHalf_hypotheses :
    WalrasLaw cdHalf ∧ (∀ p, StrictlyPositive p → cdHalf p 0 = 0) ∧
    (∀ p, StrictlyPositive p → ∀ w, 0 ≤ w → ∀ v,
      HasDerivAt (fun t : ℝ => cdHalf (p + t • v) w) (cdHalfDp p w v) 0) ∧
    (∀ p, StrictlyPositive p → ∀ w, 0 ≤ w → HasDerivAt (cdHalf p) (cdHalfDw p w) w) ∧
    (∀ v, ContinuousOn (fun z : (Fin 2 → ℝ) × ℝ => v ⬝ᵥ cdHalfDp z.1 z.2 v)
      ({p | StrictlyPositive p} ×ˢ Set.Ici 0)) ∧
    (∀ v, ContinuousOn (fun z : (Fin 2 → ℝ) × ℝ => v ⬝ᵥ cdHalfDw z.1 z.2)
      ({p | StrictlyPositive p} ×ˢ Set.Ici 0)) ∧
    (∀ p, StrictlyPositive p → ∀ w, 0 < w → ∀ v, (∀ c : ℝ, v ≠ c • p) →
      v ⬝ᵥ cdHalfDp p w v + (v ⬝ᵥ cdHalfDw p w) * (cdHalf p w ⬝ᵥ v) < 0) := by
  have hpos : ∀ z ∈ ({p | StrictlyPositive p} ×ˢ Set.Ici 0 : Set ((Fin 2 → ℝ) × ℝ)),
      ∀ l, z.1 l ≠ 0 := fun z hz l => (hz.1 l).ne'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q w hd
    have := hd.1 0
    have := hd.1 1
    simp only [cdHalf, dotProduct_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    field_simp
    ring
  · intro q _
    funext l
    fin_cases l <;> simp [cdHalf]
  · intro q hq w _ v
    have h0 : 2 * q 0 ≠ 0 := by have := hq 0; positivity
    have h1 : 2 * q 1 ≠ 0 := by have := hq 1; positivity
    refine hasDerivAt_pi.mpr fun l => ?_
    fin_cases l
    · have := hasDerivAt_ratio_line w 0 (2 * q 0) (2 * v 0) h0
      convert this using 1
      · funext t
        simp only [cdHalf, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.zero_eta,
          Matrix.cons_val_zero]
        ring
      · simp only [cdHalfDp, Fin.zero_eta, Matrix.cons_val_zero]
        field_simp
        ring
    · have := hasDerivAt_ratio_line w 0 (2 * q 1) (2 * v 1) h1
      convert this using 1
      · funext t
        simp only [cdHalf, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.mk_one,
          Matrix.cons_val_one, Matrix.cons_val_fin_one]
        ring
      · simp only [cdHalfDp, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
        field_simp
        ring
  · intro q _ w _
    refine hasDerivAt_pi.mpr fun l => ?_
    fin_cases l
    · simpa [cdHalf, cdHalfDw] using (hasDerivAt_id w).div_const (2 * q 0)
    · simpa [cdHalf, cdHalfDw] using (hasDerivAt_id w).div_const (2 * q 1)
  · intro v
    simp only [cdHalfDp, dotProduct_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    apply ContinuousOn.add <;> apply ContinuousOn.mul continuousOn_const <;>
      apply ContinuousOn.div (by fun_prop) (by fun_prop) <;> intro z hz <;>
      simp [hpos z hz]
  · intro v
    simp only [cdHalfDw, dotProduct_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    apply ContinuousOn.add <;> apply ContinuousOn.mul continuousOn_const <;>
      apply ContinuousOn.div (by fun_prop) (by fun_prop) <;> intro z hz <;>
      simp [hpos z hz]
  · intro q hq w hw v hv
    have h0 := (hq 0).ne'
    have h1 := (hq 1).ne'
    have key : v ⬝ᵥ cdHalfDp q w v + (v ⬝ᵥ cdHalfDw q w) * (cdHalf q w ⬝ᵥ v) =
        -(w / 4) * (v 0 / q 0 - v 1 / q 1) ^ 2 := by
      simp only [cdHalf, cdHalfDp, cdHalfDw, dotProduct_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one]
      field_simp
      ring
    rw [key]
    have hne : v 0 / q 0 - v 1 / q 1 ≠ 0 := by
      intro h
      apply hv (v 0 / q 0)
      funext l
      fin_cases l
      · simp only [Fin.zero_eta, Pi.smul_apply, smul_eq_mul]
        field_simp
      · simp only [Fin.mk_one, Pi.smul_apply, smul_eq_mul]
        have : v 1 / q 1 = v 0 / q 0 := by linarith
        field_simp at this ⊢
        linarith
    have : 0 < (v 0 / q 0 - v 1 / q 1) ^ 2 := by positivity
    have : 0 < w / 4 := by linarith
    nlinarith

/-- **Proposition 4.C.4** (MWG, p. 113), a proved instance of `proposition_4_C_4_strict`: the
strict ULD for the Hildenbrand aggregate of the Cobb-Douglas demand `cdHalf`. -/
theorem cobbDouglasHalf_hildenbrand {wb : ℝ} (hwb : 0 < wb) {p p' : Fin 2 → ℝ}
    (hp : StrictlyPositive p) (hp' : StrictlyPositive p') (hne : p' ≠ p) :
    (p' - p) ⬝ᵥ (hildenbrandDemand cdHalf wb p' - hildenbrandDemand cdHalf wb p) < 0 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := cdHalf_hypotheses
  have hsub : ({p | StrictlyPositive p} ×ˢ Set.Icc 0 wb : Set ((Fin 2 → ℝ) × ℝ)) ⊆
      {p | StrictlyPositive p} ×ˢ Set.Ici 0 := Set.prod_mono le_rfl Set.Icc_subset_Ici_self
  exact proposition_4_C_4_strict h1 hwb h2 (fun q hq w hw => h3 q hq w hw.1)
    (fun q hq w hw => h4 q hq w hw.1) (fun v => (h5 v).mono hsub) (fun v => (h6 v).mono hsub)
    (fun q hq w hw => h7 q hq w hw.1) hp hp' hne

/-! ### Exercise 4.C.10: the weak axiom -/

/-- The aggregate demand of Proposition 4.C.4 per consumer, as a function of prices and mean
wealth `m`: wealth uniform on `[0, 2m]`, `X(p, m) = (1/2m) ∫₀^{2m} x̃(p, w) dw`. -/
noncomputable def hildMeanDemand (x : DemandFunction L) : DemandFunction L :=
  fun p m => (1 / (2 * m)) • hildenbrandDemand x (2 * m) p

/-- **Exercise 4.C.10** (MWG, p. 124), "conclude that aggregate demand satisfies the WA for that
wealth distribution". Under the hypotheses of `proposition_4_C_4_strict` for every `w̄` (with
`x̃` homogeneous of degree zero), the aggregate demand `X(p, m)` of a continuum of consumers
with wealth uniform on `[0, 2m]` is homogeneous of degree zero, satisfies Walras' law and the
ULD, and hence the weak axiom. -/
theorem exercise_4_C_10_weakAxiom {x : DemandFunction L} (hW : WalrasLaw x)
    (hH : HomogeneousZero x) (h0 : ∀ p, StrictlyPositive p → x p 0 = 0)
    {Dp : (Fin L → ℝ) → ℝ → (Fin L → ℝ) → Fin L → ℝ} {Dw : (Fin L → ℝ) → ℝ → Fin L → ℝ}
    (hDp : ∀ p, StrictlyPositive p → ∀ w, 0 ≤ w → ∀ v,
      HasDerivAt (fun t : ℝ => x (p + t • v) w) (Dp p w v) 0)
    (hDw : ∀ p, StrictlyPositive p → ∀ w, 0 ≤ w → HasDerivAt (x p) (Dw p w) w)
    (hcp : ∀ v, ContinuousOn (fun z : (Fin L → ℝ) × ℝ => v ⬝ᵥ Dp z.1 z.2 v)
      ({p | StrictlyPositive p} ×ˢ Set.Ici 0))
    (hcw : ∀ v, ContinuousOn (fun z : (Fin L → ℝ) × ℝ => v ⬝ᵥ Dw z.1 z.2)
      ({p | StrictlyPositive p} ×ˢ Set.Ici 0))
    (hS : ∀ p, StrictlyPositive p → ∀ w, 0 < w → ∀ v, (∀ c : ℝ, v ≠ c • p) →
      v ⬝ᵥ Dp p w v + (v ⬝ᵥ Dw p w) * (x p w ⬝ᵥ v) < 0) :
    HomogeneousZero (hildMeanDemand x) ∧ WalrasLaw (hildMeanDemand x) ∧
      UncompensatedLawOfDemand (hildMeanDemand x) ∧ WeakAxiom (hildMeanDemand x) := by
  have hsub : ∀ wb : ℝ, ({p | StrictlyPositive p} ×ˢ Set.Icc 0 wb : Set ((Fin L → ℝ) × ℝ)) ⊆
      {p | StrictlyPositive p} ×ˢ Set.Ici 0 :=
    fun wb => Set.prod_mono le_rfl Set.Icc_subset_Ici_self
  have hstrict : ∀ m, 0 < m → ∀ p p' : Fin L → ℝ, StrictlyPositive p → StrictlyPositive p' →
      p' ≠ p → (p' - p) ⬝ᵥ (hildenbrandDemand x (2 * m) p' - hildenbrandDemand x (2 * m) p) < 0 :=
    fun m hm p p' hp hp' hne => proposition_4_C_4_strict hW (by linarith) h0
      (fun q hq w hw => hDp q hq w hw.1) (fun q hq w hw => hDw q hq w hw.1)
      (fun v => (hcp v).mono (hsub _)) (fun v => (hcw v).mono (hsub _))
      (fun q hq w hw => hS q hq w hw.1) hp hp' hne
  have hint : ∀ q, StrictlyPositive q → ∀ wb, ∀ l,
      IntegrableOn (fun w => x q w l) (Set.Ioc 0 wb) := by
    intro q hq wb l
    have hc : ContinuousOn (fun w => x q w l) (Set.Icc 0 wb) := fun w hw =>
      ((continuous_apply l).continuousAt.comp
        (hDw q hq w hw.1).continuousAt).continuousWithinAt
    exact hc.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hHom : HomogeneousZero (hildMeanDemand x) := by
    intro p m α hd hα
    have hαp : StrictlyPositive (α • p) := (pwDomain_smul hd hα).1
    have hm := hd.2
    funext l
    simp only [hildMeanDemand, hildenbrandDemand, Pi.smul_apply, smul_eq_mul]
    have key : ∫ w in Set.Ioc 0 (2 * (α * m)), x (α • p) w l =
        α * ∫ w in Set.Ioc 0 (2 * m), x p w l := by
      rw [← intervalIntegral.integral_of_le (by positivity),
        ← intervalIntegral.integral_of_le (by positivity)]
      rw [intervalIntegral.integral_congr (g := fun w => x p (w / α) l) fun w hw => ?_]
      · rw [intervalIntegral.integral_comp_div (fun u => x p u l) hα.ne', smul_eq_mul]
        congr 2
        · simp
        · field_simp
      · rw [Set.uIcc_of_le (by positivity)] at hw
        rcases eq_or_lt_of_le hw.1 with h | h
        · beta_reduce
          rw [← h, zero_div, h0 _ hαp, h0 _ hd.1]
        · have := hH p (w / α) α ⟨hd.1, div_pos h hα⟩ hα
          rw [mul_div_cancel₀ _ hα.ne'] at this
          simp only [this]
    rw [key]
    field_simp
  have hWal : WalrasLaw (hildMeanDemand x) := by
    intro p m hd
    have hm := hd.2
    simp only [hildMeanDemand, dotProduct_smul, smul_eq_mul]
    rw [← integral_dot_hildenbrand (hint p hd.1 (2 * m)),
      setIntegral_congr_fun measurableSet_Ioc (g := fun w => w) fun w hw => hW p w ⟨hd.1, hw.1⟩,
      ← intervalIntegral.integral_of_le (by positivity), integral_id]
    field_simp
    ring
  have hU : UncompensatedLawOfDemand (hildMeanDemand x) := by
    intro p p' m hd hp'
    by_cases hpp : p' = p
    · subst hpp
      simp
    · have hneg := hstrict m hd.2 p p' hd.1 hp' hpp
      have e : (p' - p) ⬝ᵥ (hildMeanDemand x p' m - hildMeanDemand x p m) =
          (1 / (2 * m)) * ((p' - p) ⬝ᵥ
            (hildenbrandDemand x (2 * m) p' - hildenbrandDemand x (2 * m) p)) := by
        simp only [hildMeanDemand, ← smul_sub, dotProduct_smul, smul_eq_mul]
      have hc : 0 < 1 / (2 * m) := by have := hd.2; positivity
      rw [e]
      exact ⟨(mul_neg_of_pos_of_neg hc hneg).le, fun _ => mul_neg_of_pos_of_neg hc hneg⟩
  exact ⟨hHom, hWal, hU, weakAxiom_of_uld hHom hWal hU⟩

/-- **Exercise 4.C.10** (MWG, p. 124), a proved instance of `exercise_4_C_10_weakAxiom`: the
Hildenbrand aggregate of the Cobb-Douglas demand `cdHalf` satisfies the weak axiom. -/
theorem cobbDouglasHalf_weakAxiom : WeakAxiom (hildMeanDemand cdHalf) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := cdHalf_hypotheses
  have hH : HomogeneousZero cdHalf := by
    intro p w α hd hα
    have := hd.1 0
    have := hd.1 1
    funext l
    fin_cases l <;> simp [cdHalf] <;> field_simp
  exact (exercise_4_C_10_weakAxiom h1 hH h2 h3 h4 h5 h6 h7).2.2.2

end MWG.AggregateDemand
