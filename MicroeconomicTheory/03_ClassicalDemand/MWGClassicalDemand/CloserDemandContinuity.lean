/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.ExpContinuity
import MWGClassicalDemand.RelationsBasic

/-!
# Exercise 3.AA.2: continuity of `h` and `e`, differentiability of `h`

MWG, Appendix A to Chapter 3, Exercise 3.AA.2, p. 95: under the conditions of Proposition
3.AA.1 (`u` continuous, representing locally nonsatiated `≿` on `ℝ^L_+`), `h(p, u)` is upper
hemicontinuous and `e(p, u)` is continuous, "even if we replace minimum by infimum and allow
`p = 0`"; and conditions for differentiability of `h` when it is a function.

* `exercise_3_AA_2_uhc`: `h` is upper hemicontinuous at every `(p̄, ū)` with `p̄ ≫ 0` in the
  sense of Definition 3.AA.1 (limits of Hicksian bundles along `(pⁿ, ūⁿ) → (p̄, ū)` are Hicksian
  bundles at the limit), and `exercise_3_AA_2_bounded`: `h` is locally bounded there.
* `exercise_3_AA_2_continuous`: `e` is jointly continuous on `{p ≫ 0, ū attainable}`
  (Proposition 3.E.2(iv) of Part B), and `exercise_3_AA_2_inf_continuous`: with the infimum
  definition, `e(·, ū)` is continuous on all of `ℝ^L_+`, boundary prices `p_l = 0` (and `p = 0`)
  included, for any `u` and attainable `ū`. Joint continuity in `(p, ū)` at boundary prices is
  not proved (see `docs/source-map-E.md`).
* `exercise_3_AA_2_differentiable`: when `h(·, ū)` is a function, it is differentiable at
  `p̄ ≫ 0` exactly when `∇_p e(·, ū)` is, with the same derivative (Shephard's lemma): `h` is
  `C¹` iff `e(·, ū)` is `C²`.
-/

namespace MWG.ClassicalDemand

open Filter Topology MWG.ConsumerChoice Kreps.PreferenceProperties

variable {L : ℕ}

/-- **Exercise 3.AA.2** (MWG, p. 95), upper hemicontinuity of `h` (Definition 3.AA.1). Let `u` be
continuous on `ℝ^L_+` and represent a locally nonsatiated `≿`. If `(pⁿ, ūⁿ) → (p̄, ū)` with
`p̄ ≫ 0`, `hⁿ ∈ h(pⁿ, ūⁿ)` and `hⁿ → h̄`, then `h̄ ∈ h(p̄, ū)`. -/
theorem exercise_3_AA_2_uhc {u : (Fin L → ℝ) → ℝ} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hrep : RepresentsOn (nonnegOrthant L) u r) (hu : ContinuousOn u (nonnegOrthant L))
    (hlns : LocallyNonsatiated (nonnegOrthant L) r) {ps : ℕ → Fin L → ℝ} {us : ℕ → ℝ}
    {hs : ℕ → Fin L → ℝ} {p hbar : Fin L → ℝ} {ub : ℝ} (hp : StrictlyPositive p)
    (hps : ∀ n, StrictlyPositive (ps n)) (hhs : ∀ n, hs n ∈ hicksianDemand u (ps n) (us n))
    (hpt : Tendsto ps atTop (𝓝 p)) (hut : Tendsto us atTop (𝓝 ub))
    (hht : Tendsto hs atTop (𝓝 hbar)) : hbar ∈ hicksianDemand u p ub := by
  have hclosed : IsClosed (nonnegOrthant L) := exp_isClosed_nonnegOrthant L
  have hb0 : hbar ∈ nonnegOrthant L :=
    hclosed.mem_of_tendsto hht (Eventually.of_forall fun n => (hhs n).1.1)
  have hbu : ub ≤ u hbar := by
    have hcont : Tendsto (fun n => u (hs n)) atTop (𝓝 (u hbar)) :=
      ((hu hbar hb0).tendsto.comp (tendsto_nhdsWithin_iff.2
        ⟨hht, Eventually.of_forall fun n => (hhs n).1.1⟩))
    exact le_of_tendsto_of_tendsto' hut hcont fun n => (hhs n).1.2
  -- `pⁿ·hⁿ = e(pⁿ, ūⁿ) → e(p̄, ū)`
  have hdom : ∀ n, (ps n, us n) ∈ expDomain u := fun n => ⟨hps n, hs n, (hhs n).1.1, (hhs n).1.2⟩
  have hdom0 : (p, ub) ∈ expDomain u := ⟨hp, hbar, hb0, hbu⟩
  have he := (proposition_3_E_2_iv hrep hu hlns (p, ub) hdom0).tendsto.comp
    (tendsto_nhdsWithin_iff.2 ⟨hpt.prodMk_nhds hut, Eventually.of_forall hdom⟩)
  have hval : ∀ n, expenditure u (ps n) (us n) = ps n ⬝ᵥ hs n :=
    fun n => expenditure_eq_of_mem (hhs n)
  have hdot : Tendsto (fun n => ps n ⬝ᵥ hs n) atTop (𝓝 (p ⬝ᵥ hbar)) :=
    ((continuous_fst.dotProduct continuous_snd).tendsto (p, hbar)).comp
      (hpt.prodMk_nhds hht)
  have heq : p ⬝ᵥ hbar = expenditure u p ub := by
    refine tendsto_nhds_unique hdot ?_
    refine he.congr fun n => ?_
    simp only [Function.comp_apply]
    exact hval n
  refine ⟨⟨hb0, hbu⟩, fun y hy => ?_⟩
  rw [heq]
  exact supportFn_le (exp_bddBelow hp ub) hy

/-- **Exercise 3.AA.2** (MWG, p. 95), local boundedness of `h` (footnote 32): if `p̄ ≫ 0` and
`ū` is attainable, all Hicksian bundles for `(p, ū')` near `(p̄, ū)` (with `ū'` attainable) lie
in a bounded set. -/
theorem exercise_3_AA_2_bounded {u : (Fin L → ℝ) → ℝ} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hrep : RepresentsOn (nonnegOrthant L) u r) (hu : ContinuousOn u (nonnegOrthant L))
    (hlns : LocallyNonsatiated (nonnegOrthant L) r) {p : Fin L → ℝ} {ub : ℝ}
    (hdom : (p, ub) ∈ expDomain u) :
    ∃ R : ℝ, ∀ᶠ z in 𝓝[expDomain u] (p, ub), ∀ x ∈ hicksianDemand u z.1 z.2,
      ∀ l, x l ≤ R := by
  have hp := hdom.1
  obtain ⟨c, hc, hcp⟩ := exists_pos_le_of_pos p hp
  have hcont := proposition_3_E_2_iv hrep hu hlns (p, ub) hdom
  refine ⟨2 * (expenditure u p ub + 1) / c, ?_⟩
  have h1 : ∀ᶠ z in 𝓝[expDomain u] (p, ub), expenditure u z.1 z.2 < expenditure u p ub + 1 :=
    hcont.eventually (gt_mem_nhds (lt_add_one _))
  have h2 : ∀ᶠ z in 𝓝[expDomain u] (p, ub), ∀ l, c / 2 < z.1 l := by
    apply eventually_nhdsWithin_of_eventually_nhds
    rw [eventually_all]
    intro l
    have : Tendsto (fun z : (Fin L → ℝ) × ℝ => z.1 l) (𝓝 (p, ub)) (𝓝 (p l)) :=
      ((continuous_apply l).comp continuous_fst).tendsto _
    exact this.eventually (lt_mem_nhds (by linarith [hcp l]))
  filter_upwards [h1, h2] with z hz1 hz2 x hx l
  have hval := expenditure_eq_of_mem hx
  have hxl : z.1 l * x l ≤ z.1 ⬝ᵥ x :=
    Finset.single_le_sum (f := fun j => z.1 j * x j)
      (fun j _ => mul_nonneg (by linarith [hz2 j, hc]) (hx.1.1 j)) (Finset.mem_univ l)
  have hxl0 : 0 ≤ x l := hx.1.1 l
  have hcl : c / 2 * x l ≤ z.1 l * x l := mul_le_mul_of_nonneg_right (hz2 l).le hxl0
  rw [le_div_iff₀ hc]
  nlinarith

/-- **Exercise 3.AA.2** (MWG, p. 95), continuity of `e` (Proposition 3.E.2(iv)): jointly
continuous on `{(p, ū) : p ≫ 0, ū attainable}`. -/
theorem exercise_3_AA_2_continuous {u : (Fin L → ℝ) → ℝ} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hrep : RepresentsOn (nonnegOrthant L) u r) (hu : ContinuousOn u (nonnegOrthant L))
    (hlns : LocallyNonsatiated (nonnegOrthant L) r) :
    ContinuousOn (fun z : (Fin L → ℝ) × ℝ => expenditure u z.1 z.2) (expDomain u) :=
  proposition_3_E_2_iv hrep hu hlns

/-- **Exercise 3.AA.2** (MWG, p. 95), "even if we replace minimum by infimum and allow `p = 0`":
for any `u` and attainable `ū`, `e(p, ū) = inf {p·x : x ≥ 0, u(x) ≥ ū}` is continuous in `p` on
the whole closed orthant `ℝ^L_+`. -/
theorem exercise_3_AA_2_inf_continuous (u : (Fin L → ℝ) → ℝ) {ub : ℝ}
    (hne : ∃ x ∈ nonnegOrthant L, ub ≤ u x) :
    ContinuousOn (fun p => expenditure u p ub) (nonnegOrthant L) := by
  obtain ⟨x0, hx0, hx0u⟩ := hne
  have hCne : (empConstraintSet u ub).Nonempty := ⟨x0, hx0, hx0u⟩
  have hnn : ∀ q ∈ nonnegOrthant L, ∀ x ∈ empConstraintSet u ub, 0 ≤ q ⬝ᵥ x :=
    fun q hq x hx => Finset.sum_nonneg fun l _ => mul_nonneg (hq l) (hx.1 l)
  have hbdd : ∀ q ∈ nonnegOrthant L, BddBelow ((fun x => q ⬝ᵥ x) '' empConstraintSet u ub) :=
    fun q hq => ⟨0, by rintro _ ⟨x, hx, rfl⟩; exact hnn q hq x hx⟩
  have he0 : ∀ q ∈ nonnegOrthant L, 0 ≤ expenditure u q ub :=
    fun q hq => le_supportFn hCne fun x hx => hnn q hq x hx
  intro p hp
  rw [ContinuousWithinAt, tendsto_order]
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · -- lower semicontinuity: `q ≥ (1 - η) p` near `p` gives `e(q) ≥ (1 - η) e(p)`
    rcases (he0 p hp).lt_or_eq with hpos | hzero
    · set η := min (1 / 2) ((expenditure u p ub - a) / (2 * expenditure u p ub)) with hη
      have hη0 : 0 < η := lt_min (by norm_num) (div_pos (by linarith) (by linarith))
      have hη1 : η < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
      have hηa : a < (1 - η) * expenditure u p ub := by
        have : η * expenditure u p ub ≤ (expenditure u p ub - a) / 2 := by
          calc η * expenditure u p ub ≤
              (expenditure u p ub - a) / (2 * expenditure u p ub) * expenditure u p ub :=
                mul_le_mul_of_nonneg_right (min_le_right _ _) hpos.le
            _ = (expenditure u p ub - a) / 2 := by field_simp
        linarith
      have hnear : ∀ᶠ q in 𝓝[nonnegOrthant L] p, ∀ l, (1 - η) * p l ≤ q l := by
        rw [eventually_all]
        intro l
        rcases (hp l).lt_or_eq with hpl | hpl
        · apply eventually_nhdsWithin_of_eventually_nhds
          have : Tendsto (fun q : Fin L → ℝ => q l) (𝓝 p) (𝓝 (p l)) :=
            (continuous_apply l).tendsto p
          filter_upwards [this.eventually (lt_mem_nhds (show (1 - η) * p l < p l by nlinarith))]
            with q hq using hq.le
        · filter_upwards [self_mem_nhdsWithin] with q hq
          rw [← hpl, mul_zero]
          exact hq l
      filter_upwards [hnear, self_mem_nhdsWithin] with q hq hq0
      refine lt_of_lt_of_le hηa ?_
      refine le_supportFn hCne fun x hx => ?_
      have h1 : (1 - η) * expenditure u p ub ≤ (1 - η) * (p ⬝ᵥ x) :=
        mul_le_mul_of_nonneg_left (supportFn_le (hbdd p hp) hx) (by linarith)
      have h2 : (1 - η) * (p ⬝ᵥ x) ≤ q ⬝ᵥ x := by
        rw [← smul_eq_mul, ← smul_dotProduct]
        exact Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_right (by
          simpa [smul_eq_mul] using hq l) (hx.1 l)
      exact h1.trans h2
    · filter_upwards [self_mem_nhdsWithin] with q hq
      rw [← hzero] at ha
      exact lt_of_lt_of_le ha (he0 q hq)
  · -- upper semicontinuity: `e(q) ≤ q·x` for a near-optimal `x`
    obtain ⟨_, ⟨x, hx, rfl⟩, hxa⟩ := exists_lt_of_csInf_lt (hCne.image _) ha
    have hcont : Tendsto (fun q : Fin L → ℝ => q ⬝ᵥ x) (𝓝[nonnegOrthant L] p) (𝓝 (p ⬝ᵥ x)) :=
      ((continuous_id.dotProduct continuous_const).tendsto p).mono_left nhdsWithin_le_nhds
    filter_upwards [hcont.eventually (gt_mem_nhds hxa), self_mem_nhdsWithin] with q hq hq0
    exact lt_of_le_of_lt (supportFn_le (hbdd q hq0) hx) hq

/-- **Exercise 3.AA.2** (MWG, p. 95), differentiability of `h`. Let `u` be continuous and strictly
quasiconcave on `ℝ^L_+`, so that a Hicksian demand function `hf(·, ū)` is defined on `p ≫ 0`. At
`p̄ ≫ 0`, `hf` has derivative `D` iff the gradient `∇_p e(·, ū)` does: `h(·, ū)` is
differentiable exactly where `e(·, ū)` is twice differentiable (Shephard's lemma). -/
theorem exercise_3_AA_2_differentiable {u : (Fin L → ℝ) → ℝ}
    (hu : ContinuousOn u (nonnegOrthant L)) (hq : StrictlyQuasiconcaveOn (nonnegOrthant L) u)
    {ub : ℝ} {hf : (Fin L → ℝ) → (Fin L → ℝ)}
    (hhf : ∀ q, StrictlyPositive q → hf q ∈ hicksianDemand u q ub) {p : Fin L → ℝ}
    (hp : StrictlyPositive p) (D : (Fin L → ℝ) →L[ℝ] (Fin L → ℝ)) :
    HasFDerivAt hf D p ↔
      HasFDerivAt (fun y => gradientVec (fderiv ℝ (fun q => expenditure u q ub) y)) D p := by
  have heq : (fun y => gradientVec (fderiv ℝ (fun q => expenditure u q ub) y)) =ᶠ[𝓝 p] hf := by
    filter_upwards [eventually_hasFDerivAt_expenditure hu hq hhf hp] with y hy
    rw [hy.fderiv, gradientVec_dualityDotCLM]
  exact ⟨fun h => h.congr_of_eventuallyEq heq, fun h => h.congr_of_eventuallyEq heq.symm⟩

end MWG.ClassicalDemand
