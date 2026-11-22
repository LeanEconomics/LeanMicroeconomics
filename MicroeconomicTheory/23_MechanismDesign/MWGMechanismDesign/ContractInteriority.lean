/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMechanismDesign.OptimalContract

/-!
# Example 23.F.1: interiority and the first-best contract

MWG, Section 23.F, Example 23.F.1 (pp. 900-903), footnote 48 (p. 902), and the parenthetical
claim of Exercise 23.F.1 (p. 923).

* **Footnote 48** (`footnote_23_48`): "under our assumptions, the optimal contract is interior,
  that is, has `e(θ) > 0` for (almost) all `θ`". If a feasible contract solving the relaxed
  problem pointwise exists (the hypotheses of `example_23_F_1`), every optimal feasible contract
  `(e, t)` has `e(θ) > 0` for almost every type: an optimal `e(θ)` maximises `v(e) + g(e)J(θ)`
  for almost every `θ`, and `0` never does, because the derivative there is
  `v'(0) + g'(0)J(θ) = v'(0) > 0`. Instance: the uniform example of `example_23_F_1_instance`
  (`footnote_23_48_instance`).
* **Exercise 23.F.1**, parenthetical claim about Example 23.F.1: the first-best effort `e*(θ)`
  with the agent as residual claimant, `t(θ) = v(e*(θ)) - (v(e*(θ̲)) + θ̲g(e*(θ̲))) + ū`, is ex
  post classically efficient, Bayesian incentive compatible and individually rational
  (`exercise_23_F_1_firstBest`); in the uniform instance it is incentive feasible in the full
  sense of `OCFeasible`, while the optimal (interim incentive efficient) contract is not ex post
  efficient at `θ = -2` (`exercise_23_F_1_example`).
-/

namespace MWG.MechanismDesign

open MeasureTheory

/-- **Footnote 48** (MWG, p. 902). Suppose `v'(0) > 0` and `g'(0) = 0`, and a feasible contract
`(e*, t*)` with `U*(θ̲) = ū` solves the relaxed problem pointwise (so it is optimal,
`example_23_F_1`). Then every optimal feasible contract `(e, t)` (expected payoff at least that
of `(e*, t*)`) is interior: `e(θ) > 0` for almost every type `θ`. -/
theorem footnote_23_48 (D : TypeDensity) {v g : ℝ → ℝ} {v0 g0 ubar : ℝ}
    (hv : HasDerivAt v v0 0) (hg : HasDerivAt g g0 0) (hg0 : g0 = 0) (hv0 : 0 < v0)
    {es ts : ℝ → ℝ} (hs : OCFeasible D v g ubar es ts) (hU : ocU g es ts D.lo = ubar)
    (hmax : ∀ θ ∈ Set.Icc D.lo D.hi, OCArgmax (fun x => v x + g x * D.virtualValue θ) (es θ))
    {e t : ℝ → ℝ} (h : OCFeasible D v g ubar e t) (hopt : ocPayoff D v es ts ≤ ocPayoff D v e t) :
    ∀ᵐ θ ∂D.measure, 0 < e θ := by
  have := D.isProbabilityMeasure
  obtain ⟨he, hIC, hIR, hvi, ht, hθg, hgr⟩ := h
  obtain ⟨-, hIC', -, hvi', ht', hθg', hgr'⟩ := hs
  rw [eq_23_F_4 D hIC hvi ht hθg hgr, eq_23_F_4 D hIC' hvi' ht' hθg' hgr', hU] at hopt
  have hlo := hIR D.lo ⟨le_rfl, D.lo_lt_hi.le⟩
  have iE := oc_integrable_vJ D hvi hθg hgr
  have iS := oc_integrable_vJ D hvi' hθg' hgr'
  have hae : ∀ᵐ θ ∂D.measure, θ ∈ Set.Icc D.lo D.hi := mem_ae_iff.2 D.measure_compl_Icc
  have hnn : 0 ≤ᵐ[D.measure] fun θ => (v (es θ) + g (es θ) * D.virtualValue θ) -
      (v (e θ) + g (e θ) * D.virtualValue θ) := by
    filter_upwards [hae] with θ hθ
    exact sub_nonneg.2 ((hmax θ hθ).2 (e θ) (he θ))
  have hint0 : ∫ θ, ((v (es θ) + g (es θ) * D.virtualValue θ) -
      (v (e θ) + g (e θ) * D.virtualValue θ)) ∂D.measure = 0 := by
    rw [integral_sub iS iE]
    have := integral_nonneg_of_ae hnn
    rw [integral_sub iS iE] at this
    linarith
  have hz := (integral_eq_zero_iff_of_nonneg_ae hnn (iS.sub iE)).1 hint0
  filter_upwards [hz, hae] with θ hθ hθm
  simp only [Pi.zero_apply, sub_eq_zero] at hθ
  have hargmax : OCArgmax (fun x => v x + g x * D.virtualValue θ) (e θ) :=
    ⟨he θ, fun x hx => by
      have := (hmax θ hθm).2 x hx
      simp only at this ⊢
      linarith⟩
  have hd : HasDerivAt (fun x => v x + g x * D.virtualValue θ)
      (v0 + g0 * D.virtualValue θ) 0 := hv.add (hg.mul_const _)
  rcases lt_or_eq_of_le (he θ) with hpos | hzero
  · exact hpos
  · exfalso
    rw [← hzero] at hargmax
    exact oc_not_argmax_zero hd (by rw [hg0, zero_mul, add_zero]; exact hv0) hargmax

/-- The uniform instance of Example 23.F.1 solves the relaxed problem pointwise: for `θ ∈ [-2, -1]`,
`e(θ) = 1/(2|θ|)` maximises `v(e) + g(e)J(θ) = 2e - e² + e²(2θ + 1)` over `e ≥ 0`. -/
theorem oc_instance_argmax {θ : ℝ}
    (hθ : θ ∈ Set.Icc (uniformDensity (-2) (-1) (by norm_num)).lo
      (uniformDensity (-2) (-1) (by norm_num)).hi) :
    OCArgmax (fun x => (2 * x - x ^ 2) + x ^ 2 *
      (uniformDensity (-2) (-1) (by norm_num)).virtualValue θ) (1 / (2 * |θ|)) := by
  have hθ' : θ ∈ Set.Icc (-2 : ℝ) (-1) := hθ
  have hθ0 : θ < 0 := by linarith [hθ'.2]
  have hJ : (uniformDensity (-2) (-1) (by norm_num)).virtualValue θ = 2 * θ + 1 := by
    have h := oa_uniform_virtualValue (a := (-2 : ℝ)) (b := -1) (by norm_num) (x := θ) hθ
    exact h.trans (by ring)
  have he : 2 * -θ * (1 / (2 * |θ|)) = 1 := by
    rw [abs_of_neg hθ0]; have := hθ0.ne; field_simp
  refine ⟨by positivity, fun x _ => ?_⟩
  simp only [hJ]
  have key : (2 * (1 / (2 * |θ|)) - (1 / (2 * |θ|)) ^ 2 + (1 / (2 * |θ|)) ^ 2 * (2 * θ + 1)) -
      (2 * x - x ^ 2 + x ^ 2 * (2 * θ + 1)) = 2 * (-θ) * (x - 1 / (2 * |θ|)) ^ 2 := by
    linear_combination (2 * (x - 1 / (2 * |θ|))) * he
  have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (by linarith : (0 : ℝ) ≤ -θ))
    (sq_nonneg (x - 1 / (2 * |θ|)))
  linarith

/-- **Footnote 48** (MWG, p. 902), instance: in the uniform example (types uniform on
`[-2, -1]`, `g(e) = e²`, `v(e) = 2e - e²`, `ū = 0`; `v'(0) = 2 > 0`, `g'(0) = 0`), every optimal
feasible contract has `e(θ) > 0` for almost every type. -/
theorem footnote_23_48_instance {e t : ℝ → ℝ}
    (h : OCFeasible (uniformDensity (-2) (-1) (by norm_num)) (fun e => 2 * e - e ^ 2)
      (fun e => e ^ 2) 0 e t)
    (hopt : ∀ e' t', OCFeasible (uniformDensity (-2) (-1) (by norm_num))
      (fun e => 2 * e - e ^ 2) (fun e => e ^ 2) 0 e' t' →
      ocPayoff (uniformDensity (-2) (-1) (by norm_num)) (fun e => 2 * e - e ^ 2) e' t' ≤
        ocPayoff (uniformDensity (-2) (-1) (by norm_num)) (fun e => 2 * e - e ^ 2) e t) :
    ∀ᵐ θ ∂(uniformDensity (-2) (-1) (by norm_num)).measure, 0 < e θ := by
  obtain ⟨hs, hU, -⟩ := example_23_F_1_instance
  have hv : HasDerivAt (fun e : ℝ => 2 * e - e ^ 2) 2 0 :=
    (((hasDerivAt_id' (0 : ℝ)).const_mul 2).sub (hasDerivAt_pow 2 (0 : ℝ))).congr_deriv
      (by norm_num)
  have hg : HasDerivAt (fun e : ℝ => e ^ 2) 0 0 :=
    (hasDerivAt_pow 2 (0 : ℝ)).congr_deriv (by norm_num)
  exact footnote_23_48 _ hv hg rfl (by norm_num) hs hU (fun θ hθ => oc_instance_argmax hθ) h
    (hopt _ _ hs)

/-! ### Exercise 23.F.1: the first-best contract in Example 23.F.1 -/

/-- **Exercise 23.F.1** (MWG, p. 923), claim about Example 23.F.1. Let `e*(θ)` be the first-best
effort, maximising `v(e) + θg(e)` over `e ≥ 0` for every `θ ∈ [θ̲, θ̄]`, with `g ≥ 0` on
`e ≥ 0`. Make the agent the residual claimant: `t(θ) = v(e*(θ)) - (v(e*(θ̲)) + θ̲g(e*(θ̲))) + ū`.
This social choice function is ex post classically efficient (the total surplus
`(v(e) - t) + (t + θg(e))` is maximal at every type), Bayesian incentive compatible and
individually rational: an ex post classically efficient social choice function is incentive
feasible. -/
theorem exercise_23_F_1_firstBest {v g ef : ℝ → ℝ} {lo hi ubar : ℝ} (hlohi : lo ≤ hi)
    (hg0 : ∀ x, 0 ≤ x → 0 ≤ g x)
    (hfb : ∀ θ ∈ Set.Icc lo hi, OCArgmax (fun x => v x + g x * θ) (ef θ)) :
    let t : ℝ → ℝ := fun θ => v (ef θ) - (v (ef lo) + lo * g (ef lo)) + ubar
    (∀ θ ∈ Set.Icc lo hi, ∀ x, 0 ≤ x → ∀ s : ℝ,
      (v x - s) + (s + θ * g x) ≤ (v (ef θ) - t θ) + (t θ + θ * g (ef θ))) ∧
      LinearIC (fun θ => g (ef θ)) t lo hi ∧ ∀ θ ∈ Set.Icc lo hi, ubar ≤ ocU g ef t θ := by
  intro t
  have hlo : lo ∈ Set.Icc lo hi := ⟨le_rfl, hlohi⟩
  refine ⟨fun θ hθ x hx s => ?_, fun θ hθ θh hθh => ?_, fun θ hθ => ?_⟩
  · have := (hfb θ hθ).2 x hx
    simp only at this
    linarith
  · have := (hfb θ hθ).2 (ef θh) (hfb θh hθh).1
    simp only [t] at this ⊢
    linarith
  · have h1 := (hfb θ hθ).2 (ef lo) (hfb lo hlo).1
    have h2 : lo * g (ef lo) ≤ θ * g (ef lo) :=
      mul_le_mul_of_nonneg_right hθ.1 (hg0 _ (hfb lo hlo).1)
    simp only [ocU, t] at h1 ⊢
    linarith

/-- **Exercise 23.F.1** (MWG, p. 923), the parenthetical claim in the uniform instance of
Example 23.F.1 (types uniform on `[-2, -1]`, `g(e) = e²`, `v(e) = 2e - e²`, `ū = 0`): the
first-best contract `e*(θ) = 1/(1 - θ)` (written `1/(1 + |θ|)`) with the agent as residual
claimant is incentive feasible (`OCFeasible`) and ex post classically efficient, while the
optimal contract `e(θ) = 1/(2|θ|)` derived in the example is not ex post efficient: at `θ = -2`
its total surplus is strictly below the first best. -/
theorem exercise_23_F_1_example :
    let D := uniformDensity (-2) (-1) (by norm_num)
    let v : ℝ → ℝ := fun e => 2 * e - e ^ 2
    let g : ℝ → ℝ := fun e => e ^ 2
    let ef : ℝ → ℝ := fun θ => 1 / (1 + |θ|)
    let tf : ℝ → ℝ := fun θ => v (ef θ) - (v (ef D.lo) + D.lo * g (ef D.lo))
    OCFeasible D v g 0 ef tf ∧
      (∀ θ ∈ Set.Icc D.lo D.hi, ∀ x, 0 ≤ x → v x + θ * g x ≤ v (ef θ) + θ * g (ef θ)) ∧
      v (1 / (2 * |(-2 : ℝ)|)) + (-2) * g (1 / (2 * |(-2 : ℝ)|)) <
        v (ef (-2)) + (-2) * g (ef (-2))
  := by
  intro D v g ef tf
  have hlo : D.lo = -2 := rfl
  have hhi : D.hi = -1 := rfl
  obtain ⟨-, -, -, hfb, -, -⟩ := example_23_F_1_instance
  have hefeq : ∀ θ ∈ Set.Icc D.lo D.hi, ef θ = 1 / (1 - θ) := by
    intro θ hθ
    rw [hlo, hhi] at hθ
    simp only [ef, abs_of_neg (by linarith [hθ.2] : θ < 0), sub_eq_add_neg]
  have hfb' : ∀ θ ∈ Set.Icc D.lo D.hi, OCArgmax (fun x => v x + g x * θ) (ef θ) :=
    fun θ hθ => by rw [hefeq θ hθ]; exact hfb θ hθ
  have hef : ∀ θ ∈ Set.Icc D.lo D.hi, 1 / 3 ≤ ef θ ∧ ef θ ≤ 1 / 2 := by
    intro θ hθ
    rw [hefeq θ hθ]
    rw [hlo, hhi] at hθ
    refine ⟨?_, ?_⟩
    · rw [le_div_iff₀ (by linarith [hθ.2])]; linarith [hθ.1]
    · rw [div_le_iff₀ (by linarith [hθ.2])]; linarith [hθ.2]
  have hefm : Measurable ef :=
    measurable_const.div (measurable_const.add continuous_abs.measurable)
  obtain ⟨_, hIC, hIR⟩ := exercise_23_F_1_firstBest (v := v) (g := g) (ubar := 0)
    D.lo_lt_hi.le (fun x _ => sq_nonneg x) hfb'
  have htf : tf = fun θ => v (ef θ) - (v (ef D.lo) + D.lo * g (ef D.lo)) + 0 := by
    funext θ; simp only [tf, add_zero]
  refine ⟨⟨fun θ => ?_, by rw [htf]; exact hIC, fun θ hθ => by rw [htf]; exact hIR θ hθ,
    oc_integrable_of_bound D ((measurable_const.mul hefm).sub (hefm.pow_const 2)) 2
      fun θ hθ => ?_,
    oc_integrable_of_bound D (((measurable_const.mul hefm).sub (hefm.pow_const 2)).sub
      measurable_const) 4 fun θ hθ => ?_,
    oc_integrable_of_bound D (measurable_id.mul (hefm.pow_const 2)) 2 fun θ hθ => ?_,
    oc_integrable_of_bound D ((hefm.pow_const 2).mul ((measurable_const.sub
      D.continuous_cdf.measurable).div D.measurable_dens)) 1 fun θ hθ => ?_⟩,
    fun θ hθ x hx => ?_, ?_⟩
  · simp only [ef]; positivity
  · obtain ⟨h1, h2⟩ := hef θ hθ
    simp only [v]
    rw [abs_le]; constructor <;> nlinarith
  · obtain ⟨h1, h2⟩ := hef θ hθ
    have h3 := hef D.lo ⟨le_rfl, D.lo_lt_hi.le⟩
    simp only [tf, v, g]
    rw [abs_le]; constructor <;> nlinarith [h3.1, h3.2]
  · obtain ⟨h1, h2⟩ := hef θ hθ
    have := hθ; rw [hlo, hhi] at this
    simp only [g]
    rw [abs_le]; constructor <;> nlinarith [this.1, this.2]
  · obtain ⟨h1, h2⟩ := hef θ hθ
    have := hθ; rw [hlo, hhi] at this
    have hd : D.dens θ = ((-1) - (-2) : ℝ)⁻¹ := by
      change (Set.Icc (-2 : ℝ) (-1)).indicator (fun _ => ((-1) - (-2) : ℝ)⁻¹) θ = _
      exact Set.indicator_of_mem hθ _
    have hc := oa_uniform_cdf (a := (-2 : ℝ)) (b := -1) (by norm_num) (x := θ) hθ
    have hr : (1 - D.cdf θ) / D.dens θ = -1 - θ := by
      change (1 - (uniformDensity (-2) (-1) (by norm_num)).cdf θ) / D.dens θ = _
      rw [hc, hd]; norm_num; ring
    simp only [g]
    rw [hr, abs_le]; constructor <;> nlinarith [this.1, this.2]
  · have := (hfb' θ hθ).2 x hx
    simp only at this
    linarith
  · simp only [v, g, ef]
    norm_num

end MWG.MechanismDesign
