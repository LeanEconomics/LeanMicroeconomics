/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.Tatonnement
import MWGPositiveEquilibriumTheory.LinearActivities
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Quantity tâtonnement (MWG Section 17.H, pp. 625-626)

A single production set `Y`; at each moment the production vector `y(t) ∈ Y` is given and prices
are the short-run equilibrium prices `p(y)`. With a single consumer with differentiable utility
`u` and endowment `ω`, the short-run equilibrium price is proportional to the vector of marginal
utilities `∇u(y + ω)` (p. 626), which is what `p(y)` is taken to be here (`margUtil`).

* **Definition 17.H.1** (`IsAdmissible`): `y(t) ∈ Y`, `p(y(t))·dy/dt ≥ 0`, with equality only if
  `y(t)` maximizes profit at `p(y(t))`. The long-run equilibrium maximizes `u(y + ω)` on `Y`
  (`IsLongRunEqm`).
* **Proposition 17.H.2**, the book's argument (`proposition_17_H_2_utility`): along an admissible
  trajectory, `d u(y(t) + ω)/dt = ∇u·dy/dt ≥ 0`, with equality only at the long-run equilibrium
  (for concave `u`, by the gradient inequality `concave_le_fderiv`).
* **Proposition 17.H.2 is false as printed** (`proposition_17_H_2_counter`): with
  `u = log x₁ + log x₂` (strictly concave), `ω = (1, 1)` and a compact convex `Y`, an admissible
  trajectory with `p(y(t))·dy/dt > 0` throughout converges to `(1/4, -1/4)`, not to the unique
  equilibrium `0` (the dynamics are "so sluggish that we never reach the equilibrium", as the book
  warns). Corrected statement (`proposition_17_H_2`): with `Y` compact and convex, `u` continuous
  and strictly concave, and an admissible trajectory that is *uniformly* admissible
  (`p(y(t))·dy/dt ≥ δ(ε) > 0` whenever `‖y(t) - ȳ‖ ≥ ε`), `y(t) → ȳ`. Instance:
  `proposition_17_H_2_instance`.
-/

namespace MWG.PositiveEquilibriumTheory

open Filter Topology Set

variable {L : ℕ}

/-- The vector of marginal utilities `∇u(x) = (∂u/∂xₗ(x))ₗ` (`gradVec` of the derivative). -/
noncomputable def margUtil (u : (Fin L → ℝ) → ℝ) (x : Fin L → ℝ) : Fin L → ℝ :=
  gradVec (fderiv ℝ u x)

/-- `Du(x) v = ∇u(x)·v`. -/
theorem fderiv_eq_margUtil_dot (u : (Fin L → ℝ) → ℝ) (x v : Fin L → ℝ) :
    fderiv ℝ u x v = margUtil u x ⬝ᵥ v := by
  rw [margUtil, dotProduct_comm, dotProduct_gradVec]

/-- **Definition 17.H.1** (MWG, p. 625). The differentiable trajectory `y(t) ∈ Y` (derivative
`y'(t)`, one-sided at `t = 0`) is *admissible* for the short-run price function `p(·)`:
`p(y(t))·y'(t) ≥ 0`, with equality only if `y(t)` is profit maximizing for `p(y(t))`. -/
def IsAdmissible (Y : Set (Fin L → ℝ)) (price : (Fin L → ℝ) → Fin L → ℝ)
    (y y' : ℝ → Fin L → ℝ) : Prop :=
  ∀ t, 0 ≤ t → y t ∈ Y ∧ HasDerivWithinAt y (y' t) (Ici 0) t ∧ 0 ≤ price (y t) ⬝ᵥ y' t ∧
    (price (y t) ⬝ᵥ y' t = 0 → ∀ y₁ ∈ Y, price (y t) ⬝ᵥ y₁ ≤ price (y t) ⬝ᵥ y t)

/-- **Section 17.H** (MWG, p. 626). The long-run equilibrium of the one-consumer economy: `ȳ ∈ Y`
maximizes `u(y + ω)` on `Y` (the one-consumer, one-firm example of Section 15.C). -/
def IsLongRunEqm (u : (Fin L → ℝ) → ℝ) (ω : Fin L → ℝ) (Y : Set (Fin L → ℝ))
    (yb : Fin L → ℝ) : Prop :=
  yb ∈ Y ∧ ∀ y ∈ Y, u (y + ω) ≤ u (yb + ω)

/-- The gradient inequality for a concave differentiable function:
`u(x') ≤ u(x) + Du(x)(x' - x)` on a convex set. -/
theorem concave_le_fderiv {X : Set (Fin L → ℝ)} {u : (Fin L → ℝ) → ℝ} (hX : Convex ℝ X)
    (hu : ConcaveOn ℝ X u) {x x' : Fin L → ℝ} (hx : x ∈ X) (hx' : x' ∈ X)
    (hd : DifferentiableAt ℝ u x) : u x' ≤ u x + fderiv ℝ u x (x' - x) := by
  set g : ℝ → ℝ := fun s => u (AffineMap.lineMap x x' s) with hg
  have hsub : Icc (0 : ℝ) 1 ⊆ (AffineMap.lineMap x x') ⁻¹' X := fun s hs =>
    hX.lineMap_mem hx hx' hs
  have hconc : ConcaveOn ℝ (Icc 0 1) g :=
    (hu.comp_affineMap (AffineMap.lineMap x x')).subset hsub (convex_Icc 0 1)
  have hderiv : HasDerivAt g (fderiv ℝ u x (x' - x)) 0 := by
    have h1 : HasDerivAt (AffineMap.lineMap x x' : ℝ → Fin L → ℝ) (x' - x) 0 :=
      AffineMap.hasDerivAt_lineMap
    have h2 : HasFDerivAt u (fderiv ℝ u x) (AffineMap.lineMap x x' (0 : ℝ)) := by
      rw [AffineMap.lineMap_apply_zero]; exact hd.hasFDerivAt
    exact h2.comp_hasDerivAt 0 h1
  have h := hconc.neg.le_slope_of_hasDerivAt (x := 0) (y := 1) ⟨le_rfl, zero_le_one⟩
    ⟨zero_le_one, le_rfl⟩ zero_lt_one hderiv.neg
  simp only [slope_def_field, Pi.neg_apply, sub_zero, div_one, hg,
    AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] at h
  linarith

/-- Along a differentiable trajectory, `d u(y(t) + ω)/dt = ∇u(y(t) + ω)·y'(t)`. -/
theorem qa_hasDeriv_utility {u : (Fin L → ℝ) → ℝ} {ω : Fin L → ℝ} {y y' : ℝ → Fin L → ℝ}
    {t : ℝ} (hd : DifferentiableAt ℝ u (y t + ω)) (hy : HasDerivWithinAt y (y' t) (Ici 0) t) :
    HasDerivWithinAt (fun s => u (y s + ω)) (margUtil u (y t + ω) ⬝ᵥ y' t) (Ici 0) t := by
  have h := hd.hasFDerivAt.comp_hasDerivWithinAt t (hy.add_const ω)
  rw [fderiv_eq_margUtil_dot] at h
  exact h

/-- **Proposition 17.H.2**, the argument of the proof (MWG, p. 626). For a single consumer with
concave differentiable utility `u` and short-run prices `p(y) = ∇u(y + ω)`, utility is
nondecreasing along every admissible trajectory, and `du/dt = p(y(t))·dy/dt = 0` only when `y(t)`
is the long-run equilibrium. -/
theorem proposition_17_H_2_utility {X Y : Set (Fin L → ℝ)} {u : (Fin L → ℝ) → ℝ}
    {ω : Fin L → ℝ} (hX : Convex ℝ X) (hu : ConcaveOn ℝ X u) (hYX : ∀ y ∈ Y, y + ω ∈ X)
    {y y' : ℝ → Fin L → ℝ} (hadm : IsAdmissible Y (fun y => margUtil u (y + ω)) y y')
    (hd : ∀ t, 0 ≤ t → DifferentiableAt ℝ u (y t + ω)) :
    MonotoneOn (fun t => u (y t + ω)) (Ici 0) ∧
      ∀ t, 0 ≤ t → margUtil u (y t + ω) ⬝ᵥ y' t = 0 → IsLongRunEqm u ω Y (y t) := by
  refine ⟨tat_monotoneOn (fun t ht => qa_hasDeriv_utility (hd t ht) (hadm t ht).2.1)
    fun t ht => (hadm t ht).2.2.1, fun t ht h0 => ⟨(hadm t ht).1, fun y₁ hy₁ => ?_⟩⟩
  have hmax := (hadm t ht).2.2.2 h0 y₁ hy₁
  have hgrad := concave_le_fderiv hX hu (hYX _ (hadm t ht).1) (hYX _ hy₁) (hd t ht)
  rw [fderiv_eq_margUtil_dot, show y₁ + ω - (y t + ω) = y₁ - y t by abel,
    dotProduct_sub] at hgrad
  linarith


/-- With strictly concave `u` and convex `Y`, the long-run equilibrium is unique: any `y₁ ∈ Y`
with `u(y₁ + ω) ≥ u(ȳ + ω)` is `ȳ`. -/
theorem qa_unique {X Y : Set (Fin L → ℝ)} {u : (Fin L → ℝ) → ℝ} {ω : Fin L → ℝ}
    (hu : StrictConcaveOn ℝ X u) (hYc : Convex ℝ Y) (hYX : ∀ y ∈ Y, y + ω ∈ X)
    {yb : Fin L → ℝ} (hyb : IsLongRunEqm u ω Y yb) {y₁ : Fin L → ℝ} (hy₁ : y₁ ∈ Y)
    (hge : u (yb + ω) ≤ u (y₁ + ω)) : y₁ = yb := by
  by_contra hne
  have hmid : (1 / 2 : ℝ) • y₁ + (1 / 2 : ℝ) • yb ∈ Y :=
    hYc hy₁ hyb.1 (by norm_num) (by norm_num) (by norm_num)
  have hne' : y₁ + ω ≠ yb + ω := fun h => hne (add_right_cancel h)
  have hs := hu.2 (hYX _ hy₁) (hYX _ hyb.1) hne' (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  have heq : (1 / 2 : ℝ) • (y₁ + ω) + (1 / 2 : ℝ) • (yb + ω) =
      ((1 / 2 : ℝ) • y₁ + (1 / 2 : ℝ) • yb) + ω := by
    rw [smul_add, smul_add]
    ext l
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [heq] at hs
  have := hyb.2 _ hmid
  simp only [smul_eq_mul] at hs
  linarith

/-- **Proposition 17.H.2**, corrected (MWG, p. 626). One consumer with continuous, strictly
concave utility `u` on a convex `X`, a compact convex production set `Y` (`Y + ω ⊆ X`), long-run
equilibrium `ȳ`, and short-run prices `p(y) = ∇u(y + ω)`. If the trajectory is admissible and
*uniformly* so (for every `ε > 0` there is `δ > 0` with `p(y(t))·dy/dt ≥ δ` whenever
`‖y(t) - ȳ‖ ≥ ε`; the book's "strengthen slightly the concept of an admissible trajectory"),
then `y(t) → ȳ`. -/
theorem proposition_17_H_2 {X Y : Set (Fin L → ℝ)} {u : (Fin L → ℝ) → ℝ} {ω : Fin L → ℝ}
    (hu : StrictConcaveOn ℝ X u) (hucont : ContinuousOn u X) (hYc : Convex ℝ Y)
    (hYk : IsCompact Y) (hYX : ∀ y ∈ Y, y + ω ∈ X) {yb : Fin L → ℝ}
    (hyb : IsLongRunEqm u ω Y yb) {y y' : ℝ → Fin L → ℝ}
    (hadm : IsAdmissible Y (fun y => margUtil u (y + ω)) y y')
    (hd : ∀ t, 0 ≤ t → DifferentiableAt ℝ u (y t + ω))
    (hunif : ∀ ε > 0, ∃ δ > 0, ∀ t, 0 ≤ t → ε ≤ ‖y t - yb‖ →
      δ ≤ margUtil u (y t + ω) ⬝ᵥ y' t) :
    Tendsto y atTop (𝓝 yb) := by
  set ub := u (yb + ω) with hub
  have hg : ContinuousOn (fun y => u (y + ω)) Y :=
    hucont.comp (continuous_id.add continuous_const).continuousOn fun y hy => hYX y hy
  have hU := (proposition_17_H_2_utility hu.1 hu.concaveOn hYX hadm hd).1
  have hUle : ∀ t, 0 ≤ t → u (y t + ω) ≤ ub := fun t ht => hyb.2 _ (hadm t ht).1
  -- upper contour sets shrink to `ȳ`
  have hshrink : ∀ ε > 0, ∃ η > 0, ∀ y₁ ∈ Y, ub - η < u (y₁ + ω) → ‖y₁ - yb‖ < ε := by
    intro ε hε
    set K := Y ∩ {y₁ | ε ≤ ‖y₁ - yb‖} with hK
    have hKk : IsCompact K := hYk.inter_right
      (isClosed_le continuous_const (continuous_id.sub continuous_const).norm)
    by_cases hKne : K.Nonempty
    · obtain ⟨y₁, hy₁K, hmax⟩ := hKk.exists_isMaxOn hKne (hg.mono inter_subset_left)
      have hlt : u (y₁ + ω) < ub := by
        refine lt_of_le_of_ne (hyb.2 _ hy₁K.1) fun h => ?_
        have := qa_unique hu hYc hYX hyb hy₁K.1 h.ge
        have h2 := hy₁K.2
        simp only [Set.mem_ofPred_eq, this, sub_self, norm_zero] at h2
        linarith
      refine ⟨ub - u (y₁ + ω), by linarith, fun y₂ hy₂ hlt2 => ?_⟩
      by_contra hcon
      push Not at hcon
      have := hmax ⟨hy₂, hcon⟩
      simp only [Set.mem_ofPred_eq] at this
      linarith
    · refine ⟨1, one_pos, fun y₂ hy₂ _ => ?_⟩
      by_contra hcon
      push Not at hcon
      exact hKne ⟨y₂, hy₂, hcon⟩
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  obtain ⟨η, hη, hηK⟩ := hshrink ε hε
  obtain ⟨ρ, hρ, hρK⟩ := Metric.continuousWithinAt_iff.1 (hg yb hyb.1) η hη
  obtain ⟨δ, hδ, hδK⟩ := hunif ρ hρ
  have hreach : ∃ t0, 0 ≤ t0 ∧ ‖y t0 - yb‖ < ρ := by
    by_contra hcon
    push Not at hcon
    have hmono := tat_monotoneOn (F := fun t => u (y t + ω) - δ * t)
      (F' := fun t => margUtil u (y t + ω) ⬝ᵥ y' t - δ)
      (fun t ht => by
        have := (qa_hasDeriv_utility (hd t ht) (hadm t ht).2.1).fun_sub
          ((hasDerivWithinAt_id t (Ici 0)).const_mul δ)
        simpa using this)
      (fun t ht => by linarith [hδK t ht (hcon t ht)])
    set T := (ub - u (y 0 + ω)) / δ + 1 with hT
    have hU0 := hUle 0 le_rfl
    have hT0 : 0 ≤ T := by positivity
    have h1 := hmono (Set.mem_Ici.2 le_rfl) hT0 hT0
    simp only [mul_zero, sub_zero] at h1
    have h2 : δ * T = ub - u (y 0 + ω) + δ := by rw [hT]; field_simp
    have := hUle T hT0
    linarith
  obtain ⟨t0, ht0, hnear⟩ := hreach
  have hut0 : ub - η < u (y t0 + ω) := by
    have := hρK (hadm t0 ht0).1 (by rwa [dist_eq_norm])
    rw [Real.dist_eq] at this
    linarith [neg_abs_le (u (y t0 + ω) - ub)]
  refine ⟨t0, fun t ht => ?_⟩
  have h1 : u (y t0 + ω) ≤ u (y t + ω) := hU ht0 (ht0.trans ht) ht
  rw [dist_eq_norm]
  exact hηK _ (hadm t (ht0.trans ht)).1 (by linarith)

/-! ### The counterexample to Proposition 17.H.2 as printed -/

/-- `u(x) = log x₁ + log x₂`. -/
noncomputable def qaU (x : Fin 2 → ℝ) : ℝ := Real.log (x 0) + Real.log (x 1)

/-- The production set `Y = {y : y₁ + y₂ ≤ 0, y₁ ≥ -1/2, y₂ ≥ -1/2}` (compact, convex). -/
def qaY : Set (Fin 2 → ℝ) := {y | y 0 + y 1 ≤ 0 ∧ -1 / 2 ≤ y 0 ∧ -1 / 2 ≤ y 1}

/-- The endowment `ω = (1, 1)`. -/
def qaω : Fin 2 → ℝ := fun _ => 1

theorem qaU_hasFDerivAt {x : Fin 2 → ℝ} (hx : x ∈ posOrthant 2) :
    HasFDerivAt qaU ((x 0)⁻¹ • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0 +
      (x 1)⁻¹ • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1) x :=
  ((hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 2 => ℝ) 0 x).log (hx 0).ne').add
    ((hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 2 => ℝ) 1 x).log (hx 1).ne')

theorem qaU_margUtil {x : Fin 2 → ℝ} (hx : x ∈ posOrthant 2) :
    margUtil qaU x = fun l => (x l)⁻¹ := by
  funext l
  simp only [margUtil, gradVec, (qaU_hasFDerivAt hx).fderiv]
  fin_cases l <;> simp

theorem qaU_strictConcave : StrictConcaveOn ℝ (posOrthant 2) qaU := by
  refine ⟨convex_posOrthant 2, fun x hx y hy hxy a b ha hb hab => ?_⟩
  have hl : ∀ l : Fin 2, a • Real.log (x l) + b • Real.log (y l) ≤
      Real.log ((a • x + b • y) l) := fun l =>
    strictConcaveOn_log_Ioi.concaveOn.2 (hx l) (hy l) ha.le hb.le hab
  have hne : x 0 ≠ y 0 ∨ x 1 ≠ y 1 := by
    by_contra h
    push Not at h
    exact hxy (funext fun l => by fin_cases l; exacts [h.1, h.2])
  simp only [qaU, smul_eq_mul] at hl ⊢
  rcases hne with h | h
  · have hs := strictConcaveOn_log_Ioi.2 (hx 0) (hy 0) h ha hb hab
    have := hl 1
    simp only [smul_eq_mul, Pi.add_apply, Pi.smul_apply] at hs this ⊢
    linarith
  · have hs := strictConcaveOn_log_Ioi.2 (hx 1) (hy 1) h ha hb hab
    have := hl 0
    simp only [smul_eq_mul, Pi.add_apply, Pi.smul_apply] at hs this ⊢
    linarith

theorem qaU_continuousOn : ContinuousOn qaU (posOrthant 2) :=
  ((continuous_apply 0).continuousOn.log fun _ hx => (hx 0).ne').add
    ((continuous_apply 1).continuousOn.log fun _ hx => (hx 1).ne')

theorem qaY_props : Convex ℝ qaY ∧ IsCompact qaY ∧ ∀ y ∈ qaY, y + qaω ∈ posOrthant 2 := by
  refine ⟨?_, ?_, fun y hy l => ?_⟩
  · intro x hx y hy a b ha hb hab
    simp only [qaY, Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hx hy ⊢
    refine ⟨by nlinarith, by nlinarith, by nlinarith⟩
  · have hcl : IsClosed qaY := by
      refine IsClosed.inter (isClosed_le ((continuous_apply 0).add (continuous_apply 1))
        continuous_const) (IsClosed.inter ?_ ?_)
      · exact isClosed_le continuous_const (continuous_apply 0)
      · exact isClosed_le continuous_const (continuous_apply 1)
    refine (isCompact_Icc (a := fun _ : Fin 2 => (-1 / 2 : ℝ))
      (b := fun _ => 1 / 2)).of_isClosed_subset hcl fun y hy => ⟨fun l => ?_, fun l => ?_⟩
    · fin_cases l
      · exact hy.2.1
      · exact hy.2.2
    · obtain ⟨h1, h2, h3⟩ := hy
      fin_cases l
      · change y 0 ≤ 1 / 2; linarith
      · change y 1 ≤ 1 / 2; linarith
  · obtain ⟨_, h2, h3⟩ := hy
    fin_cases l
    · change 0 < y 0 + 1; linarith
    · change 0 < y 1 + 1; linarith

/-- In the counterexample economy, `ȳ = 0` is the unique long-run equilibrium. -/
theorem qa_eqm : IsLongRunEqm qaU qaω qaY 0 ∧ ∀ yb, IsLongRunEqm qaU qaω qaY yb → yb = 0 := by
  have h0 : IsLongRunEqm qaU qaω qaY 0 := by
    refine ⟨⟨by norm_num, by norm_num, by norm_num⟩, fun y hy => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hy
    have hr : qaU (0 + qaω) = 0 := by simp [qaU, qaω]
    have hl : qaU (y + qaω) = Real.log ((y 0 + 1) * (y 1 + 1)) := by
      simp only [qaU, qaω, Pi.add_apply]
      rw [Real.log_mul (show y 0 + 1 ≠ 0 by linarith) (show y 1 + 1 ≠ 0 by linarith)]
    rw [hr, hl]
    refine Real.log_nonpos (by nlinarith) ?_
    nlinarith [sq_nonneg (y 0 - y 1), mul_nonneg (show 0 ≤ -(y 0 + y 1) by linarith)
      (show 0 ≤ y 0 + y 1 + 4 by linarith)]
  refine ⟨h0, fun yb hyb => ?_⟩
  exact qa_unique qaU_strictConcave qaY_props.1 qaY_props.2.2 h0 hyb.1 (hyb.2 0 h0.1)

/-- The trajectory of the counterexample: `y(t) = (1/4 + e^{-t}/4, -1/4 - e^{-t}/4)`. -/
noncomputable def qaPath (t : ℝ) : Fin 2 → ℝ :=
  ![1 / 4 + Real.exp (-t) / 4, -(1 / 4) - Real.exp (-t) / 4]

/-- Its derivative `y'(t) = (-e^{-t}/4, e^{-t}/4)`. -/
noncomputable def qaPath' (t : ℝ) : Fin 2 → ℝ := ![-(Real.exp (-t) / 4), Real.exp (-t) / 4]

theorem qaPath_hasDerivAt (t : ℝ) : HasDerivAt qaPath (qaPath' t) t := by
  have he : HasDerivAt (fun s => Real.exp (-s)) (-Real.exp (-t)) t := by
    simpa using (hasDerivAt_neg t).exp
  refine hasDerivAt_pi.2 fun l => ?_
  fin_cases l
  · change HasDerivAt (fun s => 1 / 4 + Real.exp (-s) / 4) (-(Real.exp (-t) / 4)) t
    convert (he.div_const 4).const_add (1 / 4) using 1
    ring
  · change HasDerivAt (fun s => -(1 / 4) - Real.exp (-s) / 4) (Real.exp (-t) / 4) t
    convert (he.div_const 4).const_sub (-(1 / 4)) using 1
    ring

/-- **Proposition 17.H.2 is false as printed** (MWG, p. 626). In the economy with the strictly
concave utility `u = log x₁ + log x₂`, `ω = (1, 1)` and the compact convex production set `qaY`,
`ȳ = 0` is the unique long-run equilibrium, the trajectory `qaPath` is admissible with
`p(y(t))·dy/dt > 0` at every `t`, yet `y(t) → (1/4, -1/4) ≠ 0`. -/
theorem proposition_17_H_2_counter :
    StrictConcaveOn ℝ (posOrthant 2) qaU ∧ Convex ℝ qaY ∧ IsCompact qaY ∧
      (∀ y ∈ qaY, y + qaω ∈ posOrthant 2) ∧ IsLongRunEqm qaU qaω qaY 0 ∧
      (∀ yb, IsLongRunEqm qaU qaω qaY yb → yb = 0) ∧
      IsAdmissible qaY (fun y => margUtil qaU (y + qaω)) qaPath qaPath' ∧
      (∀ t, 0 ≤ t → 0 < margUtil qaU (qaPath t + qaω) ⬝ᵥ qaPath' t) ∧
      Tendsto qaPath atTop (𝓝 ![1 / 4, -(1 / 4)]) ∧ ¬ Tendsto qaPath atTop (𝓝 0) := by
  have hin : ∀ t, 0 ≤ t → qaPath t ∈ qaY := by
    intro t ht
    have he := Real.exp_pos (-t)
    have he1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    refine ⟨?_, ?_, ?_⟩ <;> simp [qaPath] <;> linarith
  have hpos : ∀ t, 0 ≤ t → 0 < margUtil qaU (qaPath t + qaω) ⬝ᵥ qaPath' t := by
    intro t ht
    have he := Real.exp_pos (-t)
    have he1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    rw [qaU_margUtil (qaY_props.2.2 _ (hin t ht))]
    simp only [dotProduct, Fin.sum_univ_two, qaPath, qaPath', qaω, Pi.add_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    have h2 : 0 < -(1 / 4) - Real.exp (-t) / 4 + 1 := by linarith
    have hx : (1 / 4 + Real.exp (-t) / 4 + 1)⁻¹ < (-(1 / 4) - Real.exp (-t) / 4 + 1)⁻¹ :=
      inv_strictAnti₀ h2 (by linarith)
    have := mul_lt_mul_of_pos_left hx (by positivity : (0 : ℝ) < Real.exp (-t) / 4)
    linarith
  have hlim : Tendsto qaPath atTop (𝓝 ![1 / 4, -(1 / 4)]) := by
    have he : Tendsto (fun t : ℝ => Real.exp (-t)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
    refine tendsto_pi_nhds.2 fun l => ?_
    fin_cases l
    · change Tendsto (fun s => 1 / 4 + Real.exp (-s) / 4) atTop (𝓝 (1 / 4))
      have := (he.div_const 4).const_add (1 / 4)
      rwa [zero_div, add_zero] at this
    · change Tendsto (fun s => -(1 / 4) - Real.exp (-s) / 4) atTop (𝓝 (-(1 / 4)))
      have := (he.div_const 4).const_sub (-(1 / 4))
      rwa [zero_div, sub_zero] at this
  refine ⟨qaU_strictConcave, qaY_props.1, qaY_props.2.1, qaY_props.2.2, qa_eqm.1, qa_eqm.2,
    fun t ht => ⟨hin t ht, (qaPath_hasDerivAt t).hasDerivWithinAt, (hpos t ht).le,
      fun h => absurd h (hpos t ht).ne'⟩, hpos, hlim, fun h0 => ?_⟩
  have := tendsto_nhds_unique hlim h0
  have := congrFun this 0
  norm_num at this

/-- The trajectory of the instance: `y(t) = (e^{-t}/2, -e^{-t}/2)`. -/
noncomputable def qaPathB (t : ℝ) : Fin 2 → ℝ := ![Real.exp (-t) / 2, -(Real.exp (-t) / 2)]

/-- Its derivative. -/
noncomputable def qaPathB' (t : ℝ) : Fin 2 → ℝ := ![-(Real.exp (-t) / 2), Real.exp (-t) / 2]

/-- **Proposition 17.H.2** (corrected), instance: in the economy of the counterexample, the
trajectory `y(t) = (e^{-t}/2, -e^{-t}/2)` is uniformly admissible, so it converges to `ȳ = 0`. -/
theorem proposition_17_H_2_instance :
    IsAdmissible qaY (fun y => margUtil qaU (y + qaω)) qaPathB qaPathB' ∧
      Tendsto qaPathB atTop (𝓝 0) := by
  have he' : ∀ t : ℝ, HasDerivAt (fun s => Real.exp (-s)) (-Real.exp (-t)) t := fun t => by
    simpa using (hasDerivAt_neg t).exp
  have hd : ∀ t, HasDerivAt qaPathB (qaPathB' t) t := fun t => by
    refine hasDerivAt_pi.2 fun l => ?_
    fin_cases l
    · change HasDerivAt (fun s => Real.exp (-s) / 2) (-(Real.exp (-t) / 2)) t
      convert (he' t).div_const 2 using 1
      ring
    · change HasDerivAt (fun s => -(Real.exp (-s) / 2)) (Real.exp (-t) / 2) t
      convert ((he' t).div_const 2).fun_neg using 1
      ring
  have hin : ∀ t, 0 ≤ t → qaPathB t ∈ qaY := by
    intro t ht
    have he := Real.exp_pos (-t)
    have he1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    refine ⟨?_, ?_, ?_⟩ <;> simp [qaPathB] <;> linarith
  have hval : ∀ t, 0 ≤ t → Real.exp (-t) ^ 2 / 2 ≤
      margUtil qaU (qaPathB t + qaω) ⬝ᵥ qaPathB' t := by
    intro t ht
    have he := Real.exp_pos (-t)
    have he1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    rw [qaU_margUtil (qaY_props.2.2 _ (hin t ht))]
    simp only [dotProduct, Fin.sum_univ_two, qaPathB, qaPathB', qaω, Pi.add_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    set e := Real.exp (-t) with he_def
    have h1 : 0 < e / 2 + 1 := by linarith
    have h2 : 0 < -(e / 2) + 1 := by linarith
    have key : e ≤ (-(e / 2) + 1)⁻¹ - (e / 2 + 1)⁻¹ := by
      rw [show (-(e / 2) + 1)⁻¹ - (e / 2 + 1)⁻¹ = e / ((e / 2 + 1) * (-(e / 2) + 1)) by
        rw [inv_sub_inv h2.ne' h1.ne']; congr 1 <;> ring]
      rw [le_div_iff₀ (by positivity)]
      nlinarith [pow_pos he 3]
    have := mul_le_mul_of_nonneg_left key (by positivity : (0 : ℝ) ≤ e / 2)
    nlinarith
  have hadm : IsAdmissible qaY (fun y => margUtil qaU (y + qaω)) qaPathB qaPathB' :=
    fun t ht => ⟨hin t ht, (hd t).hasDerivWithinAt,
      le_trans (by positivity) (hval t ht), fun h => absurd h
        (ne_of_gt (lt_of_lt_of_le (by have := Real.exp_pos (-t); positivity) (hval t ht)))⟩
  refine ⟨hadm, proposition_17_H_2 qaU_strictConcave qaU_continuousOn qaY_props.1
    qaY_props.2.1 qaY_props.2.2 qa_eqm.1 hadm
    (fun t ht => (qaU_hasFDerivAt (qaY_props.2.2 _ (hin t ht))).differentiableAt) ?_⟩
  intro ε hε
  refine ⟨2 * ε ^ 2, by positivity, fun t ht hεt => ?_⟩
  have hnorm : ‖qaPathB t - 0‖ ≤ Real.exp (-t) / 2 := by
    rw [sub_zero]
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun l => ?_
    fin_cases l <;> simp [qaPathB, abs_of_pos (Real.exp_pos (-t))]
  have h1 : 2 * ε ≤ Real.exp (-t) := by linarith
  have h2 : (2 * ε) ^ 2 ≤ Real.exp (-t) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
  have := hval t ht
  nlinarith

end MWG.PositiveEquilibriumTheory
