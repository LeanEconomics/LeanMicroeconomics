/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.IntegrabilityPDE
import Mathlib.Analysis.ODE.ExistUnique

/-!
# Integrability: the expenditure function is recovered uniquely

MWG, Section 3.H, pp. 78-80. "If `e(p₁)` solves (3.H.1) for `e(p₁⁰) = w⁰`, then `e(p₁)` is the
expenditure function associated with the level of utility `u⁰`" (p. 78), and its analogue for
(3.H.2) (p. 80).

* `pde_solution_unique`: for a continuously differentiable demand function on
  `{p ≫ 0, w > 0}`, two positive solutions of (3.H.2) that agree at one price vector agree on
  all of `p ≫ 0` (along each segment they solve the same ordinary differential equation, whose
  right side is Lipschitz in `w` on compact sets; Gronwall uniqueness).
* `expenditure_solvesPDE`: the expenditure function of a continuous, strictly quasiconcave
  utility representing a locally nonsatiated preference solves (3.H.2) for its Walrasian demand
  (Shephard's lemma and (3.E.4)).
* `integrability_recovers_expenditure`: hence any positive solution of (3.H.2) with
  `E(p⁰) = e(p⁰, ū)` is the expenditure function `e(·, ū)` on all of `p ≫ 0`.
-/

namespace MWG.ClassicalDemand

open MWG.ConsumerChoice Kreps.PreferenceProperties Filter Topology
open scoped NNReal

variable {L : ℕ}

/-- The open domain `{(p, w) : p ≫ 0, w > 0}` of a demand function. -/
def demandDomain (L : ℕ) : Set ((Fin L → ℝ) × ℝ) := {z | StrictlyPositive z.1 ∧ 0 < z.2}

/-- The demand domain is open. -/
theorem isOpen_demandDomain (L : ℕ) : IsOpen (demandDomain L) :=
  ((relations_isOpen_strictlyPositive L).preimage continuous_fst).inter
    (isOpen_lt continuous_const continuous_snd)

/-- **Section 3.H** (MWG, pp. 78-80). Let `x(p, w)` be continuously differentiable on
`{p ≫ 0, w > 0}`. If `E₁` and `E₂` are positive solutions of (3.H.2) on `p ≫ 0` with
`E₁(p⁰) = E₂(p⁰)` for one `p⁰ ≫ 0`, then `E₁ = E₂` on `p ≫ 0`. -/
theorem pde_solution_unique {x : DemandFunction L}
    (hx : ContDiffOn ℝ 1 (Function.uncurry x) (demandDomain L)) {E₁ E₂ : (Fin L → ℝ) → ℝ}
    (h₁ : SolvesPDE x E₁) (h₂ : SolvesPDE x E₂)
    (hpos₁ : ∀ q, StrictlyPositive q → 0 < E₁ q) (hpos₂ : ∀ q, StrictlyPositive q → 0 < E₂ q)
    {p₀ : Fin L → ℝ} (hp₀ : StrictlyPositive p₀) (h0 : E₁ p₀ = E₂ p₀) {p : Fin L → ℝ}
    (hp : StrictlyPositive p) : E₁ p = E₂ p := by
  set z := p - p₀ with hz
  set γ : ℝ → Fin L → ℝ := fun t => p₀ + t • z with hγdef
  have hγ : ∀ t, HasDerivAt γ z t := fun t => by
    change HasDerivAt (fun t : ℝ => p₀ + t • z) z t
    simpa using ((hasDerivAt_id t).smul_const z).const_add p₀
  have hγc : Continuous γ := by rw [hγdef]; fun_prop
  have hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1, StrictlyPositive (γ t) := by
    intro t ht
    have : γ t = (1 - t) • p₀ + t • p := by simp only [hγdef, hz]; module
    rw [this]
    exact exp_convex_strictlyPositive L hp₀ hp (by linarith [ht.2]) ht.1 (by ring)
  -- the two solutions along the segment
  have hd : ∀ {E : (Fin L → ℝ) → ℝ}, SolvesPDE x E → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun t => E (γ t)) (z ⬝ᵥ x (γ t) (E (γ t))) t := by
    intro E hE t ht
    have := (hE (γ t) (hseg t ht)).comp_hasDerivAt t (hγ t)
    rwa [dualityDotCLM_apply, dotProduct_comm] at this
  have hcont : ∀ {E : (Fin L → ℝ) → ℝ}, SolvesPDE x E →
      ContinuousOn (fun t => E (γ t)) (Set.Icc 0 1) :=
    fun hE t ht => (hd hE t ht).continuousAt.continuousWithinAt
  -- a compact range of wealth levels `[m, M]` with `m > 0`
  have hK : IsCompact (Set.Icc (0 : ℝ) 1) := isCompact_Icc
  have hne : (Set.Icc (0 : ℝ) 1).Nonempty := ⟨0, by simp⟩
  obtain ⟨t₁, ht₁, hmin₁⟩ := hK.exists_isMinOn hne (hcont h₁)
  obtain ⟨t₂, ht₂, hmin₂⟩ := hK.exists_isMinOn hne (hcont h₂)
  obtain ⟨s₁, hs₁, hmax₁⟩ := hK.exists_isMaxOn hne (hcont h₁)
  obtain ⟨s₂, hs₂, hmax₂⟩ := hK.exists_isMaxOn hne (hcont h₂)
  set m := min (E₁ (γ t₁)) (E₂ (γ t₂)) with hm
  set M := max (E₁ (γ s₁)) (E₂ (γ s₂)) with hM
  have hm0 : 0 < m := lt_min (hpos₁ _ (hseg t₁ ht₁)) (hpos₂ _ (hseg t₂ ht₂))
  have hmem₁ : ∀ t ∈ Set.Icc (0 : ℝ) 1, E₁ (γ t) ∈ Set.Icc m M := fun t ht =>
    ⟨(min_le_left _ _).trans (hmin₁ ht), (hmax₁ ht).trans (le_max_left _ _)⟩
  have hmem₂ : ∀ t ∈ Set.Icc (0 : ℝ) 1, E₂ (γ t) ∈ Set.Icc m M := fun t ht =>
    ⟨(min_le_right _ _).trans (hmin₂ ht), (hmax₂ ht).trans (le_max_right _ _)⟩
  -- a bound on the derivative of `x` on the compact set `γ([0, 1]) × [m, M]`
  set C : Set ((Fin L → ℝ) × ℝ) := (γ '' Set.Icc 0 1) ×ˢ Set.Icc m M with hC
  have hCc : IsCompact C := (hK.image hγc).prod isCompact_Icc
  have hCD : C ⊆ demandDomain L := by
    rintro ⟨q, w⟩ ⟨⟨t, ht, rfl⟩, hw⟩
    exact ⟨hseg t ht, hm0.trans_le hw.1⟩
  have hfc : ContinuousOn (fderiv ℝ (Function.uncurry x)) C :=
    (hx.continuousOn_fderiv_of_isOpen (isOpen_demandDomain L) le_rfl).mono hCD
  obtain ⟨B, hB⟩ := hCc.exists_bound_of_continuousOn hfc
  have hdiff : ∀ c ∈ demandDomain L, HasFDerivAt (Function.uncurry x)
      (fderiv ℝ (Function.uncurry x) c) c := fun c hc =>
    ((hx.differentiableOn one_ne_zero c hc).differentiableAt
      ((isOpen_demandDomain L).mem_nhds hc)).hasFDerivAt
  -- the right side `v(t, w) = z·x(γ(t), w)` is Lipschitz in `w` on `[m, M]`
  set v : ℝ → ℝ → ℝ := fun t w => z ⬝ᵥ x (γ t) w with hv
  set K : ℝ≥0 := Real.toNNReal (L * (‖z‖ * B)) with hKdef
  have hlip : ∀ t ∈ Set.Ico (0 : ℝ) 1, LipschitzOnWith K (v t) (Set.Icc m M) := by
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := Set.Ico_subset_Icc_self ht
    apply (convex_Icc m M).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (f' := fun w => z ⬝ᵥ fderiv ℝ (Function.uncurry x) (γ t, w) (0, 1))
    · intro w hw
      have hc : (γ t, w) ∈ C := ⟨⟨t, ht', rfl⟩, hw⟩
      have h1 : HasDerivAt (fun w : ℝ => ((γ t, w) : (Fin L → ℝ) × ℝ)) (0, 1) w :=
        (hasDerivAt_const w (γ t)).prodMk (hasDerivAt_id w)
      have h2 := (hdiff _ (hCD hc)).comp_hasDerivAt w h1
      have h3 := (dualityDotCLM z).hasFDerivAt.comp_hasDerivAt w h2
      simp only [Function.comp_def, dualityDotCLM_apply] at h3
      exact h3.hasDerivWithinAt
    · intro w hw
      have hc : (γ t, w) ∈ C := ⟨⟨t, ht', rfl⟩, hw⟩
      rw [← NNReal.coe_le_coe, coe_nnnorm, hKdef, Real.coe_toNNReal']
      refine le_max_of_le_left ?_
      refine (duality_abs_dotProduct_le _ _).trans ?_
      have hb : ‖fderiv ℝ (Function.uncurry x) (γ t, w) ((0 : Fin L → ℝ), (1 : ℝ))‖ ≤ B := by
        refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
        have : ‖(((0 : Fin L → ℝ), (1 : ℝ)) : (Fin L → ℝ) × ℝ)‖ = 1 := by simp
        rw [this, mul_one]
        exact hB _ hc
      have hz0 : 0 ≤ ‖z‖ := norm_nonneg _
      have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb hz0) hL0
  have hderiv : ∀ {E : (Fin L → ℝ) → ℝ}, SolvesPDE x E → ∀ t ∈ Set.Ico (0 : ℝ) 1,
      HasDerivWithinAt (fun t => E (γ t)) (v t (E (γ t))) (Set.Ici t) t :=
    fun hE t ht => (hd hE t (Set.Ico_subset_Icc_self ht)).hasDerivWithinAt
  have heq := ODE_solution_unique_of_mem_Icc_right hlip (hcont h₁) (hderiv h₁)
    (fun t ht => hmem₁ t (Set.Ico_subset_Icc_self ht)) (hcont h₂) (hderiv h₂)
    (fun t ht => hmem₂ t (Set.Ico_subset_Icc_self ht)) (by simp [hγdef, h0])
  have := heq (Set.right_mem_Icc.mpr zero_le_one)
  simpa [hγdef, hz] using this

/-- **Section 3.H** (MWG, p. 78). The expenditure function solves (3.H.2) for the Walrasian
demand: if `u` is continuous and strictly quasiconcave on `ℝ^L_+`, represents a locally
nonsatiated `≿`, `ū > u(0)` is attainable and `x(p, w) ∈ x(p, w)` is a demand selection, then
`∇_p e(p, ū) = x(p, e(p, ū))` for every `p ≫ 0`. -/
theorem expenditure_solvesPDE {u : (Fin L → ℝ) → ℝ} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hrep : RepresentsOn (nonnegOrthant L) u r) (hu : ContinuousOn u (nonnegOrthant L))
    (hlns : LocallyNonsatiated (nonnegOrthant L) r)
    (hq : StrictlyQuasiconcaveOn (nonnegOrthant L) u) {ub : ℝ} (hub : u 0 < ub)
    (hne : ∃ x ∈ nonnegOrthant L, ub ≤ u x) {x : DemandFunction L}
    (hx : ∀ q w, StrictlyPositive q → 0 ≤ w → x q w ∈ walrasianDemand u q w) :
    SolvesPDE x fun q => expenditure u q ub := by
  intro q hq'
  have hmem : x q (expenditure u q ub) ∈ hicksianDemand u q ub := by
    rw [equation_3_E_4_left hrep hu hlns hq' hub hne]
    exact hx q _ hq' (expenditure_nonneg u hq' ub)
  exact shephard_lemma hu hq hq' hmem

/-- **Section 3.H** (MWG, pp. 78-80): the expenditure function is recovered uniquely from
demand. Under the hypotheses of `expenditure_solvesPDE`, with a demand selection that is
continuously differentiable on `{p ≫ 0, w > 0}` and `e(·, ū) > 0`, every positive solution `E`
of (3.H.2) with `E(p⁰) = e(p⁰, ū)` at one `p⁰ ≫ 0` equals `e(·, ū)` on `p ≫ 0`. -/
theorem integrability_recovers_expenditure {u : (Fin L → ℝ) → ℝ}
    {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hrep : RepresentsOn (nonnegOrthant L) u r) (hu : ContinuousOn u (nonnegOrthant L))
    (hlns : LocallyNonsatiated (nonnegOrthant L) r)
    (hq : StrictlyQuasiconcaveOn (nonnegOrthant L) u) {ub : ℝ} (hub : u 0 < ub)
    (hne : ∃ x ∈ nonnegOrthant L, ub ≤ u x) {x : DemandFunction L}
    (hx : ∀ q w, StrictlyPositive q → 0 ≤ w → x q w ∈ walrasianDemand u q w)
    (hxc : ContDiffOn ℝ 1 (Function.uncurry x) (demandDomain L))
    (hepos : ∀ q, StrictlyPositive q → 0 < expenditure u q ub) {E : (Fin L → ℝ) → ℝ}
    (hE : SolvesPDE x E) (hEpos : ∀ q, StrictlyPositive q → 0 < E q) {p₀ : Fin L → ℝ}
    (hp₀ : StrictlyPositive p₀) (h0 : E p₀ = expenditure u p₀ ub) {p : Fin L → ℝ}
    (hp : StrictlyPositive p) : E p = expenditure u p ub :=
  pde_solution_unique hxc hE (expenditure_solvesPDE hrep hu hlns hq hub hne hx) hEpos hepos hp₀
    h0 hp

end MWG.ClassicalDemand
