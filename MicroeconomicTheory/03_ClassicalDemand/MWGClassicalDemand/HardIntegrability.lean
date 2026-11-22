/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.IntegrabilityTwoGoods
import MWGClassicalDemand.IntegrabilityUnique
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Integrability with two commodities: global solutions of (3.H.1)

MWG, Section 3.H, pp. 78-80, and footnote 18: the case `L = 2`, from primitive hypotheses.

* A scalar ODE `y' = V(t, y)` whose field is `C¹` on `ℝ²` and bounded by `1` has, through every
  point, a solution defined on all of `ℝ`, and any two solutions defined on an interval that agree
  at one point agree on that interval (`hardInt_exists_global`, `hardInt_unique_Ioo`,
  `hardInt_unique`). Existence is the Picard-Lindelöf theorem on `[t₀ - N, t₀ + N]` with the
  ball of radius `N` (the bound `|V| ≤ 1` keeps solutions inside it), glued over `N`.
* In logarithmic coordinates `s = log p₁`, `z = log w`, equation (3.H.1)
  `e'(p₁) = x₁((p₁, 1), e(p₁))` becomes `z'(s) = p₁ x₁ / w`, which lies in `[0, 1]` by Walras' law
  and nonnegativity of demand (`hardIntLogField`, `hardIntLogField_abs_le`). Hence (3.H.1) has a
  unique positive solution on all of `p₁ > 0` through every initial condition `(p₁⁰, w⁰) ≫ 0`
  (`footnote_3_18_global`, `footnote_3_18_unique`): this is the continuation of footnote 18.
* The solutions, indexed by `u` with `e(1, u) = exp u`, are strictly increasing, continuous and
  onto `(0, ∞)` in `u` (`hardInt_solution_family`): continuity comes from monotonicity and
  surjectivity, so no continuous-dependence theorem is needed.
* **The `L = 2` integrability claim of p. 80** (`integrability_two_goods_global`): a continuously
  differentiable, nonnegative demand function on `p ≫ 0, w > 0` that is homogeneous of degree zero
  and satisfies Walras' law and the weak axiom is the Walrasian demand of a preference. The book
  says "differentiable"; we assume `C¹`, the "minor technical requirement" of footnote 19
  (`docs/corrections-F1.md`, F1-1).
-/

namespace MWG.ClassicalDemand

open MWG.ConsumerChoice Kreps.PreferenceProperties Filter Topology
open scoped NNReal

/-- A field `V` that is `C¹` on `ℝ²` is Lipschitz in `y`, uniformly for `t` in a compact interval,
on every closed ball. -/
theorem hardInt_lipschitz {V : ℝ → ℝ → ℝ} (hV : ContDiff ℝ 1 (fun z : ℝ × ℝ => V z.1 z.2))
    (A B c R : ℝ) :
    ∃ K : ℝ≥0, ∀ t ∈ Set.Icc A B, LipschitzOnWith K (V t) (Metric.closedBall c R) := by
  obtain ⟨K, hK⟩ := (hV.contDiffOn (s := Set.Icc A B ×ˢ Metric.closedBall c R)
    ).exists_lipschitzOnWith one_ne_zero ((convex_Icc A B).prod (convex_closedBall c R))
    (isCompact_Icc.prod (isCompact_closedBall c R))
  refine ⟨K, fun t ht => LipschitzOnWith.of_dist_le_mul fun y hy y' hy' => ?_⟩
  have := hK.dist_le_mul (t, y) ⟨ht, hy⟩ (t, y') ⟨ht, hy'⟩
  simp only [Prod.dist_eq, dist_self, max_eq_right dist_nonneg] at this
  exact this

/-- Uniqueness for `y' = V(t, y)` with `V` of class `C¹`: two solutions on an open interval that
agree at one point of it agree on the whole interval. -/
theorem hardInt_unique_Ioo {V : ℝ → ℝ → ℝ} (hV : ContDiff ℝ 1 (fun z : ℝ × ℝ => V z.1 z.2))
    {f g : ℝ → ℝ} {A B t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo A B)
    (hf : ∀ t ∈ Set.Ioo A B, HasDerivAt f (V t (f t)) t)
    (hg : ∀ t ∈ Set.Ioo A B, HasDerivAt g (V t (g t)) t) (h0 : f t₀ = g t₀) :
    Set.EqOn f g (Set.Ioo A B) := by
  intro t ht
  have hAm : A < min t t₀ := lt_min ht.1 ht₀.1
  have hBm : max t t₀ < B := max_lt ht.2 ht₀.2
  set A' := (A + min t t₀) / 2 with hA'
  set B' := (B + max t t₀) / 2 with hB'
  have hsub : Set.Icc A' B' ⊆ Set.Ioo A B := fun s hs =>
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hfc : ContinuousOn f (Set.Icc A' B') := fun s hs =>
    (hf s (hsub hs)).continuousAt.continuousWithinAt
  have hgc : ContinuousOn g (Set.Icc A' B') := fun s hs =>
    (hg s (hsub hs)).continuousAt.continuousWithinAt
  obtain ⟨Cf, hCf⟩ := isCompact_Icc.exists_bound_of_continuousOn hfc
  obtain ⟨Cg, hCg⟩ := isCompact_Icc.exists_bound_of_continuousOn hgc
  obtain ⟨K, hK⟩ := hardInt_lipschitz hV A' B' 0 (max Cf Cg)
  have hmin1 : min t t₀ ≤ t := min_le_left _ _
  have hmin2 : min t t₀ ≤ t₀ := min_le_right _ _
  have hmax1 : t ≤ max t t₀ := le_max_left _ _
  have hmax2 : t₀ ≤ max t t₀ := le_max_right _ _
  refine ODE_solution_unique_of_mem_Ioo (v := V) (s := fun _ => Metric.closedBall 0 (max Cf Cg))
    (fun s hs => hK s (Set.Ioo_subset_Icc_self hs)) ⟨by linarith, by linarith⟩
    (fun s hs => ⟨hf s (hsub (Set.Ioo_subset_Icc_self hs)), ?_⟩)
    (fun s hs => ⟨hg s (hsub (Set.Ioo_subset_Icc_self hs)), ?_⟩) h0 ⟨by linarith, by linarith⟩
  · rw [mem_closedBall_zero_iff]
    exact (hCf s (Set.Ioo_subset_Icc_self hs)).trans (le_max_left _ _)
  · rw [mem_closedBall_zero_iff]
    exact (hCg s (Set.Ioo_subset_Icc_self hs)).trans (le_max_right _ _)

/-- Global uniqueness for `y' = V(t, y)` with `V` of class `C¹`. -/
theorem hardInt_unique {V : ℝ → ℝ → ℝ} (hV : ContDiff ℝ 1 (fun z : ℝ × ℝ => V z.1 z.2))
    {f g : ℝ → ℝ} {t₀ : ℝ} (hf : ∀ t, HasDerivAt f (V t (f t)) t)
    (hg : ∀ t, HasDerivAt g (V t (g t)) t) (h0 : f t₀ = g t₀) : f = g := by
  funext t
  have h1 : min t t₀ - 1 < t := by linarith [min_le_left t t₀]
  have h2 : t < max t t₀ + 1 := by linarith [le_max_left t t₀]
  have h3 : min t t₀ - 1 < t₀ := by linarith [min_le_right t t₀]
  have h4 : t₀ < max t t₀ + 1 := by linarith [le_max_right t t₀]
  exact hardInt_unique_Ioo hV ⟨h3, h4⟩ (fun s _ => hf s) (fun s _ => hg s) h0 ⟨h1, h2⟩

/-- Local existence for `y' = V(t, y)` with `V` of class `C¹` and `|V| ≤ 1`, on
`(t₀ - N, t₀ + N)`, by the Picard-Lindelöf theorem with the ball of radius `N` around `y₀`. -/
theorem hardInt_exists_local {V : ℝ → ℝ → ℝ} (hV : ContDiff ℝ 1 (fun z : ℝ × ℝ => V z.1 z.2))
    (hb : ∀ t y, |V t y| ≤ 1) (t₀ y₀ : ℝ) (N : ℕ) :
    ∃ α : ℝ → ℝ, α t₀ = y₀ ∧ ∀ t ∈ Set.Ioo (t₀ - N) (t₀ + N), HasDerivAt α (V t (α t)) t := by
  obtain ⟨K, hK⟩ := hardInt_lipschitz hV (t₀ - N) (t₀ + N) y₀ N
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have ht : t₀ ∈ Set.Icc (t₀ - N) (t₀ + N) := ⟨by linarith, by linarith⟩
  have hPL : IsPicardLindelof V (⟨t₀, ht⟩ : Set.Icc (t₀ - N) (t₀ + N)) y₀ (N : ℝ≥0) 0 1 K :=
    { lipschitzOnWith := fun t ht' => by
        rw [NNReal.coe_natCast]
        exact hK t ht'
      continuousOn := fun y _ =>
        (hV.continuous.comp (continuous_id.prodMk continuous_const)).continuousOn
      norm_le := fun t _ y _ => by
        rw [Real.norm_eq_abs, NNReal.coe_one]
        exact hb t y
      mul_max_le := by
        simp only [NNReal.coe_one, one_mul, NNReal.coe_natCast, NNReal.coe_zero, sub_zero]
        rw [max_le_iff]
        constructor <;> linarith }
  obtain ⟨α, hα0, hα⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨α, hα0, fun t ht' =>
    (hα t (Set.Ioo_subset_Icc_self ht')).hasDerivAt (Icc_mem_nhds ht'.1 ht'.2)⟩

/-- Global existence for `y' = V(t, y)` with `V` of class `C¹` and `|V| ≤ 1`: through every
point `(t₀, y₀)` there is a solution defined on all of `ℝ` (the local solutions on
`(t₀ - N, t₀ + N)` agree by uniqueness and are glued). -/
theorem hardInt_exists_global {V : ℝ → ℝ → ℝ} (hV : ContDiff ℝ 1 (fun z : ℝ × ℝ => V z.1 z.2))
    (hb : ∀ t y, |V t y| ≤ 1) (t₀ y₀ : ℝ) :
    ∃ α : ℝ → ℝ, α t₀ = y₀ ∧ ∀ t, HasDerivAt α (V t (α t)) t := by
  choose β hβ0 hβ using fun N : ℕ => hardInt_exists_local hV hb t₀ y₀ N
  have hcons : ∀ N M : ℕ, N ≤ M → Set.EqOn (β N) (β M) (Set.Ioo (t₀ - N) (t₀ + N)) := by
    intro N M hNM t ht
    have hNM' : (N : ℝ) ≤ M := Nat.cast_le.mpr hNM
    have hsub : Set.Ioo (t₀ - N) (t₀ + N) ⊆ Set.Ioo (t₀ - M) (t₀ + M) :=
      Set.Ioo_subset_Ioo (by linarith) (by linarith)
    have hNpos : (0 : ℝ) < N := by
      by_contra h
      have : (N : ℝ) = 0 := le_antisymm (not_lt.mp h) (Nat.cast_nonneg N)
      rw [this] at ht
      linarith [ht.1, ht.2]
    exact hardInt_unique_Ioo hV ⟨by linarith, by linarith⟩ (hβ N)
      (fun s hs => hβ M s (hsub hs)) ((hβ0 N).trans (hβ0 M).symm) ht
  set n : ℝ → ℕ := fun t => ⌈|t - t₀|⌉₊ + 1 with hn_def
  have hn : ∀ t, t ∈ Set.Ioo (t₀ - n t) (t₀ + n t) := fun t => by
    have h1 := Nat.le_ceil |t - t₀|
    have h2 : ((n t : ℕ) : ℝ) = (⌈|t - t₀|⌉₊ : ℝ) + 1 := by
      simp only [hn_def]
      push_cast
      ring
    rw [h2]
    constructor
    · linarith [neg_abs_le (t - t₀)]
    · linarith [le_abs_self (t - t₀)]
  refine ⟨fun t => β (n t) t, hβ0 _, fun t => ?_⟩
  have heq : (fun s => β (n s) s) =ᶠ[𝓝 t] β (n t) := by
    filter_upwards [Ioo_mem_nhds (hn t).1 (hn t).2] with s hs
    rcases le_total (n s) (n t) with h | h
    · exact hcons _ _ h (hn s)
    · exact (hcons _ _ h hs).symm
  exact (hβ (n t) t (hn t)).congr_of_eventuallyEq heq

/-- **Footnote 18** (MWG, p. 79). Equation (3.H.1) `e'(p₁) = x₁((p₁, 1), e)` in logarithmic
coordinates `s = log p₁`, `z = log e`: `z'(s) = p₁ x₁((p₁, 1), w) / w` with `p₁ = exp s`,
`w = exp z`. -/
noncomputable def hardIntLogField (x : DemandFunction 2) (s z : ℝ) : ℝ :=
  Real.exp s * x ![Real.exp s, 1] (Real.exp z) 0 / Real.exp z

/-- The price vector `(exp s, 1)` is strictly positive. -/
theorem hardInt_strictlyPositive_exp (s : ℝ) :
    StrictlyPositive (![Real.exp s, 1] : Fin 2 → ℝ) := fun i => by
  fin_cases i
  · simp [Real.exp_pos]
  · simp

/-- If demand is `C¹` on `p ≫ 0, w > 0`, the logarithmic field is `C¹` on `ℝ²`. -/
theorem hardIntLogField_contDiff {x : DemandFunction 2}
    (hx : ContDiffOn ℝ 1 (Function.uncurry x) (demandDomain 2)) :
    ContDiff ℝ 1 (fun z : ℝ × ℝ => hardIntLogField x z.1 z.2) := by
  have hg : ContDiff ℝ 1
      (fun z : ℝ × ℝ => ((![Real.exp z.1, 1] : Fin 2 → ℝ), Real.exp z.2)) := by
    refine ContDiff.prodMk (contDiff_pi.mpr fun i => ?_) (Real.contDiff_exp.comp contDiff_snd)
    fin_cases i
    · convert Real.contDiff_exp.comp contDiff_fst using 1
      funext z
      rfl
    · simpa using contDiff_const
  have hmaps : ∀ z : ℝ × ℝ,
      ((![Real.exp z.1, 1] : Fin 2 → ℝ), Real.exp z.2) ∈ demandDomain 2 :=
    fun z => ⟨hardInt_strictlyPositive_exp z.1, Real.exp_pos _⟩
  have hc := hx.comp_contDiff hg hmaps
  have h0 : ContDiff ℝ 1 (fun z : ℝ × ℝ => x ![Real.exp z.1, 1] (Real.exp z.2) 0) :=
    contDiff_pi.mp hc 0
  exact ((Real.contDiff_exp.comp contDiff_fst).mul h0).div
    (Real.contDiff_exp.comp contDiff_snd) fun z => (Real.exp_pos _).ne'

/-- By Walras' law and nonnegativity of demand, `0 ≤ p₁ x₁ / w ≤ 1`: the logarithmic field is
bounded by `1`. -/
theorem hardIntLogField_abs_le {x : DemandFunction 2} (hW : WalrasLaw x)
    (hnn : ∀ q w, StrictlyPositive q → 0 < w → x q w ∈ nonnegOrthant 2) (s z : ℝ) :
    |hardIntLogField x s z| ≤ 1 := by
  have hq := hardInt_strictlyPositive_exp s
  have hw := hW _ _ ⟨hq, Real.exp_pos z⟩
  have hn := hnn _ _ hq (Real.exp_pos z)
  have h0 : 0 ≤ x ![Real.exp s, 1] (Real.exp z) 0 := hn 0
  have h1 : 0 ≤ x ![Real.exp s, 1] (Real.exp z) 1 := hn 1
  simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    one_mul] at hw
  have hez := Real.exp_pos z
  have hes := Real.exp_pos s
  unfold hardIntLogField
  rw [abs_le]
  constructor
  · have : 0 ≤ Real.exp s * x ![Real.exp s, 1] (Real.exp z) 0 / Real.exp z :=
      div_nonneg (mul_nonneg hes.le h0) hez.le
    linarith
  · rw [div_le_one hez]
    linarith

/-- From the logarithmic equation back to (3.H.1): if `z' = V(s, z)` on `ℝ`, then
`e(p₁) = exp z(log p₁)` solves `e'(p₁) = x₁((p₁, 1), e(p₁))` at every `p₁ > 0`. -/
theorem hardInt_lift_hasDerivAt {x : DemandFunction 2} {Z : ℝ → ℝ}
    (hZ : ∀ s, HasDerivAt Z (hardIntLogField x s (Z s)) s) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun t => Real.exp (Z (Real.log t)))
      (x ![r, 1] (Real.exp (Z (Real.log r))) 0) r := by
  have h1 := (hZ (Real.log r)).comp r (Real.hasDerivAt_log hr.ne')
  have h2 := (Real.hasDerivAt_exp _).comp r h1
  refine h2.congr_deriv ?_
  unfold hardIntLogField
  rw [Real.exp_log hr]
  simp only [Function.comp_apply]
  field_simp

/-- From (3.H.1) to the logarithmic equation: a positive solution `e` of (3.H.1) on `p₁ > 0` gives
the solution `z(s) = log e(exp s)` of `z' = V(s, z)` on `ℝ`. -/
theorem hardInt_log_hasDerivAt {x : DemandFunction 2} {e : ℝ → ℝ}
    (hpos : ∀ r, 0 < r → 0 < e r)
    (he : ∀ r, 0 < r → HasDerivAt e (x ![r, 1] (e r) 0) r) (s : ℝ) :
    HasDerivAt (fun t => Real.log (e (Real.exp t)))
      (hardIntLogField x s (Real.log (e (Real.exp s)))) s := by
  have hes := Real.exp_pos s
  have h1 := (he _ hes).comp s (Real.hasDerivAt_exp s)
  have h2 := h1.log (hpos _ hes).ne'
  refine h2.congr_deriv ?_
  unfold hardIntLogField
  rw [Real.exp_log (hpos _ hes)]
  simp only [Function.comp_apply]
  field_simp

/-- Two global solutions of `y' = V(t, y)` (`V` of class `C¹`) that are ordered at one time are
strictly ordered at every time: solutions cannot cross. -/
theorem hardInt_strict_order {V : ℝ → ℝ → ℝ} (hV : ContDiff ℝ 1 (fun z : ℝ × ℝ => V z.1 z.2))
    {f g : ℝ → ℝ} (hf : ∀ t, HasDerivAt f (V t (f t)) t) (hg : ∀ t, HasDerivAt g (V t (g t)) t)
    {t₀ : ℝ} (h0 : f t₀ < g t₀) (t : ℝ) : f t < g t := by
  by_contra h
  push Not at h
  have hc : ContinuousOn (fun s => g s - f s) (Set.uIcc t₀ t) := fun s _ =>
    ((hg s).continuousAt.sub (hf s).continuousAt).continuousWithinAt
  have hmem : (0 : ℝ) ∈ Set.uIcc (g t₀ - f t₀) (g t - f t) := by
    rw [Set.mem_uIcc]
    right
    constructor <;> linarith
  obtain ⟨c, -, hc0⟩ := intermediate_value_uIcc hc hmem
  have hfg : f c = g c := by
    simp only at hc0
    linarith
  have := hardInt_unique hV hf hg hfg
  rw [this] at h0
  exact lt_irrefl _ h0

/-- **Footnote 18** (MWG, p. 79), global form. Let `x` be a nonnegative demand function for two
goods satisfying Walras' law and continuously differentiable on `p ≫ 0, w > 0`. For every
initial condition `(p₁⁰, w⁰)` with `w⁰ > 0` (the book takes `p₁⁰ > 0`; the statement holds for
every `p₁⁰`), equation (3.H.1) has a solution on all of `p₁ > 0`, which is positive. -/
theorem footnote_3_18_global {x : DemandFunction 2} (hW : WalrasLaw x)
    (hnn : ∀ q w, StrictlyPositive q → 0 < w → x q w ∈ nonnegOrthant 2)
    (hx : ContDiffOn ℝ 1 (Function.uncurry x) (demandDomain 2)) {p₀ w₀ : ℝ} (hw₀ : 0 < w₀) :
    ∃ e : ℝ → ℝ, e p₀ = w₀ ∧ ∀ r, 0 < r → 0 < e r ∧ HasDerivAt e (x ![r, 1] (e r) 0) r := by
  obtain ⟨Z, hZ0, hZ⟩ := hardInt_exists_global (hardIntLogField_contDiff hx)
    (hardIntLogField_abs_le hW hnn) (Real.log p₀) (Real.log w₀)
  refine ⟨fun t => Real.exp (Z (Real.log t)), ?_, fun r hr =>
    ⟨Real.exp_pos _, hardInt_lift_hasDerivAt hZ hr⟩⟩
  simp only [hZ0, Real.exp_log hw₀]

/-- **Footnote 18** (MWG, p. 79), uniqueness. If `x` is continuously differentiable on
`p ≫ 0, w > 0`, two positive solutions of (3.H.1) on `p₁ > 0` that agree at one `p₁⁰ > 0` agree
at every `p₁ > 0`. -/
theorem footnote_3_18_unique {x : DemandFunction 2}
    (hx : ContDiffOn ℝ 1 (Function.uncurry x) (demandDomain 2)) {e₁ e₂ : ℝ → ℝ}
    (hpos₁ : ∀ r, 0 < r → 0 < e₁ r) (hpos₂ : ∀ r, 0 < r → 0 < e₂ r)
    (h₁ : ∀ r, 0 < r → HasDerivAt e₁ (x ![r, 1] (e₁ r) 0) r)
    (h₂ : ∀ r, 0 < r → HasDerivAt e₂ (x ![r, 1] (e₂ r) 0) r) {p₀ : ℝ} (hp₀ : 0 < p₀)
    (h0 : e₁ p₀ = e₂ p₀) {r : ℝ} (hr : 0 < r) : e₁ r = e₂ r := by
  have hu := hardInt_unique (hardIntLogField_contDiff hx) (t₀ := Real.log p₀)
    (hardInt_log_hasDerivAt hpos₁ h₁) (hardInt_log_hasDerivAt hpos₂ h₂)
    (by simp only [Real.exp_log hp₀, h0])
  have := congrFun hu (Real.log r)
  simp only [Real.exp_log hr] at this
  exact Real.log_injOn_pos (hpos₁ r hr) (hpos₂ r hr) this

/-- **Footnote 18 and p. 80** (MWG). The family of solutions of (3.H.1) indexed by the utility
level `u`, with `e(1, u) = exp u`: each `e(·, u)` is a positive solution on `p₁ > 0`, and at every
`p₁ > 0`, `u ↦ e(p₁, u)` is strictly increasing, continuous and onto `(0, ∞)`. -/
theorem hardInt_solution_family {x : DemandFunction 2} (hW : WalrasLaw x)
    (hnn : ∀ q w, StrictlyPositive q → 0 < w → x q w ∈ nonnegOrthant 2)
    (hx : ContDiffOn ℝ 1 (Function.uncurry x) (demandDomain 2)) :
    ∃ e : ℝ → ℝ → ℝ, (∀ u r, 0 < r → HasDerivAt (fun s => e s u) (x ![r, 1] (e r u) 0) r) ∧
      (∀ u r, 0 < r → 0 < e r u) ∧ (∀ r, 0 < r → StrictMono (e r)) ∧
      (∀ r, 0 < r → Continuous (e r)) ∧ (∀ r, 0 < r → ∀ w, 0 < w → ∃ u, e r u = w) ∧
      ∀ u, e 1 u = Real.exp u := by
  have hV := hardIntLogField_contDiff hx
  have hb := hardIntLogField_abs_le hW hnn
  choose sol hsol0 hsol using fun t₀ y₀ : ℝ => hardInt_exists_global hV hb t₀ y₀
  set e : ℝ → ℝ → ℝ := fun r u => Real.exp (sol 0 u (Real.log r)) with he
  -- the logarithmic solution through any point is a member of the family
  have hmem : ∀ s y, sol 0 (sol s y 0) = sol s y := fun s y =>
    hardInt_unique hV (t₀ := 0) (hsol 0 _) (hsol s y) (hsol0 0 _)
  -- strict monotonicity in the initial value at every time
  have hsm : ∀ s, StrictMono fun u => sol 0 u s := fun s u u' huu' =>
    hardInt_strict_order hV (hsol 0 u) (hsol 0 u') (t₀ := 0)
      (by rw [hsol0, hsol0]; exact huu') s
  have hsurjlog : ∀ s y, ∃ u, sol 0 u s = y := fun s y =>
    ⟨sol s y 0, by rw [hmem, hsol0]⟩
  refine ⟨e, fun u r hr => hardInt_lift_hasDerivAt (hsol 0 u) hr, fun u r _ => Real.exp_pos _,
    fun r _ => Real.exp_strictMono.comp (hsm _), fun r _ => ?_, fun r _ w hw => ?_, fun u => ?_⟩
  · have hc : Continuous fun u => sol 0 u (Real.log r) :=
      (hsm _).monotone.continuous_of_surjective fun y => hsurjlog _ y
    exact Real.continuous_exp.comp hc
  · obtain ⟨u, hu⟩ := hsurjlog (Real.log r) (Real.log w)
    exact ⟨u, by simp only [he, hu, Real.exp_log hw]⟩
  · simp only [he, Real.log_one, hsol0]

/-- **Section 3.H** (MWG, p. 80), the case `L = 2`, from primitive hypotheses. Let `x(p, w)` be a
nonnegative demand function for two goods that is homogeneous of degree zero, satisfies Walras'
law and the weak axiom, and is continuously differentiable on `p ≫ 0, w > 0`. Then there is a
family `e(·, u)` of solutions of (3.H.1) on `p₁ > 0`, and the preference recovered from the
expenditure functions `E(p, u) = p₂ e(p₁/p₂, u)` rationalizes `x`: its Walrasian demand at every
`(p, w) ≫ 0` is `{x(p, w)}`. -/
theorem integrability_two_goods_global {x : DemandFunction 2} (hH : HomogeneousZero x)
    (hW : WalrasLaw x) (hWA : WeakAxiom x)
    (hnn : ∀ q w, StrictlyPositive q → 0 < w → x q w ∈ nonnegOrthant 2)
    (hx : ContDiffOn ℝ 1 (Function.uncurry x) (demandDomain 2)) :
    ∃ e : ℝ → ℝ → ℝ, (∀ u r, 0 < r → HasDerivAt (fun s => e s u) (x ![r, 1] (e r u) 0) r) ∧
      ∀ p w, StrictlyPositive p → 0 < w →
        walrasianDemandPref (recoveredPref fun q u => twoGoodsLift (fun s => e s u) q) p w =
          {x p w} := by
  obtain ⟨e, hode, hepos, hmono, hcont, hsurj, -⟩ := hardInt_solution_family hW hnn hx
  refine ⟨e, hode, fun p w hp hw => ?_⟩
  have hD : ∀ q w, StrictlyPositive q → 0 < w → HasFDerivAt (Function.uncurry x)
      (fderiv ℝ (Function.uncurry x) (q, w)) (q, w) := fun q w hq hw =>
    ((hx.differentiableOn one_ne_zero (q, w) ⟨hq, hw⟩).differentiableAt
      ((isOpen_demandDomain 2).mem_nhds ⟨hq, hw⟩)).hasFDerivAt
  exact integrability_two_goods hH hW hWA hnn hD hode hepos hmono hcont hsurj hp hw

end MWG.ClassicalDemand
