import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.MonotoneContinuity
import MWGProduction.Profit
import MWGClassicalDemand.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import MWGProduction.ExercisesB
import MWGProduction.Geometry
import Mathlib.Analysis.SpecialFunctions.Sqrt
import MWGProduction.ExercisesD345
import MWGProduction.CobbDouglas
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.LagrangeMultipliers
set_option autoImplicit false

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# One-variable first-order conditions on `ℝ₊` (tools for MWG Chapter 10)

Section 10.C of MWG (pp. 317-320) repeatedly uses that, for a concave objective on `x ≥ 0`, the
Kuhn-Tucker condition "`f'(x) ≤ 0`, with equality if `x > 0`" is necessary and sufficient for a
maximum. This module proves that once, for a function differentiable within `[0, ∞)` (one-sided
at `0`, as in the book's `x ≥ 0` domain) with antitone derivative.

It also builds the solution `focSol d r` of the condition "`d(x) ≤ r`, with equality if `x > 0`"
for a strictly decreasing continuous marginal-benefit function `d`; this is how the book's
individual demand `x_i(p)` (with `d = φ_i'`) and supply `q_j(p)` (with `d = -c_j'`, `r = -p`)
are constructed on p. 319. We prove uniqueness, existence (intermediate value theorem),
monotonicity and continuity of the solution in `r`, and differentiability through the inverse
function rule.
-/

namespace MWG.CompetitiveMarkets

open Filter Topology

/-- If `f` has derivative `f' > 0` within `(a, ∞)` at `a`, then `f(y) > f(a)` for some `y > a`. -/
theorem foc_exists_gt_of_deriv_pos {f : ℝ → ℝ} {a f'a : ℝ}
    (hf : HasDerivWithinAt f f'a (Set.Ioi a) a) (hpos : 0 < f'a) (s : Set ℝ)
    (hs : s ∈ 𝓝[>] a) : ∃ y ∈ s, a < y ∧ f a < f y := by
  rw [hasDerivWithinAt_iff_tendsto_slope,
    Set.sdiff_singleton_eq_self (s := Set.Ioi a) (lt_irrefl a)] at hf
  have h1 : ∀ᶠ y in 𝓝[>] a, 0 < slope f a y := hf.eventually (lt_mem_nhds hpos)
  have h2 : ∀ᶠ y in 𝓝[>] a, a < y := self_mem_nhdsWithin
  obtain ⟨y, hy1, hy2, hy3⟩ := (h1.and (h2.and hs)).exists
  refine ⟨y, hy3, hy2, ?_⟩
  rw [slope_def_field] at hy1
  have := (div_pos_iff_of_pos_right (sub_pos.2 hy2)).1 hy1
  linarith

/-- If `f` has derivative `f' < 0` within `(-∞, a)` at `a`, then `f(y) > f(a)` for some `y < a`. -/
theorem foc_exists_lt_of_deriv_neg {f : ℝ → ℝ} {a f'a : ℝ}
    (hf : HasDerivWithinAt f f'a (Set.Iio a) a) (hneg : f'a < 0) (s : Set ℝ)
    (hs : s ∈ 𝓝[<] a) : ∃ y ∈ s, y < a ∧ f a < f y := by
  rw [hasDerivWithinAt_iff_tendsto_slope,
    Set.sdiff_singleton_eq_self (s := Set.Iio a) (lt_irrefl a)] at hf
  have h1 : ∀ᶠ y in 𝓝[<] a, slope f a y < 0 := hf.eventually (gt_mem_nhds hneg)
  have h2 : ∀ᶠ y in 𝓝[<] a, y < a := self_mem_nhdsWithin
  obtain ⟨y, hy1, hy2, hy3⟩ := (h1.and (h2.and hs)).exists
  refine ⟨y, hy3, hy2, ?_⟩
  rw [slope_def_field] at hy1
  have hd : y - a < 0 := sub_neg.2 hy2
  have := (div_neg_iff.1 hy1)
  rcases this with ⟨_, h⟩ | ⟨h, _⟩
  · linarith
  · linarith

/-- A function with derivatives within `[0, ∞)` at every point of `[0, ∞)` is continuous there. -/
theorem foc_continuousOn {f f' : ℝ → ℝ}
    (hf : ∀ x ∈ Set.Ici (0 : ℝ), HasDerivWithinAt f (f' x) (Set.Ici 0) x) :
    ContinuousOn f (Set.Ici 0) :=
  fun x hx => (hf x hx).continuousWithinAt

/-- At an interior point `x > 0`, a derivative within `[0, ∞)` is a two-sided derivative. -/
theorem foc_hasDerivAt {f f' : ℝ → ℝ}
    (hf : ∀ x ∈ Set.Ici (0 : ℝ), HasDerivWithinAt f (f' x) (Set.Ici 0) x) {x : ℝ}
    (hx : 0 < x) : HasDerivAt f (f' x) x :=
  (hf x hx.le).hasDerivAt (Ici_mem_nhds hx)

/-- On a subset `D ⊆ [0, ∞)`, derivatives within `[0, ∞)` restrict to derivatives within
the interior of `D` at interior points. -/
theorem foc_hasDerivWithin_interior {f f' : ℝ → ℝ}
    (hf : ∀ x ∈ Set.Ici (0 : ℝ), HasDerivWithinAt f (f' x) (Set.Ici 0) x) {D : Set ℝ}
    (hD : D ⊆ Set.Ici 0) : ∀ x ∈ interior D, HasDerivWithinAt f (f' x) (interior D) x := by
  intro x hx
  have hx0 : x ∈ Set.Ici (0 : ℝ) := hD (interior_subset hx)
  have hnhds : Set.Ici (0 : ℝ) ∈ 𝓝 x :=
    Filter.mem_of_superset (mem_interior_iff_mem_nhds.1 hx) hD
  exact ((hf x hx0).hasDerivAt hnhds).hasDerivWithinAt

/-- **Necessity of the Kuhn-Tucker condition on `ℝ₊`** (no concavity needed). If `a ≥ 0`
maximizes `f` on `[0, ∞)` and `f` has derivative `f'a` within `[0, ∞)` at `a`, then `f'a ≤ 0`,
with equality if `a > 0`. -/
theorem foc_max_necessary {f : ℝ → ℝ} {a f'a : ℝ} (hf : HasDerivWithinAt f f'a (Set.Ici 0) a)
    (ha : 0 ≤ a) (hmax : ∀ y, 0 ≤ y → f y ≤ f a) : f'a ≤ 0 ∧ (0 < a → f'a = 0) := by
  have hle : f'a ≤ 0 := by
    by_contra hpos
    push Not at hpos
    obtain ⟨y, _, hy, hfy⟩ := foc_exists_gt_of_deriv_pos
      (hf.mono fun z hz => (ha.trans (le_of_lt hz))) hpos Set.univ Filter.univ_mem
    exact absurd (hmax y (ha.trans hy.le)) (not_le.2 hfy)
  refine ⟨hle, fun hapos => le_antisymm hle ?_⟩
  by_contra hneg
  push Not at hneg
  have hs : Set.Ioi (0 : ℝ) ∈ 𝓝[<] a := mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hapos)
  obtain ⟨y, hy0, _, hfy⟩ := foc_exists_lt_of_deriv_neg
    ((hf.hasDerivAt (Ici_mem_nhds hapos)).hasDerivWithinAt) hneg _ hs
  exact absurd (hmax y (le_of_lt hy0)) (not_le.2 hfy)

/-- A one-sided local version: if `g` has derivative `g'` within `[a, ∞)` at `a` and
`g(t) ≤ g(a)` for all `t > a` close to `a`, then `g' ≤ 0`. -/
theorem foc_local_necessary {g : ℝ → ℝ} {a g' : ℝ} (hg : HasDerivWithinAt g g' (Set.Ici a) a)
    (hloc : ∀ᶠ t in 𝓝[>] a, g t ≤ g a) : g' ≤ 0 := by
  by_contra hpos
  push Not at hpos
  obtain ⟨y, hy, _, hfy⟩ := foc_exists_gt_of_deriv_pos (hg.mono Set.Ioi_subset_Ici_self) hpos
    {t | g t ≤ g a} hloc
  exact absurd hy (not_le.2 hfy)

/-- **The Kuhn-Tucker condition on `ℝ₊`** (MWG, pp. 317-318). Let `f` be differentiable within
`[0, ∞)` with antitone derivative `f'` (so `f` is concave). Then `a ≥ 0` maximizes `f` on
`[0, ∞)` if and only if `f'(a) ≤ 0`, with equality if `a > 0`. -/
theorem foc_max_iff {f f' : ℝ → ℝ}
    (hf : ∀ x ∈ Set.Ici (0 : ℝ), HasDerivWithinAt f (f' x) (Set.Ici 0) x)
    (hanti : AntitoneOn f' (Set.Ici 0)) {a : ℝ} (ha : 0 ≤ a) :
    (∀ y, 0 ≤ y → f y ≤ f a) ↔ (f' a ≤ 0 ∧ (0 < a → f' a = 0)) := by
  have hcont := foc_continuousOn hf
  constructor
  · exact foc_max_necessary (hf a ha) ha
  · rintro ⟨hle, heq⟩ y hy
    rcases le_total a y with hay | hya
    · have hsub : Set.Ici a ⊆ Set.Ici (0 : ℝ) := fun z hz => ha.trans hz
      have hmono : AntitoneOn f (Set.Ici a) := by
        refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici a) (hcont.mono hsub)
          (foc_hasDerivWithin_interior hf hsub) ?_
        intro x hx
        rw [interior_Ici] at hx
        exact (hanti ha (ha.trans hx.le) hx.le).trans hle
      exact hmono (Set.mem_Ici.2 le_rfl) hay hay
    · rcases eq_or_lt_of_le ha with h0 | hapos
      · have : y = a := le_antisymm hya (h0 ▸ hy)
        rw [this]
      · have hsub : Set.Icc 0 a ⊆ Set.Ici (0 : ℝ) := fun z hz => hz.1
        have hmono : MonotoneOn f (Set.Icc 0 a) := by
          refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 a) (hcont.mono hsub)
            (foc_hasDerivWithin_interior hf hsub) ?_
          intro x hx
          rw [interior_Icc] at hx
          rw [← heq hapos]
          exact hanti hx.1.le ha hx.2.le
        exact hmono ⟨hy, hya⟩ ⟨ha, le_rfl⟩ hya

/-- The tangent-line inequality on `[0, ∞)` for a function with antitone derivative:
`f(y) ≤ f(x) + f'(x)(y - x)` for all `x, y ≥ 0`. -/
theorem foc_tangent_le {f f' : ℝ → ℝ}
    (hf : ∀ x ∈ Set.Ici (0 : ℝ), HasDerivWithinAt f (f' x) (Set.Ici 0) x)
    (hanti : AntitoneOn f' (Set.Ici 0)) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    f y ≤ f x + f' x * (y - x) := by
  have hg : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt (fun z => f z - f' x * z) (f' z - f' x) (Set.Ici 0) z := by
    intro z hz
    have h := (hf z hz).sub ((hasDerivWithinAt_id z (Set.Ici (0 : ℝ))).const_mul (f' x))
    rw [mul_one] at h
    exact h
  have hganti : AntitoneOn (fun z => f' z - f' x) (Set.Ici 0) :=
    fun a ha b hb hab => by simpa using hanti ha hb hab
  have := ((foc_max_iff hg hganti hx).2 ⟨by simp, fun _ => by simp⟩) y hy
  linarith

/-- The tangent-line inequality for a function with monotone derivative on `[0, ∞)`:
`f(x) + f'(x)(y - x) ≤ f(y)`. -/
theorem foc_le_tangent_convex {f f' : ℝ → ℝ}
    (hf : ∀ x ∈ Set.Ici (0 : ℝ), HasDerivWithinAt f (f' x) (Set.Ici 0) x)
    (hmono : MonotoneOn f' (Set.Ici 0)) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    f x + f' x * (y - x) ≤ f y := by
  have h := foc_tangent_le (f := fun z => -f z) (f' := fun z => -f' z)
    (fun z hz => (hf z hz).neg) (fun a ha b hb hab => neg_le_neg (hmono ha hb hab)) hx hy
  linarith

/-! ## The solution of `d(x) ≤ r` with equality if `x > 0` -/

/-- The Kuhn-Tucker condition "`x ≥ 0`, `d(x) ≤ r`, with equality if `x > 0`" for a
marginal-benefit function `d` and a price `r` (conditions (10.C.1)-(10.C.2), MWG, p. 318). -/
def IsFOCSol (d : ℝ → ℝ) (r x : ℝ) : Prop :=
  0 ≤ x ∧ d x ≤ r ∧ (0 < x → d x = r)

/-- For strictly decreasing `d` on `[0, ∞)` the condition has at most one solution. -/
theorem isFOCSol_unique {d : ℝ → ℝ} (hd : StrictAntiOn d (Set.Ici 0)) {r x y : ℝ}
    (hx : IsFOCSol d r x) (hy : IsFOCSol d r y) : x = y := by
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · have h1 := hy.2.2 (hx.1.trans_lt hxy)
    have h2 := hd hx.1 hy.1 hxy
    linarith [hx.2.1]
  · exact hxy
  · have h1 := hx.2.2 (hy.1.trans_lt hxy)
    have h2 := hd hy.1 hx.1 hxy
    linarith [hy.2.1]

/-- Existence of the solution for continuous `d` once `d(y) ≤ r` for some `y ≥ 0`
(intermediate value theorem). -/
theorem isFOCSol_exists {d : ℝ → ℝ} (hcont : ContinuousOn d (Set.Ici 0)) {r : ℝ}
    (hr : ∃ y, 0 ≤ y ∧ d y ≤ r) : ∃ x, IsFOCSol d r x := by
  by_cases h0 : d 0 ≤ r
  · exact ⟨0, le_rfl, h0, fun h => absurd h (lt_irrefl 0)⟩
  · push Not at h0
    obtain ⟨y, hy, hyr⟩ := hr
    have hy0 : 0 ≤ y := hy
    obtain ⟨x, hx, hxr⟩ := intermediate_value_Icc' hy0 (hcont.mono Set.Icc_subset_Ici_self)
      ⟨hyr, h0.le⟩
    exact ⟨x, hx.1, hxr.le, fun _ => hxr⟩

open Classical in
/-- The solution of the Kuhn-Tucker condition (`0` when there is none). -/
noncomputable def focSol (d : ℝ → ℝ) (r : ℝ) : ℝ :=
  if h : ∃ x, IsFOCSol d r x then h.choose else 0

/-- `focSol d r` solves the condition whenever a solution exists. -/
theorem focSol_spec {d : ℝ → ℝ} {r : ℝ} (h : ∃ x, IsFOCSol d r x) :
    IsFOCSol d r (focSol d r) := by
  rw [focSol, dite_eq_left_of_eq_true (eq_true h)]
  exact h.choose_spec

/-- `focSol d r` is the solution. -/
theorem focSol_eq {d : ℝ → ℝ} (hd : StrictAntiOn d (Set.Ici 0)) {r x : ℝ}
    (hx : IsFOCSol d r x) : focSol d r = x :=
  isFOCSol_unique hd (focSol_spec ⟨x, hx⟩) hx

/-- The solution is zero exactly when `d(0) ≤ r`. -/
theorem focSol_eq_zero_iff {d : ℝ → ℝ} (hd : StrictAntiOn d (Set.Ici 0)) {r : ℝ}
    (h : ∃ x, IsFOCSol d r x) : focSol d r = 0 ↔ d 0 ≤ r := by
  constructor
  · intro h0
    have := (focSol_spec h).2.1
    rwa [h0] at this
  · intro h0
    exact focSol_eq hd ⟨le_rfl, h0, fun h => absurd h (lt_irrefl 0)⟩

/-- The solution is positive exactly when `r < d(0)`. -/
theorem focSol_pos_iff {d : ℝ → ℝ} (hd : StrictAntiOn d (Set.Ici 0)) {r : ℝ}
    (h : ∃ x, IsFOCSol d r x) : 0 < focSol d r ↔ r < d 0 := by
  have hs := focSol_spec h
  rw [← not_le, ← not_le, iff_not_comm, not_not, ← focSol_eq_zero_iff hd h]
  constructor
  · intro h0; exact le_of_eq h0
  · intro h0; exact le_antisymm h0 hs.1

/-- At a positive solution, `d(focSol d r) = r`. -/
theorem focSol_eq_of_pos {d : ℝ → ℝ} {r : ℝ} (h : ∃ x, IsFOCSol d r x)
    (hpos : 0 < focSol d r) : d (focSol d r) = r :=
  (focSol_spec h).2.2 hpos

/-- The solution is antitone in `r`. -/
theorem focSol_antitone {d : ℝ → ℝ} (hd : StrictAntiOn d (Set.Ici 0)) {r₁ r₂ : ℝ}
    (h₁ : ∃ x, IsFOCSol d r₁ x) (h₂ : ∃ x, IsFOCSol d r₂ x) (hr : r₁ ≤ r₂) :
    focSol d r₂ ≤ focSol d r₁ := by
  have s₁ := focSol_spec h₁
  have s₂ := focSol_spec h₂
  by_contra hlt
  push Not at hlt
  have e₂ := s₂.2.2 (s₁.1.trans_lt hlt)
  have := hd s₁.1 s₂.1 hlt
  linarith [s₁.2.1]

/-- The solution is strictly decreasing in `r` while positive. -/
theorem focSol_strictAnti {d : ℝ → ℝ} (hd : StrictAntiOn d (Set.Ici 0)) {r₁ r₂ : ℝ}
    (h₁ : ∃ x, IsFOCSol d r₁ x) (h₂ : ∃ x, IsFOCSol d r₂ x) (hr : r₁ < r₂)
    (hpos : 0 < focSol d r₁) : focSol d r₂ < focSol d r₁ := by
  refine lt_of_le_of_ne (focSol_antitone hd h₁ h₂ hr.le) fun heq => ?_
  have e₁ := (focSol_spec h₁).2.2 hpos
  have e₂ := (focSol_spec h₂).2.2 (heq ▸ hpos)
  rw [heq] at e₂
  linarith

/-- **Continuity of the solution** in `r` at every `r₀` near which solutions exist. -/
theorem focSol_continuousAt {d : ℝ → ℝ} (hd : StrictAntiOn d (Set.Ici 0)) {r₀ : ℝ}
    (hex : ∀ᶠ r in 𝓝 r₀, ∃ x, IsFOCSol d r x) : ContinuousAt (focSol d) r₀ := by
  have s₀ := focSol_spec hex.self_of_nhds
  set x₀ := focSol d r₀ with hx₀
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · by_cases ha0 : a < 0
    · filter_upwards [hex] with r hr
      exact ha0.trans_le (focSol_spec hr).1
    · push Not at ha0
      have hx0pos : 0 < x₀ := ha0.trans_lt ha
      have e₀ := s₀.2.2 hx0pos
      have hda : d x₀ < d a := hd ha0 s₀.1 ha
      filter_upwards [hex, gt_mem_nhds (e₀ ▸ hda : r₀ < d a)] with r hr hra
      by_contra hle
      push Not at hle
      have hs := focSol_spec hr
      have : d a ≤ d (focSol d r) := hd.antitoneOn hs.1 ha0 hle
      linarith [hs.2.1]
  · have hb0 : 0 ≤ b := s₀.1.trans hb.le
    have hdb : d b < d x₀ := hd s₀.1 hb0 hb
    filter_upwards [hex, lt_mem_nhds (hdb.trans_le s₀.2.1 : d b < r₀)] with r hr hrb
    by_contra hle
    push Not at hle
    have hs := focSol_spec hr
    have e := hs.2.2 ((s₀.1.trans_lt hb).trans_le hle)
    have : d (focSol d r) ≤ d b := hd.antitoneOn hb0 hs.1 hle
    linarith

/-- **Derivative of the solution** (MWG, p. 319: `x_i'(p) = 1/φ_i''(x_i(p))`). If the solution
is positive at `r₀ < d(0)`, solutions exist near `r₀`, and `d` has a nonzero derivative `d'` at
the solution, then `focSol d` has derivative `1/d'` at `r₀`. -/
theorem focSol_hasDerivAt {d : ℝ → ℝ} (hd : StrictAntiOn d (Set.Ici 0)) {r₀ d' : ℝ}
    (hex : ∀ᶠ r in 𝓝 r₀, ∃ x, IsFOCSol d r x) (hr₀ : r₀ < d 0)
    (hder : HasDerivAt d d' (focSol d r₀)) (hd' : d' ≠ 0) :
    HasDerivAt (focSol d) d'⁻¹ r₀ := by
  refine HasDerivAt.of_local_left_inverse (focSol_continuousAt hd hex) hder hd' ?_
  filter_upwards [hex, gt_mem_nhds hr₀] with r hr hr0
  exact focSol_eq_of_pos hr ((focSol_pos_iff hd hr).2 hr0)

/-- **A sandwich criterion for derivatives** (used for the envelope arguments of Sections 10.C
and 10.E). If the remainder `f(y) - f(a) - (y - a)d` lies between two functions that are
`o(y - a)`, then `f` has derivative `d` at `a`. -/
theorem hasDerivAt_of_sandwich {f e₁ e₂ : ℝ → ℝ} {a d : ℝ}
    (h₁ : e₁ =o[𝓝 a] fun y => y - a) (h₂ : e₂ =o[𝓝 a] fun y => y - a)
    (hb : ∀ᶠ y in 𝓝 a, e₁ y ≤ f y - f a - (y - a) * d ∧ f y - f a - (y - a) * d ≤ e₂ y) :
    HasDerivAt f d a := by
  rw [hasDerivAt_iff_isLittleO]
  have hsum : (fun y => ‖e₁ y‖ + ‖e₂ y‖) =o[𝓝 a] fun y => y - a :=
    h₁.norm_left.add h₂.norm_left
  refine Asymptotics.IsBigO.trans_isLittleO (Asymptotics.IsBigO.of_bound' ?_) hsum
  filter_upwards [hb] with y hy
  simp only [smul_eq_mul, Real.norm_eq_abs]
  rw [abs_of_nonneg (a := |e₁ y| + |e₂ y|) (add_nonneg (abs_nonneg _) (abs_nonneg _)), abs_le]
  constructor
  · linarith [neg_abs_le (e₁ y), abs_nonneg (e₂ y)]
  · linarith [le_abs_self (e₂ y), abs_nonneg (e₁ y)]

/-- The remainder of a function with derivative `d` at `a` is `o(y - a)`. -/
theorem remainder_isLittleO {f : ℝ → ℝ} {a d : ℝ} (hf : HasDerivAt f d a) :
    (fun y => f y - f a - (y - a) * d) =o[𝓝 a] fun y => y - a := by
  have := hasDerivAt_iff_isLittleO.1 hf
  simpa [smul_eq_mul] using this

end MWG.CompetitiveMarkets

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Pareto optimality and competitive equilibria (MWG Section 10.B, pp. 312-316)

An economy has consumers `i : ι`, firms `j : κ` and `L` goods. Consumer `i` has consumption set
`Xᵢ ⊆ ℝ^L` and utility `uᵢ`; firm `j` has production set `Yⱼ ⊆ ℝ^L`; `ω` is the total
endowment.

* **Definition 10.B.1**: allocations and feasibility (`Economy.IsFeasible`).
* **Definition 10.B.2**: Pareto optimality (`Economy.IsParetoOptimal`), the utility possibility
  set `U` (p. 313) and the fact that Pareto optimal allocations are exactly those whose utility
  vector is undominated in `U` (`isParetoOptimal_iff_undominated`).
* **Definition 10.B.3**: competitive (Walrasian) equilibrium of a private ownership economy
  (`PrivEconomy.IsCompetitiveEqm`). Profit maximization is membership in Chapter 5's supply
  correspondence `supply Yⱼ p` and utility maximization is membership in Chapter 3's demand
  `walrasianDemandOn Xᵢ uᵢ p w` with wealth `p·ωᵢ + ∑ⱼ θᵢⱼ p·yⱼ`.
* **Exercise 10.B.2** (p. 316): equilibria are invariant to scaling prices by `α > 0` (we do not
  need `p ≫ 0`).
* **Lemma 10.B.1** (p. 316): with `p ≫ 0`, budgets holding with equality and shares summing to
  one, clearing of all markets but one implies clearing of the last.
* **Exercise 10.B.1** (p. 344): strong and weak Pareto efficiency. (a) strong implies weak;
  (b) with `Xᵢ = ℝ^L_+`, continuous and strongly monotone utilities the notions coincide. We
  prove (b) without the interiority assumption (`exercise_10_B_1b_general`), so interiority is
  not needed (part of the answer to (c)); (c) an example where they differ when strong
  monotonicity fails.
-/

namespace MWG.CompetitiveMarkets

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.Production Kreps.PreferenceProperties

/-- **Section 10.B** (MWG, p. 312). An economy: consumption sets `Xᵢ`, utilities `uᵢ`, the
total endowment `ω` and production sets `Yⱼ`. -/
structure Economy (ι κ : Type*) (L : ℕ) where
  /-- Consumption sets. -/
  X : ι → Set (Fin L → ℝ)
  /-- Utility functions. -/
  u : ι → (Fin L → ℝ) → ℝ
  /-- Total endowment. -/
  ω : Fin L → ℝ
  /-- Production sets. -/
  Y : κ → Set (Fin L → ℝ)

/-- **Definition 10.B.1** (MWG, p. 312). An economic allocation: consumption vectors `xᵢ` and
production vectors `yⱼ`. -/
structure Allocation (ι κ : Type*) (L : ℕ) where
  /-- Consumption vectors. -/
  x : ι → Fin L → ℝ
  /-- Production vectors. -/
  y : κ → Fin L → ℝ

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {L : ℕ}

/-- **Definition 10.B.1** (MWG, p. 312). `xᵢ ∈ Xᵢ` and `yⱼ ∈ Yⱼ`. -/
def Economy.IsAllocation (E : Economy ι κ L) (a : Allocation ι κ L) : Prop :=
  (∀ i, a.x i ∈ E.X i) ∧ ∀ j, a.y j ∈ E.Y j

/-- **Definition 10.B.1** (MWG, p. 312). A feasible allocation:
`∑ᵢ x_{ℓi} ≤ ω_ℓ + ∑ⱼ y_{ℓj}` for every good `ℓ`. -/
def Economy.IsFeasible (E : Economy ι κ L) (a : Allocation ι κ L) : Prop :=
  E.IsAllocation a ∧ ∀ l, ∑ i, a.x i l ≤ E.ω l + ∑ j, a.y j l

/-- **Definition 10.B.2** (MWG, p. 313). A feasible allocation is Pareto optimal if no feasible
allocation makes every consumer weakly and some consumer strictly better off. -/
def Economy.IsParetoOptimal (E : Economy ι κ L) (a : Allocation ι κ L) : Prop :=
  E.IsFeasible a ∧ ¬ ∃ a', E.IsFeasible a' ∧ (∀ i, E.u i (a.x i) ≤ E.u i (a'.x i)) ∧
    ∃ i, E.u i (a.x i) < E.u i (a'.x i)

/-- **Definition 10.B.1** (MWG, p. 312), unfolded. -/
theorem definition_10_B_1 (E : Economy ι κ L) (a : Allocation ι κ L) :
    E.IsFeasible a ↔ (∀ i, a.x i ∈ E.X i) ∧ (∀ j, a.y j ∈ E.Y j) ∧
      ∀ l, ∑ i, a.x i l ≤ E.ω l + ∑ j, a.y j l := by
  unfold Economy.IsFeasible Economy.IsAllocation
  tauto

/-- **Definition 10.B.2** (MWG, p. 313), unfolded. -/
theorem definition_10_B_2 (E : Economy ι κ L) (a : Allocation ι κ L) :
    E.IsParetoOptimal a ↔ E.IsFeasible a ∧ ∀ a', E.IsFeasible a' →
      (∀ i, E.u i (a.x i) ≤ E.u i (a'.x i)) → ∀ i, E.u i (a'.x i) ≤ E.u i (a.x i) := by
  unfold Economy.IsParetoOptimal
  constructor
  · rintro ⟨h, hno⟩
    exact ⟨h, fun a' ha' hle i => not_lt.1 fun hlt => hno ⟨a', ha', hle, i, hlt⟩⟩
  · rintro ⟨h, hall⟩
    exact ⟨h, fun ⟨a', ha', hle, i, hlt⟩ => absurd (hall a' ha' hle i) (not_le.2 hlt)⟩

/-- **Section 10.B** (MWG, p. 313). The utility possibility set
`U = {v : ∃ feasible allocation with vᵢ ≤ uᵢ(xᵢ) for all i}` (the book writes it for `I = 2`). -/
def Economy.utilityPossibilitySet (E : Economy ι κ L) : Set (ι → ℝ) :=
  {v | ∃ a, E.IsFeasible a ∧ ∀ i, v i ≤ E.u i (a.x i)}

/-- **Section 10.B** (MWG, p. 313, Figure 10.B.1). A feasible allocation is Pareto optimal if and
only if its utility vector lies on the "northeast boundary" of `U`: no element of `U` weakly
dominates it with a strict improvement for someone. -/
theorem isParetoOptimal_iff_undominated (E : Economy ι κ L) (a : Allocation ι κ L)
    (ha : E.IsFeasible a) :
    E.IsParetoOptimal a ↔ ∀ v ∈ E.utilityPossibilitySet, (∀ i, E.u i (a.x i) ≤ v i) →
      ∀ i, v i = E.u i (a.x i) := by
  constructor
  · rintro ⟨-, hno⟩ v ⟨a', ha', hv⟩ hle i
    by_contra hne
    exact hno ⟨a', ha', fun k => (hle k).trans (hv k),
      ⟨i, lt_of_lt_of_le (lt_of_le_of_ne (hle i) (Ne.symm hne)) (hv i)⟩⟩
  · intro h
    refine ⟨ha, ?_⟩
    rintro ⟨a', ha', hle, i, hi⟩
    have := h (fun k => E.u k (a'.x k)) ⟨a', ha', fun k => le_rfl⟩ hle i
    exact (ne_of_gt hi) this

/-- The utility vector of a feasible allocation lies in `U`. -/
theorem mem_utilityPossibilitySet (E : Economy ι κ L) {a : Allocation ι κ L}
    (ha : E.IsFeasible a) : (fun i => E.u i (a.x i)) ∈ E.utilityPossibilitySet :=
  ⟨a, ha, fun _ => le_rfl⟩

/-- **Section 10.B** (MWG, p. 314). A private ownership economy: consumption sets, utilities,
production sets, individual endowments `ωᵢ` and profit shares `θᵢⱼ`. -/
structure PrivEconomy (ι κ : Type*) (L : ℕ) where
  /-- Consumption sets. -/
  X : ι → Set (Fin L → ℝ)
  /-- Utility functions. -/
  u : ι → (Fin L → ℝ) → ℝ
  /-- Production sets. -/
  Y : κ → Set (Fin L → ℝ)
  /-- Individual endowments `ωᵢ`. -/
  ωi : ι → Fin L → ℝ
  /-- Profit shares `θᵢⱼ`. -/
  θ : ι → κ → ℝ

/-- The underlying economy, with total endowment `ω = ∑ᵢ ωᵢ` (MWG, p. 314). -/
def PrivEconomy.toEconomy (E : PrivEconomy ι κ L) : Economy ι κ L where
  X := E.X
  u := E.u
  ω := ∑ i, E.ωi i
  Y := E.Y

/-- Consumer `i`'s wealth `p·ωᵢ + ∑ⱼ θᵢⱼ p·yⱼ` (MWG, p. 314, (10.B.2)). -/
def PrivEconomy.wealth (E : PrivEconomy ι κ L) (a : Allocation ι κ L) (p : Fin L → ℝ)
    (i : ι) : ℝ :=
  p ⬝ᵥ E.ωi i + ∑ j, E.θ i j * (p ⬝ᵥ a.y j)

/-- **Definition 10.B.3** (MWG, p. 314). A competitive (Walrasian) equilibrium: (i) every `yⱼ`
maximizes profit on `Yⱼ` (Chapter 5's `supply`), (ii) every `xᵢ` maximizes `uᵢ` on the budget set
in `Xᵢ` (Chapter 3's `walrasianDemandOn`), (iii) every market clears with equality (10.B.3). -/
def PrivEconomy.IsCompetitiveEqm (E : PrivEconomy ι κ L) (a : Allocation ι κ L)
    (p : Fin L → ℝ) : Prop :=
  (∀ j, a.y j ∈ supply (E.Y j) p) ∧
  (∀ i, a.x i ∈ walrasianDemandOn (E.X i) (E.u i) p (E.wealth a p i)) ∧
  ∀ l, ∑ i, a.x i l = ∑ i, E.ωi i l + ∑ j, a.y j l

/-- **Definition 10.B.3** (MWG, p. 314), unfolded into (10.B.1)-(10.B.3). -/
theorem definition_10_B_3 (E : PrivEconomy ι κ L) (a : Allocation ι κ L) (p : Fin L → ℝ) :
    E.IsCompetitiveEqm a p ↔
      (∀ j, a.y j ∈ E.Y j ∧ ∀ y ∈ E.Y j, p ⬝ᵥ y ≤ p ⬝ᵥ a.y j) ∧
      (∀ i, (a.x i ∈ E.X i ∧ p ⬝ᵥ a.x i ≤ E.wealth a p i) ∧
        ∀ x ∈ E.X i, p ⬝ᵥ x ≤ E.wealth a p i → E.u i x ≤ E.u i (a.x i)) ∧
      ∀ l, ∑ i, a.x i l = ∑ i, E.ωi i l + ∑ j, a.y j l := by
  unfold PrivEconomy.IsCompetitiveEqm supply walrasianDemandOn budgetSetOn
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, fun i => ⟨(h2 i).1, fun x hx hb => (h2 i).2 x ⟨hx, hb⟩⟩, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, fun i => ⟨(h2 i).1, fun x hx => (h2 i).2 x hx.1 hx.2⟩, h3⟩

/-- A competitive equilibrium allocation is feasible (market clearing (10.B.3) gives
feasibility (Definition 10.B.1)). -/
theorem PrivEconomy.IsCompetitiveEqm.isFeasible {E : PrivEconomy ι κ L}
    {a : Allocation ι κ L} {p : Fin L → ℝ} (h : E.IsCompetitiveEqm a p) :
    E.toEconomy.IsFeasible a := by
  refine ⟨⟨fun i => (h.2.1 i).1.1, fun j => (h.1 j).1⟩, fun l => ?_⟩
  simp only [PrivEconomy.toEconomy, Finset.sum_apply]
  exact (h.2.2 l).le

/-- **Exercise 10.B.2** (MWG, p. 344; p. 316). If `(x*, y*)` and `p*` form a competitive
equilibrium, so do `(x*, y*)` and `αp*` for every `α > 0`. (The book assumes `p* ≫ 0`; this is
not needed.) -/
theorem exercise_10_B_2 (E : PrivEconomy ι κ L) (a : Allocation ι κ L) (p : Fin L → ℝ)
    (h : E.IsCompetitiveEqm a p) {α : ℝ} (hα : 0 < α) : E.IsCompetitiveEqm a (α • p) := by
  rw [definition_10_B_3] at h ⊢
  obtain ⟨h1, h2, h3⟩ := h
  have hw : ∀ i, E.wealth a (α • p) i = α * E.wealth a p i := by
    intro i
    simp only [PrivEconomy.wealth, smul_dotProduct, smul_eq_mul, mul_add, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  refine ⟨fun j => ⟨(h1 j).1, fun y hy => ?_⟩, fun i => ⟨⟨(h2 i).1.1, ?_⟩, fun x hx hb => ?_⟩, h3⟩
  · simp only [smul_dotProduct, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left ((h1 j).2 y hy) hα.le
  · rw [hw, smul_dotProduct, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (h2 i).1.2 hα.le
  · rw [hw, smul_dotProduct, smul_eq_mul] at hb
    exact (h2 i).2 x hx (le_of_mul_le_mul_left hb hα)

/-- **Lemma 10.B.1** (MWG, p. 316). Let `p` have `p_k > 0` (the book assumes `p ≫ 0`), let the
shares of each firm sum to one, let every budget constraint hold with equality and let every
market `ℓ ≠ k` clear. Then market `k` clears. -/
theorem lemma_10_B_1 (E : PrivEconomy ι κ L) (a : Allocation ι κ L) (p : Fin L → ℝ) (k : Fin L)
    (hpk : 0 < p k) (hθ : ∀ j, ∑ i, E.θ i j = 1)
    (hbudget : ∀ i, p ⬝ᵥ a.x i = E.wealth a p i)
    (hclear : ∀ l, l ≠ k → ∑ i, a.x i l = ∑ i, E.ωi i l + ∑ j, a.y j l) :
    ∑ i, a.x i k = ∑ i, E.ωi i k + ∑ j, a.y j k := by
  set z : Fin L → ℝ := ∑ i, a.x i - ∑ i, E.ωi i - ∑ j, a.y j with hz
  have hzl : ∀ l, z l = ∑ i, a.x i l - ∑ i, E.ωi i l - ∑ j, a.y j l := fun l => by
    simp [hz, Finset.sum_apply]
  have htot : p ⬝ᵥ z = 0 := by
    rw [hz, dotProduct_sub, dotProduct_sub, dotProduct_sum, dotProduct_sum, dotProduct_sum,
      Finset.sum_congr rfl fun i _ => hbudget i]
    unfold PrivEconomy.wealth
    rw [Finset.sum_add_distrib, Finset.sum_comm (f := fun i j => E.θ i j * (p ⬝ᵥ a.y j))]
    simp only [← Finset.sum_mul, hθ, one_mul]
    ring
  have hzero : ∀ l, l ≠ k → z l = 0 := fun l hl => by rw [hzl, hclear l hl]; ring
  have hk : p ⬝ᵥ z = p k * z k := by
    unfold dotProduct
    rw [Finset.sum_eq_single k (fun l _ hl => by rw [hzero l hl, mul_zero])
      (fun h => absurd (Finset.mem_univ k) h)]
  rw [hk] at htot
  have := (mul_eq_zero.1 htot).resolve_left hpk.ne'
  rw [hzl] at this
  linarith

/-- **Lemma 10.B.1** (MWG, p. 316) with the book's hypothesis `p ≫ 0`. -/
theorem lemma_10_B_1_strictlyPositive (E : PrivEconomy ι κ L) (a : Allocation ι κ L)
    (p : Fin L → ℝ) (hp : StrictlyPositive p) (k : Fin L) (hθ : ∀ j, ∑ i, E.θ i j = 1)
    (hbudget : ∀ i, p ⬝ᵥ a.x i = E.wealth a p i)
    (hclear : ∀ l, l ≠ k → ∑ i, a.x i l = ∑ i, E.ωi i l + ∑ j, a.y j l) :
    ∑ i, a.x i k = ∑ i, E.ωi i k + ∑ j, a.y j k :=
  lemma_10_B_1 E a p k (hp k) hθ hbudget hclear

/-! ## Exercise 10.B.1: strong and weak Pareto efficiency -/

/-- **Exercise 10.B.1** (MWG, p. 344). Weak Pareto efficiency: no feasible allocation makes all
consumers strictly better off. -/
def Economy.IsWeaklyParetoOptimal (E : Economy ι κ L) (a : Allocation ι κ L) : Prop :=
  E.IsFeasible a ∧ ¬ ∃ a', E.IsFeasible a' ∧ ∀ i, E.u i (a.x i) < E.u i (a'.x i)

/-- **Exercise 10.B.1(a)** (MWG, p. 344). A strongly Pareto efficient allocation (Definition
10.B.2) is weakly Pareto efficient (there is at least one consumer). -/
theorem exercise_10_B_1a [Nonempty ι] (E : Economy ι κ L) (a : Allocation ι κ L)
    (h : E.IsParetoOptimal a) : E.IsWeaklyParetoOptimal a := by
  refine ⟨h.1, fun ⟨a', ha', hlt⟩ => h.2 ⟨a', ha', fun i => (hlt i).le, ?_⟩⟩
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact ⟨i, hlt i⟩

/-- **Exercise 10.B.1(b)** (MWG, p. 344), without interiority. If every `Xᵢ = ℝ^L_+` and every
`uᵢ` is continuous on `ℝ^L_+` and strongly monotone, then a weakly Pareto efficient allocation is
strongly Pareto efficient. -/
theorem exercise_10_B_1b_general (E : Economy ι κ L)
    (hX : ∀ i, E.X i = nonnegOrthant L) (hcont : ∀ i, ContinuousOn (E.u i) (nonnegOrthant L))
    (hmono : ∀ i, PrefStronglyMonotone (nonnegOrthant L) (utilityPref (E.u i)))
    (a : Allocation ι κ L) (h : E.IsWeaklyParetoOptimal a) : E.IsParetoOptimal a := by
  classical
  refine ⟨h.1, ?_⟩
  rintro ⟨a', ha', hle, i₀, hi₀⟩
  apply h.2
  have hmem : ∀ i, a'.x i ∈ nonnegOrthant L := fun i => hX i ▸ ha'.1.1 i
  have hmemA : ∀ i, a.x i ∈ nonnegOrthant L := fun i => hX i ▸ h.1.1.1 i
  -- strict utility comparisons from strong monotonicity
  have hsm : ∀ i, ∀ x y : Fin L → ℝ, x ∈ nonnegOrthant L → y ∈ nonnegOrthant L → x ≤ y →
      y ≠ x → E.u i x < E.u i y := by
    intro i x y hx hy hxy hne
    have := hmono i x hx y hy hxy hne
    exact lt_of_not_ge this.2
  -- `a'.x i₀ ≠ 0`
  have hne0 : a'.x i₀ ≠ 0 := by
    intro h0
    have h00 : (0 : Fin L → ℝ) ∈ nonnegOrthant L := fun _ => le_rfl
    have hle0 : E.u i₀ 0 ≤ E.u i₀ (a.x i₀) := by
      by_cases he : a.x i₀ = 0
      · rw [he]
      · exact (hsm i₀ 0 (a.x i₀) h00 (hmemA i₀) (hmemA i₀) he).le
    rw [h0] at hi₀
    linarith
  by_cases hcard : Fintype.card ι = 1
  · refine ⟨a', ha', fun i => ?_⟩
    have : i = i₀ := Fintype.card_le_one_iff.1 hcard.le i i₀
    rw [this]; exact hi₀
  -- continuity along the ray `t ↦ (1 - t) • a'.x i₀`
  have hray : ContinuousWithinAt (fun t : ℝ => E.u i₀ ((1 - t) • a'.x i₀)) (Set.Icc 0 1) 0 := by
    have hmap : Set.MapsTo (fun t : ℝ => (1 - t) • a'.x i₀) (Set.Icc 0 1) (nonnegOrthant L) := by
      intro t ht l
      simp only [Pi.smul_apply, smul_eq_mul]
      exact mul_nonneg (by linarith [ht.2]) (hmem i₀ l)
    have hc : ContinuousWithinAt (fun t : ℝ => (1 - t) • a'.x i₀) (Set.Icc 0 1) 0 :=
      ((continuous_const.sub continuous_id).smul continuous_const).continuousWithinAt
    have h0mem : (fun t : ℝ => (1 - t) • a'.x i₀) 0 ∈ nonnegOrthant L := hmap ⟨le_rfl, zero_le_one⟩
    exact ContinuousWithinAt.comp (f := fun t : ℝ => (1 - t) • a'.x i₀) (hcont i₀ _ h0mem) hc hmap
  have hev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Icc 0 1),
      E.u i₀ (a.x i₀) < E.u i₀ ((1 - t) • a'.x i₀) := by
    have := hray.eventually (lt_mem_nhds (by simpa using hi₀))
    exact this
  have hev2 : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioc 0 1),
      E.u i₀ (a.x i₀) < E.u i₀ ((1 - t) • a'.x i₀) :=
    nhdsWithin_mono _ Set.Ioc_subset_Icc_self hev
  have hne : (nhdsWithin (0 : ℝ) (Set.Ioc 0 1)).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioc zero_ne_one]
    exact ⟨le_rfl, zero_le_one⟩
  obtain ⟨δ, hδu, hδ⟩ := (hev2.and self_mem_nhdsWithin).exists
  have hn : (1 : ℝ) < Fintype.card ι := by
    have : 1 < Fintype.card ι := by
      have := (Fintype.card_pos_iff.2 ⟨i₀⟩ : 0 < Fintype.card ι)
      omega
    exact_mod_cast this
  set c : ℝ := δ / (Fintype.card ι - 1) with hc
  have hc0 : 0 < c := div_pos hδ.1 (by linarith)
  set coeff : ι → ℝ := fun i => c - (if i = i₀ then c + δ else 0) with hcoeff
  refine ⟨⟨fun i => a'.x i + coeff i • a'.x i₀, a'.y⟩, ⟨⟨fun i => ?_, ha'.1.2⟩, fun l => ?_⟩, ?_⟩
  · rw [hX i]
    intro l
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hcoeff]
    by_cases hi : i = i₀
    · subst hi
      simp only [↓reduceIte]
      have : a'.x i l + (c - (c + δ)) * a'.x i l = (1 - δ) * a'.x i l := by ring
      rw [this]
      exact mul_nonneg (by linarith [hδ.2]) (hmem i l)
    · simp only [hi, ↓reduceIte, sub_zero]
      exact add_nonneg (hmem i l) (mul_nonneg hc0.le (hmem i₀ l))
  · have hsum : ∑ i, coeff i = 0 := by
      simp only [hcoeff, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, nsmul_eq_mul, hc]
      have hn1 : (Fintype.card ι : ℝ) - 1 ≠ 0 := by linarith
      field_simp
      ring
    have : ∑ i, (a'.x i + coeff i • a'.x i₀) l = ∑ i, a'.x i l + (∑ i, coeff i) * a'.x i₀ l := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, Finset.sum_mul]
    rw [this, hsum, zero_mul, add_zero]
    exact ha'.2 l
  · intro i
    by_cases hi : i = i₀
    · subst hi
      have : a'.x i + coeff i • a'.x i = (1 - δ) • a'.x i := by
        simp only [hcoeff, ↓reduceIte]
        ext l
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      simp only
      rw [this]
      exact hδu
    · simp only
      have hco : coeff i = c := by simp [hcoeff, hi]
      rw [hco]
      refine (hle i).trans_lt (hsm i _ _ (hmem i) ?_ ?_ ?_)
      · intro l
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        exact add_nonneg (hmem i l) (mul_nonneg hc0.le (hmem i₀ l))
      · intro l
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        linarith [mul_nonneg hc0.le (hmem i₀ l)]
      · intro heq
        apply hne0
        have h2 : c • a'.x i₀ = 0 := by
          have := congrArg (fun v => v - a'.x i) heq
          simpa using this
        exact (smul_eq_zero.1 h2).resolve_left hc0.ne'

/-- **Exercise 10.B.1(b)** (MWG, p. 344), as stated: for an interior outcome (every `xᵢ ≫ 0`)
with `Xᵢ = ℝ^L_+` and continuous strongly monotone utilities, strong and weak Pareto efficiency
are equivalent. -/
theorem exercise_10_B_1b [Nonempty ι] (E : Economy ι κ L)
    (hX : ∀ i, E.X i = nonnegOrthant L) (hcont : ∀ i, ContinuousOn (E.u i) (nonnegOrthant L))
    (hmono : ∀ i, PrefStronglyMonotone (nonnegOrthant L) (utilityPref (E.u i)))
    (a : Allocation ι κ L) (_hint : ∀ i l, 0 < a.x i l) :
    E.IsParetoOptimal a ↔ E.IsWeaklyParetoOptimal a :=
  ⟨exercise_10_B_1a E a, exercise_10_B_1b_general E hX hcont hmono a⟩

/-- The economy of Exercise 10.B.1(c): one good, two consumers, one firm with `Y = {0}`, total
endowment `1`; consumer `0` is indifferent among all bundles (`u₀ = 0`), consumer `1` has
`u₁(x) = x`. -/
def exercise_10_B_1c_economy : Economy (Fin 2) (Fin 1) 1 where
  X := fun _ => nonnegOrthant 1
  u := fun i x => if i = 0 then 0 else x 0
  ω := fun _ => 1
  Y := fun _ => {0}

/-- **Exercise 10.B.1(c)** (MWG, p. 344). The two notions differ without strong monotonicity:
giving the whole endowment to the indifferent consumer is weakly but not strongly Pareto
efficient. (Interiority alone does not matter: `exercise_10_B_1b_general`.) -/
theorem exercise_10_B_1c :
    exercise_10_B_1c_economy.IsWeaklyParetoOptimal ⟨fun i _ => if i = 0 then 1 else 0, 0⟩ ∧
    ¬ exercise_10_B_1c_economy.IsParetoOptimal ⟨fun i _ => if i = 0 then 1 else 0, 0⟩ := by
  have hfeas : exercise_10_B_1c_economy.IsFeasible ⟨fun i _ => if i = 0 then 1 else 0, 0⟩ := by
    refine ⟨⟨fun i l => ?_, fun j => rfl⟩, fun l => ?_⟩
    · change (0 : ℝ) ≤ if i = 0 then 1 else 0
      split_ifs <;> norm_num
    · simp [exercise_10_B_1c_economy]
  refine ⟨⟨hfeas, ?_⟩, ?_⟩
  · rintro ⟨a', -, h⟩
    have := h 0
    simp [exercise_10_B_1c_economy] at this
  · rintro ⟨-, hno⟩
    apply hno
    refine ⟨⟨fun i _ => if i = 0 then 0 else 1, 0⟩, ⟨⟨fun i l => ?_, fun j => rfl⟩, fun l => ?_⟩,
      fun i => ?_, ⟨1, ?_⟩⟩
    · change (0 : ℝ) ≤ if i = 0 then 0 else 1
      split_ifs <;> norm_num
    · simp [exercise_10_B_1c_economy, Fin.sum_univ_two]
    · fin_cases i <;> simp [exercise_10_B_1c_economy]
    · simp [exercise_10_B_1c_economy]

end MWG.CompetitiveMarkets

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The two-good quasilinear model: consumers, firms, demand and supply (MWG Section 10.C)

MWG, pp. 317-320. Consumer `i` has utility `mᵢ + φᵢ(xᵢ)` on `ℝ × ℝ₊`, where `φᵢ` is bounded
above, twice differentiable on `x ≥ 0` with `φᵢ' > 0`, `φᵢ'' < 0`, and `φᵢ(0) = 0`
(`QLConsumer`). Firm `j` produces good `ℓ` from the numeraire at cost `cⱼ(q)`, twice
differentiable on `q ≥ 0` with `cⱼ' > 0`, `cⱼ'' ≥ 0` (`QLFirm`). Derivatives on `x ≥ 0` are taken
within `[0, ∞)` (one-sided at `0`), as the book's domain requires.

* The consumer's and firm's first-order conditions `φᵢ'(xᵢ) ≤ p` (equality if `xᵢ > 0`) and
  `p ≤ cⱼ'(qⱼ)` (equality if `qⱼ > 0`) are necessary and sufficient (pp. 317-318).
* p. 319: `φᵢ'` is strictly decreasing and takes every value in `(0, φᵢ'(0)]`; the demand
  `xᵢ(p)` is the unique solution, is zero iff `p ≥ φᵢ'(0)`, is continuous and nonincreasing on
  `p > 0`, strictly decreasing below `φᵢ'(0)`, with `xᵢ'(p) = 1/φᵢ''(xᵢ(p))`.
* For strictly convex `cⱼ` with `cⱼ' → ∞` (`QLFirmStrict`) the supply `qⱼ(p)` has the analogous
  properties. The book's `qⱼ'(p) = 1/cⱼ''(qⱼ(p)) > 0` needs `cⱼ''(qⱼ(p)) > 0`
  (`supply_hasDerivAt`); strict convexity allows `cⱼ'' = 0` at a point, where supply is not
  differentiable (`supply_not_differentiable_example`, correction 1).
* Aggregate demand and supply (p. 319): continuity, monotonicity, the zero regions and strict
  monotonicity, stated with `∃ i, p < φᵢ'(0)` for `p < maxᵢ φᵢ'(0)` and `∃ j, cⱼ'(0) < p` for
  `p > minⱼ cⱼ'(0)`.
* Concrete instances: `expConsumer a` (`φ(x) = a(1 - e^{-x})`), `linearFirm c` and `quadFirm`.
-/

namespace MWG.CompetitiveMarkets

open Filter Topology

/-- **Section 10.C** (MWG, p. 317). A quasilinear consumer `u(m, x) = m + φ(x)` on `ℝ × ℝ₊`:
`φ` bounded above, twice differentiable on `x ≥ 0` with `φ' > 0`, `φ'' < 0`, `φ(0) = 0`. -/
structure QLConsumer where
  /-- The utility of good `ℓ`. -/
  φ : ℝ → ℝ
  /-- Its derivative `φ'`. -/
  dφ : ℝ → ℝ
  /-- Its second derivative `φ''`. -/
  d2φ : ℝ → ℝ
  φ_zero : φ 0 = 0
  bddAbove : BddAbove (φ '' Set.Ici 0)
  hasDeriv : ∀ x ∈ Set.Ici (0 : ℝ), HasDerivWithinAt φ (dφ x) (Set.Ici 0) x
  hasDeriv2 : ∀ x ∈ Set.Ici (0 : ℝ), HasDerivWithinAt dφ (d2φ x) (Set.Ici 0) x
  dφ_pos : ∀ x : ℝ, 0 ≤ x → 0 < dφ x
  d2φ_neg : ∀ x : ℝ, 0 ≤ x → d2φ x < 0

/-- **Section 10.C** (MWG, p. 317). A firm with cost function `c(q)`, twice differentiable on
`q ≥ 0` with `c' > 0` and `c'' ≥ 0`. Its production set is `{(-z, q) : q ≥ 0, z ≥ c(q)}`. -/
structure QLFirm where
  /-- The cost function. -/
  c : ℝ → ℝ
  /-- Marginal cost `c'`. -/
  dc : ℝ → ℝ
  /-- Its derivative `c''`. -/
  d2c : ℝ → ℝ
  hasDeriv : ∀ q ∈ Set.Ici (0 : ℝ), HasDerivWithinAt c (dc q) (Set.Ici 0) q
  hasDeriv2 : ∀ q ∈ Set.Ici (0 : ℝ), HasDerivWithinAt dc (d2c q) (Set.Ici 0) q
  dc_pos : ∀ q : ℝ, 0 ≤ q → 0 < dc q
  d2c_nonneg : ∀ q : ℝ, 0 ≤ q → 0 ≤ d2c q

/-- **Section 10.C** (MWG, p. 319). A firm with strictly convex cost and `c'(q) → ∞`. -/
structure QLFirmStrict where
  /-- The underlying firm. -/
  toQLFirm : QLFirm
  strictConvex : StrictConvexOn ℝ (Set.Ici 0) toQLFirm.c
  dc_tendsto : Tendsto toQLFirm.dc atTop atTop

namespace QLConsumer

variable (C : QLConsumer)

theorem dφ_continuousOn : ContinuousOn C.dφ (Set.Ici 0) := foc_continuousOn C.hasDeriv2

theorem φ_continuousOn : ContinuousOn C.φ (Set.Ici 0) := foc_continuousOn C.hasDeriv

/-- `φ'` is strictly decreasing on `x ≥ 0` (MWG, p. 319). -/
theorem dφ_strictAnti : StrictAntiOn C.dφ (Set.Ici 0) := by
  refine strictAntiOn_of_hasDerivWithinAt_neg (convex_Ici 0) C.dφ_continuousOn
    (foc_hasDerivWithin_interior C.hasDeriv2 subset_rfl) fun x hx => ?_
  rw [interior_Ici] at hx
  exact C.d2φ_neg x (le_of_lt hx)

theorem dφ_antitone : AntitoneOn C.dφ (Set.Ici 0) := C.dφ_strictAnti.antitoneOn

/-- `φ` is strictly increasing on `x ≥ 0`. -/
theorem φ_strictMono : StrictMonoOn C.φ (Set.Ici 0) := by
  refine strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici 0) C.φ_continuousOn
    (foc_hasDerivWithin_interior C.hasDeriv subset_rfl) fun x hx => ?_
  rw [interior_Ici] at hx
  exact C.dφ_pos x (le_of_lt hx)

/-- `φ` is strictly concave on `x ≥ 0`. -/
theorem strictConcave : StrictConcaveOn ℝ (Set.Ici 0) C.φ := by
  refine StrictAntiOn.strictConcaveOn_of_deriv (convex_Ici 0) C.φ_continuousOn ?_
  rw [interior_Ici]
  intro x hx y hy hxy
  rw [(foc_hasDerivAt C.hasDeriv hx).deriv, (foc_hasDerivAt C.hasDeriv hy).deriv]
  exact C.dφ_strictAnti (Set.mem_Ioi.1 hx).le (Set.mem_Ioi.1 hy).le hxy

/-- The tangent inequality `φ(y) ≤ φ(x) + φ'(x)(y - x)` on `ℝ₊`. -/
theorem tangent_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    C.φ y ≤ C.φ x + C.dφ x * (y - x) :=
  foc_tangent_le C.hasDeriv C.dφ_antitone hx hy

/-- Because `φ` is bounded above and concave, `φ'` takes values below every `r > 0`
(MWG, p. 319: `φ'` takes all values in `(0, φ'(0)]`). -/
theorem exists_dφ_lt {r : ℝ} (hr : 0 < r) : ∃ y, 0 ≤ y ∧ C.dφ y < r := by
  by_contra hno
  push Not at hno
  obtain ⟨B, hB⟩ := C.bddAbove
  have hmono : MonotoneOn (fun y => C.φ y - r * y) (Set.Ici 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun y => C.dφ y - r) (convex_Ici 0)
      (C.φ_continuousOn.sub (continuousOn_const.mul continuousOn_id)) ?_ ?_
    · intro x hx
      rw [interior_Ici] at hx
      have h := (foc_hasDerivAt C.hasDeriv hx).sub ((hasDerivAt_id x).const_mul r)
      rw [mul_one] at h
      exact h.hasDerivWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      linarith [hno x (le_of_lt hx)]
  set y := (B + 1) / r with hy
  have hy0 : 0 ≤ y := div_nonneg (by linarith [hB ⟨0, Set.mem_Ici.2 le_rfl, C.φ_zero⟩]) hr.le
  have h1 := hmono (Set.mem_Ici.2 le_rfl) hy0 hy0
  have h2 := hB ⟨y, hy0, rfl⟩
  simp only [C.φ_zero, mul_zero, sub_zero] at h1
  have : r * y = B + 1 := by rw [hy]; field_simp
  linarith

/-- `φ'` takes every value in `(0, φ'(0)]` (MWG, p. 319). -/
theorem dφ_surj {r : ℝ} (hr0 : 0 < r) (hr : r ≤ C.dφ 0) : ∃ x, 0 ≤ x ∧ C.dφ x = r := by
  obtain ⟨y, hy, hyr⟩ := C.exists_dφ_lt hr0
  obtain ⟨x, hx, hxr⟩ := intermediate_value_Icc' hy (C.dφ_continuousOn.mono
    Set.Icc_subset_Ici_self) ⟨hyr.le, hr⟩
  exact ⟨x, hx.1, hxr⟩

/-- **Consumer's problem** (MWG, p. 318). `x ≥ 0` maximizes `φ(x) - px` on `x ≥ 0` if and only
if `φ'(x) ≤ p`, with equality if `x > 0`. -/
theorem max_iff {p x : ℝ} (hx : 0 ≤ x) :
    (∀ y, 0 ≤ y → C.φ y - p * y ≤ C.φ x - p * x) ↔ IsFOCSol C.dφ p x := by
  have hf : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt (fun z => C.φ z - p * z) (C.dφ z - p) (Set.Ici 0) z := by
    intro z hz
    have h := (C.hasDeriv z hz).sub ((hasDerivWithinAt_id z (Set.Ici (0 : ℝ))).const_mul p)
    rw [mul_one] at h
    exact h
  have hanti : AntitoneOn (fun z => C.dφ z - p) (Set.Ici 0) :=
    fun a ha b hb hab => sub_le_sub_right (C.dφ_antitone ha hb hab) p
  rw [foc_max_iff hf hanti hx]
  simp only [IsFOCSol, sub_nonpos, sub_eq_zero]
  exact ⟨fun h => ⟨hx, h⟩, fun h => h.2⟩

/-- Existence of a solution of the consumer's condition for every `p > 0`. -/
theorem foc_exists {p : ℝ} (hp : 0 < p) : ∃ x, IsFOCSol C.dφ p x := by
  obtain ⟨y, hy, hyr⟩ := C.exists_dφ_lt hp
  exact isFOCSol_exists C.dφ_continuousOn ⟨y, hy, hyr.le⟩

/-- **Walrasian demand for good `ℓ`** `xᵢ(p)` (MWG, p. 319); independent of wealth. -/
noncomputable def demand (p : ℝ) : ℝ := focSol C.dφ p

theorem demand_spec {p : ℝ} (hp : 0 < p) : IsFOCSol C.dφ p (C.demand p) :=
  focSol_spec (C.foc_exists hp)

theorem demand_nonneg {p : ℝ} (hp : 0 < p) : 0 ≤ C.demand p := (C.demand_spec hp).1

/-- The demand is the unique solution of the consumer's first-order condition. -/
theorem demand_eq {p x : ℝ} (h : IsFOCSol C.dφ p x) : C.demand p = x :=
  focSol_eq C.dφ_strictAnti h

/-- The demand maximizes `φ(x) - px` (MWG, p. 318). -/
theorem demand_max {p : ℝ} (hp : 0 < p) (y : ℝ) (hy : 0 ≤ y) :
    C.φ y - p * y ≤ C.φ (C.demand p) - p * C.demand p :=
  (C.max_iff (C.demand_nonneg hp)).2 (C.demand_spec hp) y hy

/-- **(MWG, p. 319)** `xᵢ(p) = 0` if and only if `p ≥ φᵢ'(0)` (for `p > 0`). -/
theorem demand_eq_zero_iff {p : ℝ} (hp : 0 < p) : C.demand p = 0 ↔ C.dφ 0 ≤ p :=
  focSol_eq_zero_iff C.dφ_strictAnti (C.foc_exists hp)

theorem demand_pos_iff {p : ℝ} (hp : 0 < p) : 0 < C.demand p ↔ p < C.dφ 0 :=
  focSol_pos_iff C.dφ_strictAnti (C.foc_exists hp)

/-- At positive demand `φᵢ'(xᵢ(p)) = p`. -/
theorem dφ_demand {p : ℝ} (hp : 0 < p) (hpos : 0 < C.demand p) : C.dφ (C.demand p) = p :=
  (C.demand_spec hp).2.2 hpos

/-- **(MWG, p. 319)** Demand is nonincreasing on `p > 0`. -/
theorem demand_antitoneOn : AntitoneOn C.demand (Set.Ioi 0) :=
  fun _ ha _ hb hab => focSol_antitone C.dφ_strictAnti (C.foc_exists ha) (C.foc_exists hb) hab

/-- **(MWG, p. 319)** Demand is strictly decreasing at every `p < φᵢ'(0)`. -/
theorem demand_strictAnti {p₁ p₂ : ℝ} (hp₁ : 0 < p₁) (h₁₂ : p₁ < p₂) (hlt : p₁ < C.dφ 0) :
    C.demand p₂ < C.demand p₁ :=
  focSol_strictAnti C.dφ_strictAnti (C.foc_exists hp₁) (C.foc_exists (hp₁.trans h₁₂)) h₁₂
    ((C.demand_pos_iff hp₁).2 hlt)

/-- **(MWG, p. 319)** Demand is continuous on `p > 0`. -/
theorem demand_continuousAt {p : ℝ} (hp : 0 < p) : ContinuousAt C.demand p :=
  focSol_continuousAt C.dφ_strictAnti
    (Filter.mem_of_superset (Ioi_mem_nhds hp) fun _ hr => C.foc_exists hr)

theorem demand_continuousOn : ContinuousOn C.demand (Set.Ioi 0) :=
  fun _ hp => (C.demand_continuousAt hp).continuousWithinAt

/-- **(MWG, p. 319)** `xᵢ'(p) = 1/φᵢ''(xᵢ(p)) < 0` for `0 < p < φᵢ'(0)`. -/
theorem demand_hasDerivAt {p : ℝ} (hp : 0 < p) (hlt : p < C.dφ 0) :
    HasDerivAt C.demand (C.d2φ (C.demand p))⁻¹ p := by
  have hpos := (C.demand_pos_iff hp).2 hlt
  exact focSol_hasDerivAt C.dφ_strictAnti
    (Filter.mem_of_superset (Ioi_mem_nhds hp) fun _ hr => C.foc_exists hr) hlt
    (foc_hasDerivAt C.hasDeriv2 hpos) (C.d2φ_neg _ hpos.le).ne

theorem demand_deriv_neg {p : ℝ} (hp : 0 < p) :
    (C.d2φ (C.demand p))⁻¹ < 0 :=
  inv_lt_zero.2 (C.d2φ_neg _ (C.demand_nonneg hp))

end QLConsumer

namespace QLFirm

variable (F : QLFirm)

theorem dc_continuousOn : ContinuousOn F.dc (Set.Ici 0) := foc_continuousOn F.hasDeriv2

theorem c_continuousOn : ContinuousOn F.c (Set.Ici 0) := foc_continuousOn F.hasDeriv

/-- `c'` is nondecreasing on `q ≥ 0`. -/
theorem dc_monotone : MonotoneOn F.dc (Set.Ici 0) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0) F.dc_continuousOn
    (foc_hasDerivWithin_interior F.hasDeriv2 subset_rfl) fun x hx => ?_
  rw [interior_Ici] at hx
  exact F.d2c_nonneg x (le_of_lt hx)

/-- `c` is strictly increasing on `q ≥ 0`. -/
theorem c_strictMono : StrictMonoOn F.c (Set.Ici 0) := by
  refine strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici 0) F.c_continuousOn
    (foc_hasDerivWithin_interior F.hasDeriv subset_rfl) fun x hx => ?_
  rw [interior_Ici] at hx
  exact F.dc_pos x (le_of_lt hx)

/-- `c` is convex on `q ≥ 0`. -/
theorem convex : ConvexOn ℝ (Set.Ici 0) F.c := by
  refine MonotoneOn.convexOn_of_deriv (convex_Ici 0) F.c_continuousOn ?_ ?_
  · rw [interior_Ici]
    exact fun x hx => (foc_hasDerivAt F.hasDeriv hx).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]
    intro x hx y hy hxy
    rw [(foc_hasDerivAt F.hasDeriv hx).deriv, (foc_hasDerivAt F.hasDeriv hy).deriv]
    exact F.dc_monotone (Set.mem_Ioi.1 hx).le (Set.mem_Ioi.1 hy).le hxy

/-- The tangent inequality `c(q) + c'(q)(q' - q) ≤ c(q')` on `ℝ₊`. -/
theorem le_tangent {q q' : ℝ} (hq : 0 ≤ q) (hq' : 0 ≤ q') :
    F.c q + F.dc q * (q' - q) ≤ F.c q' :=
  foc_le_tangent_convex F.hasDeriv F.dc_monotone hq hq'

/-- **Firm's problem** (MWG, p. 317). `q ≥ 0` maximizes `pq - c(q)` on `q ≥ 0` if and only if
`p ≤ c'(q)`, with equality if `q > 0`. -/
theorem max_iff {p q : ℝ} (hq : 0 ≤ q) :
    (∀ q', 0 ≤ q' → p * q' - F.c q' ≤ p * q - F.c q) ↔ (p ≤ F.dc q ∧ (0 < q → p = F.dc q)) := by
  have hf : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt (fun z => p * z - F.c z) (p - F.dc z) (Set.Ici 0) z := by
    intro z hz
    have h := ((hasDerivWithinAt_id z (Set.Ici (0 : ℝ))).const_mul p).sub (F.hasDeriv z hz)
    rw [mul_one] at h
    exact h
  have hanti : AntitoneOn (fun z => p - F.dc z) (Set.Ici 0) :=
    fun a ha b hb hab => sub_le_sub_left (F.dc_monotone ha hb hab) p
  rw [foc_max_iff hf hanti hq]
  simp only [sub_nonpos, sub_eq_zero]

/-- The firm's first-order condition (10.C.1) is the condition `IsFOCSol (-c') (-p)`. -/
theorem foc_iff_isFOCSol {p q : ℝ} :
    (0 ≤ q ∧ p ≤ F.dc q ∧ (0 < q → p = F.dc q)) ↔ IsFOCSol (fun z => -F.dc z) (-p) q := by
  simp only [IsFOCSol, neg_le_neg_iff, neg_inj]
  exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, h2, fun h => (h3 h).symm⟩,
    fun ⟨h1, h2, h3⟩ => ⟨h1, h2, fun h => (h3 h).symm⟩⟩

end QLFirm

namespace QLFirmStrict

variable (F : QLFirmStrict)

/-- The cost function. -/
abbrev c : ℝ → ℝ := F.toQLFirm.c

/-- Marginal cost. -/
abbrev dc : ℝ → ℝ := F.toQLFirm.dc

/-- `c''`. -/
abbrev d2c : ℝ → ℝ := F.toQLFirm.d2c

theorem hasDeriv : ∀ q ∈ Set.Ici (0 : ℝ), HasDerivWithinAt F.c (F.dc q) (Set.Ici 0) q :=
  F.toQLFirm.hasDeriv

theorem hasDeriv2 : ∀ q ∈ Set.Ici (0 : ℝ), HasDerivWithinAt F.dc (F.d2c q) (Set.Ici 0) q :=
  F.toQLFirm.hasDeriv2

theorem dc_continuousOn : ContinuousOn F.dc (Set.Ici 0) := F.toQLFirm.dc_continuousOn

/-- Strict convexity makes `c'` strictly increasing on `q ≥ 0`. -/
theorem dc_strictMono : StrictMonoOn F.dc (Set.Ici 0) := by
  intro x hx y hy hxy
  have h1 := F.strictConvex.lt_slope_of_hasDerivWithinAt hx hy hxy (F.hasDeriv x hx)
  have h2 := F.strictConvex.slope_lt_of_hasDerivWithinAt hx hy hxy (F.hasDeriv y hy)
  exact h1.trans h2

theorem neg_dc_strictAnti : StrictAntiOn (fun z => -F.dc z) (Set.Ici 0) :=
  fun _ hx _ hy hxy => neg_lt_neg (F.dc_strictMono hx hy hxy)

/-- For every price `p` some output has `c'(q) ≥ p` (since `c' → ∞`). -/
theorem foc_exists (p : ℝ) : ∃ q, IsFOCSol (fun z => -F.dc z) (-p) q := by
  obtain ⟨y, hy⟩ := (F.dc_tendsto.eventually (eventually_ge_atTop p)).and
    (eventually_ge_atTop 0) |>.exists
  exact isFOCSol_exists (F.dc_continuousOn.neg) ⟨y, hy.2, neg_le_neg hy.1⟩

/-- **Supply function** `qⱼ(p)` (MWG, p. 319). -/
noncomputable def supply (p : ℝ) : ℝ := focSol (fun z => -F.dc z) (-p)

theorem supply_foc (p : ℝ) :
    0 ≤ F.supply p ∧ p ≤ F.dc (F.supply p) ∧ (0 < F.supply p → p = F.dc (F.supply p)) :=
  (F.toQLFirm.foc_iff_isFOCSol).2 (focSol_spec (F.foc_exists p))

theorem supply_nonneg (p : ℝ) : 0 ≤ F.supply p := (F.supply_foc p).1

/-- The supply is the unique solution of the firm's first-order condition. -/
theorem supply_eq {p q : ℝ} (h : 0 ≤ q ∧ p ≤ F.dc q ∧ (0 < q → p = F.dc q)) :
    F.supply p = q :=
  focSol_eq F.neg_dc_strictAnti ((F.toQLFirm.foc_iff_isFOCSol).1 h)

/-- The supply maximizes profit `pq - c(q)` on `q ≥ 0`. -/
theorem supply_max (p q : ℝ) (hq : 0 ≤ q) :
    p * q - F.c q ≤ p * F.supply p - F.c (F.supply p) :=
  (F.toQLFirm.max_iff (F.supply_nonneg p)).2 (F.supply_foc p).2 q hq

/-- **(MWG, p. 319)** `qⱼ(p) = 0` if and only if `p ≤ cⱼ'(0)`. -/
theorem supply_eq_zero_iff (p : ℝ) : F.supply p = 0 ↔ p ≤ F.dc 0 := by
  rw [supply, focSol_eq_zero_iff F.neg_dc_strictAnti (F.foc_exists p), neg_le_neg_iff]

theorem supply_pos_iff (p : ℝ) : 0 < F.supply p ↔ F.dc 0 < p := by
  rw [supply, focSol_pos_iff F.neg_dc_strictAnti (F.foc_exists p), neg_lt_neg_iff]

/-- **(MWG, p. 319)** Supply is nondecreasing. -/
theorem supply_monotone : Monotone F.supply :=
  fun _ _ hab => focSol_antitone F.neg_dc_strictAnti (F.foc_exists _) (F.foc_exists _)
    (neg_le_neg hab)

/-- **(MWG, p. 319)** Supply is strictly increasing at every `p > cⱼ'(0)`. -/
theorem supply_strictMono {p₁ p₂ : ℝ} (h₁₂ : p₁ < p₂) (hgt : F.dc 0 < p₂) :
    F.supply p₁ < F.supply p₂ :=
  focSol_strictAnti F.neg_dc_strictAnti (F.foc_exists p₂) (F.foc_exists p₁) (neg_lt_neg h₁₂)
    ((F.supply_pos_iff p₂).2 hgt)

/-- **(MWG, p. 319)** Supply is continuous. -/
theorem supply_continuous : Continuous F.supply := by
  refine continuous_iff_continuousAt.2 fun p => ?_
  have h := focSol_continuousAt F.neg_dc_strictAnti (r₀ := -p)
    (Filter.Eventually.of_forall fun r => by simpa using F.foc_exists (-r))
  exact h.comp continuous_neg.continuousAt |>.congr (Filter.Eventually.of_forall fun r => by
    simp [supply])

/-- **(MWG, p. 319), corrected.** For `p > cⱼ'(0)` with `cⱼ''(qⱼ(p)) > 0`,
`qⱼ'(p) = 1/cⱼ''(qⱼ(p)) > 0`. (The positivity of `c''` is needed: see
`supply_not_differentiable_example`.) -/
theorem supply_hasDerivAt {p : ℝ} (hgt : F.dc 0 < p) (hc2 : 0 < F.d2c (F.supply p)) :
    HasDerivAt F.supply (F.d2c (F.supply p))⁻¹ p := by
  have hpos := (F.supply_pos_iff p).2 hgt
  have hd : HasDerivAt (fun z => -F.dc z) (-F.d2c (F.supply p)) (F.supply p) :=
    (foc_hasDerivAt F.hasDeriv2 hpos).neg
  have h := focSol_hasDerivAt F.neg_dc_strictAnti (r₀ := -p)
    (Filter.Eventually.of_forall fun r => by simpa using F.foc_exists (-r))
    (by simpa using hgt) (by simpa [supply] using hd) (neg_ne_zero.2 hc2.ne')
  have h2 := h.comp p (hasDerivAt_neg p)
  exact h2.congr_deriv (by rw [inv_neg]; ring)

end QLFirmStrict

/-! ## Aggregate demand and supply (MWG, p. 319) -/

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **(MWG, p. 319)** Aggregate demand `x(p) = ∑ᵢ xᵢ(p)`. -/
noncomputable def aggDemand (C : ι → QLConsumer) (p : ℝ) : ℝ := ∑ i, (C i).demand p

/-- **(MWG, p. 319)** Aggregate (industry) supply `q(p) = ∑ⱼ qⱼ(p)`. -/
noncomputable def aggSupply (F : κ → QLFirmStrict) (p : ℝ) : ℝ := ∑ j, (F j).supply p

theorem aggDemand_nonneg (C : ι → QLConsumer) {p : ℝ} (hp : 0 < p) : 0 ≤ aggDemand C p :=
  Finset.sum_nonneg fun i _ => (C i).demand_nonneg hp

theorem aggSupply_nonneg (F : κ → QLFirmStrict) (p : ℝ) : 0 ≤ aggSupply F p :=
  Finset.sum_nonneg fun j _ => (F j).supply_nonneg p

/-- **(MWG, p. 319)** Aggregate demand is continuous on `p > 0`. -/
theorem aggDemand_continuousOn (C : ι → QLConsumer) : ContinuousOn (aggDemand C) (Set.Ioi 0) :=
  fun _ hp => ContinuousAt.continuousWithinAt
    (tendsto_finsetSum Finset.univ fun i _ => (C i).demand_continuousAt hp)

/-- **(MWG, p. 319)** Aggregate supply is continuous. -/
theorem aggSupply_continuous (F : κ → QLFirmStrict) : Continuous (aggSupply F) :=
  continuous_finsetSum Finset.univ fun j _ => (F j).supply_continuous

/-- **(MWG, p. 319)** Aggregate demand is nonincreasing on `p > 0`. -/
theorem aggDemand_antitoneOn (C : ι → QLConsumer) : AntitoneOn (aggDemand C) (Set.Ioi 0) :=
  fun _ ha _ hb hab => Finset.sum_le_sum fun i _ => (C i).demand_antitoneOn ha hb hab

/-- **(MWG, p. 319)** Aggregate supply is nondecreasing. -/
theorem aggSupply_monotone (F : κ → QLFirmStrict) : Monotone (aggSupply F) :=
  fun _ _ hab => Finset.sum_le_sum fun j _ => (F j).supply_monotone hab

/-- **(MWG, p. 319)** `x(p) = 0` whenever `p ≥ maxᵢ φᵢ'(0)`; conversely. -/
theorem aggDemand_eq_zero_iff (C : ι → QLConsumer) {p : ℝ} (hp : 0 < p) :
    aggDemand C p = 0 ↔ ∀ i, (C i).dφ 0 ≤ p := by
  rw [aggDemand, Finset.sum_eq_zero_iff_of_nonneg fun i _ => (C i).demand_nonneg hp]
  simp only [Finset.mem_univ, true_implies, (C _).demand_eq_zero_iff hp]

/-- **(MWG, p. 320)** `q(p) = 0` whenever `p ≤ minⱼ cⱼ'(0)`; conversely. -/
theorem aggSupply_eq_zero_iff (F : κ → QLFirmStrict) (p : ℝ) :
    aggSupply F p = 0 ↔ ∀ j, p ≤ (F j).dc 0 := by
  rw [aggSupply, Finset.sum_eq_zero_iff_of_nonneg fun j _ => (F j).supply_nonneg p]
  simp only [Finset.mem_univ, true_implies, (F _).supply_eq_zero_iff]

/-- **(MWG, p. 319)** Aggregate demand is strictly decreasing at every `p < maxᵢ φᵢ'(0)`. -/
theorem aggDemand_strictAnti (C : ι → QLConsumer) {p₁ p₂ : ℝ} (hp₁ : 0 < p₁) (h₁₂ : p₁ < p₂)
    (hlt : ∃ i, p₁ < (C i).dφ 0) : aggDemand C p₂ < aggDemand C p₁ := by
  obtain ⟨i, hi⟩ := hlt
  exact Finset.sum_lt_sum (fun k _ => (C k).demand_antitoneOn hp₁ (hp₁.trans h₁₂) h₁₂.le)
    ⟨i, Finset.mem_univ i, (C i).demand_strictAnti hp₁ h₁₂ hi⟩

/-- **(MWG, p. 319)** Aggregate supply is strictly increasing at every `p > minⱼ cⱼ'(0)`. -/
theorem aggSupply_strictMono (F : κ → QLFirmStrict) {p₁ p₂ : ℝ} (h₁₂ : p₁ < p₂)
    (hgt : ∃ j, (F j).dc 0 < p₂) : aggSupply F p₁ < aggSupply F p₂ := by
  obtain ⟨j, hj⟩ := hgt
  exact Finset.sum_lt_sum (fun k _ => (F k).supply_monotone h₁₂.le)
    ⟨j, Finset.mem_univ j, (F j).supply_strictMono h₁₂ hj⟩

/-! ## Concrete instances -/

/-- The consumer `φ(x) = a(1 - e^{-x})`, `a > 0`: `φ' = ae^{-x}`, `φ'' = -ae^{-x}`. -/
noncomputable def expConsumer (a : ℝ) (ha : 0 < a) : QLConsumer where
  φ x := a * (1 - Real.exp (-x))
  dφ x := a * Real.exp (-x)
  d2φ x := -(a * Real.exp (-x))
  φ_zero := by simp
  bddAbove := ⟨a, by
    rintro _ ⟨x, -, rfl⟩
    have := Real.exp_pos (-x)
    nlinarith⟩
  hasDeriv x _ := by
    have h := ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).const_sub 1 |>.const_mul a
    exact (h.congr_deriv (by ring)).hasDerivWithinAt
  hasDeriv2 x _ := by
    have h := ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).const_mul a
    exact (h.congr_deriv (by ring)).hasDerivWithinAt
  dφ_pos x _ := mul_pos ha (Real.exp_pos _)
  d2φ_neg x _ := neg_lt_zero.2 (mul_pos ha (Real.exp_pos _))

/-- `expConsumer a` has demand `log(a/p)` below `p = a` (and `0` above). -/
theorem expConsumer_demand {a : ℝ} (ha : 0 < a) {p : ℝ} (hp : 0 < p) (hpa : p < a) :
    (expConsumer a ha).demand p = Real.log (a / p) := by
  apply QLConsumer.demand_eq
  have hlog : 0 < Real.log (a / p) := Real.log_pos (by rw [one_lt_div hp]; exact hpa)
  have he : a * Real.exp (-Real.log (a / p)) = p := by
    rw [Real.exp_neg, Real.exp_log (div_pos ha hp)]
    field_simp
  exact ⟨hlog.le, by simp only [expConsumer]; rw [he], fun _ => by simp only [expConsumer]; rw [he]⟩

/-- A constant-returns firm `c(q) = c·q`, `c > 0` (MWG, p. 320, footnote 10). -/
def linearFirm (c : ℝ) (hc : 0 < c) : QLFirm where
  c q := c * q
  dc _ := c
  d2c _ := 0
  hasDeriv q _ := by simpa using ((hasDerivAt_id q).const_mul c).hasDerivWithinAt
  hasDeriv2 q _ := hasDerivWithinAt_const q _ c
  dc_pos _ _ := hc
  d2c_nonneg _ _ := le_rfl

/-- A quadratic firm `c(q) = αq + βq²/2` with `α > 0`, `β > 0`: `c' = α + βq`. -/
noncomputable def quadFirmBase (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) : QLFirm where
  c q := α * q + β * q ^ 2 / 2
  dc q := α + β * q
  d2c _ := β
  hasDeriv q _ := by
    have h := ((hasDerivAt_id q).const_mul α).add ((hasDerivAt_pow 2 q).const_mul β |>.div_const 2)
    exact (h.congr_deriv (by simp only [Nat.cast_ofNat]; ring)).hasDerivWithinAt
  hasDeriv2 q _ := by
    have h := ((hasDerivAt_id q).const_mul β).const_add α
    simpa using h.hasDerivWithinAt
  dc_pos q hq := by positivity
  d2c_nonneg _ _ := hβ.le

/-- A quadratic firm `c(q) = αq + βq²/2` with `α > 0`, `β > 0`: strictly convex, `c' → ∞`. -/
noncomputable def quadFirm (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) : QLFirmStrict where
  toQLFirm := quadFirmBase α β hα hβ
  strictConvex := by
    refine StrictMonoOn.strictConvexOn_of_deriv (convex_Ici 0) (by fun_prop) ?_
    intro x _ y _ hxy
    have hd : ∀ z, deriv (fun q : ℝ => α * q + β * q ^ 2 / 2) z = α + β * z := by
      intro z
      have h := ((hasDerivAt_id z).const_mul α).add
        ((hasDerivAt_pow 2 z).const_mul β |>.div_const 2)
      have h' : HasDerivAt (fun q : ℝ => α * q + β * q ^ 2 / 2) (α + β * z) z :=
        h.congr_deriv (by simp only [Nat.cast_ofNat]; ring)
      exact h'.deriv
    change deriv (fun q : ℝ => α * q + β * q ^ 2 / 2) x <
      deriv (fun q : ℝ => α * q + β * q ^ 2 / 2) y
    rw [hd, hd]
    nlinarith
  dc_tendsto := by
    exact tendsto_atTop_add_const_left _ α (Filter.Tendsto.const_mul_atTop hβ tendsto_id)

/-- `quadFirm` supplies `(p - α)/β` above `p = α`. -/
theorem quadFirm_supply {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) {p : ℝ} (hp : α < p) :
    (quadFirm α β hα hβ).supply p = (p - α) / β := by
  apply QLFirmStrict.supply_eq
  have h : 0 < (p - α) / β := div_pos (by linarith) hβ
  have he : α + β * ((p - α) / β) = p := by field_simp; ring
  exact ⟨h.le, by simp only [quadFirm, QLFirmStrict.dc, quadFirmBase]; rw [he],
    fun _ => by simp only [quadFirm, QLFirmStrict.dc, quadFirmBase]; rw [he]⟩

/-- **Correction to p. 319.** A strictly convex cost with `c' → ∞` whose `c''` vanishes at an
interior point: `c'(q) = 2 + (q - 1)³`. -/
noncomputable def cubicFirmBase : QLFirm where
  c q := 2 * q + ((q - 1) ^ 4 - 1) / 4
  dc q := 2 + (q - 1) ^ 3
  d2c q := 3 * (q - 1) ^ 2
  hasDeriv q _ := by
    have h := ((hasDerivAt_id q).const_mul 2).add
      ((((hasDerivAt_id q).sub_const 1).pow 4).sub_const 1 |>.div_const 4)
    exact (h.congr_deriv (by simp only [id, Nat.cast_ofNat]; ring)).hasDerivWithinAt
  hasDeriv2 q _ := by
    have h := (((hasDerivAt_id q).sub_const 1).pow 3).const_add (2 : ℝ)
    exact (h.congr_deriv (by simp only [id, Nat.cast_ofNat]; ring)).hasDerivWithinAt
  dc_pos q hq := by
    nlinarith [mul_nonneg hq (add_nonneg (sq_nonneg (q - 3 / 2)) (by norm_num : (0 : ℝ) ≤ 3 / 4))]
  d2c_nonneg q _ := by positivity

/-- **Correction to p. 319.** `cubicFirmBase` is strictly convex with `c' → ∞`. -/
noncomputable def cubicFirm : QLFirmStrict where
  toQLFirm := cubicFirmBase
  strictConvex := by
    refine StrictMonoOn.strictConvexOn_of_deriv (convex_Ici 0) (by fun_prop) ?_
    intro x _ y _ hxy
    have hd : ∀ z, deriv (fun q : ℝ => 2 * q + ((q - 1) ^ 4 - 1) / 4) z = 2 + (z - 1) ^ 3 := by
      intro z
      have h := ((hasDerivAt_id z).const_mul 2).add
        ((((hasDerivAt_id z).sub_const 1).pow 4).sub_const 1 |>.div_const 4)
      have h' : HasDerivAt (fun q : ℝ => 2 * q + ((q - 1) ^ 4 - 1) / 4) (2 + (z - 1) ^ 3) z :=
        h.congr_deriv (by simp only [id, Nat.cast_ofNat]; ring)
      exact h'.deriv
    change deriv (fun q : ℝ => 2 * q + ((q - 1) ^ 4 - 1) / 4) x <
      deriv (fun q : ℝ => 2 * q + ((q - 1) ^ 4 - 1) / 4) y
    rw [hd, hd]
    have : (x - 1) ^ 3 < (y - 1) ^ 3 := by
      have := Odd.strictMono_pow (R := ℝ) (n := 3) (by decide)
      exact this (by linarith)
    linarith
  dc_tendsto := by
    refine tendsto_atTop_add_const_left _ 2 ?_
    exact (tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)).comp (tendsto_atTop_add_const_right _ (-1)
      tendsto_id) |>.congr fun q => by simp [sub_eq_add_neg]

/-- **Correction to p. 319.** For `cubicFirm` (strictly convex, `c' → ∞`, `c'' ≥ 0`), supply is
not differentiable at `p = 2 > c'(0) = 1`, so `q'(p) = 1/c''(q(p))` fails where `c'' = 0`. -/
theorem supply_not_differentiable_example : ¬ DifferentiableAt ℝ cubicFirm.supply 2 := by
  intro hd
  have hq : cubicFirm.supply 2 = 1 := by
    apply QLFirmStrict.supply_eq
    simp [cubicFirm, cubicFirmBase, QLFirmStrict.dc]
  -- near `2`, `c'(q(p)) = p`
  have hev : ∀ᶠ p in 𝓝 (2 : ℝ), cubicFirm.dc (cubicFirm.supply p) = p := by
    have hgt : ∀ᶠ p in 𝓝 (2 : ℝ), cubicFirm.dc 0 < p := by
      have : cubicFirm.dc 0 = 1 := by
        simp [cubicFirm, cubicFirmBase, QLFirmStrict.dc]; norm_num
      rw [this]
      exact lt_mem_nhds (by norm_num)
    filter_upwards [hgt] with p hp
    exact ((cubicFirm.supply_foc p).2.2 ((cubicFirm.supply_pos_iff p).2 hp)).symm
  have h1 : HasDerivAt (fun p => cubicFirm.dc (cubicFirm.supply p))
      (cubicFirm.d2c (cubicFirm.supply 2) * deriv cubicFirm.supply 2) 2 := by
    have hdc : HasDerivAt cubicFirm.dc (cubicFirm.d2c (cubicFirm.supply 2))
        (cubicFirm.supply 2) := by
      rw [hq]
      exact foc_hasDerivAt cubicFirm.hasDeriv2 one_pos
    exact hdc.comp 2 hd.hasDerivAt
  have h2 : HasDerivAt (fun p => cubicFirm.dc (cubicFirm.supply p)) 1 2 :=
    (hasDerivAt_id 2).congr_of_eventuallyEq hev
  have := h1.unique h2
  rw [hq] at this
  simp [cubicFirm, cubicFirmBase, QLFirmStrict.d2c] at this

end MWG.CompetitiveMarkets

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Competitive equilibrium in the two-good quasilinear model (MWG Section 10.C, pp. 317-325)

The quasilinear economy is an instance of Definition 10.B.3 (`qlEconomy`): goods `0` (the
numeraire `m`) and `1` (good `ℓ`), consumption sets `ℝ × ℝ₊`, utilities `m + φᵢ(x)`, production
sets `Yⱼ = {(-z, q) : q ≥ 0, z ≥ cⱼ(q)}`, endowments `(ω_{mi}, 0)` and shares `θᵢⱼ`; prices are
normalized to `(1, p)`.

* `ql_supply_iff`, `ql_demand_iff` (pp. 317-318): profit maximization means `z = c(q)` and `q`
  maximizes `pq - c(q)`; utility maximization means the budget binds and `x` maximizes
  `φ(x) - px`. No assumption on `φ`, `c` is needed.
* Footnote 6 (p. 318): `p* > 0` in every equilibrium (`ql_eqm_price_pos`).
* **(10.C.1)-(10.C.3)** (p. 318): `ql_isCompetitiveEqm_iff` characterizes the equilibria of
  Definition 10.B.3 by the `I + J + 1` conditions `IsQLEqm`; these do not involve endowments or
  shares, so equilibrium allocations and prices are independent of them
  (`ql_isCompetitiveEqm_of_isQLEqm`, p. 318).
* p. 318: aggregate consumption is positive when `maxᵢ φᵢ'(0) > minⱼ cⱼ'(0)`.
* p. 320: existence and uniqueness of equilibrium with strictly convex costs and `c' → ∞`
  (`ql_eqm_exists`, `ql_eqm_unique`), with `p* ∈ (minⱼ cⱼ'(0), maxᵢ φᵢ'(0))`.
* Footnote 10 and Figure 10.C.4 (pp. 320-321): constant returns `cⱼ(q) = cq`: supply is
  infinite above `c`, the equilibrium price is `c` and individual outputs are indeterminate.
* Figure 10.C.8 (p. 324): a nonconvex technology with no competitive equilibrium
  (`figure_10_C_8_no_equilibrium`).
-/

namespace MWG.CompetitiveMarkets

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.Production

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **Section 10.C** (MWG, p. 317). The two-good quasilinear economy as a private ownership
economy. Good `0` is the numeraire, good `1` is good `ℓ`. -/
def qlEconomy (φ : ι → ℝ → ℝ) (c : κ → ℝ → ℝ) (ωm : ι → ℝ) (θ : ι → κ → ℝ) :
    PrivEconomy ι κ 2 where
  X _ := {v | 0 ≤ v 1}
  u i v := v 0 + φ i (v 1)
  Y j := {y | 0 ≤ y 1 ∧ c j (y 1) ≤ -y 0}
  ωi i := ![ωm i, 0]
  θ := θ

/-- Prices with the numeraire normalized to `1` (MWG, p. 317). -/
def qlPrice (p : ℝ) : Fin 2 → ℝ := ![1, p]

theorem qlPrice_dot (p : ℝ) (v : Fin 2 → ℝ) : qlPrice p ⬝ᵥ v = v 0 + p * v 1 := by
  simp [qlPrice, dotProduct, Fin.sum_univ_two]

/-- **Profit maximization in the quasilinear model** (MWG, p. 317). A plan `y` is profit
maximizing at prices `(1, p)` iff `y = (-c(q), q)` with `q ≥ 0` maximizing `pq - c(q)`. -/
theorem ql_supply_iff (c : ℝ → ℝ) (p : ℝ) (y : Fin 2 → ℝ) :
    y ∈ supply {y : Fin 2 → ℝ | 0 ≤ y 1 ∧ c (y 1) ≤ -y 0} (qlPrice p) ↔
      0 ≤ y 1 ∧ y 0 = -c (y 1) ∧ ∀ q, 0 ≤ q → p * q - c q ≤ p * y 1 - c (y 1) := by
  constructor
  · rintro ⟨⟨hq, hz⟩, hmax⟩
    have h1 := hmax ![-c (y 1), y 1] (by simp [hq])
    simp only [qlPrice_dot] at h1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h1
    have hy0 : y 0 = -c (y 1) := le_antisymm (by linarith) (by linarith)
    refine ⟨hq, hy0, fun q hq' => ?_⟩
    have h2 := hmax ![-c q, q] (by simp [hq'])
    simp only [qlPrice_dot, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] at h2
    linarith
  · rintro ⟨hq, hy0, hmax⟩
    refine ⟨⟨hq, by rw [hy0, neg_neg]⟩, fun y' hy' => ?_⟩
    simp only [qlPrice_dot]
    have := hmax (y' 1) hy'.1
    linarith [hy'.2]

/-- **Utility maximization in the quasilinear model** (MWG, p. 318). A bundle `v = (m, x)` solves
the UMP at prices `(1, p)` and wealth `w` iff `x ≥ 0`, the budget binds (`m = w - px`), and `x`
maximizes `φ(x) - px` on `x ≥ 0`. -/
theorem ql_demand_iff (φ : ℝ → ℝ) (p w : ℝ) (v : Fin 2 → ℝ) :
    v ∈ walrasianDemandOn {v : Fin 2 → ℝ | 0 ≤ v 1} (fun v => v 0 + φ (v 1)) (qlPrice p) w ↔
      0 ≤ v 1 ∧ v 0 = w - p * v 1 ∧ ∀ x, 0 ≤ x → φ x - p * x ≤ φ (v 1) - p * v 1 := by
  constructor
  · rintro ⟨⟨hx, hb⟩, hmax⟩
    simp only [qlPrice_dot] at hb
    have hbind : v 0 = w - p * v 1 := by
      by_contra hne
      have hlt : v 0 + p * v 1 < w := lt_of_le_of_ne hb fun h => hne (by linarith)
      have := hmax ![w - p * v 1, v 1] ⟨by simpa using hx, by rw [qlPrice_dot]; simp⟩
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at this
      linarith
    refine ⟨hx, hbind, fun x hx' => ?_⟩
    have := hmax ![w - p * x, x] ⟨by simpa using hx', by rw [qlPrice_dot]; simp⟩
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at this
    linarith
  · rintro ⟨hx, hbind, hmax⟩
    refine ⟨⟨hx, by rw [qlPrice_dot, hbind]; linarith⟩, fun v' hv' => ?_⟩
    have hb := hv'.2
    rw [qlPrice_dot] at hb
    have := hmax (v' 1) hv'.1
    simp only
    linarith

omit [Fintype ι] in
/-- Consumer `i`'s wealth in the quasilinear economy:
`ω_{mi} + ∑ⱼ θᵢⱼ (yⱼ₀ + p yⱼ₁)`. -/
theorem ql_wealth (φ : ι → ℝ → ℝ) (c : κ → ℝ → ℝ) (ωm : ι → ℝ) (θ : ι → κ → ℝ)
    (a : Allocation ι κ 2) (p : ℝ) (i : ι) :
    (qlEconomy φ c ωm θ).wealth a (qlPrice p) i =
      ωm i + ∑ j, θ i j * (a.y j 0 + p * a.y j 1) := by
  simp only [PrivEconomy.wealth, qlPrice_dot]
  simp [qlEconomy]

/-- **Footnote 6** (MWG, p. 318). In any competitive equilibrium of the quasilinear model the
price of good `ℓ` is positive (otherwise a consumer with strictly increasing `φᵢ` would demand
an unbounded amount). -/
theorem ql_eqm_price_pos {φ : ι → ℝ → ℝ} {c : κ → ℝ → ℝ} {ωm : ι → ℝ} {θ : ι → κ → ℝ}
    (i₀ : ι) (hφ : StrictMonoOn (φ i₀) (Set.Ici 0)) {a : Allocation ι κ 2} {p : ℝ}
    (h : (qlEconomy φ c ωm θ).IsCompetitiveEqm a (qlPrice p)) : 0 < p := by
  have hd := (ql_demand_iff (φ i₀) p _ (a.x i₀)).1 (h.2.1 i₀)
  by_contra hp
  push Not at hp
  have h1 := hd.2.2 (a.x i₀ 1 + 1) (by linarith [hd.1])
  have h2 := hφ (Set.mem_Ici.2 hd.1) (Set.mem_Ici.2 (by linarith [hd.1]))
    (by linarith : a.x i₀ 1 < a.x i₀ 1 + 1)
  nlinarith

/-- **Conditions (10.C.1)-(10.C.3)** (MWG, p. 318): `p ≤ cⱼ'(qⱼ)` with equality if `qⱼ > 0`;
`φᵢ'(xᵢ) ≤ p` with equality if `xᵢ > 0`; `∑ᵢ xᵢ = ∑ⱼ qⱼ`. -/
def IsQLEqm (C : ι → QLConsumer) (F : κ → QLFirm) (x : ι → ℝ) (q : κ → ℝ) (p : ℝ) : Prop :=
  (∀ j, 0 ≤ q j ∧ p ≤ (F j).dc (q j) ∧ (0 < q j → p = (F j).dc (q j))) ∧
  (∀ i, IsFOCSol (C i).dφ p (x i)) ∧ ∑ i, x i = ∑ j, q j

/-- The quasilinear economy with consumers `C` and firms `F`. -/
def qlEconomyOf (C : ι → QLConsumer) (F : κ → QLFirm) (ωm : ι → ℝ) (θ : ι → κ → ℝ) :
    PrivEconomy ι κ 2 :=
  qlEconomy (fun i => (C i).φ) (fun j => (F j).c) ωm θ

/-- The allocation determined by the levels of good `ℓ` (MWG, p. 318): firm `j` uses
`zⱼ = cⱼ(qⱼ)` of the numeraire, consumer `i` consumes
`mᵢ = ω_{mi} + ∑ⱼ θᵢⱼ (p qⱼ - cⱼ(qⱼ)) - p xᵢ`. -/
noncomputable def qlAllocation (F : κ → QLFirm) (ωm : ι → ℝ) (θ : ι → κ → ℝ) (x : ι → ℝ)
    (q : κ → ℝ) (p : ℝ) : Allocation ι κ 2 where
  x i := ![ωm i + ∑ j, θ i j * (p * q j - (F j).c (q j)) - p * x i, x i]
  y j := ![-(F j).c (q j), q j]

/-- **Characterization (10.C.1)-(10.C.3)** (MWG, p. 318). With shares summing to one, an
allocation and prices `(1, p)` form a competitive equilibrium (Definition 10.B.3) of the
quasilinear economy iff the levels of good `ℓ` satisfy (10.C.1)-(10.C.3) and the numeraire
components are the ones determined by budgets and costs. -/
theorem ql_isCompetitiveEqm_iff (C : ι → QLConsumer) (F : κ → QLFirm) (ωm : ι → ℝ)
    (θ : ι → κ → ℝ) (hθ : ∀ j, ∑ i, θ i j = 1) (a : Allocation ι κ 2) (p : ℝ) :
    (qlEconomyOf C F ωm θ).IsCompetitiveEqm a (qlPrice p) ↔
      IsQLEqm C F (fun i => a.x i 1) (fun j => a.y j 1) p ∧
      a = qlAllocation F ωm θ (fun i => a.x i 1) (fun j => a.y j 1) p := by
  have hext : ∀ v w : Fin 2 → ℝ, v 0 = w 0 → v 1 = w 1 → v = w := fun v w h0 h1 => by
    ext l; fin_cases l <;> simp [h0, h1]
  constructor
  · rintro ⟨hfirm, hcons, hclear⟩
    have hF : ∀ j, 0 ≤ a.y j 1 ∧ a.y j 0 = -(F j).c (a.y j 1) ∧
        ∀ q, 0 ≤ q → p * q - (F j).c q ≤ p * a.y j 1 - (F j).c (a.y j 1) :=
      fun j => (ql_supply_iff (F j).c p (a.y j)).1 (hfirm j)
    have hC := fun i => (ql_demand_iff (C i).φ p _ (a.x i)).1 (hcons i)
    refine ⟨⟨fun j => ?_, fun i => ?_, ?_⟩, ?_⟩
    · exact ⟨(hF j).1, ((F j).max_iff (hF j).1).1 (hF j).2.2⟩
    · exact ((C i).max_iff (hC i).1).1 (hC i).2.2
    · have := hclear 1
      simpa [qlEconomyOf, qlEconomy] using this
    · cases a with
      | mk ax ay =>
        simp only [qlAllocation, Allocation.mk.injEq]
        refine ⟨funext fun i => hext _ _ ?_ (by simp), funext fun j => hext _ _ ?_ (by simp)⟩
        · have h := (hC i).2.1
          rw [qlEconomyOf, ql_wealth] at h
          simp only [Matrix.cons_val_zero]
          dsimp only at h ⊢
          rw [h]
          congr 2
          refine Finset.sum_congr rfl fun j _ => ?_
          have := (hF j).2.1
          dsimp only at this
          rw [this]; ring
        · simpa using (hF j).2.1
  · rintro ⟨⟨hq, hx, hsum⟩, ha⟩
    have hy0 : ∀ j, a.y j 0 = -(F j).c (a.y j 1) := fun j => by rw [ha]; simp [qlAllocation]
    have hm : ∀ i, a.x i 0 = ωm i + ∑ j, θ i j * (p * a.y j 1 - (F j).c (a.y j 1)) -
        p * a.x i 1 := fun i => by rw [ha]; simp [qlAllocation]
    have hw : ∀ i, (qlEconomyOf C F ωm θ).wealth a (qlPrice p) i =
        ωm i + ∑ j, θ i j * (p * a.y j 1 - (F j).c (a.y j 1)) := by
      intro i
      rw [qlEconomyOf, ql_wealth]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by rw [hy0 j]; ring
    have hfirm : ∀ j, a.y j ∈ supply ((qlEconomyOf C F ωm θ).Y j) (qlPrice p) := by
      intro j
      exact (ql_supply_iff (F j).c p (a.y j)).2
        ⟨(hq j).1, hy0 j, ((F j).max_iff (hq j).1).2 (hq j).2⟩
    have hcons : ∀ i, a.x i ∈ walrasianDemandOn ((qlEconomyOf C F ωm θ).X i)
        ((qlEconomyOf C F ωm θ).u i) (qlPrice p)
        ((qlEconomyOf C F ωm θ).wealth a (qlPrice p) i) := by
      intro i
      refine (ql_demand_iff (C i).φ p _ (a.x i)).2 ⟨(hx i).1, ?_, ((C i).max_iff (hx i).1).2 (hx i)⟩
      rw [hw, hm]
    refine ⟨hfirm, hcons, ?_⟩
    have h1 : ∑ i, a.x i 1 = ∑ i, (qlEconomyOf C F ωm θ).ωi i 1 + ∑ j, a.y j 1 := by
      simpa [qlEconomyOf, qlEconomy] using hsum
    intro l
    fin_cases l
    · refine lemma_10_B_1 (qlEconomyOf C F ωm θ) a (qlPrice p) 0 (by simp [qlPrice]) hθ
        (fun i => ?_) (fun l hl => ?_)
      · rw [hw, qlPrice_dot, hm]; ring
      · fin_cases l
        · exact absurd rfl hl
        · exact h1
    · exact h1

/-- **Independence of endowments and shares** (MWG, pp. 318-319). If `(x, q, p)` satisfies
(10.C.1)-(10.C.3), then for every distribution of endowments and of shares (summing to one) the
corresponding allocation and prices `(1, p)` are a competitive equilibrium. -/
theorem ql_isCompetitiveEqm_of_isQLEqm {C : ι → QLConsumer} {F : κ → QLFirm} {x : ι → ℝ}
    {q : κ → ℝ} {p : ℝ} (h : IsQLEqm C F x q p) (ωm : ι → ℝ) (θ : ι → κ → ℝ)
    (hθ : ∀ j, ∑ i, θ i j = 1) :
    (qlEconomyOf C F ωm θ).IsCompetitiveEqm (qlAllocation F ωm θ x q p) (qlPrice p) := by
  rw [ql_isCompetitiveEqm_iff C F ωm θ hθ]
  refine ⟨by simpa [qlAllocation] using h, ?_⟩
  simp [qlAllocation]

/-- In every solution of (10.C.1)-(10.C.3) the price is positive (footnote 6, p. 318). -/
theorem IsQLEqm.price_pos [Nonempty ι] {C : ι → QLConsumer} {F : κ → QLFirm} {x : ι → ℝ}
    {q : κ → ℝ} {p : ℝ} (h : IsQLEqm C F x q p) : 0 < p := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact ((C i).dφ_pos _ (h.2.1 i).1).trans_le (h.2.1 i).2.1

/-- **(MWG, p. 318)** If `maxᵢ φᵢ'(0) > minⱼ cⱼ'(0)`, aggregate consumption and production of
good `ℓ` are strictly positive in every competitive equilibrium. -/
theorem IsQLEqm.aggregate_pos {C : ι → QLConsumer} {F : κ → QLFirm} {x : ι → ℝ} {q : κ → ℝ}
    {p : ℝ} (h : IsQLEqm C F x q p) (hgap : ∃ i j, (F j).dc 0 < (C i).dφ 0) :
    0 < ∑ i, x i := by
  obtain ⟨i, j, hij⟩ := hgap
  by_contra hle
  push Not at hle
  have hx0 : ∀ k, x k = 0 := fun k =>
    (Finset.sum_eq_zero_iff_of_nonneg fun k _ => (h.2.1 k).1).1
      (le_antisymm hle (Finset.sum_nonneg fun k _ => (h.2.1 k).1)) k (Finset.mem_univ k)
  have hq0 : q j = 0 := by
    have hs : ∑ k, q k = 0 := by rw [← h.2.2]; exact Finset.sum_eq_zero fun k _ => hx0 k
    exact (Finset.sum_eq_zero_iff_of_nonneg fun k _ => (h.1 k).1).1 hs j (Finset.mem_univ j)
  have h1 := (h.2.1 i).2.1
  have h2 := (h.1 j).2.1
  rw [hx0 i] at h1
  rw [hq0] at h2
  linarith

/-- **Uniqueness of equilibrium** (MWG, p. 320; strictly convex costs). If
`maxᵢ φᵢ'(0) > minⱼ cⱼ'(0)`, any two solutions of (10.C.1)-(10.C.3) coincide. -/
theorem ql_eqm_unique [Nonempty ι] {C : ι → QLConsumer} {F : κ → QLFirmStrict}
    (hgap : ∃ i j, (F j).dc 0 < (C i).dφ 0) {x x' : ι → ℝ} {q q' : κ → ℝ} {p p' : ℝ}
    (h : IsQLEqm C (fun j => (F j).toQLFirm) x q p)
    (h' : IsQLEqm C (fun j => (F j).toQLFirm) x' q' p') : x = x' ∧ q = q' ∧ p = p' := by
  have hp := h.price_pos
  have hp' := h'.price_pos
  have hxd : ∀ p'' x'' q'', IsQLEqm C (fun j => (F j).toQLFirm) x'' q'' p'' →
      x'' = fun i => (C i).demand p'' := fun p'' x'' q'' hh => funext fun i =>
    ((C i).demand_eq (hh.2.1 i)).symm
  have hqd : ∀ p'' x'' q'', IsQLEqm C (fun j => (F j).toQLFirm) x'' q'' p'' →
      q'' = fun j => (F j).supply p'' := fun p'' x'' q'' hh => funext fun j =>
    ((F j).supply_eq (hh.1 j)).symm
  have hclr : ∀ p'' x'' q'', IsQLEqm C (fun j => (F j).toQLFirm) x'' q'' p'' →
      aggDemand C p'' = aggSupply F p'' := fun p'' x'' q'' hh => by
    have := hh.2.2
    rw [hxd p'' x'' q'' hh, hqd p'' x'' q'' hh] at this
    exact this
  have hpp : p = p' := by
    by_contra hne
    -- WLOG-style: treat both orders
    have key : ∀ p₁ p₂, 0 < p₁ → p₁ < p₂ → aggDemand C p₁ = aggSupply F p₁ →
        aggDemand C p₂ = aggSupply F p₂ → False := by
      intro p₁ p₂ hp₁ h₁₂ e₁ e₂
      by_cases hlt : ∃ i, p₁ < (C i).dφ 0
      · have := aggDemand_strictAnti C hp₁ h₁₂ hlt
        have := aggSupply_monotone F h₁₂.le
        linarith
      · push Not at hlt
        have hx₁ := (aggDemand_eq_zero_iff C hp₁).2 hlt
        have hx₂ := (aggDemand_eq_zero_iff C (hp₁.trans h₁₂)).2 fun i => (hlt i).trans h₁₂.le
        have hq₂ := (aggSupply_eq_zero_iff F p₂).1 (by rw [← e₂, hx₂])
        obtain ⟨i, j, hij⟩ := hgap
        linarith [hlt i, hq₂ j]
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact key p p' hp hlt (hclr _ _ _ h) (hclr _ _ _ h')
    · exact key p' p hp' hlt (hclr _ _ _ h') (hclr _ _ _ h)
  subst hpp
  exact ⟨(hxd _ _ _ h).trans (hxd _ _ _ h').symm, (hqd _ _ _ h).trans (hqd _ _ _ h').symm, rfl⟩

/-- **Existence of equilibrium** (MWG, p. 320). With strictly convex costs, `cⱼ' → ∞` and
`maxᵢ φᵢ'(0) > minⱼ cⱼ'(0)`, there is a price `p* ∈ (minⱼ cⱼ'(0), maxᵢ φᵢ'(0))` with
`x(p*) = q(p*)`, and `xᵢ* = xᵢ(p*)`, `qⱼ* = qⱼ(p*)` satisfy (10.C.1)-(10.C.3). -/
theorem ql_eqm_exists [Nonempty ι] [Nonempty κ] (C : ι → QLConsumer) (F : κ → QLFirmStrict)
    (hgap : ∃ i j, (F j).dc 0 < (C i).dφ 0) :
    ∃ p, 0 < p ∧ (∃ j, (F j).dc 0 < p) ∧ (∃ i, p < (C i).dφ 0) ∧
      aggDemand C p = aggSupply F p ∧
      IsQLEqm C (fun j => (F j).toQLFirm) (fun i => (C i).demand p)
        (fun j => (F j).supply p) p := by
  obtain ⟨j₀, -, hj₀⟩ := Finset.exists_min_image Finset.univ (fun j => (F j).dc 0)
    Finset.univ_nonempty
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ (fun i => (C i).dφ 0)
    Finset.univ_nonempty
  set lo := (F j₀).dc 0 with hlo
  set hi := (C i₀).dφ 0 with hhi
  have hlohi : lo < hi := by
    obtain ⟨i, j, hij⟩ := hgap
    exact ((hj₀ j (Finset.mem_univ j)).trans_lt hij).trans_le (hi₀ i (Finset.mem_univ i))
  have hlo0 : 0 < lo := (F j₀).toQLFirm.dc_pos 0 le_rfl
  have hZcont : ContinuousOn (fun p => aggDemand C p - aggSupply F p) (Set.Icc lo hi) :=
    ((aggDemand_continuousOn C).mono fun p hp => hlo0.trans_le hp.1).sub
      (aggSupply_continuous F).continuousOn
  have hZlo : 0 < aggDemand C lo - aggSupply F lo := by
    have hq : aggSupply F lo = 0 :=
      (aggSupply_eq_zero_iff F lo).2 fun j => hj₀ j (Finset.mem_univ j)
    have hx : 0 < aggDemand C lo := by
      refine lt_of_le_of_ne (aggDemand_nonneg C hlo0) fun h0 => ?_
      have := ((aggDemand_eq_zero_iff C hlo0).1 h0.symm) i₀
      linarith
    linarith
  have hZhi : aggDemand C hi - aggSupply F hi < 0 := by
    have hx : aggDemand C hi = 0 :=
      (aggDemand_eq_zero_iff C (hlo0.trans hlohi)).2 fun i => hi₀ i (Finset.mem_univ i)
    have hq : 0 < aggSupply F hi := by
      refine lt_of_le_of_ne (aggSupply_nonneg F hi) fun h0 => ?_
      have := ((aggSupply_eq_zero_iff F hi).1 h0.symm) j₀
      linarith
    linarith
  obtain ⟨p, hp, hpZ⟩ := intermediate_value_Icc' hlohi.le hZcont ⟨hZhi.le, hZlo.le⟩
  have hp0 : 0 < p := hlo0.trans_le hp.1
  have hplo : lo < p := lt_of_le_of_ne hp.1 fun h => by rw [← h] at hpZ; linarith
  have hphi : p < hi := lt_of_le_of_ne hp.2 fun h => by rw [h] at hpZ; linarith
  refine ⟨p, hp0, ⟨j₀, hplo⟩, ⟨i₀, hphi⟩, by linarith [hpZ], ⟨fun j => (F j).supply_foc p,
    fun i => (C i).demand_spec hp0, ?_⟩⟩
  have : aggDemand C p = aggSupply F p := by linarith [hpZ]
  exact this

/-! ## Constant returns to scale (footnote 10 and Figure 10.C.4) -/

/-- **Footnote 10** (MWG, p. 320). With `c(q) = cq` and `p > c`, profit has no maximum
(`q(p) = ∞`). -/
theorem footnote_10_C_10 {c p : ℝ} (hcp : c < p) (q : ℝ) :
    ∃ q', 0 ≤ q' ∧ p * q - c * q < p * q' - c * q' :=
  ⟨|q| + 1, by positivity, by nlinarith [le_abs_self q, abs_nonneg q]⟩

/-- **Figure 10.C.4** (MWG, p. 321). With `cⱼ(q) = cq` for all `j` (at least one firm) and some
`φᵢ'(0) > c`, every equilibrium has `p* = c` and aggregate output `x(c)`. -/
theorem figure_10_C_4_price [Nonempty κ] {C : ι → QLConsumer} {c : ℝ} (hc : 0 < c)
    (hgap : ∃ i, c < (C i).dφ 0) {x : ι → ℝ} {q : κ → ℝ} {p : ℝ}
    (h : IsQLEqm C (fun _ => linearFirm c hc) x q p) :
    p = c ∧ ∑ i, x i = aggDemand C c := by
  have hpc : p ≤ c := (h.1 (Classical.arbitrary κ)).2.1
  have hpeq : p = c := by
    refine le_antisymm hpc (not_lt.1 fun hlt => ?_)
    have hq0 : ∀ j, q j = 0 := fun j => by
      by_contra hne
      have := (h.1 j).2.2 (lt_of_le_of_ne (h.1 j).1 (Ne.symm hne))
      simp only [linearFirm] at this
      linarith
    have hs : ∑ i, x i = 0 := by rw [h.2.2]; exact Finset.sum_eq_zero fun j _ => hq0 j
    obtain ⟨i, hi⟩ := hgap
    have hx0 := (Finset.sum_eq_zero_iff_of_nonneg fun k _ => (h.2.1 k).1).1 hs i
      (Finset.mem_univ i)
    have h1 := (h.2.1 i).2.1
    rw [hx0] at h1
    linarith
  subst hpeq
  exact ⟨rfl, Finset.sum_congr rfl fun i _ => ((C i).demand_eq (h.2.1 i)).symm⟩

/-- **Figure 10.C.4** (MWG, p. 321). With constant returns `cⱼ(q) = cq`, `p* = c` and any
division of the aggregate output `x(c)` among firms is an equilibrium; with two firms
`j₁ ≠ j₂` and `x(c) > 0`, giving all output to `j₁` or all to `j₂` are two different equilibria:
individual outputs are not uniquely determined when `J > 1`. -/
theorem figure_10_C_4_indeterminate [DecidableEq κ] {C : ι → QLConsumer} {c : ℝ} (hc : 0 < c)
    (j₁ j₂ : κ) (hj : j₁ ≠ j₂) (hgap : ∃ i, c < (C i).dφ 0) :
    IsQLEqm C (fun _ => linearFirm c hc) (fun i => (C i).demand c)
      (fun j => if j = j₁ then aggDemand C c else 0) c ∧
    IsQLEqm C (fun _ => linearFirm c hc) (fun i => (C i).demand c)
      (fun j => if j = j₂ then aggDemand C c else 0) c ∧
    (fun j => if j = j₁ then aggDemand C c else 0) ≠
      (fun j => if j = j₂ then aggDemand C c else (0 : ℝ)) := by
  have hX : 0 < aggDemand C c := by
    obtain ⟨i, hi⟩ := hgap
    exact Finset.sum_pos' (fun k _ => (C k).demand_nonneg hc)
      ⟨i, Finset.mem_univ i, ((C i).demand_pos_iff hc).2 hi⟩
  have hgood : ∀ j₀ : κ, IsQLEqm C (fun _ => linearFirm c hc) (fun i => (C i).demand c)
      (fun j => if j = j₀ then aggDemand C c else 0) c := by
    intro j₀
    refine ⟨fun j => ⟨?_, by simp [linearFirm], fun _ => by simp [linearFirm]⟩,
      fun i => (C i).demand_spec hc, ?_⟩
    · dsimp only
      split_ifs <;> simp [hX.le]
    · simp [aggDemand]
  refine ⟨hgood j₁, hgood j₂, fun heq => ?_⟩
  have := congrFun heq j₁
  simp [hj] at this
  linarith

/-! ## Figure 10.C.8: nonexistence with a nonconvex technology -/

/-- The nonconvex cost of Figure 10.C.8: `c(q) = 2q - q² + q³/3`, with marginal cost
`c'(q) = 1 + (q - 1)²` rising, falling, then rising. -/
noncomputable def figure_10_C_8_cost (q : ℝ) : ℝ := 2 * q - q ^ 2 + q ^ 3 / 3

/-- **Figure 10.C.8** (MWG, p. 324). One consumer with `φ(x) = (5/2)(1 - e^{-x})` and one firm
with the continuous, differentiable but nonconvex cost `2q - q² + q³/3`: for any endowment and
shares there is no competitive equilibrium. The supply correspondence jumps from `0` to
`q ≥ 3/2` at `p = 5/4`, while demand at `p ≥ 5/4` is below `log 2 < 3/2`. -/
theorem figure_10_C_8_no_equilibrium (ωm : Fin 1 → ℝ) (θ : Fin 1 → Fin 1 → ℝ)
    (a : Allocation (Fin 1) (Fin 1) 2) (p : ℝ) :
    ¬ (qlEconomy (fun _ => (expConsumer (5 / 2) (by norm_num)).φ)
      (fun _ => figure_10_C_8_cost) ωm θ).IsCompetitiveEqm a (qlPrice p) := by
  intro h
  set C := expConsumer (5 / 2) (by norm_num) with hC
  have hp : 0 < p := ql_eqm_price_pos 0 C.φ_strictMono h
  have hd := (ql_demand_iff C.φ p _ (a.x 0)).1 (h.2.1 0)
  have hfoc := (C.max_iff hd.1).1 hd.2.2
  have hs := (ql_supply_iff figure_10_C_8_cost p (a.y 0)).1 (h.1 0)
  have hclear : a.x 0 1 = a.y 0 1 := by
    have := h.2.2 1
    simpa [qlEconomy] using this
  set q := a.y 0 1 with hq
  have hprofit := hs.2.2
  rcases eq_or_lt_of_le hs.1 with h0 | hpos
  · -- no output: then no consumption, so `p ≥ φ'(0) = 5/2`, but output `3/2` is profitable
    have hx0 : a.x 0 1 = 0 := by rw [hclear, ← h0]
    have h1 := hfoc.2.1
    rw [hx0] at h1
    simp only [hC, expConsumer, neg_zero, Real.exp_zero, mul_one] at h1
    have h2 := hprofit (3 / 2) (by norm_num)
    rw [← h0] at h2
    simp only [figure_10_C_8_cost] at h2
    nlinarith
  · -- positive output: `p = c'(q)` and nonnegative profit force `q ≥ 3/2`
    have hder : HasDerivWithinAt (fun z => p * z - figure_10_C_8_cost z)
        (p - (2 - 2 * q + q ^ 2)) (Set.Ici 0) q := by
      have h1 := ((hasDerivAt_id q).const_mul p).sub
        ((((hasDerivAt_id q).const_mul 2).sub (hasDerivAt_pow 2 q)).add
          ((hasDerivAt_pow 3 q).div_const 3))
      exact (h1.congr_deriv (by simp only [Nat.cast_ofNat]; ring)).hasDerivWithinAt
    have hnec := (foc_max_necessary hder hs.1 hprofit).2 hpos
    have hpq : p = 2 - 2 * q + q ^ 2 := by linarith
    have h0 := hprofit 0 le_rfl
    simp only [figure_10_C_8_cost] at h0
    have h1 : 0 ≤ q ^ 2 * (2 * q / 3 - 1) := by rw [hpq] at h0; nlinarith
    have hq32 : 3 / 2 ≤ q := by
      have := (mul_nonneg_iff_of_pos_left (by positivity : 0 < q ^ 2)).1 h1
      linarith
    have hxpos : 0 < a.x 0 1 := by rw [hclear]; exact hpos
    have he := hfoc.2.2 hxpos
    rw [hclear] at he
    simp only [hC, expConsumer] at he
    have hexp : Real.exp (-q) ≤ Real.exp (-(3 / 2)) := Real.exp_le_exp.2 (by linarith)
    have h52 : (5 / 2 : ℝ) ≤ Real.exp (3 / 2) := by
      have := Real.add_one_le_exp (3 / 2 : ℝ); linarith
    have hinv : Real.exp (-(3 / 2)) * Real.exp (3 / 2) = 1 := by
      rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (-(3 / 2)), Real.exp_pos (-q), sq_nonneg (q - 1)]

end MWG.CompetitiveMarkets

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The fundamental welfare theorems in a partial equilibrium context (MWG Section 10.D)

MWG, pp. 325-328, and Exercises 10.D.1-10.D.4 (p. 346). Pareto optimality is Definition 10.B.2
for the quasilinear economy of Section 10.C.

* (10.D.1) (p. 325): for fixed levels of good `ℓ`, the utility vectors attainable by
  distributing the numeraire are `{u : ∑ uᵢ ≤ ∑ φᵢ(x̄ᵢ) + ω_m - ∑ cⱼ(q̄ⱼ)}`: the boundary is a
  hyperplane with normal `(1, …, 1)` (`eq_10_D_1`).
* Pareto optimal allocations are exactly the feasible allocations whose levels of good `ℓ`
  maximize the Marshallian aggregate surplus `∑ φᵢ(xᵢ) - ∑ cⱼ(qⱼ)` subject to `∑ xᵢ = ∑ qⱼ`
  (problem (10.D.2)) and which waste no numeraire (`ql_pareto_iff`).
* (10.D.3)-(10.D.5) (p. 326): the first-order conditions of (10.D.2) are necessary
  (`optimalLevels_foc`) and sufficient (`IsQLEqm.isOptimalLevels`); they are (10.C.1)-(10.C.3)
  with `μ` in place of `p*`.
* **Proposition 10.D.1** (first welfare theorem) and **Proposition 10.D.2** (second welfare
  theorem, given that an equilibrium exists, which Section 10.C provides for strictly convex
  costs; correction 2).
* Footnote 15 and **Exercise 10.D.1**: uniqueness of optimal consumption levels, of aggregate
  output, and (with strictly convex costs) of individual outputs.
* Problem (10.D.6), **Exercise 10.D.3** and **Exercise 10.D.4** (p. 328).
-/

namespace MWG.CompetitiveMarkets

open Filter Topology MWG.ConsumerChoice

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **(10.D.2), (10.E.1)** (MWG, pp. 326, 329). The Marshallian aggregate surplus
`S(x, q) = ∑ᵢ φᵢ(xᵢ) - ∑ⱼ cⱼ(qⱼ)`. -/
def qlSurplus (φ : ι → ℝ → ℝ) (c : κ → ℝ → ℝ) (x : ι → ℝ) (q : κ → ℝ) : ℝ :=
  ∑ i, φ i (x i) - ∑ j, c j (q j)

/-- **Problem (10.D.2)** (MWG, p. 326). `(x, q)` are optimal consumption and production levels
of good `ℓ`: nonnegative, `∑ xᵢ = ∑ qⱼ`, and maximizing aggregate surplus among such levels. -/
def IsOptimalLevels (φ : ι → ℝ → ℝ) (c : κ → ℝ → ℝ) (x : ι → ℝ) (q : κ → ℝ) : Prop :=
  (∀ i, 0 ≤ x i) ∧ (∀ j, 0 ≤ q j) ∧ ∑ i, x i = ∑ j, q j ∧
    ∀ x' q', (∀ i, 0 ≤ x' i) → (∀ j, 0 ≤ q' j) → ∑ i, x' i = ∑ j, q' j →
      qlSurplus φ c x' q' ≤ qlSurplus φ c x q

/-- Feasibility (Definition 10.B.1) in the quasilinear economy, unfolded. -/
theorem ql_feasible_iff (φ : ι → ℝ → ℝ) (c : κ → ℝ → ℝ) (ωm : ι → ℝ) (θ : ι → κ → ℝ)
    (a : Allocation ι κ 2) :
    (qlEconomy φ c ωm θ).toEconomy.IsFeasible a ↔
      (∀ i, 0 ≤ a.x i 1) ∧ (∀ j, 0 ≤ a.y j 1 ∧ c j (a.y j 1) ≤ -a.y j 0) ∧
      ∑ i, a.x i 0 ≤ ∑ i, ωm i + ∑ j, a.y j 0 ∧ ∑ i, a.x i 1 ≤ ∑ j, a.y j 1 := by
  simp only [Economy.IsFeasible, Economy.IsAllocation, PrivEconomy.toEconomy, qlEconomy,
    Fin.forall_fin_two, Finset.sum_apply]
  simp only [Set.mem_ofPred_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Finset.sum_const_zero, zero_add]
  tauto

omit [Fintype κ] in
/-- Utilities in the quasilinear economy: `uᵢ(m, x) = m + φᵢ(x)`. -/
theorem ql_utility (φ : ι → ℝ → ℝ) (c : κ → ℝ → ℝ) (ωm : ι → ℝ) (θ : ι → κ → ℝ) (i : ι)
    (v : Fin 2 → ℝ) : (qlEconomy φ c ωm θ).toEconomy.u i v = v 0 + φ i (v 1) := rfl

/-- In a feasible allocation, `∑ᵢ uᵢ ≤ ω_m + S(x, q)`. -/
theorem ql_sum_utility_le {φ : ι → ℝ → ℝ} {c : κ → ℝ → ℝ} {ωm : ι → ℝ} {θ : ι → κ → ℝ}
    {a : Allocation ι κ 2} (ha : (qlEconomy φ c ωm θ).toEconomy.IsFeasible a) :
    ∑ i, (qlEconomy φ c ωm θ).toEconomy.u i (a.x i) ≤
      ∑ i, ωm i + qlSurplus φ c (fun i => a.x i 1) (fun j => a.y j 1) := by
  rw [ql_feasible_iff] at ha
  simp only [ql_utility, Finset.sum_add_distrib, qlSurplus]
  have h1 := ha.2.2.1
  have h2 : ∑ j, a.y j 0 ≤ -∑ j, c j (a.y j 1) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun j _ => by linarith [(ha.2.1 j).2]
  linarith

/-- **(10.D.1)** (MWG, p. 325). With the levels of good `ℓ` fixed at `(x̄, q̄)`, the utility
vectors attainable by distributing the remaining numeraire `ω_m - ∑ cⱼ(q̄ⱼ)` are exactly
`{u : ∑ uᵢ ≤ ∑ φᵢ(x̄ᵢ) + ω_m - ∑ cⱼ(q̄ⱼ)}` (at least one consumer). -/
theorem eq_10_D_1 [Nonempty ι] (φ : ι → ℝ → ℝ) (c : κ → ℝ → ℝ) (ωm : ℝ) (x : ι → ℝ)
    (q : κ → ℝ) :
    {u : ι → ℝ | ∃ m : ι → ℝ, ∑ i, m i ≤ ωm - ∑ j, c j (q j) ∧ ∀ i, u i ≤ m i + φ i (x i)} =
      {u | ∑ i, u i ≤ ∑ i, φ i (x i) + ωm - ∑ j, c j (q j)} := by
  ext u
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨m, hm, hu⟩
    have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hu i
    rw [Finset.sum_add_distrib] at this
    linarith
  · intro hu
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    classical
    set slack := ∑ i, φ i (x i) + ωm - ∑ j, c j (q j) - ∑ i, u i with hslack
    refine ⟨fun i => u i - φ i (x i) + if i = i₀ then slack else 0, ?_, fun i => ?_⟩
    · simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq',
        Finset.mem_univ, ↓reduceIte, hslack]
      linarith
    · have : (0 : ℝ) ≤ if i = i₀ then slack else 0 := by
        split_ifs
        · simp only [hslack]; linarith
        · exact le_rfl
      linarith

/-- A positive sum of reals has a positive term. -/
theorem exists_pos_of_sum_pos {α : Type*} [Fintype α] {f : α → ℝ} (h : 0 < ∑ i, f i) :
    ∃ i, 0 < f i := by
  obtain ⟨i, -, hi⟩ := Finset.exists_lt_of_sum_lt (s := Finset.univ) (f := fun _ => (0 : ℝ))
    (g := f) (by simpa using h)
  exact ⟨i, hi⟩

/-- Lowering production to match consumption: from nonnegative `q'` with `X ≤ ∑ q'ⱼ`, scale to
`q''` with `∑ q''ⱼ = X` and lower cost (strictly lower if `X < ∑ q'ⱼ` and costs are strictly
increasing). -/
theorem ql_reduce {c : κ → ℝ → ℝ} (hc : ∀ j, StrictMonoOn (c j) (Set.Ici 0)) {q' : κ → ℝ}
    (hq' : ∀ j, 0 ≤ q' j) {X : ℝ} (hX : 0 ≤ X) (hXq : X ≤ ∑ j, q' j) :
    ∃ q'' : κ → ℝ, (∀ j, 0 ≤ q'' j) ∧ ∑ j, q'' j = X ∧ ∑ j, c j (q'' j) ≤ ∑ j, c j (q' j) ∧
      (X < ∑ j, q' j → ∑ j, c j (q'' j) < ∑ j, c j (q' j)) := by
  rcases eq_or_lt_of_le (Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => hq' j) with h0 | hpos
  · have hX0 : X = 0 := le_antisymm (h0 ▸ hXq) hX
    refine ⟨q', hq', by rw [← h0, hX0], le_rfl, fun h => ?_⟩
    rw [← h0] at h; exact absurd h (by linarith)
  · set r := X / ∑ j, q' j with hr
    have hr0 : 0 ≤ r := div_nonneg hX hpos.le
    have hr1 : r ≤ 1 := (div_le_one hpos).2 hXq
    have hle : ∀ j, q' j * r ≤ q' j := fun j => mul_le_of_le_one_right (hq' j) hr1
    refine ⟨fun j => q' j * r, fun j => mul_nonneg (hq' j) hr0, ?_, ?_, fun hlt => ?_⟩
    · rw [← Finset.sum_mul, hr]; field_simp
    · exact Finset.sum_le_sum fun j _ =>
        (hc j).monotoneOn (mul_nonneg (hq' j) hr0) (hq' j) (hle j)
    · have hr1' : r < 1 := (div_lt_one hpos).2 hlt
      obtain ⟨j, hj⟩ := exists_pos_of_sum_pos hpos
      refine Finset.sum_lt_sum (fun k _ =>
        (hc k).monotoneOn (mul_nonneg (hq' k) hr0) (hq' k) (hle k)) ⟨j, Finset.mem_univ j, ?_⟩
      exact hc j (mul_nonneg (hq' j) hr0) (hq' j) (mul_lt_of_lt_one_right hj hr1')

/-- **Pareto optimality via aggregate surplus** (MWG, p. 325). A feasible allocation is Pareto
optimal iff the sum of utilities reaches `ω_m + S(x', q')` for all nonnegative levels with
`∑ x'ᵢ ≤ ∑ q'ⱼ`. -/
theorem ql_pareto_iff_le [Nonempty ι] (φ : ι → ℝ → ℝ) (c : κ → ℝ → ℝ) (ωm : ι → ℝ)
    (θ : ι → κ → ℝ) (a : Allocation ι κ 2) :
    (qlEconomy φ c ωm θ).toEconomy.IsParetoOptimal a ↔
      (qlEconomy φ c ωm θ).toEconomy.IsFeasible a ∧
      ∀ x' q', (∀ i, 0 ≤ x' i) → (∀ j, 0 ≤ q' j) → ∑ i, x' i ≤ ∑ j, q' j →
        ∑ i, ωm i + qlSurplus φ c x' q' ≤ ∑ i, (qlEconomy φ c ωm θ).toEconomy.u i (a.x i) := by
  classical
  constructor
  · rintro ⟨ha, hno⟩
    refine ⟨ha, fun x' q' hx' hq' hsum => not_lt.1 fun hlt => hno ?_⟩
    set n : ℝ := (Fintype.card ι : ℝ) with hn
    have hn0 : 0 < n := by rw [hn]; exact_mod_cast Fintype.card_pos
    set δ := ∑ i, ωm i + qlSurplus φ c x' q' -
      ∑ i, (qlEconomy φ c ωm θ).toEconomy.u i (a.x i) with hδ
    have hδ0 : 0 < δ := by rw [hδ]; linarith
    refine ⟨⟨fun i => ![(qlEconomy φ c ωm θ).toEconomy.u i (a.x i) - φ i (x' i) + δ / n, x' i],
      fun j => ![-c j (q' j), q' j]⟩, ?_, fun i => ?_, ?_⟩
    · rw [ql_feasible_iff]
      refine ⟨fun i => by simpa using hx' i, fun j => ⟨by simpa using hq' j, by simp⟩, ?_, ?_⟩
      · simp only [Matrix.cons_val_zero, Finset.sum_add_distrib, Finset.sum_sub_distrib,
          Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.sum_neg_distrib]
        have : (Fintype.card ι : ℝ) * (δ / n) = δ := by rw [← hn]; field_simp
        rw [this, hδ]
        simp only [qlSurplus]
        linarith
      · simpa using hsum
    · simp only [ql_utility, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      have : 0 < δ / n := div_pos hδ0 hn0
      linarith
    · obtain ⟨i⟩ := ‹Nonempty ι›
      refine ⟨i, ?_⟩
      simp only [ql_utility, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      have : 0 < δ / n := div_pos hδ0 hn0
      linarith
  · rintro ⟨ha, hmax⟩
    refine ⟨ha, fun ⟨a', ha', hle, i, hi⟩ => ?_⟩
    have h1 := ql_sum_utility_le ha'
    have hfa := (ql_feasible_iff φ c ωm θ a').1 ha'
    have h2 := hmax (fun i => a'.x i 1) (fun j => a'.y j 1) hfa.1 (fun j => (hfa.2.1 j).1)
      hfa.2.2.2
    have h3 : ∑ k, (qlEconomy φ c ωm θ).toEconomy.u k (a.x k) <
        ∑ k, (qlEconomy φ c ωm θ).toEconomy.u k (a'.x k) :=
      Finset.sum_lt_sum (fun k _ => hle k) ⟨i, Finset.mem_univ i, hi⟩
    linarith

/-- **Pareto optimal allocations** (MWG, pp. 325-326). With strictly increasing costs, a feasible
allocation is Pareto optimal iff its levels of good `ℓ` solve problem (10.D.2) and no numeraire
is wasted: `∑ᵢ uᵢ = ω_m + S(x, q)`. -/
theorem ql_pareto_iff [Nonempty ι] (φ : ι → ℝ → ℝ) (c : κ → ℝ → ℝ)
    (hc : ∀ j, StrictMonoOn (c j) (Set.Ici 0)) (ωm : ι → ℝ) (θ : ι → κ → ℝ)
    (a : Allocation ι κ 2) :
    (qlEconomy φ c ωm θ).toEconomy.IsParetoOptimal a ↔
      (qlEconomy φ c ωm θ).toEconomy.IsFeasible a ∧
      IsOptimalLevels φ c (fun i => a.x i 1) (fun j => a.y j 1) ∧
      ∑ i, (qlEconomy φ c ωm θ).toEconomy.u i (a.x i) =
        ∑ i, ωm i + qlSurplus φ c (fun i => a.x i 1) (fun j => a.y j 1) := by
  rw [ql_pareto_iff_le]
  constructor
  · rintro ⟨ha, hmax⟩
    have hf := (ql_feasible_iff φ c ωm θ a).1 ha
    have hup := ql_sum_utility_le ha
    have hself := hmax _ _ hf.1 (fun j => (hf.2.1 j).1) hf.2.2.2
    have hbal : ∑ i, a.x i 1 = ∑ j, a.y j 1 := by
      by_contra hne
      have hlt : ∑ i, a.x i 1 < ∑ j, a.y j 1 := lt_of_le_of_ne hf.2.2.2 hne
      obtain ⟨q'', hq'', hs'', -, hstrict⟩ := ql_reduce hc (fun j => (hf.2.1 j).1)
        (Finset.sum_nonneg fun i _ => hf.1 i) hf.2.2.2
      have := hmax (fun i => a.x i 1) q'' hf.1 hq'' hs''.symm.le
      have := hstrict hlt
      simp only [qlSurplus] at *
      linarith
    refine ⟨ha, ⟨hf.1, fun j => (hf.2.1 j).1, hbal, fun x' q' hx' hq' hs => ?_⟩, by linarith⟩
    have := hmax x' q' hx' hq' hs.le
    linarith
  · rintro ⟨ha, ⟨-, -, -, hopt⟩, heq⟩
    refine ⟨ha, fun x' q' hx' hq' hs => ?_⟩
    obtain ⟨q'', hq'', hs'', hle, -⟩ := ql_reduce hc hq' (Finset.sum_nonneg fun i _ => hx' i) hs
    have := hopt x' q'' hx' hq'' hs''.symm
    simp only [qlSurplus] at *
    linarith

/-! ## First-order conditions (10.D.3)-(10.D.5) -/

/-- **Sufficiency of (10.D.3)-(10.D.5)** (MWG, p. 326). Levels satisfying the conditions with
multiplier `μ` (which are (10.C.1)-(10.C.3) with `μ` for `p*`) solve problem (10.D.2). -/
theorem IsQLEqm.isOptimalLevels {C : ι → QLConsumer} {F : κ → QLFirm} {x : ι → ℝ}
    {q : κ → ℝ} {μ : ℝ} (h : IsQLEqm C F x q μ) :
    IsOptimalLevels (fun i => (C i).φ) (fun j => (F j).c) x q := by
  refine ⟨fun i => (h.2.1 i).1, fun j => (h.1 j).1, h.2.2, fun x' q' hx' hq' hs => ?_⟩
  have hcons : ∀ i, (C i).φ (x' i) - μ * x' i ≤ (C i).φ (x i) - μ * x i := fun i =>
    ((C i).max_iff (h.2.1 i).1).2 (h.2.1 i) _ (hx' i)
  have hfirm : ∀ j, μ * q' j - (F j).c (q' j) ≤ μ * q j - (F j).c (q j) := fun j =>
    ((F j).max_iff (h.1 j).1).2 (h.1 j).2 _ (hq' j)
  have e1 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hcons i
  have e2 := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hfirm j
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at e1 e2
  simp only [qlSurplus]
  rw [hs] at e1
  rw [h.2.2] at e1
  linarith

/-- The value of a function after updating one coordinate of its argument. -/
theorem sum_update_apply [DecidableEq ι] (g : ι → ℝ → ℝ) (x : ι → ℝ) (i : ι) (v : ℝ) :
    ∑ k, g k (Function.update x i v k) = ∑ k, g k (x k) + (g i v - g i (x i)) := by
  have h : ∀ k, g k (Function.update x i v k) =
      g k (x k) + if k = i then g i v - g i (x i) else 0 := by
    intro k
    by_cases hk : k = i
    · subst hk; simp
    · simp [hk]
  simp only [h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

theorem sum_update_id [DecidableEq ι] (x : ι → ℝ) (i : ι) (v : ℝ) :
    ∑ k, Function.update x i v k = ∑ k, x k + (v - x i) :=
  sum_update_apply (fun _ t => t) x i v

/-- Shifting a function's argument: `t ↦ f(a + t)` has derivative `f'(a)` within `[0, ∞)` at `0`
when `f` has it within `[0, ∞)` at `a ≥ 0`. -/
theorem hasDerivWithinAt_shift {f : ℝ → ℝ} {f'a a : ℝ}
    (hf : HasDerivWithinAt f f'a (Set.Ici 0) a) (ha : 0 ≤ a) :
    HasDerivWithinAt (fun t => f (a + t)) f'a (Set.Ici 0) 0 := by
  have hh : HasDerivWithinAt (fun t : ℝ => a + t) 1 (Set.Ici 0) 0 :=
    ((hasDerivAt_id 0).const_add a).hasDerivWithinAt
  have hmap : Set.MapsTo (fun t : ℝ => a + t) (Set.Ici 0) (Set.Ici 0) :=
    fun t ht => by simp only [Set.mem_Ici] at ht ⊢; linarith
  exact (show HasDerivWithinAt f f'a (Set.Ici 0) (a + 0) by simpa using hf).comp 0 hh hmap
    |>.congr_deriv (mul_one _)

/-- **Necessity of (10.D.3)-(10.D.5)** (MWG, p. 326). Optimal levels of good `ℓ` satisfy the
first-order conditions for some multiplier `μ`. -/
theorem optimalLevels_foc {C : ι → QLConsumer} {F : κ → QLFirm} {x : ι → ℝ} {q : κ → ℝ}
    (h : IsOptimalLevels (fun i => (C i).φ) (fun j => (F j).c) x q) :
    ∃ μ, IsQLEqm C F x q μ := by
  classical
  obtain ⟨hx, hq, hs, hopt⟩ := h
  -- perturbation: raise `xᵢ` and `qⱼ` together
  have hpert : ∀ i j (t : ℝ), 0 ≤ x i + t → 0 ≤ q j + t →
      (C i).φ (x i + t) - (F j).c (q j + t) ≤ (C i).φ (x i) - (F j).c (q j) := by
    intro i j t hxt hqt
    have := hopt (Function.update x i (x i + t)) (Function.update q j (q j + t))
      (fun k => by by_cases hk : k = i <;> simp [hk, hxt, hx k])
      (fun k => by by_cases hk : k = j <;> simp [hk, hqt, hq k])
      (by rw [sum_update_id, sum_update_id, hs]; ring)
    simp only [qlSurplus, sum_update_apply (fun k => (C k).φ),
      sum_update_apply (fun k => (F k).c)] at this
    linarith
  -- (A) `φᵢ'(xᵢ) ≤ cⱼ'(qⱼ)`
  have hA : ∀ i j, (C i).dφ (x i) ≤ (F j).dc (q j) := by
    intro i j
    have hd : HasDerivWithinAt (fun t => (C i).φ (x i + t) - (F j).c (q j + t))
        ((C i).dφ (x i) - (F j).dc (q j)) (Set.Ici 0) 0 :=
      (hasDerivWithinAt_shift ((C i).hasDeriv _ (hx i)) (hx i)).sub
        (hasDerivWithinAt_shift ((F j).hasDeriv _ (hq j)) (hq j))
    have := foc_local_necessary hd (by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht' : 0 < t := ht
      simpa using hpert i j t (by linarith [hx i]) (by linarith [hq j]))
    linarith
  -- (B) at interior points `φᵢ'(xᵢ) = cⱼ'(qⱼ)`
  have hB : ∀ i j, 0 < x i → 0 < q j → (C i).dφ (x i) = (F j).dc (q j) := by
    intro i j hxi hqj
    have hd : HasDerivAt (fun t => (C i).φ (x i + t) - (F j).c (q j + t))
        ((C i).dφ (x i) - (F j).dc (q j)) 0 := by
      have h1 := HasDerivAt.comp_const_add (x i) 0
        (by simpa using foc_hasDerivAt (C i).hasDeriv hxi)
      have h2 := HasDerivAt.comp_const_add (q j) 0
        (by simpa using foc_hasDerivAt (F j).hasDeriv hqj)
      exact h1.sub h2
    have hmax : IsLocalMax (fun t => (C i).φ (x i + t) - (F j).c (q j + t)) 0 := by
      filter_upwards [Ioi_mem_nhds (neg_lt_zero.2 (lt_min hxi hqj))] with t ht
      have ht' : -min (x i) (q j) < t := ht
      have := hpert i j t (by linarith [min_le_left (x i) (q j)])
        (by linarith [min_le_right (x i) (q j)])
      simpa using this
    have := hmax.hasDerivAt_eq_zero hd
    linarith
  by_cases hagg : 0 < ∑ i, x i
  · obtain ⟨i₀, hi₀⟩ := exists_pos_of_sum_pos hagg
    obtain ⟨j₀, hj₀⟩ := exists_pos_of_sum_pos (hs ▸ hagg)
    refine ⟨(C i₀).dφ (x i₀), fun j => ⟨hq j, hA i₀ j, fun hj => (hB i₀ j hi₀ hj)⟩,
      fun i => ⟨hx i, ?_, fun hi => ?_⟩, hs⟩
    · rw [hB i₀ j₀ hi₀ hj₀]; exact hA i j₀
    · rw [hB i j₀ hi hj₀, hB i₀ j₀ hi₀ hj₀]
  · have hx0 : ∀ i, x i = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg fun k _ => hx k).1
        (le_antisymm (not_lt.1 hagg) (Finset.sum_nonneg fun k _ => hx k)) i (Finset.mem_univ i)
    have hq0 : ∀ j, q j = 0 := fun j =>
      (Finset.sum_eq_zero_iff_of_nonneg fun k _ => hq k).1
        (by rw [← hs]; exact Finset.sum_eq_zero fun i _ => hx0 i) j (Finset.mem_univ j)
    have hqn : ∀ j, ¬ 0 < q j := fun j => by rw [hq0 j]; exact lt_irrefl 0
    have hxn : ∀ i, ¬ 0 < x i := fun i => by rw [hx0 i]; exact lt_irrefl 0
    by_cases hne : Nonempty ι
    · obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ (fun i => (C i).dφ 0)
        (Finset.univ_nonempty_iff.2 hne)
      refine ⟨(C i₀).dφ 0, fun j => ⟨hq j, ?_, fun hj => absurd hj (hqn j)⟩,
        fun i => ⟨hx i, ?_, fun hi => absurd hi (hxn i)⟩, hs⟩
      · have := hA i₀ j; rw [hx0, hq0] at this; rw [hq0]; exact this
      · rw [hx0]; exact hi₀ i (Finset.mem_univ i)
    · exact ⟨0, fun j => ⟨hq j, ((F j).dc_pos _ (hq j)).le, fun hj => absurd hj (hqn j)⟩,
        fun i => absurd ⟨i⟩ hne, hs⟩

/-- **(10.D.3)-(10.D.5)** (MWG, p. 326). Given the convexity assumptions, levels of good `ℓ`
solve problem (10.D.2) iff they satisfy the first-order conditions for some `μ`. -/
theorem optimalLevels_iff_foc (C : ι → QLConsumer) (F : κ → QLFirm) (x : ι → ℝ) (q : κ → ℝ) :
    IsOptimalLevels (fun i => (C i).φ) (fun j => (F j).c) x q ↔ ∃ μ, IsQLEqm C F x q μ :=
  ⟨optimalLevels_foc, fun ⟨_, h⟩ => h.isOptimalLevels⟩

/-! ## The welfare theorems -/

/-- The sum of utilities at a competitive equilibrium of the quasilinear economy is
`ω_m + S(x*, q*)`: no numeraire is wasted. -/
theorem ql_eqm_sum_utility (C : ι → QLConsumer) (F : κ → QLFirm) (ωm : ι → ℝ)
    (θ : ι → κ → ℝ) (hθ : ∀ j, ∑ i, θ i j = 1) {x : ι → ℝ} {q : κ → ℝ} {p : ℝ}
    (hs : ∑ i, x i = ∑ j, q j) :
    ∑ i, (qlEconomyOf C F ωm θ).toEconomy.u i ((qlAllocation F ωm θ x q p).x i) =
      ∑ i, ωm i + qlSurplus (fun i => (C i).φ) (fun j => (F j).c) x q := by
  simp only [qlEconomyOf, ql_utility, qlAllocation, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, qlSurplus, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun i j => θ i j * (p * q j - (F j).c (q j)))]
  simp only [← Finset.sum_mul, hθ, one_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hs]
  ring

/-- **Proposition 10.D.1 (the first fundamental theorem of welfare economics)** (MWG, p. 326).
If the price `p*` and an allocation form a competitive equilibrium (Definition 10.B.3) of the
quasilinear economy, the allocation is Pareto optimal (Definition 10.B.2). -/
theorem proposition_10_D_1 [Nonempty ι] (C : ι → QLConsumer) (F : κ → QLFirm) (ωm : ι → ℝ)
    (θ : ι → κ → ℝ) (hθ : ∀ j, ∑ i, θ i j = 1) (a : Allocation ι κ 2) (p : ℝ)
    (h : (qlEconomyOf C F ωm θ).IsCompetitiveEqm a (qlPrice p)) :
    (qlEconomyOf C F ωm θ).toEconomy.IsParetoOptimal a := by
  have hfeas := h.isFeasible
  obtain ⟨hq, ha⟩ := (ql_isCompetitiveEqm_iff C F ωm θ hθ a p).1 h
  rw [qlEconomyOf, ql_pareto_iff _ _ (fun j => (F j).c_strictMono)]
  refine ⟨hfeas, hq.isOptimalLevels, ?_⟩
  have := ql_eqm_sum_utility C F ωm θ hθ (p := p) hq.2.2
  rw [← ha] at this
  exact this

/-- Two solutions of problem (10.D.2) have the same aggregate surplus. -/
theorem IsOptimalLevels.surplus_eq {φ : ι → ℝ → ℝ} {c : κ → ℝ → ℝ} {x x' : ι → ℝ}
    {q q' : κ → ℝ} (h : IsOptimalLevels φ c x q) (h' : IsOptimalLevels φ c x' q') :
    qlSurplus φ c x q = qlSurplus φ c x' q' :=
  le_antisymm (h'.2.2.2 x q h.1 h.2.1 h.2.2.1) (h.2.2.2 x' q' h'.1 h'.2.1 h'.2.2.1)

/-- **Proposition 10.D.2 (the second fundamental theorem of welfare economics)** (MWG, p. 327),
given that a competitive equilibrium exists (Section 10.C). For the utility levels `u*` of any
Pareto optimal allocation there are transfers `Tᵢ` of the numeraire with `∑ Tᵢ = 0` such that a
competitive equilibrium reached from the endowments `ω_{mi} + Tᵢ` yields exactly `u*`. -/
theorem proposition_10_D_2_of_exists [Nonempty ι] (C : ι → QLConsumer) (F : κ → QLFirm)
    (ωm : ι → ℝ) (θ : ι → κ → ℝ) (hθ : ∀ j, ∑ i, θ i j = 1) (a : Allocation ι κ 2)
    (hPO : (qlEconomyOf C F ωm θ).toEconomy.IsParetoOptimal a)
    (hex : ∃ x q p, IsQLEqm C F x q p) :
    ∃ T : ι → ℝ, ∑ i, T i = 0 ∧ ∃ (a' : Allocation ι κ 2) (p : ℝ),
      (qlEconomyOf C F (ωm + T) θ).IsCompetitiveEqm a' (qlPrice p) ∧
      ∀ i, (qlEconomyOf C F (ωm + T) θ).toEconomy.u i (a'.x i) =
        (qlEconomyOf C F ωm θ).toEconomy.u i (a.x i) := by
  obtain ⟨x, q, p, hq⟩ := hex
  rw [qlEconomyOf, ql_pareto_iff _ _ (fun j => (F j).c_strictMono)] at hPO
  obtain ⟨-, hopt, hsum⟩ := hPO
  set e := qlAllocation F ωm θ x q p with he
  set T : ι → ℝ := fun i => (qlEconomyOf C F ωm θ).toEconomy.u i (a.x i) -
    (qlEconomyOf C F ωm θ).toEconomy.u i (e.x i) with hT
  have hS := hq.isOptimalLevels.surplus_eq hopt
  have hsumT : ∑ i, T i = 0 := by
    simp only [hT, Finset.sum_sub_distrib]
    have := ql_eqm_sum_utility C F ωm θ hθ (p := p) hq.2.2
    rw [← he] at this
    rw [this]
    simp only [qlEconomyOf] at hsum ⊢
    rw [hsum, hS]
    ring
  refine ⟨T, hsumT, qlAllocation F (ωm + T) θ x q p, p,
    ql_isCompetitiveEqm_of_isQLEqm hq _ θ hθ, fun i => ?_⟩
  simp only [hT, he, qlEconomyOf, ql_utility, qlAllocation, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.add_apply]
  ring

/-- **Proposition 10.D.2** (MWG, p. 327) under the assumptions of Section 10.C that give
existence (strictly convex costs, `cⱼ' → ∞`, `maxᵢ φᵢ'(0) > minⱼ cⱼ'(0)`). -/
theorem proposition_10_D_2 [Nonempty ι] [Nonempty κ] (C : ι → QLConsumer)
    (F : κ → QLFirmStrict) (hgap : ∃ i j, (F j).dc 0 < (C i).dφ 0) (ωm : ι → ℝ)
    (θ : ι → κ → ℝ) (hθ : ∀ j, ∑ i, θ i j = 1) (a : Allocation ι κ 2)
    (hPO : (qlEconomyOf C (fun j => (F j).toQLFirm) ωm θ).toEconomy.IsParetoOptimal a) :
    ∃ T : ι → ℝ, ∑ i, T i = 0 ∧ ∃ (a' : Allocation ι κ 2) (p : ℝ),
      (qlEconomyOf C (fun j => (F j).toQLFirm) (ωm + T) θ).IsCompetitiveEqm a' (qlPrice p) ∧
      ∀ i, (qlEconomyOf C (fun j => (F j).toQLFirm) (ωm + T) θ).toEconomy.u i (a'.x i) =
        (qlEconomyOf C (fun j => (F j).toQLFirm) ωm θ).toEconomy.u i (a.x i) := by
  obtain ⟨p, -, -, -, -, hq⟩ := ql_eqm_exists C F hgap
  exact proposition_10_D_2_of_exists C _ ωm θ hθ a hPO ⟨_, _, p, hq⟩

/-! ## Footnote 15 and Exercise 10.D.1: uniqueness of optimal levels -/

/-- **Exercise 10.D.1** (MWG, p. 346; footnote 15, p. 325). If every `φᵢ` is strictly concave
and every `cⱼ` convex on `ℝ₊`, the optimal individual consumption levels in problem (10.D.2) are
unique, and hence so is the optimal aggregate production level. -/
theorem exercise_10_D_1 {φ : ι → ℝ → ℝ} {c : κ → ℝ → ℝ}
    (hφ : ∀ i, StrictConcaveOn ℝ (Set.Ici 0) (φ i)) (hc : ∀ j, ConvexOn ℝ (Set.Ici 0) (c j))
    {x x' : ι → ℝ} {q q' : κ → ℝ} (h : IsOptimalLevels φ c x q)
    (h' : IsOptimalLevels φ c x' q') : x = x' ∧ ∑ j, q j = ∑ j, q' j := by
  have hS := h.surplus_eq h'
  set xm : ι → ℝ := fun i => (1 / 2 : ℝ) • x i + (1 / 2 : ℝ) • x' i with hxm
  set qm : κ → ℝ := fun j => (1 / 2 : ℝ) • q j + (1 / 2 : ℝ) • q' j with hqm
  have hxm0 : ∀ i, 0 ≤ xm i := fun i => by
    simp only [hxm, smul_eq_mul]; linarith [h.1 i, h'.1 i]
  have hqm0 : ∀ j, 0 ≤ qm j := fun j => by
    simp only [hqm, smul_eq_mul]; linarith [h.2.1 j, h'.2.1 j]
  have hsm : ∑ i, xm i = ∑ j, qm j := by
    simp only [hxm, hqm, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum, h.2.2.1,
      h'.2.2.1]
  have hle := h.2.2.2 xm qm hxm0 hqm0 hsm
  have hcost : ∑ j, c j (qm j) ≤ ∑ j, ((1 / 2 : ℝ) * c j (q j) + (1 / 2 : ℝ) * c j (q' j)) :=
    Finset.sum_le_sum fun j _ => by
      simpa [smul_eq_mul, hqm] using (hc j).2 (Set.mem_Ici.2 (h.2.1 j)) (Set.mem_Ici.2 (h'.2.1 j))
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  have hben : ∀ i, (1 / 2 : ℝ) * φ i (x i) + (1 / 2 : ℝ) * φ i (x' i) ≤ φ i (xm i) := fun i => by
    simpa [smul_eq_mul, hxm] using (hφ i).concaveOn.2 (Set.mem_Ici.2 (h.1 i))
      (Set.mem_Ici.2 (h'.1 i))
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  have hxx : x = x' := by
    by_contra hne
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
    have hstrict : (1 / 2 : ℝ) * φ i (x i) + (1 / 2 : ℝ) * φ i (x' i) < φ i (xm i) := by
      simpa [smul_eq_mul, hxm] using (hφ i).2 (Set.mem_Ici.2 (h.1 i)) (Set.mem_Ici.2 (h'.1 i)) hi
        (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    have hsumb : ∑ k, ((1 / 2 : ℝ) * φ k (x k) + (1 / 2 : ℝ) * φ k (x' k)) < ∑ k, φ k (xm k) :=
      Finset.sum_lt_sum (fun k _ => hben k) ⟨i, Finset.mem_univ i, hstrict⟩
    simp only [qlSurplus, Finset.sum_add_distrib, ← Finset.mul_sum] at hle hS hsumb hcost
    linarith
  exact ⟨hxx, by rw [← h.2.2.1, ← h'.2.2.1, hxx]⟩

/-- **Exercise 10.D.1** (MWG, p. 346), last part. If moreover every `cⱼ` is strictly convex,
the optimal individual production levels are unique too. -/
theorem exercise_10_D_1_strict {φ : ι → ℝ → ℝ} {c : κ → ℝ → ℝ}
    (hφ : ∀ i, StrictConcaveOn ℝ (Set.Ici 0) (φ i))
    (hc : ∀ j, StrictConvexOn ℝ (Set.Ici 0) (c j)) {x x' : ι → ℝ} {q q' : κ → ℝ}
    (h : IsOptimalLevels φ c x q) (h' : IsOptimalLevels φ c x' q') : x = x' ∧ q = q' := by
  obtain ⟨hxx, -⟩ := exercise_10_D_1 hφ (fun j => (hc j).convexOn) h h'
  subst hxx
  refine ⟨rfl, ?_⟩
  have hS := h.surplus_eq h'
  by_contra hne
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hne
  set qm : κ → ℝ := fun j => (1 / 2 : ℝ) • q j + (1 / 2 : ℝ) • q' j with hqm
  have hqm0 : ∀ j, 0 ≤ qm j := fun j => by
    simp only [hqm, smul_eq_mul]; linarith [h.2.1 j, h'.2.1 j]
  have hsm : ∑ i, x i = ∑ j, qm j := by
    simp only [hqm, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum, ← h.2.2.1,
      ← h'.2.2.1]
    ring
  have hle := h.2.2.2 x qm h.1 hqm0 hsm
  have hcost : ∑ k, c k (qm k) < ∑ k, ((1 / 2 : ℝ) * c k (q k) + (1 / 2 : ℝ) * c k (q' k)) :=
    Finset.sum_lt_sum (fun k _ => by
      simpa [smul_eq_mul, hqm] using (hc k).convexOn.2 (Set.mem_Ici.2 (h.2.1 k))
        (Set.mem_Ici.2 (h'.2.1 k)) (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
      ⟨j, Finset.mem_univ j, by
        simpa [smul_eq_mul, hqm] using (hc j).2 (Set.mem_Ici.2 (h.2.1 j))
          (Set.mem_Ici.2 (h'.2.1 j)) hj (by norm_num : (0 : ℝ) < 1 / 2)
          (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)⟩
  simp only [qlSurplus, Finset.sum_add_distrib, ← Finset.mul_sum] at hle hS hcost
  linarith

/-- **Footnote 15** (MWG, p. 325). Under the assumptions of Section 10.C, two Pareto optimal
allocations have the same consumption levels of good `ℓ` (and aggregate output): they differ
only in the distribution of the numeraire (and, without strict convexity, in the split of
production among firms). -/
theorem footnote_10_D_15 [Nonempty ι] (C : ι → QLConsumer) (F : κ → QLFirm) (ωm : ι → ℝ)
    (θ : ι → κ → ℝ) {a a' : Allocation ι κ 2}
    (h : (qlEconomyOf C F ωm θ).toEconomy.IsParetoOptimal a)
    (h' : (qlEconomyOf C F ωm θ).toEconomy.IsParetoOptimal a') :
    (∀ i, a.x i 1 = a'.x i 1) ∧ ∑ j, a.y j 1 = ∑ j, a'.y j 1 := by
  rw [qlEconomyOf, ql_pareto_iff _ _ (fun j => (F j).c_strictMono)] at h h'
  obtain ⟨hx, hq⟩ := exercise_10_D_1 (fun i => (C i).strictConcave) (fun j => (F j).convex)
    h.2.1 h'.2.1
  exact ⟨fun i => congrFun hx i, hq⟩

/-! ## Problem (10.D.6), Exercises 10.D.3 and 10.D.4 -/

/-- **Problem (10.D.6)** (MWG, p. 328). `a` maximizes the utility of consumer `i₁` among feasible
allocations giving every other consumer `i` at least `ūᵢ`. -/
def Economy.Solves10D6 {L : ℕ} (E : Economy ι κ L) (i₁ : ι) (ū : ι → ℝ)
    (a : Allocation ι κ L) : Prop :=
  E.IsFeasible a ∧ (∀ i, i ≠ i₁ → ū i ≤ E.u i (a.x i)) ∧
    ∀ a', E.IsFeasible a' → (∀ i, i ≠ i₁ → ū i ≤ E.u i (a'.x i)) →
      E.u i₁ (a'.x i₁) ≤ E.u i₁ (a.x i₁)

/-- **Exercise 10.D.3**, second part (MWG, p. 346). In any economy, a Pareto optimal allocation
solves problem (10.D.6) for the utility levels `ūᵢ = uᵢ(xᵢ)`. -/
theorem exercise_10_D_3_of_pareto {L : ℕ} (E : Economy ι κ L) (i₁ : ι) {a : Allocation ι κ L}
    (h : E.IsParetoOptimal a) : E.Solves10D6 i₁ (fun i => E.u i (a.x i)) a := by
  refine ⟨h.1, fun _ _ => le_rfl, fun a' ha' hcon => not_lt.1 fun hlt => h.2 ?_⟩
  refine ⟨a', ha', fun i => ?_, i₁, hlt⟩
  by_cases hi : i = i₁
  · subst hi; exact hlt.le
  · exact hcon i hi

/-- **Exercise 10.D.3**, first part (MWG, p. 346). In the quasilinear economy, any solution of
problem (10.D.6) is Pareto optimal (a surplus of another consumer could be transferred to
consumer `i₁` through the numeraire). -/
theorem exercise_10_D_3_pareto (φ : ι → ℝ → ℝ) (c : κ → ℝ → ℝ) (ωm : ι → ℝ) (θ : ι → κ → ℝ)
    (i₁ : ι) (ū : ι → ℝ) {a : Allocation ι κ 2}
    (h : (qlEconomy φ c ωm θ).toEconomy.Solves10D6 i₁ ū a) :
    (qlEconomy φ c ωm θ).toEconomy.IsParetoOptimal a := by
  classical
  obtain ⟨ha, hcon, hmax⟩ := h
  refine ⟨ha, fun ⟨a', ha', hle, k, hk⟩ => ?_⟩
  have hk1 : k ≠ i₁ := by
    rintro rfl
    have := hmax a' ha' fun i hi => (hcon i hi).trans (hle i)
    linarith
  set ε := (qlEconomy φ c ωm θ).toEconomy.u k (a'.x k) -
    (qlEconomy φ c ωm θ).toEconomy.u k (a.x k) with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  set coef : ι → ℝ := fun i => (if i = i₁ then ε else 0) - (if i = k then ε else 0) with hcoef
  set a'' : Allocation ι κ 2 := ⟨fun i => a'.x i + coef i • ![1, 0], a'.y⟩ with ha''
  have hx0 : ∀ i, a''.x i 0 = a'.x i 0 + coef i := fun i => by
    simp only [ha'', Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, mul_one]
  have hx1 : ∀ i, a''.x i 1 = a'.x i 1 := fun i => by
    simp only [ha'', Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, mul_zero, add_zero]
  have hu : ∀ i, (qlEconomy φ c ωm θ).toEconomy.u i (a''.x i) =
      (qlEconomy φ c ωm θ).toEconomy.u i (a'.x i) + coef i := by
    intro i
    rw [ql_utility, ql_utility, hx0, hx1]
    ring
  have hfeas : (qlEconomy φ c ωm θ).toEconomy.IsFeasible a'' := by
    rw [ql_feasible_iff] at ha' ⊢
    refine ⟨fun i => by rw [hx1]; exact ha'.1 i, ha'.2.1, ?_, ?_⟩
    · have hsc : ∑ i, coef i = 0 := by
        simp [hcoef, Finset.sum_sub_distrib, Finset.sum_ite_eq']
      have : ∑ i, a''.x i 0 = ∑ i, a'.x i 0 + ∑ i, coef i := by
        simp only [hx0, Finset.sum_add_distrib]
      rw [this, hsc, add_zero]
      exact ha'.2.2.1
    · simp only [hx1]; exact ha'.2.2.2
  have h1 := hmax a'' hfeas fun i hi => by
    rw [hu]
    by_cases hik : i = k
    · subst hik
      simp only [hcoef, hi, ↓reduceIte, zero_sub]
      have := hcon i hi
      rw [hε]
      linarith
    · simp only [hcoef, hi, hik, ↓reduceIte, sub_zero]
      linarith [hcon i hi, hle i]
  rw [hu] at h1
  simp only [hcoef, ↓reduceIte, Ne.symm hk1, sub_zero] at h1
  linarith [hle i₁]

/-- **Exercise 10.D.4** (MWG, p. 346). At any solution of problem (10.D.6) in the quasilinear
economy the levels of good `ℓ` satisfy (10.D.3)-(10.D.5) for some `μ` (the multipliers of the
utility constraints and of the numeraire constraint all equal `1`, and `μ` is the multiplier of
the constraint for good `ℓ`). -/
theorem exercise_10_D_4 [Nonempty ι] (C : ι → QLConsumer) (F : κ → QLFirm) (ωm : ι → ℝ)
    (θ : ι → κ → ℝ) (i₁ : ι) (ū : ι → ℝ) {a : Allocation ι κ 2}
    (h : (qlEconomyOf C F ωm θ).toEconomy.Solves10D6 i₁ ū a) :
    ∃ μ, IsQLEqm C F (fun i => a.x i 1) (fun j => a.y j 1) μ := by
  have hPO := exercise_10_D_3_pareto _ _ ωm θ i₁ ū h
  rw [ql_pareto_iff _ _ (fun j => (F j).c_strictMono)] at hPO
  exact optimalLevels_foc hPO.2.1

/-- **Exercise 10.D.4**, converse (MWG, p. 346). A feasible allocation without waste whose levels
of good `ℓ` satisfy (10.D.3)-(10.D.5) solves problem (10.D.6) for its own utility levels. -/
theorem exercise_10_D_4_converse [Nonempty ι] (C : ι → QLConsumer) (F : κ → QLFirm)
    (ωm : ι → ℝ) (θ : ι → κ → ℝ) (i₁ : ι) {a : Allocation ι κ 2} {μ : ℝ}
    (ha : (qlEconomyOf C F ωm θ).toEconomy.IsFeasible a)
    (hfoc : IsQLEqm C F (fun i => a.x i 1) (fun j => a.y j 1) μ)
    (hwaste : ∑ i, (qlEconomyOf C F ωm θ).toEconomy.u i (a.x i) =
      ∑ i, ωm i + qlSurplus (fun i => (C i).φ) (fun j => (F j).c) (fun i => a.x i 1)
        (fun j => a.y j 1)) :
    (qlEconomyOf C F ωm θ).toEconomy.Solves10D6 i₁
      (fun i => (qlEconomyOf C F ωm θ).toEconomy.u i (a.x i)) a := by
  refine exercise_10_D_3_of_pareto _ i₁ ?_
  rw [qlEconomyOf, ql_pareto_iff _ _ (fun j => (F j).c_strictMono)]
  exact ⟨ha, hfoc.isOptimalLevels, hwaste⟩

end MWG.CompetitiveMarkets

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Existence and uniqueness of equilibrium with merely convex costs (MWG, pp. 320-321, 327)

MWG proves existence of the partial equilibrium on p. 320 for strictly convex costs with
`c' → ∞`, and says that with merely convex costs "the basic features of the analysis do not
change". Here supply is a correspondence, so we argue directly through aggregate surplus:

* `optimalLevels_exist`: problem (10.D.2) has a solution for any consumers and firms of
  Section 10.C (bounded `φᵢ`, `cⱼ' > 0`, `cⱼ'' ≥ 0`), by compactness, since surplus falls below
  its value at zero once aggregate output exceeds `∑ sup φᵢ / minⱼ cⱼ'(0)`.
* `ql_eqm_exists_convex`: by (10.D.3)-(10.D.5) its first-order conditions give a competitive
  equilibrium (10.C.1)-(10.C.3), hence one in the sense of Definition 10.B.3 for every
  distribution of endowments and shares.
* `ql_eqm_unique_convex`: with `maxᵢ φᵢ'(0) > minⱼ cⱼ'(0)` the equilibrium price and individual
  consumptions are unique, and so is aggregate output (individual outputs need not be:
  Figure 10.C.4).
* `proposition_10_D_2_convex`: the second welfare theorem without presupposing an equilibrium.
-/

namespace MWG.CompetitiveMarkets

open Filter Topology

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **Existence of optimal levels** (problem (10.D.2), MWG p. 326) for the consumers and firms of
Section 10.C, with at least one firm. -/
theorem optimalLevels_exist [Nonempty κ] (C : ι → QLConsumer) (F : κ → QLFirm) :
    ∃ x q, IsOptimalLevels (fun i => (C i).φ) (fun j => (F j).c) x q := by
  classical
  choose B hB using fun i => (C i).bddAbove
  have hBφ : ∀ i y, 0 ≤ y → (C i).φ y ≤ B i := fun i y hy => hB i ⟨y, hy, rfl⟩
  have hB0 : ∀ i, 0 ≤ B i := fun i => by have := hBφ i 0 le_rfl; rwa [(C i).φ_zero] at this
  obtain ⟨j₀, -, hj₀⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (fun j => (F j).dc 0)
  set m := Finset.univ.inf' Finset.univ_nonempty (fun j => (F j).dc 0) with hmdef
  have hm : 0 < m := by rw [hj₀]; exact (F j₀).dc_pos 0 le_rfl
  have hmle : ∀ j, m ≤ (F j).dc 0 := fun j => Finset.inf'_le _ (Finset.mem_univ j)
  have hcost : ∀ j q, 0 ≤ q → (F j).c 0 + m * q ≤ (F j).c q := fun j q hq => by
    have := (F j).le_tangent le_rfl hq
    nlinarith [hmle j]
  set Mb := ∑ i, B i
  have hMb : 0 ≤ Mb := Finset.sum_nonneg fun i _ => hB0 i
  set Bd := Mb / m
  have hBd : 0 ≤ Bd := div_nonneg hMb hm.le
  set S : (ι → ℝ) × (κ → ℝ) → ℝ := fun z => ∑ i, (C i).φ (z.1 i) - ∑ j, (F j).c (z.2 j) with hS
  set D : Set ((ι → ℝ) × (κ → ℝ)) :=
    {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ ∑ i, z.1 i = ∑ j, z.2 j ∧ ∑ j, z.2 j ≤ Bd} with hD
  have hcs1 : Continuous fun z : (ι → ℝ) × (κ → ℝ) => ∑ i, z.1 i :=
    continuous_finsetSum _ fun i _ => (continuous_apply i).comp continuous_fst
  have hcs2 : Continuous fun z : (ι → ℝ) × (κ → ℝ) => ∑ j, z.2 j :=
    continuous_finsetSum _ fun j _ => (continuous_apply j).comp continuous_snd
  have hclosed : IsClosed D := by
    have e : D = {z : (ι → ℝ) × (κ → ℝ) | 0 ≤ z.1} ∩ ({z | 0 ≤ z.2} ∩
        ({z | ∑ i, z.1 i = ∑ j, z.2 j} ∩ {z | ∑ j, z.2 j ≤ Bd})) := rfl
    rw [e]
    exact (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_const continuous_snd).inter
        ((isClosed_eq hcs1 hcs2).inter (isClosed_le hcs2 continuous_const)))
  have hsub : D ⊆ Set.Icc 0 (fun _ => Bd) ×ˢ Set.Icc 0 (fun _ => Bd) := by
    rintro ⟨x, q⟩ ⟨hx, hq, hs, hb⟩
    refine ⟨⟨hx, fun i => ?_⟩, ⟨hq, fun j => ?_⟩⟩
    · have := Finset.single_le_sum (f := x) (fun k _ => hx k) (Finset.mem_univ i)
      simp only at hs hb
      linarith
    · have := Finset.single_le_sum (f := q) (fun k _ => hq k) (Finset.mem_univ j)
      simp only at hb
      linarith
  have hcomp : IsCompact D := (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset hclosed hsub
  have h0 : ((0 : ι → ℝ), (0 : κ → ℝ)) ∈ D := ⟨le_rfl, le_rfl, by simp, by simp [hBd]⟩
  have hcont : ContinuousOn S D := by
    refine ContinuousOn.sub (continuousOn_finsetSum _ fun i _ => ?_)
      (continuousOn_finsetSum _ fun j _ => ?_)
    · exact (C i).φ_continuousOn.comp ((continuous_apply i).comp continuous_fst).continuousOn
        fun z hz => Set.mem_Ici.2 (hz.1 i)
    · exact (F j).c_continuousOn.comp ((continuous_apply j).comp continuous_snd).continuousOn
        fun z hz => Set.mem_Ici.2 (hz.2.1 j)
  obtain ⟨z, hz, hmax⟩ := hcomp.exists_isMaxOn ⟨_, h0⟩ hcont
  refine ⟨z.1, z.2, fun i => hz.1 i, fun j => hz.2.1 j, hz.2.2.1, fun x' q' hx' hq' hs => ?_⟩
  have hzS : S z = qlSurplus (fun i => (C i).φ) (fun j => (F j).c) z.1 z.2 := rfl
  rw [← hzS]
  by_cases hb : ∑ j, q' j ≤ Bd
  · exact hmax (a := (x', q')) ⟨hx', hq', hs, hb⟩
  · push Not at hb
    have h1 : ∑ i, (C i).φ (x' i) ≤ Mb := Finset.sum_le_sum fun i _ => hBφ i _ (hx' i)
    have h2 : ∑ j, ((F j).c 0 + m * q' j) ≤ ∑ j, (F j).c (q' j) :=
      Finset.sum_le_sum fun j _ => hcost j _ (hq' j)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h2
    have h3 : Mb < m * ∑ j, q' j := by
      have := mul_lt_mul_of_pos_left hb hm
      rwa [mul_div_cancel₀ _ hm.ne'] at this
    have h4 : S (0, 0) ≤ S z := hmax (a := (0, 0)) h0
    have hS0 : S (0, 0) = -∑ j, (F j).c 0 := by
      simp [hS, QLConsumer.φ_zero]
    rw [hS0] at h4
    simp only [qlSurplus]
    linarith

/-- **Existence of competitive equilibrium with convex costs** (MWG, pp. 320-321): for any
consumers and (at least one) firm of Section 10.C there is a solution of (10.C.1)-(10.C.3). -/
theorem ql_eqm_exists_convex [Nonempty κ] (C : ι → QLConsumer) (F : κ → QLFirm) :
    ∃ x q p, IsQLEqm C F x q p := by
  obtain ⟨x, q, h⟩ := optimalLevels_exist C F
  obtain ⟨p, hp⟩ := optimalLevels_foc h
  exact ⟨x, q, p, hp⟩

/-- Existence in the sense of Definition 10.B.3, for every distribution of endowments and shares
summing to one. -/
theorem ql_competitiveEqm_exists_convex [Nonempty κ] (C : ι → QLConsumer) (F : κ → QLFirm)
    (ωm : ι → ℝ) (θ : ι → κ → ℝ) (hθ : ∀ j, ∑ i, θ i j = 1) :
    ∃ (a : Allocation ι κ 2) (p : ℝ), (qlEconomyOf C F ωm θ).IsCompetitiveEqm a (qlPrice p) := by
  obtain ⟨x, q, p, h⟩ := ql_eqm_exists_convex C F
  exact ⟨_, p, ql_isCompetitiveEqm_of_isQLEqm h ωm θ hθ⟩

/-- **Uniqueness with convex costs** (MWG, p. 320, Figure 10.C.4, footnote 15). If
`maxᵢ φᵢ'(0) > minⱼ cⱼ'(0)`, any two solutions of (10.C.1)-(10.C.3) have the same price, the same
individual consumptions and the same aggregate output. -/
theorem ql_eqm_unique_convex {C : ι → QLConsumer} {F : κ → QLFirm}
    (hgap : ∃ i j, (F j).dc 0 < (C i).dφ 0) {x x' : ι → ℝ} {q q' : κ → ℝ} {p p' : ℝ}
    (h : IsQLEqm C F x q p) (h' : IsQLEqm C F x' q' p') :
    x = x' ∧ ∑ j, q j = ∑ j, q' j ∧ p = p' := by
  obtain ⟨hxx, hqq⟩ := exercise_10_D_1 (fun i => (C i).strictConcave) (fun j => (F j).convex)
    h.isOptimalLevels h'.isOptimalLevels
  refine ⟨hxx, hqq, ?_⟩
  obtain ⟨i, hi⟩ := exists_pos_of_sum_pos (h.aggregate_pos hgap)
  have e1 := (h.2.1 i).2.2 hi
  have e2 := (h'.2.1 i).2.2 (hxx ▸ hi)
  rw [← hxx] at e2
  rw [← e1, e2]

/-- **Proposition 10.D.2** (MWG, p. 327) for the economy of Section 10.C with merely convex costs:
for the utility levels of any Pareto optimal allocation there are transfers `∑ Tᵢ = 0` and a
competitive equilibrium from endowments `ω_{mi} + Tᵢ` attaining them. No equilibrium is
presupposed. -/
theorem proposition_10_D_2_convex [Nonempty ι] [Nonempty κ] (C : ι → QLConsumer)
    (F : κ → QLFirm) (ωm : ι → ℝ) (θ : ι → κ → ℝ) (hθ : ∀ j, ∑ i, θ i j = 1)
    (a : Allocation ι κ 2) (hPO : (qlEconomyOf C F ωm θ).toEconomy.IsParetoOptimal a) :
    ∃ T : ι → ℝ, ∑ i, T i = 0 ∧ ∃ (a' : Allocation ι κ 2) (p : ℝ),
      (qlEconomyOf C F (ωm + T) θ).IsCompetitiveEqm a' (qlPrice p) ∧
      ∀ i, (qlEconomyOf C F (ωm + T) θ).toEconomy.u i (a'.x i) =
        (qlEconomyOf C F ωm θ).toEconomy.u i (a.x i) :=
  proposition_10_D_2_of_exists C F ωm θ hθ a hPO (ql_eqm_exists_convex C F)

/-- **Instance** (constant returns, merely convex): one consumer `φ(x) = 2(1 - e^{-x})` and one
firm `c(q) = q`. An equilibrium exists, with price `1` (unique), it is Pareto optimal, and the
second welfare theorem applies to it. -/
theorem inst_convex_existence :
    ∃ (x : Fin 1 → ℝ) (q : Fin 1 → ℝ),
      IsQLEqm (fun _ => expConsumer 2 two_pos) (fun _ => linearFirm 1 one_pos) x q 1 ∧
      ∀ (x' : Fin 1 → ℝ) (q' : Fin 1 → ℝ) (p' : ℝ),
        IsQLEqm (fun _ => expConsumer 2 two_pos) (fun _ => linearFirm 1 one_pos) x' q' p' →
          p' = 1 ∧ x' = x := by
  have hgap : ∃ i j, ((fun _ : Fin 1 => linearFirm 1 one_pos) j).dc 0 <
      ((fun _ : Fin 1 => expConsumer 2 two_pos) i).dφ 0 :=
    ⟨0, 0, by simp [linearFirm, expConsumer]⟩
  obtain ⟨x, q, p, h⟩ := ql_eqm_exists_convex (fun _ : Fin 1 => expConsumer 2 two_pos)
    (fun _ : Fin 1 => linearFirm 1 one_pos)
  have hp : p = 1 := (figure_10_C_4_price one_pos ⟨0, by simp [expConsumer]⟩ h).1
  subst hp
  refine ⟨x, q, h, fun x' q' p' h' => ?_⟩
  obtain ⟨hxx, -, hpp⟩ := ql_eqm_unique_convex hgap h h'
  exact ⟨hpp.symm, hxx.symm⟩

/-- **Instance of `proposition_10_D_2_convex`** for the constant-returns economy above. -/
theorem inst_proposition_10_D_2_convex :
    ∃ a : Allocation (Fin 1) (Fin 1) 2,
      (qlEconomyOf (fun _ => expConsumer 2 two_pos) (fun _ => linearFirm 1 one_pos) (fun _ => 1)
        (fun _ _ => 1)).toEconomy.IsParetoOptimal a ∧
      ∃ T : Fin 1 → ℝ, ∑ i, T i = 0 ∧ ∃ (a' : Allocation (Fin 1) (Fin 1) 2) (p : ℝ),
        (qlEconomyOf (fun _ => expConsumer 2 two_pos) (fun _ => linearFirm 1 one_pos)
          ((fun _ => 1) + T) (fun _ _ => 1)).IsCompetitiveEqm a' (qlPrice p) := by
  have hθ : ∀ j : Fin 1, ∑ i : Fin 1, (fun _ _ => (1 : ℝ)) i j = 1 := fun _ => by simp
  obtain ⟨a, p, h⟩ := ql_competitiveEqm_exists_convex (fun _ : Fin 1 => expConsumer 2 two_pos)
    (fun _ : Fin 1 => linearFirm 1 one_pos) (fun _ => 1) (fun _ _ => 1) hθ
  have hPO := proposition_10_D_1 _ _ _ _ hθ a p h
  obtain ⟨T, hT, a', p', h', -⟩ := proposition_10_D_2_convex _ _ _ _ hθ a hPO
  exact ⟨a, hPO, T, hT, a', p', h'⟩

end MWG.CompetitiveMarkets

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Inverse demand, industry marginal cost and the central authority (MWG Section 10.C)

MWG, pp. 321-322 (Figures 10.C.5-10.C.6, footnotes 11-12) and Exercises 10.C.3-10.C.4
(pp. 344-345).

* **Exercise 10.C.4**: the central authority allocating `x` units of good `ℓ` to maximize
  `∑ uᵢ`. Its value `γ(x)` (`grossBenefit`, defined as a supremum) is attained exactly at the
  allocations satisfying the first-order conditions (a); `γ` is differentiable at `x > 0` with
  `γ'(x) = P(x) = φᵢ'(xᵢ*)` for every active consumer (b); consumers facing `P(x)` demand `x` in
  aggregate, so `P` is the inverse of aggregate demand (c).
* **Exercise 10.C.3**: the central authority minimizing the cost `C(q)` of producing `q`
  (`minCost`, an infimum), for convex costs with `c' > 0`. (a) First-order conditions,
  necessary and sufficient; (b) `C'(q) = cⱼ'(qⱼ*)` for active firms; (c) firms maximizing profit
  at `p = C'(q)` produce `q` in aggregate (with strictly convex costs, uniquely), so `C'` is the
  inverse of the industry supply function (footnotes 11-12, Figure 10.C.5).
* `invDemand` (`P = x⁻¹`, Figure 10.C.6) and `invSupply` (`C' = q⁻¹`) with their monotonicity.
-/

namespace MWG.CompetitiveMarkets

open Filter Topology

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-! ## The consumption side -/

/-- `maxᵢ φᵢ'(0)`, the largest marginal benefit at zero consumption. -/
noncomputable def maxMB [Nonempty ι] (C : ι → QLConsumer) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i => (C i).dφ 0

theorem le_maxMB [Nonempty ι] (C : ι → QLConsumer) (i : ι) : (C i).dφ 0 ≤ maxMB C :=
  Finset.le_sup' (fun i => (C i).dφ 0) (Finset.mem_univ i)

theorem exists_eq_maxMB [Nonempty ι] (C : ι → QLConsumer) : ∃ i, (C i).dφ 0 = maxMB C := by
  obtain ⟨i, -, h⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => (C i).dφ 0)
  exact ⟨i, h.symm⟩

theorem maxMB_pos [Nonempty ι] (C : ι → QLConsumer) : 0 < maxMB C := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact ((C i).dφ_pos 0 le_rfl).trans_le (le_maxMB C i)

/-- Positive aggregate demand means some consumer has `p < φᵢ'(0)`. -/
theorem exists_lt_of_aggDemand_pos (C : ι → QLConsumer) {p : ℝ} (hp : 0 < p)
    (h : 0 < aggDemand C p) : ∃ i, p < (C i).dφ 0 := by
  by_contra hno
  push Not at hno
  rw [(aggDemand_eq_zero_iff C hp).2 hno] at h
  exact lt_irrefl 0 h

/-- **Supergradient of the gross benefit.** If `x` satisfies the consumers' first-order
conditions at `μ`, then `∑ φᵢ(yᵢ) ≤ ∑ φᵢ(xᵢ) + μ (∑ yᵢ - ∑ xᵢ)` for all `y ≥ 0`. -/
theorem foc_benefit_le {C : ι → QLConsumer} {x : ι → ℝ} {μ : ℝ}
    (hx : ∀ i, IsFOCSol (C i).dφ μ (x i)) {y : ι → ℝ} (hy : ∀ i, 0 ≤ y i) :
    ∑ i, (C i).φ (y i) ≤ ∑ i, (C i).φ (x i) + μ * (∑ i, y i - ∑ i, x i) := by
  have h : ∀ i, (C i).φ (y i) ≤ (C i).φ (x i) + μ * (y i - x i) := by
    intro i
    have ht := (C i).tangent_le (hx i).1 (hy i)
    rcases eq_or_lt_of_le (hx i).1 with h0 | hpos
    · rw [← h0] at ht ⊢
      have := (hx i).2.1
      rw [← h0] at this
      nlinarith [hy i]
    · rw [(hx i).2.2 hpos] at ht
      exact ht
  calc ∑ i, (C i).φ (y i) ≤ ∑ i, ((C i).φ (x i) + μ * (y i - x i)) :=
        Finset.sum_le_sum fun i _ => h i
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]

/-- The values `∑ φᵢ(yᵢ)` of the allocations `y ≥ 0` of `X` units of good `ℓ`. -/
def benefitSet (C : ι → QLConsumer) (X : ℝ) : Set ℝ :=
  {s | ∃ y : ι → ℝ, (∀ i, 0 ≤ y i) ∧ ∑ i, y i = X ∧ s = ∑ i, (C i).φ (y i)}

/-- **Exercise 10.C.4** (MWG, p. 345). The value function `γ(x)` of the central authority's
problem `max ∑ uᵢ` over allocations of `x` units of good `ℓ` (the numeraire being fixed). -/
noncomputable def grossBenefit (C : ι → QLConsumer) (X : ℝ) : ℝ := sSup (benefitSet C X)

/-- An allocation satisfying the first-order conditions attains `γ`. -/
theorem grossBenefit_isGreatest {C : ι → QLConsumer} {x : ι → ℝ} {μ : ℝ}
    (hx : ∀ i, IsFOCSol (C i).dφ μ (x i)) :
    IsGreatest (benefitSet C (∑ i, x i)) (∑ i, (C i).φ (x i)) := by
  refine ⟨⟨x, fun i => (hx i).1, rfl, rfl⟩, ?_⟩
  rintro s ⟨y, hy, hs, rfl⟩
  have := foc_benefit_le hx hy
  rw [hs, sub_self, mul_zero, add_zero] at this
  exact this

theorem grossBenefit_eq_of_foc {C : ι → QLConsumer} {x : ι → ℝ} {μ : ℝ}
    (hx : ∀ i, IsFOCSol (C i).dφ μ (x i)) :
    grossBenefit C (∑ i, x i) = ∑ i, (C i).φ (x i) :=
  (grossBenefit_isGreatest hx).csSup_eq

/-- The price at which aggregate demand equals a given `X ≥ 0` exists (intermediate value
theorem). -/
theorem exists_invDemand [Nonempty ι] (C : ι → QLConsumer) (X : ℝ) :
    ∃ μ, 0 ≤ X → 0 < μ ∧ aggDemand C μ = X ∧ (X = 0 → μ = maxMB C) := by
  by_cases hX : 0 ≤ X
  · rcases eq_or_lt_of_le hX with h0 | hpos
    · refine ⟨maxMB C, fun _ => ⟨maxMB_pos C, ?_, fun _ => rfl⟩⟩
      rw [← h0]
      exact (aggDemand_eq_zero_iff C (maxMB_pos C)).2 fun i => le_maxMB C i
    · obtain ⟨i₀⟩ := ‹Nonempty ι›
      set lo := (C i₀).dφ X with hlo
      have hlo0 : 0 < lo := (C i₀).dφ_pos X hX
      have hdlo : (C i₀).demand lo = X := (C i₀).demand_eq ⟨hX, le_rfl, fun _ => rfl⟩
      have hge : X ≤ aggDemand C lo := by
        rw [← hdlo]
        exact Finset.single_le_sum (f := fun i => (C i).demand lo)
          (fun i _ => (C i).demand_nonneg hlo0) (Finset.mem_univ i₀)
      have hlohi : lo ≤ maxMB C :=
        ((C i₀).dφ_antitone (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hX) hX).trans (le_maxMB C i₀)
      have hhi : aggDemand C (maxMB C) = 0 :=
        (aggDemand_eq_zero_iff C (maxMB_pos C)).2 fun i => le_maxMB C i
      obtain ⟨μ, hμ, hμX⟩ := intermediate_value_Icc' hlohi
        ((aggDemand_continuousOn C).mono fun p hp => hlo0.trans_le hp.1)
        ⟨by rw [hhi]; exact hX, hge⟩
      exact ⟨μ, fun _ => ⟨hlo0.trans_le hμ.1, hμX, fun h => absurd h hpos.ne'⟩⟩
  · exact ⟨0, fun h => absurd h hX⟩

/-- **Inverse demand function** `P(x) = x⁻¹(x)` (MWG, p. 321, Figure 10.C.6), with
`P(0) = maxᵢ φᵢ'(0)`. -/
noncomputable def invDemand [Nonempty ι] (C : ι → QLConsumer) (X : ℝ) : ℝ :=
  Classical.choose (exists_invDemand C X)

theorem invDemand_spec [Nonempty ι] (C : ι → QLConsumer) {X : ℝ} (hX : 0 ≤ X) :
    0 < invDemand C X ∧ aggDemand C (invDemand C X) = X ∧ (X = 0 → invDemand C X = maxMB C) :=
  Classical.choose_spec (exists_invDemand C X) hX

theorem invDemand_pos [Nonempty ι] (C : ι → QLConsumer) {X : ℝ} (hX : 0 ≤ X) :
    0 < invDemand C X := (invDemand_spec C hX).1

/-- **(MWG, p. 345, Exercise 10.C.4(c))** Aggregate demand at `P(x)` is `x`. -/
theorem aggDemand_invDemand [Nonempty ι] (C : ι → QLConsumer) {X : ℝ} (hX : 0 ≤ X) :
    aggDemand C (invDemand C X) = X := (invDemand_spec C hX).2.1

/-- For `x > 0`, `P(x)` is the unique price with aggregate demand `x`. -/
theorem invDemand_unique [Nonempty ι] (C : ι → QLConsumer) {X μ : ℝ} (hX : 0 < X)
    (hμ : 0 < μ) (h : aggDemand C μ = X) : invDemand C X = μ := by
  have hP := invDemand_spec C hX.le
  have key : ∀ p₁ p₂, 0 < p₁ → p₁ < p₂ → aggDemand C p₁ = X → aggDemand C p₂ = X → False := by
    intro p₁ p₂ hp₁ h₁₂ e₁ e₂
    have := aggDemand_strictAnti C hp₁ h₁₂ (exists_lt_of_aggDemand_pos C hp₁ (e₁ ▸ hX))
    linarith
  rcases lt_trichotomy (invDemand C X) μ with hlt | heq | hgt
  · exact (key _ _ hP.1 hlt hP.2.1 h).elim
  · exact heq
  · exact (key _ _ hμ hgt h hP.2.1).elim

/-- **Figure 10.C.6** (MWG, p. 322). `P` inverts aggregate demand: `P(x(p)) = p` for
`0 < p < maxᵢ φᵢ'(0)`. -/
theorem invDemand_aggDemand [Nonempty ι] (C : ι → QLConsumer) {p : ℝ} (hp : 0 < p)
    (hpm : p < maxMB C) : invDemand C (aggDemand C p) = p := by
  obtain ⟨i, hi⟩ := exists_eq_maxMB C
  have hpos : 0 < aggDemand C p :=
    Finset.sum_pos' (fun k _ => (C k).demand_nonneg hp)
      ⟨i, Finset.mem_univ i, ((C i).demand_pos_iff hp).2 (hi ▸ hpm)⟩
  exact invDemand_unique C hpos hp rfl

theorem invDemand_le_maxMB [Nonempty ι] (C : ι → QLConsumer) {X : ℝ} (hX : 0 ≤ X) :
    invDemand C X ≤ maxMB C := by
  rcases eq_or_lt_of_le hX with h0 | hpos
  · exact le_of_eq ((invDemand_spec C hX).2.2 h0.symm)
  · obtain ⟨i, hi⟩ := exists_lt_of_aggDemand_pos C (invDemand_pos C hX)
      ((aggDemand_invDemand C hX).symm ▸ hpos)
    exact hi.le.trans (le_maxMB C i)

/-- **(MWG, p. 322)** The inverse demand function is strictly decreasing on `x ≥ 0`. -/
theorem invDemand_strictAntiOn [Nonempty ι] (C : ι → QLConsumer) :
    StrictAntiOn (invDemand C) (Set.Ici 0) := by
  intro X₁ h₁ X₂ h₂ h₁₂
  have h₁' : (0 : ℝ) ≤ X₁ := h₁
  have h₂' : (0 : ℝ) ≤ X₂ := h₂
  refine lt_of_le_of_ne ?_ fun heq => ?_
  · by_contra hlt
    push Not at hlt
    have := aggDemand_antitoneOn C (invDemand_pos C h₁') (invDemand_pos C h₂') hlt.le
    rw [aggDemand_invDemand C h₁', aggDemand_invDemand C h₂'] at this
    linarith
  · have e₁ := aggDemand_invDemand C h₁'
    have e₂ := aggDemand_invDemand C h₂'
    rw [heq] at e₂
    linarith

theorem invDemand_antitoneOn [Nonempty ι] (C : ι → QLConsumer) :
    AntitoneOn (invDemand C) (Set.Ici 0) :=
  (invDemand_strictAntiOn C).antitoneOn

/-- The optimal allocation of `X` units: each consumer's demand at `P(X)`. -/
noncomputable def optAlloc [Nonempty ι] (C : ι → QLConsumer) (X : ℝ) (i : ι) : ℝ :=
  (C i).demand (invDemand C X)

theorem optAlloc_foc [Nonempty ι] (C : ι → QLConsumer) {X : ℝ} (hX : 0 ≤ X) (i : ι) :
    IsFOCSol (C i).dφ (invDemand C X) (optAlloc C X i) :=
  (C i).demand_spec (invDemand_pos C hX)

theorem optAlloc_sum [Nonempty ι] (C : ι → QLConsumer) {X : ℝ} (hX : 0 ≤ X) :
    ∑ i, optAlloc C X i = X := aggDemand_invDemand C hX

/-- `γ(X) = ∑ φᵢ(xᵢ*(X))`. -/
theorem grossBenefit_eq [Nonempty ι] (C : ι → QLConsumer) {X : ℝ} (hX : 0 ≤ X) :
    grossBenefit C X = ∑ i, (C i).φ (optAlloc C X i) := by
  have := grossBenefit_eq_of_foc (optAlloc_foc C hX)
  rwa [optAlloc_sum C hX] at this

theorem grossBenefit_zero [Nonempty ι] (C : ι → QLConsumer) : grossBenefit C 0 = 0 := by
  have h := grossBenefit_eq_of_foc (C := C) (x := fun _ => 0) (μ := maxMB C)
    (fun i => ⟨le_rfl, le_maxMB C i, fun h => absurd h (lt_irrefl 0)⟩)
  simp only [Finset.sum_const_zero] at h
  rw [h]
  simp [QLConsumer.φ_zero]

/-- **Exercise 10.C.4(a)** (MWG, p. 345). An allocation `y ≥ 0` of `x` units solves the central
authority's problem iff it satisfies the first-order conditions: for some `μ`,
`φᵢ'(yᵢ) ≤ μ` with equality if `yᵢ > 0`. -/
theorem exercise_10_C_4a [Nonempty ι] (C : ι → QLConsumer) {y : ι → ℝ} (hy : ∀ i, 0 ≤ y i) :
    IsGreatest (benefitSet C (∑ i, y i)) (∑ i, (C i).φ (y i)) ↔
      ∃ μ, ∀ i, IsFOCSol (C i).dφ μ (y i) := by
  refine ⟨fun hmax => ?_, fun ⟨μ, hμ⟩ => grossBenefit_isGreatest hμ⟩
  have hX : 0 ≤ ∑ i, y i := Finset.sum_nonneg fun i _ => hy i
  set x := optAlloc C (∑ i, y i) with hx
  have hfoc := optAlloc_foc C hX
  have hsum := optAlloc_sum C hX
  -- `y = x` by strict concavity
  have hxy : y = x := by
    by_contra hne
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
    have hval : ∑ k, (C k).φ (y k) = ∑ k, (C k).φ (x k) := by
      refine le_antisymm ?_ (hmax.2 ⟨x, fun k => (hfoc k).1, hsum, rfl⟩)
      have := foc_benefit_le hfoc hy
      rw [hsum, sub_self, mul_zero, add_zero] at this
      exact this
    set m : ι → ℝ := fun k => (1 / 2 : ℝ) • y k + (1 / 2 : ℝ) • x k with hm
    have hm0 : ∀ k, 0 ≤ m k := fun k => by
      simp only [hm, smul_eq_mul]; linarith [hy k, (hfoc k).1]
    have hsum' : ∑ k, x k = ∑ k, y k := hsum
    have hms : ∑ k, m k = ∑ k, y k := by
      simp only [hm, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [hsum']; ring
    have hle := hmax.2 ⟨m, hm0, hms, rfl⟩
    have hge : ∀ k, (1 / 2 : ℝ) * (C k).φ (y k) + (1 / 2 : ℝ) * (C k).φ (x k) ≤ (C k).φ (m k) :=
      fun k => by
        simpa [smul_eq_mul, hm] using (C k).strictConcave.concaveOn.2 (Set.mem_Ici.2 (hy k))
          (Set.mem_Ici.2 (hfoc k).1) (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    have hgt : (1 / 2 : ℝ) * (C i).φ (y i) + (1 / 2 : ℝ) * (C i).φ (x i) < (C i).φ (m i) := by
      simpa [smul_eq_mul, hm] using (C i).strictConcave.2 (Set.mem_Ici.2 (hy i))
        (Set.mem_Ici.2 (hfoc i).1) hi (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    have := Finset.sum_lt_sum (fun k _ => hge k) ⟨i, Finset.mem_univ i, hgt⟩
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at this
    linarith
  refine ⟨invDemand C (∑ i, y i), fun i => ?_⟩
  have : y i = x i := congrFun hxy i
  rw [this]
  exact hfoc i

/-- **Exercise 10.C.4(b)** (MWG, p. 345). For `x > 0` the value `γ` of the central authority's
problem is differentiable with `γ'(x) = P(x)`, and `P(x) = φᵢ'(xᵢ*)` for every consumer with
`xᵢ* > 0`. -/
theorem exercise_10_C_4b [Nonempty ι] (C : ι → QLConsumer) {X : ℝ} (hX : 0 < X) :
    HasDerivAt (grossBenefit C) (invDemand C X) X ∧
      ∀ i, 0 < optAlloc C X i → invDemand C X = (C i).dφ (optAlloc C X i) := by
  classical
  have hX0 := hX.le
  have hfoc := optAlloc_foc C hX0
  refine ⟨?_, fun i hi => ((hfoc i).2.2 hi).symm⟩
  obtain ⟨i₀, hi₀⟩ := exists_pos_of_sum_pos ((optAlloc_sum C hX0).symm ▸ hX)
  set a := optAlloc C X i₀ with ha
  set d := invDemand C X with hd
  have hda : (C i₀).dφ a = d := (hfoc i₀).2.2 hi₀
  set g : ℝ → ℝ := fun y => (C i₀).φ (a + (y - X)) with hg
  have hgd : HasDerivAt g d X := by
    have h1 : HasDerivAt (fun y : ℝ => a + (y - X)) 1 X :=
      ((hasDerivAt_id X).sub_const X).const_add a
    have h2 : HasDerivAt (C i₀).φ ((C i₀).dφ a) (a + (X - X)) := by
      rw [sub_self, add_zero]; exact foc_hasDerivAt (C i₀).hasDeriv hi₀
    have := h2.comp X h1
    rw [mul_one, hda] at this
    exact this
  have hgX : g X = (C i₀).φ a := by simp [hg]
  have hbdd : ∀ Y, 0 ≤ Y → BddAbove (benefitSet C Y) := fun Y hY =>
    ⟨_, fun s hs => (grossBenefit_isGreatest (optAlloc_foc C hY)).2
      (by rwa [optAlloc_sum C hY])⟩
  refine hasDerivAt_of_sandwich (e₂ := fun _ => 0) (remainder_isLittleO hgd)
    (Asymptotics.isLittleO_zero _ _) ?_
  have hnear : ∀ᶠ y in 𝓝 X, X - a < y := lt_mem_nhds (by linarith)
  filter_upwards [hnear] with y hy
  have ha' : a ≤ X := by
    rw [← optAlloc_sum C hX0]
    exact Finset.single_le_sum (f := optAlloc C X) (fun k _ => (hfoc k).1) (Finset.mem_univ i₀)
  have hy0 : 0 ≤ y := by linarith
  constructor
  · -- lower bound: move `y - X` to consumer `i₀`
    have hmem : ∑ k, (C k).φ (Function.update (optAlloc C X) i₀ (a + (y - X)) k) ∈
        benefitSet C y := by
      refine ⟨_, fun k => ?_, ?_, rfl⟩
      · by_cases hk : k = i₀
        · subst hk; simp only [Function.update_self]; linarith
        · simp only [Function.update_of_ne hk]; exact (hfoc k).1
      · rw [sum_update_id, optAlloc_sum C hX0]; ring
    have hle := le_csSup (hbdd y hy0) hmem
    rw [sum_update_apply (fun k => (C k).φ)] at hle
    rw [grossBenefit_eq C hX0]
    simp only [hgX] at *
    unfold grossBenefit
    simp only [hg] at *
    linarith
  · -- upper bound: the supergradient at `X`
    have := foc_benefit_le hfoc (fun k => (optAlloc_foc C hy0 k).1)
    rw [optAlloc_sum C hy0, optAlloc_sum C hX0] at this
    rw [grossBenefit_eq C hy0, grossBenefit_eq C hX0]
    linarith

/-- **Exercise 10.C.4(c)** (MWG, p. 345). If every consumer maximizes utility facing the price
`P(x)`, aggregate demand is exactly `x`: `P` is the inverse of the aggregate demand function. -/
theorem exercise_10_C_4c [Nonempty ι] (C : ι → QLConsumer) {X : ℝ} (hX : 0 ≤ X) :
    aggDemand C (invDemand C X) = X ∧
      ∀ p, 0 < p → p < maxMB C → invDemand C (aggDemand C p) = p :=
  ⟨aggDemand_invDemand C hX, fun _ hp hpm => invDemand_aggDemand C hp hpm⟩

/-! ## The production side: Exercise 10.C.3 -/

/-- The costs `∑ cⱼ(qⱼ)` of the plans `q ≥ 0` with `∑ qⱼ ≥ Q`. -/
def costSet (F : κ → QLFirm) (Q : ℝ) : Set ℝ :=
  {s | ∃ q : κ → ℝ, (∀ j, 0 ≤ q j) ∧ Q ≤ ∑ j, q j ∧ s = ∑ j, (F j).c (q j)}

/-- **Exercise 10.C.3** (MWG, p. 344; footnote 11, p. 321). The central authority's minimized
cost of producing at least `Q`: `C(Q) = min {∑ cⱼ(qⱼ) : q ≥ 0, ∑ qⱼ ≥ Q}`. -/
noncomputable def minCost (F : κ → QLFirm) (Q : ℝ) : ℝ := sInf (costSet F Q)

/-- The firms' first-order conditions at the common marginal cost `μ`. -/
def IsCostFOC (F : κ → QLFirm) (μ : ℝ) (q : κ → ℝ) : Prop :=
  ∀ j, 0 ≤ q j ∧ μ ≤ (F j).dc (q j) ∧ (0 < q j → μ = (F j).dc (q j))

/-- **Subgradient of the cost.** At plans satisfying the first-order conditions with `μ ≥ 0`,
`∑ cⱼ(q'ⱼ) ≥ ∑ cⱼ(qⱼ) + μ (∑ q'ⱼ - ∑ qⱼ)` for all `q' ≥ 0`. -/
theorem foc_cost_ge {F : κ → QLFirm} {μ : ℝ} {q : κ → ℝ} (hq : IsCostFOC F μ q)
    {q' : κ → ℝ} (hq' : ∀ j, 0 ≤ q' j) :
    ∑ j, (F j).c (q j) + μ * (∑ j, q' j - ∑ j, q j) ≤ ∑ j, (F j).c (q' j) := by
  have h : ∀ j, (F j).c (q j) + μ * (q' j - q j) ≤ (F j).c (q' j) := by
    intro j
    have ht := (F j).le_tangent (hq j).1 (hq' j)
    rcases eq_or_lt_of_le (hq j).1 with h0 | hpos
    · rw [← h0] at ht ⊢
      have := (hq j).2.1
      rw [← h0] at this
      nlinarith [hq' j]
    · rw [← (hq j).2.2 hpos] at ht
      exact ht
  calc ∑ j, (F j).c (q j) + μ * (∑ j, q' j - ∑ j, q j)
      = ∑ j, ((F j).c (q j) + μ * (q' j - q j)) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
    _ ≤ _ := Finset.sum_le_sum fun j _ => h j

/-- Costs are bounded below by `∑ cⱼ(0)`. -/
theorem costSet_lower (F : κ → QLFirm) {Q s : ℝ} (hs : s ∈ costSet F Q) :
    ∑ j, (F j).c 0 ≤ s := by
  obtain ⟨q, hq, -, rfl⟩ := hs
  exact Finset.sum_le_sum fun j _ => (F j).c_strictMono.monotoneOn (Set.mem_Ici.2 le_rfl)
    (Set.mem_Ici.2 (hq j)) (hq j)

/-- Plans satisfying the first-order conditions with `μ ≥ 0` minimize cost. -/
theorem minCost_isLeast {F : κ → QLFirm} {μ : ℝ} (hμ : 0 ≤ μ) {q : κ → ℝ}
    (hq : IsCostFOC F μ q) : IsLeast (costSet F (∑ j, q j)) (∑ j, (F j).c (q j)) := by
  refine ⟨⟨q, fun j => (hq j).1, le_rfl, rfl⟩, ?_⟩
  rintro s ⟨q', hq', hs, rfl⟩
  have := foc_cost_ge hq hq'
  nlinarith

theorem minCost_eq_of_foc {F : κ → QLFirm} {μ : ℝ} (hμ : 0 ≤ μ) {q : κ → ℝ}
    (hq : IsCostFOC F μ q) : minCost F (∑ j, q j) = ∑ j, (F j).c (q j) :=
  (minCost_isLeast hμ hq).csInf_eq

/-- **Exercise 10.C.3(a)** (MWG, p. 344): necessity. If `q ≥ 0` minimizes the cost of producing
at least `Q > 0`, then the constraint binds (`c' > 0`) and there is `μ > 0` with
`μ ≤ cⱼ'(qⱼ)`, equality if `qⱼ > 0`. -/
theorem exercise_10_C_3a (F : κ → QLFirm) {Q : ℝ} (hQ : 0 < Q) {q : κ → ℝ}
    (hq : ∀ j, 0 ≤ q j) (hsum : Q ≤ ∑ j, q j)
    (hmin : ∀ q' : κ → ℝ, (∀ j, 0 ≤ q' j) → Q ≤ ∑ j, q' j →
      ∑ j, (F j).c (q j) ≤ ∑ j, (F j).c (q' j)) :
    ∑ j, q j = Q ∧ ∃ μ, 0 < μ ∧ IsCostFOC F μ q := by
  classical
  -- the constraint binds
  have hbind : ∑ j, q j = Q := by
    by_contra hne
    have hlt : Q < ∑ j, q j := lt_of_le_of_ne hsum (Ne.symm hne)
    obtain ⟨j, hj⟩ := exists_pos_of_sum_pos (hQ.trans hlt)
    set t := min (q j) (∑ k, q k - Q) with ht
    have ht0 : 0 < t := lt_min hj (by linarith)
    have := hmin (Function.update q j (q j - t))
      (fun k => by
        by_cases hk : k = j
        · subst hk; simp only [Function.update_self]; linarith [min_le_left (q k) (∑ k, q k - Q)]
        · simp only [Function.update_of_ne hk]; exact hq k)
      (by rw [sum_update_id]; linarith [min_le_right (q j) (∑ k, q k - Q)])
    rw [sum_update_apply (fun k => (F k).c)] at this
    have := (F j).c_strictMono (Set.mem_Ici.2 (by linarith [min_le_left (q j) (∑ k, q k - Q)]))
      (Set.mem_Ici.2 (hq j)) (by linarith : q j - t < q j)
    linarith
  refine ⟨hbind, ?_⟩
  -- shifting output from an active firm `j` to `k` cannot lower cost
  have hA : ∀ j k, 0 < q j → (F j).dc (q j) ≤ (F k).dc (q k) := by
    intro j k hj
    by_cases hjk : k = j
    · subst hjk; exact le_rfl
    have hpert : ∀ t, 0 ≤ t → t ≤ q j →
        (F j).c (q j) + (F k).c (q k) ≤ (F j).c (q j - t) + (F k).c (q k + t) := by
      intro t ht htq
      have := hmin (Function.update (Function.update q j (q j - t)) k (q k + t))
        (fun l => by
          by_cases hl : l = k
          · subst hl; simp only [Function.update_self]; linarith [hq l]
          · simp only [Function.update_of_ne hl]
            by_cases hl' : l = j
            · subst hl'; simp only [Function.update_self]; linarith
            · simp only [Function.update_of_ne hl']; exact hq l)
        (by
          rw [sum_update_id, sum_update_id, Function.update_of_ne hjk]
          linarith)
      rw [sum_update_apply (fun l => (F l).c), sum_update_apply (fun l => (F l).c),
        Function.update_of_ne hjk] at this
      linarith
    have hd : HasDerivWithinAt (fun t => -((F j).c (q j - t) + (F k).c (q k + t)))
        (-(-(F j).dc (q j) + (F k).dc (q k))) (Set.Ici 0) 0 := by
      have h1 : HasDerivAt (fun t => (F j).c (q j - t)) (-(F j).dc (q j)) 0 :=
        HasDerivAt.comp_const_sub (q j) 0 (by simpa using foc_hasDerivAt (F j).hasDeriv hj)
      exact (h1.hasDerivWithinAt.add (hasDerivWithinAt_shift ((F k).hasDeriv _ (hq k))
        (hq k))).neg
    have := foc_local_necessary hd (by
      filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT hj] with t ht ht'
      have := hpert t (le_of_lt ht) ht'.2.le
      simp only [sub_zero, add_zero]
      linarith)
    linarith
  obtain ⟨j₀, hj₀⟩ := exists_pos_of_sum_pos (hbind ▸ hQ)
  refine ⟨(F j₀).dc (q j₀), (F j₀).dc_pos _ (hq j₀), fun k => ⟨hq k, hA j₀ k hj₀, fun hk => ?_⟩⟩
  exact le_antisymm (hA j₀ k hj₀) (hA k j₀ hk)

/-- **Exercise 10.C.3(a)** (MWG, p. 344): sufficiency. Plans with `∑ qⱼ = Q` satisfying the
first-order conditions minimize cost. -/
theorem exercise_10_C_3a_sufficient {F : κ → QLFirm} {μ : ℝ} (hμ : 0 ≤ μ) {q : κ → ℝ}
    (hq : IsCostFOC F μ q) : minCost F (∑ j, q j) = ∑ j, (F j).c (q j) :=
  minCost_eq_of_foc hμ hq

/-- **Exercise 10.C.3(b)** (MWG, p. 344). At a cost-minimizing plan for `Q > 0` (first-order
conditions with multiplier `μ`), `C` is differentiable with `C'(Q) = μ = cⱼ'(qⱼ*)` for every
active firm. -/
theorem exercise_10_C_3b {F : κ → QLFirm} {μ : ℝ} (hμ : 0 ≤ μ) {q : κ → ℝ}
    (hq : IsCostFOC F μ q) (hQ : 0 < ∑ j, q j) :
    HasDerivAt (minCost F) μ (∑ j, q j) ∧ ∀ j, 0 < q j → μ = (F j).dc (q j) := by
  classical
  refine ⟨?_, fun j hj => (hq j).2.2 hj⟩
  set Q := ∑ j, q j with hQdef
  obtain ⟨j₀, hj₀⟩ := exists_pos_of_sum_pos hQ
  set a := q j₀ with ha
  have hda : (F j₀).dc a = μ := ((hq j₀).2.2 hj₀).symm
  set g : ℝ → ℝ := fun y => (F j₀).c (a + (y - Q)) with hg
  have hgd : HasDerivAt g μ Q := by
    have h1 : HasDerivAt (fun y : ℝ => a + (y - Q)) 1 Q :=
      ((hasDerivAt_id Q).sub_const Q).const_add a
    have h2 : HasDerivAt (F j₀).c ((F j₀).dc a) (a + (Q - Q)) := by
      rw [sub_self, add_zero]; exact foc_hasDerivAt (F j₀).hasDeriv hj₀
    have := h2.comp Q h1
    rw [mul_one, hda] at this
    exact this
  have hgQ : g Q = (F j₀).c a := by simp [hg]
  have hmin := minCost_eq_of_foc hμ hq
  refine hasDerivAt_of_sandwich (e₁ := fun _ => 0) (Asymptotics.isLittleO_zero _ _)
    (remainder_isLittleO hgd) ?_
  have hnear : ∀ᶠ y in 𝓝 Q, Q - a < y := lt_mem_nhds (by linarith)
  filter_upwards [hnear] with y hy
  have hmem : ∑ k, (F k).c (Function.update q j₀ (a + (y - Q)) k) ∈ costSet F y := by
    refine ⟨_, fun k => ?_, ?_, rfl⟩
    · by_cases hk : k = j₀
      · subst hk; simp only [Function.update_self]; linarith
      · simp only [Function.update_of_ne hk]; exact (hq k).1
    · rw [sum_update_id]; linarith
  constructor
  · -- lower bound: the subgradient
    have hlow : ∑ k, (F k).c (q k) + μ * (y - Q) ≤ minCost F y := by
      refine le_csInf ⟨_, hmem⟩ ?_
      rintro s ⟨q', hq', hs, rfl⟩
      have := foc_cost_ge hq hq'
      nlinarith
    rw [hmin]
    linarith
  · -- upper bound: produce the change at firm `j₀`
    have hup := csInf_le ⟨_, fun s hs => costSet_lower F hs⟩ hmem
    rw [sum_update_apply (fun k => (F k).c)] at hup
    change minCost F y ≤ _ at hup
    rw [hmin]
    simp only [hg] at *
    linarith

omit [Fintype κ] in
/-- **Exercise 10.C.3(c)** (MWG, p. 344). Facing `p = C'(Q) = μ`, every firm's cost-minimizing
output `qⱼ*` maximizes its profit, so these choices produce `Q` in aggregate. -/
theorem exercise_10_C_3c {F : κ → QLFirm} {μ : ℝ} {q : κ → ℝ} (hq : IsCostFOC F μ q) (j : κ)
    (q' : ℝ) (hq' : 0 ≤ q') : μ * q' - (F j).c q' ≤ μ * q j - (F j).c (q j) :=
  ((F j).max_iff (hq j).1).2 (hq j).2 q' hq'

/-! ## Industry supply and the industry marginal cost (Figure 10.C.5) -/

/-- `minⱼ cⱼ'(0)`. -/
noncomputable def minMC [Nonempty κ] (F : κ → QLFirmStrict) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty fun j => (F j).dc 0

theorem minMC_le [Nonempty κ] (F : κ → QLFirmStrict) (j : κ) : minMC F ≤ (F j).dc 0 :=
  Finset.inf'_le (fun j => (F j).dc 0) (Finset.mem_univ j)

theorem exists_eq_minMC [Nonempty κ] (F : κ → QLFirmStrict) : ∃ j, (F j).dc 0 = minMC F := by
  obtain ⟨j, -, h⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (fun j => (F j).dc 0)
  exact ⟨j, h.symm⟩

theorem minMC_pos [Nonempty κ] (F : κ → QLFirmStrict) : 0 < minMC F := by
  obtain ⟨j, hj⟩ := exists_eq_minMC F
  rw [← hj]
  exact (F j).toQLFirm.dc_pos 0 le_rfl

theorem exists_lt_of_aggSupply_pos (F : κ → QLFirmStrict) {p : ℝ}
    (h : 0 < aggSupply F p) : ∃ j, (F j).dc 0 < p := by
  by_contra hno
  push Not at hno
  rw [(aggSupply_eq_zero_iff F p).2 hno] at h
  exact lt_irrefl 0 h

/-- The price at which industry supply equals a given `Q ≥ 0` exists. -/
theorem exists_invSupply [Nonempty κ] (F : κ → QLFirmStrict) (Q : ℝ) :
    ∃ μ, 0 ≤ Q → minMC F ≤ μ ∧ aggSupply F μ = Q ∧ (Q = 0 → μ = minMC F) := by
  by_cases hQ : 0 ≤ Q
  · rcases eq_or_lt_of_le hQ with h0 | hpos
    · refine ⟨minMC F, fun _ => ⟨le_rfl, ?_, fun _ => rfl⟩⟩
      rw [← h0]
      exact (aggSupply_eq_zero_iff F _).2 fun j => minMC_le F j
    · obtain ⟨j₀⟩ := ‹Nonempty κ›
      set hi := (F j₀).dc Q with hhi
      have hshi : (F j₀).supply hi = Q := (F j₀).supply_eq ⟨hQ, le_rfl, fun _ => rfl⟩
      have hge : Q ≤ aggSupply F hi := by
        rw [← hshi]
        exact Finset.single_le_sum (f := fun j => (F j).supply hi)
          (fun j _ => (F j).supply_nonneg hi) (Finset.mem_univ j₀)
      have hlohi : minMC F ≤ hi := (minMC_le F j₀).trans
        ((F j₀).dc_strictMono.monotoneOn (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hQ) hQ)
      have hlo : aggSupply F (minMC F) = 0 :=
        (aggSupply_eq_zero_iff F _).2 fun j => minMC_le F j
      obtain ⟨μ, hμ, hμQ⟩ := intermediate_value_Icc hlohi
        (aggSupply_continuous F).continuousOn ⟨by rw [hlo]; exact hQ, hge⟩
      exact ⟨μ, fun _ => ⟨hμ.1, hμQ, fun h => absurd h hpos.ne'⟩⟩
  · exact ⟨0, fun h => absurd h hQ⟩

/-- **The inverse industry supply function** `q⁻¹(Q)` (MWG, p. 321), with `q⁻¹(0) = minⱼ cⱼ'(0)`;
by `invSupply_hasDerivAt` it is the industry marginal cost `C'(Q)`. -/
noncomputable def invSupply [Nonempty κ] (F : κ → QLFirmStrict) (Q : ℝ) : ℝ :=
  Classical.choose (exists_invSupply F Q)

theorem invSupply_spec [Nonempty κ] (F : κ → QLFirmStrict) {Q : ℝ} (hQ : 0 ≤ Q) :
    minMC F ≤ invSupply F Q ∧ aggSupply F (invSupply F Q) = Q ∧
      (Q = 0 → invSupply F Q = minMC F) :=
  Classical.choose_spec (exists_invSupply F Q) hQ

theorem aggSupply_invSupply [Nonempty κ] (F : κ → QLFirmStrict) {Q : ℝ} (hQ : 0 ≤ Q) :
    aggSupply F (invSupply F Q) = Q := (invSupply_spec F hQ).2.1

theorem invSupply_pos [Nonempty κ] (F : κ → QLFirmStrict) {Q : ℝ} (hQ : 0 ≤ Q) :
    0 < invSupply F Q := (minMC_pos F).trans_le (invSupply_spec F hQ).1

/-- For `Q > 0`, `q⁻¹(Q)` is the unique price with industry supply `Q`. -/
theorem invSupply_unique [Nonempty κ] (F : κ → QLFirmStrict) {Q μ : ℝ} (hQ : 0 < Q)
    (h : aggSupply F μ = Q) : invSupply F Q = μ := by
  have hP := invSupply_spec F hQ.le
  have key : ∀ p₁ p₂, p₁ < p₂ → aggSupply F p₁ = Q → aggSupply F p₂ = Q → False := by
    intro p₁ p₂ h₁₂ e₁ e₂
    have := aggSupply_strictMono F h₁₂ (exists_lt_of_aggSupply_pos F (e₂ ▸ hQ))
    linarith
  rcases lt_trichotomy (invSupply F Q) μ with hlt | heq | hgt
  · exact (key _ _ hlt hP.2.1 h).elim
  · exact heq
  · exact (key _ _ hgt h hP.2.1).elim

/-- **(MWG, p. 321)** `q⁻¹(q(p)) = p` for `p > minⱼ cⱼ'(0)`. -/
theorem invSupply_aggSupply [Nonempty κ] (F : κ → QLFirmStrict) {p : ℝ} (hp : minMC F < p) :
    invSupply F (aggSupply F p) = p := by
  obtain ⟨j, hj⟩ := exists_eq_minMC F
  have hpos : 0 < aggSupply F p :=
    Finset.sum_pos' (fun k _ => (F k).supply_nonneg p)
      ⟨j, Finset.mem_univ j, ((F j).supply_pos_iff p).2 (hj ▸ hp)⟩
  exact invSupply_unique F hpos rfl

/-- The industry marginal cost is strictly increasing on `Q ≥ 0`. -/
theorem invSupply_strictMonoOn [Nonempty κ] (F : κ → QLFirmStrict) :
    StrictMonoOn (invSupply F) (Set.Ici 0) := by
  intro Q₁ h₁ Q₂ h₂ h₁₂
  have h₁' : (0 : ℝ) ≤ Q₁ := h₁
  have h₂' : (0 : ℝ) ≤ Q₂ := h₂
  refine lt_of_le_of_ne ?_ fun heq => ?_
  · by_contra hlt
    push Not at hlt
    have := aggSupply_monotone F hlt.le
    rw [aggSupply_invSupply F h₁', aggSupply_invSupply F h₂'] at this
    linarith
  · have e₁ := aggSupply_invSupply F h₁'
    have e₂ := aggSupply_invSupply F h₂'
    rw [heq] at e₁
    linarith

theorem invSupply_monotoneOn [Nonempty κ] (F : κ → QLFirmStrict) :
    MonotoneOn (invSupply F) (Set.Ici 0) := (invSupply_strictMonoOn F).monotoneOn

/-- The cost-minimizing plan for `Q`: each firm's supply at `q⁻¹(Q)`. -/
noncomputable def optPlan [Nonempty κ] (F : κ → QLFirmStrict) (Q : ℝ) (j : κ) : ℝ :=
  (F j).supply (invSupply F Q)

theorem optPlan_foc [Nonempty κ] (F : κ → QLFirmStrict) (Q : ℝ) :
    IsCostFOC (fun j => (F j).toQLFirm) (invSupply F Q) (optPlan F Q) :=
  fun j => (F j).supply_foc _

theorem optPlan_sum [Nonempty κ] (F : κ → QLFirmStrict) {Q : ℝ} (hQ : 0 ≤ Q) :
    ∑ j, optPlan F Q j = Q := aggSupply_invSupply F hQ

/-- `C(Q) = ∑ cⱼ(qⱼ*(Q))`. -/
theorem minCost_eq [Nonempty κ] (F : κ → QLFirmStrict) {Q : ℝ} (hQ : 0 ≤ Q) :
    minCost (fun j => (F j).toQLFirm) Q = ∑ j, (F j).c (optPlan F Q j) := by
  have := minCost_eq_of_foc (invSupply_pos F hQ).le (optPlan_foc F Q)
  rwa [optPlan_sum F hQ] at this

/-- **Footnotes 11-12, Figure 10.C.5** (MWG, p. 321). The industry marginal cost `C'(Q)` (the
derivative of the central authority's cost function) equals the inverse of the industry supply
function: `C' = q⁻¹` on `Q > 0`. -/
theorem invSupply_hasDerivAt [Nonempty κ] (F : κ → QLFirmStrict) {Q : ℝ} (hQ : 0 < Q) :
    HasDerivAt (minCost fun j => (F j).toQLFirm) (invSupply F Q) Q := by
  have h := (exercise_10_C_3b (invSupply_pos F hQ.le).le (optPlan_foc F Q)
    (by rw [optPlan_sum F hQ.le]; exact hQ)).1
  rwa [optPlan_sum F hQ.le] at h

/-- **Exercise 10.C.3(c)** (MWG, p. 344), strictly convex case: facing `p = C'(Q)` firms supply
exactly `Q` in aggregate, so `C'` is the inverse of the industry supply function. -/
theorem exercise_10_C_3c_strict [Nonempty κ] (F : κ → QLFirmStrict) {Q : ℝ} (hQ : 0 < Q) :
    HasDerivAt (minCost fun j => (F j).toQLFirm) (invSupply F Q) Q ∧
      aggSupply F (invSupply F Q) = Q :=
  ⟨invSupply_hasDerivAt F hQ, aggSupply_invSupply F hQ.le⟩

theorem minCost_zero [Nonempty κ] (F : κ → QLFirmStrict) :
    minCost (fun j => (F j).toQLFirm) 0 = ∑ j, (F j).c 0 := by
  have := minCost_eq F (le_refl (0 : ℝ))
  rw [this]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h0 : optPlan F 0 j = 0 := by
    have hs := optPlan_sum F (le_refl (0 : ℝ))
    exact (Finset.sum_eq_zero_iff_of_nonneg fun k _ => (F k).supply_nonneg _).1 hs j
      (Finset.mem_univ j)
  rw [h0]

end MWG.CompetitiveMarkets

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Welfare analysis in the partial equilibrium model (MWG Section 10.E, pp. 328-334)

* pp. 328-329 and footnote 17: with optimal lump-sum redistribution of the numeraire, welfare
  rises iff Marshallian aggregate surplus rises, for every (strictly increasing) social welfare
  function (`welfare_lt_iff_surplus_lt`); for the utilitarian `W = ∑ uᵢ` no transfers are
  needed. The potential Pareto improvement criterion (p. 334).
* (10.E.2)-(10.E.4) (p. 330): `dS = [P(x) - C'(x)] dx` along changes keeping the allocations
  optimal.
* (10.E.5) (p. 330): `S(x) = S₀ + ∫₀ˣ [P(s) - C'(s)] ds`, with `S₀ = -∑ cⱼ(0)` (zero when
  `cⱼ(0) = 0`), for the aggregate surplus at optimal distribution (`aggSurplus`).
* Footnote 19 (p. 331): `S` is concave, `S' = P - C'`, and `x* > 0` maximizes `S` iff
  `P(x*) = C'(x*)`, the competitive aggregate.
* Example 10.E.1 (pp. 331-333): the deadweight loss `S*(t) - S*(0) = ∫_{x*(0)}^{x*(t)} [P - C']`
  is negative (`deadweight_loss_neg`); consumer surplus (10.E.7)-(10.E.9), producer surplus
  (10.E.10)-(10.E.12), via envelope theorems `CS'(p) = -x(p)`, `Π'(p) = q(p)`.
* **Exercise 10.E.2** (p. 346): `∫₀^{x(p)} [P(s) - p] ds = ∫_p^∞ x(s) ds`.
-/

namespace MWG.CompetitiveMarkets

open Filter Topology MeasureTheory

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-! ## Social welfare and aggregate surplus (pp. 328-329) -/

/-- The utility vectors attainable by redistributing the numeraire when aggregate surplus plus
the numeraire endowment equals `s` (expression (10.D.1)). -/
def redistributionSet (s : ℝ) : Set (ι → ℝ) := {u | ∑ i, u i ≤ s}

/-- **(MWG, pp. 328-329)** With a central authority redistributing the numeraire to maximize a
social welfare function `W` that is strictly increasing (raising every utility raises `W`), the
maximized welfare is higher iff `ω_m + S` is higher: changes in welfare are measured by changes
in Marshallian aggregate surplus, for any such `W`. -/
theorem welfare_lt_iff_surplus_lt [Nonempty ι] (W : (ι → ℝ) → ℝ)
    (hW : ∀ u v : ι → ℝ, (∀ i, u i < v i) → W u < W v) {s₀ s₁ V₀ V₁ : ℝ}
    (h₀ : IsGreatest (W '' redistributionSet s₀) V₀)
    (h₁ : IsGreatest (W '' redistributionSet s₁) V₁) : V₀ < V₁ ↔ s₀ < s₁ := by
  constructor
  · intro hlt
    by_contra hle
    push Not at hle
    obtain ⟨u, hu, rfl⟩ := h₁.1
    have : W u ≤ V₀ := h₀.2 ⟨u, (show ∑ i, u i ≤ s₀ from le_trans hu hle), rfl⟩
    linarith
  · intro hlt
    obtain ⟨u, hu, rfl⟩ := h₀.1
    have hn : (0 : ℝ) < (Fintype.card ι : ℝ) := Nat.cast_pos.2 Fintype.card_pos
    set n : ℝ := (Fintype.card ι : ℝ)
    set δ := (s₁ - s₀) / n
    have hδ : 0 < δ := div_pos (by linarith) hn
    have hmem : (fun i => u i + δ) ∈ redistributionSet (ι := ι) s₁ := by
      change ∑ i, (u i + δ) ≤ s₁
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have : (Fintype.card ι : ℝ) * δ = s₁ - s₀ := by
        change n * ((s₁ - s₀) / n) = _; field_simp
      have hu' : ∑ i, u i ≤ s₀ := hu
      linarith
    exact (hW u _ fun i => by linarith).trans_le (h₁.2 ⟨_, hmem, rfl⟩)

/-- **Footnote 17** (MWG, p. 329). For the utilitarian `W = ∑ uᵢ` the maximized welfare is `s`
itself, attained by any distribution that wastes nothing: no transfers are necessary. -/
theorem footnote_10_E_17 (s : ℝ) {u : ι → ℝ} (hu : ∑ i, u i = s) :
    IsGreatest ((fun v : ι → ℝ => ∑ i, v i) '' redistributionSet s) s :=
  ⟨⟨u, hu.le, hu⟩, by rintro _ ⟨v, hv, rfl⟩; exact hv⟩

/-- **Potential Pareto improvement** (MWG, p. 334). Starting from utilities `u⁰` with no waste,
some redistribution of the numeraire after a change makes every consumer strictly better off
iff the new value of `ω_m + S` exceeds `∑ u⁰ᵢ`, i.e. iff aggregate surplus increases. -/
theorem potential_pareto_iff [Nonempty ι] (u₀ : ι → ℝ) (s₁ : ℝ) :
    (∃ u ∈ redistributionSet (ι := ι) s₁, ∀ i, u₀ i < u i) ↔ ∑ i, u₀ i < s₁ := by
  constructor
  · rintro ⟨u, hu, hlt⟩
    exact (Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ => hlt i).trans_le hu
  · intro hlt
    have hn : (0 : ℝ) < (Fintype.card ι : ℝ) := Nat.cast_pos.2 Fintype.card_pos
    set n : ℝ := (Fintype.card ι : ℝ)
    set δ := (s₁ - ∑ i, u₀ i) / n
    have hδ : 0 < δ := div_pos (by linarith) hn
    refine ⟨fun i => u₀ i + δ, ?_, fun i => by linarith⟩
    change ∑ i, (u₀ i + δ) ≤ s₁
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have : (Fintype.card ι : ℝ) * δ = s₁ - ∑ i, u₀ i := by
      change n * ((s₁ - ∑ i, u₀ i) / n) = _; field_simp
    linarith

/-! ## Differential changes (10.E.2)-(10.E.4) -/

/-- **(10.E.2)-(10.E.4)** (MWG, p. 330). If consumption is distributed optimally
(`φᵢ'(xᵢ) = P` for all `i`) and production too (`cⱼ'(qⱼ) = C'` for all `j`), then along a
differential change `(dx, dq)` with `∑ dxᵢ = ∑ dqⱼ = dx` the aggregate surplus changes at rate
`[P - C'] dx`. -/
theorem eq_10_E_4 (C : ι → QLConsumer) (F : κ → QLFirm) {x : ι → ℝ} {q : κ → ℝ}
    (hx : ∀ i, 0 < x i) (hq : ∀ j, 0 < q j) {P MC : ℝ} (hP : ∀ i, (C i).dφ (x i) = P)
    (hMC : ∀ j, (F j).dc (q j) = MC) (dx : ι → ℝ) (dq : κ → ℝ) (hd : ∑ j, dq j = ∑ i, dx i) :
    HasDerivAt (fun t => qlSurplus (fun i => (C i).φ) (fun j => (F j).c)
      (fun i => x i + t * dx i) (fun j => q j + t * dq j)) ((P - MC) * ∑ i, dx i) 0 := by
  have hφ : ∀ i, HasDerivAt (fun t => (C i).φ (x i + t * dx i)) ((C i).dφ (x i) * dx i) 0 := by
    intro i
    have h1 : HasDerivAt (fun t : ℝ => x i + t * dx i) (dx i) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (dx i)).const_add (x i)
    have h2 : HasDerivAt (C i).φ ((C i).dφ (x i)) (x i + 0 * dx i) := by
      rw [zero_mul, add_zero]; exact foc_hasDerivAt (C i).hasDeriv (hx i)
    exact h2.comp 0 h1
  have hc : ∀ j, HasDerivAt (fun t => (F j).c (q j + t * dq j)) ((F j).dc (q j) * dq j) 0 := by
    intro j
    have h1 : HasDerivAt (fun t : ℝ => q j + t * dq j) (dq j) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (dq j)).const_add (q j)
    have h2 : HasDerivAt (F j).c ((F j).dc (q j)) (q j + 0 * dq j) := by
      rw [zero_mul, add_zero]; exact foc_hasDerivAt (F j).hasDeriv (hq j)
    exact h2.comp 0 h1
  have h := (HasDerivAt.sum (u := Finset.univ) fun i _ => hφ i).sub
    (HasDerivAt.sum (u := Finset.univ) fun j _ => hc j)
  simp only [hP, hMC, ← Finset.mul_sum, hd] at h
  convert h using 1
  · ext t; simp [qlSurplus]
  · ring

/-! ## Aggregate surplus at optimal distribution (10.E.5) -/

/-- **(10.E.5)** (MWG, p. 330). Aggregate surplus at aggregate consumption `x` when consumption
and production are distributed optimally: `S(x) = γ(x) - C(x)`. -/
noncomputable def aggSurplus (C : ι → QLConsumer) (F : κ → QLFirmStrict) (X : ℝ) : ℝ :=
  grossBenefit C X - minCost (fun j => (F j).toQLFirm) X

/-- `γ` is continuous from the right at `0`: `0 ≤ γ(h) ≤ maxᵢ φᵢ'(0) · h`. -/
theorem grossBenefit_continuousWithinAt_zero [Nonempty ι] (C : ι → QLConsumer) :
    ContinuousWithinAt (grossBenefit C) (Set.Ici 0) 0 := by
  have hlow : ∀ h ∈ Set.Ici (0 : ℝ), 0 ≤ grossBenefit C h := by
    intro h hh
    rw [grossBenefit_eq C hh]
    exact Finset.sum_nonneg fun i _ => by
      have := (C i).φ_strictMono.monotoneOn (Set.mem_Ici.2 le_rfl)
        (Set.mem_Ici.2 (optAlloc_foc C hh i).1) (optAlloc_foc C hh i).1
      rwa [(C i).φ_zero] at this
  have hup : ∀ h ∈ Set.Ici (0 : ℝ), grossBenefit C h ≤ maxMB C * h := by
    intro h hh
    have := foc_benefit_le (C := C) (x := fun _ => 0) (μ := maxMB C)
      (fun i => ⟨le_rfl, le_maxMB C i, fun h => absurd h (lt_irrefl 0)⟩)
      (fun i => (optAlloc_foc C hh i).1)
    rw [optAlloc_sum C hh] at this
    rw [grossBenefit_eq C hh]
    simpa [QLConsumer.φ_zero] using this
  rw [ContinuousWithinAt, grossBenefit_zero]
  have ht : Tendsto (fun h => maxMB C * h) (𝓝[Set.Ici 0] 0) (𝓝 0) := by
    have : Tendsto (fun h => maxMB C * h) (𝓝 (0 : ℝ)) (𝓝 (maxMB C * 0)) :=
      (continuous_const.mul continuous_id).continuousAt
    rw [mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
    (eventually_nhdsWithin_of_forall hlow) (eventually_nhdsWithin_of_forall hup)

/-- `C` is continuous from the right at `0`. -/
theorem minCost_continuousWithinAt_zero [Nonempty κ] (F : κ → QLFirmStrict) :
    ContinuousWithinAt (minCost fun j => (F j).toQLFirm) (Set.Ici 0) 0 := by
  classical
  obtain ⟨j₀⟩ := ‹Nonempty κ›
  have hlow : ∀ h ∈ Set.Ici (0 : ℝ),
      minCost (fun j => (F j).toQLFirm) 0 ≤ minCost (fun j => (F j).toQLFirm) h := by
    intro h hh
    rw [minCost_zero, minCost_eq F hh]
    exact Finset.sum_le_sum fun j _ => (F j).toQLFirm.c_strictMono.monotoneOn
      (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 ((F j).supply_nonneg _)) ((F j).supply_nonneg _)
  have hup : ∀ h ∈ Set.Ici (0 : ℝ), minCost (fun j => (F j).toQLFirm) h ≤
      minCost (fun j => (F j).toQLFirm) 0 + ((F j₀).c h - (F j₀).c 0) := by
    intro h hh
    have hmem : ∑ k, (F k).c (Function.update (fun _ => (0 : ℝ)) j₀ h k) ∈
        costSet (fun j => (F j).toQLFirm) h := by
      refine ⟨_, fun k => ?_, ?_, rfl⟩
      · by_cases hk : k = j₀
        · subst hk; simp only [Function.update_self]; exact hh
        · simp only [Function.update_of_ne hk]; exact le_rfl
      · rw [sum_update_id]; simp
    have := csInf_le ⟨_, fun s hs => costSet_lower _ hs⟩ hmem
    rw [sum_update_apply (fun k => (F k).c)] at this
    rw [minCost_zero]
    exact this
  have hc : Tendsto (fun h => minCost (fun j => (F j).toQLFirm) 0 + ((F j₀).c h - (F j₀).c 0))
      (𝓝[Set.Ici 0] 0) (𝓝 (minCost (fun j => (F j).toQLFirm) 0)) := by
    have := ((F j₀).toQLFirm.c_continuousOn 0 (Set.mem_Ici.2 le_rfl)).sub
      (continuousWithinAt_const (b := (F j₀).c 0))
    have h2 := (this.const_add (minCost (fun j => (F j).toQLFirm) 0)).tendsto
    convert h2 using 2
    simp
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hc
    (eventually_nhdsWithin_of_forall hlow) (eventually_nhdsWithin_of_forall hup)

theorem aggSurplus_hasDerivAt [Nonempty ι] [Nonempty κ] (C : ι → QLConsumer)
    (F : κ → QLFirmStrict) {X : ℝ} (hX : 0 < X) :
    HasDerivAt (aggSurplus C F) (invDemand C X - invSupply F X) X :=
  (exercise_10_C_4b C hX).1.sub (invSupply_hasDerivAt F hX)

theorem aggSurplus_continuousOn [Nonempty ι] [Nonempty κ] (C : ι → QLConsumer)
    (F : κ → QLFirmStrict) : ContinuousOn (aggSurplus C F) (Set.Ici 0) := by
  intro X hX
  rcases eq_or_lt_of_le (Set.mem_Ici.1 hX) with h0 | hpos
  · subst h0
    exact (grossBenefit_continuousWithinAt_zero C).sub (minCost_continuousWithinAt_zero F)
  · exact (aggSurplus_hasDerivAt C F hpos).continuousAt.continuousWithinAt

theorem invDemand_intervalIntegrable [Nonempty ι] (C : ι → QLConsumer) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) : IntervalIntegrable (invDemand C) volume a b :=
  ((invDemand_antitoneOn C).mono fun _ hy =>
    Set.mem_Ici.2 (le_trans (le_min ha hb) hy.1)).intervalIntegrable

theorem invSupply_intervalIntegrable [Nonempty κ] (F : κ → QLFirmStrict) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) : IntervalIntegrable (invSupply F) volume a b :=
  ((invSupply_monotoneOn F).mono fun _ hy =>
    Set.mem_Ici.2 (le_trans (le_min ha hb) hy.1)).intervalIntegrable

/-- **(10.E.5)** (MWG, p. 330). `S(x) = S₀ + ∫₀ˣ [P(s) - C'(s)] ds`, with
`S₀ = S(0) = -∑ⱼ cⱼ(0)`. -/
theorem eq_10_E_5 [Nonempty ι] [Nonempty κ] (C : ι → QLConsumer) (F : κ → QLFirmStrict)
    {X : ℝ} (hX : 0 ≤ X) :
    aggSurplus C F X = aggSurplus C F 0 + ∫ s in (0 : ℝ)..X, (invDemand C s - invSupply F s) ∧
      aggSurplus C F 0 = -∑ j, (F j).c 0 := by
  refine ⟨?_, by simp [aggSurplus, grossBenefit_zero, minCost_zero]⟩
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hX
    ((aggSurplus_continuousOn C F).mono Set.Icc_subset_Ici_self)
    (fun x hx => aggSurplus_hasDerivAt C F hx.1)
    ((invDemand_intervalIntegrable C le_rfl hX).sub (invSupply_intervalIntegrable F le_rfl hX))]
  ring

/-- `S₀ = 0` when every `cⱼ(0) = 0` (MWG, p. 331). -/
theorem aggSurplus_zero_of_cost_zero [Nonempty ι] [Nonempty κ] (C : ι → QLConsumer)
    (F : κ → QLFirmStrict) (h0 : ∀ j, (F j).c 0 = 0) : aggSurplus C F 0 = 0 := by
  rw [(eq_10_E_5 C F le_rfl).2]
  simp [h0]

/-- `γ(x) = ∫₀ˣ P(s) ds`: the area under the inverse demand curve. -/
theorem grossBenefit_eq_integral [Nonempty ι] (C : ι → QLConsumer) {X : ℝ} (hX : 0 ≤ X) :
    grossBenefit C X = ∫ s in (0 : ℝ)..X, invDemand C s := by
  have hcont : ContinuousOn (grossBenefit C) (Set.Icc 0 X) := by
    intro y hy
    rcases eq_or_lt_of_le hy.1 with h0 | hpos
    · subst h0
      exact (grossBenefit_continuousWithinAt_zero C).mono Set.Icc_subset_Ici_self
    · exact (exercise_10_C_4b C hpos).1.continuousAt.continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hX hcont
    (fun x hx => (exercise_10_C_4b C hx.1).1) (invDemand_intervalIntegrable C le_rfl hX),
    grossBenefit_zero, sub_zero]

/-- `C(q) = C(0) + ∫₀^q C'(s) ds`. -/
theorem minCost_eq_integral [Nonempty κ] (F : κ → QLFirmStrict) {Q : ℝ} (hQ : 0 ≤ Q) :
    minCost (fun j => (F j).toQLFirm) Q =
      minCost (fun j => (F j).toQLFirm) 0 + ∫ s in (0 : ℝ)..Q, invSupply F s := by
  have hcont : ContinuousOn (minCost fun j => (F j).toQLFirm) (Set.Icc 0 Q) := by
    intro y hy
    rcases eq_or_lt_of_le hy.1 with h0 | hpos
    · subst h0
      exact (minCost_continuousWithinAt_zero F).mono Set.Icc_subset_Ici_self
    · exact (invSupply_hasDerivAt F hpos).continuousAt.continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hQ hcont
    (fun x hx => invSupply_hasDerivAt F hx.1) (invSupply_intervalIntegrable F le_rfl hQ)]
  ring

/-- **Footnote 19** (MWG, p. 331). `S` is concave on `x ≥ 0`. -/
theorem footnote_10_E_19_concave [Nonempty ι] [Nonempty κ] (C : ι → QLConsumer)
    (F : κ → QLFirmStrict) : ConcaveOn ℝ (Set.Ici 0) (aggSurplus C F) := by
  refine AntitoneOn.concaveOn_of_deriv (convex_Ici 0) (aggSurplus_continuousOn C F) ?_ ?_
  · rw [interior_Ici]
    exact fun x hx => (aggSurplus_hasDerivAt C F hx).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]
    intro x hx y hy hxy
    rw [(aggSurplus_hasDerivAt C F hx).deriv, (aggSurplus_hasDerivAt C F hy).deriv]
    have h1 := invDemand_antitoneOn C (Set.mem_Ici.2 (le_of_lt hx)) (Set.mem_Ici.2
      (le_of_lt hy)) hxy
    have h2 := invSupply_monotoneOn F (Set.mem_Ici.2 (le_of_lt hx)) (Set.mem_Ici.2
      (le_of_lt hy)) hxy
    linarith

/-- **Footnote 19** (MWG, p. 331). `x* > 0` maximizes aggregate surplus on `x ≥ 0` iff
`S'(x*) = P(x*) - C'(x*) = 0`. -/
theorem footnote_10_E_19 [Nonempty ι] [Nonempty κ] (C : ι → QLConsumer) (F : κ → QLFirmStrict)
    {X : ℝ} (hX : 0 < X) :
    (∀ y, 0 ≤ y → aggSurplus C F y ≤ aggSurplus C F X) ↔ invDemand C X = invSupply F X := by
  have hd := aggSurplus_hasDerivAt C F hX
  constructor
  · intro hmax
    have hloc : IsLocalMax (aggSurplus C F) X := by
      filter_upwards [Ioi_mem_nhds hX] with y hy
      exact hmax y (le_of_lt hy)
    have := hloc.hasDerivAt_eq_zero hd
    linarith
  · intro heq y hy
    have hcont := aggSurplus_continuousOn C F
    rcases le_total y X with hyX | hXy
    · have hmono : MonotoneOn (aggSurplus C F) (Set.Icc 0 X) := by
        refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 X)
          (hcont.mono Set.Icc_subset_Ici_self)
          (fun z hz => by
            rw [interior_Icc] at hz
            exact (aggSurplus_hasDerivAt C F hz.1).hasDerivWithinAt) ?_
        intro z hz
        rw [interior_Icc] at hz
        have h1 := invDemand_antitoneOn C (Set.mem_Ici.2 hz.1.le) (Set.mem_Ici.2 hX.le) hz.2.le
        have h2 := invSupply_monotoneOn F (Set.mem_Ici.2 hz.1.le) (Set.mem_Ici.2 hX.le) hz.2.le
        linarith
      exact hmono ⟨hy, hyX⟩ ⟨hX.le, le_rfl⟩ hyX
    · have hanti : AntitoneOn (aggSurplus C F) (Set.Ici X) := by
        refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici X)
          (hcont.mono fun z hz => Set.mem_Ici.2 (hX.le.trans hz))
          (fun z hz => by
            rw [interior_Ici] at hz
            exact (aggSurplus_hasDerivAt C F (hX.trans hz)).hasDerivWithinAt) ?_
        intro z hz
        rw [interior_Ici] at hz
        have h1 := invDemand_antitoneOn C (Set.mem_Ici.2 hX.le)
          (Set.mem_Ici.2 (hX.trans hz).le) hz.le
        have h2 := invSupply_monotoneOn F (Set.mem_Ici.2 hX.le)
          (Set.mem_Ici.2 (hX.trans hz).le) hz.le
        linarith
      exact hanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hXy) hXy

/-- **(MWG, p. 331)** The competitive aggregate `x* = x(p*) = q(p*) > 0` satisfies
`P(x*) = p* = C'(x*)`, so it maximizes aggregate surplus. -/
theorem competitive_maximizes_surplus [Nonempty ι] [Nonempty κ] (C : ι → QLConsumer)
    (F : κ → QLFirmStrict) {p : ℝ} (hp : 0 < p) (hX : 0 < aggDemand C p)
    (hclear : aggDemand C p = aggSupply F p) :
    invDemand C (aggDemand C p) = p ∧ invSupply F (aggDemand C p) = p ∧
      ∀ y, 0 ≤ y → aggSurplus C F y ≤ aggSurplus C F (aggDemand C p) := by
  have h1 := invDemand_unique C hX hp rfl
  have h2 := invSupply_unique F hX hclear.symm
  exact ⟨h1, h2, (footnote_10_E_19 C F hX).2 (h1.trans h2.symm)⟩

/-- **Example 10.E.1** (MWG, p. 332), (10.E.6). If aggregate consumption falls from the
competitive level `x₀` (where `P(x₀) = C'(x₀)`) to `x₁ < x₀`, the change in aggregate surplus
is `∫_{x₀}^{x₁} [P - C'] < 0`: the deadweight loss. -/
theorem deadweight_loss_neg [Nonempty ι] [Nonempty κ] (C : ι → QLConsumer)
    (F : κ → QLFirmStrict) {X₀ X₁ : ℝ} (h₁ : 0 ≤ X₁) (h₁₀ : X₁ < X₀)
    (heq : invDemand C X₀ = invSupply F X₀) :
    aggSurplus C F X₁ - aggSurplus C F X₀ =
        ∫ s in X₀..X₁, (invDemand C s - invSupply F s) ∧
      aggSurplus C F X₁ - aggSurplus C F X₀ < 0 := by
  have h₀ : 0 ≤ X₀ := h₁.trans h₁₀.le
  have hint : ∀ a b, 0 ≤ a → 0 ≤ b →
      IntervalIntegrable (fun s => invDemand C s - invSupply F s) volume a b :=
    fun a b ha hb => (invDemand_intervalIntegrable C ha hb).sub
      (invSupply_intervalIntegrable F ha hb)
  have hdiff : aggSurplus C F X₁ - aggSurplus C F X₀ =
      ∫ s in X₀..X₁, (invDemand C s - invSupply F s) := by
    rw [(eq_10_E_5 C F h₁).1, (eq_10_E_5 C F h₀).1, add_sub_add_left_eq_sub,
      intervalIntegral.integral_interval_sub_left (hint 0 X₁ le_rfl h₁) (hint 0 X₀ le_rfl h₀)]
  refine ⟨hdiff, ?_⟩
  rw [hdiff, intervalIntegral.integral_symm, neg_lt_zero]
  refine intervalIntegral.intervalIntegral_pos_of_pos_on (hint X₁ X₀ h₁ h₀) (fun s hs => ?_) h₁₀
  have hs0 : 0 ≤ s := h₁.trans hs.1.le
  have hP := invDemand_strictAntiOn C (Set.mem_Ici.2 hs0) (Set.mem_Ici.2 h₀) hs.2
  have hC := invSupply_monotoneOn F (Set.mem_Ici.2 hs0) (Set.mem_Ici.2 h₀) hs.2.le
  linarith

/-! ## Consumer and producer surplus -/

/-- **(MWG, p. 332)** Aggregate consumer surplus at effective price `p̂`:
`CS(p̂) = ∑ φᵢ(xᵢ(p̂)) - p̂ x(p̂)`. -/
noncomputable def consumerSurplus (C : ι → QLConsumer) (p : ℝ) : ℝ :=
  ∑ i, (C i).φ ((C i).demand p) - p * aggDemand C p

/-- **(MWG, p. 333)** Aggregate producer surplus (profit) at effective price `p̂`:
`Π(p̂) = p̂ q(p̂) - ∑ cⱼ(qⱼ(p̂))`. -/
noncomputable def producerSurplus (F : κ → QLFirmStrict) (p : ℝ) : ℝ :=
  p * aggSupply F p - ∑ j, (F j).c ((F j).supply p)

/-- Envelope theorem for a consumer's surplus: `d/dp [φ(x(p)) - p x(p)] = -x(p)` at `p > 0`. -/
theorem QLConsumer.surplus_hasDerivAt (C : QLConsumer) {p : ℝ} (hp : 0 < p) :
    HasDerivAt (fun r => C.φ (C.demand r) - r * C.demand r) (-C.demand p) p := by
  have hcont := C.demand_continuousAt hp
  have hlo : (fun r => C.demand r - C.demand p) =o[𝓝 p] (fun _ => (1 : ℝ)) :=
    (Asymptotics.isLittleO_one_iff ℝ).2 (tendsto_sub_nhds_zero_iff.2 hcont)
  have h₂ : (fun r => -((r - p) * (C.demand r - C.demand p))) =o[𝓝 p] fun r => r - p := by
    have := (Asymptotics.isBigO_refl (fun r => r - p) (𝓝 p)).mul_isLittleO hlo
    simpa using this.neg_left
  refine hasDerivAt_of_sandwich (e₁ := fun _ => 0) (Asymptotics.isLittleO_zero _ _) h₂ ?_
  filter_upwards [Ioi_mem_nhds hp] with r hr
  have h1 := C.demand_max hr (C.demand p) (C.demand_nonneg hp)
  have h2 := C.demand_max hp (C.demand r) (C.demand_nonneg hr)
  constructor <;> nlinarith

/-- Envelope theorem for a firm's profit: `d/dp [p q(p) - c(q(p))] = q(p)`. -/
theorem QLFirmStrict.profit_hasDerivAt (F : QLFirmStrict) (p : ℝ) :
    HasDerivAt (fun r => r * F.supply r - F.c (F.supply r)) (F.supply p) p := by
  have hcont := F.supply_continuous.continuousAt (x := p)
  have hlo : (fun r => F.supply r - F.supply p) =o[𝓝 p] (fun _ => (1 : ℝ)) :=
    (Asymptotics.isLittleO_one_iff ℝ).2 (tendsto_sub_nhds_zero_iff.2 hcont)
  have h₂ : (fun r => (r - p) * (F.supply r - F.supply p)) =o[𝓝 p] fun r => r - p := by
    simpa using (Asymptotics.isBigO_refl (fun r => r - p) (𝓝 p)).mul_isLittleO hlo
  refine hasDerivAt_of_sandwich (e₁ := fun _ => 0) (Asymptotics.isLittleO_zero _ _) h₂ ?_
  refine Filter.Eventually.of_forall fun r => ?_
  have h1 := F.supply_max r (F.supply p) (F.supply_nonneg p)
  have h2 := F.supply_max p (F.supply r) (F.supply_nonneg r)
  constructor <;> nlinarith

/-- **Envelope theorem** (MWG, p. 333): `CS'(p) = -x(p)` for `p > 0`. -/
theorem consumerSurplus_hasDerivAt (C : ι → QLConsumer) {p : ℝ} (hp : 0 < p) :
    HasDerivAt (consumerSurplus C) (-aggDemand C p) p := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun i _ => (C i).surplus_hasDerivAt hp
  have heq : (fun r => ∑ i ∈ Finset.univ, ((C i).φ ((C i).demand r) - r * (C i).demand r)) =
      consumerSurplus C := by
    ext r
    simp [consumerSurplus, aggDemand, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [heq] at h
  simpa [aggDemand, Finset.sum_neg_distrib] using h

/-- **Envelope theorem** (MWG, p. 333): `Π'(p) = q(p)`. -/
theorem producerSurplus_hasDerivAt (F : κ → QLFirmStrict) (p : ℝ) :
    HasDerivAt (producerSurplus F) (aggSupply F p) p := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun j _ => (F j).profit_hasDerivAt p
  have heq : (fun r => ∑ j ∈ Finset.univ, (r * (F j).supply r - (F j).c ((F j).supply r))) =
      producerSurplus F := by
    ext r
    simp [producerSurplus, aggSupply, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [heq] at h
  simpa [aggSupply] using h

theorem consumerSurplus_eq_zero [Nonempty ι] (C : ι → QLConsumer) {p : ℝ}
    (hp : maxMB C ≤ p) : consumerSurplus C p = 0 := by
  have hp0 : 0 < p := (maxMB_pos C).trans_le hp
  have h0 : ∀ i, (C i).demand p = 0 := fun i =>
    ((C i).demand_eq_zero_iff hp0).2 ((le_maxMB C i).trans hp)
  simp [consumerSurplus, aggDemand, h0, QLConsumer.φ_zero]

/-- **(10.E.9)** (MWG, p. 333). `CS(p') - CS(p) = -∫_p^{p'} x(s) ds` for `0 < p ≤ p'`. -/
theorem eq_10_E_9 (C : ι → QLConsumer) {p p' : ℝ} (hp : 0 < p) (hpp : p ≤ p') :
    consumerSurplus C p' - consumerSurplus C p = -∫ s in p..p', aggDemand C s := by
  have hint : IntervalIntegrable (aggDemand C) volume p p' :=
    ((aggDemand_antitoneOn C).mono fun y hy =>
      Set.mem_Ioi.2 (hp.trans_le (le_trans (le_min le_rfl hpp) hy.1))).intervalIntegrable
  rw [← intervalIntegral.integral_neg, intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hpp
    (fun x hx => (consumerSurplus_hasDerivAt C (hp.trans_le hx.1)).continuousAt.continuousWithinAt)
    (fun x hx => consumerSurplus_hasDerivAt C (hp.trans hx.1)) hint.neg]

/-- **(10.E.8)** (MWG, p. 333). `CS(p) = ∫_p^∞ x(s) ds` for `p > 0` (the integrand vanishes above
`maxᵢ φᵢ'(0)`). -/
theorem eq_10_E_8 [Nonempty ι] (C : ι → QLConsumer) {p : ℝ} (hp : 0 < p) :
    consumerSurplus C p = ∫ s in Set.Ioi p, aggDemand C s := by
  set M := max p (maxMB C) with hM
  have hpM : p ≤ M := le_max_left _ _
  have hMM : maxMB C ≤ M := le_max_right _ _
  have h1 := eq_10_E_9 C hp hpM
  rw [consumerSurplus_eq_zero C hMM] at h1
  have h2 : ∫ s in Set.Ioi p, aggDemand C s = ∫ s in Set.Ioc p M, aggDemand C s := by
    refine (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      Set.Ioc_subset_Ioi_self fun s hs => ?_)
    have hsM : M < s := by
      by_contra hle; push Not at hle; exact hs.2 ⟨hs.1, hle⟩
    exact (aggDemand_eq_zero_iff C (hp.trans hs.1)).2 fun i =>
      (le_maxMB C i).trans (hMM.trans hsM.le)
  rw [h2, ← intervalIntegral.integral_of_le hpM]
  linarith

/-- **(10.E.7)** (MWG, p. 332). `CS(p) = ∫₀^{x(p)} [P(s) - p] ds` for `p > 0`: consumption at
`p` is distributed optimally, so `∑ φᵢ(xᵢ(p)) = γ(x(p)) = ∫₀^{x(p)} P`. -/
theorem eq_10_E_7 [Nonempty ι] (C : ι → QLConsumer) {p : ℝ} (hp : 0 < p) :
    consumerSurplus C p = ∫ s in (0 : ℝ)..aggDemand C p, (invDemand C s - p) := by
  have hX := aggDemand_nonneg C hp
  have hγ : ∑ i, (C i).φ ((C i).demand p) = grossBenefit C (aggDemand C p) :=
    (grossBenefit_eq_of_foc (x := fun i => (C i).demand p) fun i => (C i).demand_spec hp).symm
  rw [intervalIntegral.integral_sub (invDemand_intervalIntegrable C le_rfl hX)
    intervalIntegrable_const, intervalIntegral.integral_const, ← grossBenefit_eq_integral C hX,
    ← hγ, consumerSurplus]
  simp [smul_eq_mul]
  ring

/-- **Exercise 10.E.2** (MWG, pp. 346-347). `∫₀^{x(p̂)} [P(s) - p̂] ds = ∫_{p̂}^∞ x(s) ds`
(proved through the common value `CS(p̂)`, by the fundamental theorem of calculus and the
envelope theorem rather than by a change of variables). -/
theorem exercise_10_E_2 [Nonempty ι] (C : ι → QLConsumer) {p : ℝ} (hp : 0 < p) :
    ∫ s in (0 : ℝ)..aggDemand C p, (invDemand C s - p) = ∫ s in Set.Ioi p, aggDemand C s := by
  rw [← eq_10_E_7 C hp, eq_10_E_8 C hp]

/-- `Π(p) = -∑ cⱼ(0)` when `p ≤ minⱼ cⱼ'(0)` (no firm is active). -/
theorem producerSurplus_eq_of_le [Nonempty κ] (F : κ → QLFirmStrict) {p : ℝ}
    (hp : p ≤ minMC F) : producerSurplus F p = -∑ j, (F j).c 0 := by
  have h0 : ∀ j, (F j).supply p = 0 := fun j =>
    ((F j).supply_eq_zero_iff p).2 (hp.trans (minMC_le F j))
  simp [producerSurplus, aggSupply, h0]

/-- **(10.E.11)** (MWG, p. 333). `Π(p) = Π₀ + ∫₀^p q(s) ds` with `Π₀ = -∑ cⱼ(0)` (zero when
`cⱼ(0) = 0`), for `p ≥ 0`. -/
theorem eq_10_E_11 [Nonempty κ] (F : κ → QLFirmStrict) {p : ℝ} (hp : 0 ≤ p) :
    producerSurplus F p = -∑ j, (F j).c 0 + ∫ s in (0 : ℝ)..p, aggSupply F s := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hp
    (fun x _ => (producerSurplus_hasDerivAt F x).continuousAt.continuousWithinAt)
    (fun x _ => producerSurplus_hasDerivAt F x)
    ((aggSupply_continuous F).intervalIntegrable 0 p),
    producerSurplus_eq_of_le F (minMC_pos F).le]
  ring

/-- **(10.E.12)** (MWG, p. 333). `Π(p') - Π(p) = ∫_p^{p'} q(s) ds`. -/
theorem eq_10_E_12 (F : κ → QLFirmStrict) {p p' : ℝ} (hpp : p ≤ p') :
    producerSurplus F p' - producerSurplus F p = ∫ s in p..p', aggSupply F s := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hpp
    (fun x _ => (producerSurplus_hasDerivAt F x).continuousAt.continuousWithinAt)
    (fun x _ => producerSurplus_hasDerivAt F x)
    ((aggSupply_continuous F).intervalIntegrable p p')]

/-- **(10.E.10)** (MWG, p. 333). `Π(p) = Π₀ + ∫₀^{q(p)} [p - C'(s)] ds` for `p ≥ 0`: production at
`p` is distributed optimally, so `∑ cⱼ(qⱼ(p)) = C(q(p)) = C(0) + ∫₀^{q(p)} C'`. -/
theorem eq_10_E_10 [Nonempty κ] (F : κ → QLFirmStrict) {p : ℝ} (hp : 0 ≤ p) :
    producerSurplus F p = -∑ j, (F j).c 0 + ∫ s in (0 : ℝ)..aggSupply F p, (p - invSupply F s) := by
  have hQ := aggSupply_nonneg F p
  have hC : ∑ j, (F j).c ((F j).supply p) = minCost (fun j => (F j).toQLFirm) (aggSupply F p) :=
    (minCost_eq_of_foc (F := fun j => (F j).toQLFirm) hp
      (fun j => (F j).supply_foc p)).symm
  rw [intervalIntegral.integral_sub intervalIntegrable_const
    (invSupply_intervalIntegrable F le_rfl hQ), intervalIntegral.integral_const,
    producerSurplus, hC, minCost_eq_integral F hQ, minCost_zero]
  simp [smul_eq_mul]
  ring

end MWG.CompetitiveMarkets

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Comparative statics of a sales tax (MWG Example 10.C.1, pp. 323-324; Example 10.E.1)

With a per-unit tax `t` paid by consumers, the equilibrium producer price `p*(t)` solves
`x(p*(t) + t) = q(p*(t))` (10.C.7). For the quasilinear model with strictly convex costs:

* `taxPrice` exists and is unique for `t ∈ (-minⱼ cⱼ'(0), maxᵢ φᵢ'(0) - minⱼ cⱼ'(0))` (taxes
  and small subsidies), with positive trade.
* Monotone comparative statics (p. 323): `p*(t)` strictly decreases, the consumer price
  `p*(t) + t` weakly increases and the quantity traded decreases as `t` increases.
* (10.C.8): `p*` is differentiable with `p*'(t) = -x'/(x' - q')` whenever aggregate demand and
  supply are differentiable at the relevant prices with `x' < 0 ≤ q'`; hence `-1 ≤ p*'(t) < 0`;
  `p*'(t) = -1` when `q' = 0`. The formula in terms of `φᵢ''`, `cⱼ''` (p. 324) and its
  derivation through the implicit function theorem (**Exercise 10.C.5**).
* Example 10.E.1: the deadweight loss `S*(t) - S*(0) < 0` for `t > 0`, the decomposition
  `S = CS + Π + tax revenue`.
* **Exercise 10.C.6** (specific versus ad valorem taxes and who pays) and **Exercise 10.C.7**
  (constant-elasticity incidence).
-/

namespace MWG.CompetitiveMarkets

open Filter Topology MeasureTheory

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- A function antitone on a neighbourhood of `a` whose image is a neighbourhood of `f a` is
continuous at `a`. -/
theorem continuousAt_of_antitoneOn_of_image_mem_nhds {f : ℝ → ℝ} {s : Set ℝ} {a : ℝ}
    (h : AntitoneOn f s) (hs : s ∈ 𝓝 a) (hfs : f '' s ∈ 𝓝 (f a)) : ContinuousAt f a := by
  have hm : MonotoneOn (fun x => -f x) s := fun x hx y hy hxy => neg_le_neg (h hx hy hxy)
  have himg : (fun x => -f x) '' s ∈ 𝓝 (-f a) := by
    have : (fun x => -f x) '' s = Neg.neg ⁻¹' (f '' s) := by
      ext y
      simp only [Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, by ring⟩
      · rintro ⟨x, hx, hxy⟩; exact ⟨x, hx, by rw [hxy, neg_neg]⟩
    rw [this]
    exact continuous_neg.continuousAt.preimage_mem_nhds (by rwa [neg_neg])
  have h2 := (continuousAt_of_monotoneOn_of_image_mem_nhds hm hs himg).neg
  convert h2 using 1
  funext x
  simp

/-- **The inverse demand function is continuous** on `x > 0`. -/
theorem invDemand_continuousAt [Nonempty ι] (C : ι → QLConsumer) {X : ℝ} (hX : 0 < X) :
    ContinuousAt (invDemand C) X := by
  refine continuousAt_of_antitoneOn_of_image_mem_nhds
    ((invDemand_antitoneOn C).mono Set.Ioi_subset_Ici_self) (Ioi_mem_nhds hX) ?_
  have hP0 := invDemand_pos C hX.le
  have hPm : invDemand C X < maxMB C := by
    obtain ⟨i, hi⟩ := exists_lt_of_aggDemand_pos C hP0 ((aggDemand_invDemand C hX.le).symm ▸ hX)
    exact hi.trans_le (le_maxMB C i)
  refine Filter.mem_of_superset (Ioo_mem_nhds hP0 hPm) fun p hp => ?_
  obtain ⟨i, hi⟩ := exists_eq_maxMB C
  have hpos : 0 < aggDemand C p := Finset.sum_pos' (fun k _ => (C k).demand_nonneg hp.1)
    ⟨i, Finset.mem_univ i, ((C i).demand_pos_iff hp.1).2 (hi ▸ hp.2)⟩
  exact ⟨aggDemand C p, hpos, invDemand_aggDemand C hp.1 hp.2⟩

/-- **Derivative of the inverse demand function**: `P'(x) = 1/x'(P(x))` when `x'(P(x)) ≠ 0`. -/
theorem invDemand_hasDerivAt [Nonempty ι] (C : ι → QLConsumer) {X d : ℝ} (hX : 0 < X)
    (hd : HasDerivAt (aggDemand C) d (invDemand C X)) (hd0 : d ≠ 0) :
    HasDerivAt (invDemand C) d⁻¹ X := by
  refine HasDerivAt.of_local_left_inverse (invDemand_continuousAt C hX) hd hd0 ?_
  filter_upwards [Ioi_mem_nhds hX] with y hy
  exact aggDemand_invDemand C (le_of_lt hy)

/-! ## The equilibrium with a tax -/

/-- Existence and uniqueness of the producer price with a tax `t` paid by consumers, for
`-minⱼ cⱼ'(0) < t < maxᵢ φᵢ'(0) - minⱼ cⱼ'(0)` (10.C.7). -/
theorem exists_taxPrice [Nonempty ι] [Nonempty κ] (C : ι → QLConsumer) (F : κ → QLFirmStrict)
    (t : ℝ) : ∃ p, (-minMC F < t ∧ t < maxMB C - minMC F) →
      minMC F < p ∧ p + t < maxMB C ∧ aggDemand C (p + t) = aggSupply F p := by
  by_cases ht : -minMC F < t ∧ t < maxMB C - minMC F
  · obtain ⟨ht1, ht2⟩ := ht
    set lo := minMC F
    set hi := maxMB C - t
    have hlohi : lo < hi := by simp only [hi]; linarith
    have hZcont : ContinuousOn (fun p => aggDemand C (p + t) - aggSupply F p) (Set.Icc lo hi) := by
      refine ContinuousOn.sub ?_ (aggSupply_continuous F).continuousOn
      exact (aggDemand_continuousOn C).comp (continuousOn_id.add continuousOn_const)
        fun p hp => Set.mem_Ioi.2 (by linarith [hp.1])
    have hZlo : 0 < aggDemand C (lo + t) - aggSupply F lo := by
      have hq : aggSupply F lo = 0 := (aggSupply_eq_zero_iff F lo).2 fun j => minMC_le F j
      obtain ⟨i, hi⟩ := exists_eq_maxMB C
      have hx : 0 < aggDemand C (lo + t) := Finset.sum_pos'
        (fun k _ => (C k).demand_nonneg (by linarith))
        ⟨i, Finset.mem_univ i, ((C i).demand_pos_iff (by linarith)).2 (by rw [hi]; linarith)⟩
      linarith
    have hZhi : aggDemand C (hi + t) - aggSupply F hi < 0 := by
      have hx : aggDemand C (hi + t) = 0 := by
        refine (aggDemand_eq_zero_iff C (by simp only [hi]; linarith [maxMB_pos C])).2
          fun i => ?_
        simp only [hi, sub_add_cancel]; exact le_maxMB C i
      obtain ⟨j, hj⟩ := exists_eq_minMC F
      have hq : 0 < aggSupply F hi := Finset.sum_pos' (fun k _ => (F k).supply_nonneg _)
        ⟨j, Finset.mem_univ j, ((F j).supply_pos_iff _).2 (by rw [hj]; exact hlohi)⟩
      linarith
    obtain ⟨p, hp, hpZ⟩ := intermediate_value_Icc' hlohi.le hZcont ⟨hZhi.le, hZlo.le⟩
    refine ⟨p, fun _ => ⟨lt_of_le_of_ne hp.1 fun h => ?_, lt_of_le_of_ne ?_ fun h => ?_, ?_⟩⟩
    · rw [← h] at hpZ; linarith
    · have := hp.2; simp only [hi] at this; linarith
    · have : p = hi := by simp only [hi]; linarith
      rw [this] at hpZ; linarith
    · linarith [hpZ]
  · exact ⟨0, fun h => absurd h ht⟩

/-- **The producer price `p*(t)` with a per-unit tax `t` on consumers** (MWG, p. 323). -/
noncomputable def taxPrice [Nonempty ι] [Nonempty κ] (C : ι → QLConsumer)
    (F : κ → QLFirmStrict) (t : ℝ) : ℝ :=
  Classical.choose (exists_taxPrice C F t)

/-- The admissible tax range `(-minⱼ cⱼ'(0), maxᵢ φᵢ'(0) - minⱼ cⱼ'(0))`. -/
def taxRange [Nonempty ι] [Nonempty κ] (C : ι → QLConsumer) (F : κ → QLFirmStrict) : Set ℝ :=
  Set.Ioo (-minMC F) (maxMB C - minMC F)

theorem taxPrice_spec [Nonempty ι] [Nonempty κ] (C : ι → QLConsumer) (F : κ → QLFirmStrict)
    {t : ℝ} (ht : t ∈ taxRange C F) :
    minMC F < taxPrice C F t ∧ taxPrice C F t + t < maxMB C ∧
      aggDemand C (taxPrice C F t + t) = aggSupply F (taxPrice C F t) :=
  Classical.choose_spec (exists_taxPrice C F t) ht

/-- **(10.C.7)** uniquely determines `p*(t)`: any price with positive consumer price clearing
the market equals `p*(t)`. -/
theorem taxPrice_unique [Nonempty ι] [Nonempty κ] (C : ι → QLConsumer) (F : κ → QLFirmStrict)
    {t p : ℝ} (ht : t ∈ taxRange C F) (hpt : 0 < p + t)
    (h : aggDemand C (p + t) = aggSupply F p) : taxPrice C F t = p := by
  obtain ⟨h1, h2, h3⟩ := taxPrice_spec C F ht
  have ht1 : -minMC F < t := ht.1
  have hp : minMC F < p := by
    by_contra hle
    push Not at hle
    have hq := (aggSupply_eq_zero_iff F p).2 fun j => hle.trans (minMC_le F j)
    rw [hq] at h
    have := (aggDemand_eq_zero_iff C hpt).1 h
    obtain ⟨i, hi⟩ := exists_eq_maxMB C
    have := this i
    rw [hi] at this
    linarith [ht.2]
  have key : ∀ p₁ p₂, minMC F < p₁ → p₁ < p₂ → 0 < p₁ + t →
      aggDemand C (p₁ + t) = aggSupply F p₁ → aggDemand C (p₂ + t) = aggSupply F p₂ → False := by
    intro p₁ p₂ hp₁ h₁₂ hpt₁ e₁ e₂
    obtain ⟨j, hj⟩ := exists_eq_minMC F
    have hs := aggSupply_strictMono F h₁₂ ⟨j, by rw [hj]; linarith⟩
    have hd := aggDemand_antitoneOn C hpt₁ (show (0 : ℝ) < p₂ + t by linarith)
      (by linarith : p₁ + t ≤ p₂ + t)
    linarith
  rcases lt_trichotomy (taxPrice C F t) p with hlt | heq | hgt
  · exact (key _ _ h1 hlt (by linarith [(minMC_pos F)]) h3 h).elim
  · exact heq
  · exact (key _ _ hp hgt hpt h h3).elim

/-- The equilibrium aggregate quantity `x*(t)`. -/
noncomputable def taxQuantity [Nonempty ι] [Nonempty κ] (C : ι → QLConsumer)
    (F : κ → QLFirmStrict) (t : ℝ) : ℝ := aggSupply F (taxPrice C F t)

theorem taxQuantity_pos [Nonempty ι] [Nonempty κ] (C : ι → QLConsumer) (F : κ → QLFirmStrict)
    {t : ℝ} (ht : t ∈ taxRange C F) : 0 < taxQuantity C F t := by
  obtain ⟨j, hj⟩ := exists_eq_minMC F
  exact Finset.sum_pos' (fun k _ => (F k).supply_nonneg _)
    ⟨j, Finset.mem_univ j, ((F j).supply_pos_iff _).2 (hj ▸ (taxPrice_spec C F ht).1)⟩

/-- **Example 10.C.1** (MWG, p. 323): monotone comparative statics. For taxes `t₁ < t₂` in the
admissible range, the producer price strictly falls, the consumer price weakly rises and the
quantity traded falls. -/
theorem example_10_C_1_monotone [Nonempty ι] [Nonempty κ] (C : ι → QLConsumer)
    (F : κ → QLFirmStrict) {t₁ t₂ : ℝ} (h₁ : t₁ ∈ taxRange C F) (h₂ : t₂ ∈ taxRange C F)
    (h₁₂ : t₁ < t₂) :
    taxPrice C F t₂ < taxPrice C F t₁ ∧
      taxPrice C F t₁ + t₁ ≤ taxPrice C F t₂ + t₂ ∧
      taxQuantity C F t₂ < taxQuantity C F t₁ := by
  obtain ⟨a1, b1, e1⟩ := taxPrice_spec C F h₁
  obtain ⟨a2, b2, e2⟩ := taxPrice_spec C F h₂
  have ht1 : -minMC F < t₁ := h₁.1
  have ht2 : -minMC F < t₂ := h₂.1
  set p₁ := taxPrice C F t₁
  set p₂ := taxPrice C F t₂
  have hm := minMC_pos F
  obtain ⟨j, hj⟩ := exists_eq_minMC F
  obtain ⟨i, hi⟩ := exists_eq_maxMB C
  have hp : p₂ < p₁ := by
    by_contra hle
    push Not at hle
    have hs := aggSupply_monotone F hle
    have hd := aggDemand_strictAnti C (by linarith : 0 < p₁ + t₁)
      (by linarith : p₁ + t₁ < p₂ + t₂) ⟨i, by rw [hi]; exact b1⟩
    linarith
  have hs := aggSupply_strictMono F hp ⟨j, by rw [hj]; exact a1⟩
  refine ⟨hp, ?_, hs⟩
  by_contra hlt
  push Not at hlt
  have hd := aggDemand_antitoneOn C (show (0 : ℝ) < p₂ + t₂ by linarith)
    (show (0 : ℝ) < p₁ + t₁ by linarith) hlt.le
  linarith

/-- `τ(p) = P(q(p)) - p`: the tax at which `p` is the producer price; `p*` is its inverse. -/
theorem taxPrice_left_inverse [Nonempty ι] [Nonempty κ] (C : ι → QLConsumer)
    (F : κ → QLFirmStrict) {t : ℝ} (ht : t ∈ taxRange C F) :
    invDemand C (aggSupply F (taxPrice C F t)) - taxPrice C F t = t := by
  obtain ⟨a, b, e⟩ := taxPrice_spec C F ht
  rw [← e, invDemand_aggDemand C (by linarith [ht.1]) b]
  ring

/-- `p*` is continuous on the admissible range. -/
theorem taxPrice_continuousAt [Nonempty ι] [Nonempty κ] (C : ι → QLConsumer)
    (F : κ → QLFirmStrict) {t : ℝ} (ht : t ∈ taxRange C F) :
    ContinuousAt (taxPrice C F) t := by
  have hopen : IsOpen (taxRange C F) := isOpen_Ioo
  refine continuousAt_of_antitoneOn_of_image_mem_nhds
    (fun a ha b hb hab => ?_) (hopen.mem_nhds ht) ?_
  · rcases eq_or_lt_of_le hab with h | h
    · rw [h]
    · exact (example_10_C_1_monotone C F ha hb h).1.le
  · -- for `p` near `p*(t)`, `τ(p)` is admissible and `p*(τ(p)) = p`
    set p₀ := taxPrice C F t
    obtain ⟨a0, b0, e0⟩ := taxPrice_spec C F ht
    have hq0 : 0 < aggSupply F p₀ := taxQuantity_pos C F ht
    have hτ : ContinuousAt (fun p => invDemand C (aggSupply F p) - p) p₀ :=
      ((invDemand_continuousAt C hq0).comp (aggSupply_continuous F).continuousAt).sub
        continuousAt_id
    have hτ0 : (fun p => invDemand C (aggSupply F p) - p) p₀ = t := taxPrice_left_inverse C F ht
    have hev : ∀ᶠ p in 𝓝 p₀, invDemand C (aggSupply F p) - p ∈ taxRange C F :=
      hτ.preimage_mem_nhds (by
        have e : invDemand C (aggSupply F p₀) - p₀ = t := hτ0
        rw [e]; exact hopen.mem_nhds ht)
    obtain ⟨j, hj⟩ := exists_eq_minMC F
    filter_upwards [hev, Ioi_mem_nhds a0] with p hp hpm
    refine ⟨_, hp, taxPrice_unique C F hp ?_ ?_⟩
    · have hqp : 0 ≤ aggSupply F p := aggSupply_nonneg F p
      simp only [add_sub_cancel]
      exact invDemand_pos C hqp
    · have hqp : 0 < aggSupply F p := Finset.sum_pos' (fun k _ => (F k).supply_nonneg _)
        ⟨j, Finset.mem_univ j, ((F j).supply_pos_iff _).2 (hj ▸ hpm)⟩
      simp only [add_sub_cancel]
      exact aggDemand_invDemand C hqp.le

/-- **(10.C.8)** (MWG, p. 323). If aggregate demand has derivative `x' < 0` at `p*(t) + t` and
aggregate supply derivative `q' ≥ 0` at `p*(t)`, then `p*` is differentiable at `t` with
`p*'(t) = -x'/(x' - q')`. -/
theorem eq_10_C_8 [Nonempty ι] [Nonempty κ] (C : ι → QLConsumer) (F : κ → QLFirmStrict)
    {t x' q' : ℝ} (ht : t ∈ taxRange C F)
    (hx : HasDerivAt (aggDemand C) x' (taxPrice C F t + t)) (hx0 : x' < 0)
    (hq : HasDerivAt (aggSupply F) q' (taxPrice C F t)) (hq0 : 0 ≤ q') :
    HasDerivAt (taxPrice C F) (-x' / (x' - q')) t := by
  obtain ⟨a, b, e⟩ := taxPrice_spec C F ht
  set p₀ := taxPrice C F t
  have hq0' : 0 < aggSupply F p₀ := taxQuantity_pos C F ht
  have hP : invDemand C (aggSupply F p₀) = p₀ + t := by
    rw [← e]; exact invDemand_aggDemand C (by linarith [ht.1]) b
  have hPd : HasDerivAt (invDemand C) x'⁻¹ (aggSupply F p₀) :=
    invDemand_hasDerivAt C hq0' (by rw [hP]; exact hx) hx0.ne
  have hτ : HasDerivAt (fun p => invDemand C (aggSupply F p) - p) (x'⁻¹ * q' - 1) p₀ :=
    (hPd.comp p₀ hq).sub (hasDerivAt_id p₀)
  have hτ0 : x'⁻¹ * q' - 1 ≠ 0 := by
    have : x'⁻¹ * q' ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (inv_lt_zero.2 hx0).le hq0
    linarith
  have h := HasDerivAt.of_local_left_inverse (taxPrice_continuousAt C F ht) hτ hτ0
    (by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      exact taxPrice_left_inverse C F hs)
  have e2 : -x' / (x' - q') = (x'⁻¹ * q' - 1)⁻¹ := by
    have h1 : x' ≠ 0 := hx0.ne
    have h2 : x' - q' ≠ 0 := by linarith
    have h3 : x'⁻¹ * q' - 1 = (q' - x') / x' := by field_simp
    rw [h3, inv_div, div_eq_div_iff h2 (by linarith : q' - x' ≠ 0)]
    ring
  rw [e2]
  exact h

/-- **Example 10.C.1** (MWG, p. 323). `-1 ≤ p*'(t) < 0`; `p*'(t) = -1` when `q' = 0`. -/
theorem example_10_C_1_bounds {x' q' : ℝ} (hx0 : x' < 0) (hq0 : 0 ≤ q') :
    -1 ≤ -x' / (x' - q') ∧ -x' / (x' - q') < 0 ∧ (q' = 0 → -x' / (x' - q') = -1) := by
  have hden : x' - q' < 0 := by linarith
  refine ⟨?_, div_neg_of_pos_of_neg (by linarith) hden, fun h => ?_⟩
  · rw [le_div_iff_of_neg hden]
    linarith
  · rw [h, sub_zero, neg_div, div_self hx0.ne]

/-- **(MWG, p. 324)** `p*'(0)` in terms of `φᵢ''` and `cⱼ''`: when every consumer and firm is
active at `t = 0` and every `cⱼ'' > 0`,
`p*'(0) = -∑ᵢ[φᵢ'']⁻¹ / (∑ᵢ[φᵢ'']⁻¹ - ∑ⱼ[cⱼ'']⁻¹)`. -/
theorem example_10_C_1_formula [Nonempty ι] [Nonempty κ] (C : ι → QLConsumer)
    (F : κ → QLFirmStrict) (h0 : (0 : ℝ) ∈ taxRange C F)
    (hxa : ∀ i, taxPrice C F 0 < (C i).dφ 0) (hqa : ∀ j, (F j).dc 0 < taxPrice C F 0)
    (hc2 : ∀ j, 0 < (F j).d2c ((F j).supply (taxPrice C F 0))) :
    HasDerivAt (taxPrice C F)
      (-(∑ i, ((C i).d2φ ((C i).demand (taxPrice C F 0)))⁻¹) /
        (∑ i, ((C i).d2φ ((C i).demand (taxPrice C F 0)))⁻¹ -
          ∑ j, ((F j).d2c ((F j).supply (taxPrice C F 0)))⁻¹)) 0 := by
  set p₀ := taxPrice C F 0
  have hp0 : 0 < p₀ := (minMC_pos F).trans (taxPrice_spec C F h0).1
  have hx : HasDerivAt (aggDemand C) (∑ i, ((C i).d2φ ((C i).demand p₀))⁻¹) (p₀ + 0) := by
    rw [add_zero]
    have := HasDerivAt.fun_sum (u := Finset.univ) fun i _ => (C i).demand_hasDerivAt hp0 (hxa i)
    exact this
  have hq : HasDerivAt (aggSupply F) (∑ j, ((F j).d2c ((F j).supply p₀))⁻¹) p₀ :=
    HasDerivAt.fun_sum (u := Finset.univ) fun j _ => (F j).supply_hasDerivAt (hqa j) (hc2 j)
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hx0 : ∑ i, ((C i).d2φ ((C i).demand p₀))⁻¹ < 0 :=
    Finset.sum_neg (fun k _ => (C k).demand_deriv_neg hp0) Finset.univ_nonempty
  have hq0 : 0 ≤ ∑ j, ((F j).d2c ((F j).supply p₀))⁻¹ :=
    Finset.sum_nonneg fun j _ => (inv_pos.2 (hc2 j)).le
  exact eq_10_C_8 C F h0 hx hx0 hq hq0

/-- **Exercise 10.C.5** (MWG, p. 345). Differentiating the equilibrium system (10.C.4)-(10.C.6)
with `p̂ᵢ = p + t`, `p̂ⱼ = p`: if differentiable paths `xᵢ(t)`, `qⱼ(t)`, `p(t)` satisfy
`φᵢ'(xᵢ(t)) = p(t) + t`, `cⱼ'(qⱼ(t)) = p(t)` and `∑ xᵢ(t) = ∑ qⱼ(t)` near `t₀`, then
`p'(t₀) = -∑[φᵢ'']⁻¹ / (∑[φᵢ'']⁻¹ - ∑[cⱼ'']⁻¹)`. -/
theorem exercise_10_C_5 [Nonempty ι] (dφ d2φ : ι → ℝ → ℝ) (dc d2c : κ → ℝ → ℝ)
    (x : ι → ℝ → ℝ) (q : κ → ℝ → ℝ) (p : ℝ → ℝ) {t₀ p' : ℝ} (x' : ι → ℝ) (q' : κ → ℝ)
    (hdφ : ∀ i, HasDerivAt (dφ i) (d2φ i (x i t₀)) (x i t₀))
    (hdc : ∀ j, HasDerivAt (dc j) (d2c j (q j t₀)) (q j t₀))
    (hneg : ∀ i, d2φ i (x i t₀) < 0) (hpos : ∀ j, 0 < d2c j (q j t₀))
    (hx : ∀ i, HasDerivAt (x i) (x' i) t₀) (hq : ∀ j, HasDerivAt (q j) (q' j) t₀)
    (hp : HasDerivAt p p' t₀)
    (e4 : ∀ᶠ t in 𝓝 t₀, ∀ i, dφ i (x i t) = p t + t)
    (e5 : ∀ᶠ t in 𝓝 t₀, ∀ j, dc j (q j t) = p t)
    (e6 : ∀ᶠ t in 𝓝 t₀, ∑ i, x i t = ∑ j, q j t) :
    p' = -(∑ i, (d2φ i (x i t₀))⁻¹) / (∑ i, (d2φ i (x i t₀))⁻¹ - ∑ j, (d2c j (q j t₀))⁻¹) := by
  have hxi : ∀ i, x' i = (p' + 1) / d2φ i (x i t₀) := by
    intro i
    have h1 := (hdφ i).comp t₀ (hx i)
    have h2 : HasDerivAt (fun t => p t + t) (p' + 1) t₀ := hp.add (hasDerivAt_id t₀)
    have h3 := h1.congr_of_eventuallyEq (by filter_upwards [e4] with t ht; exact (ht i).symm)
    have := h3.unique h2
    rw [eq_div_iff (hneg i).ne]
    linarith
  have hqj : ∀ j, q' j = p' / d2c j (q j t₀) := by
    intro j
    have h1 := (hdc j).comp t₀ (hq j)
    have h3 := h1.congr_of_eventuallyEq (by filter_upwards [e5] with t ht; exact (ht j).symm)
    have := h3.unique hp
    rw [eq_div_iff (hpos j).ne']
    linarith
  have hsum : ∑ i, x' i = ∑ j, q' j := by
    have h1 := HasDerivAt.fun_sum (u := Finset.univ) fun i _ => hx i
    have h2 := HasDerivAt.fun_sum (u := Finset.univ) fun j _ => hq j
    exact (h1.congr_of_eventuallyEq (by filter_upwards [e6] with t ht; exact ht.symm)).unique h2
  simp only [hxi, hqj, div_eq_mul_inv, ← Finset.mul_sum] at hsum
  have hA : ∑ i, (d2φ i (x i t₀))⁻¹ < 0 :=
    Finset.sum_neg (fun i _ => inv_lt_zero.2 (hneg i)) Finset.univ_nonempty
  have hB : 0 ≤ ∑ j, (d2c j (q j t₀))⁻¹ := Finset.sum_nonneg fun j _ => (inv_pos.2 (hpos j)).le
  have hden : ∑ i, (d2φ i (x i t₀))⁻¹ - ∑ j, (d2c j (q j t₀))⁻¹ ≠ 0 := by linarith
  rw [eq_div_iff hden]
  linarith

/-! ## Example 10.E.1: welfare effects of the tax -/

/-- **Example 10.E.1** (MWG, p. 332), (10.E.6). For a tax `t > 0` in the admissible range,
aggregate surplus falls: `S*(t) - S*(0) = ∫_{x*(0)}^{x*(t)} [P - C'] < 0`. -/
theorem example_10_E_1 [Nonempty ι] [Nonempty κ] (C : ι → QLConsumer) (F : κ → QLFirmStrict)
    {t : ℝ} (h0 : (0 : ℝ) ∈ taxRange C F) (ht : t ∈ taxRange C F) (htpos : 0 < t) :
    aggSurplus C F (taxQuantity C F t) - aggSurplus C F (taxQuantity C F 0) =
        ∫ s in taxQuantity C F 0..taxQuantity C F t, (invDemand C s - invSupply F s) ∧
      aggSurplus C F (taxQuantity C F t) - aggSurplus C F (taxQuantity C F 0) < 0 := by
  have hlt := (example_10_C_1_monotone C F h0 ht htpos).2.2
  obtain ⟨a, b, e⟩ := taxPrice_spec C F h0
  have hX0 := taxQuantity_pos C F h0
  rw [add_zero] at b e
  have heq : invDemand C (taxQuantity C F 0) = invSupply F (taxQuantity C F 0) := by
    unfold taxQuantity
    rw [invSupply_aggSupply F a, ← e, invDemand_aggDemand C ((minMC_pos F).trans a) b]
  exact deadweight_loss_neg C F (taxQuantity_pos C F ht).le hlt heq

/-- **Example 10.E.1** (MWG, pp. 332-333). Aggregate surplus at the taxed equilibrium splits
into consumer surplus at the consumer price, producer surplus at the producer price, and tax
revenue `t x*(t)`. -/
theorem example_10_E_1_decomposition [Nonempty ι] [Nonempty κ] (C : ι → QLConsumer)
    (F : κ → QLFirmStrict) {t : ℝ} (ht : t ∈ taxRange C F) :
    aggSurplus C F (taxQuantity C F t) =
      consumerSurplus C (taxPrice C F t + t) + producerSurplus F (taxPrice C F t) +
        t * taxQuantity C F t := by
  obtain ⟨a, b, e⟩ := taxPrice_spec C F ht
  set p := taxPrice C F t
  have hp : 0 < p := (minMC_pos F).trans a
  have hpt : 0 < p + t := by linarith [ht.1]
  have hγ : grossBenefit C (taxQuantity C F t) = ∑ i, (C i).φ ((C i).demand (p + t)) := by
    have := grossBenefit_eq_of_foc (x := fun i => (C i).demand (p + t))
      fun i => (C i).demand_spec hpt
    unfold taxQuantity
    rw [← e]
    exact this
  have hC : minCost (fun j => (F j).toQLFirm) (taxQuantity C F t) =
      ∑ j, (F j).c ((F j).supply p) :=
    minCost_eq_of_foc (F := fun j => (F j).toQLFirm) hp.le fun j => (F j).supply_foc p
  rw [aggSurplus, hγ, hC, consumerSurplus, producerSurplus, e]
  unfold taxQuantity
  ring

/-- **(MWG, p. 332)** `S*'(0) = 0`: the first-order welfare effect of a small tax is zero, when
`p*` is differentiable at `0` and supply is differentiable at `p*(0)`. -/
theorem example_10_E_1_first_order [Nonempty ι] [Nonempty κ] (C : ι → QLConsumer)
    (F : κ → QLFirmStrict) (h0 : (0 : ℝ) ∈ taxRange C F) {d q' : ℝ}
    (hp : HasDerivAt (taxPrice C F) d 0) (hq : HasDerivAt (aggSupply F) q' (taxPrice C F 0)) :
    HasDerivAt (fun t => aggSurplus C F (taxQuantity C F t)) 0 0 := by
  obtain ⟨a, b, e⟩ := taxPrice_spec C F h0
  have hX0 := taxQuantity_pos C F h0
  have hS := aggSurplus_hasDerivAt C F hX0
  have hx : HasDerivAt (taxQuantity C F) (q' * d) 0 := hq.comp 0 hp
  rw [add_zero] at b e
  have heq : invDemand C (taxQuantity C F 0) = invSupply F (taxQuantity C F 0) := by
    unfold taxQuantity
    rw [invSupply_aggSupply F a, ← e, invDemand_aggDemand C ((minMC_pos F).trans a) b]
  have := hS.comp 0 hx
  rw [heq, sub_self, zero_mul] at this
  exact this

/-! ## Exercise 10.C.6: who pays the tax -/

/-- **Exercise 10.C.6(a)** (MWG, p. 345). With a specific tax `t`, the equilibrium consumer cost
and quantity are the same whether consumers pay (`D(p + t) = S(p)`, cost `p + t`) or producers
pay (`D(p') = S(p' - t)`, cost `p'`). -/
theorem exercise_10_C_6a (D S : ℝ → ℝ) (t c Q : ℝ) :
    (∃ p, D (p + t) = S p ∧ c = p + t ∧ Q = D (p + t)) ↔
      (∃ p', D p' = S (p' - t) ∧ c = p' ∧ Q = D p') := by
  constructor
  · rintro ⟨p, h1, h2, h3⟩
    exact ⟨p + t, by rw [h1, add_sub_cancel_right], h2, h3⟩
  · rintro ⟨p', h1, h2, h3⟩
    exact ⟨p' - t, by rw [sub_add_cancel, h1], by rw [h2]; ring, by rw [h3, sub_add_cancel]⟩

/-- **Exercise 10.C.6(b)** (MWG, p. 345). With an ad valorem tax `τ ∈ (0, 1)`: if consumers pay
(`D(p(1 + τ)) = S(p)`, consumer cost `c₁ = p(1 + τ)`) and if producers pay (the government
takes `τ` times the amount the seller receives: `D(p') = S(p'(1 - τ))`, consumer cost `c₂ = p'`),
then with `D` nonincreasing and `S` strictly increasing on positive prices, `c₁ < c₂`:
collecting from producers leads to a higher cost to consumers. -/
theorem exercise_10_C_6b (D S : ℝ → ℝ) (hD : AntitoneOn D (Set.Ioi 0))
    (hS : StrictMonoOn S (Set.Ioi 0)) {τ p p' : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) (hp : 0 < p)
    (hp' : 0 < p') (h₁ : D (p * (1 + τ)) = S p) (h₂ : D p' = S (p' * (1 - τ))) :
    p * (1 + τ) < p' := by
  by_contra hle
  push Not at hle
  have hs : p' * (1 - τ) < p := by
    have : p' * (1 - τ) ≤ p * (1 + τ) * (1 - τ) := mul_le_mul_of_nonneg_right hle (by linarith)
    nlinarith [mul_pos hp (mul_pos hτ0 hτ0)]
  have h1 := hS (Set.mem_Ioi.2 (by nlinarith)) (Set.mem_Ioi.2 hp) hs
  have h2 := hD (Set.mem_Ioi.2 hp') (Set.mem_Ioi.2 (by positivity)) hle
  linarith

/-- **Exercise 10.C.6(b)**, special case (MWG, p. 345). With perfectly inelastic supply
(`S` constant) and strictly decreasing demand, the collection method is irrelevant. -/
theorem exercise_10_C_6b_inelastic (D : ℝ → ℝ) (hD : StrictAntiOn D (Set.Ioi 0)) (s₀ : ℝ)
    {τ p p' : ℝ} (hτ0 : 0 < τ) (hp : 0 < p) (hp' : 0 < p') (h₁ : D (p * (1 + τ)) = s₀)
    (h₂ : D p' = s₀) : p * (1 + τ) = p' :=
  hD.injOn (Set.mem_Ioi.2 (by positivity)) (Set.mem_Ioi.2 hp') (h₁.trans h₂.symm)

/-- **Exercise 10.C.6(b)**: a producer-collected ad valorem rate `τ` is equivalent to the
consumer-collected rate `τ/(1 - τ)`. -/
theorem exercise_10_C_6b_equivalent (D S : ℝ → ℝ) {τ p' : ℝ} (hτ1 : τ < 1) :
    D p' = S (p' * (1 - τ)) ↔
      D (p' * (1 - τ) * (1 + τ / (1 - τ))) = S (p' * (1 - τ)) := by
  have h : p' * (1 - τ) * (1 + τ / (1 - τ)) = p' := by
    field_simp [show (1 - τ) ≠ 0 by linarith]
    ring
  rw [h]

/-! ## Exercise 10.C.7: constant elasticities -/

/-- **Exercise 10.C.7** (MWG, p. 345). With `x(p) = Ap^ε` (`A > 0`, `ε < 0`), `q(p) = αp^γ`
(`α > 0`, `γ ≥ 0`) and an ad valorem tax `κ = 1 + τ` on consumers, the equilibrium producer
price is `p*(κ) = (A/α)^{1/(γ-ε)} κ^{ε/(γ-ε)}`: it solves `A(κp)^ε = αp^γ`, and is the only
positive solution. -/
theorem exercise_10_C_7_price {A ε α γ κ : ℝ} (hA : 0 < A) (hε : ε < 0) (hα : 0 < α)
    (hγ : 0 ≤ γ) (hκ : 0 < κ) {p : ℝ} (hp : 0 < p) :
    A * (κ * p) ^ ε = α * p ^ γ ↔
      p = (A / α) ^ (1 / (γ - ε)) * κ ^ (ε / (γ - ε)) := by
  have hd : 0 < γ - ε := by linarith
  have key : A * (κ * p) ^ ε = α * p ^ γ ↔ p ^ (γ - ε) = A / α * κ ^ ε := by
    rw [Real.mul_rpow hκ.le hp.le, Real.rpow_sub hp]
    constructor
    · intro h
      field_simp
      have h1 : 0 < p ^ ε := Real.rpow_pos_of_pos hp ε
      nlinarith [h]
    · intro h
      have h1 : 0 < p ^ ε := Real.rpow_pos_of_pos hp ε
      field_simp at h
      nlinarith [h]
  rw [key]
  have hrhs : 0 < A / α * κ ^ ε := mul_pos (div_pos hA hα) (Real.rpow_pos_of_pos hκ ε)
  constructor
  · intro h
    have := congrArg (fun z => z ^ (1 / (γ - ε))) h
    rw [← Real.rpow_mul hp.le, mul_one_div_cancel hd.ne', Real.rpow_one,
      Real.mul_rpow (div_pos hA hα).le (Real.rpow_pos_of_pos hκ ε).le,
      ← Real.rpow_mul hκ.le] at this
    rw [this]
    congr 2
    ring
  · intro h
    rw [h, Real.mul_rpow (Real.rpow_pos_of_pos (div_pos hA hα) _).le
      (Real.rpow_pos_of_pos hκ _).le, ← Real.rpow_mul (div_pos hA hα).le,
      ← Real.rpow_mul hκ.le]
    rw [one_div_mul_cancel hd.ne', Real.rpow_one]
    congr 2
    field_simp

/-- **Exercise 10.C.7** (MWG, p. 345). The elasticity of `p*` with respect to `κ` is
`ε/(γ - ε)`: `κ p*'(κ)/p*(κ) = ε/(γ - ε)`; that of the consumer cost `κp*` is `γ/(γ - ε)`. -/
theorem exercise_10_C_7_elasticity {A ε α γ κ : ℝ} (hA : 0 < A) (hε : ε < 0) (hα : 0 < α)
    (hγ : 0 ≤ γ) (hκ : 0 < κ) :
    let pstar : ℝ → ℝ := fun k => (A / α) ^ (1 / (γ - ε)) * k ^ (ε / (γ - ε))
    HasDerivAt pstar ((A / α) ^ (1 / (γ - ε)) * (ε / (γ - ε) * κ ^ (ε / (γ - ε) - 1))) κ ∧
      κ * ((A / α) ^ (1 / (γ - ε)) * (ε / (γ - ε) * κ ^ (ε / (γ - ε) - 1))) / pstar κ =
        ε / (γ - ε) ∧
      ε / (γ - ε) + 1 = γ / (γ - ε) := by
  intro pstar
  have hd : 0 < γ - ε := by linarith
  have hK : 0 < (A / α) ^ (1 / (γ - ε)) := Real.rpow_pos_of_pos (div_pos hA hα) _
  refine ⟨(Real.hasDerivAt_rpow_const (Or.inl hκ.ne')).const_mul _, ?_, ?_⟩
  · simp only [pstar]
    rw [Real.rpow_sub hκ, Real.rpow_one]
    have : 0 < κ ^ (ε / (γ - ε)) := Real.rpow_pos_of_pos hκ _
    field_simp
  · field_simp
    ring

/-- **Exercise 10.C.7** (MWG, p. 345): the polar cases and limits. With `γ = 0` (perfectly
inelastic supply) the producer price falls one-for-one (`ε/(γ - ε) = -1`) and the consumer cost
is unaffected; with `ε = 0` the producer price is unaffected and consumers bear the whole tax;
as `ε → -∞` the elasticity tends to `-1` (producers bear the tax) and as `γ → ∞` it tends to
`0` (consumers bear it). -/
theorem exercise_10_C_7_limits {ε γ : ℝ} (hε : ε < 0) :
    ε / (0 - ε) = -1 ∧ 0 / (γ - 0) = (0 : ℝ) ∧
      Tendsto (fun e : ℝ => e / (γ - e)) atBot (𝓝 (-1)) ∧
      Tendsto (fun g : ℝ => ε / (g - ε)) atTop (𝓝 0) := by
  refine ⟨by rw [zero_sub, div_neg, div_self hε.ne], by simp, ?_, ?_⟩
  · have h1 : Tendsto (fun e : ℝ => -1 + γ / (γ - e)) atBot (𝓝 (-1 + 0)) := by
      refine tendsto_const_nhds.add (Tendsto.div_atTop tendsto_const_nhds ?_)
      exact tendsto_atTop_add_const_left _ γ (tendsto_neg_atBot_atTop)
    rw [add_zero] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_lt_atBot (γ)] with e he
    field_simp [show γ - e ≠ 0 by linarith]
    ring
  · exact Tendsto.div_atTop tendsto_const_nhds (tendsto_atTop_add_const_right _ (-ε) tendsto_id
      |>.congr fun g => by simp only [id]; ring)

/-- A concrete instance of Example 10.C.1: one consumer `φ(x) = 2(1 - e^{-x})` and one firm
`c(q) = q + q²/2`. The tax-price function is differentiable at `0` with `-1 ≤ p*'(0) < 0`
(non-vacuity of `example_10_C_1_formula`). -/
theorem example_10_C_1_instance :
    ∃ d, HasDerivAt (taxPrice (fun _ : Fin 1 => expConsumer 2 two_pos)
      (fun _ : Fin 1 => quadFirm 1 1 one_pos one_pos)) d 0 ∧ -1 ≤ d ∧ d < 0 := by
  set C := fun _ : Fin 1 => expConsumer 2 two_pos
  set F := fun _ : Fin 1 => quadFirm 1 1 one_pos one_pos
  have hM : maxMB C = 2 := by
    simp [maxMB, C, expConsumer, Finset.sup'_const]
  have hm : minMC F = 1 := by
    simp [minMC, F, quadFirm, quadFirmBase, QLFirmStrict.dc, Finset.inf'_const]
  have h0 : (0 : ℝ) ∈ taxRange C F := by
    simp only [taxRange, hM, hm, Set.mem_Ioo]; norm_num
  obtain ⟨a, b, -⟩ := taxPrice_spec C F h0
  rw [hm] at a
  rw [hM, add_zero] at b
  have hd : ∀ i, (C i).dφ 0 = 2 := fun _ => by simp [C, expConsumer]
  have hdc : ∀ j, (F j).dc 0 = 1 := fun _ => by
    simp [F, quadFirm, quadFirmBase, QLFirmStrict.dc]
  have h := example_10_C_1_formula C F h0
    (fun i => by rw [hd i]; exact b)
    (fun j => by rw [hdc j]; exact a)
    (fun _ => by simp [F, quadFirm, quadFirmBase, QLFirmStrict.d2c])
  refine ⟨_, h, ?_⟩
  have hx0 : ∑ i, ((C i).d2φ ((C i).demand (taxPrice C F 0)))⁻¹ < 0 :=
    Finset.sum_neg (fun k _ => (C k).demand_deriv_neg ((minMC_pos F).trans
      (by rw [hm]; exact a))) Finset.univ_nonempty
  have hq0 : 0 ≤ ∑ j, ((F j).d2c ((F j).supply (taxPrice C F 0)))⁻¹ :=
    Finset.sum_nonneg fun j _ => by simp [F, quadFirm, quadFirmBase, QLFirmStrict.d2c]
  exact ⟨(example_10_C_1_bounds hx0 hq0).1, (example_10_C_1_bounds hx0 hq0).2.1⟩

end MWG.CompetitiveMarkets

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Free entry and long-run competitive equilibria (MWG Section 10.F, pp. 334-341)

* **Definition 10.F.1**: a long-run competitive equilibrium `(p*, q*, J*)` for an aggregate
  demand `x(·)` and an individual cost `c(·)` with `c(0) = 0` (`IsLREqm`; `IsLREqmReal` ignores
  the integer constraint). The long-run supply correspondence (p. 335): `PosProfit` (`Q(p) = ∞`)
  and `InLRSupply`; footnote 27: `(p*, q*, J*)` is an equilibrium iff `x(p*) ∈ Q(p*)`.
* Constant returns (p. 336, Figure 10.F.1): `p* = c`, `J*` and `q*` indeterminate.
* Strictly convex costs: **Exercise 10.F.1** (`π(p) > 0` iff `p > c'(0)`), nonexistence of a
  long-run equilibrium (Figure 10.F.2), Figure 10.F.3 (industry marginal cost `c'(Q/J)` approaches
  but never reaches `c'(0)`), and the nonclosed long-run technology (Exercise 5.B.4 from
  Chapter 5).
* A unique efficient scale `q̄` (pp. 337-338, Figure 10.F.4): `p* = c̄`, `q* = q̄`,
  `J* = x(c̄)/q̄`; the integer problem; footnote 28 (`c'(q*) = p* = c(q*)/q*`); footnote 29 (a
  range of efficient scales); footnote 25 (uniqueness of the positive output).
* p. 339: the long-run equilibrium maximizes Marshallian aggregate surplus over all aggregate
  outputs and numbers of firms (first welfare theorem without convexity).
* Example 10.F.1 (pp. 340-341): short-run versus long-run comparative statics with fixed costs
  that are sunk in the short run.
-/

namespace MWG.CompetitiveMarkets

open Filter Topology

/-- `q ≥ 0` maximizes profit `pq - c(q)` on `q ≥ 0`. -/
def IsProfitMax (c : ℝ → ℝ) (p q : ℝ) : Prop :=
  0 ≤ q ∧ ∀ q', 0 ≤ q' → p * q' - c q' ≤ p * q - c q

/-- **Definition 10.F.1** (MWG, p. 335). `(p*, q*, J*)` is a long-run competitive equilibrium
for demand `x` and individual cost `c` (with `c(0) = 0`): (i) profit maximization,
(ii) `x(p*) = J* q*`, (iii) zero profit (free entry). -/
def IsLREqm (x c : ℝ → ℝ) (p q : ℝ) (J : ℕ) : Prop :=
  IsProfitMax c p q ∧ x p = J * q ∧ p * q - c q = 0

/-- **Definition 10.F.1** (MWG, p. 335), unfolded. -/
theorem definition_10_F_1 (x c : ℝ → ℝ) (p q : ℝ) (J : ℕ) :
    IsLREqm x c p q J ↔ (0 ≤ q ∧ ∀ q', 0 ≤ q' → p * q' - c q' ≤ p * q - c q) ∧
      x p = J * q ∧ p * q - c q = 0 := Iff.rfl

/-- Definition 10.F.1 ignoring the integer constraint on the number of firms (used in
Exercises 10.F.2-10.F.4). -/
def IsLREqmReal (x c : ℝ → ℝ) (p q J : ℝ) : Prop :=
  0 ≤ J ∧ IsProfitMax c p q ∧ x p = J * q ∧ p * q - c q = 0

/-- `π(p) > 0`: some output earns positive profit (`Q(p) = ∞`, p. 335). -/
def PosProfit (c : ℝ → ℝ) (p : ℝ) : Prop := ∃ q, 0 ≤ q ∧ 0 < p * q - c q

/-- **(MWG, p. 335)** `Q ∈ Q(p)` for the long-run aggregate supply correspondence when
`π(p) = 0`: `Q = Jq` for an integer `J ≥ 0` and a profit-maximizing `q`. -/
def InLRSupply (c : ℝ → ℝ) (p Q : ℝ) : Prop :=
  ¬ PosProfit c p ∧ ∃ (J : ℕ) (q : ℝ), IsProfitMax c p q ∧ Q = J * q

/-- **Footnote 27** (MWG, p. 336). With `c(0) = 0`, `p*` is a long-run equilibrium price iff
`x(p*) ∈ Q(p*)`. -/
theorem footnote_10_F_27 {x c : ℝ → ℝ} (hc0 : c 0 = 0) (p : ℝ) :
    (∃ q J, IsLREqm x c p q J) ↔ InLRSupply c p (x p) := by
  constructor
  · rintro ⟨q, J, hmax, hx, hz⟩
    refine ⟨fun ⟨q', hq', hpos⟩ => ?_, J, q, hmax, hx⟩
    have := hmax.2 q' hq'
    linarith
  · rintro ⟨hno, J, q, hmax, hx⟩
    refine ⟨q, J, hmax, hx, le_antisymm ?_ ?_⟩
    · by_contra hlt; push Not at hlt; exact hno ⟨q, hmax.1, hlt⟩
    · have := hmax.2 0 le_rfl
      rw [hc0] at this
      linarith

/-- **(MWG, p. 335)** If `π(p) > 0`, entry makes aggregate supply unbounded: for every `M` some
number of firms, each earning positive profit, supply more than `M`. -/
theorem posProfit_unbounded {c : ℝ → ℝ} (hc0 : c 0 = 0) {p : ℝ} (h : PosProfit c p) (M : ℝ) :
    ∃ (J : ℕ) (q : ℝ), 0 < q ∧ 0 < p * q - c q ∧ M < J * q := by
  obtain ⟨q, hq, hpos⟩ := h
  have hq0 : 0 < q := by
    rcases eq_or_lt_of_le hq with h0 | h0
    · rw [← h0, hc0] at hpos; simp at hpos
    · exact h0
  obtain ⟨J, hJ⟩ := exists_nat_gt (M / q)
  exact ⟨J, q, hq0, hpos, by rwa [div_lt_iff₀ hq0] at hJ⟩

/-! ## Constant returns to scale (Figure 10.F.1) -/

/-- **(MWG, p. 336)** With `c(q) = cq` (`c > 0`) and `x(c) > 0` (demand nonincreasing below `c`),
`(p*, q*, J*)` is a long-run equilibrium iff `p* = c`, `q* ≥ 0` and `J* q* = x(c)`. -/
theorem lr_crs {x : ℝ → ℝ} {c : ℝ} (hxc : 0 < x c) (hmono : AntitoneOn x (Set.Iic c))
    {p q : ℝ} {J : ℕ} :
    IsLREqm x (fun q => c * q) p q J ↔ p = c ∧ 0 ≤ q ∧ (J : ℝ) * q = x c := by
  constructor
  · rintro ⟨⟨hq, hmax⟩, hx, hz⟩
    have hpc : p ≤ c := by
      by_contra hlt
      push Not at hlt
      have := hmax (q + 1) (by linarith)
      nlinarith
    have hxp : 0 < x p := hxc.trans_le (hmono (Set.mem_Iic.2 hpc) (Set.mem_Iic.2 le_rfl) hpc)
    have hq0 : 0 < q := by
      rw [hx] at hxp
      exact pos_of_mul_pos_right hxp (Nat.cast_nonneg J)
    have hpeq : p = c := by
      have : (p - c) * q = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · linarith
      · exact absurd h hq0.ne'
    subst hpeq
    exact ⟨rfl, hq, hx.symm⟩
  · rintro ⟨rfl, hq, hJ⟩
    exact ⟨⟨hq, fun q' _ => by ring_nf; exact le_rfl⟩, hJ.symm, by ring⟩

/-- **(MWG, p. 336)** With constant returns, `J*` and `q*` are indeterminate: `(c, x(c), 1)` and
`(c, x(c)/2, 2)` are both long-run equilibria. -/
theorem lr_crs_indeterminate {x : ℝ → ℝ} {c : ℝ} (hxc : 0 < x c)
    (hmono : AntitoneOn x (Set.Iic c)) :
    IsLREqm x (fun q => c * q) c (x c) 1 ∧ IsLREqm x (fun q => c * q) c (x c / 2) 2 ∧
      x c ≠ x c / 2 := by
  refine ⟨(lr_crs hxc hmono).2 ⟨rfl, hxc.le, by simp⟩,
    (lr_crs hxc hmono).2 ⟨rfl, by positivity, by push_cast; ring⟩, by linarith⟩

/-- **(MWG, p. 336)** The long-run supply correspondence with constant returns:
`Q(c) = [0, ∞)`, `Q(p) = {0}` for `p < c`, `Q(p) = ∞` for `p > c`. -/
theorem lrSupply_crs (c : ℝ) :
    (∀ Q, InLRSupply (fun q => c * q) c Q ↔ 0 ≤ Q) ∧
    (∀ p, 0 < p → p < c → ∀ Q, InLRSupply (fun q => c * q) p Q ↔ Q = 0) ∧
    (∀ p, c < p → PosProfit (fun q => c * q) p) := by
  refine ⟨fun Q => ⟨?_, fun hQ => ?_⟩, fun p _ hpc Q => ⟨?_, ?_⟩, fun p hcp => ⟨1, zero_le_one,
    by linarith⟩⟩
  · rintro ⟨-, J, q, ⟨hq, -⟩, rfl⟩
    exact mul_nonneg (Nat.cast_nonneg J) hq
  · refine ⟨fun ⟨q, _, hpos⟩ => by linarith, 1, Q, ⟨hQ, fun q' _ => by linarith⟩, by simp⟩
  · rintro ⟨-, J, q, ⟨hq, hmax⟩, rfl⟩
    have := hmax 0 le_rfl
    have hq0 : q = 0 := by
      by_contra hne
      have hq' : 0 < q := lt_of_le_of_ne hq (Ne.symm hne)
      nlinarith
    rw [hq0, mul_zero]
  · rintro rfl
    refine ⟨fun ⟨q, hq, hpos⟩ => by nlinarith, 0, 0, ⟨le_rfl, fun q' hq' => by nlinarith⟩,
      by simp⟩

/-! ## Strictly convex costs -/

/-- **Exercise 10.F.1** (MWG, p. 347). If `c` is strictly convex on `q ≥ 0`, differentiable there
(one-sided at `0`) and `c(0) = 0`, then `π(p) > 0` iff `p > c'(0)`. -/
theorem exercise_10_F_1 {c dc : ℝ → ℝ} (hc0 : c 0 = 0)
    (hd : ∀ q ∈ Set.Ici (0 : ℝ), HasDerivWithinAt c (dc q) (Set.Ici 0) q)
    (hconv : StrictConvexOn ℝ (Set.Ici 0) c) (p : ℝ) : PosProfit c p ↔ dc 0 < p := by
  constructor
  · rintro ⟨q, hq, hpos⟩
    by_contra hle
    push Not at hle
    rcases eq_or_lt_of_le hq with h0 | hq0
    · rw [← h0, hc0] at hpos; simp at hpos
    · have h := hconv.lt_slope_of_hasDerivWithinAt (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hq)
        hq0 (hd 0 (Set.mem_Ici.2 le_rfl))
      rw [slope_def_field, hc0, sub_zero, sub_zero, lt_div_iff₀ hq0] at h
      nlinarith
  · intro hlt
    have hg : HasDerivWithinAt (fun q => p * q - c q) (p - dc 0) (Set.Ioi 0) 0 := by
      have h := ((hasDerivWithinAt_id (0 : ℝ) (Set.Ici 0)).const_mul p).sub
        (hd 0 (Set.mem_Ici.2 le_rfl))
      rw [mul_one] at h
      exact h.mono Set.Ioi_subset_Ici_self
    obtain ⟨q, -, hq, hgt⟩ := foc_exists_gt_of_deriv_pos hg (by linarith) Set.univ Filter.univ_mem
    refine ⟨q, hq.le, ?_⟩
    simp only [mul_zero, hc0, sub_zero] at hgt
    exact hgt

/-- **(MWG, pp. 336-337, Figure 10.F.2)** With strictly convex costs, `c(0) = 0` and
`x(c'(0)) > 0`, no long-run competitive equilibrium exists. -/
theorem lr_strictConvex_nonexistence {x c dc : ℝ → ℝ} (hc0 : c 0 = 0)
    (hd : ∀ q ∈ Set.Ici (0 : ℝ), HasDerivWithinAt c (dc q) (Set.Ici 0) q)
    (hconv : StrictConvexOn ℝ (Set.Ici 0) c) (hx : 0 < x (dc 0))
    (hmono : AntitoneOn x (Set.Iic (dc 0))) : ¬ ∃ p q J, IsLREqm x c p q J := by
  rintro ⟨p, q, J, ⟨hq, hmax⟩, hxp, hz⟩
  by_cases hp : dc 0 < p
  · obtain ⟨q', hq', hpos⟩ := (exercise_10_F_1 hc0 hd hconv p).2 hp
    have := hmax q' hq'
    linarith
  · push Not at hp
    have hnpos := (exercise_10_F_1 hc0 hd hconv p).not.2 (not_lt.2 hp)
    have hq0 : q = 0 := by
      by_contra hne
      have hq' : 0 < q := lt_of_le_of_ne hq (Ne.symm hne)
      -- positive output earns negative profit
      have h := hconv.lt_slope_of_hasDerivWithinAt (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hq)
        hq' (hd 0 (Set.mem_Ici.2 le_rfl))
      rw [slope_def_field, hc0, sub_zero, sub_zero, lt_div_iff₀ hq'] at h
      nlinarith
    rw [hq0, mul_zero] at hxp
    have := hmono (Set.mem_Iic.2 hp) (Set.mem_Iic.2 le_rfl) hp
    linarith

/-- **(MWG, p. 337)** The long-run supply correspondence with strictly convex costs:
`Q(p) = ∞` for `p > c'(0)` and `Q(p) = {0}` for `p ≤ c'(0)`. -/
theorem lrSupply_strictConvex {c dc : ℝ → ℝ} (hc0 : c 0 = 0)
    (hd : ∀ q ∈ Set.Ici (0 : ℝ), HasDerivWithinAt c (dc q) (Set.Ici 0) q)
    (hconv : StrictConvexOn ℝ (Set.Ici 0) c) (p : ℝ) :
    (dc 0 < p → PosProfit c p) ∧ (p ≤ dc 0 → ∀ Q, InLRSupply c p Q ↔ Q = 0) := by
  refine ⟨(exercise_10_F_1 hc0 hd hconv p).2, fun hp Q => ⟨?_, ?_⟩⟩
  · rintro ⟨-, J, q, ⟨hq, hmax⟩, rfl⟩
    have hq0 : q = 0 := by
      by_contra hne
      have hq' : 0 < q := lt_of_le_of_ne hq (Ne.symm hne)
      have h := hconv.lt_slope_of_hasDerivWithinAt (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hq)
        hq' (hd 0 (Set.mem_Ici.2 le_rfl))
      rw [slope_def_field, hc0, sub_zero, sub_zero, lt_div_iff₀ hq'] at h
      have := hmax 0 le_rfl
      rw [hc0] at this
      nlinarith
    rw [hq0, mul_zero]
  · rintro rfl
    refine ⟨(exercise_10_F_1 hc0 hd hconv p).not.2 (not_lt.2 hp), 0, 0, ⟨le_rfl, fun q' hq' => ?_⟩,
      by simp⟩
    rw [hc0]
    rcases eq_or_lt_of_le hq' with h0 | hq0
    · rw [← h0, hc0]
    · have h := hconv.lt_slope_of_hasDerivWithinAt (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hq')
        hq0 (hd 0 (Set.mem_Ici.2 le_rfl))
      rw [slope_def_field, hc0, sub_zero, sub_zero, lt_div_iff₀ hq0] at h
      nlinarith

/-- **Figure 10.F.3** (MWG, p. 337). With strictly convex costs the industry marginal cost with
`J` firms, `c'(Q/J)`, exceeds `c'(0)` for every `J` (at `Q > 0`) but tends to `c'(0)` as
`J → ∞`. -/
theorem figure_10_F_3 {dc : ℝ → ℝ} (hmono : StrictMonoOn dc (Set.Ici 0))
    (hcont : ContinuousWithinAt dc (Set.Ici 0) 0) {Q : ℝ} (hQ : 0 < Q) :
    (∀ J : ℕ, 0 < J → dc 0 < dc (Q / J)) ∧
      Tendsto (fun J : ℕ => dc (Q / J)) atTop (𝓝 (dc 0)) := by
  refine ⟨fun J hJ => hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 (by positivity))
    (by positivity), ?_⟩
  have h1 : Tendsto (fun J : ℕ => Q / (J : ℝ)) atTop (𝓝[Set.Ici 0] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun J => ?_⟩
    · exact tendsto_const_div_atTop_nhds_zero_nat Q
    · exact Set.mem_Ici.2 (by positivity)
  exact hcont.tendsto.comp h1

/-- **(MWG, p. 337; Exercise 5.B.4)** The long-run aggregate technology generated by a
strictly convex technology need not be closed: for `{y₁ ≤ 0, y₂ ≤ √(-y₁)}` (cost `c(q) = q²`
with free disposal) the additive closure `Y⁺` is not closed (Chapter 5). -/
theorem lr_technology_not_closed : ¬ IsClosed (MWG.Production.addClosure MWG.Production.sqrtTech) :=
  MWG.Production.exercise_5_B_4_not_closed.2.2.2.2

/-! ## Efficient scale (Figure 10.F.4) -/

/-- `q̄ > 0` is an efficient scale: it minimizes average cost `c(q)/q` over `q > 0`. -/
def IsEfficientScale (c : ℝ → ℝ) (qb : ℝ) : Prop :=
  0 < qb ∧ ∀ q, 0 < q → c qb / qb ≤ c q / q

/-- At an efficient scale `q̄` with minimized average cost `c̄`, `c(q) ≥ c̄ q` for all `q ≥ 0`
(when `c(0) = 0`). -/
theorem IsEfficientScale.le_cost {c : ℝ → ℝ} {qb : ℝ} (h : IsEfficientScale c qb)
    (hc0 : c 0 = 0) {q : ℝ} (hq : 0 ≤ q) : c qb / qb * q ≤ c q := by
  rcases eq_or_lt_of_le hq with h0 | hq0
  · rw [← h0, hc0, mul_zero]
  · have := h.2 q hq0
    rw [le_div_iff₀ hq0] at this
    exact this

/-- **(MWG, pp. 337-338, Figure 10.F.4)** With a unique efficient scale `q̄`, `c(0) = 0`,
`c̄ = c(q̄)/q̄` and `x(c̄) > 0` (demand nonincreasing below `c̄`), `(p*, q*, J*)` is a long-run
equilibrium iff `p* = c̄`, `q* = q̄` and `J* q̄ = x(c̄)`. -/
theorem lr_efficientScale {x c : ℝ → ℝ} {qb : ℝ} (hc0 : c 0 = 0) (hqb : IsEfficientScale c qb)
    (huniq : ∀ q, 0 < q → c q / q = c qb / qb → q = qb) (hx : 0 < x (c qb / qb))
    (hmono : AntitoneOn x (Set.Iic (c qb / qb))) {p q : ℝ} {J : ℕ} :
    IsLREqm x c p q J ↔ p = c qb / qb ∧ q = qb ∧ (J : ℝ) * qb = x (c qb / qb) := by
  set cb := c qb / qb with hcb
  have hqb0 := hqb.1
  have hcbq : c qb = cb * qb := by rw [hcb]; field_simp
  constructor
  · rintro ⟨⟨hq, hmax⟩, hxp, hz⟩
    have hp1 : p ≤ cb := by
      by_contra hlt
      push Not at hlt
      have := hmax qb hqb0.le
      nlinarith
    have hp2 : cb ≤ p := by
      by_contra hlt
      push Not at hlt
      have hq0 : q = 0 := by
        by_contra hne
        have hq' : 0 < q := lt_of_le_of_ne hq (Ne.symm hne)
        have := hqb.le_cost hc0 hq
        nlinarith
      rw [hq0, mul_zero] at hxp
      have := hmono (Set.mem_Iic.2 hlt.le) (Set.mem_Iic.2 le_rfl) hlt.le
      linarith
    have hpeq : p = cb := le_antisymm hp1 hp2
    subst hpeq
    have hq0 : 0 < q := by
      rw [hxp] at hx
      exact pos_of_mul_pos_right hx (Nat.cast_nonneg J)
    have hAC : c q / q = cb := by
      rw [div_eq_iff hq0.ne']; linarith
    have := huniq q hq0 hAC
    subst this
    exact ⟨rfl, rfl, hxp.symm⟩
  · rintro ⟨rfl, rfl, hJ⟩
    refine ⟨⟨hqb0.le, fun q' hq' => ?_⟩, hJ.symm, by rw [hcbq]; ring⟩
    have := hqb.le_cost hc0 hq'
    rw [hcbq]
    nlinarith

/-- **(MWG, p. 338)** The integer problem: if `x(c̄)/q̄` is not an integer, no long-run
equilibrium exists. -/
theorem lr_integer_problem {x c : ℝ → ℝ} {qb : ℝ} (hc0 : c 0 = 0)
    (hqb : IsEfficientScale c qb) (huniq : ∀ q, 0 < q → c q / q = c qb / qb → q = qb)
    (hx : 0 < x (c qb / qb)) (hmono : AntitoneOn x (Set.Iic (c qb / qb)))
    (hnot : ¬ ∃ J : ℕ, (J : ℝ) * qb = x (c qb / qb)) : ¬ ∃ p q J, IsLREqm x c p q J := by
  rintro ⟨p, q, J, h⟩
  obtain ⟨-, -, hJ⟩ := (lr_efficientScale hc0 hqb huniq hx hmono).1 h
  exact hnot ⟨J, hJ⟩

/-- **(MWG, p. 338)** The long-run supply correspondence with an efficient scale:
`Q(c̄) = {Jq̄ : J ∈ ℕ}`, `Q(p) = {0}` for `p < c̄`, `Q(p) = ∞` for `p > c̄`. -/
theorem lrSupply_efficientScale {c : ℝ → ℝ} {qb : ℝ} (hc0 : c 0 = 0)
    (hqb : IsEfficientScale c qb) (huniq : ∀ q, 0 < q → c q / q = c qb / qb → q = qb) :
    (∀ Q, InLRSupply c (c qb / qb) Q ↔ ∃ J : ℕ, Q = J * qb) ∧
    (∀ p, p < c qb / qb → ∀ Q, InLRSupply c p Q ↔ Q = 0) ∧
    (∀ p, c qb / qb < p → PosProfit c p) := by
  set cb := c qb / qb with hcb
  have hqb0 := hqb.1
  have hcbq : c qb = cb * qb := by rw [hcb]; field_simp
  have hnopos : ¬ PosProfit c cb := fun ⟨q, hq, hpos⟩ => by
    have := hqb.le_cost hc0 hq; linarith
  have hmaxqb : IsProfitMax c cb qb := ⟨hqb0.le, fun q' hq' => by
    have := hqb.le_cost hc0 hq'; rw [hcbq]; nlinarith⟩
  refine ⟨fun Q => ⟨?_, ?_⟩, fun p hp Q => ⟨?_, ?_⟩, fun p hp => ⟨qb, hqb0.le, by
    rw [hcbq]; nlinarith⟩⟩
  · rintro ⟨-, J, q, ⟨hq, hmax⟩, rfl⟩
    rcases eq_or_lt_of_le hq with h0 | hq0
    · exact ⟨0, by rw [← h0]; simp⟩
    · have h1 := hmax qb hqb0.le
      have h2 := hqb.le_cost hc0 hq
      have hAC : c q / q = cb := by
        rw [div_eq_iff hq0.ne']; rw [hcbq] at h1; nlinarith
      exact ⟨J, by rw [huniq q hq0 hAC]⟩
  · rintro ⟨J, rfl⟩
    exact ⟨hnopos, J, qb, hmaxqb, rfl⟩
  · rintro ⟨-, J, q, ⟨hq, hmax⟩, rfl⟩
    have hq0 : q = 0 := by
      by_contra hne
      have hq' : 0 < q := lt_of_le_of_ne hq (Ne.symm hne)
      have h1 := hmax 0 le_rfl
      have h2 := hqb.le_cost hc0 hq
      rw [hc0] at h1
      nlinarith
    rw [hq0, mul_zero]
  · rintro rfl
    refine ⟨fun ⟨q, hq, hpos⟩ => by
      have := hqb.le_cost hc0 hq; nlinarith, 0, 0, ⟨le_rfl, fun q' hq' => ?_⟩, by simp⟩
    have := hqb.le_cost hc0 hq'
    rw [hc0]
    nlinarith

/-- **Footnote 28** (MWG, p. 338). If `c` is differentiable at a positive equilibrium output
`q*`, then `c'(q*) = p* = c(q*)/q*`: `q*` is a critical point of average cost. -/
theorem footnote_10_F_28 {x c : ℝ → ℝ} {p q d : ℝ} {J : ℕ} (h : IsLREqm x c p q J)
    (hq : 0 < q) (hd : HasDerivAt c d q) : d = p ∧ p = c q / q := by
  obtain ⟨⟨-, hmax⟩, -, hz⟩ := h
  have hder : HasDerivWithinAt (fun z => p * z - c z) (p - d) (Set.Ici 0) q := by
    have h1 := ((hasDerivAt_id q).const_mul p).sub hd
    rw [mul_one] at h1
    exact h1.hasDerivWithinAt
  have := (foc_max_necessary hder hq.le hmax).2 hq
  refine ⟨by linarith, ?_⟩
  rw [eq_div_iff hq.ne']
  linarith

/-- **Footnote 28** (MWG, p. 338) with Exercise 5.D.1 (Chapter 5): at an efficient scale where `c`
is differentiable, `c'(q̄) = c(q̄)/q̄`; hence when average cost is U-shaped (no other critical
point), `q* = q̄` and `p* = c̄`. -/
theorem footnote_10_F_28_ushaped {x c dc : ℝ → ℝ} {qb p q : ℝ} {J : ℕ}
    (hqb : IsEfficientScale c qb) (hd : ∀ q, 0 < q → HasDerivAt c (dc q) q)
    (hcrit : ∀ q, 0 < q → dc q = c q / q → q = qb) (h : IsLREqm x c p q J) (hq : 0 < q) :
    q = qb ∧ p = c qb / qb ∧ dc qb = c qb / qb := by
  have hb := (MWG.Production.exercise_5_D_1 hqb.1 hqb.2 (hd qb hqb.1)).symm
  obtain ⟨h1, h2⟩ := footnote_10_F_28 h hq (hd q hq)
  have hqq := hcrit q hq (h1.trans h2)
  subst hqq
  exact ⟨rfl, h2, hb⟩

/-- **Footnote 29** (MWG, p. 339). If average cost attains its minimum `c̄` exactly on an
interval `[q₋, q̄]` of efficient scales, a long-run equilibrium exists iff `x(c̄) = Jq` for some
`q ∈ [q₋, q̄]` and integer `J`. -/
theorem footnote_10_F_29 {x c : ℝ → ℝ} {a b cb : ℝ} (hc0 : c 0 = 0) (ha : 0 < a)
    (hab : a ≤ b) (hmin : ∀ q, 0 < q → cb ≤ c q / q)
    (heff : ∀ q, 0 < q → (c q / q = cb ↔ q ∈ Set.Icc a b)) (hx : 0 < x cb)
    (hmono : AntitoneOn x (Set.Iic cb)) :
    (∃ p q J, IsLREqm x c p q J) ↔ ∃ q ∈ Set.Icc a b, ∃ J : ℕ, (J : ℝ) * q = x cb := by
  have hle : ∀ q, 0 ≤ q → cb * q ≤ c q := fun q hq => by
    rcases eq_or_lt_of_le hq with h0 | hq0
    · rw [← h0, hc0, mul_zero]
    · have := hmin q hq0; rwa [le_div_iff₀ hq0] at this
  have hca : c a = cb * a := by
    have := (heff a ha).2 ⟨le_rfl, hab⟩
    rw [div_eq_iff ha.ne'] at this; linarith
  constructor
  · rintro ⟨p, q, J, ⟨hq, hmax⟩, hxp, hz⟩
    have hp1 : p ≤ cb := by
      by_contra hlt; push Not at hlt
      have := hmax a ha.le; nlinarith
    have hp2 : cb ≤ p := by
      by_contra hlt; push Not at hlt
      have hq0 : q = 0 := by
        by_contra hne
        have hq' : 0 < q := lt_of_le_of_ne hq (Ne.symm hne)
        have := hle q hq; nlinarith
      rw [hq0, mul_zero] at hxp
      have := hmono (Set.mem_Iic.2 hlt.le) (Set.mem_Iic.2 le_rfl) hlt.le
      linarith
    have hpeq : p = cb := le_antisymm hp1 hp2
    subst hpeq
    have hq0 : 0 < q := by
      rw [hxp] at hx; exact pos_of_mul_pos_right hx (Nat.cast_nonneg J)
    have hAC : c q / q = p := by rw [div_eq_iff hq0.ne']; linarith
    exact ⟨q, (heff q hq0).1 hAC, J, hxp.symm⟩
  · rintro ⟨q, hq, J, hJ⟩
    have hq0 : 0 < q := ha.trans_le hq.1
    have hcq : c q = cb * q := by
      have := (heff q hq0).2 hq; rw [div_eq_iff hq0.ne'] at this; linarith
    exact ⟨cb, q, J, ⟨hq0.le, fun q' hq' => by have := hle q' hq'; rw [hcq]; nlinarith⟩,
      hJ.symm, by rw [hcq]; ring⟩

/-- **Footnote 25** (MWG, p. 335). If `c` is strictly convex on `(0, ∞)`, a firm's supply
correspondence contains at most one positive output at any price. -/
theorem footnote_10_F_25 {c : ℝ → ℝ} (hconv : StrictConvexOn ℝ (Set.Ioi 0) c) {p q₁ q₂ : ℝ}
    (h₁ : IsProfitMax c p q₁) (h₂ : IsProfitMax c p q₂) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) :
    q₁ = q₂ := by
  by_contra hne
  have hmid := hconv.2 (Set.mem_Ioi.2 hq₁) (Set.mem_Ioi.2 hq₂) hne
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at hmid
  have e1 := h₁.2 _ (by positivity : (0 : ℝ) ≤ 1 / 2 * q₁ + 1 / 2 * q₂)
  have e2 := h₁.2 q₂ hq₂.le
  have e3 := h₂.2 q₁ hq₁.le
  nlinarith

/-! ## Efficiency of the long-run equilibrium (p. 339) -/

/-- **(MWG, p. 339)** The long-run equilibrium maximizes aggregate surplus even without convexity.
If `c(0) = 0` and `c(q) ≥ c̄ q` for all `q ≥ 0` (efficient scale with average cost `c̄ > 0`),
then the competitive aggregate `x(c̄)` gives aggregate surplus `γ(x(c̄)) - c̄ x(c̄)` at least
`γ(x̂) - J c(x̂/J)` for every aggregate `x̂ ≥ 0` and every number `J ≥ 1` of firms. -/
theorem lr_maximizes_surplus {ι : Type*} [Fintype ι] [Nonempty ι] (C : ι → QLConsumer) {c : ℝ → ℝ}
    {cb : ℝ} (hcb : 0 < cb) (hle : ∀ q, 0 ≤ q → cb * q ≤ c q) {X : ℝ} (hX : 0 ≤ X) {J : ℕ}
    (hJ : 0 < J) :
    grossBenefit C X - J * c (X / J) ≤ grossBenefit C (aggDemand C cb) - cb * aggDemand C cb := by
  have hfoc : ∀ i, IsFOCSol (C i).dφ cb ((C i).demand cb) := fun i => (C i).demand_spec hcb
  have hγ := grossBenefit_eq_of_foc hfoc
  have hJ' : (0 : ℝ) < J := Nat.cast_pos.2 hJ
  have hcost : cb * X ≤ J * c (X / J) := by
    have := hle (X / J) (by positivity)
    have e : cb * X = J * (cb * (X / J)) := by field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left this hJ'.le
  have hγX : grossBenefit C X ≤ grossBenefit C (aggDemand C cb) + cb * (X - aggDemand C cb) := by
    rw [grossBenefit_eq C hX, aggDemand, hγ]
    have := foc_benefit_le hfoc (fun i => (optAlloc_foc C hX i).1)
    rwa [optAlloc_sum C hX] at this
  linarith

/-! ## Example 10.F.1: short-run and long-run comparative statics -/

/-- **(10.F.1)** (MWG, p. 340). The long-run cost `c(q) = K + ψ(q)` for `q > 0`, `c(0) = 0`. -/
noncomputable def lumpyCost (K : ℝ) (ψ : ℝ → ℝ) (q : ℝ) : ℝ := if q = 0 then 0 else K + ψ q

/-- **Example 10.F.1** (MWG, pp. 340-341). Let the long-run cost be (10.F.1) with `K > 0` and
`ψ` a strictly convex cost (`ψ(0) = 0`, `ψ' > 0`, `ψ'' ≥ 0`, `ψ' → ∞`), with efficient scale
`q̄` and `c̄ = c(q̄)/q̄`, and let the industry start in a long-run equilibrium with `J₀` firms
for demand `x₀` (`J₀ q̄ = x₀(c̄)`). After a fall in demand to `x₁ < x₀` (nonincreasing), at the
short-run equilibrium price `p_s` with the `J₀` firms (cost (10.F.2), `K` sunk) we have
`p_s < c̄` and active firms make losses; in the new long-run equilibrium the price returns to
`c̄`, each firm produces `q̄`, and the number of firms falls to `J₁ < J₀`. -/
theorem example_10_F_1 {K : ℝ} (hK : 0 < K) (F : QLFirmStrict) (hψ0 : F.c 0 = 0) {qb : ℝ}
    (hqb : IsEfficientScale (lumpyCost K F.c) qb) {x₀ x₁ : ℝ → ℝ} (hfall : ∀ p, x₁ p < x₀ p)
    (hmono : AntitoneOn x₁ (Set.Ioi 0))
    {J₀ : ℕ} (hJ₀ : (J₀ : ℝ) * qb = x₀ (lumpyCost K F.c qb / qb))
    {ps : ℝ} (hps : 0 < ps) (hSR : x₁ ps = J₀ * F.supply ps) :
    ps < lumpyCost K F.c qb / qb ∧
    ps * F.supply ps - (K + F.c (F.supply ps)) < 0 ∧
    ∀ J₁ : ℕ, (J₁ : ℝ) * qb = x₁ (lumpyCost K F.c qb / qb) →
      J₁ < J₀ ∧ IsLREqm x₁ (lumpyCost K F.c) (lumpyCost K F.c qb / qb) qb J₁ := by
  set c := lumpyCost K F.c with hcdef
  set cb := c qb / qb with hcb
  have hqb0 := hqb.1
  have hc0 : c 0 = 0 := by simp [hcdef, lumpyCost]
  have hcq : ∀ q, q ≠ 0 → c q = K + F.c q := fun q hq => by simp [hcdef, lumpyCost, hq]
  have hcb0 : 0 < cb := by
    rw [hcb, hcq qb hqb0.ne']
    have : F.c 0 ≤ F.c qb := F.toQLFirm.c_strictMono.monotoneOn (Set.mem_Ici.2 le_rfl)
      (Set.mem_Ici.2 hqb0.le) hqb0.le
    rw [hψ0] at this
    exact div_pos (by linarith) hqb0
  -- the short-run supply at `c̄` is `q̄` (footnote 28 / Exercise 5.D.1)
  have hdc : F.dc qb = cb := by
    have hd : HasDerivAt c (F.dc qb) qb := by
      have h1 : HasDerivAt (fun q => K + F.c q) (F.dc qb) qb :=
        (foc_hasDerivAt F.hasDeriv hqb0).const_add K
      refine h1.congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds hqb0] with q hq
      exact hcq q (ne_of_gt hq)
    exact (MWG.Production.exercise_5_D_1 hqb0 hqb.2 hd).symm
  have hsupp : F.supply cb = qb := F.supply_eq ⟨hqb0.le, hdc.symm.le, fun _ => hdc.symm⟩
  have hps_lt : ps < cb := by
    by_contra hle
    push Not at hle
    have h1 : qb ≤ F.supply ps := hsupp ▸ F.supply_monotone hle
    have h2 : x₁ ps ≤ x₁ cb := hmono hcb0 hps hle
    have h3 := hfall cb
    have h4 : (J₀ : ℝ) * qb ≤ J₀ * F.supply ps := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
    linarith
  refine ⟨hps_lt, ?_, fun J₁ hJ₁ => ⟨?_, ?_⟩⟩
  · set qs := F.supply ps
    rcases eq_or_lt_of_le (F.supply_nonneg ps : 0 ≤ qs) with h0 | hq0
    · have h0' : qs = 0 := h0.symm
      rw [h0', hψ0]; linarith
    · have hle := hqb.le_cost hc0 hq0.le
      rw [hcq qs hq0.ne'] at hle
      nlinarith
  · have h1 := hfall cb
    have : (J₁ : ℝ) * qb < J₀ * qb := by rw [hJ₁, hJ₀]; exact h1
    exact_mod_cast lt_of_mul_lt_mul_right this hqb0.le
  · refine ⟨⟨hqb0.le, fun q' hq' => ?_⟩, hJ₁.symm, ?_⟩
    · have := hqb.le_cost hc0 hq'
      have e : c qb = cb * qb := by rw [hcb]; field_simp
      rw [e]
      nlinarith
    · have e : c qb = cb * qb := by rw [hcb]; field_simp
      rw [e]; ring

end MWG.CompetitiveMarkets

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercises 10.F.2-10.F.4 (MWG, pp. 347-348)

* The quadratic cost with a fixed cost, `c(q) = K + αq + βq²` (`q > 0`), `c(0) = 0`: efficient
  scale `q̄ = √(K/β)`, minimum average cost `c̄ = α + 2√(Kβ)` (`quadLumpy_efficientScale`).
* `lr_efficientScale_real`: Definition 10.F.1 ignoring the integer constraint.
* **Exercise 10.F.2**: (a) the long-run equilibrium with demand `A - Bp` and its dependence on
  `A`; (b) the short-run response to `A` (fixed cost sunk), whose derivative tends to `0` as
  `A → ∞`.
* **Exercise 10.F.3** (Pearce): as printed (`φ'' < 0`) the cost `K + φ(q)` has no efficient
  scale (correction); with `φ'' > 0`, the ad valorem tax leads to a higher price and the lump-sum
  tax to larger firms; the ad valorem tax raises more revenue with inelastic demand, but not in
  general (an explicit example where the lump-sum tax raises more).
* **Exercise 10.F.4** (Panzer): the long-run price `p*(w) = min_q c(w, q)/q` is nondecreasing,
  homogeneous of degree one and concave in `w`.
-/

namespace MWG.CompetitiveMarkets

open Filter Topology

/-- **Definition 10.F.1** ignoring the integer constraint: the efficient-scale characterization
(MWG, pp. 337-338) with a real number of firms. -/
theorem lr_efficientScale_real {x c : ℝ → ℝ} {qb : ℝ} (hc0 : c 0 = 0)
    (hqb : IsEfficientScale c qb) (huniq : ∀ q, 0 < q → c q / q = c qb / qb → q = qb)
    (hx : 0 < x (c qb / qb)) (hmono : AntitoneOn x (Set.Iic (c qb / qb))) {p q J : ℝ} :
    IsLREqmReal x c p q J ↔ p = c qb / qb ∧ q = qb ∧ J = x (c qb / qb) / qb := by
  set cb := c qb / qb with hcb
  have hqb0 := hqb.1
  have hcbq : c qb = cb * qb := by rw [hcb]; field_simp
  constructor
  · rintro ⟨hJ, ⟨hq, hmax⟩, hxp, hz⟩
    have hp1 : p ≤ cb := by
      by_contra hlt; push Not at hlt
      have := hmax qb hqb0.le; nlinarith
    have hp2 : cb ≤ p := by
      by_contra hlt; push Not at hlt
      have hq0 : q = 0 := by
        by_contra hne
        have hq' : 0 < q := lt_of_le_of_ne hq (Ne.symm hne)
        have := hqb.le_cost hc0 hq; nlinarith
      rw [hq0, mul_zero] at hxp
      have := hmono (Set.mem_Iic.2 hlt.le) (Set.mem_Iic.2 le_rfl) hlt.le
      linarith
    have hpeq : p = cb := le_antisymm hp1 hp2
    subst hpeq
    have hq0 : 0 < q := by rw [hxp] at hx; exact pos_of_mul_pos_right hx hJ
    have hAC : c q / q = cb := by rw [div_eq_iff hq0.ne']; linarith
    have := huniq q hq0 hAC
    subst this
    refine ⟨rfl, rfl, ?_⟩
    rw [hxp]; field_simp
  · rintro ⟨rfl, rfl, rfl⟩
    refine ⟨div_nonneg hx.le hqb0.le, ⟨hqb0.le, fun q' hq' => ?_⟩, by field_simp, by
      rw [hcbq]; ring⟩
    have := hqb.le_cost hc0 hq'
    rw [hcbq]
    nlinarith

/-! ## The quadratic cost with a fixed cost -/

/-- `c(q) = K + αq + βq²` for `q > 0`, `c(0) = 0` (Exercise 10.F.2). -/
noncomputable def quadLumpyCost (K α β : ℝ) : ℝ → ℝ :=
  lumpyCost K fun q => α * q + β * q ^ 2

/-- With `K = βs²` (`s > 0`), the average cost is `βs²/q + α + βq`, minimized uniquely at
`q̄ = s` with `c̄ = α + 2βs`. -/
theorem quadLumpy_efficientScale {α β s : ℝ} (hβ : 0 < β) (hs : 0 < s) :
    IsEfficientScale (quadLumpyCost (β * s ^ 2) α β) s ∧
      quadLumpyCost (β * s ^ 2) α β s / s = α + 2 * β * s ∧
      ∀ q, 0 < q → quadLumpyCost (β * s ^ 2) α β q / q =
        quadLumpyCost (β * s ^ 2) α β s / s → q = s := by
  have hAC : ∀ q, 0 < q → quadLumpyCost (β * s ^ 2) α β q / q =
      α + 2 * β * s + β * (q - s) ^ 2 / q := by
    intro q hq
    simp only [quadLumpyCost, lumpyCost, hq.ne', ↓reduceIte]
    field_simp
    ring
  have hcb := hAC s hs
  simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    zero_div, add_zero] at hcb
  refine ⟨⟨hs, fun q hq => ?_⟩, hcb, fun q hq heq => ?_⟩
  · rw [hcb, hAC q hq]
    have : 0 ≤ β * (q - s) ^ 2 / q := by positivity
    linarith
  · rw [hcb, hAC q hq] at heq
    have h1 : β * (q - s) ^ 2 / q = 0 := by linarith
    rcases div_eq_zero_iff.1 h1 with h | h
    · rcases mul_eq_zero.1 h with h' | h'
      · exact absurd h' hβ.ne'
      · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h'; linarith
    · exact absurd h hq.ne'

/-- In the book's parameters: `q̄ = √(K/β)` and `c̄ = α + 2√(Kβ)`. -/
theorem quadLumpy_book {K β : ℝ} (hK : 0 < K) (hβ : 0 < β) :
    β * Real.sqrt (K / β) ^ 2 = K ∧ 2 * β * Real.sqrt (K / β) = 2 * Real.sqrt (K * β) := by
  have hs : 0 ≤ K / β := by positivity
  refine ⟨by rw [Real.sq_sqrt hs]; field_simp, ?_⟩
  have : β * Real.sqrt (K / β) = Real.sqrt (K * β) := by
    rw [show K * β = (β * Real.sqrt (K / β)) ^ 2 by rw [mul_pow, Real.sq_sqrt hs]; field_simp]
    exact (Real.sqrt_sq (by positivity)).symm
  rw [mul_assoc, this]

/-- **Exercise 10.F.2(a)** (MWG, p. 347). With demand `x(p) = A - Bp` (`B > 0`) and cost
`K + αq + βq²` (`K = βs²`, so `s = √(K/β)`), if `A > B c̄` the long-run equilibrium (ignoring
the integer constraint) is `p* = c̄ = α + 2βs`, `q* = s`, aggregate output `A - Bc̄` and
`J* = (A - Bc̄)/s`. Price and firm size do not depend on `A`; output and the number of firms
increase with `A` (at rates `1` and `1/s`). -/
theorem exercise_10_F_2a {A B α β s : ℝ} (hB : 0 < B) (hβ : 0 < β) (hs : 0 < s)
    (hA : B * (α + 2 * β * s) < A) {p q J : ℝ} :
    IsLREqmReal (fun p => A - B * p) (quadLumpyCost (β * s ^ 2) α β) p q J ↔
      p = α + 2 * β * s ∧ q = s ∧ J = (A - B * (α + 2 * β * s)) / s := by
  obtain ⟨hqb, hcb, huniq⟩ := quadLumpy_efficientScale (α := α) hβ hs
  have hc0 : quadLumpyCost (β * s ^ 2) α β 0 = 0 := by simp [quadLumpyCost, lumpyCost]
  rw [lr_efficientScale_real hc0 hqb huniq (by rw [hcb]; linarith)
    (fun a _ b _ hab => by nlinarith), hcb]

/-- **Exercise 10.F.2(a)**: the comparative statics in `A`. -/
theorem exercise_10_F_2a_statics {B α β s : ℝ} (hs : 0 < s) (A : ℝ) :
    HasDerivAt (fun A => A - B * (α + 2 * β * s)) 1 A ∧
      HasDerivAt (fun A => (A - B * (α + 2 * β * s)) / s) (1 / s) A ∧ 0 < 1 / s :=
  ⟨by simpa using (hasDerivAt_id A).sub_const (B * (α + 2 * β * s)),
    by simpa using ((hasDerivAt_id A).sub_const (B * (α + 2 * β * s))).div_const s,
    by positivity⟩

/-- **Exercise 10.F.2(b)** (MWG, p. 347): short-run supply. With the fixed cost sunk, a firm's
short-run profit `pq - K - αq - βq²` is maximized at `q = (p - α)/(2β)` for `p ≥ α`. -/
theorem exercise_10_F_2b_supply {K α β p : ℝ} (hβ : 0 < β) (hp : α ≤ p) (q : ℝ) :
    0 ≤ (p - α) / (2 * β) ∧ p * q - (K + α * q + β * q ^ 2) ≤
      p * ((p - α) / (2 * β)) - (K + α * ((p - α) / (2 * β)) + β * ((p - α) / (2 * β)) ^ 2) := by
  refine ⟨div_nonneg (by linarith) (by positivity), ?_⟩
  have : p * ((p - α) / (2 * β)) - (K + α * ((p - α) / (2 * β)) + β * ((p - α) / (2 * β)) ^ 2) -
      (p * q - (K + α * q + β * q ^ 2)) = β * (q - (p - α) / (2 * β)) ^ 2 := by
    field_simp; ring
  nlinarith [sq_nonneg (q - (p - α) / (2 * β))]

/-- **Exercise 10.F.2(b)** (MWG, p. 347). With `J` firms fixed, the short-run equilibrium price
for demand `A' - Bp` is `pₛ(A') = (A' + Jα/(2β))/(B + J/(2β))`, with
`dpₛ/dA' = 1/(B + J/(2β))`. -/
theorem exercise_10_F_2b {B α β J A' : ℝ} (hB : 0 < B) (hβ : 0 < β) (hJ : 0 ≤ J) :
    A' - B * ((A' + J * α / (2 * β)) / (B + J / (2 * β))) =
        J * (((A' + J * α / (2 * β)) / (B + J / (2 * β)) - α) / (2 * β)) ∧
      HasDerivAt (fun A' => (A' + J * α / (2 * β)) / (B + J / (2 * β)))
        (1 / (B + J / (2 * β))) A' := by
  have hden : 0 < B + J / (2 * β) := by
    have := div_nonneg hJ (by positivity : (0 : ℝ) ≤ 2 * β); linarith [hB]
  have hden' := hden.ne'
  refine ⟨by field_simp; ring, ?_⟩
  simpa using ((hasDerivAt_id A').add_const (J * α / (2 * β))).div_const (B + J / (2 * β))

/-- **Exercise 10.F.2(b)** (MWG, p. 347). Starting from the long-run equilibrium for `A`, the
short-run price response `1/(B + J*(A)/(2β))` (with `J*(A) = (A - Bc̄)/s`) tends to `0` as
`A → ∞`: in a larger market there are more firms and the short-run industry supply is flatter. -/
theorem exercise_10_F_2b_limit {B β s cb : ℝ} (hβ : 0 < β) (hs : 0 < s) :
    Tendsto (fun A => 1 / (B + (A - B * cb) / s / (2 * β))) atTop (𝓝 0) := by
  refine Tendsto.div_atTop tendsto_const_nhds ?_
  refine tendsto_atTop_add_const_left _ B ?_
  have h1 : Tendsto (fun A : ℝ => A - B * cb) atTop atTop := tendsto_atTop_add_const_right _ _
    tendsto_id
  have h2 := (h1.atTop_div_const hs).atTop_div_const (by positivity : (0 : ℝ) < 2 * β)
  exact h2

/-! ## Exercise 10.F.3 -/

/-- **Exercise 10.F.3, as printed** (MWG, p. 347; correction): with `φ'' < 0` there is no
efficient scale. If `φ` is concave on `q ≥ 0` with `φ(0) ≥ 0` and `K > 0`, average cost
`(K + φ(q))/q` strictly decreases from `q` to `2q`, so it has no minimizer. -/
theorem exercise_10_F_3_printed {K : ℝ} (hK : 0 < K) {φ : ℝ → ℝ}
    (hφ : ConcaveOn ℝ (Set.Ici 0) φ) (hφ0 : 0 ≤ φ 0) :
    ∀ qb, ¬ IsEfficientScale (lumpyCost K φ) qb := by
  rintro qb ⟨hqb, hmin⟩
  have h2 := hmin (2 * qb) (by positivity)
  have hconc := hφ.2 (Set.mem_Ici.2 (by positivity : (0 : ℝ) ≤ 2 * qb)) (Set.mem_Ici.2 le_rfl)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul, mul_zero, add_zero] at hconc
  have e : 1 / 2 * (2 * qb) = qb := by ring
  rw [e] at hconc
  simp only [lumpyCost, hqb.ne', (by positivity : (2 : ℝ) * qb ≠ 0), ↓reduceIte] at h2
  rw [div_le_div_iff₀ hqb (by positivity)] at h2
  nlinarith

/-- **Exercise 10.F.3** (MWG, p. 347): a lump-sum tax `T` per operating firm raises the fixed
cost to `K + T`; the efficient scale weakly increases (`q̄ ≤ q̄_T`), and the new minimum average
cost satisfies `c̄_T ≤ c̄ + T/q̄`. -/
theorem exercise_10_F_3_scale {K T : ℝ} (hT : 0 < T) {φ : ℝ → ℝ} {qb qT : ℝ}
    (h : IsEfficientScale (lumpyCost K φ) qb) (hT' : IsEfficientScale (lumpyCost (K + T) φ) qT) :
    qb ≤ qT ∧ lumpyCost (K + T) φ qT / qT ≤ lumpyCost K φ qb / qb + T / qb := by
  have hqb := h.1
  have hqT := hT'.1
  have e1 := h.2 qT hqT
  have e2 := hT'.2 qb hqb
  simp only [lumpyCost, hqb.ne', hqT.ne', ↓reduceIte] at e1 e2 ⊢
  have h1 : (K + T + φ qT) / qT = (K + φ qT) / qT + T / qT := by field_simp; ring
  have h2 : (K + T + φ qb) / qb = (K + φ qb) / qb + T / qb := by field_simp; ring
  refine ⟨?_, by rw [← h2]; exact e2⟩
  have hsum : T / qT ≤ T / qb := by
    rw [h1, h2] at e2
    linarith
  by_contra hlt
  push Not at hlt
  have : T / qb < T / qT := div_lt_div_of_pos_left hT hqT hlt
  linarith

/-- **Exercise 10.F.3** (MWG, pp. 347-348): prices. With equal initial revenue
`T = τ c̄ q̄` (`0 < τ < 1`), the long-run price under the lump-sum tax is at most `c̄(1 + τ)`,
strictly below the long-run price `c̄/(1 - τ)` under the ad valorem tax. -/
theorem exercise_10_F_3_prices {cb cT qb τ : ℝ} (hcb : 0 < cb) (hqb : 0 < qb) (hτ0 : 0 < τ)
    (hτ1 : τ < 1) (hle : cT ≤ cb + τ * cb * qb / qb) : cT < cb / (1 - τ) := by
  rw [mul_div_assoc, div_self hqb.ne', mul_one] at hle
  rw [lt_div_iff₀ (by linarith)]
  nlinarith [mul_le_mul_of_nonneg_right hle (by linarith : (0 : ℝ) ≤ 1 - τ),
    mul_pos hcb (mul_pos hτ0 hτ0)]

/-- **Exercise 10.F.3** (MWG, pp. 347-348): with perfectly inelastic demand `X > 0` the ad valorem
tax raises more revenue after the long-run adjustment: `T X/q̄_T < τ (c̄/(1 - τ)) X`. -/
theorem exercise_10_F_3_inelastic {cb qb qT τ X : ℝ} (hcb : 0 < cb) (hqb : 0 < qb)
    (hscale : qb ≤ qT) (hτ0 : 0 < τ) (hτ1 : τ < 1) (hX : 0 < X) :
    τ * cb * qb * (X / qT) < τ * (cb / (1 - τ)) * X := by
  have hqT : 0 < qT := hqb.trans_le hscale
  have h1 : τ * cb * qb * (X / qT) ≤ τ * cb * X := by
    rw [mul_div_assoc', div_le_iff₀ hqT]
    have : 0 ≤ τ * cb * X := by positivity
    nlinarith
  have h2 : τ * cb * X < τ * (cb / (1 - τ)) * X := by
    have : cb < cb / (1 - τ) := by rw [lt_div_iff₀ (by linarith)]; nlinarith
    have := mul_lt_mul_of_pos_left this hτ0
    nlinarith
  linarith

/-- **Exercise 10.F.3** (MWG, pp. 347-348): the ad valorem tax does not always raise more. With
`c(q) = 1 + q + q²` (`q̄ = 1`, `c̄ = 3`), `τ = 1/2`, `T = τ c̄ q̄ = 3/2` and demand
`x(p) = 61/10 - p`, the ad valorem long-run revenue is `τ (c̄/(1-τ)) x(c̄/(1-τ)) = 3/10`, while
the lump-sum long-run revenue `T x(c̄_T)/q̄_T` (with `q̄_T = √(5/2)`, `c̄_T = 1 + 2√(5/2)`)
exceeds `17/10`. -/
theorem exercise_10_F_3_counterexample :
    let x : ℝ → ℝ := fun p => 61 / 10 - p
    let sT := Real.sqrt (5 / 2)
    IsEfficientScale (quadLumpyCost (1 * 1 ^ 2) 1 1) 1 ∧
      quadLumpyCost (1 * 1 ^ 2) 1 1 1 / 1 = 3 ∧
      IsEfficientScale (quadLumpyCost (1 * sT ^ 2) 1 1) sT ∧
      quadLumpyCost (1 * sT ^ 2) 1 1 sT / sT = 1 + 2 * sT ∧
      1 * sT ^ 2 = 1 * 1 ^ 2 + 3 / 2 ∧
      1 / 2 * (3 / (1 - 1 / 2)) * x (3 / (1 - 1 / 2)) = 3 / 10 ∧
      17 / 10 < 3 / 2 * (x (1 + 2 * sT) / sT) := by
  intro x sT
  have hsT : sT ^ 2 = 5 / 2 := Real.sq_sqrt (by norm_num)
  have hsT0 : 0 < sT := Real.sqrt_pos.2 (by norm_num)
  have hsTlt : sT < 8 / 5 := by nlinarith
  obtain ⟨h1, h2, -⟩ := quadLumpy_efficientScale (α := 1) one_pos one_pos
  obtain ⟨h3, h4, -⟩ := quadLumpy_efficientScale (α := 1) one_pos hsT0
  refine ⟨h1, by rw [h2]; norm_num, h3, by rw [h4]; ring, by rw [hsT]; norm_num, by
    simp only [x]; norm_num, ?_⟩
  simp only [x]
  have key : 17 / 15 < (61 / 10 - (1 + 2 * sT)) / sT := by
    rw [lt_div_iff₀ hsT0]; nlinarith
  linarith

/-! ## Exercise 10.F.4 (Panzer) -/

/-- **Exercise 10.F.4** (MWG, p. 348). Let `p*(w) = min_{q>0} c(w, q)/q` be the long-run
equilibrium price (the minimum average cost, attained at the efficient scale `q̄(w) > 0`), where
for each `q` the cost `c(·, q)` is nondecreasing, homogeneous of degree one and concave in
`w ≫ 0` (Proposition 5.C.2(i)-(ii)). Then `p*` is nondecreasing, homogeneous of degree one and
concave. -/
theorem exercise_10_F_4 {n : ℕ} (c : (Fin n → ℝ) → ℝ → ℝ) (pstar qbar : (Fin n → ℝ) → ℝ)
    (S : Set (Fin n → ℝ)) (hS : Convex ℝ S) (hSs : ∀ w ∈ S, ∀ t : ℝ, 0 < t → t • w ∈ S)
    (hmono : ∀ q, 0 < q → ∀ w ∈ S, ∀ w' ∈ S, w ≤ w' → c w q ≤ c w' q)
    (hhom : ∀ q, 0 < q → ∀ w ∈ S, ∀ t : ℝ, 0 < t → c (t • w) q = t * c w q)
    (hconc : ∀ q, 0 < q → ConcaveOn ℝ S fun w => c w q)
    (hq : ∀ w ∈ S, 0 < qbar w) (hval : ∀ w ∈ S, pstar w = c w (qbar w) / qbar w)
    (hmin : ∀ w ∈ S, ∀ q, 0 < q → pstar w ≤ c w q / q) :
    (∀ w ∈ S, ∀ w' ∈ S, w ≤ w' → pstar w ≤ pstar w') ∧
    (∀ w ∈ S, ∀ t : ℝ, 0 < t → pstar (t • w) = t * pstar w) ∧ ConcaveOn ℝ S pstar := by
  refine ⟨fun w hw w' hw' hle => ?_, fun w hw t ht => ?_, ⟨hS, fun w hw w' hw' a b ha hb hab => ?_⟩⟩
  · rw [hval w' hw']
    exact (hmin w hw _ (hq w' hw')).trans
      (div_le_div_of_nonneg_right (hmono _ (hq w' hw') w hw w' hw' hle) (hq w' hw').le)
  · have htw := hSs w hw t ht
    apply le_antisymm
    · rw [hval w hw]
      have := hmin _ htw _ (hq w hw)
      rw [hhom _ (hq w hw) w hw t ht, mul_div_assoc] at this
      exact this
    · rw [hval _ htw]
      have := hmin w hw _ (hq _ htw)
      have e : c (t • w) (qbar (t • w)) / qbar (t • w) =
          t * (c w (qbar (t • w)) / qbar (t • w)) := by
        rw [hhom _ (hq _ htw) w hw t ht, mul_div_assoc]
      rw [e]
      exact mul_le_mul_of_nonneg_left this ht.le
  · have hmem : a • w + b • w' ∈ S := hS hw hw' ha hb hab
    set q := qbar (a • w + b • w')
    have hq0 : 0 < q := hq _ hmem
    have h1 := (hconc q hq0).2 hw hw' ha hb hab
    simp only [smul_eq_mul] at h1 ⊢
    rw [hval _ hmem]
    have e1 := hmin w hw q hq0
    have e2 := hmin w' hw' q hq0
    have : a * (c w q / q) + b * (c w' q / q) ≤ c (a • w + b • w') q / q := by
      rw [← mul_div_assoc, ← mul_div_assoc, ← add_div]
      exact div_le_div_of_nonneg_right h1 hq0.le
    nlinarith [mul_le_mul_of_nonneg_left e1 ha, mul_le_mul_of_nonneg_left e2 hb]

end MWG.CompetitiveMarkets

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercises 10.F.5-10.F.7 and an instance of Example 10.F.1 (MWG, p. 348)

* `hasDerivAt_comp_pair`: the chain rule for `t ↦ f(g(t), t)` with partial derivatives, used for
  comparative statics with two arguments.
* **Exercise 10.F.5**: (a) the long-run supply response of a firm exceeds the short-run one (Le
  Chatelier; Chapter 5's Exercise 5.D.3); (b) hence the long-run price response to a demand
  shift is smaller, and the quantity response larger, than in the short run.
* **Exercise 10.F.6**: Cobb-Douglas technology `z₁^α z₂^{1-α}`: the long-run price is the unit
  cost (Chapter 5's Example 5.C.1) and the short-run industry supply with capital fixed is
  `K̄((1-α)p/w₂)^{(1-α)/α}`.
* **Exercise 10.F.7** (correction): when a factor can be increased but not decreased in the short
  run, the short-run cost curve has a kink at the long-run equilibrium for fixed proportions
  (Leontief), where short-run supply is vertical over a range of prices, but not in general: for
  a Cobb-Douglas technology it is differentiable there.
* `example_10_F_1_instance`: the hypotheses of Example 10.F.1 are satisfiable.
-/

namespace MWG.CompetitiveMarkets

open Filter Topology MWG.ConsumerChoice

/-- The chain rule for `t ↦ f(g(t), t)` when `f` has partial derivatives `a` (first argument)
and `b` (second argument). -/
theorem hasDerivAt_comp_pair {f : ℝ × ℝ → ℝ} {a b : ℝ} {g : ℝ → ℝ} {g' t₀ : ℝ}
    (hf : HasFDerivAt f (a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (g t₀, t₀))
    (hg : HasDerivAt g g' t₀) : HasDerivAt (fun t => f (g t, t)) (a * g' + b) t₀ := by
  have h := HasFDerivAt.comp_hasDerivAt (f := fun t => (g t, t)) t₀ hf
    (hg.prodMk (hasDerivAt_id t₀))
  simp only [add_apply, smul_apply, ContinuousLinearMap.coe_fst', smul_eq_mul,
    ContinuousLinearMap.coe_snd', mul_one] at h
  exact h

/-! ## Exercise 10.F.5 -/

/-- **Exercise 10.F.5(a)** (MWG, p. 348). If the short-run cost `cₛ` (with factor `k` fixed at its
long-run level) lies above the long-run cost `c` and touches it at the long-run output, the
long-run supply response to the price of good `ℓ` is at least the short-run one (Chapter 5,
Exercise 5.D.3, Le Chatelier). -/
theorem exercise_10_F_5a {c cs qL qS : ℝ → ℝ} {p dL dS : ℝ}
    (hle : ∀ q, 0 ≤ q → c q ≤ cs q) (heq : cs (qL p) = c (qL p)) (hsame : qS p = qL p)
    (hL : ∀ᶠ p' in 𝓝 p, 0 ≤ qL p' ∧ ∀ q, 0 ≤ q → p' * q - c q ≤ p' * qL p' - c (qL p'))
    (hS : ∀ᶠ p' in 𝓝 p, 0 ≤ qS p' ∧ ∀ q, 0 ≤ q → p' * q - cs q ≤ p' * qS p' - cs (qS p'))
    (hcL : ∀ᶠ p' in 𝓝 p, ContinuousAt qL p') (hcS : ∀ᶠ p' in 𝓝 p, ContinuousAt qS p')
    (hdL : HasDerivAt qL dL p) (hdS : HasDerivAt qS dS p) : dS ≤ dL :=
  MWG.Production.exercise_5_D_3 hle heq hsame hL hS hcL hcS hdL hdS

/-- **Exercise 10.F.5(b)** (MWG, p. 348): differentiating the market-clearing condition
`x(p(α), α) = J q(p(α))` gives `p'(α) = x_α / (J q' - x_p)`. -/
theorem exercise_10_F_5b_deriv {x : ℝ × ℝ → ℝ} {q p : ℝ → ℝ} {J xp xα s p' α₀ : ℝ}
    (hx : HasFDerivAt x (xp • ContinuousLinearMap.fst ℝ ℝ ℝ + xα • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (p α₀, α₀))
    (hq : HasDerivAt q s (p α₀)) (hp : HasDerivAt p p' α₀)
    (hclear : ∀ᶠ α in 𝓝 α₀, x (p α, α) = J * q (p α)) (hden : J * s - xp ≠ 0) :
    p' = xα / (J * s - xp) := by
  have h1 := hasDerivAt_comp_pair hx hp
  have h2 : HasDerivAt (fun α => J * q (p α)) (J * (s * p')) α₀ := (hq.comp α₀ hp).const_mul J
  have := (h1.congr_of_eventuallyEq (by filter_upwards [hclear] with α h; exact h.symm)).unique h2
  rw [eq_div_iff hden]
  linarith

/-- **Exercise 10.F.5(b)** (MWG, p. 348). With `x_p < 0`, `x_α > 0` and long-run supply response
`s_L` at least the short-run response `s_S ≥ 0` (part (a)), the long-run price response
`x_α/(J s_L - x_p)` is smaller than the short-run one, and the response of aggregate consumption
`J s x_α/(J s - x_p)` is larger. -/
theorem exercise_10_F_5b {J xp xα sS sL : ℝ} (hJ : 0 < J) (hxp : xp < 0) (hxα : 0 < xα)
    (hsS : 0 ≤ sS) (hSL : sS ≤ sL) :
    xα / (J * sL - xp) ≤ xα / (J * sS - xp) ∧
      J * sS * (xα / (J * sS - xp)) ≤ J * sL * (xα / (J * sL - xp)) := by
  have hS : 0 < J * sS - xp := by nlinarith
  have hL : 0 < J * sL - xp := by nlinarith
  refine ⟨div_le_div_of_nonneg_left hxα.le hS (by nlinarith), ?_⟩
  rw [mul_div_assoc', mul_div_assoc', div_le_div_iff₀ hS hL]
  nlinarith [mul_pos hJ hxα, mul_nonneg (mul_pos hJ hxα).le (sub_nonneg.2 hSL)]

/-! ## Exercise 10.F.6 -/

/-- **Exercise 10.F.6** (MWG, p. 348), long run. With the constant-returns Cobb-Douglas
technology `z₁^α z₂^{1-α}`, the cost is `c(w, q) = c₁(w) q` with unit cost
`c₁(w) = θ φ(w)` (Chapter 5, Example 5.C.1), and with demand `a - bp` (`b ≥ 0`, `a > b c₁`)
the long-run equilibrium price is `c₁(w)` and aggregate output `a - b c₁(w)`. -/
theorem exercise_10_F_6_longRun {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {w : Fin 2 → ℝ}
    (hw : StrictlyPositive w) {a b : ℝ} (hb : 0 ≤ b)
    (ha : b * (MWG.Production.cdTheta α (1 - α) * MWG.Production.cdPhi α (1 - α) w) < a)
    {p q : ℝ} {J : ℕ} :
    (∀ q', 0 < q' → MWG.Production.costFn (MWG.Production.cdProd α (1 - α)) w q' =
      MWG.Production.cdTheta α (1 - α) * MWG.Production.cdPhi α (1 - α) w * q') ∧
    (IsLREqm (fun p => a - b * p)
        (fun q => MWG.Production.cdTheta α (1 - α) * MWG.Production.cdPhi α (1 - α) w * q) p q J ↔
      p = MWG.Production.cdTheta α (1 - α) * MWG.Production.cdPhi α (1 - α) w ∧ 0 ≤ q ∧
        (J : ℝ) * q = a - b * (MWG.Production.cdTheta α (1 - α) *
          MWG.Production.cdPhi α (1 - α) w)) := by
  refine ⟨fun q' hq' => ?_, lr_crs (by linarith) (fun x _ y _ hxy => by nlinarith)⟩
  have h := (MWG.Production.example_5_C_1_cost hα0 (by linarith : 0 < 1 - α) hw hq').1
  rw [h, show α + (1 - α) = 1 by ring, div_one, Real.rpow_one]
  ring

/-- **Exercise 10.F.6** (MWG, p. 348), short run. A firm with capital fixed at `k > 0` chooses
labour `z ≥ 0` to maximize `p k^α z^{1-α} - w₂ z`; the optimum is
`z* = k((1-α)p/w₂)^{1/α}` with output `k((1-α)p/w₂)^{(1-α)/α}`. Summing over firms, the
short-run industry supply is `K̄((1-α)p/w₂)^{(1-α)/α}` with `K̄` the total capital. -/
theorem exercise_10_F_6_shortRun {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {k p w₂ : ℝ} (hk : 0 < k)
    (hp : 0 < p) (hw : 0 < w₂) :
    let r := (1 - α) * p / w₂
    let zs := k * r ^ (1 / α)
    (∀ z, 0 ≤ z → p * k ^ α * z ^ (1 - α) - w₂ * z ≤ p * k ^ α * zs ^ (1 - α) - w₂ * zs) ∧
      k ^ α * zs ^ (1 - α) = k * r ^ ((1 - α) / α) := by
  intro r zs
  have hr : 0 < r := by positivity
  have hzs : 0 < zs := by positivity
  have hzsα : zs ^ (-α) = k ^ (-α) * r⁻¹ := by
    simp only [zs]
    rw [Real.mul_rpow hk.le (by positivity), ← Real.rpow_mul hr.le,
      show 1 / α * -α = -1 by field_simp, Real.rpow_neg_one]
  have hzs1 : zs ^ (1 - α) = k ^ (1 - α) * r ^ ((1 - α) / α) := by
    simp only [zs]
    rw [Real.mul_rpow hk.le (by positivity), ← Real.rpow_mul hr.le]
    congr 2; ring
  -- first-order condition `p k^α (1 - α) zs^{-α} = w₂`
  have hfoc : p * k ^ α * ((1 - α) * zs ^ (-α)) = w₂ := by
    have hk' : k ^ α * k ^ (-α) = 1 := by
      rw [← Real.rpow_add hk, add_neg_cancel, Real.rpow_zero]
    rw [hzsα, show p * k ^ α * ((1 - α) * (k ^ (-α) * r⁻¹)) =
      (k ^ α * k ^ (-α)) * ((1 - α) * p / r) by ring, hk', one_mul]
    have h1 : (1 - α) ≠ 0 := by linarith
    simp only [r]
    field_simp
  refine ⟨fun z hz => ?_, ?_⟩
  · -- tangent line bound from Bernoulli's inequality
    have hb := rpow_one_add_le_one_add_mul_self (s := z / zs - 1) (by
      have : 0 ≤ z / zs := div_nonneg hz hzs.le; linarith) (p := 1 - α) (by linarith)
      (by linarith)
    rw [show 1 + (z / zs - 1) = z / zs by ring, Real.div_rpow hz hzs.le] at hb
    have hzsp : 0 < zs ^ (1 - α) := Real.rpow_pos_of_pos hzs _
    rw [div_le_iff₀ hzsp] at hb
    have hneg : zs ^ (1 - α) = zs * zs ^ (-α) := by
      rw [← Real.rpow_one_add' hzs.le (by linarith), show 1 + -α = 1 - α by ring]
    have hA : 0 ≤ p * k ^ α := by positivity
    have key : z ^ (1 - α) ≤ zs ^ (1 - α) + (1 - α) * zs ^ (-α) * (z - zs) := by
      have : (1 + (1 - α) * (z / zs - 1)) * zs ^ (1 - α) =
          zs ^ (1 - α) + (1 - α) * zs ^ (-α) * (z - zs) := by
        rw [hneg]; field_simp
      linarith
    have := mul_le_mul_of_nonneg_left key hA
    nlinarith [hfoc]
  · rw [hzs1, ← mul_assoc, ← Real.rpow_add hk, show α + (1 - α) = 1 by ring, Real.rpow_one]

/-! ## Exercise 10.F.7 -/

/-- The short-run cost when factor `0` cannot be reduced below `z̄₀`:
`cₛ(q) = inf {w·z : z ≥ 0, z₀ ≥ z̄₀, f(z) ≥ q}`. -/
noncomputable def srCost (f : ℝ → ℝ → ℝ) (w₀ w₁ zbar q : ℝ) : ℝ :=
  sInf {s | ∃ z₀ z₁ : ℝ, zbar ≤ z₀ ∧ 0 ≤ z₁ ∧ q ≤ f z₀ z₁ ∧ s = w₀ * z₀ + w₁ * z₁}

/-- **Exercise 10.F.7** (MWG, p. 348), fixed proportions. For `f(z) = min(z₀, z₁)`, unit factor
prices and `z̄₀ = 1` (the long-run input at `q* = 1`), the short-run cost is
`cₛ(q) = max(q, 1) + q`, which has a kink at `q* = 1`. -/
theorem exercise_10_F_7_leontief {q : ℝ} (hq : 0 ≤ q) :
    srCost (fun z₀ z₁ => min z₀ z₁) 1 1 1 q = max q 1 + q := by
  refine IsLeast.csInf_eq ⟨⟨max q 1, q, le_max_right _ _, hq, by simp, by ring⟩, ?_⟩
  rintro s ⟨z₀, z₁, h₀, h₁, hf, rfl⟩
  have hz0 : q ≤ z₀ := hf.trans (min_le_left _ _)
  have hz1 : q ≤ z₁ := hf.trans (min_le_right _ _)
  have : max q 1 ≤ z₀ := max_le hz0 h₀
  linarith

theorem exercise_10_F_7_leontief_kink :
    ¬ DifferentiableAt ℝ (fun q : ℝ => max q 1 + q) 1 := by
  intro hd
  have h := hd.hasDerivAt
  have hl : HasDerivWithinAt (fun q : ℝ => max q 1 + q) 1 (Set.Iic 1) 1 := by
    have : HasDerivWithinAt (fun q : ℝ => 1 + q) 1 (Set.Iic 1) 1 := by
      simpa using ((hasDerivAt_id (1 : ℝ)).const_add 1).hasDerivWithinAt
    exact this.congr (fun q hq => by simp [max_eq_right (Set.mem_Iic.1 hq)]) (by simp)
  have hr : HasDerivWithinAt (fun q : ℝ => max q 1 + q) 2 (Set.Ici 1) 1 := by
    have : HasDerivWithinAt (fun q : ℝ => 2 * q) 2 (Set.Ici 1) 1 := by
      simpa using ((hasDerivAt_id (1 : ℝ)).const_mul 2).hasDerivWithinAt
    exact this.congr (fun q hq => by rw [max_eq_left (Set.mem_Ici.1 hq)]; ring) (by norm_num)
  have e1 := UniqueDiffWithinAt.eq_deriv _ (uniqueDiffWithinAt_Iic 1) h.hasDerivWithinAt hl
  have e2 := UniqueDiffWithinAt.eq_deriv _ (uniqueDiffWithinAt_Ici 1) h.hasDerivWithinAt hr
  linarith

/-- **Exercise 10.F.7** (MWG, p. 348): with fixed proportions, short-run supply is vertical at
`q* = 1` for every price in `[1, 2]`: demand shifts in this range move the price but not the
quantity (short-run prices more variable than quantities). -/
theorem exercise_10_F_7_vertical_supply {p : ℝ} (hp1 : 1 ≤ p) (hp2 : p ≤ 2) (q : ℝ) :
    p * q - (max q 1 + q) ≤ p * 1 - (max 1 1 + 1) := by
  rcases le_total q 1 with h | h
  · rw [max_eq_right h]; simp; nlinarith
  · rw [max_eq_left h]; simp; nlinarith

/-- The long-run cost for `f(z) = √(z₀z₁)` at unit factor prices is `2q`. -/
theorem exercise_10_F_7_cd_longRun {q : ℝ} (hq : 0 ≤ q) :
    srCost (fun z₀ z₁ => Real.sqrt (z₀ * z₁)) 1 1 0 q = 2 * q := by
  refine IsLeast.csInf_eq ⟨⟨q, q, hq, hq, by
    change q ≤ Real.sqrt (q * q); rw [Real.sqrt_mul_self hq], by ring⟩, ?_⟩
  rintro s ⟨z₀, z₁, h₀, h₁, hf, rfl⟩
  have hf' : q ≤ Real.sqrt (z₀ * z₁) := hf
  have hzz : q ^ 2 ≤ z₀ * z₁ := by
    have := (Real.le_sqrt hq (mul_nonneg h₀ h₁)).1 hf'; nlinarith
  nlinarith [sq_nonneg (z₀ - z₁)]

/-- **Exercise 10.F.7** (MWG, p. 348), correction. For `f(z) = √(z₀z₁)` at unit factor prices with
`z₀ ≥ z̄₀ = 1` (the long-run input at `q* = 1`), the short-run cost is `1 + q²` for `q ≤ 1` and
`2q` for `q ≥ 1`. -/
theorem exercise_10_F_7_cd_shortRun {q : ℝ} (hq : 0 ≤ q) :
    srCost (fun z₀ z₁ => Real.sqrt (z₀ * z₁)) 1 1 1 q = if q ≤ 1 then 1 + q ^ 2 else 2 * q := by
  split_ifs with h
  · refine IsLeast.csInf_eq ⟨⟨1, q ^ 2, le_rfl, sq_nonneg q, by
      change q ≤ Real.sqrt (1 * q ^ 2); rw [one_mul, Real.sqrt_sq hq], by ring⟩, ?_⟩
    rintro s ⟨z₀, z₁, h₀, h₁, hf, rfl⟩
    have hf' : q ≤ Real.sqrt (z₀ * z₁) := hf
    have hzz : q ^ 2 ≤ z₀ * z₁ := by
      have := (Real.le_sqrt hq (mul_nonneg (by linarith) h₁)).1 hf'; nlinarith
    have hq2 : q ^ 2 ≤ 1 := by nlinarith
    have key : z₀ * (1 + q ^ 2) ≤ z₀ * (1 * z₀ + 1 * z₁) := by
      nlinarith [mul_nonneg (sub_nonneg.2 h₀) (sub_nonneg.2 (hq2.trans h₀))]
    exact le_of_mul_le_mul_left key (by linarith)
  · push Not at h
    refine IsLeast.csInf_eq ⟨⟨q, q, h.le, hq, by
      change q ≤ Real.sqrt (q * q); rw [Real.sqrt_mul_self hq], by ring⟩, ?_⟩
    rintro s ⟨z₀, z₁, h₀, h₁, hf, rfl⟩
    have hf' : q ≤ Real.sqrt (z₀ * z₁) := hf
    have hzz : q ^ 2 ≤ z₀ * z₁ := by
      have := (Real.le_sqrt hq (mul_nonneg (by linarith) h₁)).1 hf'; nlinarith
    nlinarith [sq_nonneg (z₀ - z₁)]

/-- **Exercise 10.F.7** (MWG, p. 348), correction: for the Cobb-Douglas technology the
short-run cost is differentiable at the long-run equilibrium output `q* = 1`, with derivative
equal to the long-run marginal cost `2`: the printed claim of a kink fails for smooth
substitution (only the slope of marginal cost jumps, from `2` to `0`). -/
theorem exercise_10_F_7_cd_smooth :
    HasDerivAt (srCost (fun z₀ z₁ => Real.sqrt (z₀ * z₁)) 1 1 1) 2 1 := by
  have hpw : HasDerivAt (fun q : ℝ => if q ≤ 1 then 1 + q ^ 2 else 2 * q) 2 1 := by
    have hl : HasDerivWithinAt (fun q : ℝ => if q ≤ 1 then 1 + q ^ 2 else 2 * q) 2
        (Set.Iic 1) 1 := by
      have : HasDerivWithinAt (fun q : ℝ => 1 + q ^ 2) 2 (Set.Iic 1) 1 := by
        have h := ((hasDerivAt_pow 2 (1 : ℝ)).const_add 1).hasDerivWithinAt (s := Set.Iic 1)
        simpa using h
      exact this.congr (fun q hq => by simp [Set.mem_Iic.1 hq]) (by norm_num)
    have hr : HasDerivWithinAt (fun q : ℝ => if q ≤ 1 then 1 + q ^ 2 else 2 * q) 2
        (Set.Ici 1) 1 := by
      have : HasDerivWithinAt (fun q : ℝ => 2 * q) 2 (Set.Ici 1) 1 := by
        simpa using ((hasDerivAt_id (1 : ℝ)).const_mul 2).hasDerivWithinAt
      refine this.congr (fun q hq => ?_) (by norm_num)
      rcases eq_or_lt_of_le (Set.mem_Ici.1 hq) with h | h
      · rw [← h]; norm_num
      · simp [not_le.2 h]
    have := hl.union hr
    rw [Set.Iic_union_Ici] at this
    exact this.hasDerivAt Filter.univ_mem
  refine hpw.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1)] with q hq
  exact exercise_10_F_7_cd_shortRun (le_of_lt hq)

/-! ## A concrete instance of Example 10.F.1 -/

/-- **Example 10.F.1** (MWG, pp. 340-341), an instance: `K = 1/2`, `ψ(q) = q + q²/2` (so
`q̄ = 1`, `c̄ = 2`), demand falls from `4 - p` (`J₀ = 2` firms) to `3 - p`. The short-run price
is `5/3 < 2`, firms make losses, and in the long run one firm remains. -/
theorem example_10_F_1_instance :
    (5 / 3 : ℝ) < lumpyCost (1 / 2) (quadFirm 1 1 one_pos one_pos).c 1 / 1 ∧
    (5 / 3 : ℝ) * (quadFirm 1 1 one_pos one_pos).supply (5 / 3) -
      (1 / 2 + (quadFirm 1 1 one_pos one_pos).c ((quadFirm 1 1 one_pos one_pos).supply (5 / 3)))
        < 0 ∧
    ∀ J₁ : ℕ, (J₁ : ℝ) * 1 = 3 - lumpyCost (1 / 2) (quadFirm 1 1 one_pos one_pos).c 1 / 1 →
      J₁ < 2 ∧ IsLREqm (fun p => 3 - p) (lumpyCost (1 / 2) (quadFirm 1 1 one_pos one_pos).c)
        (lumpyCost (1 / 2) (quadFirm 1 1 one_pos one_pos).c 1 / 1) 1 J₁ := by
  set F := quadFirm 1 1 one_pos one_pos
  have hcF : lumpyCost (1 / 2) F.c = quadLumpyCost ((1 / 2) * 1 ^ 2) 1 (1 / 2) := by
    funext q
    simp only [quadLumpyCost, lumpyCost, F, quadFirm, QLFirmStrict.c, quadFirmBase]
    split_ifs <;> ring
  obtain ⟨hqb, hcb, -⟩ := quadLumpy_efficientScale (α := 1) (β := 1 / 2) (by norm_num) one_pos
  have hcb2 : lumpyCost (1 / 2) F.c 1 / 1 = 2 := by rw [hcF, hcb]; norm_num
  have hψ0 : F.c 0 = 0 := by simp [F, quadFirm, QLFirmStrict.c, quadFirmBase]
  have hsupp : F.supply (5 / 3) = 2 / 3 := by
    rw [quadFirm_supply one_pos one_pos (by norm_num : (1 : ℝ) < 5 / 3)]; norm_num
  have hqb' : IsEfficientScale (lumpyCost (1 / 2) F.c) 1 := by rw [hcF]; exact hqb
  exact example_10_F_1 (K := 1 / 2) (by norm_num) F hψ0 hqb' (x₀ := fun p => 4 - p)
    (x₁ := fun p => 3 - p) (fun p => by norm_num) (fun a _ b _ hab => by linarith)
    (J₀ := 2) (by change (2 : ℝ) * 1 = 4 - _; rw [hcb2]; norm_num) (ps := 5 / 3) (by norm_num)
    (by change 3 - (5 / 3 : ℝ) = 2 * _; rw [hsupp]; norm_num)

end MWG.CompetitiveMarkets

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercises 10.C.1, 10.C.2, 10.C.8-10.C.11 and 10.D.2 (MWG, pp. 344-346)

* **Exercise 10.C.1**: Cobb-Douglas (log) demand `x_ℓ = w/(L p_ℓ)` and its wealth effect
  `1/(L p_ℓ)`, which vanishes when the number of goods and wealth grow proportionally.
* **Exercise 10.C.2** and **Exercise 10.D.2**: `φ(x) = α + β ln x`, `c(q) = σq`: first-order
  conditions, equilibrium `p = σ`, `x = q = β/σ`, and the same optimal levels.
* **Exercise 10.C.8**: the envelope formula `dπ/dα = p*'q* - c_α`, the weakest sufficient
  condition `c_α > q c_qα` (i.e. `∂MC/∂α < ∂AC/∂α`) for profits to fall for every demand with
  `x' ≤ 0`, and its factor-demand form (`z_k > q ∂z_k/∂q`).
* **Exercise 10.C.9**: a rise in `w_k` lowers the equilibrium price iff `k` is inferior.
* **Exercise 10.C.10**: constant-elasticity demand and marginal cost: equilibrium in logs and
  comparative statics.
* **Exercise 10.C.11**: the difference in profits of two firms with marginally different
  technologies, `-c_α Δα`.
-/

namespace MWG.CompetitiveMarkets

open Filter Topology MWG.ConsumerChoice MWG.ClassicalDemand

/-! ## Exercise 10.C.1 -/

/-- **Exercise 10.C.1(a)** (MWG, p. 344). With `u(x) = ∑ₗ ln xₗ` on strictly positive bundles,
`p ≫ 0` and `w > 0`, the Walrasian demand is `xₗ = w/(L pₗ)`. -/
theorem exercise_10_C_1a {L : ℕ} (hL : 0 < L) {p : Fin L → ℝ} (hp : ∀ l, 0 < p l) {w : ℝ}
    (hw : 0 < w) :
    walrasianDemandOn {x | ∀ l, 0 < x l} (fun x => ∑ l, Real.log (x l)) p w =
      {fun l => w / (L * p l)} := by
  have hL' : (0 : ℝ) < L := Nat.cast_pos.2 hL
  set xs : Fin L → ℝ := fun l => w / (L * p l) with hxs
  have hxs0 : ∀ l, 0 < xs l := fun l => by simp only [hxs]; have := hp l; positivity
  have hbud : p ⬝ᵥ xs = w := by
    simp only [dotProduct, hxs]
    have : ∀ l, p l * (w / (L * p l)) = w / L := fun l => by
      have := (hp l).ne'; field_simp
    simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  -- the key inequality: `∑ log yₗ - ∑ log xsₗ ≤ ∑ (yₗ/xsₗ - 1) = (L/w) p·y - L`
  have hratio : ∀ y : Fin L → ℝ, (∀ l, 0 < y l) →
      ∑ l, (y l / xs l - 1) = L / w * (p ⬝ᵥ y) - L := by
    intro y _
    simp only [dotProduct, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one, Finset.mul_sum, hxs]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    have := (hp l).ne'
    field_simp
  have hlog : ∀ y : Fin L → ℝ, (∀ l, 0 < y l) →
      ∑ l, Real.log (y l) - ∑ l, Real.log (xs l) = ∑ l, Real.log (y l / xs l) := by
    intro y hy
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun l _ => (Real.log_div (hy l).ne' (hxs0 l).ne').symm
  ext y
  simp only [Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨hy, hyb⟩, hmax⟩
    have hy' : ∀ l, 0 < y l := hy
    have hle := hmax xs ⟨hxs0, hbud.le⟩
    simp only at hle
    by_contra hne
    obtain ⟨l, hl⟩ := Function.ne_iff.1 hne
    have hstrict : ∑ k, Real.log (y k / xs k) < ∑ k, (y k / xs k - 1) := by
      refine Finset.sum_lt_sum (fun k _ => Real.log_le_sub_one_of_pos (div_pos (hy' k)
        (hxs0 k))) ⟨l, Finset.mem_univ l, Real.log_lt_sub_one_of_pos (div_pos (hy' l) (hxs0 l))
        fun h => hl ((div_eq_one_iff_eq (hxs0 l).ne').1 h)⟩
    rw [← hlog y hy', hratio y hy'] at hstrict
    have : L / w * (p ⬝ᵥ y) ≤ L := by
      calc L / w * (p ⬝ᵥ y) ≤ L / w * w := mul_le_mul_of_nonneg_left hyb (by positivity)
        _ = L := by field_simp
    linarith
  · rintro rfl
    refine ⟨⟨hxs0, hbud.le⟩, fun y ⟨hy, hyb⟩ => ?_⟩
    have hy' : ∀ l, 0 < y l := hy
    have h1 : ∑ l, Real.log (y l / xs l) ≤ ∑ l, (y l / xs l - 1) :=
      Finset.sum_le_sum fun l _ => Real.log_le_sub_one_of_pos (div_pos (hy' l) (hxs0 l))
    rw [← hlog y hy', hratio y hy'] at h1
    have : L / w * (p ⬝ᵥ y) ≤ L := by
      calc L / w * (p ⬝ᵥ y) ≤ L / w * w := mul_le_mul_of_nonneg_left hyb (by positivity)
        _ = L := by field_simp
    simp only
    linarith

/-- **Exercise 10.C.1(a)** (MWG, p. 344): the wealth effect on good `ℓ` is `∂xₗ/∂w = 1/(L pₗ)`. -/
theorem exercise_10_C_1a_wealth {L : ℕ} {pl w : ℝ} :
    HasDerivAt (fun w => w / (L * pl)) (1 / (L * pl)) w := by
  simpa using (hasDerivAt_id w).div_const ((L : ℝ) * pl)

/-- **Exercise 10.C.1(b)** (MWG, p. 344). If the number of goods `L` and wealth `w = L w₀` grow
proportionally, the demand for good `ℓ` stays `w₀/pₗ` while its wealth effect `1/(L pₗ)` tends
to `0`. -/
theorem exercise_10_C_1b {pl w₀ : ℝ} (hpl : 0 < pl) :
    (∀ L : ℕ, 0 < L → (L * w₀) / (L * pl) = w₀ / pl) ∧
      Tendsto (fun L : ℕ => 1 / ((L : ℝ) * pl)) atTop (𝓝 0) := by
  refine ⟨fun L hL => by
    have : (0 : ℝ) < L := Nat.cast_pos.2 hL
    field_simp, ?_⟩
  refine Tendsto.div_atTop tendsto_const_nhds ?_
  exact Tendsto.atTop_mul_const hpl tendsto_natCast_atTop_atTop

/-! ## Exercises 10.C.2 and 10.D.2 -/

/-- The consumer's problem with `φ(x) = α + β ln x` (`β > 0`) at price `p > 0` is solved uniquely
by `x = β/p` over `x > 0`. -/
theorem logConsumer_max {α β p : ℝ} (hβ : 0 < β) (hp : 0 < p) {x : ℝ} (hx : 0 < x) :
    (∀ y, 0 < y → α + β * Real.log y - p * y ≤ α + β * Real.log x - p * x) ↔ x = β / p := by
  have key : ∀ y, 0 < y → α + β * Real.log y - p * y ≤
      α + β * Real.log (β / p) - p * (β / p) := by
    intro y hy
    have h := Real.log_le_sub_one_of_pos (div_pos (mul_pos hp hy) hβ)
    rw [Real.log_div (mul_pos hp hy).ne' hβ.ne', Real.log_mul hp.ne' hy.ne'] at h
    rw [Real.log_div hβ.ne' hp.ne']
    have e : p * (β / p) = β := by field_simp
    rw [e]
    have : β * (Real.log p + Real.log y - Real.log β) ≤ β * (p * y / β - 1) :=
      mul_le_mul_of_nonneg_left h hβ.le
    have e2 : β * (p * y / β - 1) = p * y - β := by field_simp
    nlinarith
  constructor
  · intro hmax
    by_contra hne
    have h := hmax (β / p) (div_pos hβ hp)
    have hstrict := Real.log_lt_sub_one_of_pos (div_pos (mul_pos hp hx) hβ) (by
      intro h1
      apply hne
      rw [div_eq_one_iff_eq hβ.ne'] at h1
      field_simp; linarith)
    rw [Real.log_div (mul_pos hp hx).ne' hβ.ne', Real.log_mul hp.ne' hx.ne'] at hstrict
    rw [Real.log_div hβ.ne' hp.ne'] at h
    have e : p * (β / p) = β := by field_simp
    rw [e] at h
    have : β * (Real.log p + Real.log x - Real.log β) < β * (p * x / β - 1) :=
      mul_lt_mul_of_pos_left hstrict hβ
    have e2 : β * (p * x / β - 1) = p * x - β := by field_simp
    nlinarith
  · rintro rfl
    exact key

/-- **Exercise 10.C.2(a)** (MWG, p. 344): first-order conditions. The consumer demands
`x = β/p` (and has no optimum if `p ≤ 0`); the firm with `c(q) = σq` maximizes profit at `q ≥ 0`
iff `p ≤ σ`, with equality if `q > 0`. -/
theorem exercise_10_C_2a {α β σ : ℝ} (hβ : 0 < β) :
    (∀ p, p ≤ 0 → ∀ x, 0 < x → ∃ y, 0 < y ∧
      α + β * Real.log x - p * x < α + β * Real.log y - p * y) ∧
    (∀ p q, 0 ≤ q → ((∀ q', 0 ≤ q' → p * q' - σ * q' ≤ p * q - σ * q) ↔
      p ≤ σ ∧ (0 < q → p = σ))) := by
  refine ⟨fun p hp x hx => ⟨x + 1, by linarith, ?_⟩, fun p q hq => ⟨fun h => ?_, ?_⟩⟩
  · have := Real.log_lt_log hx (by linarith : x < x + 1)
    nlinarith
  · have hle : p ≤ σ := by
      by_contra hlt; push Not at hlt
      have := h (q + 1) (by linarith); nlinarith
    refine ⟨hle, fun hq0 => le_antisymm hle ?_⟩
    by_contra hlt; push Not at hlt
    have := h 0 le_rfl; nlinarith
  · rintro ⟨hle, heq⟩ q' hq'
    rcases eq_or_lt_of_le hq with h0 | hpos
    · rw [← h0]; nlinarith
    · rw [heq hpos]; ring_nf; exact le_rfl

/-- **Exercise 10.C.2(b)** (MWG, p. 344). With one consumer (`φ = α + β ln x`) and one firm
(`c = σq`), a price `p` and positive consumption `x` with production `q` form an equilibrium
(utility maximization, profit maximization, `x = q`) iff `p = σ` and `x = q = β/σ`. The
equilibrium does not depend on `α`, increases in `β` and decreases in `σ`. -/
theorem exercise_10_C_2b {α β σ : ℝ} (hβ : 0 < β) (hσ : 0 < σ) {p x q : ℝ} (hx : 0 < x)
    (hq : 0 ≤ q) :
    ((∀ y, 0 < y → α + β * Real.log y - p * y ≤ α + β * Real.log x - p * x) ∧
      (∀ q', 0 ≤ q' → p * q' - σ * q' ≤ p * q - σ * q) ∧ x = q) ↔
      p = σ ∧ x = β / σ ∧ q = β / σ := by
  constructor
  · rintro ⟨hcons, hfirm, hxq⟩
    have hp : 0 < p := by
      by_contra hle; push Not at hle
      obtain ⟨y, hy, hlt⟩ := (exercise_10_C_2a (α := α) (σ := σ) hβ).1 p hle x hx
      have := hcons y hy; linarith
    have hx' := (logConsumer_max hβ hp hx).1 hcons
    have hfoc := ((exercise_10_C_2a (α := α) (σ := σ) hβ).2 p q hq).1 hfirm
    have hpσ : p = σ := hfoc.2 (hxq ▸ hx)
    subst hpσ
    exact ⟨rfl, hx', hxq ▸ hx'⟩
  · rintro ⟨rfl, hx', hq'⟩
    refine ⟨(logConsumer_max hβ hσ hx).2 hx', fun q' _ => by ring_nf; exact le_rfl, ?_⟩
    rw [hx', hq']

/-- **Exercise 10.C.2(b)**: comparative statics of `β/σ`. -/
theorem exercise_10_C_2b_statics {β σ : ℝ} (hβ : 0 < β) (hσ : 0 < σ) :
    HasDerivAt (fun b => b / σ) (1 / σ) β ∧ 0 < 1 / σ ∧
      HasDerivAt (fun s => β / s) (-β / σ ^ 2) σ ∧ -β / σ ^ 2 < 0 := by
  refine ⟨by simpa using (hasDerivAt_id β).div_const σ, by positivity, ?_, ?_⟩
  · have := (hasDerivAt_inv hσ.ne').const_mul β
    convert this using 1
    · ext s; simp [div_eq_mul_inv]
    · field_simp
  · have : 0 < β / σ ^ 2 := by positivity
    rw [neg_div]; linarith

/-- **Exercise 10.D.2** (MWG, p. 346). For the economy of Exercise 10.C.2 the optimal levels
of good `ℓ` (maximize `α + β ln x - σq` subject to `x = q`) are `x = q = β/σ`, the competitive
equilibrium levels. -/
theorem exercise_10_D_2 {α β σ : ℝ} (hβ : 0 < β) (hσ : 0 < σ) {x : ℝ} (hx : 0 < x) :
    (∀ y, 0 < y → α + β * Real.log y - σ * y ≤ α + β * Real.log x - σ * x) ↔ x = β / σ :=
  logConsumer_max hβ hσ hx

/-! ## Exercises 10.C.8 and 10.C.9 -/

/-- **Comparative statics with a cost parameter** (MWG, Exercises 10.C.8-10.C.9). Let `J > 0`
identical firms have marginal cost `MC(q, α)` with partial derivatives `c_qq`, `c_qα`, and let
differentiable paths `p(α)`, `q(α)` satisfy `p = MC(q, α)` and `x(p) = J q` near `α₀`, where
`x'(p) = d`. Then `p'(α₀)(1 - c_qq d/J) = c_qα`. -/
theorem price_response_cost_param {MC : ℝ × ℝ → ℝ} {x p q : ℝ → ℝ} {J cqq cqα d p' q' α₀ : ℝ}
    (hJ : 0 < J)
    (hMC : HasFDerivAt MC (cqq • ContinuousLinearMap.fst ℝ ℝ ℝ +
      cqα • ContinuousLinearMap.snd ℝ ℝ ℝ) (q α₀, α₀))
    (hx : HasDerivAt x d (p α₀)) (hp : HasDerivAt p p' α₀) (hq : HasDerivAt q q' α₀)
    (hfoc : ∀ᶠ α in 𝓝 α₀, p α = MC (q α, α)) (hclear : ∀ᶠ α in 𝓝 α₀, x (p α) = J * q α) :
    p' * (1 - cqq * d / J) = cqα := by
  have h1 := (hasDerivAt_comp_pair hMC hq).congr_of_eventuallyEq
    (by filter_upwards [hfoc] with α h; exact h)
  have e1 := hp.unique h1
  have h2 := (hx.comp α₀ hp).congr_of_eventuallyEq
    (by filter_upwards [hclear] with α h; exact h.symm)
  have e2 := (hq.const_mul J).unique h2
  have hq' : q' = d * p' / J := by rw [eq_div_iff hJ.ne']; linarith
  calc p' * (1 - cqq * d / J) = p' - cqq * (d * p' / J) := by ring
    _ = p' - cqq * q' := by rw [hq']
    _ = cqα := by linarith

/-- **Exercise 10.C.8(a)** (MWG, p. 345). Along the equilibrium path, a firm's profit
`π(α) = p(α)q(α) - c(q(α), α)` changes at rate `dπ/dα = p'(α₀)q(α₀) - c_α` (the envelope
theorem: the effect through `q` vanishes because `p = c_q`). -/
theorem exercise_10_C_8a {c : ℝ × ℝ → ℝ} {p q : ℝ → ℝ} {cq cα p' q' α₀ : ℝ}
    (hc : HasFDerivAt c (cq • ContinuousLinearMap.fst ℝ ℝ ℝ + cα • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (q α₀, α₀))
    (hp : HasDerivAt p p' α₀) (hq : HasDerivAt q q' α₀) (hfoc : p α₀ = cq) :
    HasDerivAt (fun α => p α * q α - c (q α, α)) (p' * q α₀ - cα) α₀ := by
  have h := (hp.mul hq).sub (hasDerivAt_comp_pair hc hq)
  convert h using 1
  rw [hfoc]
  ring

/-- **Exercise 10.C.8(b)** (MWG, p. 345). With `p' = q c_qα/(1 - c_qq x'/J)`... (from
`price_response_cost_param`), `c_qq ≥ 0` and `J > 0`, the profit change
`q c_qα/(1 - c_qq d/J) - c_α` is negative for every demand slope `d ≤ 0` iff
`c_α > q c_qα`, i.e. `∂MC/∂α < ∂AC/∂α = c_α/q`. -/
theorem exercise_10_C_8b {J cqq cqα cα q : ℝ} (hJ : 0 < J) (hcqq : 0 ≤ cqq) (hq : 0 < q)
    (hcα : 0 < cα) :
    (∀ d : ℝ, d ≤ 0 → q * cqα / (1 - cqq * d / J) - cα < 0) ↔ q * cqα < cα := by
  constructor
  · intro h
    have := h 0 le_rfl
    simpa using this
  · intro hlt d hd
    have hD : 1 ≤ 1 - cqq * d / J := by
      have : cqq * d / J ≤ 0 := div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos
        hcqq hd) hJ.le
      linarith
    rcases le_or_gt cqα 0 with hneg | hpos
    · have : q * cqα / (1 - cqq * d / J) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hq.le hneg) (by linarith)
      linarith
    · have : q * cqα / (1 - cqq * d / J) ≤ q * cqα :=
        div_le_self (by positivity) hD
      linarith

/-- **Exercise 10.C.8(b)** (MWG, p. 345), the converse part (corrected): if `q c_qα > c_α`, a
vertical demand (`x' = 0`) makes profits increase with `α`; if `q c_qα = c_α` it leaves them
unchanged to first order (the book's "increase" needs the strict inequality). -/
theorem exercise_10_C_8b_converse {J cqq cqα cα q : ℝ} :
    (cα < q * cqα → 0 < q * cqα / (1 - cqq * 0 / J) - cα) ∧
      (q * cqα = cα → q * cqα / (1 - cqq * 0 / J) - cα = 0) := by
  constructor
  · intro h; simp; linarith
  · intro h; simp [h]

/-- The condition `c_α > q c_qα` is `∂MC/∂α < ∂(c/q)/∂α`. -/
theorem exercise_10_C_8b_AC {cqα cα q : ℝ} (hq : 0 < q) : q * cqα < cα ↔ cqα < cα / q := by
  rw [lt_div_iff₀ hq, mul_comm]

/-- **Exercise 10.C.8(c)** (MWG, p. 346). When `α = w_k`, Shephard's lemma (Chapter 5,
Proposition 5.C.2(vi)) gives `c_α = z_k(w, q)` and `c_qα = ∂z_k/∂q`; the condition becomes
`z_k > q ∂z_k/∂q`: the output elasticity of the conditional demand for factor `k` is below one. -/
theorem exercise_10_C_8c {zk dzk q : ℝ} (hz : 0 < zk) :
    q * dzk < zk ↔ q * dzk / zk < 1 := by
  rw [div_lt_one hz]

/-- **Exercise 10.C.9** (MWG, p. 346). With `J` identical firms (`c_qq ≥ 0`) and demand slope
`x' ≤ 0`, the equilibrium price response to `w_k` is `p' = c_qk/(1 - c_qq x'/J)`; by Shephard's
lemma `c_qk = ∂z_k/∂q`. Hence `p' < 0` iff factor `k` is inferior (`∂z_k/∂q < 0`). -/
theorem exercise_10_C_9 {J cqq dzk d p' : ℝ} (hJ : 0 < J) (hcqq : 0 ≤ cqq) (hd : d ≤ 0)
    (hp : p' * (1 - cqq * d / J) = dzk) : p' < 0 ↔ dzk < 0 := by
  have hD : 0 < 1 - cqq * d / J := by
    have : cqq * d / J ≤ 0 := div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos
      hcqq hd) hJ.le
    linarith
  rw [← hp]
  constructor
  · intro h; exact mul_neg_of_neg_of_pos h hD
  · intro h; by_contra hge; push Not at hge; nlinarith

/-! ## Exercise 10.C.10 -/

/-- **Exercise 10.C.10** (MWG, p. 346). With demand `x(p) = αp^ε` and marginal cost
`c'(q) = βq^η` for each of `J` firms (`α, β, η > 0`, `ε < 0`), the equilibrium conditions
`p = βq^η`, `αp^ε = Jq` are, in logarithms, linear; their unique solution is
`ln p = (ln J - ln α - (1/η) ln β)/(ε - 1/η)`, `ln q = (ln p - ln β)/η`. -/
theorem exercise_10_C_10 {α β η ε J p q : ℝ} (hα : 0 < α) (hβ : 0 < β) (hη : 0 < η)
    (hε : ε < 0) (hJ : 0 < J) (hp : 0 < p) (hq : 0 < q) :
    (p = β * q ^ η ∧ α * p ^ ε = J * q) ↔
      (Real.log p = (Real.log J - Real.log α - Real.log β / η) / (ε - 1 / η) ∧
        Real.log q = (Real.log p - Real.log β) / η) := by
  have hden : ε - 1 / η ≠ 0 := by have : 0 < 1 / η := by positivity
                                  linarith
  have hlogs : (p = β * q ^ η ↔ Real.log p = Real.log β + η * Real.log q) ∧
      (α * p ^ ε = J * q ↔ Real.log α + ε * Real.log p = Real.log J + Real.log q) := by
    constructor
    · constructor
      · intro h; rw [h, Real.log_mul hβ.ne' (Real.rpow_pos_of_pos hq η).ne', Real.log_rpow hq]
      · intro h
        apply Real.log_injOn_pos (Set.mem_Ioi.2 hp)
          (Set.mem_Ioi.2 (mul_pos hβ (Real.rpow_pos_of_pos hq η)))
        rw [h, Real.log_mul hβ.ne' (Real.rpow_pos_of_pos hq η).ne', Real.log_rpow hq]
    · constructor
      · intro h
        have := congrArg Real.log h
        rwa [Real.log_mul hα.ne' (Real.rpow_pos_of_pos hp ε).ne', Real.log_rpow hp,
          Real.log_mul hJ.ne' hq.ne'] at this
      · intro h
        apply Real.log_injOn_pos (Set.mem_Ioi.2 (mul_pos hα (Real.rpow_pos_of_pos hp ε)))
          (Set.mem_Ioi.2 (mul_pos hJ hq))
        rw [Real.log_mul hα.ne' (Real.rpow_pos_of_pos hp ε).ne', Real.log_rpow hp,
          Real.log_mul hJ.ne' hq.ne', h]
  rw [hlogs.1, hlogs.2]
  constructor
  · rintro ⟨h1, h2⟩
    have hq' : Real.log q = (Real.log p - Real.log β) / η := by
      rw [eq_div_iff hη.ne']; linarith
    refine ⟨?_, hq'⟩
    rw [eq_div_iff hden]
    rw [hq'] at h2
    field_simp at h2 ⊢
    linarith
  · rintro ⟨h1, h2⟩
    have e1 : Real.log p = Real.log β + η * Real.log q := by
      rw [h2]; field_simp; ring
    refine ⟨e1, ?_⟩
    rw [eq_div_iff hden] at h1
    rw [h2]
    field_simp at h1 ⊢
    linarith

/-- **Exercise 10.C.10** (MWG, p. 346): comparative statics. The elasticities of the
equilibrium price with respect to `α` and `β` are `η/(1 - εη) > 0` and `1/(1 - εη) > 0` (the
coefficients of `ln α`, `ln β` in `ln p`); those of output per firm are `1/(1 - εη) > 0` and
`ε/(1 - εη) < 0`. Both price elasticities shrink as demand becomes more elastic (`ε` more
negative). -/
theorem exercise_10_C_10_statics {η ε : ℝ} (hη : 0 < η) (hε : ε < 0) :
    -1 / (ε - 1 / η) = η / (1 - ε * η) ∧ -(1 / η) / (ε - 1 / η) = 1 / (1 - ε * η) ∧
      0 < η / (1 - ε * η) ∧ 0 < 1 / (1 - ε * η) ∧
      (1 / η) * (-1 / (ε - 1 / η)) = 1 / (1 - ε * η) ∧
      (1 / η) * (-(1 / η) / (ε - 1 / η) - 1) = ε / (1 - ε * η) ∧ ε / (1 - ε * η) < 0 ∧
      ∀ ε', ε' < ε → η / (1 - ε' * η) < η / (1 - ε * η) := by
  have h1 : 0 < 1 - ε * η := by nlinarith
  have hd : ε - 1 / η ≠ 0 := by
    have : 0 < 1 / η := by positivity
    linarith
  have ha : -1 / (ε - 1 / η) = η / (1 - ε * η) := by
    rw [div_eq_div_iff hd h1.ne']; field_simp; ring
  have hb : -(1 / η) / (ε - 1 / η) = 1 / (1 - ε * η) := by
    rw [div_eq_div_iff hd h1.ne']; field_simp; ring
  refine ⟨ha, hb, by positivity, by positivity, ?_, ?_, div_neg_of_neg_of_pos hε h1,
    fun ε' hε' => ?_⟩
  · rw [ha]; field_simp
  · rw [hb, div_sub_one h1.ne', show 1 - (1 - ε * η) = ε * η by ring, ← mul_div_assoc,
      show 1 / η * (ε * η) = ε by field_simp]
  · have h3 : 0 < 1 - ε' * η := by nlinarith
    rw [div_lt_div_iff₀ h3 h1]
    nlinarith [mul_lt_mul_of_pos_right hε' (by positivity : (0 : ℝ) < η ^ 2)]

/-! ## Exercise 10.C.11 -/

/-- **Exercise 10.C.11** (MWG, p. 346). A price-taking firm with cost `c(q, α)` facing price `p`,
whose output `q(α)` satisfies `p = c_q(q(α), α)`, has profit `π(α) = p q(α) - c(q(α), α)` with
`π'(α) = -c_α(q, α)` (envelope theorem). Hence if `α₁` and `α₂` differ marginally, the two firms'
profits differ by `π₁ - π₂ ≈ -c_α (α₁ - α₂)`. -/
theorem exercise_10_C_11 {c : ℝ × ℝ → ℝ} {q : ℝ → ℝ} {p cα q' α₀ : ℝ}
    (hc : HasFDerivAt c (p • ContinuousLinearMap.fst ℝ ℝ ℝ + cα • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (q α₀, α₀))
    (hq : HasDerivAt q q' α₀) :
    HasDerivAt (fun α => p * q α - c (q α, α)) (-cα) α₀ := by
  have h := (hq.const_mul p).sub (hasDerivAt_comp_pair hc hq)
  convert h using 1
  ring

end MWG.CompetitiveMarkets

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercises 10.E.1 and 10.E.3; the representative-consumer remarks of Section 10.E

* Small type, pp. 333-334: for a quasilinear consumer the indirect utility is
  `v(p, w) = w + [φ(x(p)) - p x(p)]`, so the compensating and the equivalent variations of a
  price change coincide and equal the change in consumer surplus.
* **Exercise 10.E.1** (tariffs): domestic Marshallian surplus `W(τ)` changes at rate
  `τ Q_f' - s' Q_f`; (a) with strictly convex foreign costs the foreign price falls with a tariff
  and a small tariff raises domestic welfare; (b) with constant-returns foreign costs a small
  tariff lowers it.
* **Exercise 10.E.3** (Ramsey taxes): (a) tax vectors with the same effective prices raise the
  same revenue, so good 1 can be left untaxed; (b) the marginal deadweight loss of a tax on good
  `ℓ` is `-t x'`, and the Lagrange conditions give the inverse elasticity rule
  `t_ℓ/(c_ℓ + t_ℓ) = (λ/(1 + λ))/|ε_ℓ|`; (c) equal rates iff equal elasticities, higher rates on
  less elastic goods, and a tax on good 1 alone is a uniform proportional tax on all goods.
-/

namespace MWG.CompetitiveMarkets

open Filter Topology MeasureTheory

/-! ## Quasilinear indirect utility (pp. 333-334) -/

/-- **(MWG, pp. 333-334)** The indirect utility of a quasilinear consumer (consumption set
`ℝ × ℝ₊`) at price `p > 0` and wealth `w` is `w + [φ(x(p)) - p x(p)]`. -/
theorem ql_indirect_utility (C : QLConsumer) {p : ℝ} (hp : 0 < p) (w : ℝ) :
    IsGreatest {u | ∃ m x : ℝ, 0 ≤ x ∧ m + p * x ≤ w ∧ u = m + C.φ x}
      (w + (C.φ (C.demand p) - p * C.demand p)) := by
  refine ⟨⟨w - p * C.demand p, C.demand p, C.demand_nonneg hp, by linarith, by ring⟩, ?_⟩
  rintro u ⟨m, x, hx, hb, rfl⟩
  have := C.demand_max hp x hx
  linarith

/-- **(MWG, p. 334)** For a quasilinear consumer, the compensating and equivalent variations of a
price change from `p₀` to `p₁` coincide and equal the change in consumer surplus
`[φ(x(p₁)) - p₁x(p₁)] - [φ(x(p₀)) - p₀x(p₀)]`: with this transfer, utility at `p₁` equals utility
at `p₀` without it, at every wealth level. -/
theorem ql_cv_eq_ev (C : QLConsumer) (p₀ p₁ w : ℝ) :
    let v : ℝ → ℝ → ℝ := fun p w => w + (C.φ (C.demand p) - p * C.demand p)
    let Δ := (C.φ (C.demand p₁) - p₁ * C.demand p₁) - (C.φ (C.demand p₀) - p₀ * C.demand p₀)
    v p₁ (w - Δ) = v p₀ w ∧ v p₀ (w + Δ) = v p₁ w := by
  intro v Δ
  constructor <;> simp only [v, Δ] <;> ring

/-! ## A two-path chain rule -/

/-- The chain rule for `t ↦ f(g₁(t), g₂(t))` with partial derivatives `a`, `b`. -/
theorem hasDerivAt_comp_two {f : ℝ × ℝ → ℝ} {a b : ℝ} {g₁ g₂ : ℝ → ℝ} {g₁' g₂' t₀ : ℝ}
    (hf : HasFDerivAt f (a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (g₁ t₀, g₂ t₀))
    (h₁ : HasDerivAt g₁ g₁' t₀) (h₂ : HasDerivAt g₂ g₂' t₀) :
    HasDerivAt (fun t => f (g₁ t, g₂ t)) (a * g₁' + b * g₂') t₀ := by
  have h := HasFDerivAt.comp_hasDerivAt (f := fun t => (g₁ t, g₂ t)) t₀ hf (h₁.prodMk h₂)
  simp only [add_apply, smul_apply, ContinuousLinearMap.coe_fst', smul_eq_mul,
    ContinuousLinearMap.coe_snd'] at h
  exact h

/-! ## Exercise 10.E.1 -/

/-- **Exercise 10.E.1** (MWG, p. 346). Domestic Marshallian surplus with an import tariff `τ`:
`W(τ) = B(X(τ)) - C_d(Q_d(τ)) - s(τ) Q_f(τ)` (domestic consumers' gross benefit, minus domestic
costs, minus payments to foreign firms at their price `s = p - τ`; tariff revenue stays at home),
with `X = Q_d + Q_f`. If consumers and domestic firms are price takers (`B' = C_d' = p`), then
`W'(τ) = τ Q_f'(τ) - s'(τ) Q_f(τ)`. -/
theorem exercise_10_E_1_deriv {B Cd Qd Qf s : ℝ → ℝ} {τ₀ p Qd' Qf' s' : ℝ}
    (hB : HasDerivAt B p (Qd τ₀ + Qf τ₀)) (hC : HasDerivAt Cd p (Qd τ₀))
    (hQd : HasDerivAt Qd Qd' τ₀) (hQf : HasDerivAt Qf Qf' τ₀) (hs : HasDerivAt s s' τ₀)
    (hsp : s τ₀ = p - τ₀) :
    HasDerivAt (fun τ => B (Qd τ + Qf τ) - Cd (Qd τ) - s τ * Qf τ)
      (τ₀ * Qf' - s' * Qf τ₀) τ₀ := by
  have h := ((hB.comp τ₀ (hQd.add hQf)).sub (hC.comp τ₀ hQd)).sub (hs.mul hQf)
  exact h.congr_deriv (by rw [hsp]; ring)

/-- **Exercise 10.E.1** (MWG, p. 346), the foreign price. Differentiating market clearing
`x(s + τ) = q_d(s + τ) + q_f(s)` gives `s'(τ) = -(x' - q_d')/(x' - q_d' - q_f')`; with
`x' ≤ q_d'`... more precisely `x' - q_d' < 0` and a strictly increasing foreign supply
(`q_f' > 0`, strictly convex foreign costs), `-1 < s' < 0`. -/
theorem exercise_10_E_1_foreign_price {x' qd' qf' s' : ℝ} (hd : x' - qd' < 0) (hf : 0 < qf')
    (hclear : x' * (s' + 1) = qd' * (s' + 1) + qf' * s') :
    s' = -(x' - qd') / (x' - qd' - qf') ∧ -1 < s' ∧ s' < 0 := by
  have hden : x' - qd' - qf' < 0 := by linarith
  have hs : s' = -(x' - qd') / (x' - qd' - qf') := by
    rw [eq_div_iff hden.ne]; linarith
  refine ⟨hs, ?_, ?_⟩
  · rw [hs, lt_div_iff_of_neg hden]; linarith
  · rw [hs]; exact div_neg_of_pos_of_neg (by linarith) hden

/-- **Exercise 10.E.1(a)** (MWG, p. 346). With strictly convex foreign costs (`s'(0) < 0`) and
positive imports, `W'(0) = -s'(0)Q_f(0) > 0`, so a small tariff raises domestic welfare. -/
theorem exercise_10_E_1a {W : ℝ → ℝ} {s' Qf0 Qf' : ℝ}
    (hW : HasDerivAt W (0 * Qf' - s' * Qf0) 0) (hs : s' < 0) (hQ : 0 < Qf0) :
    ∃ δ > 0, ∀ τ, 0 < τ → τ < δ → W 0 < W τ := by
  have hpos : 0 < 0 * Qf' - s' * Qf0 := by nlinarith
  have hsl := hW.tendsto_slope_zero_right
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t⁻¹ • (W (0 + t) - W 0) :=
    hsl.eventually (lt_mem_nhds hpos)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hev)
  refine ⟨δ, hδ, fun τ hτ hτδ => ?_⟩
  have := hball (by simpa [Real.dist_eq, abs_of_pos hτ] using hτδ) hτ
  simp only [zero_add, smul_eq_mul] at this
  have := (mul_pos_iff_of_pos_left (inv_pos.2 hτ)).1 this
  linarith

/-- **Exercise 10.E.1(b)** (MWG, p. 346). With constant-returns foreign costs the foreign price is
fixed (`s' = 0`), so `W'(τ) = τ Q_f'(τ)`; if imports fall with the tariff (`Q_f' < 0`) on
`(0, δ)`, then a small tariff lowers domestic welfare: `W(τ) < W(0)` for `0 < τ ≤ δ`. -/
theorem exercise_10_E_1b {W Qf' : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hW : ∀ τ ∈ Set.Icc 0 δ, HasDerivAt W (τ * Qf' τ - 0 * 1) τ)
    (hQ : ∀ τ ∈ Set.Ioo 0 δ, Qf' τ < 0) : ∀ τ, 0 < τ → τ ≤ δ → W τ < W 0 := by
  have hanti : StrictAntiOn W (Set.Icc 0 δ) := by
    refine strictAntiOn_of_hasDerivWithinAt_neg (f' := fun τ => τ * Qf' τ - 0 * 1)
      (convex_Icc 0 δ)
      (fun τ hτ => (hW τ hτ).continuousAt.continuousWithinAt) (fun τ hτ => ?_) (fun τ hτ => ?_)
    · rw [interior_Icc] at hτ
      exact (hW τ (Set.Ioo_subset_Icc_self hτ)).hasDerivWithinAt
    · rw [interior_Icc] at hτ
      have := hQ τ hτ
      nlinarith [hτ.1]
  intro τ hτ hτδ
  exact hanti ⟨le_rfl, hδ.le⟩ ⟨hτ.le, hτδ⟩ hτ

/-! ## Exercise 10.E.3: Ramsey taxes -/

/-- **Exercise 10.E.3(a)** (MWG, p. 347). Effective prices `(1 + t₁)(c_ℓ + t_ℓ)` (in units of
good 1) determine demands and revenue `R = ∑ [(1 + t₁)(c_ℓ + t_ℓ) - c_ℓ] x_ℓ`. If
`c_ℓ + t'_ℓ = a(c_ℓ + t_ℓ)` and `1 + t'₁ = (1/a)(1 + t₁)` (`a > 0`), effective prices, demands and
revenue coincide. In particular `a = 1 + t₁` gives an equivalent tax vector with `t'₁ = 0`. -/
theorem exercise_10_E_3a {n : ℕ} (x : Fin n → ℝ → ℝ) (c t t' : Fin n → ℝ) (t₁ t₁' a : ℝ)
    (ha : 0 < a) (ht : ∀ l, c l + t' l = a * (c l + t l)) (ht₁ : 1 + t₁' = (1 / a) * (1 + t₁)) :
    (∀ l, (1 + t₁') * (c l + t' l) = (1 + t₁) * (c l + t l)) ∧
      ∑ l, ((1 + t₁') * (c l + t' l) - c l) * x l ((1 + t₁') * (c l + t' l)) =
        ∑ l, ((1 + t₁) * (c l + t l) - c l) * x l ((1 + t₁) * (c l + t l)) := by
  have he : ∀ l, (1 + t₁') * (c l + t' l) = (1 + t₁) * (c l + t l) := fun l => by
    rw [ht, ht₁]; field_simp
  exact ⟨he, Finset.sum_congr rfl fun l _ => by rw [he]⟩

/-- **Exercise 10.E.3(a)**: normalization `t'₁ = 0` with `t'_ℓ = (1 + t₁)(c_ℓ + t_ℓ) - c_ℓ`. -/
theorem exercise_10_E_3a_normalize {n : ℕ} (c t : Fin n → ℝ) {t₁ : ℝ} (ht₁ : -1 < t₁) :
    (∀ l, c l + ((1 + t₁) * (c l + t l) - c l) = (1 + t₁) * (c l + t l)) ∧
      1 + 0 = (1 / (1 + t₁)) * (1 + t₁) := by
  refine ⟨fun l => by ring, ?_⟩
  have : 1 + t₁ ≠ 0 := by linarith
  rw [one_div, inv_mul_cancel₀ this]; ring

/-- **Exercise 10.E.3(b)** (MWG, p. 347): the marginal deadweight loss. With `t₁ = 0`,
consumer price `c + t` and continuous demand `x` differentiable at `c + t`, the deadweight loss
`D(t) = ∫_c^{c+t} x - t x(c + t)` of the tax on one good (loss of consumer surplus minus
revenue; constant returns, so no producer surplus) has `D'(t) = -t x'(c + t)`, and revenue
`t x(c + t)` has derivative `x(c + t) + t x'(c + t)`. -/
theorem exercise_10_E_3b_marginal {x : ℝ → ℝ} {c t d : ℝ} (hx : Continuous x)
    (hd : HasDerivAt x d (c + t)) :
    HasDerivAt (fun t => (∫ s in c..c + t, x s) - t * x (c + t)) (-t * d) t ∧
      HasDerivAt (fun t => t * x (c + t)) (x (c + t) + t * d) t := by
  have hshift : HasDerivAt (fun t : ℝ => c + t) 1 t := by
    simpa using (hasDerivAt_id t).const_add c
  have hI : HasDerivAt (fun t => ∫ s in c..c + t, x s) (x (c + t)) t := by
    have h := ((hx.integral_hasStrictDerivAt c (c + t)).hasDerivAt).comp t hshift
    rw [mul_one] at h
    exact h
  have hxc : HasDerivAt (fun t => x (c + t)) d t := by
    have h := hd.comp t hshift
    rw [mul_one] at h
    exact h
  have hR : HasDerivAt (fun t => t * x (c + t)) (x (c + t) + t * d) t := by
    have h := (hasDerivAt_id t).mul hxc
    exact h.congr_deriv (by simp)
  refine ⟨?_, hR⟩
  convert hI.sub hR using 1
  ring

/-- **Exercise 10.E.3(b)** (MWG, p. 347): the Ramsey (inverse elasticity) rule. If at the optimal
taxes the Lagrange condition `D'_ℓ = λ R'_ℓ` holds, i.e. `-t_ℓ x_ℓ' = λ(x_ℓ + t_ℓ x_ℓ')`, with
`x_ℓ > 0`, `x_ℓ' < 0` and `λ ≠ -1`, then
`t_ℓ/p_ℓ = (λ/(1 + λ)) · (1/|ε_ℓ|)` with `p_ℓ = c_ℓ + t_ℓ > 0` and `ε_ℓ = p_ℓ x_ℓ'/x_ℓ`. -/
theorem exercise_10_E_3b {t p xl dxl lam : ℝ} (hp : 0 < p) (hx : 0 < xl) (hd : dxl < 0)
    (hlam : 1 + lam ≠ 0) (hfoc : -t * dxl = lam * (xl + t * dxl)) :
    t / p = lam / (1 + lam) * (1 / |p * dxl / xl|) := by
  have hε : p * dxl / xl < 0 := div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hp hd) hx
  rw [abs_of_neg hε]
  have h1 : (1 + lam) ≠ 0 := hlam
  have h2 : dxl ≠ 0 := hd.ne
  have ht : t = -lam * xl / ((1 + lam) * dxl) := by
    rw [eq_div_iff (mul_ne_zero h1 h2)]; linarith
  rw [ht]
  field_simp

/-- **Exercise 10.E.3(c)** (MWG, p. 347). By the Ramsey rule the optimal proportional rate
`t_ℓ/p_ℓ = k/|ε_ℓ|` (`k = λ/(1+λ) > 0`) is the same for two goods iff their elasticities are
equal, and is higher for the less elastic good. -/
theorem exercise_10_E_3c {k e₁ e₂ : ℝ} (hk : 0 < k) (h₁ : 0 < e₁) :
    (k * (1 / e₁) = k * (1 / e₂) ↔ e₁ = e₂) ∧ (e₁ < e₂ → k * (1 / e₂) < k * (1 / e₁)) := by
  refine ⟨⟨fun h => ?_, fun h => by rw [h]⟩, fun h => ?_⟩
  · have := mul_left_cancel₀ hk.ne' h
    rw [one_div, one_div, inv_inj] at this
    exact this
  · exact mul_lt_mul_of_pos_left (one_div_lt_one_div_of_lt h₁ h) hk

/-- **Exercise 10.E.3(c)** (MWG, p. 347). Taxing only good 1 (`t₁ > 0`, `t_ℓ = 0`) is, by part (a),
equivalent to taxing every good `ℓ ≠ 1` at the uniform proportional rate `t₁/(1 + t₁)` of its
consumer price; by the Ramsey rule it is optimal only if all elasticities are equal at the
optimum. -/
theorem exercise_10_E_3c_good_one {n : ℕ} (c : Fin n → ℝ) (hc : ∀ l, 0 < c l) {t₁ : ℝ}
    (ht₁ : 0 < t₁) (l : Fin n) :
    ((1 + t₁) * (c l + 0) - c l) / ((1 + t₁) * (c l + 0)) = t₁ / (1 + t₁) := by
  have := hc l
  field_simp
  ring

end MWG.CompetitiveMarkets

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Derived equilibrium paths and Lagrange multipliers (Exercises 10.C.5, 10.E.1, 10.E.3)

This module removes the assumed ingredients of three exercises.

* `implicit_1d`: a one-variable implicit function theorem. If `A(s(τ) + τ) = B(s(τ))` near `τ₀`,
  `s` is continuous at `τ₀`, `A' = a`, `B' = b` and `b ≠ a`, then `s'(τ₀) = a/(b - a)`.
* `implicit_path`: with `N` continuous and nonincreasing and `S` continuous and strictly
  increasing, the equation `N(s + τ) = S(s)` has, for `τ` near `0`, a unique solution `s(τ)`,
  continuous at `0`.
* **Exercise 10.C.5**: in the model of Section 10.C, the equilibrium paths `xᵢ(t)`, `qⱼ(t)`,
  `p*(t)` are derived to be differentiable and to satisfy (10.C.4)-(10.C.6) near `t = 0`
  (`exercise_10_C_5_derived`).
* **Exercise 10.E.1(a)**: the foreign price path under a tariff is derived (`implicit_path`,
  `implicit_1d`) and a small tariff raises domestic welfare (`exercise_10_E_1a_derived`).
* **Exercise 10.E.3(b)**: the Lagrange multiplier exists at a constrained optimum (Mathlib's
  `IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt_1d`), so the Ramsey rule holds
  unconditionally (`exercise_10_E_3b_lagrange`).
-/

namespace MWG.CompetitiveMarkets

open Filter Topology MeasureTheory

/-! ## A one-variable implicit function theorem -/

/-- **Implicit differentiation in one variable.** If `A(s(τ) + τ) = B(s(τ))` for `τ` near `τ₀`,
`s` is continuous at `τ₀`, `A` has derivative `a` at `s(τ₀) + τ₀`, `B` has derivative `b` at
`s(τ₀)` and `b ≠ a`, then `s` is differentiable at `τ₀` with `s'(τ₀) = a/(b - a)`. -/
theorem implicit_1d {A B s : ℝ → ℝ} {τ₀ a b : ℝ} (hs : ContinuousAt s τ₀)
    (hA : HasDerivAt A a (s τ₀ + τ₀)) (hB : HasDerivAt B b (s τ₀)) (hab : b - a ≠ 0)
    (heq : ∀ᶠ τ in 𝓝 τ₀, A (s τ + τ) = B (s τ)) : HasDerivAt s (a / (b - a)) τ₀ := by
  set y₀ := s τ₀ + τ₀
  have hg : Tendsto (fun τ => s τ + τ) (𝓝 τ₀) (𝓝 y₀) := hs.add continuousAt_id
  have rA := (remainder_isLittleO hA).comp_tendsto hg
  have rB := (remainder_isLittleO hB).comp_tendsto hs
  simp only [Function.comp_def] at rA rB
  -- notation: `u = s τ - s τ₀`, `v = τ - τ₀`
  have hk : 0 < |b - a| := abs_pos.2 hab
  set ε := |b - a| / 4 with hε
  have hε0 : 0 < ε := by positivity
  have hAb := rA.bound hε0
  have hBb := rB.bound hε0
  have heq0 : A y₀ = B (s τ₀) := heq.self_of_nhds
  -- `u = O(v)`
  have hO : (fun τ => s τ - s τ₀) =O[𝓝 τ₀] fun τ => τ - τ₀ := by
    refine Asymptotics.IsBigO.of_bound ((|a| + ε) / (|b - a| / 2)) ?_
    filter_upwards [hAb, hBb, heq] with τ h1 h2 h3
    simp only [Real.norm_eq_abs] at h1 h2 ⊢
    set u := s τ - s τ₀
    set v := τ - τ₀
    have key : (b - a) * u - a * v = (A (s τ + τ) - A y₀ - (s τ + τ - y₀) * a) -
        (B (s τ) - B (s τ₀) - (s τ - s τ₀) * b) := by
      simp only [u, v, y₀]; rw [h3, heq0]; ring
    have huv : |s τ + τ - y₀| ≤ |u| + |v| := by
      have : s τ + τ - y₀ = u + v := by simp only [u, v, y₀]; ring
      rw [this]; exact abs_add_le u v
    have h4 : |b - a| * |u| ≤ |a| * |v| + ε * (|u| + |v|) + ε * |u| := by
      have e1 : |(b - a) * u| ≤ |a * v| + |A (s τ + τ) - A y₀ - (s τ + τ - y₀) * a| +
          |B (s τ) - B (s τ₀) - (s τ - s τ₀) * b| := by
        have : (b - a) * u = a * v + ((A (s τ + τ) - A y₀ - (s τ + τ - y₀) * a) -
            (B (s τ) - B (s τ₀) - (s τ - s τ₀) * b)) := by linarith
        rw [this, abs_le]
        set Y := A (s τ + τ) - A y₀ - (s τ + τ - y₀) * a
        set Z := B (s τ) - B (s τ₀) - (s τ - s τ₀) * b
        have := le_abs_self (a * v); have := neg_abs_le (a * v)
        have := le_abs_self Y; have := neg_abs_le Y
        have := le_abs_self Z; have := neg_abs_le Z
        constructor <;> linarith
      rw [abs_mul, abs_mul] at e1
      nlinarith [h1, h2, huv, hε0.le]
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith [abs_nonneg u, abs_nonneg v]
  have huv : (fun τ => s τ + τ - y₀) =O[𝓝 τ₀] fun τ => τ - τ₀ := by
    have : (fun τ => s τ + τ - y₀) = fun τ => (s τ - s τ₀) + (τ - τ₀) := by
      funext τ; simp only [y₀]; ring
    rw [this]
    exact hO.add (Asymptotics.isBigO_refl _ _)
  have rA' := rA.trans_isBigO huv
  have rB' := rB.trans_isBigO hO
  rw [hasDerivAt_iff_isLittleO]
  have hdiff := (rA'.sub rB').const_mul_left (1 / (b - a))
  refine hdiff.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [heq] with τ h3
  simp only [smul_eq_mul]
  rw [h3, heq0]
  field_simp
  ring

/-! ## Existence and continuity of an equilibrium path -/

/-- **An equilibrium path.** Let `N` be continuous and nonincreasing and `S` continuous and
strictly increasing with `N(s₀) = S(s₀)`. Then for `τ` near `0` the equation `N(s + τ) = S(s)` has
a solution `s(τ)` (unique for every `τ`), with `s(0) = s₀` and `s` continuous at `0`. -/
theorem implicit_path {N S : ℝ → ℝ} (hN : Continuous N) (hNa : Antitone N) (hS : Continuous S)
    (hSm : StrictMono S) {s₀ : ℝ} (h0 : N s₀ = S s₀) :
    ∃ s : ℝ → ℝ, s 0 = s₀ ∧ (∀ᶠ τ in 𝓝 (0 : ℝ), N (s τ + τ) = S (s τ)) ∧ ContinuousAt s 0 ∧
      ∀ τ y, N (y + τ) = S y → s τ = y := by
  classical
  -- uniqueness of solutions
  have huniq : ∀ τ y₁ y₂, N (y₁ + τ) = S y₁ → N (y₂ + τ) = S y₂ → y₁ = y₂ := by
    intro τ y₁ y₂ h₁ h₂
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := hNa (by linarith : y₁ + τ ≤ y₂ + τ); have := hSm hlt; linarith
    · have := hNa (by linarith : y₂ + τ ≤ y₁ + τ); have := hSm hlt; linarith
  set s : ℝ → ℝ := fun τ => if h : ∃ y, N (y + τ) = S y then h.choose else s₀ with hsdef
  have hspec : ∀ τ, (∃ y, N (y + τ) = S y) → N (s τ + τ) = S (s τ) := by
    intro τ h
    simp only [hsdef, dite_eq_left_of_eq_true (eq_true h)]
    exact h.choose_spec
  have hsol : ∀ τ y, N (y + τ) = S y → s τ = y := fun τ y hy =>
    huniq τ _ _ (hspec τ ⟨y, hy⟩) hy
  -- brackets
  have hbr : ∀ ε, 0 < ε → ∀ᶠ τ in 𝓝 (0 : ℝ),
      S (s₀ - ε) < N (s₀ - ε + τ) ∧ N (s₀ + ε + τ) < S (s₀ + ε) := by
    intro ε hε
    have hl : S (s₀ - ε) < N (s₀ - ε + 0) := by
      rw [add_zero]
      have := hNa (by linarith : s₀ - ε ≤ s₀); have := hSm (by linarith : s₀ - ε < s₀)
      linarith
    have hr : N (s₀ + ε + 0) < S (s₀ + ε) := by
      rw [add_zero]
      have := hNa (by linarith : s₀ ≤ s₀ + ε); have := hSm (by linarith : s₀ < s₀ + ε)
      linarith
    have c1 : ContinuousAt (fun τ => N (s₀ - ε + τ)) 0 :=
      (hN.comp (continuous_const.add continuous_id)).continuousAt
    have c2 : ContinuousAt (fun τ => N (s₀ + ε + τ)) 0 :=
      (hN.comp (continuous_const.add continuous_id)).continuousAt
    exact (c1.eventually (lt_mem_nhds hl)).and (c2.eventually (gt_mem_nhds hr))
  -- inside a bracket the solution exists and lies in it
  have hin : ∀ ε, 0 < ε → ∀ τ, S (s₀ - ε) < N (s₀ - ε + τ) → N (s₀ + ε + τ) < S (s₀ + ε) →
      N (s τ + τ) = S (s τ) ∧ s₀ - ε < s τ ∧ s τ < s₀ + ε := by
    intro ε hε τ h1 h2
    have hc : ContinuousOn (fun y => N (y + τ) - S y) (Set.Icc (s₀ - ε) (s₀ + ε)) :=
      ((hN.comp (continuous_id.add continuous_const)).sub hS).continuousOn
    obtain ⟨y, hy, hyz⟩ := intermediate_value_Icc' (by linarith : s₀ - ε ≤ s₀ + ε) hc
      ⟨by change N (s₀ + ε + τ) - S (s₀ + ε) ≤ 0; linarith,
        by change 0 ≤ N (s₀ - ε + τ) - S (s₀ - ε); linarith⟩
    have hy' : N (y + τ) = S y := by simp only at hyz; linarith
    have e := hsol τ y hy'
    rw [e]
    refine ⟨hy', lt_of_le_of_ne hy.1 fun h => ?_, lt_of_le_of_ne hy.2 fun h => ?_⟩
    · rw [← h] at hy'; linarith
    · rw [h] at hy'; linarith
  have hs0 : s 0 = s₀ := hsol 0 s₀ (by rw [add_zero, h0])
  refine ⟨s, hs0, ?_, ?_, hsol⟩
  · filter_upwards [hbr 1 one_pos] with τ hτ
    exact (hin 1 one_pos τ hτ.1 hτ.2).1
  · rw [ContinuousAt, hs0, Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [hbr ε hε] with τ hτ
    obtain ⟨-, h1, h2⟩ := hin ε hε τ hτ.1 hτ.2
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith

/-! ## Exercise 10.E.1(a), derived -/

/-- **Exercise 10.E.1(a)** (MWG, p. 346), with the equilibrium path derived. Let domestic demand
`D` and domestic supply `S_d` give a continuous nonincreasing net demand `D - S_d`, and let
foreign supply `S_f` be continuous and strictly increasing (strictly convex foreign costs), with
free-trade equilibrium price `s₀` (`D(s₀) - S_d(s₀) = S_f(s₀)`, imports `S_f(s₀) > 0`). Then the
foreign price `s(τ)` under a tariff `τ` (consumer and domestic-firm price `s(τ) + τ`) is
well defined near `τ = 0` and differentiable at `0` with `s'(0) = (d - s_d)/(s_f - d + s_d) < 0`,
and with price-taking consumers and domestic firms (`B' = C_d' = p`) a small tariff raises
domestic welfare `W(τ) = B(Q_d + Q_f) - C_d(Q_d) - s Q_f`. -/
theorem exercise_10_E_1a_derived {D Sd Sf B Cd : ℝ → ℝ} {s₀ d sd sf : ℝ}
    (hN : Continuous fun p => D p - Sd p) (hNa : Antitone fun p => D p - Sd p)
    (hSf : Continuous Sf) (hSfm : StrictMono Sf) (h0 : D s₀ - Sd s₀ = Sf s₀)
    (hD : HasDerivAt D d s₀) (hSd : HasDerivAt Sd sd s₀) (hSf' : HasDerivAt Sf sf s₀)
    (hsf : 0 < sf) (hdsd : d - sd < 0) (hQf : 0 < Sf s₀)
    (hB : HasDerivAt B s₀ (Sd s₀ + Sf s₀)) (hC : HasDerivAt Cd s₀ (Sd s₀)) :
    ∃ s : ℝ → ℝ, s 0 = s₀ ∧
      (∀ᶠ τ in 𝓝 (0 : ℝ), D (s τ + τ) - Sd (s τ + τ) = Sf (s τ)) ∧
      HasDerivAt s ((d - sd) / (sf - (d - sd))) 0 ∧ (d - sd) / (sf - (d - sd)) < 0 ∧
      ∃ δ > 0, ∀ τ, 0 < τ → τ < δ →
        B (Sd (s 0 + 0) + Sf (s 0)) - Cd (Sd (s 0 + 0)) - s 0 * Sf (s 0) <
          B (Sd (s τ + τ) + Sf (s τ)) - Cd (Sd (s τ + τ)) - s τ * Sf (s τ) := by
  obtain ⟨s, hs0, heq, hcont, -⟩ := implicit_path hN hNa hSf hSfm h0
  have hab : sf - (d - sd) ≠ 0 := by linarith
  have hA : HasDerivAt (fun p => D p - Sd p) (d - sd) (s 0 + 0) := by
    rw [hs0, add_zero]; exact hD.sub hSd
  have hBd : HasDerivAt Sf sf (s 0) := by rw [hs0]; exact hSf'
  have hsd := implicit_1d hcont hA hBd hab heq
  have hneg : (d - sd) / (sf - (d - sd)) < 0 := div_neg_of_neg_of_pos hdsd (by linarith)
  refine ⟨s, hs0, heq, hsd, hneg, ?_⟩
  set s' := (d - sd) / (sf - (d - sd))
  have hpath : HasDerivAt (fun τ => s τ + τ) (s' + 1) 0 := hsd.add (hasDerivAt_id 0)
  have hQd : HasDerivAt (fun τ => Sd (s τ + τ)) (sd * (s' + 1)) 0 := by
    have h1 : HasDerivAt Sd sd (s 0 + 0) := by rw [hs0, add_zero]; exact hSd
    exact HasDerivAt.comp (h := fun τ => s τ + τ) (0 : ℝ) h1 hpath
  have hQf' : HasDerivAt (fun τ => Sf (s τ)) (sf * s') 0 := by
    have h1 : HasDerivAt Sf sf (s 0) := by rw [hs0]; exact hSf'
    exact HasDerivAt.comp (h := s) (0 : ℝ) h1 hsd
  have hW := exercise_10_E_1_deriv (B := B) (Cd := Cd) (Qd := fun τ => Sd (s τ + τ))
    (Qf := fun τ => Sf (s τ)) (s := s) (τ₀ := 0) (p := s₀)
    (by simpa [hs0] using hB) (by simpa [hs0] using hC) hQd hQf' hsd (by rw [hs0]; ring)
  exact exercise_10_E_1a hW hneg (by simpa [hs0] using hQf)

/-- **Instance of Exercise 10.E.1(a), derived**: demand `3 - p`, domestic supply `p`, foreign
supply `s`, gross benefit `3X - X²/2` and domestic cost `Q²/2`; free-trade price `1`. -/
theorem inst_exercise_10_E_1a :
    ∃ s : ℝ → ℝ, s 0 = 1 ∧ ∃ δ > 0, ∀ τ, 0 < τ → τ < δ →
      (3 * (s 0 + 0 + s 0) - (s 0 + 0 + s 0) ^ 2 / 2) - (s 0 + 0) ^ 2 / 2 - s 0 * s 0 <
        (3 * (s τ + τ + s τ) - (s τ + τ + s τ) ^ 2 / 2) - (s τ + τ) ^ 2 / 2 - s τ * s τ := by
  obtain ⟨s, hs0, -, -, -, δ, hδ, h⟩ := exercise_10_E_1a_derived (D := fun p => 3 - p)
    (Sd := fun p => p) (Sf := fun s => s) (B := fun X => 3 * X - X ^ 2 / 2)
    (Cd := fun Q => Q ^ 2 / 2) (s₀ := 1) (d := -1) (sd := 1) (sf := 1)
    (by fun_prop) (fun a b hab => by simp only; linarith) continuous_id strictMono_id
    (by norm_num) (by simpa using (hasDerivAt_id (1 : ℝ)).const_sub 3) (hasDerivAt_id 1)
    (hasDerivAt_id 1) one_pos (by norm_num) one_pos
    (by
      have := ((hasDerivAt_id (2 : ℝ)).const_mul 3).sub ((hasDerivAt_pow 2 (2 : ℝ)).div_const 2)
      norm_num at this ⊢; convert this using 1)
    (by
      have := (hasDerivAt_pow 2 (1 : ℝ)).div_const 2
      norm_num at this ⊢; exact this)
  exact ⟨s, hs0, δ, hδ, h⟩

/-! ## Exercise 10.E.3(b): existence of the Lagrange multiplier -/

/-- With a continuously differentiable demand, the deadweight loss and the revenue of a tax on one
good are strictly differentiable. -/
theorem ramsey_strict {x x' : ℝ → ℝ} (c : ℝ) (hx : ∀ s, HasDerivAt x (x' s) s)
    (hx'c : Continuous x') (t : ℝ) :
    HasStrictDerivAt (fun t => (∫ s in c..c + t, x s) - t * x (c + t)) (-t * x' (c + t)) t ∧
      HasStrictDerivAt (fun t => t * x (c + t)) (x (c + t) + t * x' (c + t)) t := by
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun s => (hx s).continuousAt
  have hshift : Continuous fun t : ℝ => c + t := continuous_const.add continuous_id
  constructor
  · refine hasStrictDerivAt_of_hasDerivAt_of_continuousAt (f' := fun t => -t * x' (c + t))
      (Eventually.of_forall fun y => (exercise_10_E_3b_marginal hxc (hx (c + y))).1) ?_
    exact (continuous_neg.mul (hx'c.comp hshift)).continuousAt
  · refine hasStrictDerivAt_of_hasDerivAt_of_continuousAt
      (f' := fun t => x (c + t) + t * x' (c + t))
      (Eventually.of_forall fun y => (exercise_10_E_3b_marginal hxc (hx (c + y))).2) ?_
    exact ((hxc.comp hshift).add (continuous_id.mul (hx'c.comp hshift))).continuousAt

/-- **Exercise 10.E.3(b)** (MWG, p. 347), unconditionally. Let goods `ℓ` have continuously
differentiable demands `x_ℓ` with `x_ℓ > 0` and `x_ℓ' < 0` at the optimal consumer prices
`c_ℓ + t_ℓ > 0`, and let `t` minimize the total deadweight loss
`∑ (∫_{c_ℓ}^{c_ℓ+t_ℓ} x_ℓ - t_ℓ x_ℓ(c_ℓ + t_ℓ))` locally among tax vectors raising the same revenue
`∑ t_ℓ x_ℓ(c_ℓ + t_ℓ)`, with some marginal revenue nonzero. Then a Lagrange multiplier `λ ≠ -1`
exists (Lagrange's theorem) and every tax satisfies the Ramsey rule
`t_ℓ/p_ℓ = (λ/(1 + λ))(1/|ε_ℓ|)`. -/
theorem exercise_10_E_3b_lagrange {n : ℕ} (c : Fin n → ℝ) (x x' : Fin n → ℝ → ℝ)
    (hx : ∀ l s, HasDerivAt (x l) (x' l s) s) (hx'c : ∀ l, Continuous (x' l)) (t : Fin n → ℝ)
    (hmin : IsLocalMinOn
      (fun t : Fin n → ℝ => ∑ l, ((∫ s in c l..c l + t l, x l s) - t l * x l (c l + t l)))
      {t' | ∑ l, t' l * x l (c l + t' l) = ∑ l, t l * x l (c l + t l)} t)
    (hp : ∀ l, 0 < c l + t l) (hxp : ∀ l, 0 < x l (c l + t l)) (hneg : ∀ l, x' l (c l + t l) < 0)
    (hqual : ∃ l, x l (c l + t l) + t l * x' l (c l + t l) ≠ 0) :
    ∃ lam : ℝ, 1 + lam ≠ 0 ∧ ∀ l, t l / (c l + t l) =
      lam / (1 + lam) * (1 / |(c l + t l) * x' l (c l + t l) / x l (c l + t l)|) := by
  classical
  set D' : Fin n → ℝ := fun l => -t l * x' l (c l + t l)
  set R' : Fin n → ℝ := fun l => x l (c l + t l) + t l * x' l (c l + t l)
  have hD : HasStrictFDerivAt
      (fun t : Fin n → ℝ => ∑ l, ((∫ s in c l..c l + t l, x l s) - t l * x l (c l + t l)))
      (∑ l, D' l • ContinuousLinearMap.proj l) t :=
    HasStrictFDerivAt.fun_sum fun l _ =>
      HasStrictDerivAt.comp_hasStrictFDerivAt (f := fun t : Fin n → ℝ => t l) t
        (ramsey_strict (c l) (hx l) (hx'c l) (t l)).1 (hasStrictFDerivAt_apply (𝕜 := ℝ) l t)
  have hR : HasStrictFDerivAt (fun t : Fin n → ℝ => ∑ l, t l * x l (c l + t l))
      (∑ l, R' l • ContinuousLinearMap.proj l) t :=
    HasStrictFDerivAt.fun_sum fun l _ =>
      HasStrictDerivAt.comp_hasStrictFDerivAt (f := fun t : Fin n → ℝ => t l) t
        (ramsey_strict (c l) (hx l) (hx'c l) (t l)).2 (hasStrictFDerivAt_apply (𝕜 := ℝ) l t)
  obtain ⟨a, b, hab, hlin⟩ :=
    IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt_1d (Or.inl hmin) hR hD
  have hcoord : ∀ l, a * R' l + b * D' l = 0 := by
    intro l
    have := congrArg (fun L => L (Pi.single l 1)) hlin
    simpa [Pi.single_apply] using this
  have hb : b ≠ 0 := by
    intro hb0
    obtain ⟨l, hl⟩ := hqual
    have ha : a ≠ 0 := fun ha0 => hab (by rw [ha0, hb0]; rfl)
    have := hcoord l
    rw [hb0, zero_mul, add_zero] at this
    exact hl ((mul_eq_zero.1 this).resolve_left ha)
  set lam := -a / b
  have hfoc : ∀ l, -t l * x' l (c l + t l) = lam * (x l (c l + t l) + t l * x' l (c l + t l)) := by
    intro l
    have := hcoord l
    simp only [lam, D', R'] at this ⊢
    field_simp
    linarith
  have hlam : 1 + lam ≠ 0 := by
    intro h
    obtain ⟨l, -⟩ := hqual
    have := hfoc l
    rw [show lam = -1 by linarith] at this
    have := hxp l
    linarith
  exact ⟨lam, hlam, fun l => exercise_10_E_3b (hp l) (hxp l) (hneg l) hlam (hfoc l)⟩

/-- **Instance of `exercise_10_E_3b_lagrange`**: one taxed good with unit cost `1/2`, demand
`2 - p` and the tax `1/4` (revenue `5/16`); locally it is the only tax raising that revenue. -/
theorem inst_exercise_10_E_3b :
    ∃ lam : ℝ, 1 + lam ≠ 0 ∧ ∀ l : Fin 1, (fun _ : Fin 1 => (1 / 4 : ℝ)) l /
      ((fun _ : Fin 1 => (1 / 2 : ℝ)) l + (fun _ : Fin 1 => (1 / 4 : ℝ)) l) =
      lam / (1 + lam) * (1 / |((fun _ : Fin 1 => (1 / 2 : ℝ)) l +
        (fun _ : Fin 1 => (1 / 4 : ℝ)) l) * (-1) /
        (2 - ((fun _ : Fin 1 => (1 / 2 : ℝ)) l + (fun _ : Fin 1 => (1 / 4 : ℝ)) l))|) := by
  refine exercise_10_E_3b_lagrange (fun _ => 1 / 2) (fun _ p => 2 - p) (fun _ _ => -1)
    (fun _ s => by simpa using (hasDerivAt_id s).const_sub 2) (fun _ => continuous_const)
    (fun _ => 1 / 4) ?_ (fun _ => by norm_num) (fun _ => by norm_num) (fun _ => by norm_num)
    ⟨0, by norm_num⟩
  rw [IsLocalMinOn, IsMinFilter, eventually_nhdsWithin_iff]
  filter_upwards [Metric.ball_mem_nhds (fun _ : Fin 1 => (1 / 4 : ℝ)) one_pos] with y hy hys
  have hy0 : |y 0 - 1 / 4| < 1 := by
    have := (dist_le_pi_dist y (fun _ => (1 / 4 : ℝ)) 0).trans_lt hy
    rwa [Real.dist_eq] at this
  simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
    at hys
  have hq : (y 0 - 1 / 4) * (y 0 - 5 / 4) = 0 := by nlinarith
  have h14 : y 0 = 1 / 4 := by
    rcases mul_eq_zero.1 hq with h | h
    · linarith
    · rw [abs_lt] at hy0; linarith
  have hyy : y = fun _ => 1 / 4 := by funext i; fin_cases i; exact h14
  rw [hyy]

/-! ## Exercise 10.C.5, derived -/

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **Exercise 10.C.5** (MWG, p. 345), with the equilibrium paths derived. In the model of
Section 10.C with a sales tax, if at `t = 0` every consumer and firm is active and every
`cⱼ'' > 0`, then the equilibrium paths `xᵢ(t) = xᵢ(p*(t) + t)`, `qⱼ(t) = qⱼ(p*(t))`, `p*(t)` are
differentiable at `0`, satisfy (10.C.4)-(10.C.6) near `0`, and the implicit-function computation
(`exercise_10_C_5`) gives
`p*'(0) = -∑[φᵢ'']⁻¹ / (∑[φᵢ'']⁻¹ - ∑[cⱼ'']⁻¹)`. -/
theorem exercise_10_C_5_derived [Nonempty ι] [Nonempty κ] (C : ι → QLConsumer)
    (F : κ → QLFirmStrict) (h0 : (0 : ℝ) ∈ taxRange C F)
    (hxa : ∀ i, taxPrice C F 0 < (C i).dφ 0) (hqa : ∀ j, (F j).dc 0 < taxPrice C F 0)
    (hc2 : ∀ j, 0 < (F j).d2c ((F j).supply (taxPrice C F 0))) :
    ∃ p' : ℝ, HasDerivAt (taxPrice C F) p' 0 ∧
      (∀ i, HasDerivAt (fun t => (C i).demand (taxPrice C F t + t))
        (((C i).d2φ ((C i).demand (taxPrice C F 0 + 0)))⁻¹ * (p' + 1)) 0) ∧
      (∀ j, HasDerivAt (fun t => (F j).supply (taxPrice C F t))
        (((F j).d2c ((F j).supply (taxPrice C F 0)))⁻¹ * p') 0) ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), ∀ i,
        (C i).dφ ((C i).demand (taxPrice C F t + t)) = taxPrice C F t + t) ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), ∀ j, (F j).dc ((F j).supply (taxPrice C F t)) = taxPrice C F t) ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), ∑ i, (C i).demand (taxPrice C F t + t) =
        ∑ j, (F j).supply (taxPrice C F t)) ∧
      p' = -(∑ i, ((C i).d2φ ((C i).demand (taxPrice C F 0 + 0)))⁻¹) /
        (∑ i, ((C i).d2φ ((C i).demand (taxPrice C F 0 + 0)))⁻¹ -
          ∑ j, ((F j).d2c ((F j).supply (taxPrice C F 0)))⁻¹) := by
  set p₀ := taxPrice C F 0
  have hp0 : 0 < p₀ := (minMC_pos F).trans (taxPrice_spec C F h0).1
  obtain ⟨p', hp'⟩ : ∃ p', HasDerivAt (taxPrice C F) p' 0 :=
    ⟨_, example_10_C_1_formula C F h0 hxa hqa hc2⟩
  have hcont := taxPrice_continuousAt C F h0
  have hpath : HasDerivAt (fun t => taxPrice C F t + t) (p' + 1) 0 := hp'.add (hasDerivAt_id 0)
  have hx : ∀ i, HasDerivAt (fun t => (C i).demand (taxPrice C F t + t))
      (((C i).d2φ ((C i).demand (p₀ + 0)))⁻¹ * (p' + 1)) 0 := by
    intro i
    have h1 : HasDerivAt (C i).demand ((C i).d2φ ((C i).demand (p₀ + 0)))⁻¹ (p₀ + 0) := by
      rw [add_zero]; exact (C i).demand_hasDerivAt hp0 (hxa i)
    exact HasDerivAt.comp (h := fun t => taxPrice C F t + t) (0 : ℝ) h1 hpath
  have hq : ∀ j, HasDerivAt (fun t => (F j).supply (taxPrice C F t))
      (((F j).d2c ((F j).supply p₀))⁻¹ * p') 0 := fun j =>
    HasDerivAt.comp (h := taxPrice C F) (0 : ℝ) ((F j).supply_hasDerivAt (hqa j) (hc2 j)) hp'
  have hrange : ∀ᶠ t in 𝓝 (0 : ℝ), t ∈ taxRange C F := isOpen_Ioo.mem_nhds h0
  have hcont2 : ContinuousAt (fun t => taxPrice C F t + t) 0 := hcont.add continuousAt_id
  have e4 : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i,
      (C i).dφ ((C i).demand (taxPrice C F t + t)) = taxPrice C F t + t := by
    have hall : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i, taxPrice C F t + t < (C i).dφ 0 :=
      eventually_all.2 fun i => hcont2.eventually (gt_mem_nhds (by simpa using hxa i))
    filter_upwards [hall, hrange] with t ht hr i
    have hpt : 0 < taxPrice C F t + t := by
      linarith [(taxPrice_spec C F hr).1, hr.1]
    exact (C i).dφ_demand hpt (((C i).demand_pos_iff hpt).2 (ht i))
  have e5 : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ j, (F j).dc ((F j).supply (taxPrice C F t)) = taxPrice C F t := by
    have hall : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ j, (F j).dc 0 < taxPrice C F t :=
      eventually_all.2 fun j => hcont.eventually (lt_mem_nhds (hqa j))
    filter_upwards [hall] with t ht j
    exact ((F j).supply_foc _).2.2 (((F j).supply_pos_iff _).2 (ht j)) |>.symm
  have e6 : ∀ᶠ t in 𝓝 (0 : ℝ), ∑ i, (C i).demand (taxPrice C F t + t) =
      ∑ j, (F j).supply (taxPrice C F t) := by
    filter_upwards [hrange] with t hr
    exact (taxPrice_spec C F hr).2.2
  have hpos0 : ∀ i, 0 < (C i).demand (p₀ + 0) := fun i => by
    rw [add_zero]; exact ((C i).demand_pos_iff hp0).2 (hxa i)
  have hform := exercise_10_C_5 (fun i => (C i).dφ) (fun i => (C i).d2φ) (fun j => (F j).dc)
    (fun j => (F j).d2c) (fun i t => (C i).demand (taxPrice C F t + t))
    (fun j t => (F j).supply (taxPrice C F t)) (taxPrice C F) (t₀ := 0) _ _
    (fun i => foc_hasDerivAt (C i).hasDeriv2 (hpos0 i))
    (fun j => foc_hasDerivAt (F j).hasDeriv2 (((F j).supply_pos_iff _).2 (hqa j)))
    (fun i => (C i).d2φ_neg _ (hpos0 i).le) (fun j => hc2 j) hx hq hp' e4 e5 e6
  exact ⟨p', hp', hx, hq, e4, e5, e6, hform⟩

/-- **Instance of `exercise_10_C_5_derived`**: the economy of `example_10_C_1_instance` (one
consumer `2(1 - e^{-x})`, one firm `q + q²/2`) satisfies its hypotheses. -/
theorem inst_exercise_10_C_5 :
    let C := fun _ : Fin 1 => expConsumer 2 two_pos
    let F := fun _ : Fin 1 => quadFirm 1 1 one_pos one_pos
    (0 : ℝ) ∈ taxRange C F ∧ (∀ i, taxPrice C F 0 < (C i).dφ 0) ∧
      (∀ j, (F j).dc 0 < taxPrice C F 0) ∧
      (∀ j, 0 < (F j).d2c ((F j).supply (taxPrice C F 0))) := by
  intro C F
  have hM : maxMB C = 2 := by simp [maxMB, C, expConsumer, Finset.sup'_const]
  have hm : minMC F = 1 := by
    simp [minMC, F, quadFirm, quadFirmBase, QLFirmStrict.dc, Finset.inf'_const]
  have h0 : (0 : ℝ) ∈ taxRange C F := by
    simp only [taxRange, hM, hm, Set.mem_Ioo]; norm_num
  obtain ⟨a, b, -⟩ := taxPrice_spec C F h0
  rw [hm] at a
  rw [hM, add_zero] at b
  have hd : ∀ i, (C i).dφ 0 = 2 := fun _ => by simp [C, expConsumer]
  have hdc : ∀ j, (F j).dc 0 = 1 := fun _ => by simp [F, quadFirm, quadFirmBase, QLFirmStrict.dc]
  exact ⟨h0, fun i => by rw [hd i]; exact b, fun j => by rw [hdc j]; exact a,
    fun _ => by simp [F, quadFirm, quadFirmBase, QLFirmStrict.d2c]⟩

end MWG.CompetitiveMarkets

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Concluding remarks on partial equilibrium analysis (MWG Section 10.G, pp. 341-343)

A group of `M` interrelated goods with quasilinear utilities `mᵢ + φᵢ(xᵢ)`, `xᵢ ∈ ℝ^M_+`, and
costs `cⱼ(qⱼ)` (p. 342).

* `group_ump_iff`: with quasilinear utility the budget binds and `xᵢ` maximizes `φᵢ(x) - p·x`;
  wealth does not enter.
* **Exercise 10.G.1**: the equilibrium conditions (`IsGroupEqm`), their first-order form
  (`group_consumer_foc`, `group_firm_foc`), independence of wealth, maximization of aggregate
  surplus, uniqueness of individual consumptions and aggregate production, and of individual
  production with strictly convex costs.
* **Exercise 10.G.2** and footnote 31: with separable utilities and costs, the market for good
  `ℓ` decouples from the rest of the group, and aggregate surplus splits.
* **Exercises 10.G.3-10.G.5**: welfare effects of taxes with interrelated demands (cross-market
  terms, substitutes and complements, the bias of single-market measures).
* Footnote 32: a backward-bending demand when consumers are endowed with good `ℓ`.
-/

namespace MWG.CompetitiveMarkets

open Filter Topology MWG.ConsumerChoice

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {M : ℕ}

/-- **(MWG, p. 342)** With quasilinear utility `m + φ(x)` on `ℝ × ℝ^M_+` and budget
`m + p·x ≤ w`, `(m, x)` solves the UMP iff the budget binds and `x` maximizes `φ(x) - p·x` on
`ℝ^M_+`: wealth only affects the numeraire. -/
theorem group_ump_iff (φ : (Fin M → ℝ) → ℝ) (p : Fin M → ℝ) (w m : ℝ) (x : Fin M → ℝ) :
    ((x ∈ nonnegOrthant M ∧ m + p ⬝ᵥ x ≤ w) ∧
      ∀ m' x', x' ∈ nonnegOrthant M → m' + p ⬝ᵥ x' ≤ w → m' + φ x' ≤ m + φ x) ↔
      x ∈ nonnegOrthant M ∧ m = w - p ⬝ᵥ x ∧
        ∀ y ∈ nonnegOrthant M, φ y - p ⬝ᵥ y ≤ φ x - p ⬝ᵥ x := by
  constructor
  · rintro ⟨⟨hx, hb⟩, hmax⟩
    have hm : m = w - p ⬝ᵥ x := by
      have := hmax (w - p ⬝ᵥ x) x hx (by linarith)
      linarith
    refine ⟨hx, hm, fun y hy => ?_⟩
    have := hmax (w - p ⬝ᵥ y) y hy (by linarith)
    linarith
  · rintro ⟨hx, hm, hmax⟩
    refine ⟨⟨hx, by linarith⟩, fun m' x' hx' hb => ?_⟩
    have := hmax x' hx'
    linarith

/-- **Exercise 10.G.1** (MWG, p. 348). Equilibrium conditions for the group of `M` goods (prices
`p`, numeraire price `1`): every `xᵢ` maximizes `φᵢ(x) - p·x` and every `qⱼ` maximizes
`p·q - cⱼ(q)` on `ℝ^M_+`, and the `M` markets clear. They do not involve wealth. -/
def IsGroupEqm (φ : ι → (Fin M → ℝ) → ℝ) (c : κ → (Fin M → ℝ) → ℝ) (x : ι → Fin M → ℝ)
    (q : κ → Fin M → ℝ) (p : Fin M → ℝ) : Prop :=
  (∀ i, x i ∈ nonnegOrthant M ∧ ∀ y ∈ nonnegOrthant M, φ i y - p ⬝ᵥ y ≤ φ i (x i) - p ⬝ᵥ x i) ∧
  (∀ j, q j ∈ nonnegOrthant M ∧ ∀ y ∈ nonnegOrthant M, p ⬝ᵥ y - c j y ≤ p ⬝ᵥ q j - c j (q j)) ∧
  ∑ i, x i = ∑ j, q j

/-- The aggregate surplus of the group, `∑ φᵢ(xᵢ) - ∑ cⱼ(qⱼ)`. -/
def groupSurplus (φ : ι → (Fin M → ℝ) → ℝ) (c : κ → (Fin M → ℝ) → ℝ) (x : ι → Fin M → ℝ)
    (q : κ → Fin M → ℝ) : ℝ :=
  ∑ i, φ i (x i) - ∑ j, c j (q j)

/-- **(MWG, p. 342; Exercise 10.G.1)** An equilibrium of the group maximizes aggregate surplus
among nonnegative allocations with `∑ xᵢ = ∑ qⱼ` (the first welfare theorem for the group). -/
theorem IsGroupEqm.maximizes {φ : ι → (Fin M → ℝ) → ℝ} {c : κ → (Fin M → ℝ) → ℝ}
    {x : ι → Fin M → ℝ} {q : κ → Fin M → ℝ} {p : Fin M → ℝ} (h : IsGroupEqm φ c x q p)
    {x' : ι → Fin M → ℝ} {q' : κ → Fin M → ℝ} (hx' : ∀ i, x' i ∈ nonnegOrthant M)
    (hq' : ∀ j, q' j ∈ nonnegOrthant M) (hs : ∑ i, x' i = ∑ j, q' j) :
    groupSurplus φ c x' q' ≤ groupSurplus φ c x q := by
  have e1 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => (h.1 i).2 (x' i) (hx' i)
  have e2 := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => (h.2.1 j).2 (q' j) (hq' j)
  simp only [Finset.sum_sub_distrib, ← dotProduct_sum] at e1 e2
  rw [hs, h.2.2] at e1
  simp only [groupSurplus]
  linarith

/-- **Exercise 10.G.1** (MWG, pp. 348-349): uniqueness. If every `φᵢ` is strictly concave and
every `cⱼ` convex on `ℝ^M_+`, any two equilibria (at possibly different prices) have the same
individual consumptions and the same aggregate production. -/
theorem exercise_10_G_1_unique {φ : ι → (Fin M → ℝ) → ℝ} {c : κ → (Fin M → ℝ) → ℝ}
    (hφ : ∀ i, StrictConcaveOn ℝ (nonnegOrthant M) (φ i))
    (hc : ∀ j, ConvexOn ℝ (nonnegOrthant M) (c j)) {x x' : ι → Fin M → ℝ}
    {q q' : κ → Fin M → ℝ} {p p' : Fin M → ℝ} (h : IsGroupEqm φ c x q p)
    (h' : IsGroupEqm φ c x' q' p') : x = x' ∧ ∑ j, q j = ∑ j, q' j := by
  have hS : groupSurplus φ c x q = groupSurplus φ c x' q' :=
    le_antisymm (h'.maximizes (fun i => (h.1 i).1) (fun j => (h.2.1 j).1) h.2.2)
      (h.maximizes (fun i => (h'.1 i).1) (fun j => (h'.2.1 j).1) h'.2.2)
  have hconv : ∀ i, (1 / 2 : ℝ) • x i + (1 / 2 : ℝ) • x' i ∈ nonnegOrthant M := fun i =>
    (hφ i).1 (h.1 i).1 (h'.1 i).1 (by norm_num) (by norm_num) (by norm_num)
  have hconvq : ∀ j, (1 / 2 : ℝ) • q j + (1 / 2 : ℝ) • q' j ∈ nonnegOrthant M := fun j =>
    (hc j).1 (h.2.1 j).1 (h'.2.1 j).1 (by norm_num) (by norm_num) (by norm_num)
  have hsm : ∑ i, ((1 / 2 : ℝ) • x i + (1 / 2 : ℝ) • x' i) =
      ∑ j, ((1 / 2 : ℝ) • q j + (1 / 2 : ℝ) • q' j) := by
    simp only [Finset.sum_add_distrib, ← Finset.smul_sum, h.2.2, h'.2.2]
  have hle := h.maximizes hconv hconvq hsm
  have hcost : ∑ j, c j ((1 / 2 : ℝ) • q j + (1 / 2 : ℝ) • q' j) ≤
      ∑ j, ((1 / 2 : ℝ) * c j (q j) + (1 / 2 : ℝ) * c j (q' j)) :=
    Finset.sum_le_sum fun j _ => by
      simpa [smul_eq_mul] using (hc j).2 (h.2.1 j).1 (h'.2.1 j).1
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  have hben : ∀ i, (1 / 2 : ℝ) * φ i (x i) + (1 / 2 : ℝ) * φ i (x' i) ≤
      φ i ((1 / 2 : ℝ) • x i + (1 / 2 : ℝ) • x' i) := fun i => by
    simpa [smul_eq_mul] using (hφ i).concaveOn.2 (h.1 i).1 (h'.1 i).1
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  have hxx : x = x' := by
    by_contra hne
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
    have hstrict : (1 / 2 : ℝ) * φ i (x i) + (1 / 2 : ℝ) * φ i (x' i) <
        φ i ((1 / 2 : ℝ) • x i + (1 / 2 : ℝ) • x' i) := by
      simpa [smul_eq_mul] using (hφ i).2 (h.1 i).1 (h'.1 i).1 hi
        (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    have := Finset.sum_lt_sum (fun k (_ : k ∈ Finset.univ) => hben k)
      ⟨i, Finset.mem_univ i, hstrict⟩
    simp only [groupSurplus, Finset.sum_add_distrib, ← Finset.mul_sum] at hle hS this hcost
    linarith
  exact ⟨hxx, by rw [← h.2.2, ← h'.2.2, hxx]⟩

/-- **Exercise 10.G.1** (MWG, p. 349): with strictly convex costs individual production levels
are unique as well. -/
theorem exercise_10_G_1_unique_strict {φ : ι → (Fin M → ℝ) → ℝ} {c : κ → (Fin M → ℝ) → ℝ}
    (hφ : ∀ i, StrictConcaveOn ℝ (nonnegOrthant M) (φ i))
    (hc : ∀ j, StrictConvexOn ℝ (nonnegOrthant M) (c j)) {x x' : ι → Fin M → ℝ}
    {q q' : κ → Fin M → ℝ} {p p' : Fin M → ℝ} (h : IsGroupEqm φ c x q p)
    (h' : IsGroupEqm φ c x' q' p') : x = x' ∧ q = q' := by
  obtain ⟨hxx, -⟩ := exercise_10_G_1_unique hφ (fun j => (hc j).convexOn) h h'
  subst hxx
  refine ⟨rfl, ?_⟩
  have hS : groupSurplus φ c x q = groupSurplus φ c x q' :=
    le_antisymm (h'.maximizes (fun i => (h.1 i).1) (fun j => (h.2.1 j).1) h.2.2)
      (h.maximizes (fun i => (h'.1 i).1) (fun j => (h'.2.1 j).1) h'.2.2)
  by_contra hne
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hne
  have hconvq : ∀ j, (1 / 2 : ℝ) • q j + (1 / 2 : ℝ) • q' j ∈ nonnegOrthant M := fun j =>
    (hc j).1 (h.2.1 j).1 (h'.2.1 j).1 (by norm_num) (by norm_num) (by norm_num)
  have hsm : ∑ i, x i = ∑ k, ((1 / 2 : ℝ) • q k + (1 / 2 : ℝ) • q' k) := by
    simp only [Finset.sum_add_distrib, ← Finset.smul_sum, ← h.2.2, ← h'.2.2, ← add_smul]
    norm_num
  have hle := h.maximizes (fun i => (h.1 i).1) hconvq hsm
  have hcost : ∑ k, c k ((1 / 2 : ℝ) • q k + (1 / 2 : ℝ) • q' k) <
      ∑ k, ((1 / 2 : ℝ) * c k (q k) + (1 / 2 : ℝ) * c k (q' k)) :=
    Finset.sum_lt_sum (fun k _ => by
      simpa [smul_eq_mul] using (hc k).convexOn.2 (h.2.1 k).1 (h'.2.1 k).1
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
      ⟨j, Finset.mem_univ j, by
        simpa [smul_eq_mul] using (hc j).2 (h.2.1 j).1 (h'.2.1 j).1 hj
          (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)⟩
  simp only [groupSurplus, Finset.sum_add_distrib, ← Finset.mul_sum] at hle hS hcost
  linarith

/-- Moving along coordinate `l` from a bundle of the orthant. -/
theorem orthant_shift [DecidableEq (Fin M)] {x : Fin M → ℝ} (hx : x ∈ nonnegOrthant M)
    (l : Fin M) {t : ℝ} (ht : -x l ≤ t) : x + t • Pi.single l 1 ∈ nonnegOrthant M := by
  intro k
  simp only [Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  by_cases hk : k = l
  · subst hk
    simp only [↓reduceIte, mul_one]
    linarith
  · simp only [hk, ↓reduceIte, mul_zero, add_zero]
    exact hx k

/-- First-order conditions on `ℝ^M_+` along a coordinate: if `x` maximizes `F` on the orthant
and `F` has partial derivative `d` in direction `l` at `x`, then `d ≤ 0`, with equality if
`x_l > 0`. -/
theorem orthant_coord_foc {F : (Fin M → ℝ) → ℝ} {x : Fin M → ℝ} (hx : x ∈ nonnegOrthant M)
    (hmax : ∀ y ∈ nonnegOrthant M, F y ≤ F x) (l : Fin M) {d : ℝ}
    (hd : HasDerivAt (fun t : ℝ => F (x + t • Pi.single l 1)) d 0) : d ≤ 0 ∧ (0 < x l → d = 0) := by
  classical
  refine ⟨?_, fun hpos => ?_⟩
  · refine (foc_max_necessary hd.hasDerivWithinAt le_rfl fun t ht => ?_).1
    rw [zero_smul, add_zero]
    exact hmax _ (orthant_shift hx l (by linarith [hx l]))
  · have hloc : IsLocalMax (fun t : ℝ => F (x + t • Pi.single l 1)) 0 := by
      filter_upwards [Ioi_mem_nhds (neg_lt_zero.2 hpos)] with t ht
      rw [zero_smul, add_zero]
      exact hmax _ (orthant_shift hx l (le_of_lt ht))
    exact hloc.hasDerivAt_eq_zero hd

theorem dot_shift [DecidableEq (Fin M)] (p x : Fin M → ℝ) (l : Fin M) (t : ℝ) :
    p ⬝ᵥ (x + t • Pi.single l 1) = p ⬝ᵥ x + t * p l := by
  rw [dotProduct_add, dotProduct_smul, dotProduct_single, mul_one, smul_eq_mul]

/-- **Exercise 10.G.1** (MWG, p. 348): the consumers' first-order conditions. If `xᵢ` is an
equilibrium bundle and `φᵢ` has partial derivative `∂φᵢ/∂x_l` at `xᵢ`, then
`∂φᵢ/∂x_l ≤ p_l`, with equality if `x_{li} > 0`. -/
theorem group_consumer_foc {φ : (Fin M → ℝ) → ℝ} {p x : Fin M → ℝ} (hx : x ∈ nonnegOrthant M)
    (hmax : ∀ y ∈ nonnegOrthant M, φ y - p ⬝ᵥ y ≤ φ x - p ⬝ᵥ x) (l : Fin M) {dl : ℝ}
    (hd : HasDerivAt (fun t : ℝ => φ (x + t • Pi.single l 1)) dl 0) :
    dl ≤ p l ∧ (0 < x l → dl = p l) := by
  classical
  have hF : HasDerivAt (fun t : ℝ => φ (x + t • Pi.single l 1) - p ⬝ᵥ (x + t • Pi.single l 1))
      (dl - p l) 0 := by
    have h2 : HasDerivAt (fun t : ℝ => p ⬝ᵥ x + t * p l) (p l) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (p l)).const_add (p ⬝ᵥ x)
    refine (hd.sub h2).congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
    simp only [dot_shift, Pi.sub_apply]
  obtain ⟨h1, h2⟩ := orthant_coord_foc (F := fun y => φ y - p ⬝ᵥ y) hx hmax l hF
  exact ⟨by linarith, fun h => by linarith [h2 h]⟩

/-- **Exercise 10.G.1** (MWG, p. 348): the firms' first-order conditions,
`p_l ≤ ∂cⱼ/∂q_l` with equality if `q_{lj} > 0`. -/
theorem group_firm_foc {c : (Fin M → ℝ) → ℝ} {p q : Fin M → ℝ} (hq : q ∈ nonnegOrthant M)
    (hmax : ∀ y ∈ nonnegOrthant M, p ⬝ᵥ y - c y ≤ p ⬝ᵥ q - c q) (l : Fin M) {dl : ℝ}
    (hd : HasDerivAt (fun t : ℝ => c (q + t • Pi.single l 1)) dl 0) :
    p l ≤ dl ∧ (0 < q l → p l = dl) := by
  classical
  have hF : HasDerivAt (fun t : ℝ => p ⬝ᵥ (q + t • Pi.single l 1) - c (q + t • Pi.single l 1))
      (p l - dl) 0 := by
    have h2 : HasDerivAt (fun t : ℝ => p ⬝ᵥ q + t * p l) (p l) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (p l)).const_add (p ⬝ᵥ q)
    refine (h2.sub hd).congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
    simp only [dot_shift, Pi.sub_apply]
  obtain ⟨h1, h2⟩ := orthant_coord_foc (F := fun y => p ⬝ᵥ y - c y) hq hmax l hF
  exact ⟨by linarith, fun h => by linarith [h2 h]⟩

/-! ## Exercise 10.G.2 and footnote 31: separable utilities and costs -/

/-- Splitting a bundle into good `l` and the others: `p·x = p_l x_l + p·x_{-l}` with
`x_{-l} = x` with `x_l` set to `0`. -/
theorem dot_split [DecidableEq (Fin M)] (p x : Fin M → ℝ) (l : Fin M) :
    p ⬝ᵥ x = p l * x l + p ⬝ᵥ Function.update x l 0 := by
  have hx : x = Function.update x l 0 + x l • Pi.single l 1 := by
    ext k
    by_cases hk : k = l
    · subst hk; simp
    · simp [hk]
  conv_lhs => rw [hx]
  rw [dotProduct_add, dotProduct_smul, dotProduct_single, mul_one, smul_eq_mul]
  ring

/-- **Exercise 10.G.2** (MWG, p. 349; footnote 31, p. 343). If `φ(x) = f(x_l) + g(x_{-l})`, then
`x` maximizes `φ(x) - p·x` on `ℝ^M_+` iff `x_l` maximizes `f(a) - p_l a` on `a ≥ 0` and `x_{-l}`
maximizes `g(y) - p·y` over bundles with `y_l = 0`: the demand for good `l` depends only on
`p_l`. -/
theorem exercise_10_G_2_consumer [DecidableEq (Fin M)] (f : ℝ → ℝ) (g : (Fin M → ℝ) → ℝ)
    (p x : Fin M → ℝ) (l : Fin M) (hx : x ∈ nonnegOrthant M) :
    (∀ y ∈ nonnegOrthant M, f (y l) + g (Function.update y l 0) - p ⬝ᵥ y ≤
        f (x l) + g (Function.update x l 0) - p ⬝ᵥ x) ↔
      (∀ a, 0 ≤ a → f a - p l * a ≤ f (x l) - p l * x l) ∧
      (∀ y ∈ nonnegOrthant M, y l = 0 →
        g y - p ⬝ᵥ y ≤ g (Function.update x l 0) - p ⬝ᵥ Function.update x l 0) := by
  constructor
  · intro h
    refine ⟨fun a ha => ?_, fun y hy hyl => ?_⟩
    · have hmem : Function.update x l a ∈ nonnegOrthant M := by
        intro k; by_cases hk : k = l
        · subst hk; simp [ha]
        · simp [hk, hx k]
      have := h _ hmem
      rw [dot_split p (Function.update x l a) l, dot_split p x l] at this
      simp only [Function.update_self, Function.update_idem] at this
      linarith
    · have hmem : Function.update y l (x l) ∈ nonnegOrthant M := by
        intro k; by_cases hk : k = l
        · subst hk; simp [hx k]
        · simp [hk, hy k]
      have := h _ hmem
      rw [dot_split p (Function.update y l (x l)) l, dot_split p x l] at this
      simp only [Function.update_self, Function.update_idem] at this
      have hyy : Function.update y l 0 = y := by
        rw [← hyl]; exact Function.update_eq_self l y
      rw [hyy] at this
      linarith
  · rintro ⟨h1, h2⟩ y hy
    have hy0 : Function.update y l 0 ∈ nonnegOrthant M := by
      intro k; by_cases hk : k = l
      · subst hk; simp
      · simp [hk, hy k]
    have e1 := h1 (y l) (hy l)
    have e2 := h2 _ hy0 (by simp)
    rw [dot_split p y l, dot_split p x l]
    linarith

/-- **Exercise 10.G.2** (MWG, p. 349): with separable utilities and costs the aggregate surplus
of the group is the surplus `∑ fᵢ(x_{li}) - ∑ c_{lj}(q_{lj})` of market `l` plus a term not
depending on good `l`; with full separability it is the sum of the single-market surpluses. -/
theorem exercise_10_G_2_surplus [DecidableEq (Fin M)] (f : ι → ℝ → ℝ)
    (g : ι → (Fin M → ℝ) → ℝ) (cl : κ → ℝ → ℝ) (d : κ → (Fin M → ℝ) → ℝ) (l : Fin M)
    (x : ι → Fin M → ℝ) (q : κ → Fin M → ℝ) :
    groupSurplus (fun i y => f i (y l) + g i (Function.update y l 0))
        (fun j y => cl j (y l) + d j (Function.update y l 0)) x q =
      (∑ i, f i (x i l) - ∑ j, cl j (q j l)) +
        (∑ i, g i (Function.update (x i) l 0) - ∑ j, d j (Function.update (q j) l 0)) := by
  simp only [groupSurplus, Finset.sum_add_distrib]
  ring

/-- Full separability (MWG, p. 349): `φᵢ(x) = ∑ₗ φ_{li}(x_l)`, `cⱼ(q) = ∑ₗ c_{lj}(q_l)` give
aggregate surplus `∑ₗ [∑ᵢ φ_{li}(x_{li}) - ∑ⱼ c_{lj}(q_{lj})]`. -/
theorem exercise_10_G_2_full (f : ι → Fin M → ℝ → ℝ) (cl : κ → Fin M → ℝ → ℝ)
    (x : ι → Fin M → ℝ) (q : κ → Fin M → ℝ) :
    groupSurplus (fun i y => ∑ l, f i l (y l)) (fun j y => ∑ l, cl j l (y l)) x q =
      ∑ l, (∑ i, f i l (x i l) - ∑ j, cl j l (q j l)) := by
  simp only [groupSurplus, Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun i l => f i l (x i l)),
    Finset.sum_comm (f := fun j l => cl j l (q j l))]

/-! ## Exercises 10.G.3-10.G.5 -/

/-- **Exercises 10.G.3-10.G.4** (MWG, p. 349): the welfare effect of price changes in a
three-good economy with `u = x₁ + φ(x₂, x₃)` and constant unit costs `c₂, c₃`. Along a path of
consumer prices `(p₂, p₃)` with demands `(x₂(s), x₃(s))` satisfying the consumer's first-order
condition `∇φ = (p₂, p₃)`, aggregate surplus `φ(x₂, x₃) - c₂x₂ - c₃x₃` changes at rate
`t₂ x₂' + t₃ x₃'`, where `t_k = p_k - c_k` are the taxes. -/
theorem exercise_10_G_3_4 {φ : ℝ × ℝ → ℝ} {x₂ x₃ : ℝ → ℝ} {s₀ c₂ c₃ p₂ p₃ x₂' x₃' : ℝ}
    (hφ : HasFDerivAt φ (p₂ • ContinuousLinearMap.fst ℝ ℝ ℝ + p₃ • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (x₂ s₀, x₃ s₀))
    (h₂ : HasDerivAt x₂ x₂' s₀) (h₃ : HasDerivAt x₃ x₃' s₀) :
    HasDerivAt (fun s => φ (x₂ s, x₃ s) - c₂ * x₂ s - c₃ * x₃ s)
      ((p₂ - c₂) * x₂' + (p₃ - c₃) * x₃') s₀ := by
  have h := ((hasDerivAt_comp_two hφ h₂ h₃).sub (h₂.const_mul c₂)).sub (h₃.const_mul c₃)
  exact h.congr_deriv (by ring)

/-- **Exercise 10.G.3(a)** (MWG, p. 349). If market 3 is undistorted (`t₃ = 0`), the welfare
change from a tax change in market 2 is `t₂ x₂'`, the change in the area between market 2's
demand (at the initial `p₃`) and supply curves. **(b)** If `t₃ > 0`, the single-market measure
`t₂ x₂'` differs from the true change `t₂ x₂' + t₃ x₃'` by `t₃ x₃'`: when good 3 is a substitute
(`x₃' > 0` as `p₂` rises) the single-market measure overstates the welfare loss; when it is a
complement (`x₃' < 0`) it understates it. -/
theorem exercise_10_G_3 {t₂ t₃ x₂' x₃' : ℝ} :
    (t₃ = 0 → t₂ * x₂' + t₃ * x₃' = t₂ * x₂') ∧
    (0 < t₃ → 0 < x₃' → t₂ * x₂' < t₂ * x₂' + t₃ * x₃') ∧
    (0 < t₃ → x₃' < 0 → t₂ * x₂' + t₃ * x₃' < t₂ * x₂') := by
  refine ⟨fun h => by rw [h]; ring, fun h1 h2 => ?_, fun h1 h2 => ?_⟩
  · nlinarith
  · nlinarith

/-- **Exercise 10.G.4** (MWG, p. 349). Raising both taxes along `(dt₂, dt₃)` with demand
derivatives `x_{kl} = ∂x_k/∂p_l`, the welfare change is
`t₂(x₂₂dt₂ + x₂₃dt₃) + t₃(x₃₂dt₂ + x₃₃dt₃)`. -/
theorem exercise_10_G_4 {φ : ℝ × ℝ → ℝ} {x₂ x₃ : ℝ → ℝ} {s₀ c₂ c₃ p₂ p₃ : ℝ}
    {x22 x23 x32 x33 dt₂ dt₃ : ℝ}
    (hφ : HasFDerivAt φ (p₂ • ContinuousLinearMap.fst ℝ ℝ ℝ + p₃ • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (x₂ s₀, x₃ s₀))
    (h₂ : HasDerivAt x₂ (x22 * dt₂ + x23 * dt₃) s₀)
    (h₃ : HasDerivAt x₃ (x32 * dt₂ + x33 * dt₃) s₀) :
    HasDerivAt (fun s => φ (x₂ s, x₃ s) - c₂ * x₂ s - c₃ * x₃ s)
      ((p₂ - c₂) * (x22 * dt₂ + x23 * dt₃) + (p₃ - c₃) * (x32 * dt₂ + x33 * dt₃)) s₀ :=
  exercise_10_G_3_4 hφ h₂ h₃

/-- **Exercise 10.G.5(a)** (MWG, p. 349). With upward-sloping supply in market 3
(`q₃' ≥ 0`, strictly convex `c₃`) and `∂x₃/∂p₃ < 0`, differentiating market-3 clearing
`x₃(p₂, p₃) = q₃(p₃)` gives `dp₃ = x₃₂ dp₂/(q₃' - x₃₃)`; so if the tax raises `p₂`, the price of
good 3 rises when goods 2 and 3 are substitutes (`x₃₂ > 0`) and falls when they are complements. -/
theorem exercise_10_G_5a {x32 x33 q3' dp₂ dp₃ : ℝ} (hx33 : x33 < 0) (hq : 0 ≤ q3')
    (hclear : x32 * dp₂ + x33 * dp₃ = q3' * dp₃) (hdp : 0 < dp₂) :
    dp₃ = x32 * dp₂ / (q3' - x33) ∧ (0 < x32 → 0 < dp₃) ∧ (x32 < 0 → dp₃ < 0) := by
  have hden : 0 < q3' - x33 := by linarith
  have h : dp₃ = x32 * dp₂ / (q3' - x33) := by rw [eq_div_iff hden.ne']; linarith
  refine ⟨h, fun hs => ?_, fun hc => ?_⟩
  · rw [h]; positivity
  · rw [h]; exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hc hdp) hden

/-- **Exercise 10.G.5(b)** (MWG, p. 349). Evaluating the welfare change from the tax on good 2
with the demand for good 2 at the pre-change price of good 3 omits `t₂ x₂₃ dp₃`. With symmetric
cross effects (`x₂₃ = x₃₂`, quasilinear demand), `t₂ > 0` and `dp₂ > 0`, this omitted term is
nonnegative for substitutes and for complements alike: the fixed-`p₃` formula overstates the
welfare loss in both cases. -/
theorem exercise_10_G_5b {x22 x23 x32 x33 q3' t₂ dp₂ dp₃ : ℝ} (hx33 : x33 < 0) (hq : 0 ≤ q3')
    (hsym : x23 = x32) (ht : 0 < t₂) (hdp : 0 < dp₂)
    (hclear : x32 * dp₂ + x33 * dp₃ = q3' * dp₃) :
    t₂ * (x22 * dp₂ + x23 * dp₃) - t₂ * (x22 * dp₂) = t₂ * x32 ^ 2 * dp₂ / (q3' - x33) ∧
      0 ≤ t₂ * (x22 * dp₂ + x23 * dp₃) - t₂ * (x22 * dp₂) := by
  obtain ⟨h, -, -⟩ := exercise_10_G_5a hx33 hq hclear hdp
  have hden : 0 < q3' - x33 := by linarith
  have e : t₂ * (x22 * dp₂ + x23 * dp₃) - t₂ * (x22 * dp₂) = t₂ * x32 ^ 2 * dp₂ / (q3' - x33) := by
    rw [hsym, h]; field_simp; ring
  exact ⟨e, by rw [e]; positivity⟩

/-! ## Footnote 32: backward-bending demand -/

/-- **Footnote 32** (MWG, p. 343). With Leontief preferences `min(m, x)` on `ℝ²₊`, the demand
at price `p > 0` and wealth `w ≥ 0` is `m = x = w/(1 + p)` (good `ℓ` is normal). If the consumer
owns `e` units of good `ℓ` and `m₀ < e` of the numeraire, her wealth is `m₀ + pe` and her demand
`(m₀ + pe)/(1 + p)` is strictly increasing in the price `p`. -/
theorem footnote_10_G_32 {p w : ℝ} (hp : 0 < p) :
    (∀ m x : ℝ, 0 ≤ m → 0 ≤ x → m + p * x ≤ w → min m x ≤ min (w / (1 + p)) (w / (1 + p))) ∧
    (w / (1 + p) + p * (w / (1 + p)) = w) := by
  have h1 : 0 < 1 + p := by linarith
  refine ⟨fun m x hm hx hb => ?_, by field_simp⟩
  rw [min_self, le_div_iff₀ h1]
  have := min_le_left m x
  have := min_le_right m x
  nlinarith [min_le_left m x, min_le_right m x]

/-- **Footnote 32** (MWG, p. 343): the demand `(m₀ + pe)/(1 + p)` has derivative
`(e - m₀)/(1 + p)² > 0` when `e > m₀`. -/
theorem footnote_10_G_32_increasing {m₀ e p : ℝ} (hp : 0 < p) (he : m₀ < e) :
    HasDerivAt (fun p => (m₀ + p * e) / (1 + p)) ((e - m₀) / (1 + p) ^ 2) p ∧
      0 < (e - m₀) / (1 + p) ^ 2 := by
  have h1 : (1 + p) ≠ 0 := by linarith
  refine ⟨?_, by have : 0 < e - m₀ := by linarith
                 positivity⟩
  have h := (((hasDerivAt_id p).mul_const e).const_add m₀).div ((hasDerivAt_id p).const_add 1) h1
  exact h.congr_deriv (by simp only [id]; field_simp; ring)

end MWG.CompetitiveMarkets

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Concrete instances (non-vacuity of the hypothesis bundles of Chapter 10)

One consumer `φ(x) = 2(1 - e^{-x})` and one firm `c(q) = q + q²/2` satisfy all assumptions of
Section 10.C (`QLConsumer`, `QLFirmStrict`, `maxᵢ φᵢ'(0) = 2 > minⱼ cⱼ'(0) = 1`). For this economy
we exhibit a competitive equilibrium (Definition 10.B.3), check that it is Pareto optimal
(Proposition 10.D.1) and apply the second welfare theorem (Proposition 10.D.2). Further
instances: the strong-monotonicity hypotheses of Exercise 10.B.1(b), the strictly convex cost of
Exercise 10.F.1, the efficient-scale characterization of Figure 10.F.4 with linear demand, and the
utilitarian welfare function for the surplus criterion of Section 10.E.
-/

namespace MWG.CompetitiveMarkets

open MWG.ConsumerChoice MWG.ClassicalDemand

/-- The consumer of the instance economy. -/
noncomputable def instC : Fin 1 → QLConsumer := fun _ => expConsumer 2 two_pos

/-- The firm of the instance economy. -/
noncomputable def instF : Fin 1 → QLFirmStrict := fun _ => quadFirm 1 1 one_pos one_pos

theorem inst_gap : ∃ i j, (instF j).dc 0 < (instC i).dφ 0 :=
  ⟨0, 0, by simp [instF, instC, quadFirm, quadFirmBase, QLFirmStrict.dc, expConsumer]⟩

/-- **Instance of Section 10.C-10.D.** The instance economy has a competitive equilibrium in the
sense of Definition 10.B.3 (endowment `1` of the numeraire, the consumer owning the firm), and
that equilibrium allocation is Pareto optimal (Proposition 10.D.1). -/
theorem inst_equilibrium_pareto :
    ∃ (a : Allocation (Fin 1) (Fin 1) 2) (p : ℝ),
      (qlEconomyOf instC (fun j => (instF j).toQLFirm) (fun _ => 1) (fun _ _ => 1)).IsCompetitiveEqm
        a (qlPrice p) ∧
      (qlEconomyOf instC (fun j => (instF j).toQLFirm) (fun _ => 1)
        (fun _ _ => 1)).toEconomy.IsParetoOptimal a := by
  obtain ⟨p, -, -, -, -, hq⟩ := ql_eqm_exists instC instF inst_gap
  have hθ : ∀ j : Fin 1, ∑ i : Fin 1, (fun _ _ => (1 : ℝ)) i j = 1 := fun _ => by simp
  have h := ql_isCompetitiveEqm_of_isQLEqm hq (fun _ => 1) (fun _ _ => 1) hθ
  exact ⟨_, p, h, proposition_10_D_1 instC _ _ _ hθ _ p h⟩

/-- **Instance of Proposition 10.D.2.** For the Pareto optimal equilibrium allocation of the
instance economy, the transfers of the second welfare theorem exist. -/
theorem inst_second_welfare :
    ∃ a : Allocation (Fin 1) (Fin 1) 2,
      (qlEconomyOf instC (fun j => (instF j).toQLFirm) (fun _ => 1)
        (fun _ _ => 1)).toEconomy.IsParetoOptimal a ∧
      ∃ T : Fin 1 → ℝ, ∑ i, T i = 0 ∧ ∃ (a' : Allocation (Fin 1) (Fin 1) 2) (p : ℝ),
        (qlEconomyOf instC (fun j => (instF j).toQLFirm) ((fun _ => 1) + T)
          (fun _ _ => 1)).IsCompetitiveEqm a' (qlPrice p) := by
  obtain ⟨a, -, -, hPO⟩ := inst_equilibrium_pareto
  obtain ⟨T, hT, a', p, h, -⟩ := proposition_10_D_2 instC instF inst_gap (fun _ => 1)
    (fun _ _ => 1) (fun _ => by simp) a hPO
  exact ⟨a, hPO, T, hT, a', p, h⟩

/-- **Instance of Exercise 10.B.1(b).** One good, `Xᵢ = ℝ₊`, `uᵢ(x) = x`: continuous and strongly
monotone. -/
theorem inst_exercise_10_B_1b :
    ContinuousOn (fun x : Fin 1 → ℝ => x 0) (nonnegOrthant 1) ∧
      PrefStronglyMonotone (nonnegOrthant 1) (utilityPref fun x : Fin 1 → ℝ => x 0) := by
  refine ⟨(continuous_apply 0).continuousOn, fun x _ y _ hxy hne => ?_⟩
  have hlt : x 0 < y 0 := by
    refine lt_of_le_of_ne (hxy 0) fun h => hne ?_
    ext l; fin_cases l; exact h.symm
  exact ⟨hlt.le, not_le.2 hlt⟩

/-- **Instance of Exercise 10.F.1.** `c(q) = q²` (strictly convex, `c(0) = 0`): `π(p) > 0` iff
`p > c'(0) = 0`. -/
theorem inst_exercise_10_F_1 (p : ℝ) : PosProfit (fun q => q ^ 2) p ↔ 0 < p := by
  have h := exercise_10_F_1 (c := fun q => q ^ 2) (dc := fun q => 2 * q) (by simp)
    (fun q _ => by simpa using (hasDerivAt_pow 2 q).hasDerivWithinAt)
    ((strictConvexOn_pow (by norm_num : 1 < 2)).subset (fun _ h => h) (convex_Ici 0)) p
  simpa using h

/-- **Instance of Figure 10.F.4.** Demand `10 - p` and cost `1 + q + q²` (`q > 0`): the unique
long-run equilibria are `(3, 1, 7)`. -/
theorem inst_lr_efficientScale {p q : ℝ} {J : ℕ} :
    IsLREqm (fun p => 10 - p) (quadLumpyCost (1 * 1 ^ 2) 1 1) p q J ↔
      p = 3 ∧ q = 1 ∧ (J : ℝ) = 7 := by
  obtain ⟨hqb, hcb, huniq⟩ := quadLumpy_efficientScale (α := 1) one_pos one_pos
  have hc0 : quadLumpyCost (1 * 1 ^ 2) 1 1 0 = 0 := by simp [quadLumpyCost, lumpyCost]
  have hcb3 : quadLumpyCost (1 * 1 ^ 2) 1 1 1 / 1 = 3 := by rw [hcb]; norm_num
  rw [lr_efficientScale hc0 hqb huniq (by rw [hcb3]; norm_num)
    (fun a _ b _ hab => by linarith), hcb3]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, by linarith⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, by rw [h3]; norm_num⟩

/-- **Instance of the surplus criterion (pp. 328-329).** The utilitarian welfare function is
strictly increasing and attains its maximum under redistribution, so
`welfare_lt_iff_surplus_lt` applies. -/
theorem inst_welfare_lt {s₀ s₁ : ℝ} : s₀ < s₁ ↔ s₀ < s₁ :=
  welfare_lt_iff_surplus_lt (ι := Fin 2) (fun u => ∑ i, u i)
    (fun u v h => Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ => h i)
    (footnote_10_E_17 s₀ (u := fun _ => s₀ / 2) (by simp; ring))
    (footnote_10_E_17 s₁ (u := fun _ => s₁ / 2) (by simp; ring))

end MWG.CompetitiveMarkets

set_option linter.style.longLine false
#print axioms MWG.CompetitiveMarkets.foc_exists_gt_of_deriv_pos
#print axioms MWG.CompetitiveMarkets.foc_exists_lt_of_deriv_neg
#print axioms MWG.CompetitiveMarkets.foc_continuousOn
#print axioms MWG.CompetitiveMarkets.foc_hasDerivAt
#print axioms MWG.CompetitiveMarkets.foc_hasDerivWithin_interior
#print axioms MWG.CompetitiveMarkets.foc_max_necessary
#print axioms MWG.CompetitiveMarkets.foc_local_necessary
#print axioms MWG.CompetitiveMarkets.foc_max_iff
#print axioms MWG.CompetitiveMarkets.foc_tangent_le
#print axioms MWG.CompetitiveMarkets.foc_le_tangent_convex
#print axioms MWG.CompetitiveMarkets.IsFOCSol
#print axioms MWG.CompetitiveMarkets.isFOCSol_unique
#print axioms MWG.CompetitiveMarkets.isFOCSol_exists
#print axioms MWG.CompetitiveMarkets.focSol
#print axioms MWG.CompetitiveMarkets.focSol_spec
#print axioms MWG.CompetitiveMarkets.focSol_eq
#print axioms MWG.CompetitiveMarkets.focSol_eq_zero_iff
#print axioms MWG.CompetitiveMarkets.focSol_pos_iff
#print axioms MWG.CompetitiveMarkets.focSol_eq_of_pos
#print axioms MWG.CompetitiveMarkets.focSol_antitone
#print axioms MWG.CompetitiveMarkets.focSol_strictAnti
#print axioms MWG.CompetitiveMarkets.focSol_continuousAt
#print axioms MWG.CompetitiveMarkets.focSol_hasDerivAt
#print axioms MWG.CompetitiveMarkets.hasDerivAt_of_sandwich
#print axioms MWG.CompetitiveMarkets.remainder_isLittleO
#print axioms MWG.CompetitiveMarkets.Economy
#print axioms MWG.CompetitiveMarkets.Economy.mk
#print axioms MWG.CompetitiveMarkets.Economy.X
#print axioms MWG.CompetitiveMarkets.Economy.u
#print axioms MWG.CompetitiveMarkets.Economy.ω
#print axioms MWG.CompetitiveMarkets.Economy.Y
#print axioms MWG.CompetitiveMarkets.Allocation
#print axioms MWG.CompetitiveMarkets.Allocation.mk
#print axioms MWG.CompetitiveMarkets.Allocation.x
#print axioms MWG.CompetitiveMarkets.Allocation.y
#print axioms MWG.CompetitiveMarkets.Economy.IsAllocation
#print axioms MWG.CompetitiveMarkets.Economy.IsFeasible
#print axioms MWG.CompetitiveMarkets.Economy.IsParetoOptimal
#print axioms MWG.CompetitiveMarkets.definition_10_B_1
#print axioms MWG.CompetitiveMarkets.definition_10_B_2
#print axioms MWG.CompetitiveMarkets.Economy.utilityPossibilitySet
#print axioms MWG.CompetitiveMarkets.isParetoOptimal_iff_undominated
#print axioms MWG.CompetitiveMarkets.mem_utilityPossibilitySet
#print axioms MWG.CompetitiveMarkets.PrivEconomy
#print axioms MWG.CompetitiveMarkets.PrivEconomy.mk
#print axioms MWG.CompetitiveMarkets.PrivEconomy.X
#print axioms MWG.CompetitiveMarkets.PrivEconomy.u
#print axioms MWG.CompetitiveMarkets.PrivEconomy.Y
#print axioms MWG.CompetitiveMarkets.PrivEconomy.ωi
#print axioms MWG.CompetitiveMarkets.PrivEconomy.θ
#print axioms MWG.CompetitiveMarkets.PrivEconomy.toEconomy
#print axioms MWG.CompetitiveMarkets.PrivEconomy.wealth
#print axioms MWG.CompetitiveMarkets.PrivEconomy.IsCompetitiveEqm
#print axioms MWG.CompetitiveMarkets.definition_10_B_3
#print axioms MWG.CompetitiveMarkets.PrivEconomy.IsCompetitiveEqm.isFeasible
#print axioms MWG.CompetitiveMarkets.exercise_10_B_2
#print axioms MWG.CompetitiveMarkets.lemma_10_B_1
#print axioms MWG.CompetitiveMarkets.lemma_10_B_1_strictlyPositive
#print axioms MWG.CompetitiveMarkets.Economy.IsWeaklyParetoOptimal
#print axioms MWG.CompetitiveMarkets.exercise_10_B_1a
#print axioms MWG.CompetitiveMarkets.exercise_10_B_1b_general
#print axioms MWG.CompetitiveMarkets.exercise_10_B_1b
#print axioms MWG.CompetitiveMarkets.exercise_10_B_1c_economy
#print axioms MWG.CompetitiveMarkets.exercise_10_B_1c
#print axioms MWG.CompetitiveMarkets.QLConsumer
#print axioms MWG.CompetitiveMarkets.QLConsumer.mk
#print axioms MWG.CompetitiveMarkets.QLConsumer.φ
#print axioms MWG.CompetitiveMarkets.QLConsumer.dφ
#print axioms MWG.CompetitiveMarkets.QLConsumer.d2φ
#print axioms MWG.CompetitiveMarkets.QLConsumer.φ_zero
#print axioms MWG.CompetitiveMarkets.QLConsumer.bddAbove
#print axioms MWG.CompetitiveMarkets.QLConsumer.hasDeriv
#print axioms MWG.CompetitiveMarkets.QLConsumer.hasDeriv2
#print axioms MWG.CompetitiveMarkets.QLConsumer.dφ_pos
#print axioms MWG.CompetitiveMarkets.QLConsumer.d2φ_neg
#print axioms MWG.CompetitiveMarkets.QLFirm
#print axioms MWG.CompetitiveMarkets.QLFirm.mk
#print axioms MWG.CompetitiveMarkets.QLFirm.c
#print axioms MWG.CompetitiveMarkets.QLFirm.dc
#print axioms MWG.CompetitiveMarkets.QLFirm.d2c
#print axioms MWG.CompetitiveMarkets.QLFirm.hasDeriv
#print axioms MWG.CompetitiveMarkets.QLFirm.hasDeriv2
#print axioms MWG.CompetitiveMarkets.QLFirm.dc_pos
#print axioms MWG.CompetitiveMarkets.QLFirm.d2c_nonneg
#print axioms MWG.CompetitiveMarkets.QLFirmStrict
#print axioms MWG.CompetitiveMarkets.QLFirmStrict.mk
#print axioms MWG.CompetitiveMarkets.QLFirmStrict.toQLFirm
#print axioms MWG.CompetitiveMarkets.QLFirmStrict.strictConvex
#print axioms MWG.CompetitiveMarkets.QLFirmStrict.dc_tendsto
#print axioms MWG.CompetitiveMarkets.QLConsumer.dφ_continuousOn
#print axioms MWG.CompetitiveMarkets.QLConsumer.φ_continuousOn
#print axioms MWG.CompetitiveMarkets.QLConsumer.dφ_strictAnti
#print axioms MWG.CompetitiveMarkets.QLConsumer.dφ_antitone
#print axioms MWG.CompetitiveMarkets.QLConsumer.φ_strictMono
#print axioms MWG.CompetitiveMarkets.QLConsumer.strictConcave
#print axioms MWG.CompetitiveMarkets.QLConsumer.tangent_le
#print axioms MWG.CompetitiveMarkets.QLConsumer.exists_dφ_lt
#print axioms MWG.CompetitiveMarkets.QLConsumer.dφ_surj
#print axioms MWG.CompetitiveMarkets.QLConsumer.max_iff
#print axioms MWG.CompetitiveMarkets.QLConsumer.foc_exists
#print axioms MWG.CompetitiveMarkets.QLConsumer.demand
#print axioms MWG.CompetitiveMarkets.QLConsumer.demand_spec
#print axioms MWG.CompetitiveMarkets.QLConsumer.demand_nonneg
#print axioms MWG.CompetitiveMarkets.QLConsumer.demand_eq
#print axioms MWG.CompetitiveMarkets.QLConsumer.demand_max
#print axioms MWG.CompetitiveMarkets.QLConsumer.demand_eq_zero_iff
#print axioms MWG.CompetitiveMarkets.QLConsumer.demand_pos_iff
#print axioms MWG.CompetitiveMarkets.QLConsumer.dφ_demand
#print axioms MWG.CompetitiveMarkets.QLConsumer.demand_antitoneOn
#print axioms MWG.CompetitiveMarkets.QLConsumer.demand_strictAnti
#print axioms MWG.CompetitiveMarkets.QLConsumer.demand_continuousAt
#print axioms MWG.CompetitiveMarkets.QLConsumer.demand_continuousOn
#print axioms MWG.CompetitiveMarkets.QLConsumer.demand_hasDerivAt
#print axioms MWG.CompetitiveMarkets.QLConsumer.demand_deriv_neg
#print axioms MWG.CompetitiveMarkets.QLFirm.dc_continuousOn
#print axioms MWG.CompetitiveMarkets.QLFirm.c_continuousOn
#print axioms MWG.CompetitiveMarkets.QLFirm.dc_monotone
#print axioms MWG.CompetitiveMarkets.QLFirm.c_strictMono
#print axioms MWG.CompetitiveMarkets.QLFirm.convex
#print axioms MWG.CompetitiveMarkets.QLFirm.le_tangent
#print axioms MWG.CompetitiveMarkets.QLFirm.max_iff
#print axioms MWG.CompetitiveMarkets.QLFirm.foc_iff_isFOCSol
#print axioms MWG.CompetitiveMarkets.QLFirmStrict.c
#print axioms MWG.CompetitiveMarkets.QLFirmStrict.dc
#print axioms MWG.CompetitiveMarkets.QLFirmStrict.d2c
#print axioms MWG.CompetitiveMarkets.QLFirmStrict.hasDeriv
#print axioms MWG.CompetitiveMarkets.QLFirmStrict.hasDeriv2
#print axioms MWG.CompetitiveMarkets.QLFirmStrict.dc_continuousOn
#print axioms MWG.CompetitiveMarkets.QLFirmStrict.dc_strictMono
#print axioms MWG.CompetitiveMarkets.QLFirmStrict.neg_dc_strictAnti
#print axioms MWG.CompetitiveMarkets.QLFirmStrict.foc_exists
#print axioms MWG.CompetitiveMarkets.QLFirmStrict.supply
#print axioms MWG.CompetitiveMarkets.QLFirmStrict.supply_foc
#print axioms MWG.CompetitiveMarkets.QLFirmStrict.supply_nonneg
#print axioms MWG.CompetitiveMarkets.QLFirmStrict.supply_eq
#print axioms MWG.CompetitiveMarkets.QLFirmStrict.supply_max
#print axioms MWG.CompetitiveMarkets.QLFirmStrict.supply_eq_zero_iff
#print axioms MWG.CompetitiveMarkets.QLFirmStrict.supply_pos_iff
#print axioms MWG.CompetitiveMarkets.QLFirmStrict.supply_monotone
#print axioms MWG.CompetitiveMarkets.QLFirmStrict.supply_strictMono
#print axioms MWG.CompetitiveMarkets.QLFirmStrict.supply_continuous
#print axioms MWG.CompetitiveMarkets.QLFirmStrict.supply_hasDerivAt
#print axioms MWG.CompetitiveMarkets.aggDemand
#print axioms MWG.CompetitiveMarkets.aggSupply
#print axioms MWG.CompetitiveMarkets.aggDemand_nonneg
#print axioms MWG.CompetitiveMarkets.aggSupply_nonneg
#print axioms MWG.CompetitiveMarkets.aggDemand_continuousOn
#print axioms MWG.CompetitiveMarkets.aggSupply_continuous
#print axioms MWG.CompetitiveMarkets.aggDemand_antitoneOn
#print axioms MWG.CompetitiveMarkets.aggSupply_monotone
#print axioms MWG.CompetitiveMarkets.aggDemand_eq_zero_iff
#print axioms MWG.CompetitiveMarkets.aggSupply_eq_zero_iff
#print axioms MWG.CompetitiveMarkets.aggDemand_strictAnti
#print axioms MWG.CompetitiveMarkets.aggSupply_strictMono
#print axioms MWG.CompetitiveMarkets.expConsumer
#print axioms MWG.CompetitiveMarkets.expConsumer_demand
#print axioms MWG.CompetitiveMarkets.linearFirm
#print axioms MWG.CompetitiveMarkets.quadFirmBase
#print axioms MWG.CompetitiveMarkets.quadFirm
#print axioms MWG.CompetitiveMarkets.quadFirm_supply
#print axioms MWG.CompetitiveMarkets.cubicFirmBase
#print axioms MWG.CompetitiveMarkets.cubicFirm
#print axioms MWG.CompetitiveMarkets.supply_not_differentiable_example
#print axioms MWG.CompetitiveMarkets.qlEconomy
#print axioms MWG.CompetitiveMarkets.qlPrice
#print axioms MWG.CompetitiveMarkets.qlPrice_dot
#print axioms MWG.CompetitiveMarkets.ql_supply_iff
#print axioms MWG.CompetitiveMarkets.ql_demand_iff
#print axioms MWG.CompetitiveMarkets.ql_wealth
#print axioms MWG.CompetitiveMarkets.ql_eqm_price_pos
#print axioms MWG.CompetitiveMarkets.IsQLEqm
#print axioms MWG.CompetitiveMarkets.qlEconomyOf
#print axioms MWG.CompetitiveMarkets.qlAllocation
#print axioms MWG.CompetitiveMarkets.ql_isCompetitiveEqm_iff
#print axioms MWG.CompetitiveMarkets.ql_isCompetitiveEqm_of_isQLEqm
#print axioms MWG.CompetitiveMarkets.IsQLEqm.price_pos
#print axioms MWG.CompetitiveMarkets.IsQLEqm.aggregate_pos
#print axioms MWG.CompetitiveMarkets.ql_eqm_unique
#print axioms MWG.CompetitiveMarkets.ql_eqm_exists
#print axioms MWG.CompetitiveMarkets.footnote_10_C_10
#print axioms MWG.CompetitiveMarkets.figure_10_C_4_price
#print axioms MWG.CompetitiveMarkets.figure_10_C_4_indeterminate
#print axioms MWG.CompetitiveMarkets.figure_10_C_8_cost
#print axioms MWG.CompetitiveMarkets.figure_10_C_8_no_equilibrium
#print axioms MWG.CompetitiveMarkets.qlSurplus
#print axioms MWG.CompetitiveMarkets.IsOptimalLevels
#print axioms MWG.CompetitiveMarkets.ql_feasible_iff
#print axioms MWG.CompetitiveMarkets.ql_utility
#print axioms MWG.CompetitiveMarkets.ql_sum_utility_le
#print axioms MWG.CompetitiveMarkets.eq_10_D_1
#print axioms MWG.CompetitiveMarkets.exists_pos_of_sum_pos
#print axioms MWG.CompetitiveMarkets.ql_reduce
#print axioms MWG.CompetitiveMarkets.ql_pareto_iff_le
#print axioms MWG.CompetitiveMarkets.ql_pareto_iff
#print axioms MWG.CompetitiveMarkets.IsQLEqm.isOptimalLevels
#print axioms MWG.CompetitiveMarkets.sum_update_apply
#print axioms MWG.CompetitiveMarkets.sum_update_id
#print axioms MWG.CompetitiveMarkets.hasDerivWithinAt_shift
#print axioms MWG.CompetitiveMarkets.optimalLevels_foc
#print axioms MWG.CompetitiveMarkets.optimalLevels_iff_foc
#print axioms MWG.CompetitiveMarkets.ql_eqm_sum_utility
#print axioms MWG.CompetitiveMarkets.proposition_10_D_1
#print axioms MWG.CompetitiveMarkets.IsOptimalLevels.surplus_eq
#print axioms MWG.CompetitiveMarkets.proposition_10_D_2_of_exists
#print axioms MWG.CompetitiveMarkets.proposition_10_D_2
#print axioms MWG.CompetitiveMarkets.exercise_10_D_1
#print axioms MWG.CompetitiveMarkets.exercise_10_D_1_strict
#print axioms MWG.CompetitiveMarkets.footnote_10_D_15
#print axioms MWG.CompetitiveMarkets.Economy.Solves10D6
#print axioms MWG.CompetitiveMarkets.exercise_10_D_3_of_pareto
#print axioms MWG.CompetitiveMarkets.exercise_10_D_3_pareto
#print axioms MWG.CompetitiveMarkets.exercise_10_D_4
#print axioms MWG.CompetitiveMarkets.exercise_10_D_4_converse
#print axioms MWG.CompetitiveMarkets.optimalLevels_exist
#print axioms MWG.CompetitiveMarkets.ql_eqm_exists_convex
#print axioms MWG.CompetitiveMarkets.ql_competitiveEqm_exists_convex
#print axioms MWG.CompetitiveMarkets.ql_eqm_unique_convex
#print axioms MWG.CompetitiveMarkets.proposition_10_D_2_convex
#print axioms MWG.CompetitiveMarkets.inst_convex_existence
#print axioms MWG.CompetitiveMarkets.inst_proposition_10_D_2_convex
#print axioms MWG.CompetitiveMarkets.maxMB
#print axioms MWG.CompetitiveMarkets.le_maxMB
#print axioms MWG.CompetitiveMarkets.exists_eq_maxMB
#print axioms MWG.CompetitiveMarkets.maxMB_pos
#print axioms MWG.CompetitiveMarkets.exists_lt_of_aggDemand_pos
#print axioms MWG.CompetitiveMarkets.foc_benefit_le
#print axioms MWG.CompetitiveMarkets.benefitSet
#print axioms MWG.CompetitiveMarkets.grossBenefit
#print axioms MWG.CompetitiveMarkets.grossBenefit_isGreatest
#print axioms MWG.CompetitiveMarkets.grossBenefit_eq_of_foc
#print axioms MWG.CompetitiveMarkets.exists_invDemand
#print axioms MWG.CompetitiveMarkets.invDemand
#print axioms MWG.CompetitiveMarkets.invDemand_spec
#print axioms MWG.CompetitiveMarkets.invDemand_pos
#print axioms MWG.CompetitiveMarkets.aggDemand_invDemand
#print axioms MWG.CompetitiveMarkets.invDemand_unique
#print axioms MWG.CompetitiveMarkets.invDemand_aggDemand
#print axioms MWG.CompetitiveMarkets.invDemand_le_maxMB
#print axioms MWG.CompetitiveMarkets.invDemand_strictAntiOn
#print axioms MWG.CompetitiveMarkets.invDemand_antitoneOn
#print axioms MWG.CompetitiveMarkets.optAlloc
#print axioms MWG.CompetitiveMarkets.optAlloc_foc
#print axioms MWG.CompetitiveMarkets.optAlloc_sum
#print axioms MWG.CompetitiveMarkets.grossBenefit_eq
#print axioms MWG.CompetitiveMarkets.grossBenefit_zero
#print axioms MWG.CompetitiveMarkets.exercise_10_C_4a
#print axioms MWG.CompetitiveMarkets.exercise_10_C_4b
#print axioms MWG.CompetitiveMarkets.exercise_10_C_4c
#print axioms MWG.CompetitiveMarkets.costSet
#print axioms MWG.CompetitiveMarkets.minCost
#print axioms MWG.CompetitiveMarkets.IsCostFOC
#print axioms MWG.CompetitiveMarkets.foc_cost_ge
#print axioms MWG.CompetitiveMarkets.costSet_lower
#print axioms MWG.CompetitiveMarkets.minCost_isLeast
#print axioms MWG.CompetitiveMarkets.minCost_eq_of_foc
#print axioms MWG.CompetitiveMarkets.exercise_10_C_3a
#print axioms MWG.CompetitiveMarkets.exercise_10_C_3a_sufficient
#print axioms MWG.CompetitiveMarkets.exercise_10_C_3b
#print axioms MWG.CompetitiveMarkets.exercise_10_C_3c
#print axioms MWG.CompetitiveMarkets.minMC
#print axioms MWG.CompetitiveMarkets.minMC_le
#print axioms MWG.CompetitiveMarkets.exists_eq_minMC
#print axioms MWG.CompetitiveMarkets.minMC_pos
#print axioms MWG.CompetitiveMarkets.exists_lt_of_aggSupply_pos
#print axioms MWG.CompetitiveMarkets.exists_invSupply
#print axioms MWG.CompetitiveMarkets.invSupply
#print axioms MWG.CompetitiveMarkets.invSupply_spec
#print axioms MWG.CompetitiveMarkets.aggSupply_invSupply
#print axioms MWG.CompetitiveMarkets.invSupply_pos
#print axioms MWG.CompetitiveMarkets.invSupply_unique
#print axioms MWG.CompetitiveMarkets.invSupply_aggSupply
#print axioms MWG.CompetitiveMarkets.invSupply_strictMonoOn
#print axioms MWG.CompetitiveMarkets.invSupply_monotoneOn
#print axioms MWG.CompetitiveMarkets.optPlan
#print axioms MWG.CompetitiveMarkets.optPlan_foc
#print axioms MWG.CompetitiveMarkets.optPlan_sum
#print axioms MWG.CompetitiveMarkets.minCost_eq
#print axioms MWG.CompetitiveMarkets.invSupply_hasDerivAt
#print axioms MWG.CompetitiveMarkets.exercise_10_C_3c_strict
#print axioms MWG.CompetitiveMarkets.minCost_zero
#print axioms MWG.CompetitiveMarkets.redistributionSet
#print axioms MWG.CompetitiveMarkets.welfare_lt_iff_surplus_lt
#print axioms MWG.CompetitiveMarkets.footnote_10_E_17
#print axioms MWG.CompetitiveMarkets.potential_pareto_iff
#print axioms MWG.CompetitiveMarkets.eq_10_E_4
#print axioms MWG.CompetitiveMarkets.aggSurplus
#print axioms MWG.CompetitiveMarkets.grossBenefit_continuousWithinAt_zero
#print axioms MWG.CompetitiveMarkets.minCost_continuousWithinAt_zero
#print axioms MWG.CompetitiveMarkets.aggSurplus_hasDerivAt
#print axioms MWG.CompetitiveMarkets.aggSurplus_continuousOn
#print axioms MWG.CompetitiveMarkets.invDemand_intervalIntegrable
#print axioms MWG.CompetitiveMarkets.invSupply_intervalIntegrable
#print axioms MWG.CompetitiveMarkets.eq_10_E_5
#print axioms MWG.CompetitiveMarkets.aggSurplus_zero_of_cost_zero
#print axioms MWG.CompetitiveMarkets.grossBenefit_eq_integral
#print axioms MWG.CompetitiveMarkets.minCost_eq_integral
#print axioms MWG.CompetitiveMarkets.footnote_10_E_19_concave
#print axioms MWG.CompetitiveMarkets.footnote_10_E_19
#print axioms MWG.CompetitiveMarkets.competitive_maximizes_surplus
#print axioms MWG.CompetitiveMarkets.deadweight_loss_neg
#print axioms MWG.CompetitiveMarkets.consumerSurplus
#print axioms MWG.CompetitiveMarkets.producerSurplus
#print axioms MWG.CompetitiveMarkets.QLConsumer.surplus_hasDerivAt
#print axioms MWG.CompetitiveMarkets.QLFirmStrict.profit_hasDerivAt
#print axioms MWG.CompetitiveMarkets.consumerSurplus_hasDerivAt
#print axioms MWG.CompetitiveMarkets.producerSurplus_hasDerivAt
#print axioms MWG.CompetitiveMarkets.consumerSurplus_eq_zero
#print axioms MWG.CompetitiveMarkets.eq_10_E_9
#print axioms MWG.CompetitiveMarkets.eq_10_E_8
#print axioms MWG.CompetitiveMarkets.eq_10_E_7
#print axioms MWG.CompetitiveMarkets.exercise_10_E_2
#print axioms MWG.CompetitiveMarkets.producerSurplus_eq_of_le
#print axioms MWG.CompetitiveMarkets.eq_10_E_11
#print axioms MWG.CompetitiveMarkets.eq_10_E_12
#print axioms MWG.CompetitiveMarkets.eq_10_E_10
#print axioms MWG.CompetitiveMarkets.continuousAt_of_antitoneOn_of_image_mem_nhds
#print axioms MWG.CompetitiveMarkets.invDemand_continuousAt
#print axioms MWG.CompetitiveMarkets.invDemand_hasDerivAt
#print axioms MWG.CompetitiveMarkets.exists_taxPrice
#print axioms MWG.CompetitiveMarkets.taxPrice
#print axioms MWG.CompetitiveMarkets.taxRange
#print axioms MWG.CompetitiveMarkets.taxPrice_spec
#print axioms MWG.CompetitiveMarkets.taxPrice_unique
#print axioms MWG.CompetitiveMarkets.taxQuantity
#print axioms MWG.CompetitiveMarkets.taxQuantity_pos
#print axioms MWG.CompetitiveMarkets.example_10_C_1_monotone
#print axioms MWG.CompetitiveMarkets.taxPrice_left_inverse
#print axioms MWG.CompetitiveMarkets.taxPrice_continuousAt
#print axioms MWG.CompetitiveMarkets.eq_10_C_8
#print axioms MWG.CompetitiveMarkets.example_10_C_1_bounds
#print axioms MWG.CompetitiveMarkets.example_10_C_1_formula
#print axioms MWG.CompetitiveMarkets.exercise_10_C_5
#print axioms MWG.CompetitiveMarkets.example_10_E_1
#print axioms MWG.CompetitiveMarkets.example_10_E_1_decomposition
#print axioms MWG.CompetitiveMarkets.example_10_E_1_first_order
#print axioms MWG.CompetitiveMarkets.exercise_10_C_6a
#print axioms MWG.CompetitiveMarkets.exercise_10_C_6b
#print axioms MWG.CompetitiveMarkets.exercise_10_C_6b_inelastic
#print axioms MWG.CompetitiveMarkets.exercise_10_C_6b_equivalent
#print axioms MWG.CompetitiveMarkets.exercise_10_C_7_price
#print axioms MWG.CompetitiveMarkets.exercise_10_C_7_elasticity
#print axioms MWG.CompetitiveMarkets.exercise_10_C_7_limits
#print axioms MWG.CompetitiveMarkets.example_10_C_1_instance
#print axioms MWG.CompetitiveMarkets.IsProfitMax
#print axioms MWG.CompetitiveMarkets.IsLREqm
#print axioms MWG.CompetitiveMarkets.definition_10_F_1
#print axioms MWG.CompetitiveMarkets.IsLREqmReal
#print axioms MWG.CompetitiveMarkets.PosProfit
#print axioms MWG.CompetitiveMarkets.InLRSupply
#print axioms MWG.CompetitiveMarkets.footnote_10_F_27
#print axioms MWG.CompetitiveMarkets.posProfit_unbounded
#print axioms MWG.CompetitiveMarkets.lr_crs
#print axioms MWG.CompetitiveMarkets.lr_crs_indeterminate
#print axioms MWG.CompetitiveMarkets.lrSupply_crs
#print axioms MWG.CompetitiveMarkets.exercise_10_F_1
#print axioms MWG.CompetitiveMarkets.lr_strictConvex_nonexistence
#print axioms MWG.CompetitiveMarkets.lrSupply_strictConvex
#print axioms MWG.CompetitiveMarkets.figure_10_F_3
#print axioms MWG.CompetitiveMarkets.lr_technology_not_closed
#print axioms MWG.CompetitiveMarkets.IsEfficientScale
#print axioms MWG.CompetitiveMarkets.IsEfficientScale.le_cost
#print axioms MWG.CompetitiveMarkets.lr_efficientScale
#print axioms MWG.CompetitiveMarkets.lr_integer_problem
#print axioms MWG.CompetitiveMarkets.lrSupply_efficientScale
#print axioms MWG.CompetitiveMarkets.footnote_10_F_28
#print axioms MWG.CompetitiveMarkets.footnote_10_F_28_ushaped
#print axioms MWG.CompetitiveMarkets.footnote_10_F_29
#print axioms MWG.CompetitiveMarkets.footnote_10_F_25
#print axioms MWG.CompetitiveMarkets.lr_maximizes_surplus
#print axioms MWG.CompetitiveMarkets.lumpyCost
#print axioms MWG.CompetitiveMarkets.example_10_F_1
#print axioms MWG.CompetitiveMarkets.lr_efficientScale_real
#print axioms MWG.CompetitiveMarkets.quadLumpyCost
#print axioms MWG.CompetitiveMarkets.quadLumpy_efficientScale
#print axioms MWG.CompetitiveMarkets.quadLumpy_book
#print axioms MWG.CompetitiveMarkets.exercise_10_F_2a
#print axioms MWG.CompetitiveMarkets.exercise_10_F_2a_statics
#print axioms MWG.CompetitiveMarkets.exercise_10_F_2b_supply
#print axioms MWG.CompetitiveMarkets.exercise_10_F_2b
#print axioms MWG.CompetitiveMarkets.exercise_10_F_2b_limit
#print axioms MWG.CompetitiveMarkets.exercise_10_F_3_printed
#print axioms MWG.CompetitiveMarkets.exercise_10_F_3_scale
#print axioms MWG.CompetitiveMarkets.exercise_10_F_3_prices
#print axioms MWG.CompetitiveMarkets.exercise_10_F_3_inelastic
#print axioms MWG.CompetitiveMarkets.exercise_10_F_3_counterexample
#print axioms MWG.CompetitiveMarkets.exercise_10_F_4
#print axioms MWG.CompetitiveMarkets.hasDerivAt_comp_pair
#print axioms MWG.CompetitiveMarkets.exercise_10_F_5a
#print axioms MWG.CompetitiveMarkets.exercise_10_F_5b_deriv
#print axioms MWG.CompetitiveMarkets.exercise_10_F_5b
#print axioms MWG.CompetitiveMarkets.exercise_10_F_6_longRun
#print axioms MWG.CompetitiveMarkets.exercise_10_F_6_shortRun
#print axioms MWG.CompetitiveMarkets.srCost
#print axioms MWG.CompetitiveMarkets.exercise_10_F_7_leontief
#print axioms MWG.CompetitiveMarkets.exercise_10_F_7_leontief_kink
#print axioms MWG.CompetitiveMarkets.exercise_10_F_7_vertical_supply
#print axioms MWG.CompetitiveMarkets.exercise_10_F_7_cd_longRun
#print axioms MWG.CompetitiveMarkets.exercise_10_F_7_cd_shortRun
#print axioms MWG.CompetitiveMarkets.exercise_10_F_7_cd_smooth
#print axioms MWG.CompetitiveMarkets.example_10_F_1_instance
#print axioms MWG.CompetitiveMarkets.exercise_10_C_1a
#print axioms MWG.CompetitiveMarkets.exercise_10_C_1a_wealth
#print axioms MWG.CompetitiveMarkets.exercise_10_C_1b
#print axioms MWG.CompetitiveMarkets.logConsumer_max
#print axioms MWG.CompetitiveMarkets.exercise_10_C_2a
#print axioms MWG.CompetitiveMarkets.exercise_10_C_2b
#print axioms MWG.CompetitiveMarkets.exercise_10_C_2b_statics
#print axioms MWG.CompetitiveMarkets.exercise_10_D_2
#print axioms MWG.CompetitiveMarkets.price_response_cost_param
#print axioms MWG.CompetitiveMarkets.exercise_10_C_8a
#print axioms MWG.CompetitiveMarkets.exercise_10_C_8b
#print axioms MWG.CompetitiveMarkets.exercise_10_C_8b_converse
#print axioms MWG.CompetitiveMarkets.exercise_10_C_8b_AC
#print axioms MWG.CompetitiveMarkets.exercise_10_C_8c
#print axioms MWG.CompetitiveMarkets.exercise_10_C_9
#print axioms MWG.CompetitiveMarkets.exercise_10_C_10
#print axioms MWG.CompetitiveMarkets.exercise_10_C_10_statics
#print axioms MWG.CompetitiveMarkets.exercise_10_C_11
#print axioms MWG.CompetitiveMarkets.ql_indirect_utility
#print axioms MWG.CompetitiveMarkets.ql_cv_eq_ev
#print axioms MWG.CompetitiveMarkets.hasDerivAt_comp_two
#print axioms MWG.CompetitiveMarkets.exercise_10_E_1_deriv
#print axioms MWG.CompetitiveMarkets.exercise_10_E_1_foreign_price
#print axioms MWG.CompetitiveMarkets.exercise_10_E_1a
#print axioms MWG.CompetitiveMarkets.exercise_10_E_1b
#print axioms MWG.CompetitiveMarkets.exercise_10_E_3a
#print axioms MWG.CompetitiveMarkets.exercise_10_E_3a_normalize
#print axioms MWG.CompetitiveMarkets.exercise_10_E_3b_marginal
#print axioms MWG.CompetitiveMarkets.exercise_10_E_3b
#print axioms MWG.CompetitiveMarkets.exercise_10_E_3c
#print axioms MWG.CompetitiveMarkets.exercise_10_E_3c_good_one
#print axioms MWG.CompetitiveMarkets.implicit_1d
#print axioms MWG.CompetitiveMarkets.implicit_path
#print axioms MWG.CompetitiveMarkets.exercise_10_E_1a_derived
#print axioms MWG.CompetitiveMarkets.inst_exercise_10_E_1a
#print axioms MWG.CompetitiveMarkets.ramsey_strict
#print axioms MWG.CompetitiveMarkets.exercise_10_E_3b_lagrange
#print axioms MWG.CompetitiveMarkets.inst_exercise_10_E_3b
#print axioms MWG.CompetitiveMarkets.exercise_10_C_5_derived
#print axioms MWG.CompetitiveMarkets.inst_exercise_10_C_5
#print axioms MWG.CompetitiveMarkets.group_ump_iff
#print axioms MWG.CompetitiveMarkets.IsGroupEqm
#print axioms MWG.CompetitiveMarkets.groupSurplus
#print axioms MWG.CompetitiveMarkets.IsGroupEqm.maximizes
#print axioms MWG.CompetitiveMarkets.exercise_10_G_1_unique
#print axioms MWG.CompetitiveMarkets.exercise_10_G_1_unique_strict
#print axioms MWG.CompetitiveMarkets.orthant_shift
#print axioms MWG.CompetitiveMarkets.orthant_coord_foc
#print axioms MWG.CompetitiveMarkets.dot_shift
#print axioms MWG.CompetitiveMarkets.group_consumer_foc
#print axioms MWG.CompetitiveMarkets.group_firm_foc
#print axioms MWG.CompetitiveMarkets.dot_split
#print axioms MWG.CompetitiveMarkets.exercise_10_G_2_consumer
#print axioms MWG.CompetitiveMarkets.exercise_10_G_2_surplus
#print axioms MWG.CompetitiveMarkets.exercise_10_G_2_full
#print axioms MWG.CompetitiveMarkets.exercise_10_G_3_4
#print axioms MWG.CompetitiveMarkets.exercise_10_G_3
#print axioms MWG.CompetitiveMarkets.exercise_10_G_4
#print axioms MWG.CompetitiveMarkets.exercise_10_G_5a
#print axioms MWG.CompetitiveMarkets.exercise_10_G_5b
#print axioms MWG.CompetitiveMarkets.footnote_10_G_32
#print axioms MWG.CompetitiveMarkets.footnote_10_G_32_increasing
#print axioms MWG.CompetitiveMarkets.instC
#print axioms MWG.CompetitiveMarkets.instF
#print axioms MWG.CompetitiveMarkets.inst_gap
#print axioms MWG.CompetitiveMarkets.inst_equilibrium_pareto
#print axioms MWG.CompetitiveMarkets.inst_second_welfare
#print axioms MWG.CompetitiveMarkets.inst_exercise_10_B_1b
#print axioms MWG.CompetitiveMarkets.inst_exercise_10_F_1
#print axioms MWG.CompetitiveMarkets.inst_lr_efficientScale
#print axioms MWG.CompetitiveMarkets.inst_welfare_lt
