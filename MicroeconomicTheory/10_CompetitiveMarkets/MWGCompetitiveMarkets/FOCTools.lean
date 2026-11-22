/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.MonotoneContinuity

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
