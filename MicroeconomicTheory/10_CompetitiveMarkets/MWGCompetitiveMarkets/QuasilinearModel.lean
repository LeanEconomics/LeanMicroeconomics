/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGCompetitiveMarkets.FOCTools
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow

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
