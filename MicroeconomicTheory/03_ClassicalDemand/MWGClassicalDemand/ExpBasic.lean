/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.DualitySupport
import MWGClassicalDemand.UMPBasic

/-!
# The expenditure minimization problem

MWG, Section 3.E, pp. 57-63, and Exercises 3.E.1, 3.E.3, 3.E.4 (pp. 61, 98).

* The EMP `min p·x` subject to `x ∈ ℝ^L_+`, `u(x) ≥ ū`; its constraint set
  `empConstraintSet u ū`, the Hicksian demand correspondence `hicksianDemand u p ū` (the set of
  solutions) and the expenditure function `expenditure u p ū`. The expenditure function is by
  definition the support function of the constraint set (Section 3.F, p. 66).
* Existence (Exercise 3.E.3), Proposition 3.E.1 (UMP and EMP are dual), Proposition 3.E.2(i)-(iii)
  (homogeneity, monotonicity, concavity), the relations (3.E.1) and (3.E.4), Proposition 3.E.3
  (homogeneity, no excess utility, convexity/uniqueness = Exercise 3.E.4) and Proposition 3.E.4
  (the compensated law of demand, for arbitrary selections).
* Exercise 3.E.1: the first-order conditions (3.E.2)-(3.E.3) hold with multiplier `1/λ`, `λ` the
  UMP multiplier at wealth `p·x*`, whenever `λ > 0`; without a constraint qualification they can
  fail (`exercise_3_E_1_counterexample`, correction B2).
* Exercise 3.E.4 as printed ("if `u` is strictly convex") is false; the corrected statement
  (strictly convex `≿`) is proved (correction B3).
-/

namespace MWG.ClassicalDemand

open MWG.ConsumerChoice Kreps.PreferenceProperties Filter Topology

variable {L : ℕ}

/-- **Section 3.E** (MWG, p. 58). The constraint set `{x ∈ ℝ^L_+ : u(x) ≥ ū}` of the EMP. -/
def empConstraintSet (u : (Fin L → ℝ) → ℝ) (ub : ℝ) : Set (Fin L → ℝ) :=
  {x | x ∈ nonnegOrthant L ∧ ub ≤ u x}

/-- **Section 3.E** (MWG, pp. 60-61). The Hicksian (compensated) demand correspondence
`h(p, ū)`: the solutions of the EMP `min p·x` s.t. `x ≥ 0`, `u(x) ≥ ū`. -/
def hicksianDemand (u : (Fin L → ℝ) → ℝ) (p : Fin L → ℝ) (ub : ℝ) : Set (Fin L → ℝ) :=
  supportArgmin (empConstraintSet u ub) p

/-- **Section 3.E** (MWG, p. 59). The expenditure function `e(p, ū)`, the value of the EMP. It
is the support function of `{x ∈ ℝ^L_+ : u(x) ≥ ū}` (MWG, p. 66). -/
noncomputable def expenditure (u : (Fin L → ℝ) → ℝ) (p : Fin L → ℝ) (ub : ℝ) : ℝ :=
  supportFn (empConstraintSet u ub) p

/-- **Section 3.F** (MWG, p. 66). The expenditure function is the support function of
`{x ∈ ℝ^L_+ : u(x) ≥ ū}`. -/
theorem expenditure_eq_supportFn (u : (Fin L → ℝ) → ℝ) (p : Fin L → ℝ) (ub : ℝ) :
    expenditure u p ub = supportFn (empConstraintSet u ub) p := rfl

/-- Membership in `h(p, ū)`, unfolded. -/
theorem mem_hicksianDemand_iff (u : (Fin L → ℝ) → ℝ) (p : Fin L → ℝ) (ub : ℝ)
    (x : Fin L → ℝ) : x ∈ hicksianDemand u p ub ↔
      (x ∈ nonnegOrthant L ∧ ub ≤ u x) ∧
        ∀ y, y ∈ nonnegOrthant L → ub ≤ u y → p ⬝ᵥ x ≤ p ⬝ᵥ y :=
  ⟨fun h => ⟨h.1, fun y hy hu => h.2 y ⟨hy, hu⟩⟩, fun h => ⟨h.1, fun y hy => h.2 y hy.1 hy.2⟩⟩

/-- The nonnegative orthant is closed. -/
theorem exp_isClosed_nonnegOrthant (L : ℕ) : IsClosed (nonnegOrthant L) := by
  have : nonnegOrthant L = ⋂ l : Fin L, {x : Fin L → ℝ | 0 ≤ x l} := by
    ext x; simp [nonnegOrthant]
  rw [this]
  exact isClosed_iInter fun l => isClosed_le continuous_const (continuous_apply l)

/-- The EMP constraint set of a utility continuous on `ℝ^L_+` is closed. -/
theorem isClosed_empConstraintSet {u : (Fin L → ℝ) → ℝ}
    (hu : ContinuousOn u (nonnegOrthant L)) (ub : ℝ) : IsClosed (empConstraintSet u ub) :=
  hu.preimage_isClosed_of_isClosed (exp_isClosed_nonnegOrthant L) isClosed_Ici

/-- With `p ≥ 0`, expenditure on bundles of `ℝ^L_+` is bounded below by `0`. -/
theorem exp_bddBelow {u : (Fin L → ℝ) → ℝ} {p : Fin L → ℝ} (hp : StrictlyPositive p)
    (ub : ℝ) : BddBelow ((fun x => p ⬝ᵥ x) '' empConstraintSet u ub) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact Finset.sum_nonneg fun l _ => mul_nonneg (hp l).le (hx.1 l)

/-- `e(p, ū) ≥ 0` for `p ≫ 0`. -/
theorem expenditure_nonneg (u : (Fin L → ℝ) → ℝ) {p : Fin L → ℝ} (hp : StrictlyPositive p)
    (ub : ℝ) : 0 ≤ expenditure u p ub := by
  rcases (empConstraintSet u ub).eq_empty_or_nonempty with h | h
  · simp [expenditure, supportFn, h]
  · exact le_supportFn h fun x hx => Finset.sum_nonneg fun l _ => mul_nonneg (hp l).le (hx.1 l)

/-- `p·x > 0` for `p ≫ 0` and a nonzero `x ≥ 0`. -/
theorem exp_dotProduct_pos {p x : Fin L → ℝ} (hp : StrictlyPositive p)
    (hx : x ∈ nonnegOrthant L) (hne : x ≠ 0) : 0 < p ⬝ᵥ x := by
  obtain ⟨l, hl⟩ : ∃ l, x l ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (funext h)
  exact Finset.sum_pos' (fun k _ => mul_nonneg (hp k).le (hx k))
    ⟨l, Finset.mem_univ l, mul_pos (hp l) (lt_of_le_of_ne (hx l) (Ne.symm hl))⟩

/-- The scaling step used in the proofs of Propositions 3.E.1(ii), 3.E.2(ii) and 3.E.3(ii)
(MWG, pp. 59, 61): if `u` is continuous on `ℝ^L_+` and `u(y) > t`, then `u(αy) > t` for some
`α ∈ (0, 1)`. -/
theorem exp_exists_scale_down {u : (Fin L → ℝ) → ℝ} (hu : ContinuousOn u (nonnegOrthant L))
    {y : Fin L → ℝ} (hy : y ∈ nonnegOrthant L) {t : ℝ} (ht : t < u y) :
    ∃ α : ℝ, 0 < α ∧ α < 1 ∧ t < u (α • y) := by
  have hpath : Tendsto (fun α : ℝ => α • y) (𝓝[<] 1) (𝓝[nonnegOrthant L] y) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have : Tendsto (fun α : ℝ => α • y) (𝓝 1) (𝓝 ((1 : ℝ) • y)) :=
        (continuous_id.smul continuous_const).tendsto 1
      rw [one_smul] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with α hα l
      exact mul_nonneg hα.1.le (hy l)
  have hlim := ((hu y hy).tendsto.comp hpath).eventually (lt_mem_nhds ht)
  have hI : ∀ᶠ α in 𝓝[<] (1 : ℝ), α ∈ Set.Ioo 0 1 := Ioo_mem_nhdsLT (by norm_num)
  obtain ⟨α, hα, hlt⟩ := (hI.and hlim).exists
  exact ⟨α, hα.1, hα.2, hlt⟩

/-- **Exercise 3.E.3** (MWG, pp. 59, 98). A solution to the EMP exists if `p ≫ 0`, `u` is
continuous and some `x ∈ ℝ^L_+` has `u(x) ≥ ū`. -/
theorem exercise_3_E_3 {u : (Fin L → ℝ) → ℝ} (hu : ContinuousOn u (nonnegOrthant L))
    {p : Fin L → ℝ} (hp : StrictlyPositive p) {ub : ℝ}
    (hne : ∃ x ∈ nonnegOrthant L, ub ≤ u x) : (hicksianDemand u p ub).Nonempty := by
  obtain ⟨x0, hx0, hux0⟩ := hne
  set S := budgetSet p (p ⬝ᵥ x0) ∩ empConstraintSet u ub
  have hS : IsCompact S := (isCompact_budgetSet hp _).inter_right (isClosed_empConstraintSet hu ub)
  have hSne : S.Nonempty := ⟨x0, ⟨hx0, le_rfl⟩, hx0, hux0⟩
  obtain ⟨x, hxS, hmin⟩ :=
    hS.exists_isMinOn hSne (by fun_prop : Continuous fun y => p ⬝ᵥ y).continuousOn
  refine ⟨x, hxS.2, fun y hy => ?_⟩
  by_cases hy0 : p ⬝ᵥ y ≤ p ⬝ᵥ x0
  · exact hmin ⟨⟨hy.1, hy0⟩, hy⟩
  · exact hxS.1.2.trans (not_le.mp hy0).le

/-- At `p ≫ 0` the expenditure function is attained: `e(p, ū) = p·x` for `x ∈ h(p, ū)`. -/
theorem expenditure_eq_of_mem {u : (Fin L → ℝ) → ℝ} {p : Fin L → ℝ} {ub : ℝ}
    {x : Fin L → ℝ} (hx : x ∈ hicksianDemand u p ub) : expenditure u p ub = p ⬝ᵥ x :=
  supportFn_eq_of_mem_argmin hx

/-- **Proposition 3.E.1(i)** (MWG, p. 58). If `x*` solves the UMP at `p ≫ 0` and wealth `w`,
then `x*` solves the EMP with required utility `u(x*)`, and the minimized expenditure is `w`.
(Uses local nonsatiation; `w > 0` is not needed.) -/
theorem proposition_3_E_1_i {u : (Fin L → ℝ) → ℝ} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hu : RepresentsOn (nonnegOrthant L) u r) (hlns : LocallyNonsatiated (nonnegOrthant L) r)
    {p : Fin L → ℝ} {w : ℝ} {x : Fin L → ℝ} (hx : x ∈ walrasianDemand u p w) :
    x ∈ hicksianDemand u p (u x) ∧ expenditure u p (u x) = w := by
  have hxh : x ∈ hicksianDemand u p (u x) := by
    refine ⟨⟨hx.1.1, le_rfl⟩, fun y hy => ?_⟩
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨z, hz, hpz, hs⟩ := exists_better_affordable hlns p hy.1 (hlt.trans_le hx.1.2)
    have h1 := hx.2 z ⟨hz, hpz.le⟩
    have h2 := (hu.strict_iff hz hy.1).mp hs
    linarith [hy.2]
  exact ⟨hxh, (expenditure_eq_of_mem hxh).trans (proposition_3_D_2_ii hu hlns hx)⟩

/-- **Proposition 3.E.3(ii)** (MWG, p. 61). No excess utility: if `u` is continuous on `ℝ^L_+`,
`p ≫ 0` and `ū ≥ u(0)`, every `x ∈ h(p, ū)` has `u(x) = ū`. (The book's standing assumption is
`ū > u(0)`; local nonsatiation is not used.) -/
theorem proposition_3_E_3_ii {u : (Fin L → ℝ) → ℝ} (hu : ContinuousOn u (nonnegOrthant L))
    {p : Fin L → ℝ} (hp : StrictlyPositive p) {ub : ℝ} (hub : u 0 ≤ ub) {x : Fin L → ℝ}
    (hx : x ∈ hicksianDemand u p ub) : u x = ub := by
  by_contra hne
  have hgt : ub < u x := lt_of_le_of_ne hx.1.2 (Ne.symm hne)
  have hx0 : x ≠ 0 := by
    rintro rfl
    linarith
  obtain ⟨α, hα0, hα1, hα⟩ := exp_exists_scale_down hu hx.1.1 hgt
  have hmem : α • x ∈ empConstraintSet u ub :=
    ⟨fun l => mul_nonneg hα0.le (hx.1.1 l), hα.le⟩
  have h1 := hx.2 _ hmem
  have hpos := exp_dotProduct_pos hp hx.1.1 hx0
  rw [dotProduct_smul, smul_eq_mul] at h1
  nlinarith

/-- **Proposition 3.E.1(ii)** (MWG, p. 58). If `x*` solves the EMP at `p ≫ 0` with required
utility `ū > u(0)`, then `x*` solves the UMP at wealth `p·x*`, and the maximized utility is
`ū`. -/
theorem proposition_3_E_1_ii {u : (Fin L → ℝ) → ℝ} (hu : ContinuousOn u (nonnegOrthant L))
    {p : Fin L → ℝ} (hp : StrictlyPositive p) {ub : ℝ} (hub : u 0 < ub) {x : Fin L → ℝ}
    (hx : x ∈ hicksianDemand u p ub) :
    x ∈ walrasianDemand u p (p ⬝ᵥ x) ∧ indirectUtility u p (p ⬝ᵥ x) = ub := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    linarith [hx.1.2]
  have hpos := exp_dotProduct_pos hp hx.1.1 hx0
  have hxw : x ∈ walrasianDemand u p (p ⬝ᵥ x) := by
    refine ⟨⟨hx.1.1, le_rfl⟩, fun y hy => ?_⟩
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨α, hα0, hα1, hα⟩ := exp_exists_scale_down hu hy.1 hlt
    have hmem : α • y ∈ empConstraintSet u ub :=
      ⟨fun l => mul_nonneg hα0.le (hy.1 l), hx.1.2.trans hα.le⟩
    have h1 := hx.2 _ hmem
    rw [dotProduct_smul, smul_eq_mul] at h1
    have h2 : α * p ⬝ᵥ y ≤ α * p ⬝ᵥ x := mul_le_mul_of_nonneg_left hy.2 hα0.le
    nlinarith
  exact ⟨hxw, (indirectUtility_eq_of_mem hxw).trans (proposition_3_E_3_ii hu hp hub.le hx)⟩

/-- **Proposition 3.E.3(i)** (MWG, p. 61). `h(αp, ū) = h(p, ū)` for `α > 0`. -/
theorem proposition_3_E_3_i (u : (Fin L → ℝ) → ℝ) (p : Fin L → ℝ) (ub : ℝ) {α : ℝ}
    (hα : 0 < α) : hicksianDemand u (α • p) ub = hicksianDemand u p ub := by
  ext x
  simp only [hicksianDemand, supportArgmin, Set.mem_ofPred_eq, smul_dotProduct, smul_eq_mul]
  constructor
  · rintro ⟨hx, h⟩
    exact ⟨hx, fun y hy => le_of_mul_le_mul_left (h y hy) hα⟩
  · rintro ⟨hx, h⟩
    exact ⟨hx, fun y hy => mul_le_mul_of_nonneg_left (h y hy) hα.le⟩

/-- **Proposition 3.E.3(iii)** and **Exercise 3.E.4**, first part (MWG, pp. 61, 98). If `u` is
quasiconcave on `ℝ^L_+` (i.e. `≿` is convex), `h(p, ū)` is convex. -/
theorem exercise_3_E_4_convex {u : (Fin L → ℝ) → ℝ} (hq : QuasiconcaveOn ℝ (nonnegOrthant L) u)
    (p : Fin L → ℝ) (ub : ℝ) : Convex ℝ (hicksianDemand u p ub) := by
  intro x hx y hy a b ha hb hab
  have hK : Convex ℝ (empConstraintSet u ub) := hq ub
  have hxy : p ⬝ᵥ x = p ⬝ᵥ y := le_antisymm (hx.2 y hy.1) (hy.2 x hx.1)
  refine ⟨hK hx.1 hy.1 ha hb hab, fun z hz => ?_⟩
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
  rw [← hxy, ← add_mul, hab, one_mul]
  exact hx.2 z hz

/-- **Proposition 3.E.3(iii)** and **Exercise 3.E.4**, second part (corrected; MWG, pp. 61,
98). If `u` is continuous and strictly quasiconcave on `ℝ^L_+` (i.e. `≿` is strictly convex)
and `p ≫ 0`, then `h(p, ū)` has at most one element. -/
theorem exercise_3_E_4_unique {u : (Fin L → ℝ) → ℝ} (hu : ContinuousOn u (nonnegOrthant L))
    (hq : StrictlyQuasiconcaveOn (nonnegOrthant L) u) {p : Fin L → ℝ} (hp : StrictlyPositive p)
    (ub : ℝ) : (hicksianDemand u p ub).Subsingleton := by
  intro x hx y hy
  by_contra hne
  have hxy : p ⬝ᵥ x = p ⬝ᵥ y := le_antisymm (hx.2 y hy.1) (hy.2 x hx.1)
  set z : Fin L → ℝ := (1 / 2 : ℝ) • x + (1 - 1 / 2 : ℝ) • y with hz
  have hz0 : z ∈ nonnegOrthant L := convex_nonnegOrthant L hx.1.1 hy.1.1 (by norm_num)
    (by norm_num) (by norm_num)
  have hlt : ub < u z := hq.2 x hx.1.1 y hy.1.1 hne (1 / 2) (by norm_num) (by norm_num) ub
    hx.1.2 hy.1.2
  have hpz : p ⬝ᵥ z = p ⬝ᵥ x := by
    rw [hz, dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← hxy]
    ring
  have hzne : z ≠ 0 := by
    intro h
    have hx0 : p ⬝ᵥ x = 0 := by rw [← hpz, h, dotProduct_zero]
    have : x = 0 := by
      by_contra hx0'
      exact (exp_dotProduct_pos hp hx.1.1 hx0').ne' hx0
    have : y = 0 := by
      by_contra hy0'
      exact (exp_dotProduct_pos hp hy.1.1 hy0').ne' (hxy ▸ hx0)
    exact hne (by simp_all)
  obtain ⟨α, hα0, hα1, hα⟩ := exp_exists_scale_down hu hz0 hlt
  have hmem : α • z ∈ empConstraintSet u ub := ⟨fun l => mul_nonneg hα0.le (hz0 l), hα.le⟩
  have h1 := hx.2 _ hmem
  have hpos := exp_dotProduct_pos hp hz0 hzne
  rw [dotProduct_smul, smul_eq_mul, hpz] at h1
  rw [hpz] at hpos
  nlinarith

/-- **Proposition 3.E.3(iii)** (MWG, p. 61), in the book's terms: for a continuous `u`
representing `≿` on `ℝ^L_+` and `p ≫ 0`, `h(p, ū)` is convex if `≿` is convex and has at most
one element if `≿` is strictly convex. -/
theorem proposition_3_E_3_iii {u : (Fin L → ℝ) → ℝ} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hrep : RepresentsOn (nonnegOrthant L) u r) (hu : ContinuousOn u (nonnegOrthant L))
    {p : Fin L → ℝ} (hp : StrictlyPositive p) (ub : ℝ) :
    (PrefConvex (nonnegOrthant L) r → Convex ℝ (hicksianDemand u p ub)) ∧
      (PrefStrictlyConvex (nonnegOrthant L) r → (hicksianDemand u p ub).Subsingleton) :=
  ⟨fun h => exercise_3_E_4_convex
      ((prefConvex_iff_quasiconcaveOn (convex_nonnegOrthant L) hrep).mp h) p ub,
    fun h => exercise_3_E_4_unique hu
      ((prefStrictlyConvex_iff_strictlyQuasiconcaveOn (convex_nonnegOrthant L) hrep).mp h) hp ub⟩

/-- The strictly convex utility `x₁² + x₂²` of correction B3. -/
def exercise_3_E_4_utility (x : Fin 2 → ℝ) : ℝ := x 0 ^ 2 + x 1 ^ 2

/-- **Exercise 3.E.4** (MWG, p. 98) as printed is false (correction B3): `u(x) = x₁² + x₂²` is
a strictly convex function, yet at `p = (1, 1)`, `ū = 1` the EMP has the two solutions `(1, 0)`
and `(0, 1)`. -/
theorem exercise_3_E_4_printed_counterexample :
    StrictConvexOn ℝ (nonnegOrthant 2) exercise_3_E_4_utility ∧
      ![1, 0] ∈ hicksianDemand exercise_3_E_4_utility ![1, 1] 1 ∧
      ![0, 1] ∈ hicksianDemand exercise_3_E_4_utility ![1, 1] 1 ∧
      (![1, 0] : Fin 2 → ℝ) ≠ ![0, 1] := by
  have hval : ∀ y : Fin 2 → ℝ, (![1, 1] : Fin 2 → ℝ) ⬝ᵥ y = y 0 + y 1 := by
    intro y; simp [dotProduct, Fin.sum_univ_two]
  have hmin : ∀ y : Fin 2 → ℝ, y ∈ empConstraintSet exercise_3_E_4_utility 1 → 1 ≤ y 0 + y 1 := by
    rintro y ⟨hy0, hy⟩
    simp only [exercise_3_E_4_utility] at hy
    have h0 := hy0 0
    have h1 := hy0 1
    nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨convex_nonnegOrthant 2, fun x _ y _ hxy a b ha hb hab => ?_⟩
    have hd : x - y ≠ 0 := sub_ne_zero.mpr hxy
    have hdl : x 0 - y 0 ≠ 0 ∨ x 1 - y 1 ≠ 0 := by
      by_contra h
      push Not at h
      apply hd
      funext i
      fin_cases i <;> simp [h.1, h.2]
    simp only [exercise_3_E_4_utility, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hb' : b = 1 - a := by linarith
    subst hb'
    have hab' : 0 < a * (1 - a) := mul_pos ha hb
    rcases hdl with h | h
    · have := mul_pos hab' (pow_pos (abs_pos.mpr h) 2)
      rw [sq_abs] at this
      nlinarith [sq_nonneg (x 1 - y 1), mul_nonneg hab'.le (sq_nonneg (x 1 - y 1))]
    · have := mul_pos hab' (pow_pos (abs_pos.mpr h) 2)
      rw [sq_abs] at this
      nlinarith [sq_nonneg (x 0 - y 0), mul_nonneg hab'.le (sq_nonneg (x 0 - y 0))]
  · refine ⟨⟨fun i => by fin_cases i <;> simp, by simp [exercise_3_E_4_utility]⟩, fun y hy => ?_⟩
    rw [hval, hval]
    simpa using hmin y hy
  · refine ⟨⟨fun i => by fin_cases i <;> simp, by simp [exercise_3_E_4_utility]⟩, fun y hy => ?_⟩
    rw [hval, hval]
    simpa using hmin y hy
  · intro h
    have := congrFun h 0
    simp at this

/-- **Proposition 3.E.2(i)** (MWG, p. 59). `e(αp, ū) = α e(p, ū)` for `α > 0`. -/
theorem proposition_3_E_2_i (u : (Fin L → ℝ) → ℝ) (p : Fin L → ℝ) (ub : ℝ) {α : ℝ}
    (hα : 0 < α) : expenditure u (α • p) ub = α * expenditure u p ub :=
  supportFn_smul _ p hα.le

/-- **Proposition 3.E.2(ii)** (MWG, p. 59), first half. For `u` continuous on `ℝ^L_+`,
`p ≫ 0` and `u(0) < ū < ū'` with `ū'` attainable, `e(p, ū) < e(p, ū')`. -/
theorem proposition_3_E_2_ii_utility {u : (Fin L → ℝ) → ℝ}
    (hu : ContinuousOn u (nonnegOrthant L)) {p : Fin L → ℝ} (hp : StrictlyPositive p)
    {ub ub' : ℝ} (hub : u 0 < ub) (hlt : ub < ub') (hne : ∃ x ∈ nonnegOrthant L, ub' ≤ u x) :
    expenditure u p ub < expenditure u p ub' := by
  obtain ⟨x, hx⟩ := exercise_3_E_3 hu hp hne
  have hx0 : x ≠ 0 := by
    rintro rfl
    linarith [hx.1.2]
  obtain ⟨α, hα0, hα1, hα⟩ := exp_exists_scale_down hu hx.1.1 (hlt.trans_le hx.1.2)
  have hmem : α • x ∈ empConstraintSet u ub := ⟨fun l => mul_nonneg hα0.le (hx.1.1 l), hα.le⟩
  have h1 := supportFn_le (exp_bddBelow hp ub) hmem
  rw [dotProduct_smul, smul_eq_mul] at h1
  have hpos := exp_dotProduct_pos hp hx.1.1 hx0
  rw [expenditure_eq_of_mem hx]
  change expenditure u p ub ≤ _ at h1
  nlinarith

/-- **Proposition 3.E.2(ii)** (MWG, p. 59), second half. `e(p, ū)` is nondecreasing in prices:
`p ≤ p'` (both `≫ 0`) implies `e(p, ū) ≤ e(p', ū)`. -/
theorem proposition_3_E_2_ii_prices (u : (Fin L → ℝ) → ℝ) {p p' : Fin L → ℝ}
    (hp : StrictlyPositive p) (hpp : p ≤ p') (ub : ℝ) :
    expenditure u p ub ≤ expenditure u p' ub := by
  rcases (empConstraintSet u ub).eq_empty_or_nonempty with h | h
  · simp [expenditure, supportFn, h]
  apply le_supportFn h
  intro x hx
  exact (supportFn_le (exp_bddBelow hp ub) hx).trans
    (dotProduct_le_dotProduct_of_nonneg_right hpp hx.1)

/-- The set of strictly positive price vectors is convex. -/
theorem exp_convex_strictlyPositive (L : ℕ) : Convex ℝ {p : Fin L → ℝ | StrictlyPositive p} := by
  intro p hp p' hp' a b ha hb hab l
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rcases ha.lt_or_eq with ha' | ha'
  · exact add_pos_of_pos_of_nonneg (mul_pos ha' (hp l)) (mul_nonneg hb (hp' l).le)
  · subst ha'
    simp only [zero_add] at hab
    subst hab
    simpa using hp' l

/-- **Proposition 3.E.2(iii)** (MWG, p. 60). `e(p, ū)` is concave in `p` on `{p ≫ 0}`. -/
theorem proposition_3_E_2_iii (u : (Fin L → ℝ) → ℝ) (ub : ℝ) :
    ConcaveOn ℝ {p : Fin L → ℝ | StrictlyPositive p} (fun p => expenditure u p ub) := by
  rcases (empConstraintSet u ub).eq_empty_or_nonempty with h | h
  · have : (fun p => expenditure u p ub) = fun _ => 0 := by
      funext p; simp [expenditure, supportFn, h]
    rw [this]
    exact concaveOn_const 0 (exp_convex_strictlyPositive L)
  · exact (supportFn_concaveOn h).subset (fun p hp => exp_bddBelow hp ub)
      (exp_convex_strictlyPositive L)

/-- **Section 3.E** (MWG, p. 60; Figure 3.E.2(a)). The graph of `e(·, ū)` lies below the linear
function `p ↦ p·x̄` and touches it at `p̄`, for `x̄ ∈ h(p̄, ū)`. -/
theorem expenditure_le_linear {u : (Fin L → ℝ) → ℝ} {p₀ p : Fin L → ℝ} {ub : ℝ}
    {x : Fin L → ℝ} (hx : x ∈ hicksianDemand u p₀ ub) (hp : StrictlyPositive p) :
    expenditure u p ub ≤ p ⬝ᵥ x ∧ expenditure u p₀ ub = p₀ ⬝ᵥ x :=
  ⟨supportFn_le (exp_bddBelow hp ub) hx.1, expenditure_eq_of_mem hx⟩

/-- **Equation (3.E.1)** (MWG, p. 60), first identity: `e(p, v(p, w)) = w` for `p ≫ 0`,
`w ≥ 0`. -/
theorem equation_3_E_1_left {u : (Fin L → ℝ) → ℝ} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hrep : RepresentsOn (nonnegOrthant L) u r) (hu : ContinuousOn u (nonnegOrthant L))
    (hlns : LocallyNonsatiated (nonnegOrthant L) r) {p : Fin L → ℝ} (hp : StrictlyPositive p)
    {w : ℝ} (hw : 0 ≤ w) : expenditure u p (indirectUtility u p w) = w := by
  obtain ⟨x, hx⟩ := proposition_3_D_1 hu hp hw
  rw [indirectUtility_eq_of_mem hx]
  exact (proposition_3_E_1_i hrep hlns hx).2

/-- **Equation (3.E.1)** (MWG, p. 60), second identity: `v(p, e(p, ū)) = ū` for `p ≫ 0`,
`ū > u(0)` attainable. -/
theorem equation_3_E_1_right {u : (Fin L → ℝ) → ℝ} (hu : ContinuousOn u (nonnegOrthant L))
    {p : Fin L → ℝ} (hp : StrictlyPositive p) {ub : ℝ} (hub : u 0 < ub)
    (hne : ∃ x ∈ nonnegOrthant L, ub ≤ u x) : indirectUtility u p (expenditure u p ub) = ub := by
  obtain ⟨x, hx⟩ := exercise_3_E_3 hu hp hne
  rw [expenditure_eq_of_mem hx]
  exact (proposition_3_E_1_ii hu hp hub hx).2

/-- `v(p, w) ≥ u(0)` for `w ≥ 0`. -/
theorem exp_indirectUtility_ge_zero {u : (Fin L → ℝ) → ℝ}
    (hu : ContinuousOn u (nonnegOrthant L)) {p : Fin L → ℝ} (hp : StrictlyPositive p) {w : ℝ}
    (hw : 0 ≤ w) : u 0 ≤ indirectUtility u p w :=
  le_indirectUtility hu hp (zero_mem_budgetSet p hw)

/-- **Equation (3.E.4)** (MWG, p. 62), first identity: `h(p, ū) = x(p, e(p, ū))` for
`p ≫ 0`, `ū > u(0)` attainable. -/
theorem equation_3_E_4_left {u : (Fin L → ℝ) → ℝ} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hrep : RepresentsOn (nonnegOrthant L) u r) (hu : ContinuousOn u (nonnegOrthant L))
    (hlns : LocallyNonsatiated (nonnegOrthant L) r) {p : Fin L → ℝ} (hp : StrictlyPositive p)
    {ub : ℝ} (hub : u 0 < ub) (hne : ∃ x ∈ nonnegOrthant L, ub ≤ u x) :
    hicksianDemand u p ub = walrasianDemand u p (expenditure u p ub) := by
  ext y
  constructor
  · intro hy
    rw [expenditure_eq_of_mem hy]
    exact (proposition_3_E_1_ii hu hp hub hy).1
  · intro hy
    have h1 := proposition_3_E_1_i hrep hlns hy
    have h2 : u y = ub := by
      rw [← indirectUtility_eq_of_mem hy]
      exact equation_3_E_1_right hu hp hub hne
    rw [← h2]
    exact h1.1

/-- **Equation (3.E.4)** (MWG, p. 62), second identity: `x(p, w) = h(p, v(p, w))` for
`p ≫ 0`, `w ≥ 0`. -/
theorem equation_3_E_4_right {u : (Fin L → ℝ) → ℝ} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hrep : RepresentsOn (nonnegOrthant L) u r) (hu : ContinuousOn u (nonnegOrthant L))
    (hlns : LocallyNonsatiated (nonnegOrthant L) r) {p : Fin L → ℝ} (hp : StrictlyPositive p)
    {w : ℝ} (hw : 0 ≤ w) :
    walrasianDemand u p w = hicksianDemand u p (indirectUtility u p w) := by
  ext y
  constructor
  · intro hy
    rw [indirectUtility_eq_of_mem hy]
    exact (proposition_3_E_1_i hrep hlns hy).1
  · intro hy
    obtain ⟨x, hx⟩ := proposition_3_D_1 hu hp hw
    have hv := indirectUtility_eq_of_mem hx
    have he : p ⬝ᵥ y = w := by
      rw [← expenditure_eq_of_mem hy]
      exact equation_3_E_1_left hrep hu hlns hp hw
    have hyx : y ∈ hicksianDemand u p (u x) := hv ▸ hy
    -- `y` is affordable at `w` and gives utility at least `u(x)`
    refine ⟨⟨hy.1.1, he.le⟩, fun z hz => ?_⟩
    have := hx.2 z hz
    rw [hv] at hy
    exact this.trans hyx.1.2

/-- **Proposition 3.E.4** (MWG, p. 62), the compensated law of demand (3.E.5): for any
`h' ∈ h(p', ū)` and `h'' ∈ h(p'', ū)`, `(p'' - p')·(h'' - h') ≤ 0`. (Single-valuedness, assumed
in the book, is not needed.) -/
theorem proposition_3_E_4 (u : (Fin L → ℝ) → ℝ) {p' p'' : Fin L → ℝ} {ub : ℝ}
    {h' h'' : Fin L → ℝ} (h1 : h' ∈ hicksianDemand u p' ub)
    (h2 : h'' ∈ hicksianDemand u p'' ub) : (p'' - p') ⬝ᵥ (h'' - h') ≤ 0 := by
  have a := h2.2 h' h1.1
  have b := h1.2 h'' h2.1
  simp only [sub_dotProduct, dotProduct_sub]
  linarith

/-- **Section 3.E** (MWG, p. 63). Compensated own-price effects are nonpositive: if only `p_l`
changes, `(p''_l - p'_l)(h_l(p'', ū) - h_l(p', ū)) ≤ 0`. -/
theorem compensated_own_price (u : (Fin L → ℝ) → ℝ) {p' p'' : Fin L → ℝ} {ub : ℝ} {l : Fin L}
    (hother : ∀ k, k ≠ l → p'' k = p' k) {h' h'' : Fin L → ℝ}
    (h1 : h' ∈ hicksianDemand u p' ub) (h2 : h'' ∈ hicksianDemand u p'' ub) :
    (p'' l - p' l) * (h'' l - h' l) ≤ 0 := by
  have := proposition_3_E_4 u h1 h2
  have hsum : (p'' - p') ⬝ᵥ (h'' - h') = (p'' l - p' l) * (h'' l - h' l) := by
    rw [dotProduct, Finset.sum_eq_single l]
    · simp
    · intro k _ hk
      simp [hother k hk]
    · simp
  linarith

/-- **Exercise 3.E.1** (MWG, p. 61). At a solution `x*` of the EMP with `ū > u(0)` and `p ≫ 0`,
if `u` is differentiable at `x*`, the UMP conditions (3.D.1) hold at wealth `p·x*` with some
`λ ≥ 0`; whenever `λ > 0` the EMP conditions (3.E.2)-(3.E.3) hold with multiplier `1/λ`:
`p ≥ (1/λ)∇u(x*)` and `x*·[p - (1/λ)∇u(x*)] = 0`. -/
theorem exercise_3_E_1 {u : (Fin L → ℝ) → ℝ} (hu : ContinuousOn u (nonnegOrthant L))
    {u' : (Fin L → ℝ) →L[ℝ] ℝ} {p : Fin L → ℝ} (hp : StrictlyPositive p) {ub : ℝ}
    (hub : u 0 < ub) {x : Fin L → ℝ} (hx : x ∈ hicksianDemand u p ub)
    (hd : HasFDerivAt u u' x) :
    ∃ lam : ℝ, 0 ≤ lam ∧ (∀ l, gradientVec u' l ≤ lam * p l ∧
      (0 < x l → gradientVec u' l = lam * p l)) ∧
      (0 < lam → (∀ l, (1 / lam) * gradientVec u' l ≤ p l) ∧
        x ⬝ᵥ (p - (1 / lam) • gradientVec u') = 0) := by
  obtain ⟨lam, hlam, hkt⟩ := ump_kuhn_tucker hp (proposition_3_E_1_ii hu hp hub hx).1 hd
  refine ⟨lam, hlam, hkt, fun hpos => ⟨fun l => ?_, ?_⟩⟩
  · rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hpos, mul_comm]
    exact (hkt l).1
  · simp only [dotProduct, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_eq_zero fun l _ => ?_
    rcases (hx.1.1 l).lt_or_eq with h | h
    · rw [(hkt l).2 h]
      field_simp
      ring
    · rw [← h]; ring

/-- **Exercise 3.E.1** (MWG, p. 61), the multiplier is positive when some consumed good has a
nonzero marginal utility. -/
theorem exercise_3_E_1_lam_pos {u' : (Fin L → ℝ) →L[ℝ] ℝ} {p x : Fin L → ℝ} {lam : ℝ}
    (hlam : 0 ≤ lam) (hkt : ∀ l, 0 < x l → gradientVec u' l = lam * p l) {l : Fin L}
    (hl : 0 < x l) (hg : gradientVec u' l ≠ 0) : 0 < lam := by
  rcases hlam.lt_or_eq with h | h
  · exact h
  · exfalso
    apply hg
    rw [hkt l hl, ← h, zero_mul]

/-- **Exercise 3.E.1** (MWG, p. 61): without a constraint qualification (3.E.2)-(3.E.3) can
fail (correction B2). For `L = 1`, `u(x) = (x - 1)³` (continuous, strictly increasing, hence
locally nonsatiated), `p = 1`, `ū = 0 > u(0) = -1`: `h(p, ū) = {1}` and `u'(1) = 0`, so
`x*·[p - λ u'(x*)] = 1 ≠ 0` for every `λ`. -/
theorem exercise_3_E_1_counterexample :
    let u : (Fin 1 → ℝ) → ℝ := fun x => (x 0 - 1) ^ 3
    u 0 < 0 ∧ (1 : Fin 1 → ℝ) ∈ hicksianDemand u 1 0 ∧
      HasFDerivAt u (0 : (Fin 1 → ℝ) →L[ℝ] ℝ) 1 ∧
      ∀ lam : ℝ, (1 : Fin 1 → ℝ) ⬝ᵥ (1 - lam • gradientVec (0 : (Fin 1 → ℝ) →L[ℝ] ℝ)) ≠ 0 := by
  intro u
  refine ⟨by norm_num [u], ⟨⟨fun _ => zero_le_one, by norm_num [u]⟩, fun y hy => ?_⟩, ?_, ?_⟩
  · have h1 : 0 ≤ (y 0 - 1) ^ 3 := hy.2
    have h2 : 1 ≤ y 0 := by
      by_contra h
      push Not at h
      have : (y 0 - 1) ^ 3 < 0 := Odd.pow_neg (by decide) (by linarith)
      linarith
    simpa [dotProduct] using h2
  · have hd : HasFDerivAt (fun x : Fin 1 → ℝ => x 0)
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0) 1 :=
      hasFDerivAt_apply 0 1
    have := ((hd.sub_const 1).pow 3)
    simp only [Pi.one_apply, sub_self] at this
    convert this using 1
    ext v
    simp
  · intro lam
    simp [dotProduct, gradientVec]

end MWG.ClassicalDemand
