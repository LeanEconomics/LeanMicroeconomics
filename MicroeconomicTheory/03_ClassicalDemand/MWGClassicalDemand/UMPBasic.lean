/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.UtilityRepresentation
import MWGConsumerChoice.AppendixMA
import ConsumerDemand.IndirectUtility
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.Instances.NNReal.Lemmas

/-!
# The utility maximization problem

MWG, Section 3.D, pp. 50-57.

* Compactness of `B_{p,w}` for `p ≫ 0`, and Proposition 3.D.1: a continuous utility attains its
  maximum on the budget set (for every `w ≥ 0`).
* Proposition 3.D.2: (i) homogeneity of degree zero (no assumption on `u`), (ii) Walras' law
  from local nonsatiation (no sign condition on `p` is needed), (iii) convexity of `x(p, w)`
  for quasiconcave `u` (convex `≿`) and single-valuedness for strictly quasiconcave `u`
  (strictly convex `≿`). Bridges to Chapter 2's `HomogeneousZeroCorr` and `WalrasLawCorr`.
* The Kuhn-Tucker conditions (3.D.1)-(3.D.4) at every solution with `p ≫ 0` and `u`
  differentiable at the solution, proved directly from feasible directions (no constraint
  qualification is needed, as footnote 8 says); (3.D.5); footnote 10; the multiplier is the
  marginal utility of wealth (p. 54); sufficiency of the conditions under (M.K.9) or
  concavity (p. 55, small type).
* Proposition 3.D.3: the indirect utility function is (i) homogeneous of degree zero,
  (ii) strictly increasing in `w` and nonincreasing in `p`, (iii) quasiconvex in `(p, w)`,
  (iv) continuous on `(p, w) ≫ 0` (Berge's theorem, through Kreps's Proposition 3.3). The
  dependence `ṽ = f ∘ v` on the utility representation (p. 57).
-/

namespace MWG.ClassicalDemand

open MWG.ConsumerChoice Kreps.PreferenceProperties Filter Topology

variable {L : ℕ}

/-- Each coordinate of a budget bundle satisfies `x_l ≤ w / p_l` (MWG, p. 51). -/
theorem budgetSet_coord_le {p : Fin L → ℝ} (hp : StrictlyPositive p) {w : ℝ}
    {x : Fin L → ℝ} (hx : x ∈ budgetSet p w) (l : Fin L) : x l ≤ w / p l := by
  have h : p l * x l ≤ p ⬝ᵥ x :=
    Finset.single_le_sum (f := fun k => p k * x k)
      (fun k _ => mul_nonneg (hp k).le (hx.1 k)) (Finset.mem_univ l)
  rw [le_div_iff₀ (hp l)]
  linarith [hx.2]

/-- The Walrasian budget set is closed. -/
theorem isClosed_budgetSet (p : Fin L → ℝ) (w : ℝ) : IsClosed (budgetSet p w) := by
  have h1 : IsClosed (nonnegOrthant L) := by
    have : nonnegOrthant L = ⋂ l, {x : Fin L → ℝ | 0 ≤ x l} := by
      ext x
      simp [nonnegOrthant]
    rw [this]
    exact isClosed_iInter fun l => isClosed_le continuous_const (continuous_apply l)
  have h2 : IsClosed {x : Fin L → ℝ | p ⬝ᵥ x ≤ w} := by
    apply isClosed_le _ continuous_const
    exact continuous_finsetSum _ fun l _ => continuous_const.mul (continuous_apply l)
  exact h1.inter h2

/-- **Proposition 3.D.1, proof** (MWG, p. 51). For `p ≫ 0` the budget set is compact. -/
theorem isCompact_budgetSet {p : Fin L → ℝ} (hp : StrictlyPositive p) (w : ℝ) :
    IsCompact (budgetSet p w) :=
  (isCompact_Icc (a := (0 : Fin L → ℝ)) (b := fun l => w / p l)).of_isClosed_subset
    (isClosed_budgetSet p w) fun _ hx => ⟨fun l => hx.1 l, fun l => budgetSet_coord_le hp hx l⟩

/-- The zero bundle is affordable at nonnegative wealth. -/
theorem zero_mem_budgetSet (p : Fin L → ℝ) {w : ℝ} (hw : 0 ≤ w) : (0 : Fin L → ℝ) ∈ budgetSet p w :=
  ⟨fun _ => le_rfl, by simpa using hw⟩

/-- **Proposition 3.D.1** (MWG, p. 50). If `p ≫ 0` and `u` is continuous (on `ℝ^L_+`), the
utility maximization problem has a solution, for every wealth `w ≥ 0`. -/
theorem proposition_3_D_1 {u : (Fin L → ℝ) → ℝ} (hu : ContinuousOn u (nonnegOrthant L))
    {p : Fin L → ℝ} (hp : StrictlyPositive p) {w : ℝ} (hw : 0 ≤ w) :
    (walrasianDemand u p w).Nonempty := by
  obtain ⟨x, hx, hmax⟩ := (isCompact_budgetSet hp w).exists_isMaxOn
    ⟨0, zero_mem_budgetSet p hw⟩ (hu.mono fun _ hx => hx.1)
  exact ⟨x, hx, fun y hy => hmax hy⟩

/-- A continuous utility is bounded above on a budget set with `p ≫ 0`. -/
theorem bddAbove_image_budgetSet {u : (Fin L → ℝ) → ℝ} (hu : ContinuousOn u (nonnegOrthant L))
    {p : Fin L → ℝ} (hp : StrictlyPositive p) (w : ℝ) : BddAbove (u '' budgetSet p w) :=
  (isCompact_budgetSet hp w).bddAbove_image (hu.mono fun _ hx => hx.1)

/-- Every affordable bundle gives at most the indirect utility. -/
theorem le_indirectUtility {u : (Fin L → ℝ) → ℝ} (hu : ContinuousOn u (nonnegOrthant L))
    {p : Fin L → ℝ} (hp : StrictlyPositive p) {w : ℝ} {x : Fin L → ℝ}
    (hx : x ∈ budgetSet p w) : u x ≤ indirectUtility u p w :=
  le_csSup (bddAbove_image_budgetSet hu hp w) ⟨x, hx, rfl⟩

/-- **Proposition 3.D.2(i)** (MWG, p. 52). Walrasian demand is homogeneous of degree zero:
`x(αp, αw) = x(p, w)` for `α > 0`; no assumption on `u` is needed. -/
theorem proposition_3_D_2_i (u : (Fin L → ℝ) → ℝ) (p : Fin L → ℝ) (w : ℝ) {α : ℝ}
    (ha : 0 < α) : walrasianDemand u (α • p) (α * w) = walrasianDemand u p w := by
  simp only [walrasianDemand, walrasianDemandOn, budgetSetOn_nonnegOrthant, budgetSet_smul p w ha]

/-- **Proposition 3.D.2(i)** in Chapter 2's terms (Definition 2.E.1). -/
theorem homogeneousZeroCorr_walrasianDemand (u : (Fin L → ℝ) → ℝ) :
    HomogeneousZeroCorr (walrasianDemand u) :=
  fun p w _ _ ha => proposition_3_D_2_i u p w ha

/-- The spending change from `x` to `y` is at most `∑ |p_l|` times their Euclidean distance. -/
theorem dotProduct_sub_le_euclidDist (p x y : Fin L → ℝ) :
    p ⬝ᵥ y - p ⬝ᵥ x ≤ (∑ l, |p l|) * euclidDist y x := by
  rw [← dotProduct_sub, dotProduct, Finset.sum_mul]
  refine Finset.sum_le_sum fun l _ => ?_
  calc p l * (y - x) l ≤ |p l * (y - x) l| := le_abs_self _
    _ = |p l| * |y l - x l| := by rw [abs_mul, Pi.sub_apply]
    _ ≤ |p l| * euclidDist y x := mul_le_mul_of_nonneg_left (abs_sub_le_euclidDist y x l)
        (abs_nonneg _)

/-- Below the budget line, local nonsatiation yields a strictly better bundle with spending
below any higher level `w' > p·x`. -/
theorem exists_better_affordable {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hlns : LocallyNonsatiated (nonnegOrthant L) r) (p : Fin L → ℝ) {x : Fin L → ℝ}
    (hx : x ∈ nonnegOrthant L) {w' : ℝ} (hlt : p ⬝ᵥ x < w') :
    ∃ y ∈ nonnegOrthant L, p ⬝ᵥ y < w' ∧ Strict r y x := by
  set c := ∑ l, |p l| with hc
  have hc0 : 0 ≤ c := Finset.sum_nonneg fun l _ => abs_nonneg _
  set ε := (w' - p ⬝ᵥ x) / (c + 1) with hε
  have hε0 : 0 < ε := div_pos (by linarith) (by linarith)
  obtain ⟨y, hy, hd, hs⟩ := hlns x hx ε hε0
  refine ⟨y, hy, ?_, hs⟩
  have h1 := dotProduct_sub_le_euclidDist p x y
  have h2 : c * euclidDist y x ≤ c * ε := mul_le_mul_of_nonneg_left hd hc0
  have h3 : c * ε < w' - p ⬝ᵥ x := by
    rw [hε, mul_div_assoc']
    rw [div_lt_iff₀ (by linarith)]
    nlinarith
  linarith

/-- **Proposition 3.D.2(ii)** (MWG, p. 52). If `u` represents a locally nonsatiated `≿` on
`ℝ^L_+`, every demanded bundle exhausts wealth: `p·x = w` (Walras' law). -/
theorem proposition_3_D_2_ii {u : (Fin L → ℝ) → ℝ} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hu : RepresentsOn (nonnegOrthant L) u r) (hlns : LocallyNonsatiated (nonnegOrthant L) r)
    {p : Fin L → ℝ} {w : ℝ} {x : Fin L → ℝ} (hx : x ∈ walrasianDemand u p w) : p ⬝ᵥ x = w := by
  by_contra hne
  have hlt : p ⬝ᵥ x < w := lt_of_le_of_ne hx.1.2 hne
  obtain ⟨y, hy, hpy, hs⟩ := exists_better_affordable hlns p hx.1.1 hlt
  have := hx.2 y ⟨hy, hpy.le⟩
  exact absurd this (not_le.mpr ((hu.strict_iff hy hx.1.1).mp hs))

/-- **Proposition 3.D.2(ii)** in Chapter 2's terms (Definition 2.E.2). -/
theorem walrasLawCorr_walrasianDemand {u : (Fin L → ℝ) → ℝ}
    {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop} (hu : RepresentsOn (nonnegOrthant L) u r)
    (hlns : LocallyNonsatiated (nonnegOrthant L) r) : WalrasLawCorr (walrasianDemand u) :=
  fun _ _ _ _ hx => proposition_3_D_2_ii hu hlns hx

/-- **Proposition 3.D.2(iii)** (MWG, p. 52). If `u` is quasiconcave on `ℝ^L_+`, then `x(p, w)`
is a convex set. -/
theorem proposition_3_D_2_iii_convex {u : (Fin L → ℝ) → ℝ}
    (hq : QuasiconcaveOn ℝ (nonnegOrthant L) u) (p : Fin L → ℝ) (w : ℝ) :
    Convex ℝ (walrasianDemand u p w) := by
  intro x hx x' hx' a b ha hb hab
  have hmem : a • x + b • x' ∈ budgetSet p w := convex_budgetSet p w hx.1 hx'.1 ha hb hab
  have heq : u x = u x' := le_antisymm (hx'.2 x hx.1) (hx.2 x' hx'.1)
  have hmin := ((quasiconcaveOn_iff_min_le.mp hq).2 hx.1.1 hx'.1.1 ha hb hab)
  rw [heq, min_self] at hmin
  refine ⟨hmem, fun y hy => ?_⟩
  exact (hx'.2 y hy).trans hmin

/-- **Proposition 3.D.2(iii)** (MWG, p. 52), uniqueness. If `u` is strictly quasiconcave on
`ℝ^L_+`, then `x(p, w)` has at most one element. -/
theorem proposition_3_D_2_iii_unique {u : (Fin L → ℝ) → ℝ}
    (hq : StrictlyQuasiconcaveOn (nonnegOrthant L) u) (p : Fin L → ℝ) (w : ℝ) :
    (walrasianDemand u p w).Subsingleton := by
  intro x hx x' hx'
  by_contra hne
  have heq : u x = u x' := le_antisymm (hx'.2 x hx.1) (hx.2 x' hx'.1)
  have hmem : (1 / 2 : ℝ) • x + (1 - 1 / 2 : ℝ) • x' ∈ budgetSet p w :=
    convex_budgetSet p w hx.1 hx'.1 (by norm_num) (by norm_num) (by norm_num)
  have hlt := hq.2 x hx.1.1 x' hx'.1.1 hne (1 / 2) (by norm_num) (by norm_num) (u x) le_rfl
    heq.le
  exact absurd (hx.2 _ hmem) (not_le.mpr hlt)

/-- **Proposition 3.D.2(iii)** (MWG, p. 52) for preferences: if `≿` is convex, `x(p, w)` is
convex; if it is strictly convex, `x(p, w)` has at most one element. -/
theorem proposition_3_D_2_iii {u : (Fin L → ℝ) → ℝ} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hu : RepresentsOn (nonnegOrthant L) u r) (p : Fin L → ℝ) (w : ℝ) :
    (PrefConvex (nonnegOrthant L) r → Convex ℝ (walrasianDemand u p w)) ∧
      (PrefStrictlyConvex (nonnegOrthant L) r → (walrasianDemand u p w).Subsingleton) :=
  ⟨fun h => proposition_3_D_2_iii_convex
      ((prefConvex_iff_quasiconcaveOn (convex_nonnegOrthant L) hu).mp h) p w,
    fun h => proposition_3_D_2_iii_unique
      ((prefStrictlyConvex_iff_strictlyQuasiconcaveOn (convex_nonnegOrthant L) hu).mp h) p w⟩

/-- At a maximizer of `u` over `S`, the derivative of `u` is nonpositive in every direction `z`
along which the points `x + tz`, `0 < t < δ`, remain in `S`. -/
theorem deriv_nonpos_of_feasible {u : (Fin L → ℝ) → ℝ} {u' : (Fin L → ℝ) →L[ℝ] ℝ}
    {x : Fin L → ℝ} (hu : HasFDerivAt u u' x) {S : Set (Fin L → ℝ)}
    (hmax : ∀ y ∈ S, u y ≤ u x) {z : Fin L → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hfeas : ∀ t : ℝ, 0 < t → t < δ → x + t • z ∈ S) : u' z ≤ 0 := by
  have hd := mc_line_hasDerivAt hu z
  apply le_of_tendsto hd.tendsto_slope_zero_right
  filter_upwards [Ioo_mem_nhdsGT hδ] with t ht
  rw [zero_add, smul_eq_mul, zero_smul, add_zero]
  exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr ht.1.le)
    (sub_nonpos.mpr (hmax _ (hfeas t ht.1 ht.2)))

/-- The partial derivative `∂u/∂x_l` as the value of the derivative at `e_l`. -/
theorem gradientVec_apply (u' : (Fin L → ℝ) →L[ℝ] ℝ) (l : Fin L) :
    gradientVec u' l = u' (Pi.single l 1) := rfl

/-- **Conditions (3.D.1)** (MWG, p. 53). At any solution `x* ∈ x(p, w)` with `p ≫ 0` and `u`
differentiable at `x*`, there is a multiplier `λ ≥ 0` with `∂u(x*)/∂x_l ≤ λp_l` for all `l`,
with equality whenever `x*_l > 0`. -/
theorem ump_kuhn_tucker {u : (Fin L → ℝ) → ℝ} {u' : (Fin L → ℝ) →L[ℝ] ℝ}
    {p : Fin L → ℝ} (hp : StrictlyPositive p) {w : ℝ} {x : Fin L → ℝ}
    (hx : x ∈ walrasianDemand u p w) (hu : HasFDerivAt u u' x) :
    ∃ lam : ℝ, 0 ≤ lam ∧ ∀ l, gradientVec u' l ≤ lam * p l ∧
      (0 < x l → gradientVec u' l = lam * p l) := by
  classical
  set g := gradientVec u' with hg
  have hmax : ∀ y ∈ budgetSet p w, u y ≤ u x := hx.2
  -- (A): substitution between goods `k` and `l` when `x_l > 0`
  have hA : ∀ k l, 0 < x l → g k / p k ≤ g l / p l := by
    intro k l hl
    set z : Fin L → ℝ := (1 / p k) • Pi.single k 1 - (1 / p l) • Pi.single l 1 with hz
    have hpz : p ⬝ᵥ z = 0 := by
      simp [hz, dotProduct_sub, dotProduct_smul, (hp k).ne', (hp l).ne']
    have hfeas : ∀ t : ℝ, 0 < t → t < x l * p l → x + t • z ∈ budgetSet p w := by
      intro t ht0 ht1
      refine ⟨fun m => ?_, ?_⟩
      · by_cases hml : m = l
        · subst hml
          have hxl : t / p m < x m := by rw [div_lt_iff₀ (hp m)]; linarith
          by_cases hkm : k = m
          · subst hkm
            simp [hz]
            linarith
          · have : t * (p m)⁻¹ ≤ x m := by rw [← div_eq_mul_inv]; linarith
            simpa [hz, Ne.symm hkm] using this
        · have hzm : 0 ≤ z m := by
            simp only [hz, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, hml,
              ↓reduceIte, mul_zero, sub_zero]
            split_ifs
            · exact mul_nonneg (one_div_pos.mpr (hp k)).le zero_le_one
            · simp
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          exact add_nonneg (hx.1.1 m) (mul_nonneg ht0.le hzm)
      · rw [dotProduct_add, dotProduct_smul, hpz, smul_zero, add_zero]
        exact hx.1.2
    have hle := deriv_nonpos_of_feasible hu hmax (mul_pos hl (hp l)) hfeas
    rw [hz, map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul, one_div, one_div,
      mul_comm (p k)⁻¹, mul_comm (p l)⁻¹] at hle
    rw [div_eq_mul_inv, div_eq_mul_inv]
    have e1 : g k = u' (Pi.single k 1) := rfl
    have e2 : g l = u' (Pi.single l 1) := rfl
    rw [e1, e2]
    linarith
  -- (B): reducing a good consumed in positive amount
  have hB : ∀ l, 0 < x l → 0 ≤ g l := by
    intro l hl
    have hfeas : ∀ t : ℝ, 0 < t → t < x l → x + t • (-(Pi.single l 1 : Fin L → ℝ)) ∈
        budgetSet p w := by
      intro t ht0 ht1
      refine ⟨fun m => ?_, ?_⟩
      · by_cases hml : m = l
        · subst hml
          simp
          linarith
        · simp [hml, hx.1.1 m]
      · rw [dotProduct_add, dotProduct_smul, dotProduct_neg]
        have : p ⬝ᵥ (Pi.single l 1 : Fin L → ℝ) = p l := by simp
        rw [this, smul_eq_mul]
        nlinarith [hx.1.2, hp l]
    have hle := deriv_nonpos_of_feasible hu hmax hl hfeas
    rw [map_neg] at hle
    have : g l = u' (Pi.single l 1) := rfl
    linarith
  by_cases hpos : ∃ l, 0 < x l
  · obtain ⟨l, hl⟩ := hpos
    refine ⟨g l / p l, div_nonneg (hB l hl) (hp l).le, fun k => ⟨?_, fun hk => ?_⟩⟩
    · have := hA k l hl
      rwa [div_le_iff₀ (hp k)] at this
    · have h1 := hA k l hl
      have h2 := hA l k hk
      have : g k / p k = g l / p l := le_antisymm h1 h2
      rw [← this, div_mul_cancel₀ _ (hp k).ne']
  · push Not at hpos
    refine ⟨∑ k, |g k| / p k, Finset.sum_nonneg fun k _ => div_nonneg (abs_nonneg _) (hp k).le,
      fun k => ⟨?_, fun hk => absurd hk (not_lt.mpr (hpos k))⟩⟩
    have h1 : |g k| / p k ≤ ∑ k, |g k| / p k :=
      Finset.single_le_sum (f := fun k => |g k| / p k)
        (fun k _ => div_nonneg (abs_nonneg _) (hp k).le) (Finset.mem_univ k)
    have h2 : g k ≤ |g k| / p k * p k := by
      rw [div_mul_cancel₀ _ (hp k).ne']
      exact le_abs_self _
    exact h2.trans (mul_le_mul_of_nonneg_right h1 (hp k).le)

/-- **Conditions (3.D.2)-(3.D.3)** (MWG, p. 53), matrix form: `∇u(x*) ≤ λp` and
`x*·[∇u(x*) - λp] = 0`. -/
theorem equations_3_D_2_3 {u : (Fin L → ℝ) → ℝ} {u' : (Fin L → ℝ) →L[ℝ] ℝ}
    {p : Fin L → ℝ} (hp : StrictlyPositive p) {w : ℝ} {x : Fin L → ℝ}
    (hx : x ∈ walrasianDemand u p w) (hu : HasFDerivAt u u' x) :
    ∃ lam : ℝ, 0 ≤ lam ∧ gradientVec u' ≤ lam • p ∧ x ⬝ᵥ (gradientVec u' - lam • p) = 0 := by
  obtain ⟨lam, hlam, h⟩ := ump_kuhn_tucker hp hx hu
  refine ⟨lam, hlam, fun l => by simpa using (h l).1, ?_⟩
  refine Finset.sum_eq_zero fun l _ => ?_
  rcases (hx.1.1 l).lt_or_eq with hl | hl
  · simp [(h l).2 hl]
  · simp [← hl]

/-- **Condition (3.D.4)** (MWG, p. 53). At an interior optimum `x* ≫ 0`, `∇u(x*) = λp`. -/
theorem equation_3_D_4 {u : (Fin L → ℝ) → ℝ} {u' : (Fin L → ℝ) →L[ℝ] ℝ}
    {p : Fin L → ℝ} (hp : StrictlyPositive p) {w : ℝ} {x : Fin L → ℝ}
    (hx : x ∈ walrasianDemand u p w) (hu : HasFDerivAt u u' x) (hint : ∀ l, 0 < x l) :
    ∃ lam : ℝ, 0 ≤ lam ∧ gradientVec u' = lam • p := by
  obtain ⟨lam, hlam, h⟩ := ump_kuhn_tucker hp hx hu
  exact ⟨lam, hlam, funext fun l => by simpa using (h l).2 (hint l)⟩

/-- **Condition (3.D.5)** (MWG, p. 54). At an interior optimum with `∇u(x*) ≫ 0`, the marginal
rate of substitution equals the price ratio: `(∂u/∂x_l)/(∂u/∂x_k) = p_l/p_k`. -/
theorem equation_3_D_5 {u : (Fin L → ℝ) → ℝ} {u' : (Fin L → ℝ) →L[ℝ] ℝ}
    {p : Fin L → ℝ} (hp : StrictlyPositive p) {w : ℝ} {x : Fin L → ℝ}
    (hx : x ∈ walrasianDemand u p w) (hu : HasFDerivAt u u' x) (hint : ∀ l, 0 < x l)
    (hgrad : ∀ l, 0 < gradientVec u' l) (l k : Fin L) :
    gradientVec u' l / gradientVec u' k = p l / p k := by
  obtain ⟨lam, -, h⟩ := equation_3_D_4 hp hx hu hint
  have hk := hgrad k
  rw [h] at hk ⊢
  simp only [Pi.smul_apply, smul_eq_mul] at hk ⊢
  have hlam : lam ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hk
    exact lt_irrefl _ hk
  rw [mul_div_mul_left _ _ hlam]

/-- **Footnote 10** (MWG, p. 55). If `∇u(x*) ≥ 0` and `∇u(x*) ≠ 0` at an interior optimum, the
multiplier in (3.D.4) is strictly positive. -/
theorem footnote_3_D_10 {u' : (Fin L → ℝ) →L[ℝ] ℝ} {p : Fin L → ℝ} {lam : ℝ} (hlam : 0 ≤ lam)
    (hfoc : gradientVec u' = lam • p) (hne : gradientVec u' ≠ 0) : 0 < lam := by
  rcases hlam.lt_or_eq with h | h
  · exact h
  · exfalso
    apply hne
    rw [hfoc, ← h, zero_smul]

/-- **Section 3.D** (MWG, p. 54). The multiplier is the marginal utility of wealth: if the
demand path `w ↦ x(p, w)` is differentiable at `w`, satisfies Walras' law near `w`, and
`∇u(x(p, w)) = λp`, then `d u(x(p, w))/dw = λ`. -/
theorem lagrange_multiplier_marginal_utility {u : (Fin L → ℝ) → ℝ}
    {u' : (Fin L → ℝ) →L[ℝ] ℝ} {p : Fin L → ℝ} {xw : ℝ → Fin L → ℝ} {x' : Fin L → ℝ}
    {w lam : ℝ} (hx : HasDerivAt xw x' w) (hu : HasFDerivAt u u' (xw w))
    (hfoc : gradientVec u' = lam • p) (hwal : ∀ᶠ w' in 𝓝 w, p ⬝ᵥ xw w' = w') :
    HasDerivAt (fun w' => u (xw w')) lam w := by
  have hchain : HasDerivAt (fun w' => u (xw w')) (u' x') w := hu.comp_hasDerivAt w hx
  have hdot : HasDerivAt (fun w' => p ⬝ᵥ xw w') (p ⬝ᵥ x') w := by
    have : HasDerivAt (fun w' => ∑ l, p l * xw w' l) (∑ l, p l * x' l) w :=
      HasDerivAt.fun_sum fun l _ => (hasDerivAt_pi.mp hx l).const_mul (p l)
    exact this
  have hid : HasDerivAt (fun w' => p ⬝ᵥ xw w') 1 w :=
    (hasDerivAt_id w).congr_of_eventuallyEq (hwal.mono fun w' h => h)
  have h1 : p ⬝ᵥ x' = 1 := hdot.unique hid
  have h2 : u' x' = lam := by
    rw [fderiv_apply_eq_gradient_dot, hfoc, smul_dotProduct, h1, smul_eq_mul, mul_one]
  rwa [h2] at hchain

/-- **Section 3.D, small type** (MWG, p. 55). Sufficiency of the Kuhn-Tucker conditions: if
`x*` exhausts the budget, satisfies (3.D.1) with some `λ ≥ 0`, and `u` satisfies condition
(M.K.9) at `x*` on `ℝ^L_+`, then `x*` solves the UMP. -/
theorem ump_kuhn_tucker_sufficient {u : (Fin L → ℝ) → ℝ} {u' : (Fin L → ℝ) →L[ℝ] ℝ}
    {p : Fin L → ℝ} {w : ℝ} {x : Fin L → ℝ} (hx : x ∈ budgetSet p w) (hbind : p ⬝ᵥ x = w)
    {lam : ℝ} (hlam : 0 ≤ lam)
    (hfoc : ∀ l, gradientVec u' l ≤ lam * p l ∧ (0 < x l → gradientVec u' l = lam * p l))
    (hMK9 : ∀ y ∈ nonnegOrthant L, u x < u y → 0 < u' (y - x)) :
    x ∈ walrasianDemand u p w := by
  refine ⟨hx, fun y hy => ?_⟩
  by_contra hlt
  push Not at hlt
  have hpos := hMK9 y hy.1 hlt
  rw [fderiv_apply_eq_gradient_dot, dotProduct_sub] at hpos
  have h1 : gradientVec u' ⬝ᵥ y ≤ lam * (p ⬝ᵥ y) := by
    rw [dotProduct, dotProduct, Finset.mul_sum]
    refine Finset.sum_le_sum fun l _ => ?_
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hfoc l).1 (hy.1 l)
  have h2 : gradientVec u' ⬝ᵥ x = lam * (p ⬝ᵥ x) := by
    rw [dotProduct, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rcases (hx.1 l).lt_or_eq with hl | hl
    · rw [(hfoc l).2 hl, mul_assoc]
    · rw [← hl]
      simp
  have h3 : lam * (p ⬝ᵥ y) ≤ lam * w := mul_le_mul_of_nonneg_left hy.2 hlam
  rw [hbind] at h2
  linarith

/-- **Section 3.D, small type** (MWG, p. 55). For a utility concave on `ℝ^L_+` and
differentiable there, the Kuhn-Tucker conditions with an exhausted budget are sufficient. -/
theorem ump_kuhn_tucker_sufficient_concave {u : (Fin L → ℝ) → ℝ}
    {u' : (Fin L → ℝ) → (Fin L → ℝ) →L[ℝ] ℝ} (hconc : ConcaveOn ℝ (nonnegOrthant L) u)
    (hdiff : ∀ y ∈ nonnegOrthant L, HasFDerivAt u (u' y) y)
    {p : Fin L → ℝ} {w : ℝ} {x : Fin L → ℝ} (hx : x ∈ budgetSet p w) (hbind : p ⬝ᵥ x = w)
    {lam : ℝ} (hlam : 0 ≤ lam)
    (hfoc : ∀ l, gradientVec (u' x) l ≤ lam * p l ∧
      (0 < x l → gradientVec (u' x) l = lam * p l)) :
    x ∈ walrasianDemand u p w := by
  refine ump_kuhn_tucker_sufficient hx hbind hlam hfoc fun y hy hlt => ?_
  have := theorem_M_C_1_necessity (z := y - x) hdiff hconc hx.1 (by rw [add_sub_cancel]; exact hy)
  simp only [add_sub_cancel] at this
  linarith

/-- **Proposition 3.D.3(i)** (MWG, p. 56). The indirect utility function is homogeneous of
degree zero. -/
theorem proposition_3_D_3_i (u : (Fin L → ℝ) → ℝ) (p : Fin L → ℝ) (w : ℝ) {α : ℝ}
    (ha : 0 < α) : indirectUtility u (α • p) (α * w) = indirectUtility u p w := by
  simp only [indirectUtility, indirectUtilityOn, budgetSetOn_nonnegOrthant,
    budgetSet_smul p w ha]

/-- **Proposition 3.D.3(ii)** (MWG, p. 56), first half. For a continuous utility representing
a locally nonsatiated `≿` on `ℝ^L_+` and `p ≫ 0`, `v(p, w)` is strictly increasing in `w ≥ 0`. -/
theorem proposition_3_D_3_ii_wealth {u : (Fin L → ℝ) → ℝ}
    {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop} (hu : RepresentsOn (nonnegOrthant L) u r)
    (hcont : ContinuousOn u (nonnegOrthant L)) (hlns : LocallyNonsatiated (nonnegOrthant L) r)
    {p : Fin L → ℝ} (hp : StrictlyPositive p) {w w' : ℝ} (hw : 0 ≤ w) (hww : w < w') :
    indirectUtility u p w < indirectUtility u p w' := by
  obtain ⟨x, hx⟩ := proposition_3_D_1 hcont hp hw
  rw [indirectUtility_eq_of_mem hx]
  obtain ⟨y, hy, hpy, hs⟩ := exists_better_affordable hlns p hx.1.1 (hx.1.2.trans_lt hww)
  exact ((hu.strict_iff hy hx.1.1).mp hs).trans_le (le_indirectUtility hcont hp ⟨hy, hpy.le⟩)

/-- **Proposition 3.D.3(ii)** (MWG, p. 56), second half. `v(p, w)` is nonincreasing in prices:
`p ≤ p'` (both `≫ 0`) implies `v(p', w) ≤ v(p, w)`, in particular in each `p_l`. -/
theorem proposition_3_D_3_ii_prices {u : (Fin L → ℝ) → ℝ}
    (hcont : ContinuousOn u (nonnegOrthant L)) {p p' : Fin L → ℝ} (hp : StrictlyPositive p)
    (hp' : StrictlyPositive p') (hpp : p ≤ p') {w : ℝ} (hw : 0 ≤ w) :
    indirectUtility u p' w ≤ indirectUtility u p w := by
  obtain ⟨x, hx⟩ := proposition_3_D_1 hcont hp' hw
  rw [indirectUtility_eq_of_mem hx]
  apply le_indirectUtility hcont hp
  refine ⟨hx.1.1, le_trans ?_ hx.1.2⟩
  exact dotProduct_le_dotProduct_of_nonneg_right hpp fun l => hx.1.1 l

/-- The price-wealth domain `{(p, w) : p ≫ 0, w > 0}`. -/
def pwDomainSet (L : ℕ) : Set ((Fin L → ℝ) × ℝ) := {q | PWDomain q.1 q.2}

/-- The price-wealth domain is convex. -/
theorem convex_pwDomainSet (L : ℕ) : Convex ℝ (pwDomainSet L) := by
  intro q hq q' hq' a b ha hb hab
  refine ⟨fun l => ?_, ?_⟩
  · simp only [Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases ha.lt_or_eq with ha' | ha'
    · exact add_pos_of_pos_of_nonneg (mul_pos ha' (hq.1 l)) (mul_nonneg hb (hq'.1 l).le)
    · subst ha'
      simp only [zero_add] at hab
      subst hab
      simpa using hq'.1 l
  · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    rcases ha.lt_or_eq with ha' | ha'
    · exact add_pos_of_pos_of_nonneg (mul_pos ha' hq.2) (mul_nonneg hb hq'.2.le)
    · subst ha'
      simp only [zero_add] at hab
      subst hab
      simpa using hq'.2

/-- **Proposition 3.D.3(iii)** (MWG, pp. 56-57). For a continuous `u`, the indirect utility
function is quasiconvex in `(p, w)` on `(p, w) ≫ 0`: `{(p, w) : v(p, w) ≤ v̄}` is convex.
(Footnote 11: no quasiconcavity of `u` is needed.) -/
theorem proposition_3_D_3_iii {u : (Fin L → ℝ) → ℝ} (hcont : ContinuousOn u (nonnegOrthant L)) :
    QuasiconvexOn ℝ (pwDomainSet L) (fun q => indirectUtility u q.1 q.2) := by
  intro t q hq q' hq' a b ha hb hab
  refine ⟨convex_pwDomainSet L hq.1 hq'.1 ha hb hab, ?_⟩
  simp only
  refine csSup_le ⟨u 0, 0, zero_mem_budgetSet _ (by
    simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha hq.1.2.le) (mul_nonneg hb hq'.1.2.le)), rfl⟩ ?_
  rintro _ ⟨x, hx, rfl⟩
  have hspend : a * (q.1 ⬝ᵥ x) + b * (q'.1 ⬝ᵥ x) ≤ a * q.2 + b * q'.2 := by
    have := hx.2
    simp only [Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, add_dotProduct,
      smul_dotProduct, smul_eq_mul] at this
    exact this
  by_cases h1 : q.1 ⬝ᵥ x ≤ q.2
  · exact (le_indirectUtility hcont hq.1.1 ⟨hx.1, h1⟩).trans hq.2
  · have h2 : q'.1 ⬝ᵥ x ≤ q'.2 := by
      by_contra h2
      push Not at h1 h2
      rcases ha.lt_or_eq with ha' | ha'
      · nlinarith
      · subst ha'
        simp only [zero_add] at hab
        subst hab
        linarith
    exact (le_indirectUtility hcont hq'.1.1 ⟨hx.1, h2⟩).trans hq'.2

/-- Our indirect utility is Kreps's `IndirectUtility` of the restricted utility. -/
theorem indirectUtility_eq_kreps (u : (Fin L → ℝ) → ℝ) (p : Fin L → ℝ)
    (hp : StrictlyPositive p) (w : ℝ) (hw : 0 ≤ w) :
    indirectUtility u p w =
      Kreps.ConsumerDemand.IndirectUtility (fun a : Kreps.ConsumerDemand.NonnegativeOrthant L =>
        u a.1) ⟨p, hp⟩ (⟨w, hw⟩ : NNReal) := by
  unfold indirectUtility indirectUtilityOn Kreps.ConsumerDemand.IndirectUtility
  congr 1
  ext t
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, fun l => hx.1 l⟩, hx.2, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a.1, ⟨fun l => a.2 l, ha⟩, rfl⟩

/-- **Proposition 3.D.3(iv)** (MWG, p. 56). For a continuous `u`, the indirect utility function
is continuous on `(p, w) ≫ 0`. The book omits the proof; this is Berge's theorem of the
maximum, applied through Kreps's Proposition 3.3. -/
theorem proposition_3_D_3_iv {u : (Fin L → ℝ) → ℝ} (hcont : ContinuousOn u (nonnegOrthant L)) :
    ContinuousOn (fun q : (Fin L → ℝ) × ℝ => indirectUtility u q.1 q.2) (pwDomainSet L) := by
  have hu' : Continuous (fun a : Kreps.ConsumerDemand.NonnegativeOrthant L => u a.1) := by
    have := (continuousOn_iff_continuous_domRestrict.mp hcont)
    exact this.comp (continuous_subtype_val.subtype_mk
      fun (a : Kreps.ConsumerDemand.NonnegativeOrthant L) => fun l => a.2 l)
  have hK := (Kreps.ConsumerDemand.consumer_maximum_theorem hu').2.2.2
  rw [continuousOn_iff_continuous_domRestrict]
  let φ : pwDomainSet L → Kreps.ConsumerDemand.PriceIncome L :=
    fun q => (⟨q.1.1, q.2.1⟩, Real.toNNReal q.1.2)
  have hφ : Continuous φ :=
    ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
      (continuous_real_toNNReal.comp (continuous_snd.comp continuous_subtype_val))
  convert hK.comp hφ using 1
  funext q
  simp only [Set.domRestrict_apply, Function.comp_apply, φ]
  rw [indirectUtility_eq_kreps u q.1.1 q.2.1 q.1.2 q.2.2.le]
  congr
  exact (max_eq_left q.2.2.le).symm

/-- **Section 3.D** (MWG, p. 57). The indirect utility depends on the representation: for a
strictly increasing `f`, the indirect utility of `f ∘ u` is `f ∘ v` (whenever the UMP has a
solution). -/
theorem indirectUtility_comp {u : (Fin L → ℝ) → ℝ} {f : ℝ → ℝ} (hf : StrictMono f)
    {p : Fin L → ℝ} {w : ℝ} (hne : (walrasianDemand u p w).Nonempty) :
    indirectUtility (f ∘ u) p w = f (indirectUtility u p w) := by
  obtain ⟨x, hx⟩ := hne
  have hx' : x ∈ walrasianDemand (f ∘ u) p w :=
    ⟨hx.1, fun y hy => hf.monotone (hx.2 y hy)⟩
  rw [indirectUtility_eq_of_mem hx', indirectUtility_eq_of_mem hx, Function.comp_apply]

end MWG.ClassicalDemand
