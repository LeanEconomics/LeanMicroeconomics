/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.IntegrabilityUnique
import MWGClassicalDemand.WelfareBasic
import MWGConsumerChoice.SlutskyExamples

/-!
# Integrability: Exercises 3.H.2-3.H.5 and 3.H.7

MWG, Exercises 3.H.2-3.H.5 and 3.H.7 (p. 102).

* Exercise 3.H.2: if `e(·, ū)` is differentiable at `p ≫ 0`, the expenditure minimizer is unique
  and equals `∇e(p, ū)`, both for the actual at-least-as-good set and for `V_ū`; so every
  minimizer over `V_ū` already lies in the actual set (`exercise_3_H_2`). That the actual set is
  then convex is OPEN (see the source map).
* Exercise 3.H.3: `v(p, w)` is the unique `ū` with `e(p, ū) = w` (`exercise_3_H_3`).
* Exercise 3.H.4: with two goods, indifference curves are the solutions of
  `φ'(x₁) = -g₁(x)/g₂(x)` for the indirect demand `g(x) = ∇u(x)/(x·∇u(x))` (`exercise_3_H_4`).
* Exercise 3.H.5: from `v`: `e(p, ū)` is the wealth with `v(p, w) = ū`, and
  `u(x) = min_{p ≫ 0} v(p, p·x)` at every bundle demanded at some prices (`exercise_3_H_5_*`).
* Exercise 3.H.7 (the demand `x_k = w/∑ p_l` of Exercise 2.F.17): `e(p, 1) = ∑ p_l` is the
  unique solution of (3.H.2) through `(1, ..., 1)`, and `V₁ = {x : x ≥ (1, ..., 1)}`.
-/

namespace MWG.ClassicalDemand

open MWG.ConsumerChoice Kreps.PreferenceProperties Filter Topology

variable {L : ℕ}

/-- **Exercise 3.H.2** (MWG, p. 102). Let `u` be continuous on `ℝ^L_+`, representing a locally
nonsatiated `≿` (any convexity), `ū` attainable. If `e(·, ū)` is differentiable at `p ≫ 0` with
gradient `∇e`, then (Proposition 3.F.1) the expenditure minimizer is unique, `h(p, ū) = {∇e}`;
the minimizer over the convex set `V_ū` is also unique and equal to `∇e`; so the minimizer over
`V_ū` lies in the actual at-least-as-good set. -/
theorem exercise_3_H_2 {u : (Fin L → ℝ) → ℝ} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hrep : RepresentsOn (nonnegOrthant L) u r) (hu : ContinuousOn u (nonnegOrthant L))
    (hlns : LocallyNonsatiated (nonnegOrthant L) r) {ub : ℝ}
    (hne : ∃ x ∈ nonnegOrthant L, ub ≤ u x) {p : Fin L → ℝ} (hp : StrictlyPositive p)
    {E' : (Fin L → ℝ) →L[ℝ] ℝ} (hd : HasFDerivAt (fun q => expenditure u q ub) E' p) :
    hicksianDemand u p ub = {gradientVec E'} ∧
      supportArgmin (recoveredSet fun q => expenditure u q ub) p = {gradientVec E'} ∧
      gradientVec E' ∈ empConstraintSet u ub := by
  set V := recoveredSet fun q => expenditure u q ub with hV
  have hbdd : ∀ {K : Set (Fin L → ℝ)}, K ⊆ nonnegOrthant L →
      ∀ᶠ q in 𝓝 p, BddBelow ((fun x => q ⬝ᵥ x) '' K) := by
    intro K hK
    filter_upwards [relations_eventually_strictlyPositive hp] with q hq
    refine ⟨0, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact Finset.sum_nonneg fun l _ => mul_nonneg (hq l).le (hK hy l)
  -- the actual set `K`
  have hK : IsClosed (empConstraintSet u ub) := isClosed_empConstraintSet hu ub
  have hKne : (empConstraintSet u ub).Nonempty := by
    obtain ⟨x, hx, hux⟩ := hne
    exact ⟨x, hx, hux⟩
  obtain ⟨x, hx, huniq, hfd⟩ := duality_unique_of_differentiable hK hKne
    ⟨hbdd fun _ hy => hy.1, hd.differentiableAt⟩
  have hgrad : gradientVec E' = x := by
    have : fderiv ℝ (supportFn (empConstraintSet u ub)) p = E' := hd.fderiv
    rw [← this, hfd, gradientVec_dualityDotCLM]
  -- the convex set `V_ū` has the same support function near `p`
  have hsupp : ∀ q, StrictlyPositive q → supportFn V q = expenditure u q ub := fun q hq =>
    (recoveredSet_generates_expenditure hrep hu hlns hne hq).2.2
  have hdV : HasFDerivAt (supportFn V) E' p := by
    apply hd.congr_of_eventuallyEq
    filter_upwards [relations_eventually_strictlyPositive hp] with q hq
    exact hsupp q hq
  have hVne : V.Nonempty := ⟨x, (subset_recoveredSet fun _ hy => hy.1) hx.1⟩
  obtain ⟨y, hy, huniqV, hfdV⟩ := duality_unique_of_differentiable (isClosed_recoveredSet _)
    hVne ⟨hbdd fun _ hz => hz.1, hdV.differentiableAt⟩
  have hgradV : gradientVec E' = y := by
    rw [← hdV.fderiv, hfdV, gradientVec_dualityDotCLM]
  refine ⟨?_, ?_, hgrad ▸ hx.1⟩
  · rw [hgrad]
    exact Set.eq_singleton_iff_unique_mem.mpr ⟨hx, huniq⟩
  · rw [hgradV]
    exact Set.eq_singleton_iff_unique_mem.mpr ⟨hy, huniqV⟩

/-- **Exercise 3.H.3** (MWG, p. 102). The indirect utility is recovered from the expenditure
function by inversion: for `p ≫ 0`, `w > 0`, `e(p, v(p, w)) = w`, and `v(p, w)` is the only
attainable level `ū > u(0)` with `e(p, ū) = w`. -/
theorem exercise_3_H_3 {u : (Fin L → ℝ) → ℝ} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hrep : RepresentsOn (nonnegOrthant L) u r) (hu : ContinuousOn u (nonnegOrthant L))
    (hlns : LocallyNonsatiated (nonnegOrthant L) r) {p : Fin L → ℝ} (hp : StrictlyPositive p)
    {w : ℝ} (hw : 0 < w) :
    expenditure u p (indirectUtility u p w) = w ∧
      ∀ ub, u 0 < ub → (∃ x ∈ nonnegOrthant L, ub ≤ u x) → expenditure u p ub = w →
        ub = indirectUtility u p w := by
  refine ⟨equation_3_E_1_left hrep hu hlns hp hw.le, fun ub hub hne he => ?_⟩
  rw [← he, equation_3_E_1_right hu hp hub hne]

/-- **Exercise 3.H.4** (MWG, p. 102), `L = 2`. Let `u` be differentiable at `x = (t, φ(t))`
with `∂u/∂x₂ ≠ 0` and `x·∇u(x) ≠ 0`, and let `g(x) = ∇u(x)/(x·∇u(x))` be the indirect demand of
Exercise 3.G.7. If `φ` is differentiable at `t`, then `t ↦ u(t, φ(t))` is stationary at `t` iff
`φ'(t) = -g₁(x)/g₂(x)`: the indifference curves are recovered by solving this ordinary
differential equation. -/
theorem exercise_3_H_4 {u : (Fin 2 → ℝ) → ℝ} {φ : ℝ → ℝ} {t φ' : ℝ}
    {u' : (Fin 2 → ℝ) →L[ℝ] ℝ} (hd : HasFDerivAt u u' ![t, φ t]) (hφ : HasDerivAt φ φ' t)
    (h2 : gradientVec u' 1 ≠ 0) (hne : ![t, φ t] ⬝ᵥ gradientVec u' ≠ 0) :
    let g := (1 / (![t, φ t] ⬝ᵥ gradientVec u')) • gradientVec u'
    HasDerivAt (fun s => u ![s, φ s]) (gradientVec u' 0 + gradientVec u' 1 * φ') t ∧
      (gradientVec u' 0 + gradientVec u' 1 * φ' = 0 ↔ φ' = -(g 0 / g 1)) := by
  intro g
  have hγ : HasDerivAt (fun s => (![s, φ s] : Fin 2 → ℝ)) ![1, φ'] t := by
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · exact hasDerivAt_id' t
    · simpa using hφ
  have hcomp := hd.comp_hasDerivAt t hγ
  have hval : u' ![1, φ'] = gradientVec u' 0 + gradientVec u' 1 * φ' := by
    rw [integ_apply_eq_dot]
    simp [dotProduct, Fin.sum_univ_two]
  refine ⟨hval ▸ hcomp, ?_⟩
  have hc : 1 / (![t, φ t] ⬝ᵥ gradientVec u') ≠ 0 := one_div_ne_zero hne
  have hg : g 0 / g 1 = gradientVec u' 0 / gradientVec u' 1 := by
    simp only [g, Pi.smul_apply, smul_eq_mul]
    rw [mul_div_mul_left _ _ hc]
  rw [hg]
  constructor
  · intro h
    field_simp
    linarith
  · intro h
    rw [h]
    field_simp
    ring

/-- **Exercise 3.H.5** (MWG, p. 102), the expenditure function from `v`: `e(p, ū)` is the wealth
at which the indirect utility is `ū` (for `p ≫ 0` and attainable `ū > u(0)`):
`v(p, e(p, ū)) = ū`, and `v(p, w) = ū` with `w ≥ 0` forces `e(p, ū) = w`. -/
theorem exercise_3_H_5_expenditure {u : (Fin L → ℝ) → ℝ} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hrep : RepresentsOn (nonnegOrthant L) u r) (hu : ContinuousOn u (nonnegOrthant L))
    (hlns : LocallyNonsatiated (nonnegOrthant L) r) {p : Fin L → ℝ} (hp : StrictlyPositive p)
    {ub : ℝ} (hub : u 0 < ub) (hne : ∃ x ∈ nonnegOrthant L, ub ≤ u x) :
    indirectUtility u p (expenditure u p ub) = ub ∧
      ∀ w, 0 ≤ w → indirectUtility u p w = ub → expenditure u p ub = w := by
  refine ⟨equation_3_E_1_right hu hp hub hne, fun w hw h => ?_⟩
  rw [← h]
  exact equation_3_E_1_left hrep hu hlns hp hw

/-- **Exercise 3.H.5** (MWG, p. 102), the direct utility from `v`: for `x ∈ ℝ^L_+`,
`u(x) ≤ v(p, p·x)` for every `p ≫ 0`, with equality at any `p` at which `x` is demanded; so
`u(x) = min_{p ≫ 0} v(p, p·x)` at every bundle demanded at some `p ≫ 0`. -/
theorem exercise_3_H_5_utility {u : (Fin L → ℝ) → ℝ} (hu : ContinuousOn u (nonnegOrthant L))
    {x : Fin L → ℝ} (hx : x ∈ nonnegOrthant L) :
    (∀ p, StrictlyPositive p → u x ≤ indirectUtility u p (p ⬝ᵥ x)) ∧
      ∀ p, x ∈ walrasianDemand u p (p ⬝ᵥ x) → indirectUtility u p (p ⬝ᵥ x) = u x :=
  ⟨fun _ hp => le_indirectUtility hu hp ⟨hx, le_rfl⟩,
    fun _ hd => indirectUtility_eq_of_mem hd⟩

/-- **Exercise 3.H.7(a)** (MWG, p. 102), for the demand `x_k(p, w) = w/∑ p_l` of Exercise
2.F.17 (`L ≥ 1`). The function `E(p) = ∑ p_l` solves (3.H.2) and passes through the bundle
`(1, ..., 1)` (demanded at `(p, ∑ p_l)`); by uniqueness (`pde_solution_unique`) it is the only
positive solution with `E(p⁰) = ∑ p⁰_l`: the expenditure function at the utility level `1` of
`(1, ..., 1)` is `e(p, 1) = ∑ p_l`. -/
theorem exercise_3_H_7a [NeZero L] :
    SolvesPDE (demand_2_F_17 L) (fun p => ∑ l, p l) ∧
      (∀ p : Fin L → ℝ, StrictlyPositive p → demand_2_F_17 L p (∑ l, p l) = fun _ => 1) ∧
      ∀ E : (Fin L → ℝ) → ℝ, SolvesPDE (demand_2_F_17 L) E →
        (∀ q, StrictlyPositive q → 0 < E q) → ∀ p₀, StrictlyPositive p₀ →
          E p₀ = ∑ l, p₀ l → ∀ p, StrictlyPositive p → E p = ∑ l, p l := by
  have hsum : ∀ p : Fin L → ℝ, StrictlyPositive p → 0 < ∑ l, p l := fun p hp =>
    Finset.sum_pos (fun l _ => hp l) Finset.univ_nonempty
  have hpde : SolvesPDE (demand_2_F_17 L) (fun p => ∑ l, p l) := by
    intro q hq
    have : (fun p : Fin L → ℝ => ∑ l, p l) = dualityDotCLM (fun _ => 1) := by
      funext p
      simp [dualityDotCLM_apply, dotProduct]
    rw [this]
    have h1 : demand_2_F_17 L q (dualityDotCLM (fun _ => (1 : ℝ)) q) = fun _ => 1 := by
      rw [dualityDotCLM_apply]
      funext k
      simp only [demand_2_F_17, dotProduct, one_mul]
      exact div_self (hsum q hq).ne'
    rw [h1]
    exact (dualityDotCLM _).hasFDerivAt
  have hcd : ContDiffOn ℝ 1 (Function.uncurry (demand_2_F_17 L)) (demandDomain L) := by
    have : Function.uncurry (demand_2_F_17 L) =
        fun z : (Fin L → ℝ) × ℝ => fun _ : Fin L => z.2 / ∑ l, z.1 l := by
      funext z
      rfl
    rw [this]
    refine contDiffOn_pi.mpr fun _ => ?_
    apply ContDiffOn.div (by fun_prop) (by fun_prop)
    intro z hz
    exact (hsum z.1 hz.1).ne'
  refine ⟨hpde, fun p hp => ?_, fun E hE hEpos p₀ hp₀ h0 p hp =>
    pde_solution_unique hcd hE hpde hEpos (fun q hq => hsum q hq) hp₀ h0 hp⟩
  funext k
  exact div_self (hsum p hp).ne'

/-- **Exercise 3.H.7(b)** (MWG, p. 102). For `e(p, 1) = ∑ p_l`, the at-least-as-good set of
`(1, ..., 1)` is `V₁ = {x : x_l ≥ 1 for all l}` (the Leontief upper contour set). -/
theorem exercise_3_H_7b :
    recoveredSet (fun p : Fin L → ℝ => ∑ l, p l) = {x | ∀ l, 1 ≤ x l} := by
  ext x
  constructor
  · intro hx l
    apply le_of_forall_pos_lt_add
    intro ε hε
    set δ := ε / (∑ k, x k + 1) with hδ
    have hS : 0 < ∑ k, x k + 1 := by
      have := Finset.sum_nonneg fun k (_ : k ∈ Finset.univ) => hx.1 k
      linarith
    have hδ0 : 0 < δ := div_pos hε hS
    set p : Fin L → ℝ := fun k => if k = l then 1 else δ with hp
    have hpos : StrictlyPositive p := fun k => by
      simp only [hp]; split_ifs <;> linarith
    have h : ∑ k, p k ≤ p ⬝ᵥ x := hx.2 p hpos
    have hsplit : ∀ f : Fin L → ℝ, ∑ k, (if k = l then 1 else δ) * f k =
        f l + δ * ∑ k, (if k = l then 0 else f k) := by
      intro f
      rw [Finset.mul_sum, ← Finset.sum_erase_add _ _ (Finset.mem_univ l),
        ← Finset.sum_erase_add (s := Finset.univ) (a := l) _ (Finset.mem_univ l)]
      simp only [ite_true, one_mul, mul_zero, add_zero]
      rw [add_comm]
      congr 1
      refine Finset.sum_congr rfl fun k hk => ?_
      simp [Finset.ne_of_mem_erase hk]
    have h1 : ∑ k, p k = 1 + δ * ∑ k, (if k = l then 0 else 1) := by
      have := hsplit fun _ => 1
      simpa [hp] using this
    have h2 : p ⬝ᵥ x = x l + δ * ∑ k, (if k = l then 0 else x k) := by
      have := hsplit x
      simpa [hp, dotProduct] using this
    rw [h1, h2] at h
    have hb : ∑ k, (if k = l then 0 else x k) ≤ ∑ k, x k :=
      Finset.sum_le_sum fun k _ => by split_ifs <;> linarith [hx.1 k]
    have hc : 0 ≤ ∑ k, (if k = l then (0 : ℝ) else 1) :=
      Finset.sum_nonneg fun k _ => by split_ifs <;> norm_num
    have hδx : δ * ∑ k, x k < ε := by
      rw [hδ, div_mul_eq_mul_div, div_lt_iff₀ hS]
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hb hδ0.le, mul_nonneg hδ0.le hc]
  · intro hx
    refine ⟨fun l => le_trans zero_le_one (hx l), fun p hp => ?_⟩
    simp only [dotProduct]
    exact Finset.sum_le_sum fun l _ => le_mul_of_one_le_right (hp l).le (hx l)

/-- **Section 3.H** (MWG, p. 78, small type). If the actual at-least-as-good set `K ⊆ ℝ^L_+` is
nonempty and closed upward in `ℝ^L_+` (as for monotone preferences), then
`V_u = {x ≥ 0 : p·x ≥ μ_K(p) for all p ≫ 0}` is the closed convex hull of `K` (the book says
"the convex hull"; see correction D2). -/
theorem recoveredSet_eq_closure_convexHull {K : Set (Fin L → ℝ)} (hK : K ⊆ nonnegOrthant L)
    (hne : K.Nonempty) (hup : ∀ x ∈ K, ∀ y, x ≤ y → y ∈ K) :
    recoveredSet (supportFn K) = closure (convexHull ℝ K) := by
  apply Set.Subset.antisymm
  · intro x hx
    rw [← halfspace_inter_eq_closure]
    intro p
    by_cases hp : ∀ l, 0 ≤ p l
    · have hbdd : ∀ q : Fin L → ℝ, (∀ l, 0 ≤ q l) → BddBelow ((fun x => q ⬝ᵥ x) '' K) :=
        fun q hq => ⟨0, by
          rintro _ ⟨y, hy, rfl⟩
          exact Finset.sum_nonneg fun l _ => mul_nonneg (hq l) (hK hy l)⟩
      rw [supportFnE_eq_coe hne (hbdd p hp), EReal.coe_le_coe_iff]
      apply le_of_forall_pos_lt_add
      intro ε hε
      have hS : 0 < ∑ l, x l + 1 := by
        have := Finset.sum_nonneg fun l (_ : l ∈ Finset.univ) => hx.1 l
        linarith
      set δ := ε / (∑ l, x l + 1) with hδ
      have hδ0 : 0 < δ := div_pos hε hS
      set q : Fin L → ℝ := p + fun _ => δ with hq
      have hqpos : StrictlyPositive q := fun l => by simp only [hq, Pi.add_apply]; linarith [hp l]
      have h1 : supportFn K p ≤ supportFn K q := by
        apply le_supportFn hne
        intro y hy
        refine (supportFn_le (hbdd p hp) hy).trans ?_
        apply dotProduct_le_dotProduct_of_nonneg_right _ (hK hy)
        intro l
        simp only [hq, Pi.add_apply]
        linarith
      have h2 := hx.2 q hqpos
      have h3 : q ⬝ᵥ x = p ⬝ᵥ x + δ * ∑ l, x l := by
        simp only [hq, dotProduct, Pi.add_apply, Finset.mul_sum]
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun l _ => by ring
      have h4 : δ * ∑ l, x l < ε := by
        rw [hδ, div_mul_eq_mul_div, div_lt_iff₀ hS]
        nlinarith
      linarith
    · push Not at hp
      obtain ⟨l, hl⟩ := hp
      rw [supportFnE_eq_bot]
      · exact bot_le
      · rw [not_bddBelow_iff]
        intro m
        obtain ⟨k, hk⟩ := hne
        set t := (|m| + |p ⬝ᵥ k| + 1) / (-p l) with ht
        have ht0 : 0 ≤ t := div_nonneg (by positivity) (by linarith)
        have hle : k ≤ k + t • Pi.single l 1 := by
          intro j
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          have : 0 ≤ (Pi.single l (1 : ℝ) : Fin L → ℝ) j := by
            rw [Pi.single_apply]; split_ifs <;> norm_num
          nlinarith
        refine ⟨_, ⟨k + t • Pi.single l 1, hup k hk _ hle, rfl⟩, ?_⟩
        simp only [dotProduct_add, dotProduct_smul, dotProduct_single, mul_one, smul_eq_mul]
        have : t * p l = -(|m| + |p ⬝ᵥ k| + 1) := by
          rw [ht, div_mul_eq_mul_div, div_eq_iff (by linarith)]
          ring
        rw [this]
        have := le_abs_self (p ⬝ᵥ k)
        have := neg_abs_le m
        linarith
  · apply closure_minimal _ (isClosed_recoveredSet _)
    exact convexHull_min (subset_recoveredSet hK) (convex_recoveredSet _)

/-- **Section 3.H** (MWG, pp. 79-80). A solution of (3.H.2) need not exist when `L > 2`: the
demand of Exercise 2.F.15 (`L = 3`) is homogeneous of degree zero and satisfies Walras' law and
the weak axiom, but its Slutsky matrix is nowhere symmetric, so (3.H.2) has no solution that is
positive at any `p ≫ 0` (`pde_slutsky_symmetric`), and no expenditure function can be recovered. -/
theorem section_3_H_no_solution :
    HomogeneousZero demand_2_F_15 ∧ WalrasLaw demand_2_F_15 ∧ WeakAxiom demand_2_F_15 ∧
      ∀ E : (Fin 3 → ℝ) → ℝ, SolvesPDE demand_2_F_15 E →
        ∀ p, StrictlyPositive p → ¬ 0 < E p := by
  refine ⟨exercise_2_F_15_basic.1, exercise_2_F_15_basic.2.1, exercise_2_F_15_weakAxiom,
    fun E hE p hp hpos => ?_⟩
  have hd : PWDomain p (E p) := ⟨hp, hpos⟩
  have hD := (demand_2_F_15_differentiableAt hd).hasFDerivAt
  have hsym := pde_slutsky_symmetric hE hp hD
  exact exercise_2_F_15_not_symm hd (Matrix.IsSymm.ext fun i j => hsym j i)

end MWG.ClassicalDemand
