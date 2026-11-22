/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGAggregateDemand.LShaped
import MWGClassicalDemand.SARPBasic
import Mathlib.Topology.Order.Compact

/-!
# Aggregate demand and the existence of a representative consumer

MWG, Section 4.D, pp. 116-122, and Exercises 4.D.1, 4.D.2, 4.D.3, 4.D.4(b), 4.D.5, 4.D.8
(pp. 125-126).

* **Definition 4.D.1** (p. 116): a positive representative consumer `IsPositiveRepresentative`;
  footnote 14: its demand satisfies the weak axiom and (for a relation rational on all bundles)
  the strong axiom.
* **Definition 4.D.2** (p. 117): a Bergson-Samuelson social welfare function
  `SocialWelfareFunction`; problem (4.D.1), `SolvesSWP`, and its value `v(p, w)`.
* **Proposition 4.D.1** (p. 117). The book's proof uses first-order conditions, Roy's identity
  and the envelope theorem and neglects corners. Here it is proved without differentiability or
  interiority (so Exercise 4.D.3, corners allowed, is covered), by Exercise 4.D.4's route: the
  utility `u(x) = sup {W(u₁(x₁), …, u_I(x_I)) : xᵢ ≥ 0, ∑ᵢ xᵢ ≤ x}` (`repUtility`) has indirect
  utility `v(p, w)`, and the aggregate demand `x(p, w) = ∑ᵢ xᵢ(p, wᵢ(p, w))` is a maximizer of
  `u` on `B_{p,w}` (`proposition_4_D_1_demand`, monotone `W` only). With `W` continuous and
  strictly increasing, `uᵢ` continuous with single-valued demand, and problem (4.D.1) uniquely
  solved, `x(p, w)` is the only maximizer, so `u` is a positive representative consumer
  (`proposition_4_D_1`). The uniqueness of the optimal distribution is implicit in the book,
  which treats `(wᵢ(p, w))` as a function and needs single-valued representative demand
  (correction 6).
* **Exercise 4.D.1**: `v(p, w)` is also the value of distributing bundles, and the bundles
  `xᵢ(p, wᵢ(p, w))` solve that problem.
* **Exercise 4.D.2**: `v` is homogeneous of degree zero, nondecreasing in `w`, nonincreasing in
  `p` and quasiconvex.
* **Definition 4.D.3** (p. 118): a normative representative consumer.
* **Section 4.D** (p. 121): a normative representative needs `A ⊆ B` (`normative_A_subset_B`).
* **Exercise 4.D.5**: an economy with fixed shares and no positive representative consumer
  (Example 4.C.1's economy).
* **Exercise 4.D.8**: passing the potential compensation test means every normative
  representative consumer prefers the change.
-/

namespace MWG.AggregateDemand

open MWG.ConsumerChoice MWG.ClassicalDemand Kreps.PreferenceProperties

variable {L I : ℕ}

/-- **Definition 4.D.1** (MWG, p. 116). A positive representative consumer for the aggregate
demand function `x(p, w)`: a rational preference `≿` on `ℝ^L_+` whose Walrasian demand is
`x(p, w)`, i.e. `x(p, w) ≻ y` whenever `y ≠ x(p, w)` and `y ∈ B_{p,w}`. -/
def IsPositiveRepresentative (r : (Fin L → ℝ) → (Fin L → ℝ) → Prop) (x : DemandFunction L) :
    Prop :=
  RationalOn (nonnegOrthant L) r ∧ ∀ p w, PWDomain p w →
    x p w ∈ budgetSet p w ∧ ∀ y ∈ budgetSet p w, y ≠ x p w → Strict r (x p w) y

/-- **Footnote 14** (MWG, p. 116). If there is a positive representative consumer, aggregate
demand satisfies the weak axiom. -/
theorem weakAxiom_of_positiveRepresentative {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    {x : DemandFunction L} (h : IsPositiveRepresentative r x) : WeakAxiom x := by
  intro p w p' w' hd hd' hle hne
  have h1 := (h.2 p w hd).2 (x p' w') ⟨(h.2 p' w' hd').1.1, hle⟩ hne
  by_contra hcon
  push Not at hcon
  have h2 := (h.2 p' w' hd').2 (x p w) ⟨(h.2 p w hd).1.1, hcon⟩ (Ne.symm hne)
  exact h1.2 h2.1

/-- **Footnote 14** (MWG, p. 116). If the positive representative's relation is rational on all
bundles (as the relation `utilityPref u` induced by any utility is), aggregate demand also
satisfies the strong axiom (MWG Chapter 3's `strongAxiom_of_rationalizes`). -/
theorem strongAxiom_of_positiveRepresentative {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    {x : DemandFunction L} (h : IsPositiveRepresentative r x) (hr : Rational r) :
    StrongAxiom x :=
  strongAxiom_of_rationalizes (fun p w hd => (h.2 p w hd).1.1) hr fun p w hd => (h.2 p w hd).2

/-- The relation induced by a utility function is rational on all bundles. -/
theorem rational_utilityPref (u : (Fin L → ℝ) → ℝ) : Rational (utilityPref u) :=
  ⟨fun a b => le_total (u b) (u a), fun _ _ _ h1 h2 => h2.trans h1⟩

/-- **Definition 4.D.2** (MWG, p. 117). A (Bergson-Samuelson) social welfare function
`W : ℝ^I → ℝ`, assigning a social utility to each vector of individual utility levels. -/
abbrev SocialWelfareFunction (I : ℕ) := (Fin I → ℝ) → ℝ

/-- A feasible wealth distribution in problem (4.D.1): `wᵢ ≥ 0`, `∑ᵢ wᵢ ≤ w`. -/
def FeasibleDistribution (w : ℝ) (ws : Fin I → ℝ) : Prop :=
  (∀ i, 0 ≤ ws i) ∧ ∑ i, ws i ≤ w

/-- **Problem (4.D.1)** (MWG, p. 117). The distribution `ws` maximizes
`W(v₁(p, w₁), …, v_I(p, w_I))` over feasible distributions, `vᵢ` the indirect utility of `uᵢ`. -/
def SolvesSWP (W : SocialWelfareFunction I) (us : Fin I → (Fin L → ℝ) → ℝ) (p : Fin L → ℝ)
    (w : ℝ) (ws : Fin I → ℝ) : Prop :=
  FeasibleDistribution w ws ∧ ∀ ws', FeasibleDistribution w ws' →
    W (fun i => indirectUtility (us i) p (ws' i)) ≤ W (fun i => indirectUtility (us i) p (ws i))

/-- **Section 4.D** (MWG, p. 117). The value `v(p, w) = W(v₁(p, w₁(p, w)), …)` of problem
(4.D.1) at the distribution given by the rule `wr`: the social indirect utility function. -/
noncomputable def socialIndirectUtility (W : SocialWelfareFunction I)
    (us : Fin I → (Fin L → ℝ) → ℝ) (wr : Fin I → (Fin L → ℝ) → ℝ → ℝ) (p : Fin L → ℝ)
    (w : ℝ) : ℝ :=
  W fun i => indirectUtility (us i) p (wr i p w)

/-- **Exercise 4.D.4** (MWG, p. 125). The utility of the normative representative consumer:
`u(x) = sup {W(u₁(x₁), …, u_I(x_I)) : xᵢ ∈ ℝ^L_+, ∑ᵢ xᵢ ≤ x}`. -/
noncomputable def repUtility (W : SocialWelfareFunction I) (us : Fin I → (Fin L → ℝ) → ℝ)
    (x : Fin L → ℝ) : ℝ :=
  sSup {t | ∃ ys : Fin I → Fin L → ℝ, (∀ i, ys i ∈ nonnegOrthant L) ∧ ∑ i, ys i ≤ x ∧
    t = W fun i => us i (ys i)}

/-- The dot product with `p ≥ 0` is monotone. -/
theorem dotProduct_le_of_le {p a b : Fin L → ℝ} (hp : ∀ l, 0 ≤ p l) (hab : a ≤ b) :
    p ⬝ᵥ a ≤ p ⬝ᵥ b :=
  Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hab l) (hp l)

/-- **Exercise 4.D.1** (MWG, p. 125), the bound. If `ws` solves (4.D.1) at `(p, w)` and `W` is
monotone, then every bundle distribution `(yᵢ) ≥ 0` with `p·∑ᵢ yᵢ ≤ w` has
`W(u₁(y₁), …) ≤ W(v₁(p, w₁), …)`: give consumer `i` the wealth `p·yᵢ`. -/
theorem split_value_le {W : SocialWelfareFunction I} (hW : Monotone W)
    {us : Fin I → (Fin L → ℝ) → ℝ} (hu : ∀ i, ContinuousOn (us i) (nonnegOrthant L))
    {p : Fin L → ℝ} (hp : StrictlyPositive p) {w : ℝ} {ws : Fin I → ℝ}
    (hopt : SolvesSWP W us p w ws) {ys : Fin I → Fin L → ℝ}
    (hys : ∀ i, ys i ∈ nonnegOrthant L) (hb : p ⬝ᵥ ∑ i, ys i ≤ w) :
    (W fun i => us i (ys i)) ≤ W fun i => indirectUtility (us i) p (ws i) := by
  have hfeas : FeasibleDistribution w fun i => p ⬝ᵥ ys i := by
    refine ⟨fun i => Finset.sum_nonneg fun l _ => mul_nonneg (hp l).le (hys i l), ?_⟩
    rw [← dotProduct_sum]
    exact hb
  refine le_trans (hW fun i => ?_) (hopt.2 _ hfeas)
  exact le_indirectUtility (hu i) hp ⟨hys i, le_rfl⟩

/-- **Exercise 4.D.1** (MWG, p. 125). Suppose `ws` solves (4.D.1) at `(p, w)` and each
`xᵢ ∈ xᵢ(p, wᵢ)`. Then the bundles `(xᵢ)` solve `max W(u₁(x₁), …, u_I(x_I))` subject to
`p·∑ᵢ xᵢ ≤ w`, and the value of that problem is `v(p, w)`: the planner need only distribute
wealth and let consumers choose. -/
theorem exercise_4_D_1 {W : SocialWelfareFunction I} (hW : Monotone W)
    {us : Fin I → (Fin L → ℝ) → ℝ} (hu : ∀ i, ContinuousOn (us i) (nonnegOrthant L))
    {p : Fin L → ℝ} (hp : StrictlyPositive p) {w : ℝ} {ws : Fin I → ℝ}
    (hopt : SolvesSWP W us p w ws) {xb : Fin I → Fin L → ℝ}
    (hxb : ∀ i, xb i ∈ walrasianDemand (us i) p (ws i)) :
    (∀ i, xb i ∈ nonnegOrthant L) ∧ p ⬝ᵥ ∑ i, xb i ≤ w ∧
      ((W fun i => us i (xb i)) = W fun i => indirectUtility (us i) p (ws i)) ∧
      ∀ ys : Fin I → Fin L → ℝ, (∀ i, ys i ∈ nonnegOrthant L) → p ⬝ᵥ ∑ i, ys i ≤ w →
        (W fun i => us i (ys i)) ≤ W fun i => us i (xb i) := by
  have hval : (W fun i => us i (xb i)) = W fun i => indirectUtility (us i) p (ws i) := by
    congr 1
    funext i
    exact (indirectUtility_eq_of_mem (hxb i)).symm
  refine ⟨fun i => (hxb i).1.1, ?_, hval, fun ys hys hb => ?_⟩
  · rw [dotProduct_sum]
    exact (Finset.sum_le_sum fun i _ => (hxb i).1.2).trans hopt.1.2
  · rw [hval]
    exact split_value_le hW hu hp hopt hys hb

/-- The standing hypotheses of Section 4.D on the planner's problem: `W` monotone, each `uᵢ`
continuous on `ℝ^L_+`, the rule `wr` solves (4.D.1) at every `p ≫ 0`, `w ≥ 0`, and each
consumer's demand function `xᵢ` is a selection from `xᵢ(p, w)` at every `p ≫ 0`, `w ≥ 0`. -/
structure PlannerSetup (W : SocialWelfareFunction I) (us : Fin I → (Fin L → ℝ) → ℝ) where
  /-- The optimal distribution rule. -/
  wr : Fin I → (Fin L → ℝ) → ℝ → ℝ
  /-- The individual demand functions. -/
  xs : Fin I → DemandFunction L
  monotone : Monotone W
  cont : ∀ i, ContinuousOn (us i) (nonnegOrthant L)
  opt : ∀ p w, StrictlyPositive p → 0 ≤ w → SolvesSWP W us p w fun i => wr i p w
  demand : ∀ i p w, StrictlyPositive p → 0 ≤ w → xs i p w ∈ walrasianDemand (us i) p w

variable {W : SocialWelfareFunction I} {us : Fin I → (Fin L → ℝ) → ℝ}

/-- The aggregate demand of a planner setup, `x(p, w) = ∑ᵢ xᵢ(p, wᵢ(p, w))`. -/
theorem PlannerSetup.aggregate_mem_budgetSet (S : PlannerSetup W us) {p : Fin L → ℝ}
    (hp : StrictlyPositive p) {w : ℝ} (hw : 0 ≤ w) :
    ruleDemand S.xs S.wr p w ∈ budgetSet p w := by
  refine ⟨fun l => ?_, ?_⟩
  · simp only [ruleDemand, Finset.sum_apply]
    exact Finset.sum_nonneg fun i _ => (S.demand i p _ hp ((S.opt p w hp hw).1.1 i)).1.1 l
  · simp only [ruleDemand]
    rw [dotProduct_sum]
    exact (Finset.sum_le_sum fun i _ =>
      (S.demand i p _ hp ((S.opt p w hp hw).1.1 i)).1.2).trans (S.opt p w hp hw).1.2

/-- **Exercise 4.D.4(b)** (MWG, p. 126), the key bound: on `B_{p,w}`, `u(y) ≤ v(p, w)`, and
`u(x(p, w)) = v(p, w)`. -/
theorem PlannerSetup.repUtility_spec (S : PlannerSetup W us) {p : Fin L → ℝ}
    (hp : StrictlyPositive p) {w : ℝ} (hw : 0 ≤ w) :
    (∀ y ∈ budgetSet p w, repUtility W us y ≤ socialIndirectUtility W us S.wr p w) ∧
      repUtility W us (ruleDemand S.xs S.wr p w) = socialIndirectUtility W us S.wr p w := by
  have hopt := S.opt p w hp hw
  have hbound : ∀ y ∈ budgetSet p w, ∀ t ∈ {t | ∃ ys : Fin I → Fin L → ℝ,
      (∀ i, ys i ∈ nonnegOrthant L) ∧ ∑ i, ys i ≤ y ∧ t = W fun i => us i (ys i)},
      t ≤ socialIndirectUtility W us S.wr p w := by
    rintro y hy _ ⟨ys, hys, hsum, rfl⟩
    exact split_value_le S.monotone S.cont hp hopt hys
      ((dotProduct_le_of_le (fun l => (hp l).le) hsum).trans hy.2)
  have hne : ∀ y ∈ budgetSet p w, ({t | ∃ ys : Fin I → Fin L → ℝ,
      (∀ i, ys i ∈ nonnegOrthant L) ∧ ∑ i, ys i ≤ y ∧ t = W fun i => us i (ys i)}).Nonempty :=
    fun y hy => ⟨_, fun _ => 0, fun _ _ => le_rfl, fun l => by simpa using hy.1 l, rfl⟩
  refine ⟨fun y hy => csSup_le (hne y hy) (hbound y hy), ?_⟩
  have hx := S.aggregate_mem_budgetSet hp hw
  apply le_antisymm (csSup_le (hne _ hx) (hbound _ hx))
  apply le_csSup ⟨_, hbound _ hx⟩
  refine ⟨fun i => S.xs i p (S.wr i p w), fun i => (S.demand i p _ hp (hopt.1.1 i)).1.1,
    le_rfl, ?_⟩
  unfold socialIndirectUtility
  congr 1
  funext i
  exact indirectUtility_eq_of_mem (S.demand i p _ hp (hopt.1.1 i))

/-- **Proposition 4.D.1** (MWG, p. 117), existence part, and **Exercise 4.D.4(b)**. For a
monotone `W` and an optimal distribution rule, the aggregate demand
`x(p, w) = ∑ᵢ xᵢ(p, wᵢ(p, w))` is a Walrasian demand of the representative utility `u`
(`max u(x)` s.t. `p·x ≤ w`), and the indirect utility of `u` is the value `v(p, w)` of
(4.D.1). No differentiability or interiority is needed (Exercise 4.D.3). -/
theorem proposition_4_D_1_demand (S : PlannerSetup W us) {p : Fin L → ℝ}
    (hp : StrictlyPositive p) {w : ℝ} (hw : 0 ≤ w) :
    ruleDemand S.xs S.wr p w ∈ walrasianDemand (repUtility W us) p w ∧
      indirectUtility (repUtility W us) p w = socialIndirectUtility W us S.wr p w := by
  obtain ⟨hle, heq⟩ := S.repUtility_spec hp hw
  have hmem : ruleDemand S.xs S.wr p w ∈ walrasianDemand (repUtility W us) p w :=
    ⟨S.aggregate_mem_budgetSet hp hw, fun y hy => (hle y hy).trans heq.ge⟩
  exact ⟨hmem, (indirectUtility_eq_of_mem hmem).trans heq⟩

/-- The set of bundle distributions `ys ≥ 0` with `∑ᵢ yᵢ ≤ y` is compact. -/
theorem isCompact_splits (y : Fin L → ℝ) :
    IsCompact {ys : Fin I → Fin L → ℝ | (∀ i, ys i ∈ nonnegOrthant L) ∧ ∑ i, ys i ≤ y} := by
  apply (isCompact_Icc (a := (0 : Fin I → Fin L → ℝ)) (b := fun _ => y)).of_isClosed_subset
  · have h1 : IsClosed {ys : Fin I → Fin L → ℝ | ∀ i, ys i ∈ nonnegOrthant L} := by
      have : {ys : Fin I → Fin L → ℝ | ∀ i, ys i ∈ nonnegOrthant L} =
          ⋂ i, ⋂ l, {ys : Fin I → Fin L → ℝ | 0 ≤ ys i l} := by
        ext ys
        simp [nonnegOrthant]
      rw [this]
      exact isClosed_iInter fun i => isClosed_iInter fun l =>
        isClosed_le continuous_const ((continuous_apply l).comp (continuous_apply i))
    have h2 : IsClosed {ys : Fin I → Fin L → ℝ | ∑ i, ys i ≤ y} :=
      isClosed_le (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const
    exact h1.inter h2
  · rintro ys ⟨hys, hsum⟩
    refine ⟨fun i l => hys i l, fun i l => ?_⟩
    have := hsum l
    simp only [Finset.sum_apply] at this
    calc ys i l ≤ ∑ j, ys j l :=
          Finset.single_le_sum (f := fun j => ys j l) (fun j _ => hys j l) (Finset.mem_univ i)
      _ ≤ y l := this

/-- **Proposition 4.D.1** (MWG, p. 117). Suppose `W` is continuous and strictly increasing,
each `uᵢ` is continuous on `ℝ^L_+` with single-valued Walrasian demand satisfying Walras' law,
and for each `(p, w)` the distribution `(wᵢ(p, w))` (adding up to `w`) is the unique solution
of (4.D.1). Then the value function `v(p, w)` of (4.D.1) is the indirect utility function of a
positive representative consumer for `x(p, w) = ∑ᵢ xᵢ(p, wᵢ(p, w))`: the preference
represented by `u` of Exercise 4.D.4. -/
theorem proposition_4_D_1 (S : PlannerSetup W us) (hWc : Continuous W) (hWs : StrictMono W)
    (hrule : IsWealthDistributionRule S.wr)
    (huniq : ∀ i p w, StrictlyPositive p → 0 ≤ w → (walrasianDemand (us i) p w).Subsingleton)
    (hwal : ∀ i p w, StrictlyPositive p → 0 ≤ w → p ⬝ᵥ S.xs i p w = w)
    (hoptu : ∀ p w ws, PWDomain p w → SolvesSWP W us p w ws → ws = fun i => S.wr i p w) :
    IsPositiveRepresentative (utilityPref (repUtility W us)) (ruleDemand S.xs S.wr) ∧
      ∀ p w, PWDomain p w →
        indirectUtility (repUtility W us) p w = socialIndirectUtility W us S.wr p w := by
  refine ⟨⟨(representsOn_utilityPref _ _).rationalOn, fun p w hd => ?_⟩,
    fun p w hd => (proposition_4_D_1_demand S hd.1 hd.2.le).2⟩
  obtain ⟨hmem, -⟩ := proposition_4_D_1_demand S hd.1 hd.2.le
  obtain ⟨hle, heq⟩ := S.repUtility_spec hd.1 hd.2.le
  refine ⟨hmem.1, fun y hy hne => ?_⟩
  refine ⟨hmem.2 y hy, fun hge => hne ?_⟩
  -- `y` is also a maximizer: `u(y) = v(p, w)`; pick an optimal split of `y`
  have hyv : repUtility W us y = socialIndirectUtility W us S.wr p w :=
    le_antisymm (hle y hy) (heq ▸ hge)
  set K := {ys : Fin I → Fin L → ℝ | (∀ i, ys i ∈ nonnegOrthant L) ∧ ∑ i, ys i ≤ y}
  have hKne : K.Nonempty := ⟨fun _ => 0, fun _ _ => le_rfl, fun l => by simpa using hy.1 l⟩
  have hcont : ContinuousOn (fun ys : Fin I → Fin L → ℝ => W fun i => us i (ys i)) K := by
    apply hWc.comp_continuousOn
    apply continuousOn_pi.mpr
    intro i
    exact (S.cont i).comp (continuous_apply i).continuousOn fun ys hys => hys.1 i
  obtain ⟨ys, hysK, hmax⟩ := (isCompact_splits y).exists_isMaxOn hKne hcont
  have hval : (W fun i => us i (ys i)) = socialIndirectUtility W us S.wr p w := by
    rw [← hyv]
    apply le_antisymm
    · unfold repUtility
      refine le_csSup ⟨socialIndirectUtility W us S.wr p w, ?_⟩ ⟨ys, hysK.1, hysK.2, rfl⟩
      rintro _ ⟨zs, hzs, hzsum, rfl⟩
      exact split_value_le S.monotone S.cont hd.1 (S.opt p w hd.1 hd.2.le) hzs
        ((dotProduct_le_of_le (fun l => (hd.1 l).le) hzsum).trans hy.2)
    · unfold repUtility
      refine csSup_le ⟨_, ys, hysK.1, hysK.2, rfl⟩ ?_
      rintro _ ⟨zs, hzs, hzsum, rfl⟩
      exact hmax ⟨hzs, hzsum⟩
  -- wealth `p·yᵢ` for consumer `i`
  set ws' : Fin I → ℝ := fun i => p ⬝ᵥ ys i with hws'
  have hfeas : FeasibleDistribution w ws' := by
    refine ⟨fun i => Finset.sum_nonneg fun l _ => mul_nonneg (hd.1 l).le (hysK.1 i l), ?_⟩
    simp only [hws']
    rw [← dotProduct_sum]
    exact (dotProduct_le_of_le (fun l => (hd.1 l).le) hysK.2).trans hy.2
  have hui : ∀ i, us i (ys i) ≤ indirectUtility (us i) p (ws' i) :=
    fun i => le_indirectUtility (S.cont i) hd.1 ⟨hysK.1 i, le_rfl⟩
  have hopt := S.opt p w hd.1 hd.2.le
  have hle2 : (W fun i => indirectUtility (us i) p (ws' i)) ≤
      socialIndirectUtility W us S.wr p w := hopt.2 _ hfeas
  have hequ : ∀ i, us i (ys i) = indirectUtility (us i) p (ws' i) := by
    by_contra hc
    push Not at hc
    obtain ⟨j, hj⟩ := hc
    have hlt : (fun i => us i (ys i)) < fun i => indirectUtility (us i) p (ws' i) :=
      lt_of_le_of_ne (fun i => hui i) fun h => hj (congrFun h j)
    have := hWs hlt
    linarith
  -- `ws'` solves (4.D.1), hence equals the rule
  have hsolve : SolvesSWP W us p w ws' := by
    refine ⟨hfeas, fun ws'' h'' => ?_⟩
    have h1 := hopt.2 ws'' h''
    have h2 : (W fun i => indirectUtility (us i) p (ws' i)) =
        socialIndirectUtility W us S.wr p w := by
      rw [← hval]
      congr 1
      funext i
      exact (hequ i).symm
    rw [h2]
    exact h1
  have hws_eq := hoptu p w ws' hd hsolve
  -- each `yᵢ` is consumer `i`'s demand at `wᵢ(p, w)`
  have hyi : ∀ i, ys i = S.xs i p (S.wr i p w) := by
    intro i
    have hwi : ws' i = S.wr i p w := congrFun hws_eq i
    have hmemi : ys i ∈ walrasianDemand (us i) p (S.wr i p w) := by
      refine ⟨⟨hysK.1 i, by rw [← hwi]⟩, fun z hz => ?_⟩
      rw [hequ i, hwi]
      exact le_indirectUtility (S.cont i) hd.1 hz
    exact huniq i p _ hd.1 (hopt.1.1 i) hmemi (S.demand i p _ hd.1 (hopt.1.1 i))
  -- `y ≥ ∑ᵢ yᵢ = x(p, w)` and `p·y ≤ w = p·x(p, w)` force `y = x(p, w)`
  have hsumx : ∑ i, ys i = ruleDemand S.xs S.wr p w := by
    simp only [ruleDemand]
    exact Finset.sum_congr rfl fun i _ => hyi i
  have hxle : ruleDemand S.xs S.wr p w ≤ y := hsumx ▸ hysK.2
  have hpx : p ⬝ᵥ ruleDemand S.xs S.wr p w = w := by
    simp only [ruleDemand]
    rw [dotProduct_sum]
    calc ∑ i, p ⬝ᵥ S.xs i p (S.wr i p w) = ∑ i, S.wr i p w :=
          Finset.sum_congr rfl fun i _ => hwal i p _ hd.1 (hopt.1.1 i)
      _ = w := hrule p w
  funext l
  have hdiff : p ⬝ᵥ (y - ruleDemand S.xs S.wr p w) ≤ 0 := by
    rw [dotProduct_sub, hpx]
    linarith [hy.2]
  have hterms : ∀ k, 0 ≤ p k * (y - ruleDemand S.xs S.wr p w) k :=
    fun k => mul_nonneg (hd.1 k).le (sub_nonneg.mpr (hxle k))
  have hzero : p l * (y - ruleDemand S.xs S.wr p w) l = 0 := by
    have hsum0 : ∑ k, p k * (y - ruleDemand S.xs S.wr p w) k = 0 :=
      le_antisymm hdiff (Finset.sum_nonneg fun k _ => hterms k)
    exact (Finset.sum_eq_zero_iff_of_nonneg fun k _ => hterms k).mp hsum0 l (Finset.mem_univ l)
  have := (mul_eq_zero.mp hzero).resolve_left (hd.1 l).ne'
  simp only [Pi.sub_apply] at this
  linarith

/-- **Definition 4.D.3** (MWG, p. 118). The positive representative consumer `≿` for
`x(p, w) = ∑ᵢ xᵢ(p, wᵢ(p, w))` is a normative representative consumer relative to `W` if the
rule `(wᵢ(p, w))` is a wealth distribution rule solving (4.D.1) at every `(p, w)` and the value
function of (4.D.1) is an indirect utility function for `≿`. -/
def IsNormativeRepresentative (W : SocialWelfareFunction I) (us : Fin I → (Fin L → ℝ) → ℝ)
    (wr : Fin I → (Fin L → ℝ) → ℝ → ℝ) (r : (Fin L → ℝ) → (Fin L → ℝ) → Prop)
    (x : DemandFunction L) : Prop :=
  IsPositiveRepresentative r x ∧ IsWealthDistributionRule wr ∧
    (∀ p w, PWDomain p w → SolvesSWP W us p w fun i => wr i p w) ∧
    ∃ u, RepresentsOn (nonnegOrthant L) u r ∧
      ∀ p w, PWDomain p w → indirectUtility u p w = socialIndirectUtility W us wr p w

/-- **Section 4.D** (MWG, p. 118). Under the hypotheses of Proposition 4.D.1 the
representative consumer `u` of Exercise 4.D.4 is a normative representative consumer. -/
theorem proposition_4_D_1_normative (S : PlannerSetup W us) (hWc : Continuous W)
    (hWs : StrictMono W) (hrule : IsWealthDistributionRule S.wr)
    (huniq : ∀ i p w, StrictlyPositive p → 0 ≤ w → (walrasianDemand (us i) p w).Subsingleton)
    (hwal : ∀ i p w, StrictlyPositive p → 0 ≤ w → p ⬝ᵥ S.xs i p w = w)
    (hoptu : ∀ p w ws, PWDomain p w → SolvesSWP W us p w ws → ws = fun i => S.wr i p w) :
    IsNormativeRepresentative W us S.wr (utilityPref (repUtility W us)) (ruleDemand S.xs S.wr) :=
  have h := proposition_4_D_1 S hWc hWs hrule huniq hwal hoptu
  ⟨h.1, hrule, fun p w hd => S.opt p w hd.1 hd.2.le,
    repUtility W us, representsOn_utilityPref _ _, h.2⟩

/-! ### Exercise 4.D.2 -/

/-- **Exercise 4.D.2** (MWG, p. 125). The value function `v(p, w)` of (4.D.1) has the properties
of an indirect utility function: (i) homogeneous of degree zero (given that the rule picks a
solution at `(αp, αw)`, the value there is the value at `(p, w)`); (ii) nondecreasing in `w`;
(iii) nonincreasing in `p`; (iv) quasiconvex on `{p ≫ 0, w > 0}`. -/
theorem exercise_4_D_2 (S : PlannerSetup W us) :
    (∀ p w α, StrictlyPositive p → 0 ≤ w → 0 < α →
      socialIndirectUtility W us S.wr (α • p) (α * w) = socialIndirectUtility W us S.wr p w) ∧
    (∀ p w w', StrictlyPositive p → 0 ≤ w → w ≤ w' →
      socialIndirectUtility W us S.wr p w ≤ socialIndirectUtility W us S.wr p w') ∧
    (∀ p p' w, StrictlyPositive p → StrictlyPositive p' → p ≤ p' → 0 ≤ w →
      socialIndirectUtility W us S.wr p' w ≤ socialIndirectUtility W us S.wr p w) ∧
    QuasiconvexOn ℝ {q : (Fin L → ℝ) × ℝ | PWDomain q.1 q.2}
      (fun q => socialIndirectUtility W us S.wr q.1 q.2) := by
  -- value at the rule dominates every feasible distribution
  have hdom : ∀ p w, StrictlyPositive p → 0 ≤ w → ∀ ws, FeasibleDistribution w ws →
      (W fun i => indirectUtility (us i) p (ws i)) ≤ socialIndirectUtility W us S.wr p w :=
    fun p w hp hw ws hws => (S.opt p w hp hw).2 ws hws
  refine ⟨fun p w α hp hw hα => ?_, fun p w w' hp hw hww => ?_,
    fun p p' w hp hp' hpp hw => ?_, ?_⟩
  · have hαp : StrictlyPositive (α • p) := fun l => by simpa using mul_pos hα (hp l)
    have hαw : 0 ≤ α * w := mul_nonneg hα.le hw
    apply le_antisymm
    · -- the rule at `(αp, αw)`, scaled by `1/α`, is feasible at `(p, w)`
      have hf : FeasibleDistribution w fun i => α⁻¹ * S.wr i (α • p) (α * w) := by
        obtain ⟨h0, hs⟩ := (S.opt _ _ hαp hαw).1
        refine ⟨fun i => mul_nonneg (inv_pos.mpr hα).le (h0 i), ?_⟩
        rw [← Finset.mul_sum, inv_mul_le_iff₀ hα]
        exact hs
      refine le_trans (le_of_eq ?_) (hdom p w hp hw _ hf)
      unfold socialIndirectUtility
      congr 1
      funext i
      rw [← proposition_3_D_3_i (us i) p _ hα, ← mul_assoc, mul_inv_cancel₀ hα.ne', one_mul]
    · have hf : FeasibleDistribution (α * w) fun i => α * S.wr i p w := by
        obtain ⟨h0, hs⟩ := (S.opt _ _ hp hw).1
        refine ⟨fun i => mul_nonneg hα.le (h0 i), ?_⟩
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left hs hα.le
      refine le_trans (le_of_eq ?_) (hdom _ _ hαp hαw _ hf)
      unfold socialIndirectUtility
      congr 1
      funext i
      rw [proposition_3_D_3_i (us i) p _ hα]
  · obtain ⟨h0, hs⟩ := (S.opt p w hp hw).1
    exact hdom p w' hp (hw.trans hww) _ ⟨h0, hs.trans hww⟩
  · refine le_trans (S.monotone fun i => ?_) (hdom p w hp hw _ (S.opt p' w hp' hw).1)
    exact proposition_3_D_3_ii_prices (S.cont i) hp hp' hpp ((S.opt p' w hp' hw).1.1 i)
  · intro t q hq q' hq' a b ha hb hab
    have hdom' : Convex ℝ {q : (Fin L → ℝ) × ℝ | PWDomain q.1 q.2} :=
      convex_pwDomainSet L
    refine ⟨hdom' hq.1 hq'.1 ha hb hab, ?_⟩
    obtain ⟨⟨hqd, hqt⟩, ⟨hq'd, hq't⟩⟩ := And.intro hq hq'
    set q'' := a • q + b • q' with hq''
    have hq''d : PWDomain q''.1 q''.2 := hdom' hqd hq'd ha hb hab
    -- the bundles demanded at `q''` are affordable (as a distribution) at `q` or at `q'`
    set xb : Fin I → Fin L → ℝ := fun i => S.xs i q''.1 (S.wr i q''.1 q''.2)
    have hopt'' := S.opt q''.1 q''.2 hq''d.1 hq''d.2.le
    obtain ⟨hx0, hxb, hval, -⟩ := exercise_4_D_1 S.monotone S.cont hq''d.1 hopt''
      (xb := xb) fun i => S.demand i _ _ hq''d.1 (hopt''.1.1 i)
    have hsplit : q''.1 ⬝ᵥ ∑ i, xb i = a * (q.1 ⬝ᵥ ∑ i, xb i) + b * (q'.1 ⬝ᵥ ∑ i, xb i) := by
      simp only [hq'', Prod.fst_add, Prod.smul_fst, add_dotProduct, smul_dotProduct,
        smul_eq_mul]
    have hw'' : q''.2 = a * q.2 + b * q'.2 := by simp [hq'']
    have hcase : q.1 ⬝ᵥ ∑ i, xb i ≤ q.2 ∨ q'.1 ⬝ᵥ ∑ i, xb i ≤ q'.2 := by
      by_contra hc
      push Not at hc
      have : q''.1 ⬝ᵥ ∑ i, xb i > q''.2 := by
        rw [hsplit, hw'']
        rcases eq_or_lt_of_le ha with ha0 | ha0
        · rw [← ha0] at hab ⊢
          simp only [zero_add] at hab
          rw [hab]
          linarith [hc.2]
        · nlinarith [hc.1, hc.2]
      linarith
    change socialIndirectUtility W us S.wr q''.1 q''.2 ≤ t
    unfold socialIndirectUtility
    rw [← hval]
    rcases hcase with h | h
    · exact (split_value_le S.monotone S.cont hqd.1 (S.opt _ _ hqd.1 hqd.2.le) hx0 h).trans hqt
    · exact (split_value_le S.monotone S.cont hq'd.1 (S.opt _ _ hq'd.1 hq'd.2.le) hx0 h).trans
        hq't

/-! ### The necessary condition `A ⊆ B` -/

/-- **Section 4.D** (MWG, p. 121; Figure 4.D.1). For the representative utility `u` of
Exercise 4.D.4, at `x̄ = x(p̄, w̄) = ∑ᵢ x̄ᵢ` with `x̄ᵢ = xᵢ(p̄, w̄ᵢ)`, every aggregate bundle
`∑ᵢ xᵢ` with `uᵢ(xᵢ) ≥ uᵢ(x̄ᵢ)` for all `i` (the set `A`) is at least as good as `x̄` for `u`
(the set `B`): `A ⊆ B`, the necessary condition for a normative representative consumer. -/
theorem normative_A_subset_B (S : PlannerSetup W us) {p : Fin L → ℝ}
    (hp : StrictlyPositive p) {w : ℝ} (hw : 0 ≤ w) {ys : Fin I → Fin L → ℝ}
    (hys : ∀ i, ys i ∈ nonnegOrthant L)
    (hge : ∀ i, us i (S.xs i p (S.wr i p w)) ≤ us i (ys i))
    (hbdd : BddAbove {t | ∃ zs : Fin I → Fin L → ℝ, (∀ i, zs i ∈ nonnegOrthant L) ∧
      ∑ i, zs i ≤ ∑ i, ys i ∧ t = W fun i => us i (zs i)}) :
    repUtility W us (ruleDemand S.xs S.wr p w) ≤ repUtility W us (∑ i, ys i) := by
  rw [(S.repUtility_spec hp hw).2]
  have hopt := S.opt p w hp hw
  unfold socialIndirectUtility
  have hv : (fun i => indirectUtility (us i) p (S.wr i p w)) =
      fun i => us i (S.xs i p (S.wr i p w)) := by
    funext i
    exact indirectUtility_eq_of_mem (S.demand i p _ hp (hopt.1.1 i))
  rw [hv]
  exact (S.monotone hge).trans (le_csSup hbdd ⟨ys, hys, le_rfl, rfl⟩)

/-! ### Exercise 4.D.5 -/

/-- **Exercise 4.D.5** (MWG, p. 126). An economy with fixed wealth shares `αᵢ` that admits no
positive representative consumer: the two consumers of Example 4.C.1 with `α = (1/2, 1/2)`.
Their aggregate demand violates the weak axiom, while the demand of a positive representative
consumer satisfies it (footnote 14). -/
theorem exercise_4_D_5 {x1 x2 : DemandFunction 2}
    (hx1 : ∀ p w, PWDomain p w → x1 p w ∈ walrasianDemand ex41U1 p w)
    (hx2 : ∀ p w, PWDomain p w → x2 p w ∈ walrasianDemand ex41U2 p w) :
    ¬ ∃ r, IsPositiveRepresentative r (shareDemand ![x1, x2] ![1 / 2, 1 / 2]) := by
  rintro ⟨r, hr⟩
  exact (example_4_C_1 hx1 hx2).2.2.2.2 (weakAxiom_of_positiveRepresentative hr)

/-! ### Exercise 4.D.8 -/

/-- **Section 4.D** (MWG, p. 120; Exercise 4.D.8). `(p', w')` passes the potential compensation
test over `(p, w)`: for every distribution `(wᵢ)` of `w` there is a distribution `(w'ᵢ)` of `w'`
with `vᵢ(p', w'ᵢ) > vᵢ(p, wᵢ)` for all `i` (distributions are nonnegative and add up to the
total). -/
def PassesPotentialCompensation (v : Fin I → (Fin L → ℝ) → ℝ → ℝ) (p : Fin L → ℝ) (w : ℝ)
    (p' : Fin L → ℝ) (w' : ℝ) : Prop :=
  ∀ ws : Fin I → ℝ, (∀ i, 0 ≤ ws i) → ∑ i, ws i = w →
    ∃ ws' : Fin I → ℝ, (∀ i, 0 ≤ ws' i) ∧ ∑ i, ws' i = w' ∧ ∀ i, v i p (ws i) < v i p' (ws' i)

/-- **Exercise 4.D.8** (MWG, p. 126). If `(p', w')` passes the potential compensation test over
`(p, w)` and `W` is strictly increasing, then any normative representative consumer prefers
`(p', w')`: its indirect utility (the value of (4.D.1)) is strictly higher. -/
theorem exercise_4_D_8 (hI : 0 < I) (hWs : StrictMono W) {wr : Fin I → (Fin L → ℝ) → ℝ → ℝ}
    {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop} {x : DemandFunction L}
    (hN : IsNormativeRepresentative W us wr r x) {p p' : Fin L → ℝ} {w w' : ℝ}
    (hd : PWDomain p w) (hd' : PWDomain p' w')
    (hpc : PassesPotentialCompensation (fun i => indirectUtility (us i)) p w p' w') :
    ∃ u, RepresentsOn (nonnegOrthant L) u r ∧ indirectUtility u p w < indirectUtility u p' w' := by
  obtain ⟨-, hrule, hopt, u, hu, hv⟩ := hN
  refine ⟨u, hu, ?_⟩
  rw [hv p w hd, hv p' w' hd']
  obtain ⟨ws', h0, hsum, hlt⟩ := hpc (fun i => wr i p w) (hopt p w hd).1.1 (hrule p w)
  have h1 : (W fun i => indirectUtility (us i) p (wr i p w)) <
      W fun i => indirectUtility (us i) p' (ws' i) :=
    hWs (Pi.lt_def.mpr ⟨fun i => (hlt i).le, ⟨⟨0, hI⟩, hlt _⟩⟩)
  exact h1.trans_le ((hopt p' w' hd').2 ws' ⟨h0, hsum.le⟩)

end MWG.AggregateDemand
