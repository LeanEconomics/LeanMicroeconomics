/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGWelfareTheorems.Replica

/-!
# Pareto optimality and social welfare optima (MWG Section 16.E, pp. 558-561)

Preferences are represented by utility functions `uᵢ` (`PrefEconomy.ofUtility`).

* The utility possibility set `U` and the Pareto frontier `UP` (p. 558-559);
  **Proposition 16.E.1**: a feasible allocation is Pareto optimal iff its utility vector lies in
  `UP`. Footnote 12: a boundary point of `U` need not be Pareto optimal (Figure 16.C.1).
* **Exercise 16.E.2**: convex `Xᵢ`, `Yⱼ` and concave `uᵢ` give a convex `U`.
* **Proposition 16.E.2**: a maximizer of `λ·u` on `U` with `λ ≫ 0` is in `UP`; if `U` is convex,
  every `ū ∈ UP` maximizes `λ·u` on `U` for some `λ ≥ 0`, `λ ≠ 0` (supporting hyperplane,
  Mathlib's geometric Hahn-Banach). Without convexity this fails (the point `ū` of Figure 16.E.1,
  made concrete with `uᵢ(x) = x²`).
* The normative representative consumer (16.E.2) (p. 561).
* **Exercise 16.E.1**: (a) a point of `U'` on the boundary of `U` that is not Pareto optimal;
  (b) with free disposal and continuous, strongly monotone utilities on `ℝ^L₊`, the utility vector
  of a feasible allocation that is not Pareto optimal is interior to `U` (so boundary points of
  `U` in `U'` are Pareto optimal), and `U' = U ∩ ℝ^I₊` when `uᵢ(0) = 0` and `0 ∈ Yⱼ`; (c) in a pure
  exchange economy with `ω̄ ≫ 0` and continuous preferences, no feasible allocation makes every
  consumer better off than at a price quasiequilibrium with transfers.
-/

namespace MWG.WelfareTheorems

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.Production Kreps.PreferenceProperties
open MWG.CompetitiveMarkets (Allocation)
open Filter Topology

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {L : ℕ}

/-- **Section 16.E** (MWG, p. 558). The utility possibility set
`U = {v ∈ ℝ^I : vᵢ ≤ uᵢ(xᵢ) for some feasible (x, y)}`. -/
def utilityPossibilitySet (E : PrefEconomy ι κ L) (u : ι → (Fin L → ℝ) → ℝ) : Set (ι → ℝ) :=
  {v | ∃ a, E.IsFeasible a ∧ ∀ i, v i ≤ u i (a.x i)}

/-- **Exercise 16.E.1** (MWG, p. 576). The set `U' ⊆ U` of utility vectors achieved by feasible
allocations. -/
def achievedUtilitySet (E : PrefEconomy ι κ L) (u : ι → (Fin L → ℝ) → ℝ) : Set (ι → ℝ) :=
  {v | ∃ a, E.IsFeasible a ∧ ∀ i, v i = u i (a.x i)}

/-- **Section 16.E** (MWG, p. 559). The Pareto frontier `UP`: the points of `U` not weakly
dominated, with a strict improvement, by another point of `U`. -/
def paretoFrontier (U : Set (ι → ℝ)) : Set (ι → ℝ) :=
  {v | v ∈ U ∧ ¬ ∃ v' ∈ U, (∀ i, v i ≤ v' i) ∧ ∃ i, v i < v' i}

/-- `U' ⊆ U`. -/
theorem achievedUtilitySet_subset (E : PrefEconomy ι κ L) (u : ι → (Fin L → ℝ) → ℝ) :
    achievedUtilitySet E u ⊆ utilityPossibilitySet E u :=
  fun _ ⟨a, ha, hv⟩ => ⟨a, ha, fun i => (hv i).le⟩

/-- `U` is comprehensive: `U - ℝ^I₊ ⊆ U`. -/
theorem utilityPossibilitySet_down {E : PrefEconomy ι κ L} {u : ι → (Fin L → ℝ) → ℝ}
    {v w : ι → ℝ} (hv : v ∈ utilityPossibilitySet E u) (hwv : w ≤ v) :
    w ∈ utilityPossibilitySet E u :=
  let ⟨a, ha, h⟩ := hv
  ⟨a, ha, fun i => (hwv i).trans (h i)⟩

/-- **Proposition 16.E.1** (MWG, p. 559). A feasible allocation is Pareto optimal if and only if
its utility vector lies on the Pareto frontier `UP`. -/
theorem proposition_16_E_1 {X : ι → Set (Fin L → ℝ)} {u : ι → (Fin L → ℝ) → ℝ}
    {Y : κ → Set (Fin L → ℝ)} {ω : Fin L → ℝ} {a : Allocation ι κ L}
    (ha : (PrefEconomy.ofUtility X u Y ω).IsFeasible a) :
    (PrefEconomy.ofUtility X u Y ω).IsParetoOptimal a ↔
      (fun i => u i (a.x i)) ∈ paretoFrontier
        (utilityPossibilitySet (PrefEconomy.ofUtility X u Y ω) u) := by
  constructor
  · rintro ⟨-, hno⟩
    refine ⟨⟨a, ha, fun _ => le_rfl⟩, ?_⟩
    rintro ⟨v', ⟨a', ha', hv'⟩, hle, i, hlt⟩
    exact hno ⟨a', ha', fun k => (hle k).trans (hv' k), i, (hle i).trans (hv' i),
      not_le.mpr (lt_of_lt_of_le hlt (hv' i))⟩
  · rintro ⟨-, hno⟩
    refine ⟨ha, ?_⟩
    rintro ⟨a', ha', hle, i, hi⟩
    exact hno ⟨fun k => u k (a'.x k), ⟨a', ha', fun _ => le_rfl⟩, fun k => hle k, i,
      not_le.mp hi.2⟩

/-- **Exercise 16.E.2** (MWG, p. 576; p. 559). If every `Xᵢ` and every `Yⱼ` is convex and every
`uᵢ` is concave on `Xᵢ`, the utility possibility set `U` is convex. -/
theorem exercise_16_E_2 {X : ι → Set (Fin L → ℝ)} {u : ι → (Fin L → ℝ) → ℝ}
    {Y : κ → Set (Fin L → ℝ)} {ω : Fin L → ℝ} (hY : ∀ j, Convex ℝ (Y j))
    (hu : ∀ i, ConcaveOn ℝ (X i) (u i)) :
    Convex ℝ (utilityPossibilitySet (PrefEconomy.ofUtility X u Y ω) u) := by
  rintro v ⟨a, ⟨⟨hx, hy⟩, hc⟩, hv⟩ v' ⟨a', ⟨⟨hx', hy'⟩, hc'⟩, hv'⟩ α β hα hβ hαβ
  refine ⟨⟨fun i => α • a.x i + β • a'.x i, fun j => α • a.y j + β • a'.y j⟩,
    ⟨⟨fun i => (hu i).1 (hx i) (hx' i) hα hβ hαβ, fun j => hY j (hy j) (hy' j) hα hβ hαβ⟩, ?_⟩,
    fun i => ?_⟩
  · change ∑ i, (α • a.x i + β • a'.x i) = ω + ∑ j, (α • a.y j + β • a'.y j)
    have hc0 : ∑ i, a.x i = ω + ∑ j, a.y j := hc
    have hc1 : ∑ i, a'.x i = ω + ∑ j, a'.y j := hc'
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum,
      ← Finset.smul_sum, ← Finset.smul_sum, hc0, hc1, smul_add, smul_add]
    have : α • ω + β • ω = ω := by rw [← add_smul, hαβ, one_smul]
    rw [show ω + (α • ∑ j, a.y j + β • ∑ j, a'.y j) =
      (α • ω + β • ω) + (α • ∑ j, a.y j + β • ∑ j, a'.y j) by rw [this]]
    abel
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := (hu i).2 (hx i) (hx' i) hα hβ hαβ
    simp only [smul_eq_mul] at this
    nlinarith [hv i, hv' i, mul_le_mul_of_nonneg_left (hv i) hα,
      mul_le_mul_of_nonneg_left (hv' i) hβ]

/-- **Proposition 16.E.2** (MWG, p. 560), first part. If `u*` maximizes `λ·u` on `U` for some
`λ ≫ 0`, then `u* ∈ UP`. -/
theorem proposition_16_E_2_i {U : Set (ι → ℝ)} {lam us : ι → ℝ} (hlam : ∀ i, 0 < lam i)
    (hus : us ∈ U) (hmax : ∀ v ∈ U, ∑ i, lam i * v i ≤ ∑ i, lam i * us i) :
    us ∈ paretoFrontier U := by
  refine ⟨hus, ?_⟩
  rintro ⟨v, hv, hle, i, hlt⟩
  have := Finset.sum_lt_sum (fun k _ => mul_le_mul_of_nonneg_left (hle k) (hlam k).le)
    ⟨i, Finset.mem_univ i, mul_lt_mul_of_pos_left hlt (hlam i)⟩
  linarith [hmax v hv]

/-- A continuous linear functional on `ℝ^I` is a weighted sum of the coordinates. -/
theorem strongDual_apply_eq_sum [DecidableEq ι] (f : StrongDual ℝ (ι → ℝ)) (v : ι → ℝ) :
    f v = ∑ i, f (Pi.single i 1) * v i := by
  conv_lhs => rw [show v = ∑ i, v i • (Pi.single i 1 : ι → ℝ) by
    funext k; simp [Finset.sum_apply, Pi.single_apply]]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]

/-- **Proposition 16.E.2** (MWG, p. 560), second part. If `U ⊆ ℝ^I` (`I > 0`) is convex and
comprehensive (`U - ℝ^I₊ ⊆ U`, as is every utility possibility set), then for every `ū ∈ UP`
there are welfare weights `λ ≥ 0`, `λ ≠ 0` such that `ū` maximizes `λ·u` on `U`. -/
theorem proposition_16_E_2_ii [Nonempty ι] {U : Set (ι → ℝ)} (hU : Convex ℝ U)
    (hdown : ∀ v ∈ U, ∀ w, w ≤ v → w ∈ U) {ub : ι → ℝ} (hub : ub ∈ paretoFrontier U) :
    ∃ lam : ι → ℝ, (∀ i, 0 ≤ lam i) ∧ lam ≠ 0 ∧
      ∀ v ∈ U, ∑ i, lam i * v i ≤ ∑ i, lam i * ub i := by
  classical
  set O : Set (ι → ℝ) := {v | ∀ i, ub i < v i} with hO
  have hOopen : IsOpen O := by
    have : O = ⋂ i, {v : ι → ℝ | ub i < v i} := by ext v; simp [hO]
    rw [this]
    exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)
  have hOconv : Convex ℝ O := by
    intro x hx y hy a b ha hb hab i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h1 := hx i; have h2 := hy i
    have : ub i = a * ub i + b * ub i := by rw [← add_mul, hab, one_mul]
    rcases ha.lt_or_eq with ha' | ha'
    · nlinarith [mul_lt_mul_of_pos_left h1 ha', mul_le_mul_of_nonneg_left h2.le hb]
    · subst ha'
      have hb1 : b = 1 := by linarith
      subst hb1
      simpa using h2
  have hdisj : Disjoint O U := by
    rw [Set.disjoint_left]
    intro v hvO hvU
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    exact hub.2 ⟨v, hvU, fun i => (hvO i).le, i₀, hvO i₀⟩
  obtain ⟨f, s, hfO, hfU⟩ := geometric_hahn_banach_open hOconv hOopen hU hdisj
  set lam : ι → ℝ := fun i => -f (Pi.single i 1) with hlam
  have hf : ∀ v, f v = -∑ i, lam i * v i := fun v => by
    rw [strongDual_apply_eq_sum]
    simp [hlam, Finset.sum_neg_distrib]
  -- `λ·v ≤ -s` on `U` and `λ·ū ≥ -s`
  have hU' : ∀ v ∈ U, ∑ i, lam i * v i ≤ -s := fun v hv => by
    have := hfU v hv
    rw [hf] at this
    linarith
  have hub' : -s ≤ ∑ i, lam i * ub i := by
    by_contra hlt
    push Not at hlt
    set S := ∑ i, |lam i| with hS
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => abs_nonneg _
    set ε := (-s - ∑ i, lam i * ub i) / (S + 1) with hε
    have hε0 : 0 < ε := div_pos (by linarith) (by linarith)
    have hmem : (fun i => ub i + ε) ∈ O := fun i => by simp; linarith
    have h1 := hfO _ hmem
    rw [hf] at h1
    have h2 : ∑ i, lam i * (ub i + ε) ≤ ∑ i, lam i * ub i + ε * S := by
      rw [hS, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun i _ => ?_
      have := le_abs_self (lam i)
      nlinarith
    have h3 : ε * S < -s - ∑ i, lam i * ub i := by
      rw [hε, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith
    linarith
  refine ⟨lam, fun i => ?_, ?_, fun v hv => (hU' v hv).trans hub'⟩
  · by_contra hneg
    push Not at hneg
    have hmem := hdown ub hub.1 (ub - (Pi.single i 1 : ι → ℝ)) (fun k => by
      by_cases hk : k = i
      · subst hk; simp
      · simp [hk])
    have := hU' _ hmem
    have hcalc : ∑ k, lam k * (ub - (Pi.single i 1 : ι → ℝ)) k = ∑ k, lam k * ub k - lam i := by
      simp [mul_sub, Finset.sum_sub_distrib, Pi.single_apply]
    rw [hcalc] at this
    linarith
  · intro h0
    have := hfU ub hub.1
    have h2 := hfO (fun i => ub i + 1) (fun i => by simp)
    rw [hf] at this h2
    simp [h0] at this h2
    linarith

/-- **Section 16.E** (MWG, p. 560). If the utility possibility set is convex (and `I > 0`), every
Pareto optimal allocation (in particular every Walrasian equilibrium allocation, by Proposition
16.C.1) maximizes `∑ᵢ λᵢuᵢ` on `U` for some welfare weights `λ ≥ 0`, `λ ≠ 0`. -/
theorem pareto_isWelfareOptimum [Nonempty ι] {X : ι → Set (Fin L → ℝ)}
    {u : ι → (Fin L → ℝ) → ℝ} {Y : κ → Set (Fin L → ℝ)} {ω : Fin L → ℝ}
    (hU : Convex ℝ (utilityPossibilitySet (PrefEconomy.ofUtility X u Y ω) u))
    {a : Allocation ι κ L} (hpo : (PrefEconomy.ofUtility X u Y ω).IsParetoOptimal a) :
    ∃ lam : ι → ℝ, (∀ i, 0 ≤ lam i) ∧ lam ≠ 0 ∧
      ∀ v ∈ utilityPossibilitySet (PrefEconomy.ofUtility X u Y ω) u,
        ∑ i, lam i * v i ≤ ∑ i, lam i * u i (a.x i) :=
  proposition_16_E_2_ii hU (fun _ hv _ hwv => utilityPossibilitySet_down hv hwv)
    ((proposition_16_E_1 hpo.1).mp hpo)

/-- **Section 16.E** (MWG, p. 560). Every feasible allocation whose utility vector maximizes a
linear social welfare function with weights `λ ≫ 0` on `U` is Pareto optimal. -/
theorem welfareOptimum_isPareto {X : ι → Set (Fin L → ℝ)} {u : ι → (Fin L → ℝ) → ℝ}
    {Y : κ → Set (Fin L → ℝ)} {ω : Fin L → ℝ} {lam : ι → ℝ} (hlam : ∀ i, 0 < lam i)
    {a : Allocation ι κ L} (ha : (PrefEconomy.ofUtility X u Y ω).IsFeasible a)
    (hmax : ∀ v ∈ utilityPossibilitySet (PrefEconomy.ofUtility X u Y ω) u,
      ∑ i, lam i * v i ≤ ∑ i, lam i * u i (a.x i)) :
    (PrefEconomy.ofUtility X u Y ω).IsParetoOptimal a :=
  (proposition_16_E_1 ha).mpr (proposition_16_E_2_i hlam ⟨a, ha, fun _ => le_rfl⟩ hmax)

/-! ## Footnote 12 and Exercise 16.E.1(a): boundary points that are not Pareto optimal -/

/-- The utility functions of the economy of Figure 16.C.1. -/
noncomputable def fig16C1Utilities : Fin 2 → (Fin 2 → ℝ) → ℝ := ![fig16C1u1, fig16C1u2]

/-- **Footnote 12** (MWG, p. 559) and **Exercise 16.E.1(a)** (MWG, p. 576). In the two-consumer,
two-good exchange economy of Figure 16.C.1, the utility vector `(1, 5/2)` of `x*` is achieved by a
feasible allocation (it is in `U'`), lies on the boundary of `U` (it is in `U` but not in its
interior), and `x*` is not Pareto optimal. -/
theorem footnote_12 :
    (fun i => fig16C1Utilities i (fig16C1Eqm.x i)) ∈
        achievedUtilitySet fig16C1Economy fig16C1Utilities ∧
      (fun i => fig16C1Utilities i (fig16C1Eqm.x i)) ∈
        frontier (utilityPossibilitySet fig16C1Economy fig16C1Utilities) ∧
      ¬ fig16C1Economy.IsParetoOptimal fig16C1Eqm := by
  have hpet := figure_16_C_1.1
  have hach : (fun i => fig16C1Utilities i (fig16C1Eqm.x i)) ∈
      achievedUtilitySet fig16C1Economy fig16C1Utilities := ⟨_, hpet.isFeasible, fun _ => rfl⟩
  refine ⟨hach, ⟨subset_closure (achievedUtilitySet_subset _ _ hach), fun hint => ?_⟩,
    figure_16_C_1.2.1⟩
  -- consumer 1's utility never exceeds `1`
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior _ hint
  have hmem : (fun i => fig16C1Utilities i (fig16C1Eqm.x i) + ε / 2) ∈
      utilityPossibilitySet fig16C1Economy fig16C1Utilities := by
    apply interior_subset
    apply hball
    rw [Metric.mem_ball, dist_pi_lt_iff hε]
    intro i
    rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos (half_pos hε)]
    linarith
  obtain ⟨a, -, ha⟩ := hmem
  have h0 := ha 0
  simp only [fig16C1Utilities, fig16C1Eqm, Matrix.cons_val_zero] at h0
  have h1 : fig16C1u1 ![3 / 2, 0] = 1 := by norm_num [fig16C1u1]
  have h2 : fig16C1u1 (a.x 0) ≤ 1 := min_le_right _ _
  rw [h1] at h0
  linarith

/-! ## Figure 16.E.1: a Pareto optimum that maximizes no linear welfare function -/

/-- The utility `u(x) = x²` of the one-good example. -/
def squareUtility : Fin 2 → (Fin 1 → ℝ) → ℝ := fun _ x => x 0 ^ 2

/-- **Figure 16.E.1** (MWG, pp. 559-561). The exchange economy with one good, endowment `1`, two
consumers with `uᵢ(x) = x²`. -/
def fig16E1Economy : PrefEconomy (Fin 2) Unit 1 :=
  PrefEconomy.ofUtility (fun _ => nonnegOrthant 1) squareUtility (fun _ => nonposOrthant 1) ![1]

/-- **Figure 16.E.1** (MWG, p. 561). With a nonconvex utility possibility set, a Pareto optimum
need not maximize any linear social welfare function: in `fig16E1Economy` the equal split
`(1/2, 1/2)` is Pareto optimal (utilities `(1/4, 1/4)`), but for every `λ ≥ 0`, `λ ≠ 0`, one of the
extreme allocations gives a strictly higher `λ·u`. -/
theorem figure_16_E_1 :
    fig16E1Economy.IsParetoOptimal ⟨fun _ => ![1 / 2], fun _ => 0⟩ ∧
      ∀ lam : Fin 2 → ℝ, (∀ i, 0 ≤ lam i) → lam ≠ 0 →
        ∃ v ∈ utilityPossibilitySet fig16E1Economy squareUtility,
          ∑ i, lam i * (1 / 4 : ℝ) < ∑ i, lam i * v i := by
  refine ⟨⟨⟨⟨fun _ l => ?_, fun _ _ => le_rfl⟩, ?_⟩, ?_⟩, fun lam hlam hne => ?_⟩
  · fin_cases l; norm_num
  · funext l; fin_cases l; simp [fig16E1Economy, PrefEconomy.ofUtility]
  · rintro ⟨a', ⟨⟨hx', hy'⟩, hc'⟩, hle, k, hk⟩
    have h0 := congrFun hc' 0
    simp [fig16E1Economy, PrefEconomy.ofUtility, Fin.sum_univ_two] at h0
    have hy := hy' () 0
    have hx0 := hx' 0 0
    have hx1 := hx' 1 0
    have hl0 := hle 0
    have hl1 := hle 1
    simp only [fig16E1Economy, PrefEconomy.ofUtility, utilityPref, squareUtility] at hl0 hl1 hk
    simp only [Matrix.cons_val_zero] at hl0 hl1 hk
    have ha0 : 1 / 2 ≤ a'.x 0 0 := by nlinarith
    have ha1 : 1 / 2 ≤ a'.x 1 0 := by nlinarith
    have e0 : a'.x 0 0 = 1 / 2 := by linarith
    have e1 : a'.x 1 0 = 1 / 2 := by linarith
    apply hk.2
    fin_cases k <;> simp only [utilityPref, squareUtility] <;> simp [e0, e1]
  · have hfeas : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        fig16E1Economy.IsFeasible ⟨![![t], ![1 - t]], fun _ => 0⟩ := by
      intro t ht0 ht1
      refine ⟨⟨fun i l => ?_, fun _ _ => le_rfl⟩, ?_⟩
      · fin_cases i <;> fin_cases l <;> simp <;> linarith
      · funext l; fin_cases l; simp [fig16E1Economy, PrefEconomy.ofUtility]
    have hsum : 0 < lam 0 + lam 1 := by
      rcases (hlam 0).lt_or_eq with h | h
      · linarith [hlam 1]
      rcases (hlam 1).lt_or_eq with h' | h'
      · linarith
      exfalso; apply hne; funext i; fin_cases i <;> simp [← h, ← h']
    rcases le_total (lam 1) (lam 0) with hle | hle
    · refine ⟨_, ⟨_, hfeas 1 zero_le_one le_rfl, fun _ => le_rfl⟩, ?_⟩
      simp [squareUtility, Fin.sum_univ_two]
      nlinarith
    · refine ⟨_, ⟨_, hfeas 0 le_rfl zero_le_one, fun _ => le_rfl⟩, ?_⟩
      simp [squareUtility, Fin.sum_univ_two]
      nlinarith

/-! ## The normative representative consumer (16.E.2) -/

/-- **(16.E.2)** (MWG, p. 561). The utility of the normative representative consumer for weights
`λ`: `u_λ(x̄) = sup {∑ᵢ λᵢ uᵢ(xᵢ) : xᵢ ∈ Xᵢ, ∑ᵢ xᵢ = x̄}`. -/
noncomputable def repUtility (X : ι → Set (Fin L → ℝ)) (u : ι → (Fin L → ℝ) → ℝ)
    (lam : ι → ℝ) (xb : Fin L → ℝ) : ℝ :=
  sSup {s | ∃ x : ι → Fin L → ℝ, (∀ i, x i ∈ X i) ∧ ∑ i, x i = xb ∧
    s = ∑ i, lam i * u i (x i)}

/-- **Section 16.E** (MWG, p. 561). Let `(x*, y*)` be feasible and let `λ` be welfare weights at
which `u(x*)` maximizes `λ·u` on `U` (e.g. from Proposition 16.E.2, `λ ≥ 0`). Then `x*` attains
`u_λ(∑ᵢ x*ᵢ) = ∑ᵢ λᵢ uᵢ(x*ᵢ)`, and `(∑ᵢ x*ᵢ, ∑ⱼ y*ⱼ)` solves the representative consumer's problem
`max u_λ(x̄)` subject to `x̄ = ω̄ + ȳ`, `ȳ ∈ Y = ∑ⱼ Yⱼ`. -/
theorem representative_consumer {X : ι → Set (Fin L → ℝ)} {u : ι → (Fin L → ℝ) → ℝ}
    {Y : κ → Set (Fin L → ℝ)} {ω : Fin L → ℝ} {lam : ι → ℝ} {a : Allocation ι κ L}
    (ha : (PrefEconomy.ofUtility X u Y ω).IsFeasible a)
    (hmax : ∀ v ∈ utilityPossibilitySet (PrefEconomy.ofUtility X u Y ω) u,
      ∑ i, lam i * v i ≤ ∑ i, lam i * u i (a.x i)) :
    repUtility X u lam (∑ i, a.x i) = ∑ i, lam i * u i (a.x i) ∧
      ∀ y : κ → Fin L → ℝ, (∀ j, y j ∈ Y j) →
        (∃ x : ι → Fin L → ℝ, (∀ i, x i ∈ X i) ∧ ∑ i, x i = ω + ∑ j, y j) →
        repUtility X u lam (ω + ∑ j, y j) ≤ repUtility X u lam (∑ i, a.x i) := by
  have hbound : ∀ y : κ → Fin L → ℝ, (∀ j, y j ∈ Y j) → ∀ x : ι → Fin L → ℝ,
      (∀ i, x i ∈ X i) → ∑ i, x i = ω + ∑ j, y j →
      ∑ i, lam i * u i (x i) ≤ ∑ i, lam i * u i (a.x i) := fun y hy x hx hs =>
    hmax _ ⟨⟨x, y⟩, ⟨⟨hx, hy⟩, hs⟩, fun _ => le_rfl⟩
  have hval : repUtility X u lam (∑ i, a.x i) = ∑ i, lam i * u i (a.x i) := by
    apply le_antisymm
    · refine csSup_le ⟨_, a.x, ha.1.1, rfl, rfl⟩ ?_
      rintro s ⟨x, hx, hs, rfl⟩
      exact hbound a.y ha.1.2 x hx (hs.trans ha.2)
    · refine le_csSup ⟨∑ i, lam i * u i (a.x i), ?_⟩ ⟨a.x, ha.1.1, rfl, rfl⟩
      rintro s ⟨x, hx, hs, rfl⟩
      exact hbound a.y ha.1.2 x hx (hs.trans ha.2)
  refine ⟨hval, fun y hy hne => ?_⟩
  rw [hval]
  obtain ⟨x0, hx0, hs0⟩ := hne
  refine csSup_le ⟨_, x0, hx0, hs0, rfl⟩ ?_
  rintro s ⟨x, hx, hs, rfl⟩
  exact hbound y hy x hx hs

end MWG.WelfareTheorems
