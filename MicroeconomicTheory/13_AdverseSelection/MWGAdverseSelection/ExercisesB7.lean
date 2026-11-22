/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGAdverseSelection.ExercisesB
import MWGAdverseSelection.Unraveling

/-!
# Exercise 13.B.7: Pareto-improving interventions

MWG, Section 13.B, Exercise 13.B.7, p. 474, in the setting of `Constrained.lean` (pp. 445-447):
the authority pays `w_e` to the employed and `w_u` to the unemployed, the types in
`Θ(w_e - w_u)` work, the budget is `BudgetOK` and Pareto improvement is `IsParetoImprovement`
relative to the competitive equilibrium with wage `w*`.

* `ReducesEmployment`, `IncreasesEmployment`: the set of types in `[θ̲, θ̄]` employed under the
  intervention is a strict subset (superset) of the equilibrium set `Θ(w*) ∩ [θ̲, θ̄]`.
* `budgetOK_iff`: the budget says exactly `w_u ≤ Π(w_e - w_u)`.
* `exercise_13_B_7_reduce`: a Pareto-improving intervention reducing employment exists iff one of
  the form `(w*, ŵ_u)`, `ŵ_u > 0`, does (no assumption on `r` beyond measurability).
* `exercise_13_B_7_increase`: a Pareto-improving intervention increasing employment exists iff one
  of the form `(ŵ_e, 0)`, `ŵ_e > w*`, does. Departure: this needs the level sets
  `{θ : r(θ) = c}` to be null (true in the model of Section 13.B, `MonoModel.levelNull`).
* `exercise_13_B_7_proposition_13_B_2`: the "simple proof" of Proposition 13.B.2 (in the
  generality of Exercise 13.B.10): at the highest-wage equilibrium an intervention reducing
  employment fails because `E[θ | θ ≤ θ̂] < w*`, one increasing employment fails because firms
  lose money above `w*`, and one keeping employment cannot balance the budget.
* `exercise_13_B_7_instance`: in Example 13.B.1 with `α = 1/4` (`W* = {0, 1}`), at the low
  equilibrium `w* = 0` both sides of `exercise_13_B_7_increase` hold with `ŵ_e = 1`. (An
  instance of `exercise_13_B_7_reduce` is `exercise_13_B_9`.)
-/

namespace MWG.AdverseSelection

open MeasureTheory

/-- **Exercise 13.B.7** (MWG, p. 474). The intervention `(w_e, w_u)` reduces employment relative
to the equilibrium with wage `w*`: the types in `[θ̲, θ̄]` that work under it are a strict subset
of those working in the equilibrium. -/
def ReducesEmployment (θl θh : ℝ) (r : ℝ → ℝ) (ws we wu : ℝ) : Prop :=
  acceptSet r (we - wu) ∩ Set.Icc θl θh ⊂ acceptSet r ws ∩ Set.Icc θl θh

/-- **Exercise 13.B.7** (MWG, p. 474). The intervention `(w_e, w_u)` increases employment relative
to the equilibrium with wage `w*`. -/
def IncreasesEmployment (θl θh : ℝ) (r : ℝ → ℝ) (ws we wu : ℝ) : Prop :=
  acceptSet r ws ∩ Set.Icc θl θh ⊂ acceptSet r (we - wu) ∩ Set.Icc θl θh

/-- **(13.B.8)** (MWG, p. 447). The budget constraint says exactly that `w_u` is at most the
profit of a firm paying `w_e - w_u`. -/
theorem budgetOK_iff {μ : Measure ℝ} {θl θh : ℝ} (hd : TypeDist μ θl θh) {r : ℝ → ℝ}
    (hr : Measurable r) {we wu : ℝ} :
    BudgetOK μ r we wu ↔ wu ≤ firmProfit μ r (we - wu) := by
  have := hd.prob
  rw [firmProfit_eq_setIntegral hr, integral_sub hd.integrable_id.integrableOn
    (integrable_const _).integrableOn, setIntegral_const, smul_eq_mul]
  unfold BudgetOK
  constructor <;> intro hb <;> nlinarith

/-- A reducing intervention leaves home a type that worked in the equilibrium. -/
theorem exB7_reduces_exists {θl θh : ℝ} {r : ℝ → ℝ} {ws we wu : ℝ}
    (h : ReducesEmployment θl θh r ws we wu) :
    ∃ θ ∈ Set.Icc θl θh, we - wu < r θ ∧ r θ ≤ ws := by
  obtain ⟨θ, ⟨hθw, hθI⟩, hθn⟩ := Set.exists_of_ssubset h
  exact ⟨θ, hθI, not_le.1 fun hle => hθn ⟨hle, hθI⟩, hθw⟩

/-- A type that worked in the equilibrium but not under `(w_e, w_u)` makes it reducing. -/
theorem exB7_reduces_of {θl θh : ℝ} {r : ℝ → ℝ} {ws we wu θ : ℝ} (hθ : θ ∈ Set.Icc θl θh)
    (h1 : we - wu < r θ) (h2 : r θ ≤ ws) : ReducesEmployment θl θh r ws we wu :=
  ssubset_of_subset_not_subset (fun _ hθ' => ⟨le_trans hθ'.1 (h1.trans_le h2).le, hθ'.2⟩)
    fun hsub => absurd (hsub ⟨h2, hθ⟩).1 (not_le.2 h1)

/-- An increasing intervention employs a type that stayed home in the equilibrium. -/
theorem exB7_increases_exists {θl θh : ℝ} {r : ℝ → ℝ} {ws we wu : ℝ}
    (h : IncreasesEmployment θl θh r ws we wu) :
    ∃ θ ∈ Set.Icc θl θh, ws < r θ ∧ r θ ≤ we - wu := by
  obtain ⟨θ, ⟨hθw, hθI⟩, hθn⟩ := Set.exists_of_ssubset h
  exact ⟨θ, hθI, not_le.1 fun hle => hθn ⟨hle, hθI⟩, hθw⟩

/-- A type that works under `(w_e, w_u)` but not in the equilibrium makes it increasing. -/
theorem exB7_increases_of {θl θh : ℝ} {r : ℝ → ℝ} {ws we wu θ : ℝ} (hθ : θ ∈ Set.Icc θl θh)
    (h1 : ws < r θ) (h2 : r θ ≤ we - wu) : IncreasesEmployment θl θh r ws we wu :=
  ssubset_of_subset_not_subset (fun _ hθ' => ⟨le_trans hθ'.1 (h1.trans_le h2).le, hθ'.2⟩)
    fun hsub => absurd (hsub ⟨h2, hθ⟩).1 (not_le.2 h1)

/-- A worker employed under `(w_e, w_u)` gets `w_e`. -/
theorem exB7_pay_emp {we wu x : ℝ} (h : x ≤ we - wu) : max we (wu + x) = we :=
  max_eq_left (by linarith)

/-- A worker at home under `(w_e, w_u)` gets `w_u + r(θ)`. -/
theorem exB7_pay_unemp {we wu x : ℝ} (h : we - wu < x) : max we (wu + x) = wu + x :=
  max_eq_right (by linarith)

/-- If no type in `[θ̲, θ̄]` accepts `w`, a firm paying `w` earns nothing. -/
theorem exB7_profit_of_empty {μ : Measure ℝ} {θl θh : ℝ} (hd : TypeDist μ θl θh) {r : ℝ → ℝ}
    (hr : Measurable r) {w : ℝ} (h : ∀ θ ∈ Set.Icc θl θh, w < r θ) : firmProfit μ r w = 0 := by
  refine firmProfit_of_null hr ?_
  rw [← measure_acceptSet_inter hd]
  convert measure_empty (μ := μ)
  exact Set.eq_empty_iff_forall_notMem.2 fun θ hθ => absurd hθ.1 (not_le.2 (h θ hθ.2))

/-- **Exercise 13.B.7** (MWG, p. 474). There is a budget-feasible Pareto-improving intervention
that reduces employment iff there is one of the form `(w*, ŵ_u)` with `ŵ_u > 0`. (Only
measurability of `r` is used; `w*` need not even be an equilibrium wage.) -/
theorem exercise_13_B_7_reduce {μ : Measure ℝ} {θl θh : ℝ} (hd : TypeDist μ θl θh) {r : ℝ → ℝ}
    (hr : Measurable r) (ws : ℝ) :
    (∃ we wu, BudgetOK μ r we wu ∧ IsParetoImprovement θl θh r ws we wu ∧
      ReducesEmployment θl θh r ws we wu) ↔
    ∃ wu', 0 < wu' ∧ BudgetOK μ r ws wu' ∧ IsParetoImprovement θl θh r ws ws wu' ∧
      ReducesEmployment θl θh r ws ws wu' := by
  constructor
  · rintro ⟨we, wu, hb, ⟨hall, θ1, hθ1, hstrict⟩, hred⟩
    obtain ⟨θ0, hθ0, h01, h02⟩ := exB7_reduces_exists hred
    have hwu := (budgetOK_iff hd hr).1 hb
    have hdws : we - wu < ws := h01.trans_le h02
    have hwe : ws ≤ we := by
      by_cases hex : ∃ θ ∈ Set.Icc θl θh, r θ ≤ we - wu
      · obtain ⟨θ, hθ, hle⟩ := hex
        have := hall θ hθ
        rw [exB7_pay_emp hle] at this
        exact (le_max_left _ _).trans this
      · push Not at hex
        rw [exB7_profit_of_empty hd hr hex] at hwu
        have := hstrict
        rw [exB7_pay_unemp (hex θ1 hθ1)] at this
        linarith [le_max_right ws (r θ1)]
    refine ⟨ws - (we - wu), by linarith, ?_, ⟨fun θ _ => ?_, θ0, hθ0, ?_⟩, ?_⟩
    · rw [budgetOK_iff hd hr, sub_sub_cancel]
      linarith
    · exact max_le_max le_rfl (by linarith)
    · rw [max_eq_left h02]
      exact lt_max_of_lt_right (by linarith)
    · unfold ReducesEmployment
      rw [sub_sub_cancel]
      exact hred
  · rintro ⟨wu', -, hb, hpi, hred⟩
    exact ⟨ws, wu', hb, hpi, hred⟩

/-- In the model of Section 13.B (`MonoModel`), the level sets of `r` are null. -/
theorem MonoModel.levelNull {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ} (h : MonoModel μ θl θh r)
    (c : ℝ) : μ {θ | r θ = c} = 0 := by
  rw [← measure_acceptSet_inter h.dist]
  by_cases hex : ∃ θ0 ∈ Set.Icc θl θh, r θ0 = c
  · obtain ⟨θ0, hθ0, hc⟩ := hex
    refine measure_mono_null (t := {θ0}) (fun θ hθ => ?_) (h.dens.noAtom θ0)
    exact h.mono.injOn hθ.2 hθ0 (hθ.1.trans hc.symm)
  · push Not at hex
    convert measure_empty (μ := μ)
    exact Set.eq_empty_iff_forall_notMem.2 fun θ hθ => hex θ hθ.2 hθ.1

/-- **Exercise 13.B.7** (MWG, p. 474). There is a budget-feasible Pareto-improving intervention
that increases employment iff there is one of the form `(ŵ_e, 0)` with `ŵ_e > w*`. We assume
that the level sets `{θ : r(θ) = c}` are null (true in the model of Section 13.B,
`MonoModel.levelNull`). -/
theorem exercise_13_B_7_increase {μ : Measure ℝ} {θl θh : ℝ} (hd : TypeDist μ θl θh)
    {r : ℝ → ℝ} (hr : Measurable r) (hlev : ∀ c, μ {θ | r θ = c} = 0) (ws : ℝ) :
    (∃ we wu, BudgetOK μ r we wu ∧ IsParetoImprovement θl θh r ws we wu ∧
      IncreasesEmployment θl θh r ws we wu) ↔
    ∃ we', ws < we' ∧ BudgetOK μ r we' 0 ∧ IsParetoImprovement θl θh r ws we' 0 ∧
      IncreasesEmployment θl θh r ws we' 0 := by
  have := hd.prob
  constructor
  · rintro ⟨we, wu, hb, ⟨hall, θ1, hθ1, hstrict⟩, hinc⟩
    obtain ⟨θ0, hθ0, h01, h02⟩ := exB7_increases_exists hinc
    have hwu := (budgetOK_iff hd hr).1 hb
    have hwsd : ws < we - wu := h01.trans_le h02
    by_cases hA : ∃ θ ∈ Set.Icc θl θh, we - wu < r θ
    · obtain ⟨θ2, hθ2, hd2⟩ := hA
      have hwu0 : 0 ≤ wu := by
        have := hall θ2 hθ2
        rw [exB7_pay_unemp hd2, max_eq_right (hwsd.trans hd2).le] at this
        linarith
      rcases eq_or_lt_of_le hwu0 with h0 | hpos
      · subst h0
        exact ⟨we, by linarith, hb, ⟨hall, θ1, hθ1, hstrict⟩, hinc⟩
      · -- some type in `[θ̲, θ̄]` has `r(θ) < w_e - w_u`
        have hP : 0 < firmProfit μ r (we - wu) := hpos.trans_le hwu
        have hmeas : 0 < μ (acceptSet r (we - wu)) := by
          by_contra h0
          rw [not_lt, nonpos_iff_eq_zero] at h0
          rw [firmProfit_of_null hr h0] at hP
          exact lt_irrefl _ hP
        have hex : ∃ θ ∈ Set.Icc θl θh, r θ < we - wu := by
          by_contra hno
          push Not at hno
          refine hmeas.ne' (measure_mono_null (t := {θ | r θ = we - wu} ∪ (Set.Icc θl θh)ᶜ)
            (fun θ hθ => ?_) (measure_union_null (hlev _) hd.supp))
          by_cases hθI : θ ∈ Set.Icc θl θh
          · exact Or.inl (le_antisymm hθ (hno θ hθI))
          · exact Or.inr hθI
        obtain ⟨θ3, hθ3, hr3⟩ := hex
        refine ⟨we - wu, hwsd, ?_, ⟨fun θ _ => ?_, θ3, hθ3, ?_⟩, ?_⟩
        · rw [budgetOK_iff hd hr, sub_zero]; exact hP.le
        · rw [zero_add]; exact max_le_max hwsd.le le_rfl
        · rw [zero_add, max_eq_left hr3.le]; exact max_lt hwsd hr3
        · exact exB7_increases_of hθ0 h01 (by rw [sub_zero]; exact h02)
    · -- everybody works under the intervention
      push Not at hA
      have hfull : Set.Icc θl θh ⊆ acceptSet r (we - wu) := fun θ hθ => hA θ hθ
      rw [firmProfit_of_full hd hr hfull] at hwu
      have hpay : ∀ θ ∈ Set.Icc θl θh, max we (wu + r θ) = we := fun θ hθ =>
        exB7_pay_emp (hA θ hθ)
      have hle : ∀ θ ∈ Set.Icc θl θh, r θ ≤ we := fun θ hθ =>
        (le_max_right ws (r θ)).trans ((hall θ hθ).trans (hpay θ hθ).le)
      have hwswe : ws < we := by
        have := hstrict; rw [hpay θ1 hθ1] at this; exact (le_max_left _ _).trans_lt this
      have hfull' : Set.Icc θl θh ⊆ acceptSet r (we - 0) := fun θ hθ => by
        rw [sub_zero]; exact hle θ hθ
      refine ⟨we, hwswe, ?_, ⟨fun θ hθ => ?_, θ1, hθ1, ?_⟩, ?_⟩
      · rw [budgetOK_iff hd hr, firmProfit_of_full hd hr hfull']; linarith
      · rw [zero_add, max_eq_left (hle θ hθ)]; exact (hall θ hθ).trans (hpay θ hθ).le
      · rw [zero_add, max_eq_left (hle θ1 hθ1)]
        exact hstrict.trans_le (hpay θ1 hθ1).le
      · exact exB7_increases_of hθ0 h01 (by rw [sub_zero]; exact hle θ0 hθ0)
  · rintro ⟨we', -, hb, hpi, hinc⟩
    exact ⟨we', 0, hb, hpi, hinc⟩

/-- Under `(w_e, w_u)` with the same employed types as at `w`, the profit at `w_e - w_u` is
`Π(w) + F(Θ(w)) (w - (w_e - w_u))`. -/
theorem exB7_profit_congr {μ : Measure ℝ} {θl θh : ℝ} (hd : TypeDist μ θl θh) {r : ℝ → ℝ}
    (hr : Measurable r) {d w : ℝ}
    (hE : acceptSet r d ∩ Set.Icc θl θh = acceptSet r w ∩ Set.Icc θl θh) :
    firmProfit μ r d = firmProfit μ r w + μ.real (acceptSet r w) * (w - d) := by
  have := hd.prob
  rw [firmProfit_eq_setIntegral hr, firmProfit_eq_setIntegral hr,
    setIntegral_congr_set (exB_ae_eq_of_inter hd hE)]
  have h : ∫ θ in acceptSet r w, (θ - d) ∂μ =
      ∫ θ in acceptSet r w, ((θ - w) + (w - d)) ∂μ := by
    congr 1; funext θ; ring
  rw [h, integral_add (f := fun θ => θ - w) (g := fun _ => w - d)
    (hd.integrable_id.sub (integrable_const w)).integrableOn
    (integrable_const _).integrableOn, setIntegral_const, smul_eq_mul]

/-- In the `MonoModel`, if some type does not accept `c`, a positive mass does not. -/
theorem MonoModel.measureReal_acceptSet_lt_one {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ}
    (h : MonoModel μ θl θh r) {c θ : ℝ} (hθ : θ ∈ Set.Icc θl θh) (hc : c < r θ) :
    μ.real (acceptSet r c) < 1 := by
  have hd := h.dist
  have := hd.prob
  have hh : θh ∈ Set.Icc θl θh := ⟨hd.lt.le, le_rfl⟩
  have hch : c < r θh := hc.trans_le (h.mono.monotoneOn hθ hh hθ.2)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1
    ((h.cont θh hh).eventually (lt_mem_nhds hch))
  set a := max θl (θh - ε / 2)
  have ha : a < θh := max_lt hd.lt (by linarith)
  have hpos : 0 < μ (Set.Icc a θh) := h.dens.pos a θh (le_max_left _ _) ha le_rfl
  have hsub : Set.Icc a θh ⊆ (acceptSet r c)ᶜ := fun y hy hacc => by
    have hyI : y ∈ Set.Icc θl θh := ⟨(le_max_left _ _).trans hy.1, hy.2⟩
    have hdist : Dist.dist y θh < ε := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [hy.1, hy.2, le_max_right θl (θh - ε / 2)]
    have hlt : c < r y := hball ⟨Metric.mem_ball.2 hdist, hyI⟩
    exact absurd (hacc : r y ≤ c) (not_le.2 hlt)
  have hlt : μ (acceptSet r c) < 1 := by
    have h1 := prob_compl_eq_one_sub (μ := μ) (measurableSet_acceptSet h.meas c)
    have h2 : 0 < μ (acceptSet r c)ᶜ := hpos.trans_le (measure_mono hsub)
    rw [h1] at h2
    exact tsub_pos_iff_lt.1 h2
  rw [Measure.real]
  exact (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.one_ne_top).2 hlt |>.trans_eq
    ENNReal.toReal_one

/-- **Exercise 13.B.7** (MWG, p. 474): the "simple proof" of **Proposition 13.B.2**, in the
generality of Exercise 13.B.10 (`r(θ) ≤ θ` not needed). At the highest-wage competitive
equilibrium no budget-feasible intervention is a Pareto improvement: by
`exercise_13_B_7_reduce` a reducing one would give one of the form `(w*, ŵ_u)`, impossible since
`E[θ | θ ≤ θ̂] < w*`; by `exercise_13_B_7_increase` an increasing one would give one of the
form `(ŵ_e, 0)`, impossible since firms lose money above `w*`; and one keeping the employed
set cannot pay anybody more. -/
theorem exercise_13_B_7_proposition_13_B_2 {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ}
    (h : MonoModel μ θl θh r) {ws : ℝ} (hmax : IsGreatest (eqWages μ θl θh r) ws) :
    IsConstrainedPO μ θl θh r ws := by
  have hd := h.dist
  have := hd.prob
  have hl : θl ∈ Set.Icc θl θh := ⟨le_rfl, hd.lt.le⟩
  have hh : θh ∈ Set.Icc θl θh := ⟨hd.lt.le, le_rfl⟩
  intro we wu hb hpi
  have hP0 : firmProfit μ r ws = 0 := by
    rcases eq_zero_or_pos (μ (acceptSet r ws)) with h0 | hpos
    · exact firmProfit_of_null h.meas h0
    · exact (mem_eqWages_iff_profit hd h.meas hpos).1 hmax.1
  by_cases hred : ReducesEmployment θl θh r ws we wu
  · obtain ⟨wu', hwu', hb', -, hred'⟩ :=
      (exercise_13_B_7_reduce hd h.meas ws).1 ⟨we, wu, hb, hpi, hred⟩
    obtain ⟨θ0, hθ0, h1, h2⟩ := exB7_reduces_exists hred'
    have hP := (budgetOK_iff hd h.meas).1 hb'
    by_cases hdl : ws - wu' < r θl
    · rw [firmProfit_of_lt hd h.mono.monotoneOn h.meas hdl] at hP
      linarith
    · have := h.profit_add_lt hmax.1 (not_lt.1 hdl) (by linarith)
        (h1.trans_le (h.mono.monotoneOn hθ0 hh hθ0.2))
      linarith
  by_cases hinc : IncreasesEmployment θl θh r ws we wu
  · obtain ⟨we', hwe', hb', ⟨-, θ1, hθ1, hs⟩, -⟩ :=
      (exercise_13_B_7_increase hd h.meas h.levelNull ws).1 ⟨we, wu, hb, hpi, hinc⟩
    have hP := (budgetOK_iff hd h.meas).1 hb'
    rw [sub_zero] at hP
    rw [zero_add] at hs
    have hrl : r θl < we' := by
      by_contra hc
      rw [not_lt] at hc
      rw [max_eq_right (hc.trans (h.mono.monotoneOn hl hθ1 hθ1.1))] at hs
      exact absurd hs (not_lt.2 (le_max_right _ _))
    have hneg := h.firmProfit_neg_of_gt_max hmax hwe'
      (measure_acceptSet_pos hd h.dens h.cont hrl)
    linarith
  -- the employed set is unchanged
  obtain ⟨hall, θ1, hθ1, hstrict⟩ := hpi
  have hE : acceptSet r (we - wu) ∩ Set.Icc θl θh = acceptSet r ws ∩ Set.Icc θl θh := by
    rcases le_or_gt (we - wu) ws with hle | hgt
    · have hsub : acceptSet r (we - wu) ∩ Set.Icc θl θh ⊆ acceptSet r ws ∩ Set.Icc θl θh :=
        fun θ hθ => ⟨le_trans hθ.1 hle, hθ.2⟩
      rcases hsub.eq_or_ssubset with heq | hss
      · exact heq
      · exact absurd hss hred
    · have hsub : acceptSet r ws ∩ Set.Icc θl θh ⊆ acceptSet r (we - wu) ∩ Set.Icc θl θh :=
        fun θ hθ => ⟨le_trans hθ.1 hgt.le, hθ.2⟩
      rcases hsub.eq_or_ssubset with heq | hss
      · exact heq.symm
      · exact absurd hss hinc
  have hwu := (budgetOK_iff hd h.meas).1 hb
  rw [exB7_profit_congr hd h.meas hE, hP0, zero_add] at hwu
  set p := μ.real (acceptSet r ws) with hp
  have hp0 : 0 ≤ p := measureReal_nonneg
  have hp1 : p ≤ 1 := by
    rw [hp, Measure.real]
    exact (ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one).trans_eq ENNReal.toReal_one
  -- employed types (in both) get `w_e`, the others `w_u + r(θ)`
  have hemp : ∀ θ ∈ Set.Icc θl θh, r θ ≤ ws → r θ ≤ we - wu := fun θ hθ hle => by
    have hm : θ ∈ acceptSet r (we - wu) ∩ Set.Icc θl θh := by rw [hE]; exact ⟨hle, hθ⟩
    exact hm.1
  have hun : ∀ θ ∈ Set.Icc θl θh, ws < r θ → we - wu < r θ := fun θ hθ hlt => by
    refine not_le.1 fun hle => ?_
    have hm : θ ∈ acceptSet r ws ∩ Set.Icc θl θh := by rw [← hE]; exact ⟨hle, hθ⟩
    exact absurd (hm.1 : r θ ≤ ws) (not_le.2 hlt)
  have hwe : ∀ θ ∈ Set.Icc θl θh, r θ ≤ ws → ws ≤ we := fun θ hθ hle => by
    have := hall θ hθ
    rw [exB7_pay_emp (hemp θ hθ hle), max_eq_left hle] at this
    exact this
  have hwu0 : ∀ θ ∈ Set.Icc θl θh, ws < r θ → 0 ≤ wu := fun θ hθ hlt => by
    have := hall θ hθ
    rw [exB7_pay_unemp (hun θ hθ hlt), max_eq_right hlt.le] at this
    linarith
  have hst : (r θ1 ≤ ws ∧ ws < we) ∨ (ws < r θ1 ∧ 0 < wu) := by
    rcases le_or_gt (r θ1) ws with hle | hlt
    · have := hstrict
      rw [exB7_pay_emp (hemp θ1 hθ1 hle), max_eq_left hle] at this
      exact Or.inl ⟨hle, this⟩
    · have := hstrict
      rw [exB7_pay_unemp (hun θ1 hθ1 hlt), max_eq_right hlt.le] at this
      exact Or.inr ⟨hlt, by linarith⟩
  by_cases hU : ∃ θ ∈ Set.Icc θl θh, ws < r θ
  · obtain ⟨θu, hθu, hu⟩ := hU
    have hwupos := hwu0 θu hθu hu
    have hplt : p < 1 := h.measureReal_acceptSet_lt_one hθu hu
    by_cases hEm : ∃ θ ∈ Set.Icc θl θh, r θ ≤ ws
    · obtain ⟨θe, hθe, he⟩ := hEm
      have hwege := hwe θe hθe he
      have hwu_zero : wu = 0 := by nlinarith
      rcases hst with ⟨hle1, hlt1⟩ | ⟨-, hlt1⟩
      · -- then `p = 0`, so nobody works at `w_e - w_u > w*`: impossible
        have hpz : p = 0 := by nlinarith
        have hgt : r θl < we - wu := by
          rw [hwu_zero, sub_zero]
          exact ((h.mono.monotoneOn hl hθ1 hθ1.1).trans hle1).trans_lt hlt1
        have hposd := measure_acceptSet_pos hd h.dens h.cont hgt
        have hmeq : μ (acceptSet r (we - wu)) = μ (acceptSet r ws) :=
          measure_congr (exB_ae_eq_of_inter hd hE)
        have : 0 < p := by
          rw [hp, Measure.real, ← hmeq]
          exact ENNReal.toReal_pos hposd.ne' (measure_ne_top _ _)
        linarith
      · linarith
    · push Not at hEm
      have hpz : p = 0 := by
        rw [hp, Measure.real, ← measure_acceptSet_inter hd]
        convert ENNReal.toReal_zero
        convert measure_empty (μ := μ)
        exact Set.eq_empty_iff_forall_notMem.2 fun θ hθ => absurd hθ.1 (not_le.2 (hEm θ hθ.2))
      rcases hst with ⟨hle1, -⟩ | ⟨-, hlt1⟩
      · exact absurd hle1 (not_le.2 (hEm θ1 hθ1))
      · rw [hpz] at hwu; linarith
  · push Not at hU
    have hpo : p = 1 := by
      have hI1 : μ (Set.Icc θl θh) = 1 := (prob_compl_eq_zero_iff measurableSet_Icc).1 hd.supp
      rw [hp, Measure.real, ← measure_acceptSet_inter hd,
        Set.inter_eq_right.2 (show Set.Icc θl θh ⊆ acceptSet r ws from fun θ hθ => hU θ hθ),
        hI1, ENNReal.toReal_one]
    rcases hst with ⟨-, hlt1⟩ | ⟨hlt1, -⟩
    · rw [hpo] at hwu; linarith
    · exact absurd hlt1 (not_lt.2 (hU θ1 hθ1))

/-- **Exercise 13.B.7**, instance (MWG, pp. 442, 474). Example 13.B.1 with `α = 1/4`: at the
dominated equilibrium `w* = 0` the intervention `(1, 0)` increases employment and is a
budget-feasible Pareto improvement, so both sides of `exercise_13_B_7_increase` hold. -/
theorem exercise_13_B_7_instance :
    (∃ we wu, BudgetOK (unifMeas 0 2) (akerlofR (1 / 4)) we wu ∧
      IsParetoImprovement 0 2 (akerlofR (1 / 4)) 0 we wu ∧
      IncreasesEmployment 0 2 (akerlofR (1 / 4)) 0 we wu) ∧
    ∃ we', 0 < we' ∧ BudgetOK (unifMeas 0 2) (akerlofR (1 / 4)) we' 0 ∧
      IsParetoImprovement 0 2 (akerlofR (1 / 4)) 0 we' 0 ∧
      IncreasesEmployment 0 2 (akerlofR (1 / 4)) 0 we' 0 := by
  have hR := akerlof_regular (α := 1 / 4) (by norm_num) (by norm_num)
  have hW := example_13_B_1_lowα (α := 1 / 4) (by norm_num) (by norm_num)
  have h1 : (1 : ℝ) ∈ eqWages (unifMeas 0 2) 0 2 (akerlofR (1 / 4)) := by
    rw [hW]; exact Or.inr rfl
  have hpos : 0 < unifMeas 0 2 (acceptSet (akerlofR (1 / 4)) 1) :=
    measure_acceptSet_pos hR.dist hR.dens hR.cont (by simp only [akerlofR]; norm_num)
  have hrhs : ∃ we', 0 < we' ∧ BudgetOK (unifMeas 0 2) (akerlofR (1 / 4)) we' 0 ∧
      IsParetoImprovement 0 2 (akerlofR (1 / 4)) 0 we' 0 ∧
      IncreasesEmployment 0 2 (akerlofR (1 / 4)) 0 we' 0 := by
    refine ⟨1, one_pos, (highest_wage_implementable hR.dist hR.meas h1 hpos).1,
      ⟨fun θ _ => max_le_max zero_le_one (by rw [zero_add]), 0, ⟨le_rfl, zero_le_two⟩, ?_⟩,
      exB7_increases_of (θ := 1) ⟨zero_le_one, one_le_two⟩ (by simp only [akerlofR]; norm_num)
        (by simp only [akerlofR]; norm_num)⟩
    simp only [akerlofR]; norm_num
  refine ⟨?_, hrhs⟩
  obtain ⟨we', -, hb, hpi, hinc⟩ := hrhs
  exact ⟨we', 0, hb, hpi, hinc⟩

end MWG.AdverseSelection
