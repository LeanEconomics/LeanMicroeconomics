/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGAdverseSelection.ExercisesB7

/-!
# Exercise 13.B.8: interventions based on observable purchases of `x`

MWG, Section 13.B, Exercise 13.B.8, p. 474. Home production uses a good `x`; a type-`θ` worker at
home buys `x(θ)`, which the authority observes. An intervention is an employment wage `w_e` and
an unemployment benefit `b(x)` depending on the observed purchase: type `θ` works iff
`r(θ) + b(x(θ)) ≤ w_e` and then gets `w_e`, otherwise `r(θ) + b(x(θ))`. The authority runs the
firms: its net revenue from type `θ` is `θ - w_e` if employed and `-b(x(θ))` otherwise
(`xNetRev`), and its budget (`XBudgetOK`) requires this to be integrable with nonnegative mean.
`IsXParetoImprovement` asks that no type in `[θ̲, θ̄]` loses and that a set of types of positive
probability gains: since `x` can single out one type, a gain for a null set of types costs
nothing and would make the notion trivial.

* `xBudgetOK_const_iff`: a constant benefit `b ≡ w_u` is the scheme `(w_e, w_u)` of
  `Constrained.lean`.
* Correction, `exercise_13_B_8_false`: in the model of Section 13.B (`RegularModel`: `r` strictly
  increasing and continuous, `r(θ) ≤ θ`, positive density), at the highest-wage equilibrium NO
  intervention of this kind (for any observable `x` and any benefit schedule `b`) is a Pareto
  improvement. So the printed claim is false in that model.
* `exercise_13_B_8`: what is true. If `x` is injective on `[θ̲, θ̄]` (e.g. strictly increasing)
  and, at an equilibrium with wage `w*` (for instance the highest-wage one), a positive mass of
  employed types is more productive at home (`r(θ) > θ`, the setting of Exercise 13.B.10), the
  benefit `b(x(θ)) = w* - θ` for exactly those types is a budget-neutral Pareto improvement.
  `exercise_13_B_8_instance`: here the highest-wage equilibrium is a constrained Pareto optimum
  for `(w_e, w_u)` schemes (Exercise 13.B.10), yet observing `x` allows a Pareto improvement.
* `exercise_13_B_8_const_x`: with `x` constant (weakly increasing is not enough) no such
  improvement exists at the highest-wage equilibrium.
-/

namespace MWG.AdverseSelection

open MeasureTheory

/-- **Exercise 13.B.8** (MWG, p. 474). The authority's net revenue from a type-`θ` worker under
the intervention `(w_e, b)`: `θ - w_e` if she works, `-b(x(θ))` if she stays home. -/
noncomputable def xNetRev (r x : ℝ → ℝ) (we : ℝ) (b : ℝ → ℝ) (θ : ℝ) : ℝ :=
  if r θ + b (x θ) ≤ we then θ - we else -b (x θ)

/-- **Exercise 13.B.8** (MWG, p. 474). The budget of the intervention `(w_e, b)`: the net
revenue is integrable and its mean is nonnegative. -/
def XBudgetOK (μ : Measure ℝ) (r x : ℝ → ℝ) (we : ℝ) (b : ℝ → ℝ) : Prop :=
  Integrable (xNetRev r x we b) μ ∧ 0 ≤ ∫ θ, xNetRev r x we b θ ∂μ

/-- **Exercise 13.B.8** (MWG, p. 474). The intervention `(w_e, b)` Pareto improves on the
competitive equilibrium with wage `w*`: no type in `[θ̲, θ̄]` is worse off and a set of types of
positive probability is strictly better off. -/
def IsXParetoImprovement (μ : Measure ℝ) (θl θh : ℝ) (r x : ℝ → ℝ) (ws we : ℝ)
    (b : ℝ → ℝ) : Prop :=
  (∀ θ ∈ Set.Icc θl θh, max ws (r θ) ≤ max we (r θ + b (x θ))) ∧
    0 < μ {θ | max ws (r θ) < max we (r θ + b (x θ))}

/-- With a constant benefit `w_u` the net revenue is the profit integrand at `w_e - w_u`
minus `w_u`. -/
theorem xNetRev_const (r x : ℝ → ℝ) (we wu : ℝ) :
    xNetRev r x we (fun _ => wu) = fun θ =>
      (acceptSet r (we - wu)).indicator (fun θ => θ - (we - wu)) θ - wu := by
  funext θ
  unfold xNetRev
  by_cases hθ : r θ ≤ we - wu
  · rw [Set.indicator_of_mem (show θ ∈ acceptSet r (we - wu) from hθ)]
    split_ifs with h1
    · ring
    · exact absurd (by linarith : r θ + wu ≤ we) h1
  · rw [Set.indicator_of_notMem (show θ ∉ acceptSet r (we - wu) from hθ)]
    split_ifs with h1
    · exact absurd (by linarith : r θ ≤ we - wu) hθ
    · ring

/-- **Exercise 13.B.8** (MWG, p. 474). A constant benefit `b ≡ w_u` is the scheme `(w_e, w_u)` of
p. 446: the budgets coincide. -/
theorem xBudgetOK_const_iff {μ : Measure ℝ} {θl θh : ℝ} (hd : TypeDist μ θl θh) {r : ℝ → ℝ}
    (hr : Measurable r) (x : ℝ → ℝ) (we wu : ℝ) :
    XBudgetOK μ r x we (fun _ => wu) ↔ BudgetOK μ r we wu := by
  have := hd.prob
  have hi1 : Integrable ((acceptSet r (we - wu)).indicator (fun θ => θ - (we - wu))) μ :=
    (hd.integrable_id.sub (integrable_const _)).indicator (measurableSet_acceptSet hr _)
  have hint : Integrable (fun θ =>
      (acceptSet r (we - wu)).indicator (fun θ => θ - (we - wu)) θ - wu) μ :=
    hi1.sub (integrable_const wu)
  have hI : ∫ θ, ((acceptSet r (we - wu)).indicator (fun θ => θ - (we - wu)) θ - wu) ∂μ =
      firmProfit μ r (we - wu) - wu := by
    rw [integral_sub hi1 (integrable_const wu), integral_const, smul_eq_mul, probReal_univ,
      one_mul]
    rfl
  rw [XBudgetOK, xNetRev_const, budgetOK_iff hd hr]
  beta_reduce
  rw [hI]
  exact ⟨fun h => by linarith [h.2], fun h => ⟨hint, by linarith⟩⟩

/-- If `f ≤ g` almost everywhere and `f < g` on a set of positive measure, `∫ f < ∫ g`. -/
theorem exB8_integral_lt {μ : Measure ℝ} {f g : ℝ → ℝ} (hf : Integrable f μ)
    (hg : Integrable g μ) (hle : ∀ᵐ θ ∂μ, f θ ≤ g θ) (hlt : 0 < μ {θ | f θ < g θ}) :
    ∫ θ, f θ ∂μ < ∫ θ, g θ ∂μ := by
  rw [← sub_pos, ← integral_sub hg hf]
  refine (integral_pos_iff_support_of_nonneg_ae (f := fun θ => g θ - f θ)
    (hle.mono fun θ h => sub_nonneg.2 h) (hg.sub hf)).2
    (hlt.trans_le (measure_mono fun θ hθ => ?_))
  exact sub_ne_zero.2 (ne_of_gt (hθ : f θ < g θ))

/-- **Exercise 13.B.8, correction** (MWG, p. 474). In the adverse selection model of Section 13.B
(positive density, `r` strictly increasing and continuous, `r(θ) ≤ θ`), at the highest-wage
competitive equilibrium no intervention `(w_e, b)` with a benefit depending on observed purchases
`x(θ)` is a budget-feasible Pareto improvement, whatever the function `x` (increasing or not)
and the schedule `b`. The printed claim is therefore false in this model. -/
theorem exercise_13_B_8_false {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ}
    (h : RegularModel μ θl θh r) {ws : ℝ} (hmax : IsGreatest (eqWages μ θl θh r) ws)
    (x b : ℝ → ℝ) (we : ℝ) :
    ¬ (XBudgetOK μ r x we b ∧ IsXParetoImprovement μ θl θh r x ws we b) := by
  rintro ⟨⟨hint, hbud⟩, hall, hS⟩
  have hd := h.dist
  have := hd.prob
  set S := {θ | max ws (r θ) < max we (r θ + b (x θ))} with hSdef
  have hSI : 0 < μ (S ∩ Set.Icc θl θh) := by rwa [measure_acceptSet_inter hd]
  rcases le_or_gt we ws with hwe | hwe
  · -- `w_e ≤ w*`: the net revenue is at most the equilibrium profit integrand
    have hP0 : firmProfit μ r ws = 0 := by
      rcases eq_zero_or_pos (μ (acceptSet r ws)) with h0 | hpos
      · exact firmProfit_of_null h.meas h0
      · exact (mem_eqWages_iff_profit hd h.meas hpos).1 hmax.1
    set g := (acceptSet r ws).indicator (fun θ => θ - ws) with hgdef
    have hg : Integrable g μ :=
      (hd.integrable_id.sub (integrable_const ws)).indicator (measurableSet_acceptSet h.meas ws)
    have hpt : ∀ θ ∈ Set.Icc θl θh,
        xNetRev r x we b θ ≤ g θ ∧ (θ ∈ S → xNetRev r x we b θ < g θ) := by
      intro θ hθ
      have hP := hall θ hθ
      unfold xNetRev
      split_ifs with hemp
      · rw [max_eq_left hemp] at hP
        have hrθ : r θ ≤ ws := (le_max_right _ _).trans (hP.trans hwe)
        have hgθ : g θ = θ - ws := Set.indicator_of_mem (show θ ∈ acceptSet r ws from hrθ) _
        refine ⟨by rw [hgθ]; linarith [(le_max_left ws (r θ)).trans hP], fun hθS => ?_⟩
        have hs : max ws (r θ) < max we (r θ + b (x θ)) := hθS
        rw [max_eq_left hemp] at hs
        linarith [le_max_left ws (r θ)]
      · rw [not_le] at hemp
        rw [max_eq_right hemp.le] at hP
        by_cases hacc : r θ ≤ ws
        · have hgθ : g θ = θ - ws := Set.indicator_of_mem (show θ ∈ acceptSet r ws from hacc) _
          rw [max_eq_left hacc] at hP
          have hrle := h.le θ hθ
          refine ⟨by rw [hgθ]; linarith, fun hθS => ?_⟩
          have hs : max ws (r θ) < max we (r θ + b (x θ)) := hθS
          rw [max_eq_right hemp.le, max_eq_left hacc] at hs
          rw [hgθ]; linarith
        · rw [not_le] at hacc
          have hgθ : g θ = 0 :=
            Set.indicator_of_notMem (show θ ∉ acceptSet r ws from not_le.2 hacc) _
          rw [max_eq_right hacc.le] at hP
          refine ⟨by rw [hgθ]; linarith, fun hθS => ?_⟩
          have hs : max ws (r θ) < max we (r θ + b (x θ)) := hθS
          rw [max_eq_right hemp.le, max_eq_right hacc.le] at hs
          rw [hgθ]; linarith
    have hlt := exB8_integral_lt hint hg (hd.ae_mem.mono fun θ hθ => (hpt θ hθ).1)
      (hSI.trans_le (measure_mono fun θ hθ => (hpt θ hθ.2).2 hθ.1))
    have hg0 : ∫ θ, g θ ∂μ = 0 := hP0
    linarith
  · -- `w_e > w*`: the net revenue is at most the profit integrand at `w_e`
    set g := (acceptSet r we).indicator (fun θ => θ - we) with hgdef
    have hg : Integrable g μ :=
      (hd.integrable_id.sub (integrable_const we)).indicator (measurableSet_acceptSet h.meas we)
    have hpt : ∀ θ ∈ Set.Icc θl θh, xNetRev r x we b θ ≤ g θ ∧
        (θ ∈ S → θ ∉ acceptSet r we → xNetRev r x we b θ < g θ) := by
      intro θ hθ
      have hP := hall θ hθ
      unfold xNetRev
      split_ifs with hemp
      · rw [max_eq_left hemp] at hP
        have hrθ : r θ ≤ we := (le_max_right _ _).trans hP
        have hm : θ ∈ acceptSet r we := hrθ
        exact ⟨(Set.indicator_of_mem hm (fun θ => θ - we)).ge, fun _ hn => absurd hm hn⟩
      · rw [not_le] at hemp
        rw [max_eq_right hemp.le] at hP
        by_cases hacc : r θ ≤ we
        · have hgθ : g θ = θ - we := Set.indicator_of_mem (show θ ∈ acceptSet r we from hacc) _
          have hrle := h.le θ hθ
          exact ⟨by rw [hgθ]; linarith, fun _ hn => absurd hacc hn⟩
        · rw [not_le] at hacc
          have hgθ : g θ = 0 :=
            Set.indicator_of_notMem (show θ ∉ acceptSet r we from not_le.2 hacc) _
          rw [max_eq_right (hwe.trans hacc).le] at hP
          refine ⟨by rw [hgθ]; linarith, fun hθS _ => ?_⟩
          have hs : max ws (r θ) < max we (r θ + b (x θ)) := hθS
          rw [max_eq_right hemp.le, max_eq_right (hwe.trans hacc).le] at hs
          rw [hgθ]; linarith
    have hle : ∫ θ, xNetRev r x we b θ ∂μ ≤ ∫ θ, g θ ∂μ :=
      integral_mono_ae hint hg (hd.ae_mem.mono fun θ hθ => (hpt θ hθ).1)
    have hgP : ∫ θ, g θ ∂μ = firmProfit μ r we := rfl
    rcases eq_zero_or_pos (μ (acceptSet r we)) with h0 | hpos
    · rw [hgP, firmProfit_of_null h.meas h0] at hle
      have hD : 0 < μ ((S ∩ Set.Icc θl θh) \ acceptSet r we) := by
        rwa [measure_sdiff_null h0]
      have hlt := exB8_integral_lt hint hg (hd.ae_mem.mono fun θ hθ => (hpt θ hθ).1)
        (hD.trans_le (measure_mono fun θ hθ => (hpt θ hθ.1.2).2 hθ.1.1 hθ.2))
      rw [hgP, firmProfit_of_null h.meas h0] at hlt
      linarith
    · have hneg := h.toMono.firmProfit_neg_of_gt_max hmax hwe hpos
      linarith

/-- **Exercise 13.B.8** (MWG, p. 474), corrected. Let `x` be injective on `[θ̲, θ̄]` (e.g.
strictly increasing), so that the purchases of a worker at home reveal her type, and let `w*` be
a competitive equilibrium wage (for instance the highest one) at which a positive mass of
employed types is more productive at home (`r(θ) > θ`). Then the benefit `b(x(θ)) = w* - θ` for
exactly these types (and `0` otherwise), with `w_e = w*`, is a budget-feasible Pareto
improvement: the types sent home gain `r(θ) - θ > 0`, nobody else is affected, and the benefit
paid equals the net output `θ - w*` the authority no longer gets. -/
theorem exercise_13_B_8 {μ : Measure ℝ} {θl θh : ℝ} {r x : ℝ → ℝ} (hd : TypeDist μ θl θh)
    (hr : Measurable r) (hx : Set.InjOn x (Set.Icc θl θh)) {ws : ℝ}
    (hws : ws ∈ eqWages μ θl θh r) (hmis : 0 < μ (acceptSet r ws ∩ {θ | θ < r θ})) :
    ∃ b : ℝ → ℝ, XBudgetOK μ r x ws b ∧ IsXParetoImprovement μ θl θh r x ws ws b := by
  classical
  have := hd.prob
  set Q := acceptSet r ws ∩ {θ | θ < r θ} ∩ Set.Icc θl θh with hQ
  have hQsub : Q ⊆ Set.Icc θl θh := Set.inter_subset_right
  set b : ℝ → ℝ := fun y =>
    if y ∈ x '' Q then ws - Function.invFunOn x (Set.Icc θl θh) y else 0 with hbdef
  have hb : ∀ θ ∈ Set.Icc θl θh, b (x θ) = Q.indicator (fun θ => ws - θ) θ := by
    intro θ hθ
    by_cases hθQ : θ ∈ Q
    · simp only [hbdef, Set.mem_image_of_mem x hθQ, ↓reduceIte, hx.leftInvOn_invFunOn hθ,
        Set.indicator_of_mem hθQ]
    · have hn : x θ ∉ x '' Q := fun hm => hθQ ((hx.mem_image_iff hQsub hθ).1 hm)
      simp only [hbdef, hn, ↓reduceIte, Set.indicator_of_notMem hθQ]
  have hpos : 0 < μ (acceptSet r ws) := hmis.trans_le (measure_mono Set.inter_subset_left)
  have hP0 : firmProfit μ r ws = 0 := (mem_eqWages_iff_profit hd hr hpos).1 hws
  set g := (acceptSet r ws).indicator (fun θ => θ - ws) with hgdef
  have hg : Integrable g μ :=
    (hd.integrable_id.sub (integrable_const ws)).indicator (measurableSet_acceptSet hr ws)
  have hnet : ∀ θ ∈ Set.Icc θl θh, xNetRev r x ws b θ = g θ := by
    intro θ hθ
    unfold xNetRev
    rw [hb θ hθ]
    by_cases hθQ : θ ∈ Q
    · have hacc : θ ∈ acceptSet r ws := hθQ.1.1
      have hlt : θ < r θ := hθQ.1.2
      rw [Set.indicator_of_mem hθQ, hgdef, Set.indicator_of_mem hacc]
      split_ifs with h1
      · exact absurd h1 (by linarith)
      · ring
    · rw [Set.indicator_of_notMem hθQ, add_zero]
      by_cases hacc : r θ ≤ ws
      · rw [hgdef, Set.indicator_of_mem (show θ ∈ acceptSet r ws from hacc)]
        split_ifs; rfl
      · rw [hgdef, Set.indicator_of_notMem (show θ ∉ acceptSet r ws from hacc)]
        split_ifs; simp
  have hae : g =ᵐ[μ] xNetRev r x ws b := hd.ae_mem.mono fun θ hθ => (hnet θ hθ).symm
  refine ⟨b, ⟨hg.congr hae, ?_⟩, fun θ hθ => ?_, ?_⟩
  · rw [← integral_congr_ae hae]
    exact hP0.ge
  · rw [hb θ hθ]
    by_cases hθQ : θ ∈ Q
    · rw [Set.indicator_of_mem hθQ, max_eq_left (hθQ.1.1 : r θ ≤ ws)]
      exact le_max_left _ _
    · rw [Set.indicator_of_notMem hθQ, add_zero]
  · refine (by rwa [hQ, measure_acceptSet_inter hd] : 0 < μ Q).trans_le
      (measure_mono fun θ hθQ => ?_)
    have hθ := hQsub hθQ
    have hlt : θ < r θ := hθQ.1.2
    have hs : max ws (r θ) < max ws (r θ + b (x θ)) := by
      rw [hb θ hθ, Set.indicator_of_mem hθQ, max_eq_left (hθQ.1.1 : r θ ≤ ws)]
      exact lt_max_of_lt_right (by linarith)
    exact hs

/-- **Exercise 13.B.8** (MWG, p. 474). An `x` that does not separate types does not help: if
`x` is constant, then at the highest-wage equilibrium of the `MonoModel` no intervention
`(w_e, b)` is a budget-feasible Pareto improvement (Proposition 13.B.2, Exercise 13.B.10). -/
theorem exercise_13_B_8_const_x {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ}
    (h : MonoModel μ θl θh r) {ws : ℝ} (hmax : IsGreatest (eqWages μ θl θh r) ws)
    {x : ℝ → ℝ} {c : ℝ} (hx : ∀ θ, x θ = c) (we : ℝ) (b : ℝ → ℝ) :
    ¬ (XBudgetOK μ r x we b ∧ IsXParetoImprovement μ θl θh r x ws we b) := by
  rintro ⟨hB, hall, hS⟩
  have hfun : xNetRev r x we b = xNetRev r x we (fun _ => b c) := by
    funext θ; simp only [xNetRev, hx]
  have hB' : BudgetOK μ r we (b c) := by
    rw [← xBudgetOK_const_iff h.dist h.meas x, XBudgetOK, ← hfun]
    exact hB
  have hSI : 0 < μ ({θ | max ws (r θ) < max we (r θ + b (x θ))} ∩ Set.Icc θl θh) := by
    rwa [measure_acceptSet_inter h.dist]
  obtain ⟨θ1, hθ1S, hθ1⟩ := MeasureTheory.nonempty_of_measure_ne_zero hSI.ne'
  refine h.isConstrainedPO hmax we (b c) hB' ⟨fun θ hθ => ?_, θ1, hθ1, ?_⟩
  · have := hall θ hθ
    rwa [hx, add_comm] at this
  · have : max ws (r θ1) < max we (r θ1 + b (x θ1)) := hθ1S
    rwa [hx, add_comm] at this

/-- **Exercise 13.B.8**, instance (MWG, p. 474). Types uniform on `[0, 2]`, `r(θ) = θ/4 + 1/4`
(strictly increasing, `r(θ) > θ` for `θ < 1/3`), purchases `x(θ) = θ`. The highest equilibrium
wage is `w* = E[θ] = 1` (everybody works); it is a constrained Pareto optimum for the schemes
`(w_e, w_u)` of p. 446, but the authority observing `x` can Pareto improve on it. -/
theorem exercise_13_B_8_instance :
    IsGreatest (eqWages (unifMeas 0 2) 0 2 fun θ => θ / 4 + 1 / 4) 1 ∧
      IsConstrainedPO (unifMeas 0 2) 0 2 (fun θ => θ / 4 + 1 / 4) 1 ∧
      ∃ b : ℝ → ℝ, XBudgetOK (unifMeas 0 2) (fun θ => θ / 4 + 1 / 4) id 1 b ∧
        IsXParetoImprovement (unifMeas 0 2) 0 2 (fun θ => θ / 4 + 1 / 4) id 1 1 b := by
  have hd : TypeDist (unifMeas 0 2) 0 2 := unifMeas_typeDist le_rfl two_pos
  have hM : MonoModel (unifMeas 0 2) 0 2 (fun θ => θ / 4 + 1 / 4) :=
    ⟨hd, unifMeas_density two_pos, (measurable_id.div_const 4).add_const _,
      fun a _ b _ hab => by linarith, by fun_prop⟩
  have hE : meanType (unifMeas 0 2) = 1 := by rw [unifMeas_mean two_pos]; norm_num
  have hsub : ∀ w, 3 / 4 ≤ w → Set.Icc (0 : ℝ) 2 ⊆ acceptSet (fun θ => θ / 4 + 1 / 4) w :=
    fun w hw θ hθ => by change θ / 4 + 1 / 4 ≤ w; linarith [hθ.2]
  have h1 : (1 : ℝ) ∈ eqWages (unifMeas 0 2) 0 2 fun θ => θ / 4 + 1 / 4 := by
    have := mean_mem_eqWages hd (hE ▸ hsub 1 (by norm_num))
    rwa [hE] at this
  have hmax : IsGreatest (eqWages (unifMeas 0 2) 0 2 fun θ => θ / 4 + 1 / 4) 1 := by
    refine ⟨h1, fun w hw => ?_⟩
    by_contra hw1
    rw [not_le] at hw1
    rw [mem_eqWages_iff, condMean_of_superset hd (hsub w (by linarith)), hE] at hw
    linarith
  refine ⟨hmax, hM.isConstrainedPO hmax, exercise_13_B_8 hd hM.meas (Set.injOn_id _) h1 ?_⟩
  refine ((unifMeas_density two_pos).pos 0 (1 / 4) le_rfl (by norm_num)
    (by norm_num)).trans_le (measure_mono fun θ hθ => ⟨?_, ?_⟩)
  · change θ / 4 + 1 / 4 ≤ 1; linarith [hθ.2]
  · change θ < θ / 4 + 1 / 4; linarith [hθ.2]

end MWG.AdverseSelection
