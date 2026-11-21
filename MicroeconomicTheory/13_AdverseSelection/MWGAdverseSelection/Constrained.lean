/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGAdverseSelection.Regular

/-!
# Constrained Pareto optimality: Proposition 13.B.2

MWG, Section 13.B, pp. 445-448.

A central authority that cannot observe types runs the firms, pays `w_e` to those who accept
employment and `w_u` to those who do not, and must balance its budget. Type `θ` accepts iff
`w_u + r(θ) ≤ w_e`, i.e. iff `θ ∈ Θ(w_e - w_u)`, and then earns `max(w_e, w_u + r(θ))`.

* `BudgetOK` is the budget constraint (13.B.8), written as `≤` (footnote 15 shows a surplus is
  never optimal: `footnote_15`). `budget_wu_le`: it says exactly that `w_u` is at most the profit
  of a firm paying `w_e - w_u`.
* `IsParetoImprovement`, `IsConstrainedPO`: the definitions of p. 445.
* `proposition_13_B_2`: in the model of p. 441 (with `r` continuous) the highest-wage
  competitive equilibrium is a constrained Pareto optimum. The proof does not use `r(θ) ≤ θ`, so
  it also proves **Exercise 13.B.10** (`exercise_13_B_10`).
* `scheme_13_B_9`, `scheme_13_B_10`, ...: the scheme `(w_u(θ̂), w_e(θ̂))` of (13.B.7)-(13.B.12)
  and its value at `θ̂ = θ*`.
* `highest_wage_implementable` (p. 446): the authority can implement the highest-wage
  equilibrium with `w_e = w*`, `w_u = 0`; so a Pareto-dominated equilibrium is not a constrained
  Pareto optimum (`dominated_not_constrainedPO`).
-/

namespace MWG.AdverseSelection

open MeasureTheory Set

/-- The model of p. 441 without `r(θ) ≤ θ` (as in Exercise 13.B.10): positive density, `r`
measurable, strictly increasing and continuous on `[θ̲, θ̄]`. -/
structure MonoModel (μ : Measure ℝ) (θl θh : ℝ) (r : ℝ → ℝ) : Prop where
  dist : TypeDist μ θl θh
  dens : HasPosDensity μ θl θh
  meas : Measurable r
  mono : StrictMonoOn r (Icc θl θh)
  cont : ContinuousOn r (Icc θl θh)

/-- The model of p. 441 is a `MonoModel`. -/
theorem RegularModel.toMono {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ}
    (h : RegularModel μ θl θh r) : MonoModel μ θl θh r :=
  ⟨h.dist, h.dens, h.meas, h.mono, h.cont⟩

/-- **(13.B.8)** (MWG, p. 447). The authority's budget: paying `w_e` to the employed set
`E = Θ(w_e - w_u)` and `w_u` to the others costs at most the output `∫_E θ dF`. -/
def BudgetOK (μ : Measure ℝ) (r : ℝ → ℝ) (we wu : ℝ) : Prop :=
  we * μ.real (acceptSet r (we - wu)) + wu * (1 - μ.real (acceptSet r (we - wu))) ≤
    ∫ θ in acceptSet r (we - wu), θ ∂μ

/-- **Section 13.B** (MWG, pp. 445-446). The intervention `(w_e, w_u)` Pareto improves on the
competitive equilibrium with wage `w*`: no worker type is worse off and some type is better
off (firms' owners earn zero in both). -/
def IsParetoImprovement (θl θh : ℝ) (r : ℝ → ℝ) (ws we wu : ℝ) : Prop :=
  (∀ θ ∈ Icc θl θh, max ws (r θ) ≤ max we (wu + r θ)) ∧
    ∃ θ ∈ Icc θl θh, max ws (r θ) < max we (wu + r θ)

/-- **Section 13.B** (MWG, pp. 445-446). The competitive equilibrium with wage `w*` is a
constrained Pareto optimum: no budget-feasible intervention Pareto improves on it. -/
def IsConstrainedPO (μ : Measure ℝ) (θl θh : ℝ) (r : ℝ → ℝ) (ws : ℝ) : Prop :=
  ∀ we wu, BudgetOK μ r we wu → ¬ IsParetoImprovement θl θh r ws we wu

/-- The budget constraint says that `w_u` is at most the profit of a firm paying
`w_e - w_u`. -/
theorem budget_wu_le {μ : Measure ℝ} {θl θh : ℝ} (hd : TypeDist μ θl θh) {r : ℝ → ℝ}
    (hr : Measurable r) {we wu : ℝ} (hb : BudgetOK μ r we wu) :
    wu ≤ firmProfit μ r (we - wu) := by
  have := hd.prob
  rw [firmProfit_eq_setIntegral hr, integral_sub hd.integrable_id.integrableOn
    (integrable_const _).integrableOn, setIntegral_const, smul_eq_mul]
  unfold BudgetOK at hb
  nlinarith

/-- **Footnote 15** (MWG, p. 447). If `(w_e, w_u)` leaves a budget surplus, raising both by
`ε` keeps the employed set, stays feasible for small `ε`, and makes every worker better off. -/
theorem footnote_15 {μ : Measure ℝ} {r : ℝ → ℝ} {we wu ε : ℝ} (hε : 0 < ε)
    (hsur : we * μ.real (acceptSet r (we - wu)) + wu * (1 - μ.real (acceptSet r (we - wu))) + ε ≤
      ∫ θ in acceptSet r (we - wu), θ ∂μ) :
    BudgetOK μ r (we + ε) (wu + ε) ∧ ∀ x, max we (wu + x) < max (we + ε) (wu + ε + x) := by
  have hd : we + ε - (wu + ε) = we - wu := by ring
  refine ⟨?_, fun x => ?_⟩
  · unfold BudgetOK; rw [hd]; nlinarith
  · rw [show wu + ε + x = (wu + x) + ε by ring, max_add_add_right]; linarith

/-- The worker's payoff under an intervention: `max(w_e, w_u + r) = w_u + max(w_e - w_u, r)`. -/
theorem scheme_payoff (we wu x : ℝ) : max we (wu + x) = wu + max (we - wu) x := by
  rw [← max_add_add_left]; congr 1; ring

/-- In the `MonoModel`, above the largest equilibrium wage the profit is negative wherever
`Θ(w)` has positive probability. -/
theorem MonoModel.firmProfit_neg_of_gt_max {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ}
    (h : MonoModel μ θl θh r) {ws : ℝ} (hmax : IsGreatest (eqWages μ θl θh r) ws) {w : ℝ}
    (hw : ws < w) (hpos : 0 < μ (acceptSet r w)) : firmProfit μ r w < 0 := by
  have hcont := continuous_firmProfit h.dist h.dens.noAtom h.meas h.mono.injOn
  have hne : firmProfit μ r w ≠ 0 := fun h0 =>
    absurd (hmax.2 ((mem_eqWages_iff_profit h.dist h.meas hpos).2 h0)) (not_le.2 hw)
  rcases lt_or_gt_of_ne hne with hneg | hp
  · exact hneg
  · exfalso
    set b := max w θh + 1
    have hwb : w ≤ b := by simp only [b]; linarith [le_max_left w θh]
    have hbθ : θh < b := by simp only [b]; linarith [le_max_right w θh]
    have hmono : ∀ c, w ≤ c → 0 < μ (acceptSet r c) := fun c hc =>
      hpos.trans_le (measure_mono fun θ hθ => le_trans hθ hc)
    have hb := firmProfit_neg_of_gt h.dist h.meas hbθ (hmono b hwb)
    obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc' hwb hcont.continuousOn ⟨hb.le, hp.le⟩
    have hcm := (mem_eqWages_iff_profit h.dist h.meas (hmono c hc.1)).2 hc0
    exact absurd (hmax.2 hcm) (not_le.2 (hw.trans_le hc.1))

/-- **Proposition 13.B.2**, proof (MWG, pp. 447-448), the case `θ̂ < θ*`. If the authority
employs fewer types than the equilibrium with wage `w*` (cutoff wage `d` with
`r(θ̲) ≤ d < w*` and `d < r(θ̄)`), then `w_e ≤ w_u + d ≤ Π(d) + d < w*`: the type `θ̲` is worse
off. This is `E[θ | θ ≤ θ̂] < E[θ | θ ≤ θ*]`. -/
theorem MonoModel.profit_add_lt {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ}
    (h : MonoModel μ θl θh r) {ws d : ℝ} (hws : ws ∈ eqWages μ θl θh r) (hd1 : r θl ≤ d)
    (hd2 : d < ws) (hd3 : d < r θh) : firmProfit μ r d + d < ws := by
  have := h.dist.prob
  have hl : θl ∈ Icc θl θh := ⟨le_rfl, h.dist.lt.le⟩
  have hh : θh ∈ Icc θl θh := ⟨h.dist.lt.le, le_rfl⟩
  -- the type `a` with `r(a) = d`
  obtain ⟨a, ha, hra⟩ := intermediate_value_Icc h.dist.lt.le h.cont ⟨hd1, hd3.le⟩
  have hah : a < θh := by
    rcases eq_or_lt_of_le ha.2 with he | hlt
    · rw [he] at hra; exact absurd hra hd3.ne'
    · exact hlt
  have hiff : ∀ θ ∈ Icc θl θh, r θ ≤ d ↔ θ ≤ a := fun θ hθ => by
    rw [← hra]; exact h.mono.le_iff_le hθ ha
  set E := acceptSet r d
  set E' := acceptSet r ws
  set D := E' \ E
  have hEm := measurableSet_acceptSet h.meas d
  have hE'm := measurableSet_acceptSet h.meas ws
  have hsub : E ⊆ E' := fun θ hθ => le_trans hθ hd2.le
  have hE'pos : 0 < μ E' := measure_acceptSet_pos h.dist h.dens h.cont (hd1.trans_lt hd2)
  have hP : firmProfit μ r ws = 0 := (mem_eqWages_iff_profit h.dist h.meas hE'pos).1 hws
  have hint := h.dist.integrable_id
  -- integrals and measures
  have hIE' : ∫ θ in E', θ ∂μ = ws * μ.real E' := by
    have := hP
    rw [firmProfit_eq_setIntegral h.meas, integral_sub hint.integrableOn
      (integrable_const _).integrableOn, setIntegral_const, smul_eq_mul] at this
    linarith
  have hunion : E' = E ∪ D := (union_sdiff_cancel hsub).symm
  have hdisj : Disjoint E D := disjoint_sdiff_right
  have hDm : MeasurableSet D := hE'm.diff hEm
  have hIsplit : ∫ θ in E', θ ∂μ = ∫ θ in E, θ ∂μ + ∫ θ in D, θ ∂μ := by
    rw [hunion]; exact setIntegral_union hdisj hDm hint.integrableOn hint.integrableOn
  have hMsplit : μ.real E' = μ.real E + μ.real D := by
    rw [hunion]; exact measureReal_union hdisj hDm
  have hEa : ∫ θ in E, θ ∂μ ≤ a * μ.real E := by
    have := setIntegral_mono_on_ae hint.integrableOn (integrable_const a).integrableOn hEm
      (h.dist.ae_mem.mono fun θ hθ hθE => (hiff θ hθ).1 hθE)
    rwa [setIntegral_const, smul_eq_mul, mul_comm] at this
  have hDa : a * μ.real D ≤ ∫ θ in D, θ ∂μ := by
    have := setIntegral_mono_on_ae (integrable_const a).integrableOn hint.integrableOn hDm
      (h.dist.ae_mem.mono fun θ hθ hθD => by
        by_contra hlt
        exact hθD.2 ((hiff θ hθ).2 (not_le.1 hlt).le))
    rwa [setIntegral_const, smul_eq_mul, mul_comm] at this
  have hE0 := measureReal_nonneg (μ := μ) (s := E)
  have hD0 := measureReal_nonneg (μ := μ) (s := D)
  -- `E[θ | E] ≤ w*`
  have hclaim : ∫ θ in E, θ ∂μ ≤ ws * μ.real E := by
    by_contra hcon
    rw [not_le] at hcon
    have hEpos : 0 < μ.real E := by
      rcases eq_or_lt_of_le hE0 with he | hlt
      · rw [← he] at hcon hEa; linarith
      · exact hlt
    have hwa : ws < a := lt_of_mul_lt_mul_right (hcon.trans_le hEa) hE0
    have hsplit' : ws * μ.real E' = ws * μ.real E + ws * μ.real D := by rw [hMsplit]; ring
    have hDlt : ∫ θ in D, θ ∂μ < ws * μ.real D := by linarith
    rcases eq_or_lt_of_le hD0 with he | hDpos
    · rw [← he] at hDlt hDa; linarith
    · have : a * μ.real D < ws * μ.real D := hDa.trans_lt hDlt
      linarith [lt_of_mul_lt_mul_right this hD0]
  -- some types are not employed at `d`
  have hEl1 : μ.real E < 1 := by
    have hIoi : 0 < μ (Ioi a) := by
      refine (h.dens.pos ((a + θh) / 2) θh (by linarith [ha.1]) (by linarith) le_rfl).trans_le
        (measure_mono fun θ hθ => ?_)
      exact show a < θ by linarith [hθ.1]
    have hEle : μ E ≤ μ (Iic a) := measure_mono_ae (h.dist.ae_mem.mono fun θ hθ hθE =>
      show θ ≤ a from (hiff θ hθ).1 hθE)
    have hsum : μ (Iic a) + μ (Ioi a) = 1 := by
      rw [← compl_Iic, measure_add_measure_compl measurableSet_Iic, measure_univ]
    have hlt1 : μ E < 1 := by
      calc μ E ≤ μ (Iic a) := hEle
        _ < μ (Iic a) + μ (Ioi a) := ENNReal.lt_add_right (measure_ne_top _ _) hIoi.ne'
        _ = 1 := hsum
    rw [Measure.real]
    exact (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.one_ne_top).2 hlt1 |>.trans_eq
      ENNReal.toReal_one
  rw [firmProfit_eq_setIntegral h.meas, integral_sub hint.integrableOn
    (integrable_const _).integrableOn, setIntegral_const, smul_eq_mul]
  nlinarith

/-- When every type in `[θ̲, θ̄]` accepts `w`, the profit is `E[θ] - w`. -/
theorem firmProfit_of_full {μ : Measure ℝ} {θl θh : ℝ} (hd : TypeDist μ θl θh) {r : ℝ → ℝ}
    (hr : Measurable r) {w : ℝ} (hfull : Icc θl θh ⊆ acceptSet r w) :
    firmProfit μ r w = meanType μ - w := by
  have := hd.prob
  rw [firmProfit_eq_setIntegral hr, setIntegral_eq_integral_of_ae_compl_eq_zero
    (hd.ae_mem.mono fun θ hθ hc => absurd (hfull hθ) hc), integral_sub hd.integrable_id
    (integrable_const w), integral_const, meanType]
  simp

/-- If every type accepts `E[θ]`, then `E[θ]` is a competitive equilibrium wage (full
employment). -/
theorem mean_mem_eqWages {μ : Measure ℝ} {θl θh : ℝ} (hd : TypeDist μ θl θh) {r : ℝ → ℝ}
    (hfull : Icc θl θh ⊆ acceptSet r (meanType μ)) : meanType μ ∈ eqWages μ θl θh r := by
  rw [mem_eqWages_iff, condMean_of_superset hd hfull]

/-- **Proposition 13.B.2** in the generality of **Exercise 13.B.10** (MWG, pp. 447-448, 474).
In the model with positive density and `r` strictly increasing and continuous (`r(θ) ≤ θ` is not
needed), the highest-wage competitive equilibrium is a constrained Pareto optimum. -/
theorem MonoModel.isConstrainedPO {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ}
    (h : MonoModel μ θl θh r) {ws : ℝ} (hmax : IsGreatest (eqWages μ θl θh r) ws) :
    IsConstrainedPO μ θl θh r ws := by
  have := h.dist.prob
  intro we wu hb ⟨hall, θ0, hθ0, hstrict⟩
  have hl : θl ∈ Icc θl θh := ⟨le_rfl, h.dist.lt.le⟩
  have hh : θh ∈ Icc θl θh := ⟨h.dist.lt.le, le_rfl⟩
  have hwu := budget_wu_le h.dist h.meas hb
  have hTl := hall θl hl
  have hTh := hall θh hh
  rw [scheme_payoff] at hTl hTh hstrict
  set d := we - wu with hd
  have hr0l : r θl ≤ r θ0 := h.mono.monotoneOn hl hθ0 hθ0.1
  have hr0h : r θ0 ≤ r θh := h.mono.monotoneOn hθ0 hh hθ0.2
  have hfullOf : ∀ x, r θh ≤ x → Icc θl θh ⊆ acceptSet r x := fun x hx θ hθ =>
    (h.mono.monotoneOn hθ hh hθ.2).trans hx
  rcases lt_trichotomy d ws with hdlt | hdeq | hdgt
  · by_cases hd1 : d < r θl
    · have hP := firmProfit_of_lt h.dist h.mono.monotoneOn h.meas hd1
      rw [max_eq_right hd1.le] at hTl
      have : wu = 0 := le_antisymm (hP ▸ hwu) (by linarith [le_max_right ws (r θl)])
      linarith [max_le_max hdlt.le (le_refl (r θ0))]
    · rw [not_lt] at hd1
      rw [max_eq_left hd1] at hTl
      by_cases hd3 : d < r θh
      · have := h.profit_add_lt hmax.1 hd1 hdlt hd3
        linarith [le_max_left ws (r θl)]
      · rw [not_lt] at hd3
        have hP := firmProfit_of_full h.dist h.meas (hfullOf d hd3)
        have hE : ws ≤ meanType μ := by linarith [le_max_left ws (r θl)]
        have hEm : meanType μ ≤ ws :=
          hmax.2 (mean_mem_eqWages h.dist (hfullOf _ (by linarith)))
        rw [max_eq_left (hr0h.trans hd3)] at hstrict
        linarith [le_max_left ws (r θ0)]
  · have hP : firmProfit μ r ws ≤ 0 := by
      by_cases hpos : 0 < μ (acceptSet r ws)
      · exact ((mem_eqWages_iff_profit h.dist h.meas hpos).1 hmax.1).le
      · exact (firmProfit_of_null h.meas (le_antisymm (not_lt.1 hpos) bot_le)).le
    rw [hdeq] at hwu hstrict
    linarith
  · by_cases hdl : d ≤ r θl
    · have hP : firmProfit μ r d = 0 := by
        rcases eq_or_lt_of_le hdl with he | hlt
        · rw [he]; exact firmProfit_rl h.dist h.mono h.dens h.meas
        · exact firmProfit_of_lt h.dist h.mono.monotoneOn h.meas hlt
      rw [max_eq_right (hdl.trans hr0l)] at hstrict
      linarith [le_max_right ws (r θ0)]
    · rw [not_le] at hdl
      have hneg := h.firmProfit_neg_of_gt_max hmax hdgt
        (measure_acceptSet_pos h.dist h.dens h.cont hdl)
      by_cases hdh : d ≤ r θh
      · rw [max_eq_right hdh] at hTh
        linarith [le_max_right ws (r θh)]
      · rw [not_le] at hdh
        have hP := firmProfit_of_full h.dist h.meas (hfullOf d hdh.le)
        rw [max_eq_left hdh.le] at hTh
        have hEm : meanType μ ≤ ws :=
          hmax.2 (mean_mem_eqWages h.dist (hfullOf _ (by linarith [le_max_right ws (r θh)])))
        rw [max_eq_left (hr0h.trans hdh.le)] at hstrict
        linarith [le_max_left ws (r θ0)]

/-- **Proposition 13.B.2** (MWG, p. 447). In the adverse selection model (`r` strictly
increasing, here also continuous, `r(θ) ≤ θ`, positive density) the highest-wage competitive
equilibrium is a constrained Pareto optimum. -/
theorem proposition_13_B_2 {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ}
    (h : RegularModel μ θl θh r) {ws : ℝ} (hmax : IsGreatest (eqWages μ θl θh r) ws) :
    IsConstrainedPO μ θl θh r ws :=
  h.toMono.isConstrainedPO hmax

/-- **Exercise 13.B.10** (MWG, p. 474). Proposition 13.B.2 continues to hold when `r(θ) > θ` for
some `θ`. -/
theorem exercise_13_B_10 {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ}
    (h : MonoModel μ θl θh r) {ws : ℝ} (hmax : IsGreatest (eqWages μ θl θh r) ws) :
    IsConstrainedPO μ θl θh r ws :=
  h.isConstrainedPO hmax

/-- **(13.B.9)** (MWG, p. 447). The unemployment benefit that employs exactly the types
`θ ≤ θ̂` with a balanced budget: `w_u(θ̂) = ∫_{θ̲}^{θ̂} θ f(θ) dθ - r(θ̂) F(θ̂)`. -/
noncomputable def schemeWu (μ : Measure ℝ) (r : ℝ → ℝ) (θhat : ℝ) : ℝ :=
  (∫ θ in Iic θhat, θ ∂μ) - r θhat * μ.real (Iic θhat)

/-- **(13.B.10)** (MWG, p. 447). The employment wage
`w_e(θ̂) = ∫_{θ̲}^{θ̂} θ f(θ) dθ + r(θ̂)(1 - F(θ̂))`. -/
noncomputable def schemeWe (μ : Measure ℝ) (r : ℝ → ℝ) (θhat : ℝ) : ℝ :=
  (∫ θ in Iic θhat, θ ∂μ) + r θhat * (1 - μ.real (Iic θhat))

/-- **(13.B.7)-(13.B.10)** (MWG, p. 447). `(w_e(θ̂), w_u(θ̂))` satisfies the indifference
condition (13.B.7) `w_u + r(θ̂) = w_e` and the budget (13.B.8), and is the only pair doing so. -/
theorem scheme_13_B_7_8 (μ : Measure ℝ) (r : ℝ → ℝ) (θhat : ℝ) :
    schemeWu μ r θhat + r θhat = schemeWe μ r θhat ∧
      schemeWe μ r θhat * μ.real (Iic θhat) + schemeWu μ r θhat * (1 - μ.real (Iic θhat)) =
        ∫ θ in Iic θhat, θ ∂μ ∧
      ∀ we wu, wu + r θhat = we →
        we * μ.real (Iic θhat) + wu * (1 - μ.real (Iic θhat)) = ∫ θ in Iic θhat, θ ∂μ →
        wu = schemeWu μ r θhat ∧ we = schemeWe μ r θhat := by
  refine ⟨by unfold schemeWu schemeWe; ring, by unfold schemeWu schemeWe; ring,
    fun we wu h7 h8 => ?_⟩
  subst h7
  unfold schemeWu schemeWe
  constructor <;> linarith

/-- **(13.B.11)-(13.B.12)** (MWG, p. 447). With `F(θ̂) > 0`,
`w_u(θ̂) = F(θ̂)(E[θ | θ ≤ θ̂] - r(θ̂))` and `w_e(θ̂) = F(θ̂)(E[θ | θ ≤ θ̂] - r(θ̂)) + r(θ̂)`. -/
theorem scheme_13_B_11_12 (μ : Measure ℝ) (r : ℝ → ℝ) {θhat : ℝ}
    (hF : 0 < μ.real (Iic θhat)) :
    schemeWu μ r θhat = μ.real (Iic θhat) *
        ((∫ θ in Iic θhat, θ ∂μ) / μ.real (Iic θhat) - r θhat) ∧
      schemeWe μ r θhat = μ.real (Iic θhat) *
        ((∫ θ in Iic θhat, θ ∂μ) / μ.real (Iic θhat) - r θhat) + r θhat := by
  unfold schemeWu schemeWe
  constructor
  · field_simp
  · field_simp; ring

/-- **Proposition 13.B.2**, proof (MWG, p. 447). At the highest type `θ*` employed in the
highest-wage equilibrium, `r(θ*) = E[θ | θ ≤ θ*]`, so `w_u(θ*) = 0` and `w_e(θ*) = r(θ*)`: the
scheme reproduces the equilibrium. -/
theorem scheme_at_θstar (μ : Measure ℝ) (r : ℝ → ℝ) {θs : ℝ} (hF : 0 < μ.real (Iic θs))
    (heq : r θs = (∫ θ in Iic θs, θ ∂μ) / μ.real (Iic θs)) :
    schemeWu μ r θs = 0 ∧ schemeWe μ r θs = r θs := by
  obtain ⟨h1, h2⟩ := scheme_13_B_11_12 μ r hF
  rw [h1, h2, ← heq]; simp

/-- **Section 13.B** (MWG, p. 446). The authority can implement any competitive equilibrium
(in particular the highest-wage one) by setting `w_e = w*`, `w_u = 0`: the budget balances
since `w* = E[θ | r(θ) ≤ w*]`, and every type gets her equilibrium payoff. -/
theorem highest_wage_implementable {μ : Measure ℝ} {θl θh : ℝ} (hd : TypeDist μ θl θh)
    {r : ℝ → ℝ} (hr : Measurable r) {ws : ℝ} (hws : ws ∈ eqWages μ θl θh r)
    (hpos : 0 < μ (acceptSet r ws)) :
    BudgetOK μ r ws 0 ∧ ∀ θ, max ws (0 + r θ) = max ws (r θ) := by
  have := hd.prob
  refine ⟨?_, fun θ => by rw [zero_add]⟩
  have hP := (mem_eqWages_iff_profit hd hr hpos).1 hws
  rw [firmProfit_eq_setIntegral hr, integral_sub hd.integrable_id.integrableOn
    (integrable_const _).integrableOn, setIntegral_const, smul_eq_mul] at hP
  unfold BudgetOK
  rw [sub_zero]
  linarith

/-- **Section 13.B** (MWG, p. 446). A competitive equilibrium Pareto dominated by another one
(with positive employment, and some type employed at the higher wage) is not a constrained
Pareto optimum. -/
theorem dominated_not_constrainedPO {μ : Measure ℝ} {θl θh : ℝ} (hd : TypeDist μ θl θh)
    {r : ℝ → ℝ} (hr : Measurable r) {w₁ w₂ : ℝ} (hw₂ : w₂ ∈ eqWages μ θl θh r)
    (hpos : 0 < μ (acceptSet r w₂)) (hlt : w₁ < w₂) (hemp : ∃ θ ∈ Icc θl θh, r θ < w₂) :
    ¬ IsConstrainedPO μ θl θh r w₁ := by
  intro hcpo
  obtain ⟨hb, hpay⟩ := highest_wage_implementable hd hr hw₂ hpos
  refine hcpo w₂ 0 hb ⟨fun θ _ => ?_, ?_⟩
  · rw [hpay]; exact max_le_max hlt.le le_rfl
  · obtain ⟨θ, hθ, hrθ⟩ := hemp
    refine ⟨θ, hθ, ?_⟩
    rw [hpay, max_eq_left hrθ.le]
    exact max_lt hlt hrθ

end MWG.AdverseSelection
