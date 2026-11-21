/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPrincipalAgent.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# The hidden-action model and the observable-effort benchmark

MWG, Section 14.B, pp. 478-483.

Profits `π` are distributed with density `f(π | e)` with respect to a measure `ν` on `ℝ`
(MWG: Lebesgue measure on `[π̲, π̄]`; any measure is allowed here, so that the discrete version of
footnote 6 is the case of a sum of Dirac masses). The manager has utility `v(w) - g(e)` with
`v' > 0` and `v` concave (`v'' ≤ 0`); the owner is risk neutral. A compensation scheme is a
measurable `w : ℝ → ℝ` for which all expected wages and utilities exist (`Adm`); wages may be
negative (footnote 6).

* `ha_cost_lower_bound`: any scheme giving the manager `ū` at effort `e` costs at least the fixed
  wage `w*_e` of (14.B.4) (Jensen).
* `ha_fixed_wage_costMin`, `ha_costMin_binds`, `ha_costMin_unique`: problem (14.B.2) is solved by
  the fixed wage, its constraint binds, and under strict risk aversion the solution is unique
  (`ν`-a.e., footnote 6).
* `ha_foc_constant`, `ha_riskNeutral_costMin`: condition (14.B.3) and the risk-neutral case.
* `proposition_14_B_1`, `proposition_14_B_1_unique`: Proposition 14.B.1.
* `ha_value_le_obs`: the owner never does better when effort is unobservable (p. 482).
* `proposition_14_B_2`, `proposition_14_B_2_every`: Proposition 14.B.2 ("selling the project").
-/

namespace MWG.PrincipalAgent

open MeasureTheory Set

/-- **Section 14.B** (MWG, pp. 479-480). The hidden-action principal-agent model with effort set
`ε`: a reference measure `ν` on profits, densities `f e`, the manager's utility of income `v`
with derivative `dv`, his disutility of effort `g`, and his reservation utility `ubar`. -/
structure HAModel (ε : Type*) where
  ν : Measure ℝ
  f : ε → ℝ → ℝ
  v : ℝ → ℝ
  dv : ℝ → ℝ
  g : ε → ℝ
  ubar : ℝ

namespace HAModel

variable {ε : Type*}

/-- **Section 14.B** (MWG, pp. 479-480). The standing assumptions: each `f e` is a measurable
density, positive at every profit level, with a finite mean; `v` is differentiable with `v' > 0`
and concave (`v'' ≤ 0`). -/
structure Standing (M : HAModel ε) : Prop where
  f_meas : ∀ e, Measurable (M.f e)
  f_pos : ∀ e x, 0 < M.f e x
  f_int : ∀ e, Integrable (M.f e) M.ν
  f_one : ∀ e, ∫ x, M.f e x ∂M.ν = 1
  x_int : ∀ e, Integrable (fun x => x * M.f e x) M.ν
  v_deriv : ∀ w, HasDerivAt M.v (M.dv w) w
  dv_pos : ∀ w, 0 < M.dv w
  v_conc : ConcaveOn ℝ univ M.v

/-- An admissible compensation scheme: measurable, with finite expected wage and utility under
every effort. -/
def Adm (M : HAModel ε) (w : ℝ → ℝ) : Prop :=
  Measurable w ∧ ∀ e, Integrable (fun x => w x * M.f e x) M.ν ∧
    Integrable (fun x => M.v (w x) * M.f e x) M.ν

/-- The expected wage `∫ w(π) f(π | e) dπ`. -/
noncomputable def EW (M : HAModel ε) (e : ε) (w : ℝ → ℝ) : ℝ := ∫ x, w x * M.f e x ∂M.ν

/-- The expected utility of income `∫ v(w(π)) f(π | e) dπ`. -/
noncomputable def EV (M : HAModel ε) (e : ε) (w : ℝ → ℝ) : ℝ :=
  ∫ x, M.v (w x) * M.f e x ∂M.ν

/-- The manager's expected utility `∫ v(w(π)) f(π | e) dπ - g(e)`. -/
noncomputable def EU (M : HAModel ε) (e : ε) (w : ℝ → ℝ) : ℝ := M.EV e w - M.g e

/-- Expected gross profit `∫ π f(π | e) dπ`. -/
noncomputable def GP (M : HAModel ε) (e : ε) : ℝ := ∫ x, x * M.f e x ∂M.ν

/-- The owner's payoff `∫ (π - w(π)) f(π | e) dπ`, the objective of (14.B.1). -/
noncomputable def OP (M : HAModel ε) (e : ε) (w : ℝ → ℝ) : ℝ :=
  ∫ x, (x - w x) * M.f e x ∂M.ν

/-- The constraint of (14.B.1)-(14.B.2): an admissible scheme giving the manager at least `ū`
when he takes effort `e`. -/
def ObsFeasible (M : HAModel ε) (e : ε) (w : ℝ → ℝ) : Prop := M.Adm w ∧ M.ubar ≤ M.EU e w

/-- **(14.B.1)** (MWG, p. 480). An optimal contract `(e, w(π))` when effort is observable. -/
def IsObsOptimal (M : HAModel ε) (e : ε) (w : ℝ → ℝ) : Prop :=
  M.ObsFeasible e w ∧ ∀ e' w', M.ObsFeasible e' w' → M.OP e' w' ≤ M.OP e w

/-- **(14.B.2)** (MWG, p. 480). `w` minimizes the expected wage of implementing `e` when effort
is observable. -/
def IsCostMin (M : HAModel ε) (e : ε) (w : ℝ → ℝ) : Prop :=
  M.ObsFeasible e w ∧ ∀ w', M.ObsFeasible e w' → M.EW e w ≤ M.EW e w'

/-- **(14.B.9)(ii)** (MWG, p. 483). The incentive constraint: `e` maximizes the manager's
expected utility under `w`. -/
def IC (M : HAModel ε) (e : ε) (w : ℝ → ℝ) : Prop := ∀ e', M.EU e' w ≤ M.EU e w

/-- The constraints of (14.B.9) (MWG, p. 483). -/
def HAFeasible (M : HAModel ε) (e : ε) (w : ℝ → ℝ) : Prop := M.ObsFeasible e w ∧ M.IC e w

/-- **(14.B.9)** (MWG, p. 483). `w` is an optimal incentive scheme for implementing `e`. -/
def IsHACostMin (M : HAModel ε) (e : ε) (w : ℝ → ℝ) : Prop :=
  M.HAFeasible e w ∧ ∀ w', M.HAFeasible e w' → M.EW e w ≤ M.EW e w'

/-- An optimal contract when effort is not observable: the owner picks the effort to implement
and an incentive-compatible scheme (MWG, pp. 482-483). -/
def IsHAOptimal (M : HAModel ε) (e : ε) (w : ℝ → ℝ) : Prop :=
  M.HAFeasible e w ∧ ∀ e' w', M.HAFeasible e' w' → M.OP e' w' ≤ M.OP e w

/-- The owner's payoff is expected gross profit less the expected wage (MWG, p. 480). -/
theorem ha_OP_eq {M : HAModel ε} (hM : M.Standing) {w : ℝ → ℝ} (hw : M.Adm w) (e : ε) :
    M.OP e w = M.GP e - M.EW e w := by
  unfold OP GP EW
  rw [← integral_sub (hM.x_int e) (hw.2 e).1]
  congr 1; funext x; ring

/-- Constant schemes are admissible. -/
theorem ha_const_adm {M : HAModel ε} (hM : M.Standing) (c : ℝ) : M.Adm (fun _ => c) :=
  ⟨measurable_const, fun e => ⟨(hM.f_int e).const_mul c, (hM.f_int e).const_mul _⟩⟩

/-- A fixed wage `c` costs `c`. -/
theorem ha_EW_const {M : HAModel ε} (hM : M.Standing) (e : ε) (c : ℝ) :
    M.EW e (fun _ => c) = c := by
  unfold EW; rw [integral_const_mul, hM.f_one, mul_one]

/-- A fixed wage `c` gives expected utility of income `v(c)`. -/
theorem ha_EV_const {M : HAModel ε} (hM : M.Standing) (e : ε) (c : ℝ) :
    M.EV e (fun _ => c) = M.v c := by
  unfold EV; rw [integral_const_mul, hM.f_one, mul_one]

/-- The manager's utility of income is strictly increasing (`v' > 0`). -/
theorem ha_v_strictMono {M : HAModel ε} (hM : M.Standing) : StrictMono M.v :=
  strictMono_of_hasDerivAt_pos hM.v_deriv hM.dv_pos

/-- Jensen's inequality in the model: `∫ v(w) f(· | e) ≤ v(∫ w f(· | e))`. -/
theorem ha_EV_le {M : HAModel ε} (hM : M.Standing) {w : ℝ → ℝ} (hw : M.Adm w) (e : ε) :
    M.EV e w ≤ M.v (M.EW e w) :=
  tpa_jensen hM.v_conc hM.v_deriv (fun x => (hM.f_pos e x).le) (hM.f_int e) (hM.f_one e)
    (hw.2 e).1 (hw.2 e).2

/-- **(14.B.4)** (MWG, p. 481). Any admissible scheme giving the manager at least `ū` at effort
`e` costs at least the fixed wage `w*_e` with `v(w*_e) - g(e) = ū`. -/
theorem ha_cost_lower_bound {M : HAModel ε} (hM : M.Standing) {e : ε} {w : ℝ → ℝ}
    (hw : M.ObsFeasible e w) {wbar : ℝ} (hwbar : M.v wbar = M.ubar + M.g e) :
    wbar ≤ M.EW e w := by
  have h1 := ha_EV_le hM hw.1 e
  have h2 := hw.2
  unfold EU at h2
  exact (ha_v_strictMono hM).le_iff_le.1 (by linarith)

/-- The fixed wage `w*_e` of (14.B.4) satisfies the participation constraint with equality. -/
theorem ha_fixed_wage_feasible {M : HAModel ε} (hM : M.Standing) {e : ε} {wbar : ℝ}
    (hwbar : M.v wbar = M.ubar + M.g e) :
    M.ObsFeasible e (fun _ => wbar) ∧ M.EU e (fun _ => wbar) = M.ubar := by
  have : M.EU e (fun _ => wbar) = M.ubar := by
    unfold EU; rw [ha_EV_const hM, hwbar]; ring
  exact ⟨⟨ha_const_adm hM wbar, this.ge⟩, this⟩

/-- **(14.B.2)-(14.B.4)** (MWG, pp. 480-481). The fixed wage `w*_e` solves (14.B.2). -/
theorem ha_fixed_wage_costMin {M : HAModel ε} (hM : M.Standing) {e : ε} {wbar : ℝ}
    (hwbar : M.v wbar = M.ubar + M.g e) : M.IsCostMin e (fun _ => wbar) := by
  refine ⟨(ha_fixed_wage_feasible hM hwbar).1, fun w' hw' => ?_⟩
  rw [ha_EW_const hM]
  exact ha_cost_lower_bound hM hw' hwbar

/-- **(14.B.2)** (MWG, p. 480): "the constraint always binds at a solution", and every solution
costs exactly `w*_e`. -/
theorem ha_costMin_binds {M : HAModel ε} (hM : M.Standing) {e : ε} {w : ℝ → ℝ}
    (hw : M.IsCostMin e w) {wbar : ℝ} (hwbar : M.v wbar = M.ubar + M.g e) :
    M.EW e w = wbar ∧ M.EU e w = M.ubar := by
  have hle := ha_cost_lower_bound hM hw.1 hwbar
  have hge := hw.2 _ (ha_fixed_wage_feasible hM hwbar).1
  rw [ha_EW_const hM] at hge
  have heq : M.EW e w = wbar := le_antisymm hge hle
  refine ⟨heq, ?_⟩
  have h1 := ha_EV_le hM hw.1.1 e
  have h2 := hw.1.2
  unfold EU at h2 ⊢
  rw [heq, hwbar] at h1
  linarith

/-- **Proposition 14.B.1, uniqueness part; footnote 6** (MWG, p. 481). If `v'' < 0` (here: `v`
strictly concave), every solution of (14.B.2) is the fixed wage `w*_e` at a set of profit levels
of full measure. -/
theorem ha_costMin_unique {M : HAModel ε} (hM : M.Standing) (hsc : StrictConcaveOn ℝ univ M.v)
    {e : ε} {w : ℝ → ℝ} (hw : M.IsCostMin e w) {wbar : ℝ}
    (hwbar : M.v wbar = M.ubar + M.g e) : ∀ᵐ x ∂M.ν, w x = wbar := by
  obtain ⟨hEW, hEU⟩ := ha_costMin_binds hM hw hwbar
  have heq : M.EV e w = M.v (M.EW e w) := by
    unfold EU at hEU; rw [hEW, hwbar]; linarith
  have := tpa_jensen_eq hsc hM.v_deriv (hM.f_pos e) (hM.f_int e) (hM.f_one e) (hw.1.1.2 e).1
    (hw.1.1.2 e).2 heq
  filter_upwards [this] with x hx
  rw [hx]; exact hEW

/-- **(14.B.3)** (MWG, p. 481): with strict risk aversion (`v'` strictly decreasing) a scheme
satisfying `1 / v'(w(π)) = γ` at every profit level is a fixed wage. -/
theorem ha_foc_constant {M : HAModel ε} (hda : StrictAnti M.dv) {w : ℝ → ℝ} {γ : ℝ}
    (hfoc : ∀ x, 1 / M.dv (w x) = γ) (x y : ℝ) : w x = w y := by
  have h : M.dv (w x) = M.dv (w y) := by
    have := (hfoc x).trans (hfoc y).symm
    simpa using this
  exact hda.injective h

/-- **(14.B.3), risk-neutral case** (MWG, p. 481). If `v(w) = w`, condition (14.B.3) holds for
every scheme (with `γ = 1`), and a scheme solves (14.B.2) iff it gives an expected wage of
`ū + g(e)`. -/
theorem ha_riskNeutral_costMin {M : HAModel ε} (hM : M.Standing) (hv : ∀ w, M.v w = w)
    (hdv : ∀ w, M.dv w = 1) {e : ε} {w : ℝ → ℝ} (hw : M.Adm w) :
    (∀ x, 1 / M.dv (w x) = 1) ∧
      (M.IsCostMin e w ↔ M.EW e w = M.ubar + M.g e) := by
  have hEV : M.EV e w = M.EW e w := by unfold EV EW; simp only [hv]
  refine ⟨fun x => by simp [hdv], ⟨fun h => ?_, fun h => ⟨⟨hw, ?_⟩, fun w' hw' => ?_⟩⟩⟩
  · exact (ha_costMin_binds hM h (hv _)).1
  · unfold EU; rw [hEV, h]; ring_nf; exact le_refl _
  · rw [h]; have := ha_cost_lower_bound hM hw' (hv (M.ubar + M.g e)); exact this

/-- Since `g(e_H) > g(e_L)`, the fixed wage is higher when the contract calls for `e_H`
(MWG, p. 481). -/
theorem ha_wage_higher {M : HAModel ε} (hM : M.Standing) {eL eH : ε} (hg : M.g eL < M.g eH)
    {wL wH : ℝ} (hL : M.v wL = M.ubar + M.g eL) (hH : M.v wH = M.ubar + M.g eH) : wL < wH :=
  (ha_v_strictMono hM).lt_iff_lt.1 (by rw [hL, hH]; linarith)

/-- **Proposition 14.B.1** (MWG, p. 481). Let `w*(e)` solve `v(w*(e)) = ū + g(e)` for every `e`.
If `e*` maximizes `∫ π f(π | e) dπ - v⁻¹(ū + g(e))`, the contract specifying `e*` and the fixed
wage `w*(e*)` is optimal when effort is observable. -/
theorem proposition_14_B_1 {M : HAModel ε} (hM : M.Standing) {wstar : ε → ℝ}
    (hws : ∀ e, M.v (wstar e) = M.ubar + M.g e) {estar : ε}
    (hmax : ∀ e, M.GP e - wstar e ≤ M.GP estar - wstar estar) :
    M.IsObsOptimal estar (fun _ => wstar estar) := by
  refine ⟨(ha_fixed_wage_feasible hM (hws estar)).1, fun e' w' hw' => ?_⟩
  rw [ha_OP_eq hM hw'.1, ha_OP_eq hM (ha_const_adm hM _), ha_EW_const hM]
  have := ha_cost_lower_bound hM hw' (hws e')
  linarith [hmax e']

/-- **Proposition 14.B.1, "uniquely optimal"** (MWG, p. 481). If `v` is strictly concave, every
optimal contract `(e, w)` specifies an effort maximizing `∫ π f(π | e) dπ - v⁻¹(ū + g(e))` and pays
the fixed wage `w*(e)` at a set of profit levels of full measure (footnote 6). -/
theorem proposition_14_B_1_unique {M : HAModel ε} (hM : M.Standing)
    (hsc : StrictConcaveOn ℝ univ M.v) {wstar : ε → ℝ}
    (hws : ∀ e, M.v (wstar e) = M.ubar + M.g e) {e : ε} {w : ℝ → ℝ}
    (hopt : M.IsObsOptimal e w) :
    (∀ e', M.GP e' - wstar e' ≤ M.GP e - wstar e) ∧ ∀ᵐ x ∂M.ν, w x = wstar e := by
  have hcost : M.IsCostMin e w := by
    refine ⟨hopt.1, fun w' hw' => ?_⟩
    have := hopt.2 e w' hw'
    rw [ha_OP_eq hM hw'.1, ha_OP_eq hM hopt.1.1] at this
    linarith
  have hEW := (ha_costMin_binds hM hcost (hws e)).1
  refine ⟨fun e' => ?_, ha_costMin_unique hM hsc hcost (hws e)⟩
  have := hopt.2 e' _ (ha_fixed_wage_feasible hM (hws e')).1
  rw [ha_OP_eq hM (ha_const_adm hM _), ha_EW_const hM, ha_OP_eq hM hopt.1.1, hEW] at this
  exact this

/-- The owner can never do better when effort is unobservable than when it is observable
(MWG, p. 482, proof of Proposition 14.B.2; p. 484). -/
theorem ha_value_le_obs {M : HAModel ε} {e : ε} {w : ℝ → ℝ} (h : M.HAFeasible e w) :
    M.ObsFeasible e w := h.1

/-- **(14.B.6)-(14.B.8), Proposition 14.B.2** (MWG, pp. 482-483). With a risk-neutral manager
(`v(w) = w`), let `e*` solve (14.B.6) and `α* = ∫ π f(π | e*) dπ - g(e*) - ū`. The scheme
`w(π) = π - α*` ("selling the project") is incentive compatible for `e*`, gives the manager
exactly `ū`, gives the owner `α*` (the value of (14.B.6)), and is an optimal contract when
effort is unobservable. -/
theorem proposition_14_B_2 {M : HAModel ε} (hM : M.Standing) (hv : ∀ w, M.v w = w)
    {estar : ε} (hmax : ∀ e, M.GP e - M.g e - M.ubar ≤ M.GP estar - M.g estar - M.ubar) :
    let α := M.GP estar - M.g estar - M.ubar
    M.IsHAOptimal estar (fun x => x - α) ∧ M.EU estar (fun x => x - α) = M.ubar ∧
      M.OP estar (fun x => x - α) = α := by
  intro α
  have hadm : M.Adm (fun x => x - α) := by
    refine ⟨measurable_id.sub_const _, fun e => ?_⟩
    have h1 : Integrable (fun x => (x - α) * M.f e x) M.ν := by
      have : (fun x => (x - α) * M.f e x) = fun x => x * M.f e x - α * M.f e x := by
        funext x; ring
      rw [this]; exact (hM.x_int e).sub ((hM.f_int e).const_mul α)
    exact ⟨h1, by simpa only [hv] using h1⟩
  have hEW : ∀ e, M.EW e (fun x => x - α) = M.GP e - α := by
    intro e
    unfold EW GP
    have : (fun x => (x - α) * M.f e x) = fun x => x * M.f e x - α * M.f e x := by
      funext x; ring
    rw [this, integral_sub (hM.x_int e) ((hM.f_int e).const_mul α), integral_const_mul,
      hM.f_one, mul_one]
  have hEU : ∀ e, M.EU e (fun x => x - α) = M.GP e - α - M.g e := by
    intro e; unfold EU; rw [← hEW e]; unfold EV EW; simp only [hv]
  have hEUs : M.EU estar (fun x => x - α) = M.ubar := by rw [hEU]; ring
  have hOP : M.OP estar (fun x => x - α) = α := by
    rw [ha_OP_eq hM hadm, hEW]; ring
  refine ⟨⟨⟨⟨hadm, hEUs.ge⟩, fun e' => ?_⟩, fun e' w' hw' => ?_⟩, hEUs, hOP⟩
  · rw [hEU, hEU]; linarith [hmax e']
  · rw [hOP, ha_OP_eq hM hw'.1.1]
    have := ha_cost_lower_bound hM hw'.1 (hv (M.ubar + M.g e'))
    linarith [hmax e']

/-- **Proposition 14.B.2, "an optimal contract generates the same effort choice and expected
utilities"** (MWG, p. 482). With a risk-neutral manager, every optimal contract under
unobservable effort gives the owner the value of (14.B.6) and the manager exactly `ū`, and
implements an effort level solving (14.B.6). -/
theorem proposition_14_B_2_every {M : HAModel ε} (hM : M.Standing) (hv : ∀ w, M.v w = w)
    {estar : ε} (hmax : ∀ e, M.GP e - M.g e - M.ubar ≤ M.GP estar - M.g estar - M.ubar)
    {e : ε} {w : ℝ → ℝ} (hopt : M.IsHAOptimal e w) :
    M.OP e w = M.GP estar - M.g estar - M.ubar ∧ M.EU e w = M.ubar ∧
      ∀ e', M.GP e' - M.g e' - M.ubar ≤ M.GP e - M.g e - M.ubar := by
  obtain ⟨hsell, -, hOPs⟩ := proposition_14_B_2 hM hv hmax
  have h1 := hopt.2 _ _ hsell.1
  have h2 := hsell.2 e w hopt.1
  rw [hOPs] at h1 h2
  have hEU : M.EU e w = M.EW e w - M.g e := by unfold EU EV EW; simp only [hv]
  have hp := hopt.1.1.2
  rw [ha_OP_eq hM hopt.1.1.1] at h1 h2
  have hm := hmax e
  refine ⟨by rw [ha_OP_eq hM hopt.1.1.1]; linarith, by linarith, fun e' => ?_⟩
  linarith [hmax e']

end HAModel

end MWG.PrincipalAgent
