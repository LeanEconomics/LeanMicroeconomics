/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGAdverseSelection.ExercisesB
import MWGAdverseSelection.CondMeanMono
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Exercise 13.B.6: Wilson's model with heterogeneous firms

MWG, Exercise 13.B.6, p. 474 (based on Wilson 1980).

Firms differ in productivity: in a firm of type `γ` a worker of type `θ` produces `γθ`; each
firm wants at most one worker; firm types have a density `g > 0` on `[0, ∞)` (`FirmDensity`,
which also assumes `g` continuous, as part (b) allows: "all relevant functions are
differentiable"). The `N` firms are a continuum of mass `N` (so that aggregate demand is the
number `N ∫ g` of firms that want to hire, as in the book's formula).

* (a) `exercise_13_B_6a`: firm `γ` hires iff `γμ ≥ w` (`wil_hire_best`), so
  `z(w, μ) = N ∫_{w/μ}^∞ g(γ) dγ = N (1 - ∫_0^{w/μ} g)`.
* (b) `exercise_13_B_6b`: `z*(w) = z(w, μ(w))` has derivative
  `N g(w/μ) (wμ' - μ)/μ²` at `w̃`, positive iff the elasticity `w̃ μ'(w̃)/μ(w̃)` exceeds `1` (and
  negative iff it is below `1`). "Strictly increasing at `w̃`" is read as `z*'(w̃) > 0`.
* (c) `exercise_13_B_6c`: with `μ(w) = E[θ | r(θ) ≤ w]` and supply `s(w) = F(Θ(w))`, if
  `w₁ < w₂` are competitive equilibria (`z*(wᵢ) = s(wᵢ)`) then `μ(w₁) ≤ μ(w₂)`,
  `w₂/μ(w₂) ≤ w₁/μ(w₁)`, every firm's profit `max(γμ - w, 0)` and every worker's payoff
  `max(w, r(θ))` is weakly higher at `w₂`, and strictly higher for every worker with
  `r(θ) < w₂` (a set containing `θ̲`): the highest-wage equilibrium Pareto dominates.
* (d) The game (`WilsonEconomy.offerPay`, `WilsonEconomy.IsSPNE`): firms simultaneously offer
  wages (or stay out), workers accept the highest offer that is at least `r(θ)`, with random
  rationing among applicants. At a market-clearing common wage `w`, a firm that deviates to
  `w' > w` is the unique highest bidder and hires a random applicant from `Θ(w')` (expected
  productivity `μ(w')`), earning `γμ(w') - w'`; a firm offering `w' < w` finds no applicant
  (every type accepting `w'` is employed at `w`). `exercise_13_B_6d_i`: an SPNE wage is the
  highest competitive equilibrium wage. `exercise_13_B_6d_ii_necessary`: the book's condition
  `z*(w) ≤ z*(w*)` for `w > w*` is necessary.

Correction. The converse in (ii) is false: high-`γ` firms, which value quality more, deviate
to a higher wage whenever it raises `μ`, whatever happens to `z*`
(`exercise_13_B_6d_ii_counterexample`). The correct statement
(`exercise_13_B_6d_ii_corrected`): a competitive equilibrium `w*` is an SPNE iff
`μ(w) ≤ μ(w*)` for all `w > w*`; this holds, in particular, when `w* ≥ r(θ̄)`
(`exercise_13_B_6d_ii_full_employment`).

Added regularity (`WilsonEconomy.Valid`): `θ̲ > 0` (so `μ > 0`), `r` monotone on `[θ̲, θ̄]` and
`r(θ̲) ≥ 0` (so equilibrium wages are nonnegative).
-/

namespace MWG.AdverseSelection

open MeasureTheory

/-- **Exercise 13.B.6** (MWG, p. 474). The firm types have a continuous density `g` with
`g(γ) > 0` for `γ ∈ [0, ∞)`. -/
structure FirmDensity (g : ℝ → ℝ) : Prop where
  cont : Continuous g
  pos : ∀ γ, 0 ≤ γ → 0 < g γ
  integrable : IntegrableOn g (Set.Ici 0)
  total : ∫ γ in Set.Ici 0, g γ = 1

/-- **Exercise 13.B.6(a)** (MWG, p. 474). The firm types that hire at wage `w` when the average
productivity of the workers is `m`: `γm ≥ w`. -/
def wilHireSet (w m : ℝ) : Set ℝ := {γ | 0 ≤ γ ∧ w ≤ γ * m}

/-- **Exercise 13.B.6(a)** (MWG, p. 474). The aggregate demand for labor `z(w, m)`: the mass of
firms that hire. -/
noncomputable def wilDemand (N : ℝ) (g : ℝ → ℝ) (w m : ℝ) : ℝ := N * ∫ γ in wilHireSet w m, g γ

/-- The tail `∫_x^∞ g`. -/
noncomputable def wilTail (g : ℝ → ℝ) (x : ℝ) : ℝ := ∫ γ in Set.Ici x, g γ

/-- **Exercise 13.B.6(a)** (MWG, p. 474). A firm of type `γ` hiring one worker of average
productivity `m` at wage `w` earns `γm - w`: hiring is a best choice iff `w ≤ γm`, not hiring
iff `γm ≤ w`. -/
theorem wil_hire_best (γ m w : ℝ) :
    ((0 : ℝ) * (γ * m - w) ≤ 1 * (γ * m - w) ↔ w ≤ γ * m) ∧
      ((1 : ℝ) * (γ * m - w) ≤ 0 * (γ * m - w) ↔ γ * m ≤ w) := by
  constructor <;> constructor <;> intro h <;> linarith

theorem wilHireSet_eq {w m : ℝ} (hm : 0 < m) (hw : 0 ≤ w) : wilHireSet w m = Set.Ici (w / m) := by
  ext γ
  simp only [wilHireSet, Set.mem_ofPred_eq, Set.mem_Ici, div_le_iff₀ hm]
  constructor
  · rintro ⟨_, h⟩; exact h
  · intro h
    refine ⟨?_, h⟩
    by_contra hγ
    rw [not_le] at hγ
    nlinarith

theorem measurableSet_wilHireSet (w m : ℝ) : MeasurableSet (wilHireSet w m) :=
  (measurableSet_le measurable_const measurable_id).inter
    (measurableSet_le measurable_const (measurable_id.mul_const m))

theorem wilTail_split {g : ℝ → ℝ} (hg : FirmDensity g) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    wilTail g x = (∫ γ in x..y, g γ) + wilTail g y := by
  have hI : IntegrableOn g (Set.Ici x) := hg.integrable.mono_set (Set.Ici_subset_Ici.2 hx)
  unfold wilTail
  rw [← Set.Ico_union_Ici_eq_Ici hxy,
    setIntegral_union (s := Set.Ico x y) (t := Set.Ici y)
      (Set.disjoint_left.2 fun t ht ht' => not_le.2 ht.2 ht') measurableSet_Ici
      (hI.mono_set Set.Ico_subset_Ici_self) (hI.mono_set (Set.Ici_subset_Ici.2 hxy)),
    intervalIntegral.integral_of_le hxy, integral_Ico_eq_integral_Ioo,
    integral_Ioc_eq_integral_Ioo]

theorem wilTail_lt {g : ℝ → ℝ} (hg : FirmDensity g) {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) :
    wilTail g y < wilTail g x := by
  rw [wilTail_split hg hx hxy.le]
  have := intervalIntegral.intervalIntegral_pos_of_pos_on (hg.cont.intervalIntegrable x y)
    (fun t ht => hg.pos t (hx.trans ht.1.le)) hxy
  linarith

theorem wilTail_anti {g : ℝ → ℝ} (hg : FirmDensity g) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    wilTail g y ≤ wilTail g x := by
  rcases eq_or_lt_of_le hxy with h | h
  · rw [h]
  · exact (wilTail_lt hg hx h).le

theorem wilTail_nonneg {g : ℝ → ℝ} (hg : FirmDensity g) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ wilTail g x :=
  setIntegral_nonneg measurableSet_Ici fun γ hγ => (hg.pos γ (hx.trans hγ)).le

theorem wilTail_pos {g : ℝ → ℝ} (hg : FirmDensity g) {x : ℝ} (hx : 0 ≤ x) : 0 < wilTail g x :=
  (wilTail_nonneg hg (by linarith)).trans_lt (wilTail_lt hg hx (lt_add_one x))

/-- **Exercise 13.B.6(a)** (MWG, p. 474). For `μ > 0` and `w ≥ 0` the aggregate demand for labor
is `z(w, μ) = N ∫_{w/μ}^∞ g(γ) dγ = N (1 - ∫_0^{w/μ} g(γ) dγ)`. -/
theorem exercise_13_B_6a {N : ℝ} {g : ℝ → ℝ} (hg : FirmDensity g) {w m : ℝ} (hm : 0 < m)
    (hw : 0 ≤ w) :
    wilDemand N g w m = N * ∫ γ in Set.Ici (w / m), g γ ∧
      wilDemand N g w m = N * (1 - ∫ γ in (0 : ℝ)..(w / m), g γ) := by
  have h1 : wilDemand N g w m = N * wilTail g (w / m) := by
    rw [wilDemand, wilHireSet_eq hm hw]; rfl
  refine ⟨h1, ?_⟩
  have h2 := wilTail_split hg le_rfl (div_nonneg hw hm.le)
  rw [wilTail, hg.total] at h2
  rw [h1]
  congr 1
  linarith

/-- **Exercise 13.B.6(b)** (MWG, p. 474). If `μ(·)` is differentiable at `w̃ > 0` with
`μ(w̃) > 0`, then `z*(w) = z(w, μ(w))` has derivative `N g(w̃/μ) (w̃μ' - μ)/μ²` at `w̃`; it is
positive iff the elasticity `w̃μ'/μ` of `μ` exceeds `1`, and negative iff it is below `1`. -/
theorem exercise_13_B_6b {N : ℝ} {g μf : ℝ → ℝ} (hg : FirmDensity g) (hN : 0 < N) {w μ' : ℝ}
    (hw : 0 < w) (hμ : 0 < μf w) (hd : HasDerivAt μf μ' w) :
    HasDerivAt (fun x => wilDemand N g x (μf x))
        (N * g (w / μf w) * ((w * μ' - μf w) / μf w ^ 2)) w ∧
      (0 < N * g (w / μf w) * ((w * μ' - μf w) / μf w ^ 2) ↔ 1 < w * μ' / μf w) ∧
      (N * g (w / μf w) * ((w * μ' - μf w) / μf w ^ 2) < 0 ↔ w * μ' / μf w < 1) := by
  have hev : (fun x => N * (1 - ∫ γ in (0 : ℝ)..(x / μf x), g γ)) =ᶠ[nhds w]
      fun x => wilDemand N g x (μf x) := by
    filter_upwards [hd.continuousAt.eventually (lt_mem_nhds hμ), lt_mem_nhds hw] with x hx hx'
    exact ((exercise_13_B_6a hg hx hx'.le).2).symm
  have hq : HasDerivAt (fun x => x / μf x) ((1 * μf w - w * μ') / μf w ^ 2) w :=
    (hasDerivAt_id' w).div hd hμ.ne'
  have hG := (hg.cont.integral_hasStrictDerivAt 0 (w / μf w)).hasDerivAt.comp w hq
  have hz := (hG.const_sub 1).const_mul N
  have hgp : 0 < N * g (w / μf w) := mul_pos hN (hg.pos _ (div_nonneg hw.le hμ.le))
  have hsq : 0 < μf w ^ 2 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · refine (hz.congr_of_eventuallyEq hev.symm).congr_deriv ?_
    field_simp
    ring
  · rw [one_lt_div hμ, mul_pos_iff_of_pos_left hgp, div_pos_iff_of_pos_right hsq, sub_pos]
  · rw [div_lt_one hμ]
    constructor
    · intro h
      by_contra hle
      rw [not_lt] at hle
      have : 0 ≤ (w * μ' - μf w) / μf w ^ 2 := div_nonneg (by linarith) hsq.le
      nlinarith
    · intro h
      have : (w * μ' - μf w) / μf w ^ 2 < 0 := div_neg_of_neg_of_pos (by linarith) hsq
      nlinarith

/-- **Exercise 13.B.6** (MWG, p. 474). The economy: `N` firms with type density `g`, the worker
type distribution `F` on `[θ̲, θ̄]` and home production `r`. -/
structure WilsonEconomy where
  N : ℝ
  g : ℝ → ℝ
  F : Measure ℝ
  θl : ℝ
  θh : ℝ
  r : ℝ → ℝ

namespace WilsonEconomy

/-- **Exercise 13.B.6(b)** (MWG, p. 474). `μ(w) = E[θ | r(θ) ≤ w]`. -/
noncomputable def mu (E : WilsonEconomy) (w : ℝ) : ℝ := condMean E.F E.θl E.θh (acceptSet E.r w)

/-- **Exercise 13.B.6(b)** (MWG, p. 474). The aggregate demand function `z*(w) = z(w, μ(w))`. -/
noncomputable def zstar (E : WilsonEconomy) (w : ℝ) : ℝ := wilDemand E.N E.g w (E.mu w)

/-- **Exercise 13.B.6(c)** (MWG, p. 474). The aggregate supply `s(w) = F(r⁻¹(w))`, the
probability of `Θ(w) = {θ : r(θ) ≤ w}`. -/
noncomputable def supply (E : WilsonEconomy) (w : ℝ) : ℝ := (E.F (acceptSet E.r w)).toReal

/-- **Exercise 13.B.6(c)** (MWG, p. 474). A competitive equilibrium wage: `z*(w*) = s(w*)`. -/
def IsCE (E : WilsonEconomy) (w : ℝ) : Prop := E.zstar w = E.supply w

/-- **Exercise 13.B.6** (MWG, p. 474). The assumptions: `g` a firm density, `N > 0`, `F` a type
distribution, and (added) `θ̲ > 0`, `r` measurable and monotone on `[θ̲, θ̄]` with
`r(θ̲) ≥ 0`. -/
structure Valid (E : WilsonEconomy) : Prop where
  firms : FirmDensity E.g
  N_pos : 0 < E.N
  dist : TypeDist E.F E.θl E.θh
  θl_pos : 0 < E.θl
  meas : Measurable E.r
  mono : MonotoneOn E.r (Set.Icc E.θl E.θh)
  r_nonneg : 0 ≤ E.r E.θl

variable {E : WilsonEconomy}

theorem Valid.mu_pos (hE : E.Valid) (w : ℝ) : 0 < E.mu w :=
  hE.θl_pos.trans_le (condMean_ge hE.dist _)

theorem Valid.zstar_eq (hE : E.Valid) {w : ℝ} (hw : 0 ≤ w) :
    E.zstar w = E.N * wilTail E.g (w / E.mu w) := by
  rw [zstar, wilDemand, wilHireSet_eq (hE.mu_pos w) hw]; rfl

/-- The demand for labor is always positive. -/
theorem Valid.zstar_pos (hE : E.Valid) (w : ℝ) : 0 < E.zstar w := by
  have hm := hE.mu_pos w
  set c := max (w / E.mu w) 0
  have hsub : Set.Ici c ⊆ wilHireSet w (E.mu w) := fun γ hγ =>
    ⟨(le_max_right _ _).trans hγ, (div_le_iff₀ hm).1 ((le_max_left _ _).trans hγ)⟩
  have hI : IntegrableOn E.g (wilHireSet w (E.mu w)) :=
    hE.firms.integrable.mono_set fun γ hγ => hγ.1
  have hle := setIntegral_mono_set hI
    ((ae_restrict_iff' (measurableSet_wilHireSet _ _)).2
      (Filter.Eventually.of_forall fun γ hγ => (hE.firms.pos γ hγ.1).le))
    hsub.eventuallyLE
  have hpos : 0 < wilTail E.g c := wilTail_pos hE.firms (le_max_right _ _)
  unfold wilTail at hpos
  exact mul_pos hE.N_pos (hpos.trans_le hle)

/-- In a competitive equilibrium `w* ≥ r(θ̲)`: some types in `[θ̲, θ̄]` accept `w*`. -/
theorem Valid.ce_ge (hE : E.Valid) {w : ℝ} (h : E.IsCE w) : E.r E.θl ≤ w := by
  have hs : 0 < E.supply w := h ▸ hE.zstar_pos w
  have hpos : E.F (acceptSet E.r w) ≠ 0 := fun h0 => by simp [supply, h0] at hs
  obtain ⟨θ, hθA, hθI⟩ : (acceptSet E.r w ∩ Set.Icc E.θl E.θh).Nonempty := by
    by_contra hne
    exact hpos (measure_mono_null (fun θ hθ hθI => hne ⟨θ, hθ, hθI⟩) hE.dist.supp)
  exact (hE.mono ⟨le_rfl, hE.dist.lt.le⟩ hθI hθI.1).trans hθA

theorem Valid.ce_nonneg (hE : E.Valid) {w : ℝ} (h : E.IsCE w) : 0 ≤ w :=
  hE.r_nonneg.trans (hE.ce_ge h)

theorem Valid.supply_mono (hE : E.Valid) {w w' : ℝ} (hww : w ≤ w') :
    E.supply w ≤ E.supply w' := by
  have := hE.dist.prob
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono fun θ hθ => le_trans hθ hww)

/-- **Exercise 13.B.6(c)** (MWG, p. 474). If `w₁ < w₂` are competitive equilibrium wages, then
`μ(w₁) ≤ μ(w₂)` and `w₂/μ(w₂) ≤ w₁/μ(w₁)`; every firm's profit `max(γμ - w, 0)` and every
worker's payoff `max(w, r(θ))` is at least as high at `w₂`, and strictly higher for each worker
with `r(θ) < w₂`, in particular for `θ̲`. So the highest-wage equilibrium Pareto dominates. -/
theorem exercise_13_B_6c (hE : E.Valid) {w₁ w₂ : ℝ} (h₁ : E.IsCE w₁) (h₂ : E.IsCE w₂)
    (hlt : w₁ < w₂) :
    E.mu w₁ ≤ E.mu w₂ ∧ w₂ / E.mu w₂ ≤ w₁ / E.mu w₁ ∧
      (∀ γ, max (γ * E.mu w₁ - w₁) 0 ≤ max (γ * E.mu w₂ - w₂) 0) ∧
      (∀ θ, max w₁ (E.r θ) ≤ max w₂ (E.r θ)) ∧
      (∀ θ, E.r θ < w₂ → max w₁ (E.r θ) < max w₂ (E.r θ)) ∧ E.r E.θl < w₂ := by
  have hw₁ := hE.ce_ge h₁
  have hw₁0 := hE.ce_nonneg h₁
  have hw₂0 : 0 ≤ w₂ := by linarith
  have hm₁ := hE.mu_pos w₁
  have hm₂ := hE.mu_pos w₂
  have hmu : E.mu w₁ ≤ E.mu w₂ :=
    condMean_acceptSet_mono hE.dist hE.meas hE.mono hw₁ hlt.le
  have hratio : w₂ / E.mu w₂ ≤ w₁ / E.mu w₁ := by
    by_contra hgt
    rw [not_le] at hgt
    have hT := wilTail_lt hE.firms (div_nonneg hw₁0 hm₁.le) hgt
    have hz : E.zstar w₂ < E.zstar w₁ := by
      rw [hE.zstar_eq hw₁0, hE.zstar_eq hw₂0]
      exact mul_lt_mul_of_pos_left hT hE.N_pos
    have hs := hE.supply_mono hlt.le
    rw [h₁, h₂] at hz
    linarith
  refine ⟨hmu, hratio, fun γ => ?_, fun θ => max_le_max hlt.le le_rfl,
    fun θ hθ => ?_, lt_of_le_of_lt hw₁ hlt⟩
  · rcases le_or_gt (γ * E.mu w₁ - w₁) 0 with h | h
    · rw [max_eq_right h]; exact le_max_right _ _
    · rw [max_eq_left h.le]
      refine le_max_of_le_left ?_
      set a₁ := w₁ / E.mu w₁
      set a₂ := w₂ / E.mu w₂
      have e₁ : w₁ = a₁ * E.mu w₁ := by rw [div_mul_cancel₀ _ hm₁.ne']
      have e₂ : w₂ = a₂ * E.mu w₂ := by rw [div_mul_cancel₀ _ hm₂.ne']
      have hγ : a₁ ≤ γ := by
        by_contra hγ
        rw [not_le] at hγ
        nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hratio hm₂.le,
        mul_le_mul_of_nonneg_right hmu (sub_nonneg.2 hγ)]
  · rw [max_eq_left hθ.le]
    exact max_lt hlt hθ

/-- **Exercise 13.B.6(d)** (MWG, p. 474). The payoff of a firm of type `γ` that offers `w'` when
the other firms hire at the common market-clearing wage `w`: as the unique highest bidder
(`w' > w`) it hires a random applicant from `Θ(w')`; at `w' = w` it hires a random worker from
`Θ(w)`; below `w` no worker applies. Staying out gives `0`. -/
noncomputable def offerPay (E : WilsonEconomy) (γ w w' : ℝ) : ℝ :=
  if w < w' then γ * E.mu w' - w' else if w' = w then γ * E.mu w - w else 0

/-- **Exercise 13.B.6(d)** (MWG, p. 474). A (pure, common-wage) SPNE outcome of the wage-offer
game: the market clears at `w` (the firms with `γμ(w) ≥ w` hire, earning `max(γμ(w) - w, 0)`,
and all workers in `Θ(w)` are employed), and no firm gains by offering any other wage. Workers'
behaviour (accepting a highest offer that is at least `r(θ)`) is optimal by `worker_best`. -/
def IsSPNE (E : WilsonEconomy) (w : ℝ) : Prop :=
  E.IsCE w ∧ ∀ γ, 0 ≤ γ → ∀ w', E.offerPay γ w w' ≤ max (γ * E.mu w - w) 0

/-- If a higher wage `w'` attracts a better pool, a firm with a high enough `γ` gains by
offering it. -/
theorem Valid.deviation_of_mu_lt (hE : E.Valid) {w w' : ℝ} (hw : 0 ≤ w) (hww : w < w')
    (hμ : E.mu w < E.mu w') : ∃ γ, 0 ≤ γ ∧ max (γ * E.mu w - w) 0 < γ * E.mu w' - w' := by
  have hm' := hE.mu_pos w'
  set A := (w' - w) / (E.mu w' - E.mu w)
  set B := w' / E.mu w'
  have hA : 0 ≤ A := div_nonneg (by linarith) (by linarith)
  have hB : 0 ≤ B := div_nonneg (by linarith) hm'.le
  have eA : A * (E.mu w' - E.mu w) = w' - w := div_mul_cancel₀ _ (by linarith)
  have eB : B * E.mu w' = w' := div_mul_cancel₀ _ hm'.ne'
  refine ⟨A + B + 1, by linarith, max_lt ?_ ?_⟩
  · nlinarith [mul_nonneg hA hm'.le]
  · nlinarith [mul_nonneg hB (by linarith : (0 : ℝ) ≤ E.mu w' - E.mu w)]

/-- **Exercise 13.B.6(d)(i)** (MWG, p. 474). Only the highest-wage competitive equilibrium can
be an SPNE outcome: an SPNE wage is a competitive equilibrium wage at least as high as every
other one. -/
theorem exercise_13_B_6d_i (hE : E.Valid) {w : ℝ} (hw : E.IsSPNE w) :
    IsGreatest {x | E.IsCE x} w := by
  refine ⟨hw.1, fun w' hw' => ?_⟩
  by_contra hlt
  rw [Set.mem_ofPred_eq, not_le] at *
  obtain ⟨hmu, hratio, -⟩ := exercise_13_B_6c hE hw.1 hw' hlt
  have hw0 := hE.ce_nonneg hw.1
  rcases eq_or_lt_of_le hmu with heq | hμlt
  · rw [← heq] at hratio
    have := (div_le_div_iff_of_pos_right (hE.mu_pos w)).1 hratio
    linarith
  · obtain ⟨γ, hγ, hdev⟩ := hE.deviation_of_mu_lt hw0 hlt hμlt
    have := hw.2 γ hγ w'
    simp only [offerPay, hlt, ↓reduceIte] at this
    linarith

/-- **Exercise 13.B.6(d)(ii)** (MWG, p. 474), the true direction: if `w*` is an SPNE outcome then
`z*(w) ≤ z*(w*)` for all `w > w*` (otherwise a firm with `w/μ(w) < γ < w*/μ(w*)`, idle at `w*`,
profits from offering `w`). -/
theorem exercise_13_B_6d_ii_necessary (hE : E.Valid) {ws : ℝ} (h : E.IsSPNE ws) {w : ℝ}
    (hw : ws < w) : E.zstar w ≤ E.zstar ws := by
  by_contra hgt
  rw [not_le] at hgt
  have hws0 := hE.ce_nonneg h.1
  have hw0 : 0 ≤ w := by linarith
  have hm := hE.mu_pos w
  have hms := hE.mu_pos ws
  have hr : w / E.mu w < ws / E.mu ws := by
    by_contra hle
    rw [not_lt] at hle
    have hT := wilTail_anti hE.firms (div_nonneg hws0 hms.le) hle
    rw [hE.zstar_eq hw0, hE.zstar_eq hws0] at hgt
    nlinarith [hE.N_pos]
  set γ := (w / E.mu w + ws / E.mu ws) / 2
  have hγ0 : 0 ≤ γ := by
    have := div_nonneg hw0 hm.le
    have := div_nonneg hws0 hms.le
    positivity
  have h1 : 0 < γ * E.mu w - w := by
    have : w / E.mu w < γ := by simp only [γ]; linarith
    rw [div_lt_iff₀ hm] at this
    linarith
  have h2 : γ * E.mu ws - ws < 0 := by
    have : γ < ws / E.mu ws := by simp only [γ]; linarith
    rw [lt_div_iff₀ hms] at this
    linarith
  have := h.2 γ hγ0 w
  simp only [offerPay, hw, ↓reduceIte] at this
  rw [max_eq_right h2.le] at this
  linarith

/-- **Exercise 13.B.6(d)(ii)** (MWG, p. 474), corrected statement: a competitive equilibrium wage
`w*` is an SPNE outcome iff no higher wage attracts a better pool: `μ(w) ≤ μ(w*)` for all
`w > w*`. -/
theorem exercise_13_B_6d_ii_corrected (hE : E.Valid) {ws : ℝ} (hce : E.IsCE ws) :
    E.IsSPNE ws ↔ ∀ w, ws < w → E.mu w ≤ E.mu ws := by
  have hws0 := hE.ce_nonneg hce
  constructor
  · intro h w hw
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨γ, hγ, hdev⟩ := hE.deviation_of_mu_lt hws0 hw hlt
    have := h.2 γ hγ w
    simp only [offerPay, hw, ↓reduceIte] at this
    linarith
  · intro hmu
    refine ⟨hce, fun γ hγ w' => ?_⟩
    unfold offerPay
    split_ifs with h1 h2
    · have := mul_le_mul_of_nonneg_left (hmu w' h1) hγ
      exact le_max_of_le_left (by linarith)
    · exact le_max_left _ _
    · exact le_max_right _ _

/-- **Exercise 13.B.6(d)(ii)** (MWG, p. 474): a competitive equilibrium at which every type works
(`w* ≥ r(θ̄)`) is an SPNE outcome. -/
theorem exercise_13_B_6d_ii_full_employment (hE : E.Valid) {ws : ℝ} (hce : E.IsCE ws)
    (hfull : E.r E.θh ≤ ws) : E.IsSPNE ws := by
  have hall : ∀ w, ws ≤ w → E.mu w = meanType E.F := fun w hw =>
    condMean_of_superset hE.dist fun θ hθ =>
      ((hE.mono hθ ⟨hE.dist.lt.le, le_rfl⟩ hθ.2).trans hfull).trans hw
  refine (exercise_13_B_6d_ii_corrected hE hce).2 fun w hw => ?_
  rw [hall w hw.le, hall ws le_rfl]

end WilsonEconomy

/-! ### Concrete instances -/

/-- The exponential density `g(γ) = e^{-γ}`. -/
theorem expDensity : FirmDensity fun γ => Real.exp (-γ) where
  cont := Real.continuous_exp.comp continuous_neg
  pos γ _ := Real.exp_pos _
  integrable := (integrableOn_Ici_iff_integrableOn_Ioi).2 (integrableOn_exp_neg_Ioi 0)
  total := by rw [integral_Ici_eq_integral_Ioi, integral_exp_neg_Ioi_zero]

theorem wilTail_exp (x : ℝ) : wilTail (fun γ => Real.exp (-γ)) x = Real.exp (-x) := by
  rw [wilTail, integral_Ici_eq_integral_Ioi, integral_exp_neg_Ioi]

/-- Home production `r(θ) = 0` for `θ ≤ 3/2` and `R` above. -/
noncomputable def stepR (R : ℝ) (θ : ℝ) : ℝ := if θ ≤ 3 / 2 then 0 else R

/-- **Exercise 13.B.6**, the economy of the instances: types uniform on `[1, 2]`, home
production `stepR R`, firm density `e^{-γ}`, mass `N` of firms. -/
noncomputable def stepEconomy (N R : ℝ) : WilsonEconomy where
  N := N
  g := fun γ => Real.exp (-γ)
  F := unifMeas 1 2
  θl := 1
  θh := 2
  r := stepR R

theorem stepEconomy_valid {N R : ℝ} (hN : 0 < N) (hR : 0 ≤ R) : (stepEconomy N R).Valid where
  firms := expDensity
  N_pos := hN
  dist := unifMeas_typeDist zero_le_one one_lt_two
  θl_pos := one_pos
  meas := Measurable.ite measurableSet_Iic measurable_const measurable_const
  mono := by
    intro a _ b _ hab
    change stepR R a ≤ stepR R b
    unfold stepR
    split_ifs with h1 h2 <;> first | exact le_rfl | exact hR | linarith
  r_nonneg := by
    change (0 : ℝ) ≤ stepR R 1
    unfold stepR
    norm_num

theorem stepR_accept_low {R w : ℝ} (hw : 0 ≤ w) (hwR : w < R) :
    acceptSet (stepR R) w = Set.Iic (3 / 2) := by
  ext θ
  by_cases h : θ ≤ 3 / 2
  · simp [acceptSet, stepR, h, hw]
  · simp [acceptSet, stepR, h, not_le.2 hwR]

theorem stepR_accept_high {R w : ℝ} (hw : 0 ≤ w) (hRw : R ≤ w) :
    acceptSet (stepR R) w = Set.univ := by
  ext θ
  by_cases h : θ ≤ 3 / 2 <;> simp [acceptSet, stepR, h, hw, hRw]

theorem stepEconomy_mu_low {N R w : ℝ} (hw : 0 ≤ w) (hwR : w < R) :
    (stepEconomy N R).mu w = 5 / 4 := by
  change condMean (unifMeas 1 2) 1 2 (acceptSet (stepR R) w) = 5 / 4
  rw [stepR_accept_low hw hwR, exB_unif_condMean_Iic one_lt_two (by norm_num) (by norm_num)]
  norm_num

theorem stepEconomy_mu_high {N R w : ℝ} (hw : 0 ≤ w) (hRw : R ≤ w) :
    (stepEconomy N R).mu w = 3 / 2 := by
  change condMean (unifMeas 1 2) 1 2 (acceptSet (stepR R) w) = 3 / 2
  rw [stepR_accept_high hw hRw, condMean_of_superset (unifMeas_typeDist zero_le_one one_lt_two)
    (Set.subset_univ _), unifMeas_mean one_lt_two]
  norm_num

theorem stepEconomy_supply_low {N R w : ℝ} (hw : 0 ≤ w) (hwR : w < R) :
    (stepEconomy N R).supply w = 1 / 2 := by
  change (unifMeas 1 2 (acceptSet (stepR R) w)).toReal = 1 / 2
  rw [stepR_accept_low hw hwR, unifMeas_Iic one_lt_two (by norm_num) (by norm_num),
    ENNReal.toReal_ofReal (by norm_num)]
  norm_num

theorem stepEconomy_supply_high {N R w : ℝ} (hw : 0 ≤ w) (hRw : R ≤ w) :
    (stepEconomy N R).supply w = 1 := by
  have := unifMeas_isProb (a := 1) (b := 2) one_lt_two
  change (unifMeas 1 2 (acceptSet (stepR R) w)).toReal = 1
  rw [stepR_accept_high hw hRw, measure_univ, ENNReal.toReal_one]

theorem stepEconomy_zstar_low {N R w : ℝ} (hw : 0 ≤ w) (hwR : w < R) :
    (stepEconomy N R).zstar w = N * Real.exp (-(4 / 5 * w)) := by
  rw [WilsonEconomy.zstar, stepEconomy_mu_low hw hwR, wilDemand, wilHireSet_eq (by norm_num) hw]
  change N * wilTail (fun γ => Real.exp (-γ)) (w / (5 / 4)) = _
  rw [wilTail_exp]
  congr 2
  ring

theorem stepEconomy_zstar_high {N R w : ℝ} (hw : 0 ≤ w) (hRw : R ≤ w) :
    (stepEconomy N R).zstar w = N * Real.exp (-(2 / 3 * w)) := by
  rw [WilsonEconomy.zstar, stepEconomy_mu_high hw hRw, wilDemand,
    wilHireSet_eq (by norm_num) hw]
  change N * wilTail (fun γ => Real.exp (-γ)) (w / (3 / 2)) = _
  rw [wilTail_exp]
  congr 2
  ring

theorem exp_neg_log_two : Real.exp (-Real.log 2) = 1 / 2 := by
  rw [Real.exp_neg, Real.exp_log two_pos, one_div]

theorem log_two_bounds : 0 < Real.log 2 ∧ Real.log 2 < 6 / 5 :=
  ⟨Real.log_pos one_lt_two, (Real.log_le_sub_one_of_pos two_pos).trans_lt (by norm_num)⟩

/-- **Exercise 13.B.6(b)**, instances (MWG, p. 474). In `stepEconomy (e⁶) 9`, `μ` is constant
(`5/4`) near `w̃ = 1`: elasticity `0 < 1`, and `z*` is decreasing there. With `μ(w) = w²`
(elasticity `2 > 1`) and `g(γ) = e^{-γ}`, `z*` is increasing at `w̃ = 1`. -/
theorem exercise_13_B_6b_instance :
    HasDerivAt (fun x => wilDemand (Real.exp 6) (fun γ => Real.exp (-γ)) x
        ((stepEconomy (Real.exp 6) 9).mu x))
      (Real.exp 6 * Real.exp (-(1 / (5 / 4))) * ((1 * 0 - 5 / 4) / (5 / 4) ^ 2)) 1 ∧
      Real.exp 6 * Real.exp (-(1 / (5 / 4))) * ((1 * 0 - 5 / 4) / (5 / 4) ^ 2) < 0 ∧
      HasDerivAt (fun x => wilDemand 1 (fun γ => Real.exp (-γ)) x (x ^ 2))
        (1 * Real.exp (-(1 / 1 ^ 2)) * ((1 * 2 - 1 ^ 2) / (1 ^ 2) ^ 2)) 1 ∧
      0 < 1 * Real.exp (-(1 / 1 ^ 2)) * ((1 * 2 - 1 ^ 2) / (1 ^ 2) ^ 2) := by
  have hμ1 : (stepEconomy (Real.exp 6) 9).mu 1 = 5 / 4 :=
    stepEconomy_mu_low zero_le_one (by norm_num)
  have hd : HasDerivAt (stepEconomy (Real.exp 6) 9).mu 0 1 := by
    refine (hasDerivAt_const (1 : ℝ) (5 / 4 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds (zero_lt_one : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) < 9)]
      with x hx
    exact stepEconomy_mu_low hx.1.le hx.2
  have h1 := exercise_13_B_6b expDensity (Real.exp_pos 6) one_pos (by rw [hμ1]; norm_num) hd
  rw [hμ1] at h1
  have hd2 : HasDerivAt (fun x : ℝ => x ^ 2) 2 1 := by
    simpa using hasDerivAt_pow 2 (1 : ℝ)
  have h2 := exercise_13_B_6b expDensity one_pos one_pos (by norm_num) hd2
  refine ⟨h1.1, h1.2.2.2 (by norm_num), h2.1, h2.2.1.2 (by norm_num)⟩

/-- **Exercise 13.B.6(c)-(d)(i)**, instance (MWG, p. 474). In `stepEconomy (e⁶) 9` there are two
competitive equilibrium wages, `w₁ = 15/2 + (5/4) log 2` (only the types `θ ≤ 3/2` work) and
`w₂ = 9` (everybody works), and `9` is the highest; `9` Pareto dominates `w₁`, `9` is an SPNE
outcome and `w₁` is not. -/
theorem exercise_13_B_6_instance :
    (stepEconomy (Real.exp 6) 9).Valid ∧
      (stepEconomy (Real.exp 6) 9).IsCE (15 / 2 + 5 / 4 * Real.log 2) ∧
      (stepEconomy (Real.exp 6) 9).IsCE 9 ∧
      IsGreatest {x | (stepEconomy (Real.exp 6) 9).IsCE x} 9 ∧
      (stepEconomy (Real.exp 6) 9).mu (15 / 2 + 5 / 4 * Real.log 2) <
        (stepEconomy (Real.exp 6) 9).mu 9 ∧
      (stepEconomy (Real.exp 6) 9).IsSPNE 9 ∧
      ¬ (stepEconomy (Real.exp 6) 9).IsSPNE (15 / 2 + 5 / 4 * Real.log 2) := by
  have hE := stepEconomy_valid (Real.exp_pos 6) (by norm_num : (0 : ℝ) ≤ 9)
  obtain ⟨hl0, hl1⟩ := log_two_bounds
  have hw0 : 0 ≤ 15 / 2 + 5 / 4 * Real.log 2 := by linarith
  have hw9 : 15 / 2 + 5 / 4 * Real.log 2 < 9 := by linarith
  have hce1 : (stepEconomy (Real.exp 6) 9).IsCE (15 / 2 + 5 / 4 * Real.log 2) := by
    rw [WilsonEconomy.IsCE, stepEconomy_zstar_low hw0 hw9, stepEconomy_supply_low hw0 hw9,
      ← Real.exp_add, ← exp_neg_log_two]
    congr 1
    ring
  have hce9 : (stepEconomy (Real.exp 6) 9).IsCE 9 := by
    rw [WilsonEconomy.IsCE, stepEconomy_zstar_high (by norm_num) le_rfl,
      stepEconomy_supply_high (by norm_num) le_rfl, ← Real.exp_add]
    norm_num
  have hgr : IsGreatest {x | (stepEconomy (Real.exp 6) 9).IsCE x} 9 := by
    refine ⟨hce9, fun w hw => ?_⟩
    by_contra hlt
    rw [not_le] at hlt
    have h := hw
    rw [Set.mem_ofPred_eq, WilsonEconomy.IsCE, stepEconomy_zstar_high (by linarith) hlt.le,
      stepEconomy_supply_high (by linarith) hlt.le, ← Real.exp_add] at h
    have : Real.exp (6 + -(2 / 3 * w)) < Real.exp 0 := Real.exp_lt_exp.2 (by linarith)
    rw [Real.exp_zero] at this
    linarith
  have hspne : (stepEconomy (Real.exp 6) 9).IsSPNE 9 :=
    WilsonEconomy.exercise_13_B_6d_ii_full_employment hE hce9 (by
      change stepR 9 2 ≤ 9
      unfold stepR
      norm_num)
  refine ⟨hE, hce1, hce9, hgr, ?_, hspne, fun h => ?_⟩
  · rw [stepEconomy_mu_low hw0 hw9, stepEconomy_mu_high (by norm_num) le_rfl]
    norm_num
  · have := (WilsonEconomy.exercise_13_B_6d_i hE h).2 hce9
    linarith

/-- **Exercise 13.B.6(d)(ii)** (MWG, p. 474), counterexample to the "if" direction. In
`stepEconomy 1 3` the unique (hence highest) competitive equilibrium wage is
`w* = (5/4) log 2` and `z*(w) ≤ z*(w*)` for all `w > w*`, yet `w*` is not an SPNE outcome: at
`w = 3` the pool improves (`μ` rises from `5/4` to `3/2`), and firms with high `γ` deviate. -/
theorem exercise_13_B_6d_ii_counterexample :
    (stepEconomy 1 3).Valid ∧ IsGreatest {x | (stepEconomy 1 3).IsCE x} (5 / 4 * Real.log 2) ∧
      (∀ w, 5 / 4 * Real.log 2 < w →
        (stepEconomy 1 3).zstar w ≤ (stepEconomy 1 3).zstar (5 / 4 * Real.log 2)) ∧
      ¬ (stepEconomy 1 3).IsSPNE (5 / 4 * Real.log 2) := by
  have hE := stepEconomy_valid one_pos (by norm_num : (0 : ℝ) ≤ 3)
  obtain ⟨hl0, hl1⟩ := log_two_bounds
  have hw0 : 0 ≤ 5 / 4 * Real.log 2 := by linarith
  have hw3 : 5 / 4 * Real.log 2 < 3 := by linarith
  have hzs : (stepEconomy 1 3).zstar (5 / 4 * Real.log 2) = 1 / 2 := by
    rw [stepEconomy_zstar_low hw0 hw3, one_mul, ← exp_neg_log_two]
    congr 1
    ring
  have hce : (stepEconomy 1 3).IsCE (5 / 4 * Real.log 2) := by
    rw [WilsonEconomy.IsCE, hzs, stepEconomy_supply_low hw0 hw3]
  have he2 : Real.exp (-2) ≤ 1 / 2 := by
    rw [Real.exp_neg]
    have := Real.add_one_le_exp 2
    rw [one_div]
    exact inv_anti₀ two_pos (by linarith)
  refine ⟨hE, ⟨hce, fun w hw => ?_⟩, fun w hw => ?_, fun h => ?_⟩
  · have hw0' := hE.ce_nonneg hw
    rw [Set.mem_ofPred_eq, WilsonEconomy.IsCE] at hw
    rcases lt_or_ge w 3 with h3 | h3
    · rw [stepEconomy_zstar_low hw0' h3, stepEconomy_supply_low hw0' h3, one_mul,
        ← exp_neg_log_two] at hw
      have := Real.exp_injective hw
      linarith
    · rw [stepEconomy_zstar_high hw0' h3, stepEconomy_supply_high hw0' h3, one_mul] at hw
      have : Real.exp (-(2 / 3 * w)) < Real.exp 0 := Real.exp_lt_exp.2 (by linarith)
      rw [Real.exp_zero] at this
      linarith
  · rw [hzs]
    rcases lt_or_ge w 3 with h3 | h3
    · rw [stepEconomy_zstar_low (by linarith) h3, one_mul, ← exp_neg_log_two]
      exact Real.exp_le_exp.2 (by linarith)
    · rw [stepEconomy_zstar_high (by linarith) h3, one_mul]
      exact (Real.exp_le_exp.2 (by linarith)).trans he2
  · have := (WilsonEconomy.exercise_13_B_6d_ii_corrected hE hce).1 h 3 hw3
    rw [stepEconomy_mu_high (by norm_num) le_rfl, stepEconomy_mu_low hw0 hw3] at this
    norm_num at this

end MWG.AdverseSelection
