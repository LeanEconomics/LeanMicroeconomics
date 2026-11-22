/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGChoiceUnderUncertainty.ExercisesC5
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Exercises 6.C.17 (myopic portfolio choice) and 6.C.19 (CARA and normal returns)

MWG, pp. 212-213.

Exercise 6.C.17: with returns taking finitely many positive values, safe gross return `R > 0`,
and the fraction `α ∈ [0,1]` in the risky asset, wealth evolves as
`w_t = ((1 - α_{t-1})R + α_{t-1}x_t) w_{t-1}`. Under constant relative risk aversion
(`u(w) = w^{1-ρ}/(1-ρ)`, `ρ ≠ 1`, or `u = ln`) the period-1 problem at any wealth and the
period-0 problem (against the optimal period-1 value) have exactly the optimal fractions of
the one-period problem, so `α₀ = α₁` is optimal. Under constant absolute risk aversion the
optimal amount invested does not depend on wealth, so the optimal fraction does, and
`α₀ = α₁` fails whenever `w₁ ≠ w₀`.

Exercise 6.C.19: jointly normal returns are given through their moment generating function
`E[e^{t·z}] = e^{t·μ + t'Vt/2}` (which characterizes the multivariate normal law; a concrete
instance with Mathlib's `gaussianReal` is proved). The demand for the risky assets is
`α* = V⁻¹(μ - r1)/a`, the unique maximizer, and `w - ∑ α*` is held in the riskless asset.
-/

namespace MWG.ChoiceUnderUncertainty

open MeasureTheory ProbabilityTheory Filter Topology Set

variable {m : ℕ}

/-- The gross portfolio return `(1 - α)R + αx_i`. -/
def grossReturn (R : ℝ) (x : Fin m → ℝ) (α : ℝ) (i : Fin m) : ℝ := (1 - α) * R + α * x i

theorem grossReturn_pos {R : ℝ} (hR : 0 < R) {x : Fin m → ℝ} (hx : ∀ i, 0 < x i) {α : ℝ}
    (hα : α ∈ Icc (0 : ℝ) 1) (i : Fin m) : 0 < grossReturn R x α i := by
  unfold grossReturn
  rcases eq_or_lt_of_le hα.2 with h | h
  · rw [h]; simpa using hx i
  · have := hx i; nlinarith [hα.1]

/-- The CRRA utility `w^{1-ρ}/(1-ρ)`. -/
noncomputable def crra (ρ w : ℝ) : ℝ := w ^ (1 - ρ) / (1 - ρ)

/-- Expected CRRA utility of investing the fraction `α` of wealth `w`. -/
noncomputable def crraObjective (ρ : ℝ) (q : Fin m → ℝ) (R : ℝ) (x : Fin m → ℝ) (w α : ℝ) :
    ℝ :=
  ∑ i, q i * crra ρ (w * grossReturn R x α i)

/-- Homogeneity: `E u(w G) = w^{1-ρ} E u(G)`. -/
theorem crraObjective_homog {ρ : ℝ} (q : Fin m → ℝ) {R : ℝ} (hR : 0 < R) {x : Fin m → ℝ}
    (hx : ∀ i, 0 < x i) {w : ℝ} (hw : 0 < w) {α : ℝ} (hα : α ∈ Icc (0 : ℝ) 1) :
    crraObjective ρ q R x w α = w ^ (1 - ρ) * crraObjective ρ q R x 1 α := by
  unfold crraObjective crra
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.mul_rpow hw.le (grossReturn_pos hR hx hα i).le, one_mul]
  ring

/-- Scaling an objective by a positive constant preserves its maximizers. -/
theorem isMaxOn_const_mul_iff {f g : ℝ → ℝ} {S : Set ℝ} {c : ℝ} (hc : 0 < c)
    (h : ∀ β ∈ S, f β = c * g β) {α : ℝ} (hα : α ∈ S) : IsMaxOn f S α ↔ IsMaxOn g S α := by
  constructor
  · intro hm β hβ
    have := hm hβ
    simp only [mem_ofPred_eq, h β hβ, h α hα] at this
    exact le_of_mul_le_mul_left this hc
  · intro hm β hβ
    have := hm hβ
    simp only [mem_ofPred_eq] at this ⊢
    rw [h β hβ, h α hα]
    exact mul_le_mul_of_nonneg_left this hc.le

/-- **Exercise 6.C.17** (MWG, p. 212), period 1. Under CRRA the optimal fractions at any wealth
`w₁ > 0` are those of the one-period problem at unit wealth. -/
theorem exercise_6_C_17_period1 {ρ : ℝ} (q : Fin m → ℝ) {R : ℝ} (hR : 0 < R) {x : Fin m → ℝ}
    (hx : ∀ i, 0 < x i) {w : ℝ} (hw : 0 < w) {α : ℝ} (hα : α ∈ Icc (0 : ℝ) 1) :
    IsMaxOn (crraObjective ρ q R x w) (Icc 0 1) α ↔
      IsMaxOn (crraObjective ρ q R x 1) (Icc 0 1) α :=
  isMaxOn_const_mul_iff (Real.rpow_pos_of_pos hw _)
    (fun _ hβ => crraObjective_homog q hR hx hw hβ) hα

/-- The one-period CRRA objective is continuous on `[0, 1]`. -/
theorem crraObjective_continuousOn (ρ : ℝ) (q : Fin m → ℝ) {R : ℝ} (hR : 0 < R)
    {x : Fin m → ℝ} (hx : ∀ i, 0 < x i) : ContinuousOn (crraObjective ρ q R x 1) (Icc 0 1) := by
  unfold crraObjective crra
  apply continuousOn_finsetSum
  intro i _
  apply ContinuousOn.mul continuousOn_const
  apply ContinuousOn.div_const
  apply ContinuousOn.rpow_const (by unfold grossReturn; fun_prop)
  intro α hα
  left
  rw [one_mul]
  exact (grossReturn_pos hR hx hα i).ne'

/-- The optimal period-1 value `V₁(w) = max_α E u(w G_α)`. -/
noncomputable def crraValue (ρ : ℝ) (q : Fin m → ℝ) (R : ℝ) (x : Fin m → ℝ) (w : ℝ) : ℝ :=
  sSup (crraObjective ρ q R x w '' Icc 0 1)

/-- **Exercise 6.C.17** (MWG, p. 212), period 0. Under CRRA (`ρ ≠ 1`), with probabilities
`q_i ≥ 0` summing to one, the fraction `α₀` maximizes the period-0 objective
`E[V₁((1 - α₀)R + α₀x₁) w₀]` iff it maximizes the one-period problem; together with
`exercise_6_C_17_period1`, the individual optimally sets `α₀ = α₁`. -/
theorem exercise_6_C_17_period0 {ρ : ℝ} (hρ : ρ ≠ 1) {q : Fin m → ℝ} (hq : ∀ i, 0 ≤ q i)
    (hq1 : ∑ i, q i = 1) {R : ℝ} (hR : 0 < R) {x : Fin m → ℝ} (hx : ∀ i, 0 < x i) {w₀ : ℝ}
    (hw₀ : 0 < w₀) {α : ℝ} (hα : α ∈ Icc (0 : ℝ) 1) :
    IsMaxOn (fun a => ∑ i, q i * crraValue ρ q R x (w₀ * grossReturn R x a i)) (Icc 0 1) α ↔
      IsMaxOn (crraObjective ρ q R x 1) (Icc 0 1) α := by
  have h1ρ : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ)
  obtain ⟨αs, hαs, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨0, le_rfl, zero_le_one⟩
    (crraObjective_continuousOn ρ q hR hx)
  set J := crraObjective ρ q R x 1
  -- `V₁(w) = w^{1-ρ} J(αs)`
  have hV (w : ℝ) (hw : 0 < w) : crraValue ρ q R x w = w ^ (1 - ρ) * J αs := by
    apply IsGreatest.csSup_eq
    refine ⟨⟨αs, hαs, crraObjective_homog q hR hx hw hαs⟩, ?_⟩
    rintro _ ⟨β, hβ, rfl⟩
    rw [crraObjective_homog q hR hx hw hβ]
    exact mul_le_mul_of_nonneg_left (hmax hβ) (Real.rpow_nonneg hw.le _)
  -- `(1 - ρ) J(β) > 0`
  have hpos (β : ℝ) (hβ : β ∈ Icc (0 : ℝ) 1) : 0 < (1 - ρ) * J β := by
    simp only [J, crraObjective, crra, one_mul, Finset.mul_sum]
    have hterm (i : Fin m) : (1 - ρ) * (q i * (grossReturn R x β i ^ (1 - ρ) / (1 - ρ))) =
        q i * grossReturn R x β i ^ (1 - ρ) := by field_simp
    simp only [hterm]
    obtain ⟨i, hi⟩ : ∃ i, 0 < q i := by
      by_contra hcon
      push Not at hcon
      have : ∑ i, q i ≤ 0 := Finset.sum_nonpos fun i _ => hcon i
      linarith
    exact lt_of_lt_of_le (mul_pos hi (Real.rpow_pos_of_pos (grossReturn_pos hR hx hβ i) _))
      (Finset.single_le_sum (fun j _ => mul_nonneg (hq j)
        (Real.rpow_nonneg (grossReturn_pos hR hx hβ j).le _)) (Finset.mem_univ i))
  set K := (1 - ρ) * J αs * w₀ ^ (1 - ρ)
  have hK : 0 < K := mul_pos (hpos αs hαs) (Real.rpow_pos_of_pos hw₀ _)
  apply isMaxOn_const_mul_iff hK _ hα
  intro β hβ
  have hG (i : Fin m) := grossReturn_pos hR hx hβ i
  simp only [J]
  rw [show ∑ i, q i * crraValue ρ q R x (w₀ * grossReturn R x β i) =
      ∑ i, q i * ((w₀ * grossReturn R x β i) ^ (1 - ρ) * J αs) from
    Finset.sum_congr rfl fun i _ => by rw [hV _ (mul_pos hw₀ (hG i))]]
  simp only [K, crraObjective, crra, one_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.mul_rpow hw₀.le (hG i).le]
  field_simp

/-- Expected CARA utility of investing the fraction `α` of wealth `w`. -/
noncomputable def caraObjective (k : ℝ) (q : Fin m → ℝ) (R : ℝ) (x : Fin m → ℝ) (w α : ℝ) : ℝ :=
  ∑ i, q i * -Real.exp (-k * (w * grossReturn R x α i))

/-- Expected CARA utility of investing the amount `A`, net of the safe wealth. -/
noncomputable def caraAmount (k : ℝ) (q : Fin m → ℝ) (R : ℝ) (x : Fin m → ℝ) (A : ℝ) : ℝ :=
  ∑ i, q i * -Real.exp (-k * (A * (x i - R)))

/-- Under CARA, `E u(w G_α) = e^{-kwR} E u(αw(x - R))`: the problem in amounts does not depend
on wealth. -/
theorem caraObjective_eq (k : ℝ) (q : Fin m → ℝ) (R : ℝ) (x : Fin m → ℝ) (w α : ℝ) :
    caraObjective k q R x w α = Real.exp (-k * w * R) * caraAmount k q R x (α * w) := by
  unfold caraObjective caraAmount grossReturn
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show -k * (w * ((1 - α) * R + α * x i)) = -k * w * R + -k * (α * w * (x i - R)) by ring,
    Real.exp_add]
  ring

/-- **Exercise 6.C.17** (MWG, p. 212), CARA. Myopia fails: if the amount problem has a unique
maximizer `A₀ > 0` on `[0, W]` with `A₀ ≤ min(w, w')` and `max(w, w') ≤ W`, then the optimal
fractions at two different wealth levels `w ≠ w'` differ (they are `A₀/w` and `A₀/w'`). -/
theorem exercise_6_C_17_cara {k : ℝ} (q : Fin m → ℝ) (R : ℝ) (x : Fin m → ℝ) {A₀ W w w' α α' : ℝ}
    (hA : 0 < A₀) (hw : A₀ ≤ w) (hw' : A₀ ≤ w') (hW : w ≤ W) (hW' : w' ≤ W)
    (huniq : ∀ A ∈ Icc 0 W, caraAmount k q R x A ≤ caraAmount k q R x A₀ ∧
      (caraAmount k q R x A = caraAmount k q R x A₀ → A = A₀))
    (hα : α ∈ Icc (0 : ℝ) 1) (hα' : α' ∈ Icc (0 : ℝ) 1)
    (hopt : IsMaxOn (caraObjective k q R x w) (Icc 0 1) α)
    (hopt' : IsMaxOn (caraObjective k q R x w') (Icc 0 1) α') (hne : w ≠ w') : α ≠ α' := by
  have hw0 : 0 < w := hA.trans_le hw
  have hw0' : 0 < w' := hA.trans_le hw'
  have amount (v a : ℝ) (hv : 0 < v) (hvA : A₀ ≤ v) (hvW : v ≤ W) (ha : a ∈ Icc (0 : ℝ) 1)
      (ho : IsMaxOn (caraObjective k q R x v) (Icc 0 1) a) : a * v = A₀ := by
    have hA0 : A₀ / v ∈ Icc (0 : ℝ) 1 := ⟨by positivity, (div_le_one hv).mpr hvA⟩
    have := ho hA0
    simp only [mem_ofPred_eq, caraObjective_eq] at this
    rw [div_mul_cancel₀ _ hv.ne'] at this
    have h1 := le_of_mul_le_mul_left this (Real.exp_pos _)
    have haW : a * v ∈ Icc 0 W := ⟨mul_nonneg ha.1 hv.le,
      (mul_le_of_le_one_left hv.le ha.2).trans hvW⟩
    exact (huniq _ haW).2 (le_antisymm (huniq _ haW).1 h1)
  have e1 := amount w α hw0 hw hW hα hopt
  have e2 := amount w' α' hw0' hw' hW' hα' hopt'
  intro heq
  rw [heq] at e1
  apply hne
  have : α' * (w - w') = 0 := by linarith
  rcases mul_eq_zero.mp this with h | h
  · rw [h, zero_mul] at e2; linarith
  · linarith

/-- Adding a constant preserves maximizers. -/
theorem isMaxOn_add_const_iff {f g : ℝ → ℝ} {S : Set ℝ} {c : ℝ} (h : ∀ β ∈ S, f β = c + g β)
    {α : ℝ} (hα : α ∈ S) : IsMaxOn f S α ↔ IsMaxOn g S α := by
  constructor
  · intro hm β hβ
    have := hm hβ
    simp only [mem_ofPred_eq, h β hβ, h α hα] at this ⊢
    linarith
  · intro hm β hβ
    have := hm hβ
    simp only [mem_ofPred_eq] at this ⊢
    rw [h β hβ, h α hα]
    linarith

/-- Expected logarithmic utility (constant relative risk aversion `1`). -/
noncomputable def logObjective (q : Fin m → ℝ) (R : ℝ) (x : Fin m → ℝ) (w α : ℝ) : ℝ :=
  ∑ i, q i * Real.log (w * grossReturn R x α i)

theorem logObjective_shift {q : Fin m → ℝ} (hq1 : ∑ i, q i = 1) {R : ℝ} (hR : 0 < R)
    {x : Fin m → ℝ} (hx : ∀ i, 0 < x i) {w : ℝ} (hw : 0 < w) {α : ℝ} (hα : α ∈ Icc (0 : ℝ) 1) :
    logObjective q R x w α = Real.log w + logObjective q R x 1 α := by
  unfold logObjective
  have e (i : Fin m) : q i * Real.log (w * grossReturn R x α i) =
      q i * Real.log w + q i * Real.log (1 * grossReturn R x α i) := by
    rw [Real.log_mul hw.ne' (grossReturn_pos hR hx hα i).ne', one_mul]; ring
  simp only [e, Finset.sum_add_distrib, ← Finset.sum_mul, hq1, one_mul]

/-- **Exercise 6.C.17** (MWG, p. 212), logarithmic utility. With `u = ln` the optimal fractions
in period 1 at any wealth, and in period 0 against the optimal period-1 value, are those of
the one-period problem. -/
theorem exercise_6_C_17_log {q : Fin m → ℝ} (hq1 : ∑ i, q i = 1) {R : ℝ} (hR : 0 < R)
    {x : Fin m → ℝ} (hx : ∀ i, 0 < x i) {w₀ : ℝ} (hw₀ : 0 < w₀) {α : ℝ}
    (hα : α ∈ Icc (0 : ℝ) 1) (hcont : ContinuousOn (logObjective q R x 1) (Icc 0 1)) :
    (∀ w > 0, IsMaxOn (logObjective q R x w) (Icc 0 1) α ↔
      IsMaxOn (logObjective q R x 1) (Icc 0 1) α) ∧
    (IsMaxOn (fun a => ∑ i, q i * sSup (logObjective q R x (w₀ * grossReturn R x a i) ''
      Icc 0 1)) (Icc 0 1) α ↔ IsMaxOn (logObjective q R x 1) (Icc 0 1) α) := by
  refine ⟨fun w hw => isMaxOn_add_const_iff (fun β hβ => logObjective_shift hq1 hR hx hw hβ) hα,
    ?_⟩
  obtain ⟨αs, hαs, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨0, le_rfl, zero_le_one⟩ hcont
  have hV (w : ℝ) (hw : 0 < w) : sSup (logObjective q R x w '' Icc 0 1) =
      Real.log w + logObjective q R x 1 αs := by
    apply IsGreatest.csSup_eq
    refine ⟨⟨αs, hαs, logObjective_shift hq1 hR hx hw hαs⟩, ?_⟩
    rintro _ ⟨β, hβ, rfl⟩
    rw [logObjective_shift hq1 hR hx hw hβ]
    have := hmax hβ
    simp only [mem_ofPred_eq] at this
    linarith
  apply isMaxOn_add_const_iff (c := Real.log w₀ + logObjective q R x 1 αs) _ hα
  intro β hβ
  have hG (i : Fin m) := grossReturn_pos hR hx hβ i
  rw [show ∑ i, q i * sSup (logObjective q R x (w₀ * grossReturn R x β i) '' Icc 0 1) =
      ∑ i, q i * (Real.log (w₀ * grossReturn R x β i) + logObjective q R x 1 αs) from
    Finset.sum_congr rfl fun i _ => by rw [hV _ (mul_pos hw₀ (hG i))]]
  have e (i : Fin m) : q i * (Real.log (w₀ * grossReturn R x β i) + logObjective q R x 1 αs) =
      q i * (Real.log w₀ + logObjective q R x 1 αs) +
        q i * Real.log (1 * grossReturn R x β i) := by
    rw [Real.log_mul hw₀.ne' (hG i).ne', one_mul]; ring
  simp only [e, Finset.sum_add_distrib, ← Finset.sum_mul, hq1, one_mul]
  simp only [logObjective, one_mul]

/-- The expected CARA utility of holding `α` (amounts) in risky assets with returns `z` and
`w - ∑ α` in the riskless asset with return `r`. -/
noncomputable def caraPortfolioEU {N : ℕ} (a w r : ℝ) (ρ : Measure (Fin N → ℝ))
    (α : Fin N → ℝ) : ℝ :=
  ∫ z, -Real.exp (-a * ((w - ∑ n, α n) * r + α ⬝ᵥ z)) ∂ρ

/-- The certainty-equivalent index `wr + α · (μ - r1) - (a/2) α'Vα`. -/
noncomputable def caraCE {N : ℕ} (a w r : ℝ) (μ : Fin N → ℝ) (V : Matrix (Fin N) (Fin N) ℝ)
    (α : Fin N → ℝ) : ℝ :=
  w * r + α ⬝ᵥ (μ - fun _ => r) - a / 2 * (α ⬝ᵥ (V.mulVec α))

/-- With normal returns (given by their moment generating function), expected CARA utility is
`-exp(-a · CE(α))`. -/
theorem caraPortfolioEU_eq {N : ℕ} {a w r : ℝ} {ρ : Measure (Fin N → ℝ)} {μ : Fin N → ℝ}
    {V : Matrix (Fin N) (Fin N) ℝ}
    (hmgf : ∀ t : Fin N → ℝ, ∫ z, Real.exp (t ⬝ᵥ z) ∂ρ = Real.exp (t ⬝ᵥ μ + t ⬝ᵥ (V.mulVec t) / 2))
    (α : Fin N → ℝ) : caraPortfolioEU a w r ρ α = -Real.exp (-a * caraCE a w r μ V α) := by
  unfold caraPortfolioEU caraCE
  have e (z : Fin N → ℝ) : -Real.exp (-a * ((w - ∑ n, α n) * r + α ⬝ᵥ z)) =
      -Real.exp (-a * ((w - ∑ n, α n) * r)) * Real.exp ((-a • α) ⬝ᵥ z) := by
    rw [show -a * ((w - ∑ n, α n) * r + α ⬝ᵥ z) = -a * ((w - ∑ n, α n) * r) + (-a • α) ⬝ᵥ z by
      rw [smul_dotProduct, smul_eq_mul]; ring, Real.exp_add]
    ring
  simp only [e]
  rw [integral_const_mul, hmgf, neg_mul, ← Real.exp_add]
  congr 2
  simp only [smul_dotProduct, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, dotProduct_sub]
  have hs : α ⬝ᵥ (fun _ => r) = (∑ n, α n) * r := by
    simp [dotProduct, Finset.sum_mul]
  rw [hs]
  ring

/-- **Exercise 6.C.19** (MWG, pp. 212-213). With `u(x) = -e^{-ax}`, `a > 0`, riskless return
`r` and jointly normal risky returns with mean `μ` and positive definite covariance `V`, the
risky demand `α*` solving `aVα* = μ - r1` (i.e. `α* = V⁻¹(μ - r1)/a`) is the unique optimal
portfolio; the riskless demand is `w - ∑ α*`. -/
theorem exercise_6_C_19 {N : ℕ} {a w r : ℝ} (ha : 0 < a) {ρ : Measure (Fin N → ℝ)}
    {μ : Fin N → ℝ} {V : Matrix (Fin N) (Fin N) ℝ} (hV : V.PosDef)
    (hmgf : ∀ t : Fin N → ℝ, ∫ z, Real.exp (t ⬝ᵥ z) ∂ρ = Real.exp (t ⬝ᵥ μ + t ⬝ᵥ (V.mulVec t) / 2))
    {αs : Fin N → ℝ} (hαs : a • (V.mulVec αs) = μ - fun _ => r) :
    ∀ α, caraPortfolioEU a w r ρ α ≤ caraPortfolioEU a w r ρ αs ∧
      (caraPortfolioEU a w r ρ α = caraPortfolioEU a w r ρ αs → α = αs) := by
  have hsym (x y : Fin N → ℝ) : x ⬝ᵥ (V.mulVec y) = y ⬝ᵥ (V.mulVec x) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm]
    congr 2
    have := hV.1
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
    exact this
  have key (α : Fin N → ℝ) : caraCE a w r μ V αs - caraCE a w r μ V α =
      a / 2 * ((α - αs) ⬝ᵥ (V.mulVec (α - αs))) := by
    unfold caraCE
    rw [← hαs]
    simp only [dotProduct_smul, smul_eq_mul, Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct,
      hsym αs α]
    ring
  intro α
  rw [caraPortfolioEU_eq hmgf, caraPortfolioEU_eq hmgf]
  have hq : 0 ≤ (α - αs) ⬝ᵥ (V.mulVec (α - αs)) := by
    by_cases h : α - αs = 0
    · rw [h]; simp
    · exact (hV.dotProduct_mulVec_pos h).le
  constructor
  · have : caraCE a w r μ V α ≤ caraCE a w r μ V αs := by
      have := key α; nlinarith
    simp only [neg_le_neg_iff, Real.exp_le_exp]
    nlinarith
  · intro heq
    have h1 : caraCE a w r μ V α = caraCE a w r μ V αs := by
      have := Real.exp_injective (neg_injective heq)
      have := mul_left_cancel₀ (neg_ne_zero.mpr ha.ne') this
      exact this
    by_contra hne
    have hpos := hV.dotProduct_mulVec_pos (sub_ne_zero.mpr hne)
    simp only [star_trivial] at hpos
    have := key α
    rw [h1, sub_self] at this
    nlinarith

/-- **Exercise 6.C.19**: existence and uniqueness of the solution `α* = V⁻¹(μ - r1)/a`. -/
theorem exercise_6_C_19_exists {N : ℕ} {a r : ℝ} (ha : 0 < a) {μ : Fin N → ℝ}
    {V : Matrix (Fin N) (Fin N) ℝ} (hV : V.PosDef) :
    ∃! αs : Fin N → ℝ, a • (V.mulVec αs) = μ - fun _ => r := by
  have hu : IsUnit V := hV.isUnit
  refine ⟨a⁻¹ • (V⁻¹.mulVec (μ - fun _ => r)), ?_, fun β hβ => ?_⟩
  · change a • V.mulVec (a⁻¹ • V⁻¹.mulVec (μ - fun _ => r)) = μ - fun _ => r
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det V).mp hu), Matrix.one_mulVec, smul_smul,
      mul_inv_cancel₀ ha.ne', one_smul]
  · have hinj := Matrix.mulVec_injective_iff_isUnit.mpr hu
    apply hinj
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det V).mp hu), Matrix.one_mulVec, ← hβ, smul_smul,
      inv_mul_cancel₀ ha.ne', one_smul]

/-- A concrete instance of the normality hypothesis of Exercise 6.C.19: one risky asset with a
Gaussian return of mean `m` and variance `v > 0`. -/
theorem exercise_6_C_19_instance (m : ℝ) (v : NNReal) :
    ∀ t : Fin 1 → ℝ, ∫ z, Real.exp (t ⬝ᵥ z) ∂((gaussianReal m v).map fun x => fun _ => x) =
      Real.exp (t ⬝ᵥ (fun _ => m) + t ⬝ᵥ ((Matrix.of fun _ _ => (v : ℝ)).mulVec t) / 2) := by
  intro t
  rw [integral_map (by fun_prop) (by fun_prop)]
  have h := congrFun (mgf_id_gaussianReal (μ := m) (v := v)) (t 0)
  simp only [mgf, id] at h
  simp only [dotProduct, Fin.sum_univ_one, Matrix.mulVec, Matrix.of_apply]
  rw [show (fun x : ℝ => Real.exp (t 0 * x)) = fun x => Real.exp (t 0 * x) from rfl, h]
  congr 1
  ring

end MWG.ChoiceUnderUncertainty
