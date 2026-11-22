/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMechanismDesign.RevenueEquivalence
import MWGMechanismDesign.MultipleEquilibria

/-!
# The Myerson-Satterthwaite theorem

MWG, Section 23.E, pp. 891-897, and Exercises 23.E.1, 23.E.2, 23.E.3, 23.E.7 (pp. 921-923).

Bilateral trade: agent `0` is the seller, agent `1` the buyer, `uᵢ = θᵢyᵢ + tᵢ` (`allocV`),
`yᵢ(θ)` the probability that `i` ends up with the good, types independent (`P = ∏ᵢ μᵢ`) on
`Θ = [θ̲₀, θ̄₀] × [θ̲₁, θ̄₁]` (`InTypes`). All requirements are imposed on `Θ` only:
ex post efficiency (`ExPostEfficientTrade`: `y₀ + y₁ = 1`, `y₁ ∈ [0, 1]`, trade iff `θ₁ > θ₀`,
ties free) with budget balance (`BudgetBalancedOn`), Bayesian incentive compatibility
(`BayesianICOn`, from `LinearBIC`), interim individual rationality (23.E.2) (`InterimIR`:
`U₀(θ₀) ≥ θ₀`, `U₁(θ₁) ≥ 0`).

* **Proposition 23.E.1** for general type distributions (`proposition_23_E_1_general`: each `μᵢ`
  concentrated on `[θ̲ᵢ, θ̄ᵢ]` with positive mass on open subintervals) and as stated, with
  strictly positive densities (`proposition_23_E_1`). Footnote 41: `footnote_23_41`.
* The proof departs from MWG's (23.E.4)-(23.E.7): `ms_core` compares `f` with the rule
  `t₀ = θ₁y₁`, `t₁ = -θ₀y₁` (dominant strategy incentive compatible, `ms_vcg_bic`); by
  Proposition 23.D.2 the interim transfers differ by constants, budget balance and individual
  rationality at `θ̄₀`, `θ̲₁` give `E[(θ₁ - θ₀)⁺] ≤ E[(θ₁ - θ̄₀)⁺] + E[(θ̲₁ - θ₀)⁺]`, which fails
  because of a strict pointwise inequality on a box of positive probability in the overlap.
* Non-vacuity (uniform types on `[0, 1]`), one instance per dropped requirement:
  without individual rationality the expected externality mechanism (`exercise_23_E_1`); without
  budget balance the comparison rule (`proposition_23_E_1_instance_no_bb`); without efficiency
  the posted price `1/2` (`proposition_23_E_1_instance_no_eff`); without incentive compatibility
  split-the-difference (`proposition_23_E_1_instance_no_bic`).
* p. 894: ex post IR implies interim IR (`ms_interimIR_of_exPostIR`); dominant strategy IC
  implies Bayesian IC (`ms_bic_of_dsic`).
* Exercise 23.E.1: in the expected externality mechanism with uniform types the seller of type
  `1` gets `U₀(1) = 2/3 < 1`. Exercise 23.E.2(a), (b) (`exercise_23_E_2a`, `exercise_23_E_2b`).
  Exercise 23.E.3: a two-type example with a Bayesian incentive compatible, ex post efficient,
  ex post individually rational social choice function (`exercise_23_E_3`). Exercise 23.E.7:
  (a) `≥ 5/6`, (b) `≤ 2/3 = E[max(θ₀, θ₁)]`, together M-S for uniform types.

**Corrections.** Exercise 23.E.2(a), (b) as printed omit ex post efficiency and are then false:
the no-trade rule is dominant strategy incentive compatible, budget balanced and ex post
individually rational (`exercise_23_E_2_literal_false`); with ex post efficiency they follow
from Proposition 23.E.1. In Exercise 23.E.7(a) "ex post efficient" must mean the trading rule
only (no budget balance): with budget balance no such `f` exists (Proposition 23.E.1) and (a)
would be vacuous. Footnote 41's equivalence needs nondegenerate intervals.
-/

namespace MWG.MechanismDesign

open MeasureTheory Function

/-- The type space `Θ = [θ̲₀, θ̄₀] × [θ̲₁, θ̄₁]` of the bilateral trade setting (MWG, p. 894);
agent `0` is the seller and agent `1` the buyer. -/
def InTypes (lo hi : Fin 2 → ℝ) (θ : Fin 2 → ℝ) : Prop := ∀ i, θ i ∈ Set.Icc (lo i) (hi i)

/-- Ex post efficiency in the bilateral trade setting (MWG, pp. 862, 895): on `Θ`, the good is
always held by someone (`y₀ + y₁ = 1`, with `y₁ ∈ [0, 1]` a probability), the buyer gets it when
`θ₁ > θ₀` and the seller keeps it when `θ₁ < θ₀`. -/
def ExPostEfficientTrade (lo hi : Fin 2 → ℝ) (y : (Fin 2 → ℝ) → Fin 2 → ℝ) : Prop :=
  ∀ θ, InTypes lo hi θ → y θ 0 + y θ 1 = 1 ∧ 0 ≤ y θ 1 ∧ y θ 1 ≤ 1 ∧
    (θ 0 < θ 1 → y θ 1 = 1) ∧ (θ 1 < θ 0 → y θ 1 = 0)

/-- Budget balance on `Θ`: `t₀(θ) + t₁(θ) = 0` (MWG, p. 895). -/
def BudgetBalancedOn (lo hi : Fin 2 → ℝ) (t : (Fin 2 → ℝ) → Fin 2 → ℝ) : Prop :=
  ∀ θ, InTypes lo hi θ → t θ 0 + t θ 1 = 0

/-- Interim individual rationality (23.E.2) in the bilateral trade setting (MWG, p. 894): every
seller type gets `U₀(θ₀) ≥ θ₀` (his utility from consuming the good) and every buyer type gets
`U₁(θ₁) ≥ 0`. -/
def InterimIR (P : Measure (Fin 2 → ℝ)) (y t : (Fin 2 → ℝ) → Fin 2 → ℝ) (lo hi : Fin 2 → ℝ) :
    Prop :=
  (∀ x ∈ Set.Icc (lo 0) (hi 0), x ≤ interimU P allocV y t 0 x) ∧
    ∀ x ∈ Set.Icc (lo 1) (hi 1), 0 ≤ interimU P allocV y t 1 x

/-- The comparison transfers: the seller receives the buyer's valuation and the buyer pays the
seller's valuation whenever trade occurs, `t₀ = θ₁y₁`, `t₁ = -θ₀y₁` (a Vickrey-Clarke-Groves
rule; not budget balanced). -/
def msVcgT (y : (Fin 2 → ℝ) → Fin 2 → ℝ) : (Fin 2 → ℝ) → Fin 2 → ℝ :=
  fun θ => ![θ 1 * y θ 1, -(θ 0 * y θ 1)]

/-- `d c ≤ max(d, 0)` for `c ∈ [0, 1]`. -/
theorem ms_mul_le_max {d c : ℝ} (h0 : 0 ≤ c) (h1 : c ≤ 1) : d * c ≤ max d 0 := by
  rcases le_total d 0 with hd | hd
  · rw [max_eq_right hd]; nlinarith
  · rw [max_eq_left hd]; nlinarith

/-- On `Θ`, the efficient trade gives `(θ₁ - θ₀)y₁(θ) = max(θ₁ - θ₀, 0)`. -/
theorem ms_eff_mul {lo hi : Fin 2 → ℝ} {y : (Fin 2 → ℝ) → Fin 2 → ℝ}
    (heff : ExPostEfficientTrade lo hi y) {θ : Fin 2 → ℝ} (hθ : InTypes lo hi θ) :
    (θ 1 - θ 0) * y θ 1 = max (θ 1 - θ 0) 0 := by
  obtain ⟨-, -, -, h1, h2⟩ := heff θ hθ
  rcases lt_trichotomy (θ 0) (θ 1) with h | h | h
  · rw [h1 h, max_eq_left (by linarith)]; ring
  · rw [h]; simp
  · rw [h2 h, max_eq_right (by linarith)]; ring

/-- The seller's utility under the comparison transfers: reporting into profile `u ∈ Θ`, a seller
of type `x` gets `x y₀(u) + u₁y₁(u) ≤ x + max(u₁ - x, 0)`, with equality when `u₀ = x`. -/
theorem ms_vcg_seller {lo hi : Fin 2 → ℝ} {y : (Fin 2 → ℝ) → Fin 2 → ℝ}
    (heff : ExPostEfficientTrade lo hi y) {u : Fin 2 → ℝ} (hu : InTypes lo hi u) (x : ℝ) :
    linU allocV 0 (y u, msVcgT y u) x ≤ x + max (u 1 - x) 0 ∧
      linU allocV 0 (y u, msVcgT y u) (u 0) = u 0 + max (u 1 - u 0) 0 := by
  obtain ⟨hs, h0, h1, -, -⟩ := heff u hu
  have e : ∀ z, linU allocV 0 (y u, msVcgT y u) z = z + (u 1 - z) * y u 1 := by
    intro z
    simp only [linU, allocV, msVcgT, Matrix.cons_val_zero]
    rw [show y u 0 = 1 - y u 1 by linarith]
    ring
  refine ⟨?_, ?_⟩
  · rw [e]; linarith [ms_mul_le_max (d := u 1 - x) h0 h1]
  · rw [e, ms_eff_mul heff hu]

/-- The buyer's utility under the comparison transfers: reporting into profile `u ∈ Θ`, a buyer of
type `x` gets `(x - u₀)y₁(u) ≤ max(x - u₀, 0)`, with equality when `u₁ = x`. -/
theorem ms_vcg_buyer {lo hi : Fin 2 → ℝ} {y : (Fin 2 → ℝ) → Fin 2 → ℝ}
    (heff : ExPostEfficientTrade lo hi y) {u : Fin 2 → ℝ} (hu : InTypes lo hi u) (x : ℝ) :
    linU allocV 1 (y u, msVcgT y u) x ≤ max (x - u 0) 0 ∧
      linU allocV 1 (y u, msVcgT y u) (u 1) = max (u 1 - u 0) 0 := by
  obtain ⟨-, h0, h1, -, -⟩ := heff u hu
  have e : ∀ z, linU allocV 1 (y u, msVcgT y u) z = (z - u 0) * y u 1 := by
    intro z
    simp only [linU, allocV, msVcgT, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    ring
  refine ⟨?_, ?_⟩
  · rw [e]; exact ms_mul_le_max h0 h1
  · rw [e, ms_eff_mul heff hu]

/-- On `Θ`, `|t^g_i(u)| ≤ |θ̲ⱼ| + |θ̄ⱼ|` for the comparison transfers. -/
theorem ms_vcg_bound {lo hi : Fin 2 → ℝ} {y : (Fin 2 → ℝ) → Fin 2 → ℝ}
    (heff : ExPostEfficientTrade lo hi y) {u : Fin 2 → ℝ} (hu : InTypes lo hi u) (i : Fin 2) :
    |msVcgT y u i| ≤ |lo 0| + |hi 0| + (|lo 1| + |hi 1|) := by
  obtain ⟨-, h0, h1, -, -⟩ := heff u hu
  have hy : |y u 1| ≤ 1 := abs_le.2 ⟨by linarith, h1⟩
  have b0 := re_abs_le_of_mem (hu 0)
  have b1 := re_abs_le_of_mem (hu 1)
  fin_cases i
  · simp only [msVcgT, Fin.zero_eta, Matrix.cons_val_zero, abs_mul]
    nlinarith [abs_nonneg (u 1), abs_nonneg (y u 1), abs_nonneg (lo 0), abs_nonneg (hi 0)]
  · simp only [msVcgT, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, abs_neg,
      abs_mul]
    nlinarith [abs_nonneg (u 0), abs_nonneg (y u 1), abs_nonneg (lo 1), abs_nonneg (hi 1)]

/-- The comparison transfers are measurable when `y` is. -/
theorem ms_measurable_vcg {y : (Fin 2 → ℝ) → Fin 2 → ℝ} (hym : Measurable y) (i : Fin 2) :
    Measurable fun θ => msVcgT y θ i := by
  have h1 : Measurable fun θ : Fin 2 → ℝ => y θ 1 := (measurable_pi_apply 1).comp hym
  fin_cases i
  · simp only [msVcgT, Fin.zero_eta, Matrix.cons_val_zero]
    exact (measurable_pi_apply 1).mul h1
  · simp only [msVcgT, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    exact ((measurable_pi_apply 0).mul h1).neg

variable (μ : Fin 2 → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]

/-- The comparison rule `(y, t^g)` is Bayesian incentive compatible and its interim expectations
exist, whenever `y` is measurable and ex post efficient (dominant strategy incentive
compatibility on `Θ`, integrated). -/
theorem ms_vcg_bic {lo hi : Fin 2 → ℝ} (hsupp : ∀ i, μ i (Set.Icc (lo i) (hi i))ᶜ = 0)
    {y : (Fin 2 → ℝ) → Fin 2 → ℝ} (hym : Measurable y) (heff : ExPostEfficientTrade lo hi y)
    (hy : ∀ i, ∀ a ∈ Set.Icc (lo i) (hi i),
      Integrable (fun θ' => allocV i (y (update θ' i a))) (Measure.pi μ)) :
    InterimIntegrable (Measure.pi μ) allocV y (msVcgT y) lo hi ∧
      BayesianICOn (Measure.pi μ) allocV y (msVcgT y) lo hi := by
  have hint : InterimIntegrable (Measure.pi μ) allocV y (msVcgT y) lo hi := by
    intro i a ha
    refine ⟨hy i a ha, Integrable.of_bound
      ((ms_measurable_vcg hym i).comp measurable_update_left).aestronglyMeasurable
      (|lo 0| + |hi 0| + (|lo 1| + |hi 1|)) ?_⟩
    filter_upwards [re_ae_update_mem μ hsupp ha] with θ' hθ'
    rw [Real.norm_eq_abs]
    exact ms_vcg_bound heff hθ' i
  refine ⟨hint, ?_⟩
  have hI : ∀ i, ∀ a ∈ Set.Icc (lo i) (hi i), ∀ x : ℝ, Integrable (fun θ' =>
      linU allocV i (y (update θ' i a), msVcgT y (update θ' i a)) x) (Measure.pi μ) :=
    fun i a ha x => ((hint i a ha).1.const_mul x).add (hint i a ha).2
  intro i x hx a ha
  refine integral_mono_ae (hI i a ha x) (hI i x hx x) ?_
  filter_upwards [re_ae_update_mem μ hsupp ha, re_ae_update_mem μ hsupp hx] with θ' h1 h2
  fin_cases i
  · have e1 := (ms_vcg_seller heff (u := update θ' 0 a) h1 x).1
    have e2 := (ms_vcg_seller heff (u := update θ' 0 x) h2 x).2
    simp only [Fin.zero_eta, update_self, update_of_ne (Ne.symm zero_ne_one)] at e1 e2 ⊢
    rw [e2]; exact e1
  · have e1 := (ms_vcg_buyer heff (u := update θ' 1 a) h1 x).1
    have e2 := (ms_vcg_buyer heff (u := update θ' 1 x) h2 x).2
    simp only [Fin.mk_one, update_self, update_of_ne zero_ne_one] at e1 e2 ⊢
    rw [e2]; exact e1

/-- A measurable function bounded on `Θ` is integrable under `∏ᵢ μᵢ` when each `μᵢ` is concentrated
on `[θ̲ᵢ, θ̄ᵢ]`. -/
theorem ms_integrable_of_bound {lo hi : Fin 2 → ℝ} (hsupp : ∀ i, μ i (Set.Icc (lo i) (hi i))ᶜ = 0)
    {F : (Fin 2 → ℝ) → ℝ} (hF : Measurable F) (C : ℝ) (hC : ∀ θ, InTypes lo hi θ → |F θ| ≤ C) :
    Integrable F (Measure.pi μ) := by
  refine Integrable.of_bound hF.aestronglyMeasurable C ?_
  filter_upwards [re_ae_mem μ hsupp] with θ hθ
  rw [Real.norm_eq_abs]; exact hC θ hθ

/-- `|max(u - v, 0)| ≤ |u| + |v|`. -/
theorem ms_abs_max_sub_le (u v : ℝ) : |max (u - v) 0| ≤ |u| + |v| := by
  rw [abs_of_nonneg (le_max_right _ _)]
  exact max_le ((le_abs_self _).trans (abs_sub _ _)) (by positivity)

/-- The positive parts `(θⱼ - x)⁺` and `(x - θⱼ)⁺`, and `(θ₁ - θ₀)⁺`, are integrable under
`∏ᵢ μᵢ` when each `μᵢ` is concentrated on `[θ̲ᵢ, θ̄ᵢ]`. -/
theorem ms_integrable_pos_parts {lo hi : Fin 2 → ℝ}
    (hsupp : ∀ i, μ i (Set.Icc (lo i) (hi i))ᶜ = 0) (j : Fin 2) (x : ℝ) :
    Integrable (fun θ => max (θ j - x) 0) (Measure.pi μ) ∧
      Integrable (fun θ => max (x - θ j) 0) (Measure.pi μ) ∧
      Integrable (fun θ => max (θ 1 - θ 0) 0) (Measure.pi μ) := by
  refine ⟨ms_integrable_of_bound μ hsupp (((measurable_pi_apply j).sub measurable_const).max
      measurable_const) (|lo j| + |hi j| + |x|) fun θ hθ => (ms_abs_max_sub_le _ _).trans
      (by linarith [re_abs_le_of_mem (hθ j)]), ms_integrable_of_bound μ hsupp
      ((measurable_const.sub (measurable_pi_apply j)).max measurable_const)
      (|lo j| + |hi j| + |x|) fun θ hθ => (ms_abs_max_sub_le _ _).trans
      (by linarith [re_abs_le_of_mem (hθ j)]), ms_integrable_of_bound μ hsupp
      (((measurable_pi_apply 1).sub (measurable_pi_apply 0)).max measurable_const)
      (|lo 1| + |hi 1| + (|lo 0| + |hi 0|)) fun θ hθ => (ms_abs_max_sub_le _ _).trans
      (by linarith [re_abs_le_of_mem (hθ 0), re_abs_le_of_mem (hθ 1)])⟩

/-- **Proposition 23.E.1**, the common core of the proof (MWG, pp. 895-896). Let `f = (y, t)` be
Bayesian incentive compatible and interim individually rational with an efficient trading rule
`y` (budget balance is NOT assumed). Then for the comparison transfers
`t^g₀ = θ₁y₁`, `t^g₁ = -θ₀y₁` there are constants `cᵢ` with `E[tᵢ] = E[t^gᵢ] + cᵢ`,
`c₀ ≥ -E[(θ₁ - θ̄₀)⁺]` and `c₁ ≥ -E[(θ̲₁ - θ₀)⁺]`; moreover
`E[t^g₀] + E[t^g₁] = E[(θ₁ - θ₀)⁺]`. -/
theorem ms_core {lo hi : Fin 2 → ℝ} (hlo : ∀ i, lo i ≤ hi i)
    (hsupp : ∀ i, μ i (Set.Icc (lo i) (hi i))ᶜ = 0)
    {y t : (Fin 2 → ℝ) → Fin 2 → ℝ} (hym : Measurable y)
    (hint : InterimIntegrable (Measure.pi μ) allocV y t lo hi)
    (ht : ∀ i, Integrable (fun θ => t θ i) (Measure.pi μ))
    (heff : ExPostEfficientTrade lo hi y)
    (hbic : BayesianICOn (Measure.pi μ) allocV y t lo hi)
    (hir : InterimIR (Measure.pi μ) y t lo hi) :
    ∃ c : Fin 2 → ℝ, (∀ i, ∫ θ, t θ i ∂Measure.pi μ = ∫ θ, msVcgT y θ i ∂Measure.pi μ + c i) ∧
      -∫ θ, max (θ 1 - hi 0) 0 ∂Measure.pi μ ≤ c 0 ∧
      -∫ θ, max (lo 1 - θ 0) 0 ∂Measure.pi μ ≤ c 1 ∧
      ∫ θ, msVcgT y θ 0 ∂Measure.pi μ + ∫ θ, msVcgT y θ 1 ∂Measure.pi μ =
        ∫ θ, max (θ 1 - θ 0) 0 ∂Measure.pi μ := by
  have hae := re_ae_mem μ hsupp
  obtain ⟨hintg, hbicg⟩ := ms_vcg_bic μ hsupp hym heff fun i a ha => (hint i a ha).1
  have htg : ∀ i, Integrable (fun θ => msVcgT y θ i) (Measure.pi μ) := fun i =>
    ms_integrable_of_bound μ hsupp (ms_measurable_vcg hym i) _
      fun θ hθ => ms_vcg_bound heff hθ i
  set c : Fin 2 → ℝ := fun i => interimU (Measure.pi μ) allocV y t i (lo i) -
    interimU (Measure.pi μ) allocV y (msVcgT y) i (lo i) with hc
  have hconst : ∀ i, ∀ x ∈ Set.Icc (lo i) (hi i), interimTransfer (Measure.pi μ) t i x =
      interimTransfer (Measure.pi μ) (msVcgT y) i x + c i := by
    intro i x hx
    rw [re_interimTransfer_eq hint hbic i hx, re_interimTransfer_eq hintg hbicg i hx, hc]
    ring
  refine ⟨c, fun i => ?_, ?_, ?_, ?_⟩
  · rw [re_expected_transfer μ i (ht i), re_expected_transfer μ i (htg i)]
    have hI : Integrable (fun θ => interimTransfer (Measure.pi μ) (msVcgT y) i (θ i))
        (Measure.pi μ) := re_integrable_integral_update μ i (htg i)
    rw [integral_congr_ae (g := fun θ => interimTransfer (Measure.pi μ) (msVcgT y) i (θ i) + c i)
      ?_, integral_add hI (integrable_const _)]
    · simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    filter_upwards [hae] with θ hθ using hconst i (θ i) (hθ i)
  · have hhi0 : hi 0 ∈ Set.Icc (lo 0) (hi 0) := ⟨hlo 0, le_rfl⟩
    have h1 : interimU (Measure.pi μ) allocV y t 0 (hi 0) -
        interimU (Measure.pi μ) allocV y (msVcgT y) 0 (hi 0) = c 0 := by
      simp only [interimU]; rw [hconst 0 (hi 0) hhi0]; ring
    have h2 : interimU (Measure.pi μ) allocV y (msVcgT y) 0 (hi 0) =
        hi 0 + ∫ θ, max (θ 1 - hi 0) 0 ∂Measure.pi μ := by
      rw [interimU, ← eq_23_D_10 (hintg 0 _ hhi0).1 (hintg 0 _ hhi0).2 (hi 0),
        integral_congr_ae (g := fun θ => hi 0 + max (θ 1 - hi 0) 0) ?_,
        integral_add (integrable_const _) (ms_integrable_pos_parts μ hsupp 1 (hi 0)).1]
      · simp
      filter_upwards [re_ae_update_mem μ hsupp hhi0] with θ' h
      have := (ms_vcg_seller heff h (hi 0)).2
      simp only [update_self, update_of_ne (Ne.symm zero_ne_one)] at this
      rw [this]
    have h3 := hir.1 (hi 0) hhi0
    linarith
  · have hlo1 : lo 1 ∈ Set.Icc (lo 1) (hi 1) := ⟨le_rfl, hlo 1⟩
    have h1 : interimU (Measure.pi μ) allocV y t 1 (lo 1) -
        interimU (Measure.pi μ) allocV y (msVcgT y) 1 (lo 1) = c 1 := by
      simp only [interimU]; rw [hconst 1 (lo 1) hlo1]; ring
    have h2 : interimU (Measure.pi μ) allocV y (msVcgT y) 1 (lo 1) =
        ∫ θ, max (lo 1 - θ 0) 0 ∂Measure.pi μ := by
      rw [interimU, ← eq_23_D_10 (hintg 1 _ hlo1).1 (hintg 1 _ hlo1).2 (lo 1)]
      refine integral_congr_ae ?_
      filter_upwards [re_ae_update_mem μ hsupp hlo1] with θ' h
      have := (ms_vcg_buyer heff h (lo 1)).2
      simp only [update_self, update_of_ne zero_ne_one] at this
      rw [this]
    have h3 := hir.2 (lo 1) hlo1
    linarith
  · rw [← integral_add (htg 0) (htg 1)]
    refine integral_congr_ae ?_
    filter_upwards [hae] with θ hθ
    simp only [msVcgT, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [← ms_eff_mul heff hθ]; ring

/-- **Proposition 23.E.1** (MWG, p. 895), the Myerson-Satterthwaite theorem, for general type
distributions. Agent `0` (seller) and agent `1` (buyer) have linear utilities `θᵢyᵢ + tᵢ`, and
independent valuations `θᵢ ~ μᵢ` with `μᵢ` concentrated on `[θ̲ᵢ, θ̄ᵢ]` and giving positive
probability to every open subinterval; gains from trade are possible but not certain,
`(θ̲₀, θ̄₀) ∩ (θ̲₁, θ̄₁) ≠ ∅` (footnote 41). Then no social choice function `(y, t)` is ex post
efficient (efficient trade and budget balance on `Θ`), Bayesian incentive compatible and interim
individually rational.

Proof (not MWG's integration by parts): compare `f` with the rule `g = (y, t^g)`,
`t^g₀ = θ₁y₁`, `t^g₁ = -θ₀y₁`, which is Bayesian incentive compatible. By Proposition 23.D.2 the
interim transfers of `f` and `g` differ by constants `cᵢ` on `Θᵢ`; budget balance gives
`c₀ + c₁ = -E[(θ₁ - θ₀)⁺]`, and interim individual rationality at `θ₀ = θ̄₀` and `θ₁ = θ̲₁` gives
`c₀ ≥ -E[(θ₁ - θ̄₀)⁺]`, `c₁ ≥ -E[(θ̲₁ - θ₀)⁺]`. But on `Θ`,
`(θ₁ - θ₀)⁺ ≥ (θ₁ - θ̄₀)⁺ + (θ̲₁ - θ₀)⁺`, strictly on a box of positive probability in the
overlap. The integrability hypotheses say the expectations exist; `y` is assumed measurable. -/
theorem proposition_23_E_1_general {lo hi : Fin 2 → ℝ}
    (hsupp : ∀ i, μ i (Set.Icc (lo i) (hi i))ᶜ = 0)
    (hpos : ∀ i, ∀ a b, lo i ≤ a → a < b → b ≤ hi i → 0 < μ i (Set.Ioo a b))
    (hov : (Set.Ioo (lo 0) (hi 0) ∩ Set.Ioo (lo 1) (hi 1)).Nonempty)
    {y t : (Fin 2 → ℝ) → Fin 2 → ℝ} (hym : Measurable y)
    (hint : InterimIntegrable (Measure.pi μ) allocV y t lo hi)
    (ht : ∀ i, Integrable (fun θ => t θ i) (Measure.pi μ))
    (heff : ExPostEfficientTrade lo hi y) (hbb : BudgetBalancedOn lo hi t)
    (hbic : BayesianICOn (Measure.pi μ) allocV y t lo hi)
    (hir : InterimIR (Measure.pi μ) y t lo hi) : False := by
  obtain ⟨z, ⟨hz0, hz0'⟩, ⟨hz1, hz1'⟩⟩ := hov
  have hlo : ∀ i, lo i ≤ hi i := by
    intro i; fin_cases i
    · exact (hz0.trans hz0').le
    · exact (hz1.trans hz1').le
  obtain ⟨c, hE, hc0, hc1, hgE⟩ := ms_core μ hlo hsupp hym hint ht heff hbic hir
  have hae := re_ae_mem μ hsupp
  have hbbE : ∫ θ, t θ 0 ∂Measure.pi μ + ∫ θ, t θ 1 ∂Measure.pi μ = 0 := by
    rw [← integral_add (ht 0) (ht 1), integral_congr_ae (g := fun _ => (0 : ℝ)) ?_]
    · simp
    filter_upwards [hae] with θ hθ using hbb θ hθ
  set pp : (Fin 2 → ℝ) → ℝ := fun θ => max (θ 1 - θ 0) 0 with hpp
  set q0 : (Fin 2 → ℝ) → ℝ := fun θ => max (θ 1 - hi 0) 0 with hq0
  set q1 : (Fin 2 → ℝ) → ℝ := fun θ => max (lo 1 - θ 0) 0 with hq1
  have hppI : Integrable pp (Measure.pi μ) := (ms_integrable_pos_parts μ hsupp 0 0).2.2
  have hq0I : Integrable q0 (Measure.pi μ) := (ms_integrable_pos_parts μ hsupp 1 (hi 0)).1
  have hq1I : Integrable q1 (Measure.pi μ) := (ms_integrable_pos_parts μ hsupp 0 (lo 1)).2.1
  -- the pointwise inequality and its strict version on a box in the overlap
  have hnn : ∀ θ, InTypes lo hi θ → 0 ≤ pp θ - q0 θ - q1 θ := by
    intro θ hθ
    obtain ⟨a0, b0⟩ := hθ 0
    obtain ⟨a1, b1⟩ := hθ 1
    simp only [hpp, hq0, hq1, max_def]
    split_ifs <;> linarith
  set a := max (lo 0) (lo 1) with ha
  set b := min (hi 0) (hi 1) with hb'
  have haz : a < z := max_lt hz0 hz1
  have hzb : z < b := lt_min hz0' hz1'
  set S : Set (Fin 2 → ℝ) := Set.pi Set.univ ![Set.Ioo a z, Set.Ioo z b] with hS
  have hSpos : 0 < Measure.pi μ S := by
    rw [hS, Measure.pi_pi, Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    exact ENNReal.mul_pos (hpos 0 a z (le_max_left _ _) haz hz0'.le).ne'
      (hpos 1 z b hz1.le hzb (min_le_right _ _)).ne'
  have hSsupp : S ⊆ Function.support fun θ => pp θ - q0 θ - q1 θ := by
    intro θ hθ
    rw [hS, Set.mem_univ_pi] at hθ
    have h0 := hθ 0
    have h1 := hθ 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Set.mem_Ioo] at h0 h1
    have e1 : pp θ = θ 1 - θ 0 := max_eq_left (by linarith)
    have e2 : q0 θ = 0 := max_eq_right (by linarith [min_le_left (hi 0) (hi 1)])
    have e3 : q1 θ = 0 := max_eq_right (by linarith [le_max_right (lo 0) (lo 1)])
    simp only [Function.mem_support, e1, e2, e3]
    linarith
  have hI2 : Integrable (fun θ => pp θ - q0 θ) (Measure.pi μ) := hppI.sub hq0I
  have hI3 : Integrable (fun θ => pp θ - q0 θ - q1 θ) (Measure.pi μ) := hI2.sub hq1I
  have hstrict : 0 < ∫ θ, (pp θ - q0 θ - q1 θ) ∂Measure.pi μ := by
    rw [integral_pos_iff_support_of_nonneg_ae _ hI3]
    · exact hSpos.trans_le (measure_mono hSsupp)
    · filter_upwards [hae] with θ hθ using hnn θ hθ
  rw [integral_sub (f := fun θ => pp θ - q0 θ) hI2 hq1I, integral_sub hppI hq0I] at hstrict
  have := hE 0
  have := hE 1
  linarith

/-- **Footnote 41** (MWG, p. 895). For nondegenerate intervals (`θ̲ᵢ < θ̄ᵢ`),
`(θ̲₀, θ̄₀) ∩ (θ̲₁, θ̄₁) ≠ ∅` iff `θ̄₁ > θ̲₀` and `θ̄₀ > θ̲₁`. -/
theorem footnote_23_41 {lo hi : Fin 2 → ℝ} (h0 : lo 0 < hi 0) (h1 : lo 1 < hi 1) :
    (Set.Ioo (lo 0) (hi 0) ∩ Set.Ioo (lo 1) (hi 1)).Nonempty ↔ lo 0 < hi 1 ∧ lo 1 < hi 0 := by
  constructor
  · rintro ⟨z, ⟨a0, b0⟩, ⟨a1, b1⟩⟩
    exact ⟨a0.trans b1, a1.trans b0⟩
  · rintro ⟨c0, c1⟩
    refine ⟨(max (lo 0) (lo 1) + min (hi 0) (hi 1)) / 2, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
      simp only [max_def, min_def] <;> split_ifs <;> linarith

/-- **Proposition 23.E.1** (MWG, p. 895), the Myerson-Satterthwaite theorem, as stated: the
seller's and buyer's valuations are independent with strictly positive densities on
`[θ̲₀, θ̄₀]` and `[θ̲₁, θ̄₁]`, and `(θ̲₀, θ̄₀) ∩ (θ̲₁, θ̄₁) ≠ ∅`. Then no Bayesian incentive
compatible social choice function is ex post efficient and gives every buyer type and every
seller type nonnegative expected gains from participation. (`y` measurable and the integrability
hypotheses say that the expectations exist.) -/
theorem proposition_23_E_1 (D : Fin 2 → TypeDensity)
    (hov : (Set.Ioo (D 0).lo (D 0).hi ∩ Set.Ioo (D 1).lo (D 1).hi).Nonempty)
    {y t : (Fin 2 → ℝ) → Fin 2 → ℝ} (hym : Measurable y)
    (hint : InterimIntegrable (Measure.pi fun j => (D j).measure) allocV y t
      (fun i => (D i).lo) fun i => (D i).hi)
    (ht : ∀ i, Integrable (fun θ => t θ i) (Measure.pi fun j => (D j).measure))
    (heff : ExPostEfficientTrade (fun i => (D i).lo) (fun i => (D i).hi) y)
    (hbb : BudgetBalancedOn (fun i => (D i).lo) (fun i => (D i).hi) t)
    (hbic : BayesianICOn (Measure.pi fun j => (D j).measure) allocV y t
      (fun i => (D i).lo) fun i => (D i).hi)
    (hir : InterimIR (Measure.pi fun j => (D j).measure) y t (fun i => (D i).lo)
      fun i => (D i).hi) : False := by
  have : ∀ j, IsProbabilityMeasure (D j).measure := fun j => (D j).isProbabilityMeasure
  exact proposition_23_E_1_general (fun j => (D j).measure) (fun i => (D i).measure_compl_Icc)
    (fun i _ _ ha hab hb => (D i).measure_Ioo_pos ha hab hb) hov hym hint ht heff hbb hbic hir

/-! ### Dominant strategies, ex post participation, and Exercise 23.E.2 -/

/-- Dominant strategy incentive compatibility (23.C.3) on `Θ` in the bilateral trade setting:
for every profile `θ ∈ Θ` and announcement `a ∈ Θᵢ`, `uᵢ(f(a, θ₋ᵢ), θᵢ) ≤ uᵢ(f(θ), θᵢ)`. -/
def DominantICOn (lo hi : Fin 2 → ℝ) (y t : (Fin 2 → ℝ) → Fin 2 → ℝ) : Prop :=
  ∀ i, ∀ θ, InTypes lo hi θ → ∀ a ∈ Set.Icc (lo i) (hi i),
    linU allocV i (y (update θ i a), t (update θ i a)) (θ i) ≤ linU allocV i (y θ, t θ) (θ i)

/-- Ex post individual rationality (23.E.1) in the bilateral trade setting: on `Θ`, the seller
gets at least `θ₀` and the buyer at least `0`. -/
def ExPostIR (lo hi : Fin 2 → ℝ) (y t : (Fin 2 → ℝ) → Fin 2 → ℝ) : Prop :=
  ∀ θ, InTypes lo hi θ → θ 0 ≤ linU allocV 0 (y θ, t θ) (θ 0) ∧
    0 ≤ linU allocV 1 (y θ, t θ) (θ 1)

/-- `(θ₋ᵢ, x)` lies in `Θ` when `θ` does and `x ∈ Θᵢ`. -/
theorem ms_update_mem {lo hi : Fin 2 → ℝ} {θ : Fin 2 → ℝ} (hθ : InTypes lo hi θ) {i : Fin 2}
    {x : ℝ} (hx : x ∈ Set.Icc (lo i) (hi i)) : InTypes lo hi (update θ i x) := by
  intro j
  by_cases hj : j = i
  · subst hj; simpa using hx
  · simpa [hj] using hθ j

/-- **Section 23.D** (MWG, p. 884), in the linear bilateral setting: a dominant strategy incentive
compatible social choice function is Bayesian incentive compatible (with independent types
concentrated on `Θ`, the expectations existing). -/
theorem ms_bic_of_dsic {lo hi : Fin 2 → ℝ} (hsupp : ∀ i, μ i (Set.Icc (lo i) (hi i))ᶜ = 0)
    {y t : (Fin 2 → ℝ) → Fin 2 → ℝ} (hint : InterimIntegrable (Measure.pi μ) allocV y t lo hi)
    (hds : DominantICOn lo hi y t) : BayesianICOn (Measure.pi μ) allocV y t lo hi := by
  intro i x hx a ha
  have hI : ∀ b ∈ Set.Icc (lo i) (hi i), Integrable (fun θ' =>
      linU allocV i (y (update θ' i b), t (update θ' i b)) x) (Measure.pi μ) :=
    fun b hb => ((hint i b hb).1.const_mul x).add (hint i b hb).2
  refine integral_mono_ae (hI a ha) (hI x hx) ?_
  filter_upwards [re_ae_update_mem μ hsupp hx] with θ' h
  have := hds i (update θ' i x) h a ha
  simpa only [update_idem, update_self] using this

/-- **Section 23.E** (MWG, p. 894): ex post individual rationality (23.E.1) implies interim
individual rationality (23.E.2). -/
theorem ms_interimIR_of_exPostIR {lo hi : Fin 2 → ℝ}
    (hsupp : ∀ i, μ i (Set.Icc (lo i) (hi i))ᶜ = 0) {y t : (Fin 2 → ℝ) → Fin 2 → ℝ}
    (hint : InterimIntegrable (Measure.pi μ) allocV y t lo hi) (hir : ExPostIR lo hi y t) :
    InterimIR (Measure.pi μ) y t lo hi := by
  have hI : ∀ i, ∀ b ∈ Set.Icc (lo i) (hi i), Integrable (fun θ' =>
      linU allocV i (y (update θ' i b), t (update θ' i b)) b) (Measure.pi μ) :=
    fun i b hb => ((hint i b hb).1.const_mul b).add (hint i b hb).2
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · rw [interimU, ← eq_23_D_10 (hint 0 x hx).1 (hint 0 x hx).2 x]
    have h := integral_mono_ae (integrable_const x) (hI 0 x hx) (by
      filter_upwards [re_ae_update_mem μ hsupp hx] with θ' h
      simpa using (hir _ h).1)
    simpa using h
  · rw [interimU, ← eq_23_D_10 (hint 1 x hx).1 (hint 1 x hx).2 x]
    exact integral_nonneg_of_ae (by
      filter_upwards [re_ae_update_mem μ hsupp hx] with θ' h
      simpa using (hir _ h).2)

/-- **Exercise 23.E.2(a)** (MWG, p. 921), corrected. Under the assumptions of Proposition 23.E.1
(general form), no social choice function is dominant strategy incentive compatible, interim
individually rational and ex post efficient (efficient trade and budget balance). -/
theorem exercise_23_E_2a {lo hi : Fin 2 → ℝ}
    (hsupp : ∀ i, μ i (Set.Icc (lo i) (hi i))ᶜ = 0)
    (hpos : ∀ i, ∀ a b, lo i ≤ a → a < b → b ≤ hi i → 0 < μ i (Set.Ioo a b))
    (hov : (Set.Ioo (lo 0) (hi 0) ∩ Set.Ioo (lo 1) (hi 1)).Nonempty)
    {y t : (Fin 2 → ℝ) → Fin 2 → ℝ} (hym : Measurable y)
    (hint : InterimIntegrable (Measure.pi μ) allocV y t lo hi)
    (ht : ∀ i, Integrable (fun θ => t θ i) (Measure.pi μ))
    (heff : ExPostEfficientTrade lo hi y) (hbb : BudgetBalancedOn lo hi t)
    (hds : DominantICOn lo hi y t) (hir : InterimIR (Measure.pi μ) y t lo hi) : False :=
  proposition_23_E_1_general μ hsupp hpos hov hym hint ht heff hbb
    (ms_bic_of_dsic μ hsupp hint hds) hir

/-- **Exercise 23.E.2(b)** (MWG, p. 922), corrected. Under the assumptions of Proposition 23.E.1
(general form), no social choice function is Bayesian incentive compatible, ex post individually
rational and ex post efficient (efficient trade and budget balance). -/
theorem exercise_23_E_2b {lo hi : Fin 2 → ℝ}
    (hsupp : ∀ i, μ i (Set.Icc (lo i) (hi i))ᶜ = 0)
    (hpos : ∀ i, ∀ a b, lo i ≤ a → a < b → b ≤ hi i → 0 < μ i (Set.Ioo a b))
    (hov : (Set.Ioo (lo 0) (hi 0) ∩ Set.Ioo (lo 1) (hi 1)).Nonempty)
    {y t : (Fin 2 → ℝ) → Fin 2 → ℝ} (hym : Measurable y)
    (hint : InterimIntegrable (Measure.pi μ) allocV y t lo hi)
    (ht : ∀ i, Integrable (fun θ => t θ i) (Measure.pi μ))
    (heff : ExPostEfficientTrade lo hi y) (hbb : BudgetBalancedOn lo hi t)
    (hbic : BayesianICOn (Measure.pi μ) allocV y t lo hi) (hir : ExPostIR lo hi y t) : False :=
  proposition_23_E_1_general μ hsupp hpos hov hym hint ht heff hbb hbic
    (ms_interimIR_of_exPostIR μ hsupp hint hir)

/-- The no-trade rule: the seller keeps the good and no money changes hands. -/
def noTradeY : (Fin 2 → ℝ) → Fin 2 → ℝ := fun _ => ![1, 0]

/-- **Exercise 23.E.2(a)-(b)** as printed are false (MWG, pp. 921-922): without ex post
efficiency, the no-trade rule (`y = (1, 0)`, `t = 0`) is dominant strategy and Bayesian incentive
compatible, budget balanced, and ex post (hence interim) individually rational, for any
independent prior. -/
theorem exercise_23_E_2_literal_false (lo hi : Fin 2 → ℝ) :
    DominantICOn lo hi noTradeY (fun _ => 0) ∧
      BayesianICOn (Measure.pi μ) allocV noTradeY (fun _ => 0) lo hi ∧
      BudgetBalancedOn lo hi (fun _ => 0) ∧ ExPostIR lo hi noTradeY (fun _ => 0) ∧
      InterimIR (Measure.pi μ) noTradeY (fun _ => 0) lo hi := by
  have hint : InterimIntegrable (Measure.pi μ) allocV noTradeY (fun _ => 0) lo hi :=
    fun _ _ _ => ⟨integrable_const _, integrable_const _⟩
  refine ⟨fun i θ _ a _ => le_rfl, fun i x _ a _ => le_rfl, fun _ _ => by simp,
    fun θ _ => ?_, ⟨fun x _ => ?_, fun x _ => ?_⟩⟩
  · simp [linU, allocV, noTradeY]
  · simp [interimU, interimBenefit, interimTransfer, allocV, noTradeY]
  · simp [interimU, interimBenefit, interimTransfer, allocV, noTradeY]

/-! ### Uniform types on `[0, 1]`: Exercises 23.E.1 and 23.E.7, and non-vacuity -/

/-- The uniform prior on `[0, 1]²` satisfies the hypotheses of Proposition 23.E.1 (general form):
support in `[0, 1]`, positive probability of open subintervals, overlapping intervals. -/
theorem ms_unif_hyps :
    (∀ i : Fin 2, uniform01.measure (Set.Icc ((fun _ => (0 : ℝ)) i) ((fun _ => (1 : ℝ)) i))ᶜ
      = 0) ∧
    (∀ i : Fin 2, ∀ a b, (fun _ => (0 : ℝ)) i ≤ a → a < b → b ≤ (fun _ => (1 : ℝ)) i →
      0 < uniform01.measure (Set.Ioo a b)) ∧
    (Set.Ioo ((fun _ : Fin 2 => (0 : ℝ)) 0) ((fun _ : Fin 2 => (1 : ℝ)) 0) ∩
      Set.Ioo ((fun _ : Fin 2 => (0 : ℝ)) 1) ((fun _ : Fin 2 => (1 : ℝ)) 1)).Nonempty :=
  ⟨fun _ => uniform01.measure_compl_Icc, fun _ _ _ ha hab hb => uniform01.measure_Ioo_pos ha hab hb,
    ⟨1 / 2, by norm_num, by norm_num⟩⟩

/-- Under the uniform prior, `E[θᵢ] = 1/2`. -/
theorem ms_unif_mean (i : Fin 2) : ∫ θ, θ i ∂unif2 = 1 / 2 := by
  have := uniform01.isProbabilityMeasure
  rw [integral_eval_pi (Θ := fun _ => ℝ) (fun _ : Fin 2 => uniform01.measure) i (F := fun x => x)
    measurable_id.aestronglyMeasurable, uniform01_integral, integral_id]
  norm_num

/-- Under the uniform prior, the expected gains from trade are `E[(θ₁ - θ₀)⁺] = 1/6`. -/
theorem ms_unif_gains : ∫ θ, max (θ 1 - θ 0) 0 ∂unif2 = 1 / 6 := by
  have := uniform01.isProbabilityMeasure
  rw [re_unif2_integral (ms_integrable_pos_parts (fun _ : Fin 2 => uniform01.measure)
    (lo := fun _ => 0) (hi := fun _ => 1) ms_unif_hyps.1 0 0).2.2]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [intervalIntegral.integral_congr (g := fun a => (1 - a) ^ 2 / 2) fun a ha => ?_]
  · rw [intervalIntegral.integral_comp_sub_left (fun x => x ^ 2 / 2), intervalIntegral.integral_div,
      integral_pow]
    norm_num
  · rw [Set.uIcc_of_le zero_le_one] at ha
    have e : ∀ x : ℝ, max (x - a) 0 = if a < x then x - a else 0 := by
      intro x
      split_ifs with h
      · exact max_eq_left (by linarith)
      · exact max_eq_right (by linarith [not_lt.1 h])
    simp only [e]
    rw [re_integral_ite_gt ha, intervalIntegral.integral_sub (f := fun x => x)
      (continuous_id.intervalIntegrable _ _) intervalIntegrable_const, integral_id,
      intervalIntegral.integral_const, smul_eq_mul]
    ring

/-- **Exercise 23.E.7(b)** (MWG, p. 923), the expected surplus: `E[max(θ₀, θ₁)] = 2/3`. -/
theorem exercise_23_E_7b_surplus : ∫ θ, max (θ 0) (θ 1) ∂unif2 = 2 / 3 := by
  have := uniform01.isProbabilityMeasure
  have e : (fun θ : Fin 2 → ℝ => max (θ 0) (θ 1)) = fun θ => θ 0 + max (θ 1 - θ 0) 0 := by
    funext θ
    rcases le_total (θ 0) (θ 1) with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  have hI0 : Integrable (fun θ : Fin 2 → ℝ => θ 0) unif2 :=
    (re_unif2_integrable (measurable_pi_apply 0) 1 fun θ hθ =>
      abs_le.2 ⟨by linarith [(hθ 0).1], (hθ 0).2⟩).1
  rw [e, integral_add hI0 (ms_integrable_pos_parts (fun _ : Fin 2 => uniform01.measure)
    (lo := fun _ => 0) (hi := fun _ => 1) ms_unif_hyps.1 0 0).2.2, ms_unif_mean, ms_unif_gains]
  norm_num

/-- **Exercise 23.E.7(b)** (MWG, p. 923). With types uniform on `[0, 1]`, no feasible social choice
function (`yᵢ ≥ 0`, `y₀ + y₁ ≤ 1`, `t₀ + t₁ ≤ 0` on `[0, 1]²`), Bayesian incentive compatible and
individually rational or not, gives the seller and buyer a sum of expected utilities
`E[θ₀y₀ + t₀] + E[θ₁y₁ + t₁]` above `E[max(θ₀, θ₁)] = 2/3`. (The integrability hypotheses say
that the expected utilities exist.) -/
theorem exercise_23_E_7b {y t : (Fin 2 → ℝ) → Fin 2 → ℝ}
    (hI : ∀ i, Integrable (fun θ => linU allocV i (y θ, t θ) (θ i)) unif2)
    (hfeas : ∀ θ, InTypes (fun _ => 0) (fun _ => 1) θ →
      0 ≤ y θ 0 ∧ 0 ≤ y θ 1 ∧ y θ 0 + y θ 1 ≤ 1 ∧ t θ 0 + t θ 1 ≤ 0) :
    ∑ i, ∫ θ, linU allocV i (y θ, t θ) (θ i) ∂unif2 ≤ 2 / 3 := by
  have := uniform01.isProbabilityMeasure
  have hmax : Integrable (fun θ : Fin 2 → ℝ => max (θ 0) (θ 1)) unif2 :=
    (re_unif2_integrable ((measurable_pi_apply 0).max (measurable_pi_apply 1)) 1 fun θ hθ =>
      abs_le.2 ⟨by linarith [le_max_left (θ 0) (θ 1), (hθ 0).1],
        max_le (hθ 0).2 (hθ 1).2⟩).1
  rw [Fin.sum_univ_two, ← integral_add (hI 0) (hI 1), ← exercise_23_E_7b_surplus]
  refine integral_mono_ae ((hI 0).add (hI 1)) hmax ?_
  filter_upwards [re_ae_mem (fun _ : Fin 2 => uniform01.measure) (lo := fun _ => 0)
    (hi := fun _ => 1) ms_unif_hyps.1] with θ hθ
  obtain ⟨h0, h1, h2, h3⟩ := hfeas θ hθ
  simp only [linU, allocV]
  have m0 := le_max_left (θ 0) (θ 1)
  have m1 := le_max_right (θ 0) (θ 1)
  have mp : 0 ≤ max (θ 0) (θ 1) := (hθ 0).1.trans m0
  nlinarith [mul_le_mul_of_nonneg_right m0 h0, mul_le_mul_of_nonneg_right m1 h1]

/-- **Exercise 23.E.7(a)** (MWG, pp. 922-923). With types uniform on `[0, 1]`, if `f = (y, t)` is
Bayesian incentive compatible and interim individually rational and its trading rule is ex post
efficient (budget balance is not required), then the sum of the seller's and buyer's expected
utilities is at least `5/6`. (`y` measurable; integrability hypotheses say expectations exist.) -/
theorem exercise_23_E_7a {y t : (Fin 2 → ℝ) → Fin 2 → ℝ} (hym : Measurable y)
    (hint : InterimIntegrable unif2 allocV y t (fun _ => 0) (fun _ => 1))
    (ht : ∀ i, Integrable (fun θ => t θ i) unif2)
    (heff : ExPostEfficientTrade (fun _ => 0) (fun _ => 1) y)
    (hbic : BayesianICOn unif2 allocV y t (fun _ => 0) (fun _ => 1))
    (hir : InterimIR unif2 y t (fun _ => 0) (fun _ => 1)) :
    5 / 6 ≤ ∑ i, ∫ θ, linU allocV i (y θ, t θ) (θ i) ∂unif2 := by
  have := uniform01.isProbabilityMeasure
  have hae := re_ae_mem (fun _ : Fin 2 => uniform01.measure) (lo := fun _ => 0)
    (hi := fun _ => 1) ms_unif_hyps.1
  obtain ⟨c, hE, hc0, hc1, hgE⟩ := ms_core (fun _ : Fin 2 => uniform01.measure)
    (fun _ => zero_le_one) ms_unif_hyps.1 hym hint ht heff hbic hir
  have hq0 : ∫ θ, max (θ 1 - (fun _ : Fin 2 => (1 : ℝ)) 0) 0 ∂unif2 = 0 := by
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hae] with θ hθ
    exact max_eq_right (by linarith [(hθ 1).2])
  have hq1 : ∫ θ, max ((fun _ : Fin 2 => (0 : ℝ)) 1 - θ 0) 0 ∂unif2 = 0 := by
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hae] with θ hθ
    exact max_eq_right (by linarith [(hθ 0).1])
  have hyI : ∀ i, Integrable (fun θ => θ i * y θ i) unif2 := by
    intro i
    refine ms_integrable_of_bound (fun _ : Fin 2 => uniform01.measure) ms_unif_hyps.1
      ((measurable_pi_apply i).mul ((measurable_pi_apply i).comp hym)) 1 fun θ hθ => ?_
    obtain ⟨hs, h0, h1, -, -⟩ := heff θ hθ
    have hy : |y θ i| ≤ 1 := (Fin.forall_fin_two (p := fun i => |y θ i| ≤ 1)).2
      ⟨abs_le.2 ⟨by linarith, by linarith⟩, abs_le.2 ⟨by linarith, h1⟩⟩ i
    rw [abs_mul]
    exact (mul_le_mul (abs_le.2 ⟨by linarith [(hθ i).1], (hθ i).2⟩) hy (abs_nonneg _)
      zero_le_one).trans_eq (one_mul 1)
  have hval : ∫ θ, θ 0 * y θ 0 ∂unif2 + ∫ θ, θ 1 * y θ 1 ∂unif2 = 1 / 2 + 1 / 6 := by
    rw [← integral_add (hyI 0) (hyI 1), ← ms_unif_mean 0, ← ms_unif_gains, ← integral_add
      ((re_unif2_integrable (measurable_pi_apply 0) 1 fun θ hθ =>
        abs_le.2 ⟨by linarith [(hθ 0).1], (hθ 0).2⟩).1)
      (ms_integrable_pos_parts (fun _ : Fin 2 => uniform01.measure)
        (lo := fun _ => 0) (hi := fun _ => 1) ms_unif_hyps.1 0 0).2.2]
    refine integral_congr_ae ?_
    filter_upwards [hae] with θ hθ
    obtain ⟨hs, -, -, -, -⟩ := heff θ hθ
    have := ms_eff_mul heff hθ
    rw [show y θ 0 = 1 - y θ 1 by linarith]
    linarith
  rw [Fin.sum_univ_two]
  simp only [linU, allocV]
  rw [integral_add (hyI 0) (ht 0), integral_add (hyI 1) (ht 1), hE 0, hE 1]
  rw [hq0] at hc0
  rw [hq1] at hc1
  have := ms_unif_gains
  linarith

/-- The trading rule `twoY` (trade iff `θ₀ < θ₁`) is ex post efficient. -/
theorem twoY_efficient (lo hi : Fin 2 → ℝ) : ExPostEfficientTrade lo hi twoY := by
  intro θ _
  obtain ⟨h1, h2, h3, -, -⟩ := twoY_props θ
  refine ⟨h1, h2, h3, fun h => ?_, fun h => ?_⟩
  · simp [twoY, h]
  · simp [twoY, not_lt.2 h.le]

/-- `twoY` is measurable as a map into `ℝ²`. -/
theorem measurable_twoY' : Measurable twoY := Measurable.of_eval measurable_twoY

/-- **Exercise 23.E.7** (MWG, pp. 922-923): parts (a) and (b) together give the
Myerson-Satterthwaite conclusion for uniform types, since an ex post efficient (budget
balanced) social choice function is feasible: `5/6 > 2/3`. -/
theorem exercise_23_E_7 {y t : (Fin 2 → ℝ) → Fin 2 → ℝ} (hym : Measurable y)
    (hint : InterimIntegrable unif2 allocV y t (fun _ => 0) (fun _ => 1))
    (ht : ∀ i, Integrable (fun θ => t θ i) unif2)
    (heff : ExPostEfficientTrade (fun _ => 0) (fun _ => 1) y)
    (hbb : BudgetBalancedOn (fun _ => 0) (fun _ => 1) t)
    (hbic : BayesianICOn unif2 allocV y t (fun _ => 0) (fun _ => 1))
    (hir : InterimIR unif2 y t (fun _ => 0) (fun _ => 1)) : False := by
  have := uniform01.isProbabilityMeasure
  have ha := exercise_23_E_7a hym hint ht heff hbic hir
  have hyI : ∀ i, Integrable (fun θ => θ i * y θ i) unif2 := by
    intro i
    refine ms_integrable_of_bound (fun _ : Fin 2 => uniform01.measure) ms_unif_hyps.1
      ((measurable_pi_apply i).mul ((measurable_pi_apply i).comp hym)) 1 fun θ hθ => ?_
    obtain ⟨hs, h0, h1, -, -⟩ := heff θ hθ
    have hy : |y θ i| ≤ 1 := (Fin.forall_fin_two (p := fun i => |y θ i| ≤ 1)).2
      ⟨abs_le.2 ⟨by linarith, by linarith⟩, abs_le.2 ⟨by linarith, h1⟩⟩ i
    rw [abs_mul]
    exact (mul_le_mul (abs_le.2 ⟨by linarith [(hθ i).1], (hθ i).2⟩) hy (abs_nonneg _)
      zero_le_one).trans_eq (one_mul 1)
  have hb := exercise_23_E_7b (y := y) (t := t) (fun i => (hyI i).add (ht i)) fun θ hθ => by
    obtain ⟨hs, h0, h1, -, -⟩ := heff θ hθ
    exact ⟨by linarith, h0, hs.le, (hbb θ hθ).le⟩
  linarith

/-- The expected externality transfers for bilateral trade with uniform types
(Exercise 23.D.2(a)): `t₀ = (θ₁² - θ₀²)/2`, `t₁ = (θ₀² - θ₁²)/2`. -/
noncomputable def agvBT : (Fin 2 → ℝ) → Fin 2 → ℝ :=
  fun θ => ![(θ 1 ^ 2 - θ 0 ^ 2) / 2, (θ 0 ^ 2 - θ 1 ^ 2) / 2]

/-- `agvBT` is measurable and bounded by `1` on `[0, 1]²`. -/
theorem agvBT_facts : (∀ i, Measurable fun θ => agvBT θ i) ∧
    ∀ θ : Fin 2 → ℝ, (∀ j, θ j ∈ Set.Icc (0 : ℝ) 1) → ∀ i, |agvBT θ i| ≤ 1 := by
  refine ⟨fun i => ?_, fun θ hθ i => ?_⟩
  · fin_cases i
    · exact (((measurable_pi_apply 1).pow_const 2).sub
        ((measurable_pi_apply 0).pow_const 2)).div_const 2
    · exact (((measurable_pi_apply 0).pow_const 2).sub
        ((measurable_pi_apply 1).pow_const 2)).div_const 2
  · obtain ⟨a0, b0⟩ := hθ 0
    obtain ⟨a1, b1⟩ := hθ 1
    fin_cases i <;> simp only [agvBT, Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, abs_le] <;> constructor <;> nlinarith

/-- The interim transfers of `agvBT`: `t̄ᵢ(a) = 1/6 - a²/2`. -/
theorem agvBT_interim (i : Fin 2) (a : ℝ) :
    interimTransfer unif2 agvBT i a = 1 / 6 - a ^ 2 / 2 := by
  unfold interimTransfer
  rw [re_unif2_update (G := fun θ => agvBT θ i) (agvBT_facts.1 i) i a]
  have hI : IntervalIntegrable (fun x : ℝ => x ^ 2) volume 0 1 :=
    (continuous_pow 2).intervalIntegrable _ _
  fin_cases i
  · simp only [Fin.zero_eta, re_update_vec0, agvBT, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    rw [intervalIntegral.integral_div, intervalIntegral.integral_sub hI intervalIntegrable_const,
      integral_pow, intervalIntegral.integral_const]
    norm_num; ring
  · simp only [Fin.mk_one, re_update_vec1, agvBT, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    rw [intervalIntegral.integral_div, intervalIntegral.integral_sub hI intervalIntegrable_const,
      integral_pow, intervalIntegral.integral_const]
    norm_num; ring

/-- **Exercise 23.E.1** (MWG, p. 921). In the bilateral trade setting with types uniform on
`[0, 1]`, the expected externality mechanism (whose transfers are `agvBT` on `[0, 1]²`, Exercise
23.D.2(a)) is Bayesian incentive compatible, ex post efficient and budget balanced, but the seller
of type `θ₀ = 1` gets expected utility `U₀(1) = 2/3 < 1`, so he strictly prefers not to
participate: interim individual rationality fails. This is the non-vacuity instance of
Proposition 23.E.1 without individual rationality. -/
theorem exercise_23_E_1 :
    (∀ θ : Fin 2 → ℝ, (∀ j, θ j ∈ Set.Icc (0 : ℝ) 1) → ∀ i,
      agvTransfer unif2 bilatV bilatK (agvH unif2 bilatV bilatK) θ i = agvBT θ i) ∧
    InterimIntegrable unif2 allocV twoY agvBT (fun _ => 0) (fun _ => 1) ∧
    BayesianICOn unif2 allocV twoY agvBT (fun _ => 0) (fun _ => 1) ∧
    ExPostEfficientTrade (fun _ => 0) (fun _ => 1) twoY ∧
    BudgetBalancedOn (fun _ => 0) (fun _ => 1) agvBT ∧
    interimU unif2 allocV twoY agvBT 0 1 = 2 / 3 ∧
    ¬InterimIR unif2 twoY agvBT (fun _ => 0) (fun _ => 1) := by
  obtain ⟨hm, hb⟩ := agvBT_facts
  obtain ⟨hint, hbic, -, -⟩ := re_twoY_bic hm hb (1 / 6) fun i a _ => agvBT_interim i a
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hU : interimU unif2 allocV twoY agvBT 0 1 = 2 / 3 := by
    rw [interimU, twoY_interimBenefit h1, agvBT_interim 0 1]; norm_num
  refine ⟨fun θ hθ i => ?_, hint, hbic, twoY_efficient _ _, fun θ _ => ?_, hU, fun hir => ?_⟩
  · obtain ⟨e0, e1⟩ := exercise_23_D_2a hθ
    fin_cases i
    · simp only [Fin.zero_eta, e0, agvBT, Matrix.cons_val_zero]
    · simp only [Fin.mk_one, e1, agvBT, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  · simp only [agvBT, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]; ring
  · have := hir.1 1 h1
    rw [hU] at this
    norm_num at this

/-- The comparison rule `(y, t^g)` of the proof of Proposition 23.E.1 is interim individually
rational (each type's expected payoff is `θ₀ + E[(θ₁ - θ₀)⁺]` or `E[(θ₁ - θ₀)⁺]`). -/
theorem ms_vcg_interimIR {lo hi : Fin 2 → ℝ} (hsupp : ∀ i, μ i (Set.Icc (lo i) (hi i))ᶜ = 0)
    {y : (Fin 2 → ℝ) → Fin 2 → ℝ} (hym : Measurable y) (heff : ExPostEfficientTrade lo hi y)
    (hy : ∀ i, ∀ a ∈ Set.Icc (lo i) (hi i),
      Integrable (fun θ' => allocV i (y (update θ' i a))) (Measure.pi μ)) :
    InterimIR (Measure.pi μ) y (msVcgT y) lo hi := by
  obtain ⟨hint, -⟩ := ms_vcg_bic μ hsupp hym heff hy
  have hI : ∀ i, ∀ b ∈ Set.Icc (lo i) (hi i), Integrable (fun θ' =>
      linU allocV i (y (update θ' i b), msVcgT y (update θ' i b)) b) (Measure.pi μ) :=
    fun i b hb => ((hint i b hb).1.const_mul b).add (hint i b hb).2
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · rw [interimU, ← eq_23_D_10 (hint 0 x hx).1 (hint 0 x hx).2 x]
    have h := integral_mono_ae (integrable_const x) (hI 0 x hx) (by
      filter_upwards [re_ae_update_mem μ hsupp hx] with θ' h
      have := (ms_vcg_seller heff h x).2
      simp only [update_self] at this
      rw [this]; linarith [le_max_right ((update θ' 0 x) 1 - x) 0])
    simpa using h
  · rw [interimU, ← eq_23_D_10 (hint 1 x hx).1 (hint 1 x hx).2 x]
    exact integral_nonneg_of_ae (by
      filter_upwards [re_ae_update_mem μ hsupp hx] with θ' h
      have := (ms_vcg_buyer heff h x).2
      simp only [update_self] at this
      rw [this]; exact le_max_right _ _)

/-- Non-vacuity of Proposition 23.E.1 without budget balance: with uniform types the comparison
rule `t₀ = θ₁y₁`, `t₁ = -θ₀y₁` with efficient trade is Bayesian incentive compatible, interim
individually rational and ex post efficient in trade, but not budget balanced. -/
theorem proposition_23_E_1_instance_no_bb :
    InterimIntegrable unif2 allocV twoY (msVcgT twoY) (fun _ => 0) (fun _ => 1) ∧
    BayesianICOn unif2 allocV twoY (msVcgT twoY) (fun _ => 0) (fun _ => 1) ∧
    InterimIR unif2 twoY (msVcgT twoY) (fun _ => 0) (fun _ => 1) ∧
    ExPostEfficientTrade (fun _ => 0) (fun _ => 1) twoY ∧
    ¬BudgetBalancedOn (fun _ => 0) (fun _ => 1) (msVcgT twoY) := by
  have := uniform01.isProbabilityMeasure
  have hy : ∀ i, ∀ a ∈ Set.Icc ((fun _ : Fin 2 => (0 : ℝ)) i) ((fun _ : Fin 2 => (1 : ℝ)) i),
      Integrable (fun θ' => allocV i (twoY (update θ' i a))) unif2 := by
    intro i a ha
    refine (re_unif2_integrable (measurable_twoY i) 1 fun θ _ => ?_).2 i a ha
    obtain ⟨-, h2, h3, h4, h5⟩ := twoY_props θ
    exact (Fin.forall_fin_two (p := fun i => |allocV i (twoY θ)| ≤ 1)).2
      ⟨abs_le.2 ⟨by simp only [allocV]; linarith, h5⟩,
        abs_le.2 ⟨by simp only [allocV]; linarith, h3⟩⟩ i
  obtain ⟨hint, hbic⟩ := ms_vcg_bic (fun _ : Fin 2 => uniform01.measure) ms_unif_hyps.1
    measurable_twoY' (twoY_efficient _ _) hy
  refine ⟨hint, hbic, ms_vcg_interimIR (fun _ : Fin 2 => uniform01.measure) ms_unif_hyps.1
    measurable_twoY' (twoY_efficient _ _) hy, twoY_efficient _ _, fun hbb => ?_⟩
  have := hbb ![0, 1] fun j => by fin_cases j <;> simp
  simp [msVcgT, twoY] at this

/-- The posted-price rule at price `1/2`: trade iff `θ₀ ≤ 1/2 ≤ θ₁`. -/
noncomputable def postQ (θ : Fin 2 → ℝ) : ℝ :=
  if θ 0 ≤ 1 / 2 then (if 1 / 2 ≤ θ 1 then 1 else 0) else 0

/-- The posted-price allocation `(1 - q, q)`. -/
noncomputable def postY (θ : Fin 2 → ℝ) : Fin 2 → ℝ := ![1 - postQ θ, postQ θ]

/-- The posted-price transfers: the buyer pays the seller `1/2` when they trade. -/
noncomputable def postT (θ : Fin 2 → ℝ) : Fin 2 → ℝ := ![postQ θ / 2, -(postQ θ / 2)]

/-- `postQ` is measurable. -/
theorem measurable_postQ : Measurable postQ :=
  Measurable.ite (measurableSet_le (measurable_pi_apply 0) measurable_const)
    (Measurable.ite (measurableSet_le measurable_const (measurable_pi_apply 1)) measurable_const
      measurable_const) measurable_const

/-- Non-vacuity of Proposition 23.E.1 without ex post efficiency: with uniform types, the
posted-price rule at `1/2` is dominant strategy (hence Bayesian) incentive compatible, ex post
(hence interim) individually rational and budget balanced, but its trading rule is not ex post
efficient (no trade at `θ = (3/4, 7/8)`). -/
theorem proposition_23_E_1_instance_no_eff :
    InterimIntegrable unif2 allocV postY postT (fun _ => 0) (fun _ => 1) ∧
    DominantICOn (fun _ => 0) (fun _ => 1) postY postT ∧
    BayesianICOn unif2 allocV postY postT (fun _ => 0) (fun _ => 1) ∧
    ExPostIR (fun _ => 0) (fun _ => 1) postY postT ∧
    InterimIR unif2 postY postT (fun _ => 0) (fun _ => 1) ∧
    BudgetBalancedOn (fun _ => 0) (fun _ => 1) postT ∧
    ¬ExPostEfficientTrade (fun _ => 0) (fun _ => 1) postY := by
  have := uniform01.isProbabilityMeasure
  have hq : ∀ θ, 0 ≤ postQ θ ∧ postQ θ ≤ 1 := fun θ => by
    simp only [postQ]; split_ifs <;> norm_num
  have hint : InterimIntegrable unif2 allocV postY postT (fun _ => 0) (fun _ => 1) := by
    intro i a ha
    have hb : ∀ θ : Fin 2 → ℝ, |allocV i (postY θ)| ≤ 1 ∧ |postT θ i| ≤ 1 := by
      intro θ
      obtain ⟨h0, h1⟩ := hq θ
      fin_cases i <;> simp only [allocV, postY, postT, Fin.zero_eta, Fin.mk_one,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, abs_le] <;>
        constructor <;> constructor <;> linarith
    have hm : Measurable (fun θ => allocV i (postY θ)) ∧ Measurable fun θ => postT θ i := by
      fin_cases i
      · exact ⟨measurable_const.sub measurable_postQ, measurable_postQ.div_const 2⟩
      · exact ⟨measurable_postQ, (measurable_postQ.div_const 2).neg⟩
    exact ⟨(re_unif2_integrable hm.1 1 fun θ _ => (hb θ).1).2 i a ha,
      (re_unif2_integrable hm.2 1 fun θ _ => (hb θ).2).2 i a ha⟩
  have hds : DominantICOn (fun _ => 0) (fun _ => 1) postY postT := by
    intro i θ hθ a ha
    fin_cases i
    · simp only [Fin.zero_eta, linU, allocV, postY, postT, postQ, Matrix.cons_val_zero,
        update_self, update_of_ne (show (1 : Fin 2) ≠ 0 by decide)]
      split_ifs <;> linarith
    · simp only [Fin.mk_one, linU, allocV, postY, postT, postQ, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, update_self, update_of_ne (show (0 : Fin 2) ≠ 1 by decide)]
      split_ifs <;> linarith
  have hxir : ExPostIR (fun _ => 0) (fun _ => 1) postY postT := by
    intro θ _
    simp only [linU, allocV, postY, postT, postQ, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    constructor <;> split_ifs <;> linarith
  refine ⟨hint, hds, ms_bic_of_dsic (fun _ : Fin 2 => uniform01.measure) ms_unif_hyps.1 hint hds,
    hxir, ms_interimIR_of_exPostIR (fun _ : Fin 2 => uniform01.measure) ms_unif_hyps.1 hint hxir,
    fun θ _ => by simp [postT], fun heff => ?_⟩
  have h := (heff ![3 / 4, 7 / 8] fun j => by fin_cases j <;> norm_num).2.2.2.1 (by norm_num)
  norm_num [postY, postQ] at h

/-- The split-the-difference rule: trade iff `θ₀ < θ₁`, at the price `(θ₀ + θ₁)/2`. -/
noncomputable def splitT (θ : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![(θ 0 + θ 1) / 2 * twoY θ 1, -((θ 0 + θ 1) / 2 * twoY θ 1)]

/-- Non-vacuity of Proposition 23.E.1 without incentive compatibility: with uniform types, the
split-the-difference rule is ex post efficient (efficient trade and budget balance) and ex post
(hence interim) individually rational, but not Bayesian incentive compatible: a seller of type
`0` expects `1/4` from the truth and `5/16` from announcing `1/2`. -/
theorem proposition_23_E_1_instance_no_bic :
    InterimIntegrable unif2 allocV twoY splitT (fun _ => 0) (fun _ => 1) ∧
    ExPostEfficientTrade (fun _ => 0) (fun _ => 1) twoY ∧
    BudgetBalancedOn (fun _ => 0) (fun _ => 1) splitT ∧
    ExPostIR (fun _ => 0) (fun _ => 1) twoY splitT ∧
    InterimIR unif2 twoY splitT (fun _ => 0) (fun _ => 1) ∧
    ¬BayesianICOn unif2 allocV twoY splitT (fun _ => 0) (fun _ => 1) := by
  have := uniform01.isProbabilityMeasure
  have hm : ∀ i, Measurable fun θ => splitT θ i := by
    intro i; fin_cases i
    · exact (((measurable_pi_apply 0).add (measurable_pi_apply 1)).div_const 2).mul
        (measurable_twoY 1)
    · exact ((((measurable_pi_apply 0).add (measurable_pi_apply 1)).div_const 2).mul
        (measurable_twoY 1)).neg
  have hint : InterimIntegrable unif2 allocV twoY splitT (fun _ => 0) (fun _ => 1) := by
    intro i a ha
    refine ⟨(re_unif2_integrable (measurable_twoY i) 1 fun θ _ => ?_).2 i a ha,
      (re_unif2_integrable (hm i) 1 fun θ hθ => ?_).2 i a ha⟩
    · obtain ⟨-, h2, h3, h4, h5⟩ := twoY_props θ
      exact (Fin.forall_fin_two (p := fun i => |allocV i (twoY θ)| ≤ 1)).2
        ⟨abs_le.2 ⟨by simp only [allocV]; linarith, h5⟩,
          abs_le.2 ⟨by simp only [allocV]; linarith, h3⟩⟩ i
    · obtain ⟨-, h2, h3, -, -⟩ := twoY_props θ
      obtain ⟨a0, b0⟩ := hθ 0
      obtain ⟨a1, b1⟩ := hθ 1
      fin_cases i <;> simp only [splitT, Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, abs_le] <;> constructor <;> nlinarith
  have hxir : ExPostIR (fun _ => 0) (fun _ => 1) twoY splitT := by
    intro θ _
    simp only [linU, allocV, splitT, twoY, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    constructor <;> split_ifs <;> linarith
  refine ⟨hint, twoY_efficient _ _, fun θ _ => by simp [splitT], hxir,
    ms_interimIR_of_exPostIR (fun _ : Fin 2 => uniform01.measure) ms_unif_hyps.1 hint hxir,
    fun hbic => ?_⟩
  have hG : Measurable fun σ : Fin 2 → ℝ => linU allocV 0 (twoY σ, splitT σ) 0 := by
    simp only [linU, allocV, zero_mul, zero_add]
    exact hm 0
  have hval : ∀ a ∈ Set.Icc (0 : ℝ) 1, ∫ θ', linU allocV 0 (twoY (update θ' 0 a),
      splitT (update θ' 0 a)) 0 ∂unif2 = ∫ x in a..1, (a + x) / 2 := by
    intro a ha
    rw [re_unif2_update hG 0 a]
    simp only [re_update_vec0, linU, allocV, splitT, twoY, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, zero_mul, zero_add]
    have e : ∀ x : ℝ, (a + x) / 2 * (if a < x then (1 : ℝ) else 0) =
        if a < x then (a + x) / 2 else 0 := fun x => by split_ifs <;> ring
    simp only [e]
    exact re_integral_ite_gt ha _
  have h := hbic 0 0 ⟨le_rfl, zero_le_one⟩ (1 / 2) ⟨by norm_num, by norm_num⟩
  change ∫ θ', linU allocV 0 (twoY (update θ' 0 (1 / 2)), splitT (update θ' 0 (1 / 2))) 0
    ∂unif2 ≤ ∫ θ', linU allocV 0 (twoY (update θ' 0 0), splitT (update θ' 0 0)) 0 ∂unif2 at h
  rw [hval (1 / 2) ⟨by norm_num, by norm_num⟩, hval 0 ⟨le_rfl, zero_le_one⟩] at h
  rw [intervalIntegral.integral_div, intervalIntegral.integral_div,
    intervalIntegral.integral_add (g := fun x => x) intervalIntegrable_const
      (continuous_id.intervalIntegrable _ _),
    intervalIntegral.integral_add (g := fun x => x) intervalIntegrable_const
      (continuous_id.intervalIntegrable _ _), integral_id, integral_id,
    intervalIntegral.integral_const, intervalIntegral.integral_const]
    at h
  norm_num at h

/-! ### Exercise 23.E.3: two types each -/

/-- Exercise 23.E.3's valuations: the seller's are `0` (type `false`) or `2` (type `true`), the
buyer's `1` (type `false`) or `3` (type `true`). -/
def discVal : Fin 2 → Bool → ℝ :=
  fun i b => if i = 0 then (if b then 2 else 0) else (if b then 3 else 1)

/-- Linear utilities `θᵢyᵢ + tᵢ` with these valuations; outcomes are `(y, t)`. -/
def discU : Fin 2 → (Fin 2 → ℝ) × (Fin 2 → ℝ) → Bool → ℝ :=
  fun i x b => discVal i b * x.1 i + x.2 i

/-- Trade unless the seller has valuation `2` and the buyer `1` (exactly when `θ₀ < θ₁`), at
price `1` when both valuations are low and `2` otherwise. -/
def discF (θ : Fin 2 → Bool) : (Fin 2 → ℝ) × (Fin 2 → ℝ) :=
  let q : ℝ := if θ 0 = true ∧ θ 1 = false then 0 else 1
  let p : ℝ := if θ 0 = false ∧ θ 1 = false then 1 else 2
  (![1 - q, q], ![p * q, -(p * q)])

/-- **Exercise 23.E.3** (MWG, p. 922). With two equally likely valuations each, seller in
`{0, 2}` and buyer in `{1, 3}` (independent; `(0, 2) ∩ (1, 3) ≠ ∅`, so gains from trade are
possible but not certain), the social choice function `discF` is Bayesian incentive compatible,
ex post efficient (trade exactly when `θ₀ < θ₁`, budget balance) and ex post (hence interim)
individually rational. So the strictly positive density assumption of Proposition 23.E.1 cannot
be dropped. -/
theorem exercise_23_E_3 :
    BayesianIC (indepBeliefs (aaP (1 / 2))) discU discF ∧
    (∀ θ, (discF θ).1 0 + (discF θ).1 1 = 1 ∧
      ((discF θ).1 1 = 1 ↔ discVal 0 (θ 0) < discVal 1 (θ 1)) ∧
      ((discF θ).1 1 = 0 ↔ discVal 1 (θ 1) < discVal 0 (θ 0))) ∧
    (∀ θ, (discF θ).2 0 + (discF θ).2 1 = 0) ∧
    (∀ θ, discVal 0 (θ 0) ≤ discU 0 (discF θ) (θ 0) ∧ 0 ≤ discU 1 (discF θ) (θ 1)) ∧
    (∀ b, discVal 0 b ≤ ∫ θ', discU 0 (discF (update θ' 0 b)) b ∂aaP (1 / 2)) ∧
    (∀ b, 0 ≤ ∫ θ', discU 1 (discF (update θ' 1 b)) b ∂aaP (1 / 2)) := by
  have h0 : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have h1 : (1 / 2 : ℝ) ≤ 1 := by norm_num
  refine ⟨fun i θi θh => ?_, fun θ => ?_, fun θ => ?_, fun θ => ?_, fun b => ?_, fun b => ?_⟩
  · simp only [indepBeliefs]
    rw [integral_aaP _ h0 h1 i θh (fun σ => discU i (discF σ) θi),
      integral_aaP _ h0 h1 i θi (fun σ => discU i (discF σ) θi)]
    fin_cases i <;> cases θi <;> cases θh <;>
      simp [discU, discF, discVal] <;> norm_num
  · obtain ⟨b0, hb0⟩ : ∃ b, θ 0 = b := ⟨_, rfl⟩
    obtain ⟨b1, hb1⟩ : ∃ b, θ 1 = b := ⟨_, rfl⟩
    cases b0 <;> cases b1 <;> simp [discF, discVal, hb0, hb1]
    norm_num
  · simp [discF]
  · obtain ⟨b0, hb0⟩ : ∃ b, θ 0 = b := ⟨_, rfl⟩
    obtain ⟨b1, hb1⟩ : ∃ b, θ 1 = b := ⟨_, rfl⟩
    cases b0 <;> cases b1 <;> simp [discU, discF, discVal, hb0, hb1] <;> norm_num
  · rw [integral_aaP _ h0 h1 0 b (fun σ => discU 0 (discF σ) b)]
    cases b <;> simp [discU, discF, discVal] <;> norm_num
  · rw [integral_aaP _ h0 h1 1 b (fun σ => discU 1 (discF σ) b)]
    cases b <;> simp [discU, discF, discVal]
    norm_num

end MWG.MechanismDesign
