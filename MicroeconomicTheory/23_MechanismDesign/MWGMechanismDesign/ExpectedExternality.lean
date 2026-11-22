/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMechanismDesign.Independent
import MWGMechanismDesign.BudgetBalance

/-!
# The expected externality mechanism

MWG, Section 23.D, pp. 885-887.

In the quasilinear environment with statistically independent types, the expected externality
(d'Aspremont-Gérard-Varet, Arrow) mechanism pays agent `i`
`ξᵢ(θᵢ) = E_{θ̃₋ᵢ}[∑_{j≠i} vⱼ(k*(θᵢ, θ̃₋ᵢ), θ̃ⱼ)]` plus `hᵢ(θ₋ᵢ)` (23.D.8).

* `agv_bayesianIC`: for any `hᵢ(θ₋ᵢ)`, (23.D.8) is Bayesian incentive compatible.
* `agv_budgetBalanced`: with `hᵢ(θ₋ᵢ) = -(1/(I-1)) ∑_{j≠i} ξⱼ(θⱼ)` (23.D.9) and `I ≥ 2`, the
  transfers balance the budget, (23.D.7).
* `agv_exPostEfficient_bic`: hence, with independent types, an ex post efficient social choice
  function is Bayesian implementable (p. 887).

The integrability hypotheses say that the expectations in (23.D.8) exist; for finitely many
types they hold automatically (`agv_finite`).
-/

namespace MWG.MechanismDesign

open Function MeasureTheory Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Θ : ι → Type*} [∀ i, MeasurableSpace (Θ i)]
  {K : Type*}

/-- **(23.D.8)** (MWG, p. 886). The expected benefit of the agents `j ≠ i` when `i` announces `a`
and the others tell the truth, `ξᵢ(a) = E_{θ̃₋ᵢ}[∑_{j≠i} vⱼ(k*(a, θ̃₋ᵢ), θ̃ⱼ)]`. -/
noncomputable def expectedExternality (P : Measure ((i : ι) → Θ i))
    (v : (i : ι) → K → Θ i → ℝ) (k : ((i : ι) → Θ i) → K) (i : ι) (a : Θ i) : ℝ :=
  ∫ θ', ∑ j ∈ univ.erase i, v j (k (update θ' i a)) (θ' j) ∂P

/-- **(23.D.8)** (MWG, p. 886). The transfers `tᵢ(θ) = ξᵢ(θᵢ) + hᵢ(θ₋ᵢ)`. -/
noncomputable def agvTransfer (P : Measure ((i : ι) → Θ i)) (v : (i : ι) → K → Θ i → ℝ)
    (k : ((i : ι) → Θ i) → K) (h : (i : ι) → ((j : ι) → Θ j) → ℝ) :
    ((i : ι) → Θ i) → ι → ℝ :=
  fun θ i => expectedExternality P v k i (θ i) + h i θ

/-- **(23.D.9)** (MWG, p. 886). `hᵢ(θ₋ᵢ) = -(1/(I-1)) ∑_{j≠i} ξⱼ(θⱼ)`. -/
noncomputable def agvH (P : Measure ((i : ι) → Θ i)) (v : (i : ι) → K → Θ i → ℝ)
    (k : ((i : ι) → Θ i) → K) : (i : ι) → ((j : ι) → Θ j) → ℝ :=
  fun i θ => -(1 / ((Fintype.card ι : ℝ) - 1)) *
    ∑ j ∈ univ.erase i, expectedExternality P v k j (θ j)

/-- The `hᵢ` of (23.D.9) depends only on `θ₋ᵢ`. -/
theorem agvH_indepOwn (P : Measure ((i : ι) → Θ i)) (v : (i : ι) → K → Θ i → ℝ)
    (k : ((i : ι) → Θ i) → K) : IndepOwn (agvH P v k) := by
  intro i θ a
  simp only [agvH]
  congr 1
  exact sum_congr rfl fun j hj => by rw [update_of_ne (ne_of_mem_erase hj)]

/-- **Section 23.D** (MWG, p. 886). With independent types (beliefs equal to the prior `P`), the
expected externality mechanism (23.D.8) is Bayesian incentive compatible, for any `hᵢ(θ₋ᵢ)`:
`E[vᵢ(k*(θ̂ᵢ, θ₋ᵢ), θᵢ) + tᵢ(θ̂ᵢ, θ₋ᵢ)] = E[∑ⱼ vⱼ(k*(θ̂ᵢ, θ₋ᵢ), θⱼ)] + E[hᵢ(θ₋ᵢ)]`, which is
maximized by truth telling because `k*` satisfies (23.D.6). -/
theorem agv_bayesianIC (P : Measure ((i : ι) → Θ i)) [IsProbabilityMeasure P]
    {v : (i : ι) → K → Θ i → ℝ} (m : ι → ℝ) {k : ((i : ι) → Θ i) → K}
    (hk : EfficientProject v k) {h : (i : ι) → ((j : ι) → Θ j) → ℝ} (hh : IndepOwn h)
    (hint : ∀ i (a θi : Θ i) j,
      Integrable (fun θ' => v j (k (update θ' i a)) (update θ' i θi j)) P)
    (hhint : ∀ i, Integrable (h i) P) :
    BayesianIC (indepBeliefs P) (qlU v m) (fun θ => (k θ, agvTransfer P v k h θ)) := by
  intro i θi θh
  simp only [indepBeliefs]
  -- the total expected valuation when `i` (of type `θi`) announces `a`
  have key : ∀ a : Θ i, ∫ θ', qlU v m i (k (update θ' i a), agvTransfer P v k h (update θ' i a))
      θi ∂P = ∫ θ', ∑ j, v j (k (update θ' i a)) (update θ' i θi j) ∂P + m i + ∫ θ', h i θ' ∂P := by
    intro a
    have hi1 : Integrable (fun θ' => v i (k (update θ' i a)) θi) P := by
      simpa using hint i a θi i
    have hi2 : Integrable (fun θ' => ∑ j ∈ univ.erase i, v j (k (update θ' i a)) (θ' j)) P :=
      integrable_finsetSum _ fun j hj => by
        simpa [update_of_ne (ne_of_mem_erase hj)] using hint i a θi j
    have hsplit : (fun θ' => ∑ j, v j (k (update θ' i a)) (update θ' i θi j)) =
        fun θ' => v i (k (update θ' i a)) θi +
          ∑ j ∈ univ.erase i, v j (k (update θ' i a)) (θ' j) := by
      funext θ'
      rw [← add_sum_erase _ _ (mem_univ i)]
      simp only [update_self]
      congr 1
      exact sum_congr rfl fun j hj => by rw [update_of_ne (ne_of_mem_erase hj)]
    have hpt : (fun θ' => qlU v m i (k (update θ' i a),
        agvTransfer P v k h (update θ' i a)) θi) =
        fun θ' => (v i (k (update θ' i a)) θi + (m i + expectedExternality P v k i a)) +
          h i θ' := by
      funext θ'
      simp only [qlU, agvTransfer, update_self, hh i θ' a]
      ring
    set ξ := expectedExternality P v k i a with hξ
    have e1 : ∫ θ', (v i (k (update θ' i a)) θi + (m i + ξ)) + h i θ' ∂P =
        ∫ θ', (v i (k (update θ' i a)) θi + (m i + ξ)) ∂P + ∫ θ', h i θ' ∂P :=
      integral_add (hi1.add (integrable_const _)) (hhint i)
    have e2 : ∫ θ', (v i (k (update θ' i a)) θi + (m i + ξ)) ∂P =
        ∫ θ', v i (k (update θ' i a)) θi ∂P + (m i + ξ) := by
      rw [integral_add hi1 (integrable_const _), integral_const, probReal_univ, one_smul]
    have e3 : ∫ θ', ∑ j, v j (k (update θ' i a)) (update θ' i θi j) ∂P =
        ∫ θ', v i (k (update θ' i a)) θi ∂P +
          ∫ θ', ∑ j ∈ univ.erase i, v j (k (update θ' i a)) (θ' j) ∂P := by
      rw [hsplit, integral_add hi1 hi2]
    rw [hpt, e1, e2, e3, hξ, expectedExternality]
    ring
  rw [key θh, key θi]
  have hsum : ∀ a : Θ i, Integrable (fun θ' => ∑ j, v j (k (update θ' i a)) (update θ' i θi j)) P :=
    fun a => integrable_finsetSum _ fun j _ => hint i a θi j
  have := integral_mono (hsum θh) (hsum θi) fun θ' => hk (update θ' i θi) (k (update θ' i θh))
  linarith

/-- **(23.D.9)** (MWG, p. 886). With `I ≥ 2` and `hᵢ` as in (23.D.9), the expected externality
mechanism is budget balanced, (23.D.7). -/
theorem agv_budgetBalanced (hI : 2 ≤ Fintype.card ι) (P : Measure ((i : ι) → Θ i))
    (v : (i : ι) → K → Θ i → ℝ) (k : ((i : ι) → Θ i) → K) :
    BudgetBalanced (agvTransfer P v k (agvH P v k)) := by
  intro θ
  have hI' : ((Fintype.card ι : ℝ) - 1) ≠ 0 := by
    have : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hI
    intro h; linarith
  simp only [agvTransfer, agvH, sum_add_distrib, ← mul_sum,
    sum_sum_erase fun j => expectedExternality P v k j (θ j)]
  field_simp
  ring

/-- **Section 23.D** (MWG, p. 887). With statistically independent types and `I ≥ 2`, the
expected externality mechanism with (23.D.9) implements an ex post efficient social choice
function in Bayesian Nash equilibrium: its project rule satisfies (23.D.6), it is budget
balanced (23.D.7), and it is Bayesian incentive compatible. -/
theorem agv_exPostEfficient_bic (hI : 2 ≤ Fintype.card ι) (P : Measure ((i : ι) → Θ i))
    [IsProbabilityMeasure P] {v : (i : ι) → K → Θ i → ℝ} (m : ι → ℝ)
    {k : ((i : ι) → Θ i) → K} (hk : EfficientProject v k)
    (hint : ∀ i (a θi : Θ i) j,
      Integrable (fun θ' => v j (k (update θ' i a)) (update θ' i θi j)) P)
    (hξ : ∀ j : ι, Integrable (fun θ : (l : ι) → Θ l => expectedExternality P v k j (θ j)) P) :
    EfficientProject v k ∧ BudgetBalanced (agvTransfer P v k (agvH P v k)) ∧
      BayesianIC (indepBeliefs P) (qlU v m)
        (fun θ => (k θ, agvTransfer P v k (agvH P v k) θ)) :=
  ⟨hk, agv_budgetBalanced hI P v k, agv_bayesianIC P m hk (agvH_indepOwn P v k) hint
    fun _ => (integrable_finsetSum _ fun j _ => hξ j).const_mul _⟩

/-- **Section 23.D**, the finite case (MWG, p. 887). With finitely many types, the integrability
hypotheses hold, so the expected externality mechanism with (23.D.9) is budget balanced and
Bayesian incentive compatible whenever `k*` satisfies (23.D.6) and `I ≥ 2`. -/
theorem agv_finite (hI : 2 ≤ Fintype.card ι) [Finite ((i : ι) → Θ i)]
    [MeasurableSingletonClass ((i : ι) → Θ i)] (P : Measure ((i : ι) → Θ i))
    [IsProbabilityMeasure P] {v : (i : ι) → K → Θ i → ℝ} (m : ι → ℝ)
    {k : ((i : ι) → Θ i) → K} (hk : EfficientProject v k) :
    BudgetBalanced (agvTransfer P v k (agvH P v k)) ∧
      BayesianIC (indepBeliefs P) (qlU v m)
        (fun θ => (k θ, agvTransfer P v k (agvH P v k) θ)) :=
  (agv_exPostEfficient_bic hI P m hk (fun _ _ _ _ => Integrable.of_finite)
    fun _ => Integrable.of_finite).2

end MWG.MechanismDesign
