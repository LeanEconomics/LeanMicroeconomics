/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMechanismDesign.MyersonSatterthwaite
import MWGMechanismDesign.Examples23B

/-!
# Auctions and bilateral trade in Section 23.B

MWG, Section 23.B, pp. 863-869 (Examples 23.B.4-23.B.7, Definitions 23.B.3-23.B.4 for auctions)
and Exercises 23.B.2-23.B.4 (p. 918).

Two buyers (or a seller `0` and a buyer `1`) with types independent and uniform on `[0, 1]`
(`unif2`); an outcome is `(y, t)` with `y` the vector of probabilities of holding the good and
`uᵢ((y, t), θᵢ) = θᵢyᵢ + tᵢ` (`linU allocV`). The allocation `twoY` gives the good to agent `0`
iff `θ₁ ≤ θ₀` (ties to the lowest index, MWG's footnotes 8 and 10). Agent `0` here is MWG's buyer
1 (or seller), agent `1` MWG's buyer 2 (or buyer); the auctioneer of footnote 5 is left out, as
his transfer `t₀ = -(t₁ + t₂)` does not affect the buyers.

* **Example 23.B.4** (pp. 863-864): for the social choice function (23.B.3)-(23.B.8) (the winner
  pays his valuation), if the other buyer tells the truth, buyer `i`'s expected utility from
  announcing `θ̂ ∈ [0, 1]` is `(θᵢ - θ̂)θ̂`, uniquely maximized at `θ̂ = θᵢ/2`; truth telling is not
  optimal (`example_23_B_4_firstPriceType`). For the second-price variant truth telling is a
  weakly dominant strategy (`example_23_B_4_secondPriceType`).
* **Example 23.B.5** (pp. 865-866), the first-price sealed-bid auction: against `b_j = α_jθ_j`
  (`α_j > 0`), bidding `b ≥ 0` gives `(θᵢ - b) min(b/α_j, 1)` (`fp_interim`), maximized at
  `min(θᵢ/2, α_j)` (`example_23_B_5_bestResponse`); `bᵢ = θᵢ/2` is a Bayesian Nash
  equilibrium that implements (23.B.9)-(23.B.14) (`example_23_B_5`).
* **Example 23.B.6** and **Exercise 23.B.3** (pp. 866-867, 918), the second-price sealed-bid
  auction with any number of buyers: `bᵢ = θᵢ` is weakly dominant (`exercise_23_B_3`), for any
  real bids (`sp_truth_dominant`); with two buyers it implements the second-price social choice
  function (`example_23_B_6`). The general first- and second-price outcome functions (p. 867)
  are `firstPriceOutcome`, `secondPriceOutcome` (winner: lowest index among the highest bids).
* **Example 23.B.7** (pp. 868-869): in the direct mechanism for (23.B.9)-(23.B.14), announcing
  `θ̂` gives `(θᵢ - θ̂/2)θ̂`, maximized at `θ̂ = θᵢ` (`example_23_B_7`).
* **Exercise 23.B.2** (the split-the-difference rule `splitT` of `MyersonSatterthwaite.lean`:
  trade iff `θ₁ > θ₀`, at price `(θ₀ + θ₁)/2`): if the seller tells the truth, the buyer's
  expected utility from announcing `θ̂` is `θ₂θ̂ - 3θ̂²/4`, maximized at `θ̂ = 2θ₂/3`: the buyer
  understates his valuation (`exercise_23_B_2`). Also `example_23_B_4_auction_efficient`: the
  social choice function (23.B.3)-(23.B.8) is ex post efficient (p. 863).
* **Exercise 23.B.4**, the double auction: `b₁ = 2θ₁/3 + 1/4`, `b₂ = 2θ₂/3 + 1/12` is a Bayesian
  Nash equilibrium (`exercise_23_B_4a`); it implements "trade iff `θ₂ > θ₁ + 1/4`, at price
  `(θ₁ + θ₂)/3 + 1/6`" (`exercise_23_B_4a_outcome`), which is not ex post efficient
  (`exercise_23_B_4a_not_efficient`) and is Bayesian incentive compatible (`exercise_23_B_4b`).

Departures. Types are real numbers with the uniform prior on `[0, 1]`; a Bayesian Nash
equilibrium is required for the types in `[0, 1]` and bids `b ≥ 0` (`IsBNEOn`); the interim
expected utilities are computed exactly from the uniform distribution, as MWG pose the buyers'
problems. Exercise 23.B.4(a) asks for "a" linear equilibrium: we verify the
Chatterjee-Samuelson one (MWG's other linear equilibria are not classified).
-/

namespace MWG.MechanismDesign

open MeasureTheory Function Set

/-! ### Integration tools -/

/-- `max 0 (min τ 1)`, the point of `[0, 1]` nearest to `τ`. -/
def clamp01 (τ : ℝ) : ℝ := max 0 (min τ 1)

/-- `clamp01 τ ∈ [0, 1]`. -/
theorem clamp01_mem (τ : ℝ) : clamp01 τ ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩

/-- `clamp01 τ = τ` on `[0, 1]`. -/
theorem clamp01_of_mem {τ : ℝ} (h : τ ∈ Icc (0 : ℝ) 1) : clamp01 τ = τ := by
  simp [clamp01, h.1, h.2]

/-- `clamp01 τ = 0` for `τ ≤ 0`. -/
theorem clamp01_of_nonpos {τ : ℝ} (h : τ ≤ 0) : clamp01 τ = 0 := by
  simp [clamp01, h.trans zero_le_one, h]

/-- `clamp01 τ = 1` for `τ ≥ 1`. -/
theorem clamp01_of_one_le {τ : ℝ} (h : 1 ≤ τ) : clamp01 τ = 1 := by
  simp [clamp01, h]

/-- `∫_0^1 1{x ≤ τ} g(x) dx = ∫_0^{clamp τ} g` for every real `τ`. -/
theorem au_int_le (τ : ℝ) (g : ℝ → ℝ) :
    ∫ x in (0 : ℝ)..1, (if x ≤ τ then g x else 0) = ∫ x in (0 : ℝ)..clamp01 τ, g x := by
  rcases le_or_gt τ 0 with h | h
  · rw [clamp01_of_nonpos h, intervalIntegral.integral_same,
      intervalIntegral.integral_of_le zero_le_one]
    refine setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_
    simp [not_le.2 (lt_of_le_of_lt h hx.1)]
  · rcases le_or_gt τ 1 with h1 | h1
    · rw [clamp01_of_mem ⟨h.le, h1⟩]; exact re_integral_ite_le ⟨h.le, h1⟩ g
    · rw [clamp01_of_one_le h1.le]
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [uIcc_of_le zero_le_one] at hx
      simp [hx.2.trans h1.le]

/-- `∫_0^1 1{x < τ} g(x) dx = ∫_0^{clamp τ} g` for every real `τ`. -/
theorem au_int_lt (τ : ℝ) (g : ℝ → ℝ) :
    ∫ x in (0 : ℝ)..1, (if x < τ then g x else 0) = ∫ x in (0 : ℝ)..clamp01 τ, g x := by
  rcases le_or_gt τ 0 with h | h
  · rw [clamp01_of_nonpos h, intervalIntegral.integral_same]
    refine (intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun x hx => ?_).trans
      (by simp)
    rw [uIcc_of_le zero_le_one] at hx
    simp [not_lt.2 (h.trans hx.1)]
  · rcases le_or_gt τ 1 with h1 | h1
    · rw [clamp01_of_mem ⟨h.le, h1⟩]; exact re_integral_ite_lt ⟨h.le, h1⟩ g
    · rw [clamp01_of_one_le h1.le]
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [uIcc_of_le zero_le_one] at hx
      simp [lt_of_le_of_lt hx.2 h1]

/-- `∫_0^1 1{τ < x} g(x) dx = ∫_{clamp τ}^1 g` for every real `τ`. -/
theorem au_int_gt (τ : ℝ) (g : ℝ → ℝ) :
    ∫ x in (0 : ℝ)..1, (if τ < x then g x else 0) = ∫ x in clamp01 τ..1, g x := by
  rcases lt_or_ge τ 0 with h | h
  · rw [clamp01_of_nonpos h.le]
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le zero_le_one] at hx
    simp [lt_of_lt_of_le h hx.1]
  · rcases le_or_gt τ 1 with h1 | h1
    · rw [clamp01_of_mem ⟨h, h1⟩]; exact re_integral_ite_gt ⟨h, h1⟩ g
    · rw [clamp01_of_one_le h1.le, intervalIntegral.integral_same]
      refine (intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun x hx => ?_).trans
        (by simp)
      rw [uIcc_of_le zero_le_one] at hx
      simp [not_lt.2 (hx.2.trans h1.le)]

/-- `∫_a^b (A + Bx) dx = A(b - a) + B(b² - a²)/2`. -/
theorem au_int_affine (A B a b : ℝ) :
    ∫ x in a..b, (A + B * x) = A * (b - a) + B * ((b ^ 2 - a ^ 2) / 2) := by
  rw [intervalIntegral.integral_add intervalIntegrable_const
    ((by fun_prop : Continuous fun x : ℝ => B * x).intervalIntegrable a b),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id,
    smul_eq_mul]
  ring

/-- With two independent uniform types, the expectation of a function of `θⱼ` alone is
`∫_0^1`. -/
theorem au_eval {H : ℝ → ℝ} (hH : Measurable H) (j : Fin 2) :
    ∫ θ, H (θ j) ∂unif2 = ∫ x in (0 : ℝ)..1, H x := by
  have := uniform01.isProbabilityMeasure
  exact (integral_eval_pi (Θ := fun _ => ℝ) (fun _ : Fin 2 => uniform01.measure) j
    hH.aestronglyMeasurable).trans (uniform01_integral _)

/-- `x ↦ 1{x ≤ τ}(A + Bx)` is measurable. -/
theorem au_meas_le (τ A B : ℝ) : Measurable fun x : ℝ => if x ≤ τ then A + B * x else 0 :=
  Measurable.ite measurableSet_Iic (by fun_prop) measurable_const

/-- `x ↦ 1{x < τ}(A + Bx)` is measurable. -/
theorem au_meas_lt (τ A B : ℝ) : Measurable fun x : ℝ => if x < τ then A + B * x else 0 :=
  Measurable.ite measurableSet_Iio (by fun_prop) measurable_const

/-- `x ↦ 1{τ < x}(A + Bx)` is measurable. -/
theorem au_meas_gt (τ A B : ℝ) : Measurable fun x : ℝ => if τ < x then A + B * x else 0 :=
  Measurable.ite measurableSet_Ioi (by fun_prop) measurable_const

/-! ### Example 23.B.4: the auction social choice functions -/

/-- **(23.B.6)-(23.B.7)** (MWG, p. 863). The winner pays his own valuation:
`tᵢ(θ) = -θᵢyᵢ(θ)`. -/
noncomputable def fullPriceT : (Fin 2 → ℝ) → Fin 2 → ℝ :=
  fun θ => ![-(θ 0 * twoY θ 0), -(θ 1 * twoY θ 1)]

/-- **Example 23.B.4** (MWG, pp. 863-864). For the social choice function (23.B.3)-(23.B.8), with
the other buyer truthful, buyer `i`'s expected utility from announcing `a ∈ [0, 1]` is
`(θᵢ - a) Prob(θⱼ ≤ a) = (θᵢ - a)a`. -/
theorem fullPrice_interim (i : Fin 2) (θi : ℝ) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) :
    ∫ θ', linU allocV i (twoY (update θ' i a), fullPriceT (update θ' i a)) θi ∂unif2 =
      (θi - a) * a := by
  have hm : Measurable fun θ : Fin 2 → ℝ => linU allocV i (twoY θ, fullPriceT θ) θi := by
    simp only [linU, allocV]
    refine (measurable_const.mul (measurable_twoY i)).add ?_
    fin_cases i
    · exact ((measurable_pi_apply 0).mul (measurable_twoY 0)).neg
    · exact ((measurable_pi_apply 1).mul (measurable_twoY 1)).neg
  rw [re_unif2_update (G := fun θ => linU allocV i (twoY θ, fullPriceT θ) θi) hm i a]
  fin_cases i
  · simp only [Fin.zero_eta, re_update_vec0, linU, allocV, fullPriceT, twoY,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    have e : ∀ x : ℝ, θi * (if x ≤ a then (1 : ℝ) else 0) + -(a * if x ≤ a then 1 else 0) =
        if x ≤ a then (θi - a) + 0 * x else 0 := fun x => by split_ifs <;> ring
    simp only [e]
    rw [re_integral_ite_le ha, au_int_affine]; ring
  · simp only [Fin.mk_one, re_update_vec1, linU, allocV, fullPriceT, twoY,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    have e : ∀ x : ℝ, θi * (if x < a then (1 : ℝ) else 0) + -(a * if x < a then 1 else 0) =
        if x < a then (θi - a) + 0 * x else 0 := fun x => by split_ifs <;> ring
    simp only [e]
    rw [re_integral_ite_lt ha, au_int_affine]; ring

/-- **Example 23.B.4** (MWG, pp. 863-864). Buyer `i`'s problem `max_{θ̂} (θᵢ - θ̂)θ̂` over
`θ̂ ∈ [0, 1]` has the unique solution `θ̂ = θᵢ/2`; for `θᵢ ∈ (0, 1]` truth telling is not optimal
(it gives `0 < θᵢ²/4`). -/
theorem example_23_B_4_firstPriceType (i : Fin 2) {θi : ℝ} (hθ : θi ∈ Icc (0 : ℝ) 1) :
    θi / 2 ∈ Icc (0 : ℝ) 1 ∧
      (∀ a ∈ Icc (0 : ℝ) 1,
        ∫ θ', linU allocV i (twoY (update θ' i a), fullPriceT (update θ' i a)) θi ∂unif2 ≤
          ∫ θ', linU allocV i (twoY (update θ' i (θi / 2)), fullPriceT (update θ' i (θi / 2)))
            θi ∂unif2) ∧
      (∀ a ∈ Icc (0 : ℝ) 1,
        ∫ θ', linU allocV i (twoY (update θ' i a), fullPriceT (update θ' i a)) θi ∂unif2 =
          ∫ θ', linU allocV i (twoY (update θ' i (θi / 2)), fullPriceT (update θ' i (θi / 2)))
            θi ∂unif2 → a = θi / 2) ∧
      (0 < θi → ∫ θ', linU allocV i (twoY (update θ' i θi), fullPriceT (update θ' i θi)) θi
          ∂unif2 < ∫ θ', linU allocV i (twoY (update θ' i (θi / 2)),
            fullPriceT (update θ' i (θi / 2))) θi ∂unif2) := by
  have hh : θi / 2 ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  refine ⟨hh, fun a ha => ?_, fun a ha he => ?_, fun hpos => ?_⟩
  · rw [fullPrice_interim i θi ha, fullPrice_interim i θi hh]; nlinarith [sq_nonneg (a - θi / 2)]
  · rw [fullPrice_interim i θi ha, fullPrice_interim i θi hh] at he
    nlinarith [sq_nonneg (a - θi / 2)]
  · rw [fullPrice_interim i θi hθ, fullPrice_interim i θi hh]; nlinarith

/-- **Example 23.B.4** (MWG, p. 864). For the second-price social choice function (the winner pays
the other's valuation), truth telling is a weakly dominant strategy for each buyer, whatever the
other announces: the social choice function is strategy-proof (for all real valuations). -/
theorem example_23_B_4_secondPriceType :
    StrategyProof (Θ := fun _ : Fin 2 => ℝ) (linU allocV) fun θ => (twoY θ, secondPriceT θ) := by
  intro i θ θh
  fin_cases i
  · simp only [Fin.zero_eta, linU, allocV, twoY, secondPriceT, update_self,
      update_of_ne (show (1 : Fin 2) ≠ 0 by decide), Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    split_ifs <;> linarith
  · simp only [Fin.mk_one, linU, allocV, twoY, secondPriceT, update_self,
      update_of_ne (show (0 : Fin 2) ≠ 1 by decide), Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    split_ifs <;> linarith

/-- **Example 23.B.4** (MWG, p. 863). The auction social choice function (23.B.3)-(23.B.8) with the
seller as agent `0` and buyers `1, 2` (footnote 5), as an allocation of the good (`QLAlt`): buyer
`1` gets the good iff `θ₁ ≥ θ₂`, the winner pays his valuation to the seller. -/
noncomputable def auctionSCF (θ : Fin 3 → ℝ) : QLAlt (Fin 3) (Fin 3) :=
  ⟨(if θ 2 ≤ θ 1 then 1 else 2,
    ![θ 1 * (if θ 2 ≤ θ 1 then 1 else 0) + θ 2 * (if θ 2 ≤ θ 1 then 0 else 1),
      -(θ 1 * if θ 2 ≤ θ 1 then 1 else 0), -(θ 2 * if θ 2 ≤ θ 1 then 0 else 1)]),
    le_of_eq (by simp [Fin.sum_univ_three])⟩

/-- **Example 23.B.4** (MWG, p. 863). "`f(·)` is ex post efficient": at every profile with the
seller's valuation `θ₀ = 0` and buyers' valuations in `[0, 1]` (only `θ₁ ≥ 0` is used), no
feasible alternative (`∑ᵢ yᵢ = 1`, `∑ᵢ tᵢ ≤ 0`) makes someone better off and nobody worse off. -/
theorem example_23_B_4_auction_efficient (θ : Fin 3 → ℝ) (h0 : θ 0 = 0) (h1 : 0 ≤ θ 1) :
    ¬∃ x : QLAlt (Fin 3) (Fin 3), (∀ i, qlU goodV 0 i (auctionSCF θ).1 (θ i) ≤
      qlU goodV 0 i x.1 (θ i)) ∧ ∃ i, qlU goodV 0 i (auctionSCF θ).1 (θ i) <
        qlU goodV 0 i x.1 (θ i) := by
  rintro ⟨x, hx, j, hj⟩
  have hsum := Finset.sum_lt_sum (fun i _ => hx i) ⟨j, Finset.mem_univ j, hj⟩
  simp only [qlU, goodV, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ,
    ↓reduceIte, Pi.zero_apply, zero_add] at hsum
  have hmax : ∀ k : Fin 3, θ k ≤ θ (auctionSCF θ).1.1 := by
    intro k
    simp only [auctionSCF]
    fin_cases k <;> split_ifs with h <;> simp <;> linarith
  have hx2 := x.2
  have ht : ∑ i, (auctionSCF θ).1.2 i = 0 := by simp [auctionSCF, Fin.sum_univ_three]
  linarith [hmax x.1.1]

/-! ### Example 23.B.7 and Exercise 23.B.2 -/

/-- **Example 23.B.7** (MWG, pp. 868-869). In the direct revelation mechanism for
(23.B.9)-(23.B.14), buyer `i`'s expected utility from announcing `a ∈ [0, 1]` when the other
tells the truth is `(θᵢ - a/2) Prob(θⱼ ≤ a) = (θᵢ - a/2)a`; it is maximized at `a = θᵢ`, so truth
telling is optimal, and the social choice function is Bayesian incentive compatible. -/
theorem example_23_B_7 (i : Fin 2) (θi : ℝ) :
    (∀ a ∈ Icc (0 : ℝ) 1,
      ∫ θ', linU allocV i (twoY (update θ' i a), firstPriceT (update θ' i a)) θi ∂unif2 =
        (θi - a / 2) * a) ∧
      (∀ a ∈ Icc (0 : ℝ) 1, (θi - a / 2) * a ≤ (θi - θi / 2) * θi) ∧
      BayesianICOn unif2 allocV twoY firstPriceT (fun _ => 0) (fun _ => 1) := by
  have key : ∀ a ∈ Icc (0 : ℝ) 1,
      ∫ θ', linU allocV i (twoY (update θ' i a), firstPriceT (update θ' i a)) θi ∂unif2 =
        (θi - a / 2) * a := by
    intro a ha
    have hm : Measurable fun θ : Fin 2 → ℝ => linU allocV i (twoY θ, firstPriceT θ) θi := by
      simp only [linU, allocV]
      refine (measurable_const.mul (measurable_twoY i)).add ?_
      fin_cases i
      · exact (((measurable_pi_apply 0).mul (measurable_twoY 0)).div_const 2).neg
      · exact (((measurable_pi_apply 1).mul (measurable_twoY 1)).div_const 2).neg
    rw [re_unif2_update (G := fun θ => linU allocV i (twoY θ, firstPriceT θ) θi) hm i a]
    fin_cases i
    · simp only [Fin.zero_eta, re_update_vec0, linU, allocV, firstPriceT, twoY,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      have e : ∀ x : ℝ, θi * (if x ≤ a then (1 : ℝ) else 0) + -(a * (if x ≤ a then 1 else 0) / 2)
          = if x ≤ a then (θi - a / 2) + 0 * x else 0 := fun x => by split_ifs <;> ring
      simp only [e]
      rw [re_integral_ite_le ha, au_int_affine]; ring
    · simp only [Fin.mk_one, re_update_vec1, linU, allocV, firstPriceT, twoY,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      have e : ∀ x : ℝ, θi * (if x < a then (1 : ℝ) else 0) + -(a * (if x < a then 1 else 0) / 2)
          = if x < a then (θi - a / 2) + 0 * x else 0 := fun x => by split_ifs <;> ring
      simp only [e]
      rw [re_integral_ite_lt ha, au_int_affine]; ring
  exact ⟨key, fun a _ => by nlinarith [sq_nonneg (a - θi)], exercise_23_D_3.1⟩

/-- **Exercise 23.B.2** (MWG, p. 918). For the social choice function `(twoY, splitT)` (the
buyer gets the good iff `θ₁ > θ₀` and pays `(θ₀ + θ₁)/2`), with the seller truthful and both
types uniform on `[0, 1]`, the buyer's expected utility from announcing `a ∈ [0, 1]` is
`∫_0^a (θ₂ - (x + a)/2) dx = θ₂a - 3a²/4`. It is maximized at `a = 2θ₂/3`, so for `θ₂ ∈ (0, 1]`
the buyer does not reveal his type: he understates his valuation to lower the price, at the
cost of trading less often (like a monopsonist). -/
theorem exercise_23_B_2 {θb : ℝ} (hθ : θb ∈ Icc (0 : ℝ) 1) :
    (∀ a ∈ Icc (0 : ℝ) 1,
      ∫ θ', linU allocV 1 (twoY (update θ' 1 a), splitT (update θ' 1 a)) θb ∂unif2 =
        θb * a - 3 * a ^ 2 / 4) ∧
      2 * θb / 3 ∈ Icc (0 : ℝ) 1 ∧
      (∀ a ∈ Icc (0 : ℝ) 1, θb * a - 3 * a ^ 2 / 4 ≤ θb * (2 * θb / 3) - 3 * (2 * θb / 3) ^ 2 / 4) ∧
      (0 < θb → θb * θb - 3 * θb ^ 2 / 4 < θb * (2 * θb / 3) - 3 * (2 * θb / 3) ^ 2 / 4) := by
  refine ⟨fun a ha => ?_, ⟨by linarith [hθ.1], by linarith [hθ.2]⟩,
    fun a _ => by nlinarith [sq_nonneg (a - 2 * θb / 3)], fun h => by nlinarith⟩
  have hm : Measurable fun θ : Fin 2 → ℝ => linU allocV 1 (twoY θ, splitT θ) θb := by
    simp only [linU, allocV, splitT, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    exact (measurable_const.mul (measurable_twoY 1)).add
      ((((measurable_pi_apply 0).add (measurable_pi_apply 1)).div_const 2).mul
        (measurable_twoY 1)).neg
  rw [re_unif2_update (G := fun θ => linU allocV 1 (twoY θ, splitT θ) θb) hm 1 a]
  simp only [re_update_vec1, linU, allocV, splitT, twoY, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  have e : ∀ x : ℝ, θb * (if x < a then (1 : ℝ) else 0) + -((x + a) / 2 * if x < a then 1 else 0)
      = if x < a then (θb - a / 2) + (-1 / 2) * x else 0 := fun x => by split_ifs <;> ring
  simp only [e]
  rw [re_integral_ite_lt ha, au_int_affine]; ring

/-! ### Bayesian Nash equilibrium on the type space -/

/-- **Definition 23.D.1** (MWG, p. 883; used informally on p. 865) relative to a type space
`Tᵢ ⊆ Θᵢ` and a strategy space `Aᵢ ⊆ Sᵢ`: `sᵢ*(θᵢ) ∈ Aᵢ` and, for every type `θᵢ ∈ Tᵢ`, no action
in `Aᵢ` gives a higher interim expected utility than `sᵢ*(θᵢ)`. -/
def IsBNEOn {ι : Type*} [DecidableEq ι] {Θ : ι → Type*} [∀ i, MeasurableSpace (Θ i)]
    {X : Type*} {S : ι → Type*} (B : (i : ι) → Θ i → Measure ((j : ι) → Θ j))
    (u : (i : ι) → X → Θ i → ℝ) (Γ : Mechanism S X) (s : (i : ι) → Θ i → S i)
    (T : (i : ι) → Set (Θ i)) (A : (i : ι) → Set (S i)) : Prop :=
  (∀ i, ∀ θi ∈ T i, s i θi ∈ A i) ∧ ∀ i, ∀ θi ∈ T i, ∀ a ∈ A i,
    interimUtility B u Γ s i θi a ≤ interimUtility B u Γ s i θi (s i θi)

/-! ### Example 23.B.5: the first-price sealed-bid auction -/

/-- **Example 23.B.5** (MWG, pp. 865, 867). The first-price sealed-bid auction with two bidders:
bids `bᵢ`, the highest bid wins (ties to bidder `0`, footnote 8) and the winner pays his bid,
`tᵢ = -bᵢyᵢ`. -/
noncomputable def fpMech2 : Mechanism (fun _ : Fin 2 => ℝ) ((Fin 2 → ℝ) × (Fin 2 → ℝ)) :=
  ⟨fun b => (twoY b, fullPriceT b)⟩

/-- **Example 23.B.5** (MWG, p. 865). Linear bidding strategies `bᵢ(θᵢ) = αᵢθᵢ`. -/
def linStrat (α : Fin 2 → ℝ) : (i : Fin 2) → ℝ → ℝ := fun i θ => α i * θ

/-- **Example 23.B.5** (MWG, p. 865). If the other bidder `j` bids `αⱼθⱼ` (`αⱼ > 0`), bidder `i`
of type `θᵢ` bidding `b` has expected utility `(θᵢ - b) Prob(αⱼθⱼ ≤ b) = (θᵢ - b) clamp(b/αⱼ)`
(`clamp(b/αⱼ) = b/αⱼ` for `b ∈ [0, αⱼ]`, as in MWG's restated problem, and `1` for `b ≥ αⱼ`). -/
theorem fp_interim (α : Fin 2 → ℝ) (hα : ∀ j, 0 < α j) (i : Fin 2) (θi b : ℝ) :
    interimUtility (indepBeliefs unif2) (linU allocV) fpMech2 (linStrat α) i θi b =
      (θi - b) * clamp01 (b / α (1 - i)) := by
  unfold interimUtility indepBeliefs
  fin_cases i
  · have e : (fun θ : Fin 2 → ℝ => linU allocV 0
        (fpMech2.outcome (update (play (linStrat α) θ) 0 b)) θi) =
        fun θ => (fun x => if x ≤ b / α 1 then (θi - b) + 0 * x else 0) (θ 1) := by
      funext θ
      simp only [fpMech2, play, linStrat, linU, allocV, twoY, fullPriceT, update_self,
        update_of_ne (show (1 : Fin 2) ≠ 0 by decide), Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one]
      have hiff : α 1 * θ 1 ≤ b ↔ θ 1 ≤ b / α 1 := by rw [le_div_iff₀ (hα 1), mul_comm]
      by_cases h : α 1 * θ 1 ≤ b
      · simp only [h, hiff.1 h, ↓reduceIte]; ring
      · simp only [h, mt hiff.2 h, ↓reduceIte]; ring
    simp only [Fin.zero_eta, sub_zero]
    rw [e, au_eval (au_meas_le _ _ _) 1, au_int_le, au_int_affine]; ring
  · have e : (fun θ : Fin 2 → ℝ => linU allocV 1
        (fpMech2.outcome (update (play (linStrat α) θ) 1 b)) θi) =
        fun θ => (fun x => if x < b / α 0 then (θi - b) + 0 * x else 0) (θ 0) := by
      funext θ
      simp only [fpMech2, play, linStrat, linU, allocV, twoY, fullPriceT, update_self,
        update_of_ne (show (0 : Fin 2) ≠ 1 by decide), Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one]
      have hiff : α 0 * θ 0 < b ↔ θ 0 < b / α 0 := by rw [lt_div_iff₀ (hα 0), mul_comm]
      by_cases h : α 0 * θ 0 < b
      · simp only [h, hiff.1 h, ↓reduceIte]; ring
      · simp only [h, mt hiff.2 h, ↓reduceIte]; ring
    simp only [Fin.mk_one, sub_self]
    rw [e, au_eval (au_meas_lt _ _ _) 0, au_int_lt, au_int_affine]; ring

/-- The bidder's problem of Example 23.B.5: for `α > 0` and `θ ≥ 0`, the bid
`b* = min(θ/2, α)` maximizes `(θ - b) clamp(b/α)` over `b ≥ 0`. -/
theorem fp_br_ineq {θ α b : ℝ} (hα : 0 < α) (hθ : 0 ≤ θ) (hb : 0 ≤ b) :
    (θ - b) * clamp01 (b / α) ≤ (θ - min (θ / 2) α) * clamp01 (min (θ / 2) α / α) := by
  rcases le_or_gt (θ / 2) α with h | h
  · rw [min_eq_left h, clamp01_of_mem ⟨div_nonneg (by linarith) hα.le,
      (div_le_one hα).2 h⟩]
    rcases le_or_gt b α with hb' | hb'
    · rw [clamp01_of_mem ⟨div_nonneg hb hα.le, (div_le_one hα).2 hb'⟩, mul_div_assoc',
        mul_div_assoc']
      exact div_le_div_of_nonneg_right (by nlinarith [sq_nonneg (b - θ / 2)]) hα.le
    · rw [clamp01_of_one_le ((one_le_div hα).2 hb'.le), mul_one, mul_div_assoc',
        le_div_iff₀ hα]
      nlinarith [sq_nonneg (θ - 2 * α)]
  · rw [min_eq_right h.le, div_self hα.ne', clamp01_of_one_le le_rfl, mul_one]
    rcases le_or_gt b α with hb' | hb'
    · rw [clamp01_of_mem ⟨div_nonneg hb hα.le, (div_le_one hα).2 hb'⟩, mul_div_assoc',
        div_le_iff₀ hα]
      nlinarith
    · rw [clamp01_of_one_le ((one_le_div hα).2 hb'.le), mul_one]; linarith

/-- **Example 23.B.5** (MWG, p. 865). If bidder `j` uses `bⱼ = αⱼθⱼ` with `αⱼ > 0`, bidder `i`'s
best response is `bᵢ(θᵢ) = θᵢ/2` if `θᵢ/2 ≤ αⱼ` and `αⱼ` if `θᵢ/2 > αⱼ` (for `θᵢ ≥ 0`); on
`[0, αⱼ]` his objective is MWG's `(θᵢ - bᵢ)(bᵢ/αⱼ)`. -/
theorem example_23_B_5_bestResponse (α : Fin 2 → ℝ) (hα : ∀ j, 0 < α j) (i : Fin 2)
    {θi : ℝ} (hθ : 0 ≤ θi) :
    (∀ b ∈ Icc 0 (α (1 - i)), interimUtility (indepBeliefs unif2) (linU allocV) fpMech2
      (linStrat α) i θi b = (θi - b) * (b / α (1 - i))) ∧
    0 ≤ min (θi / 2) (α (1 - i)) ∧
    ∀ b, 0 ≤ b → interimUtility (indepBeliefs unif2) (linU allocV) fpMech2 (linStrat α) i θi b ≤
      interimUtility (indepBeliefs unif2) (linU allocV) fpMech2 (linStrat α) i θi
        (min (θi / 2) (α (1 - i))) := by
  refine ⟨fun b hb => ?_, le_min (by linarith) (hα _).le, fun b hb => ?_⟩
  · rw [fp_interim α hα, clamp01_of_mem ⟨div_nonneg hb.1 (hα _).le,
      (div_le_one (hα _)).2 hb.2⟩]
  · rw [fp_interim α hα, fp_interim α hα]
    exact fp_br_ineq (hα _) hθ hb

/-- **Example 23.B.5** (MWG, pp. 865-866). With two bidders whose valuations are independent and
uniform on `[0, 1]`, `bᵢ(θᵢ) = θᵢ/2` is a Bayesian Nash equilibrium of the first-price
sealed-bid auction (for types in `[0, 1]` and bids `b ≥ 0`), and it yields the outcomes of the
social choice function (23.B.9)-(23.B.14) (`twoY`, `firstPriceT`): the auction implements it
(Definition 23.B.4). -/
theorem example_23_B_5 :
    IsBNEOn (indepBeliefs unif2) (linU allocV) fpMech2 (linStrat fun _ => 1 / 2)
      (fun _ => Icc 0 1) (fun _ => Ici 0) ∧
    (∀ θ, fpMech2.outcome (play (linStrat fun _ => 1 / 2) θ) = (twoY θ, firstPriceT θ)) ∧
    Implements {s | IsBNEOn (indepBeliefs unif2) (linU allocV) fpMech2 s (fun _ => Icc 0 1)
      (fun _ => Ici 0)} fpMech2 fun θ => (twoY θ, firstPriceT θ) := by
  have hα : ∀ j : Fin 2, (0 : ℝ) < (fun _ => 1 / 2) j := fun _ => by norm_num
  have hbne : IsBNEOn (indepBeliefs unif2) (linU allocV) fpMech2 (linStrat fun _ => 1 / 2)
      (fun _ => Icc 0 1) (fun _ => Ici 0) := by
    refine ⟨fun i θi hθ => ?_, fun i θi hθ b hb => ?_⟩
    · simp only [linStrat, mem_Ici]; linarith [hθ.1]
    · have hmin : min (θi / 2) ((fun _ : Fin 2 => (1 : ℝ) / 2) (1 - i)) = linStrat
          (fun _ => 1 / 2) i θi := by
        simp only [linStrat]; rw [min_eq_left (by linarith [hθ.2])]; ring
      have := (example_23_B_5_bestResponse _ hα i hθ.1).2.2 b hb
      rwa [hmin] at this
  have hout : ∀ θ, fpMech2.outcome (play (linStrat fun _ => 1 / 2) θ) =
      (twoY θ, firstPriceT θ) := by
    intro θ
    have hy : twoY (play (linStrat fun _ => 1 / 2) θ) = twoY θ := by
      funext j
      fin_cases j <;> simp [twoY, play, linStrat]
    simp only [fpMech2, hy, Prod.mk.injEq, true_and]
    funext j
    simp only [fullPriceT, firstPriceT, hy]
    fin_cases j <;> simp [play, linStrat] <;> ring
  exact ⟨hbne, hout, ⟨_, hbne, hout⟩⟩

/-! ### Sealed-bid auctions with any number of bidders (p. 867) -/

/-- Some bidder makes the highest bid. -/
theorem au_maxSet_nonempty {ι : Type*} [Fintype ι] [Nonempty ι] (b : ι → ℝ) :
    (Finset.univ.filter fun i => ∀ j, b j ≤ b i).Nonempty := by
  classical
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ b Finset.univ_nonempty
  exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ i, fun j => hi j (Finset.mem_univ j)⟩⟩

/-- **Section 23.B** (MWG, p. 867, footnotes 8 and 10). The winner of a sealed-bid auction: the
lowest-numbered of the highest bidders, `min{j : bⱼ = max{b₁, …, b_I}}`. -/
noncomputable def auctionWinner {ι : Type*} [Fintype ι] [LinearOrder ι] [Nonempty ι]
    (b : ι → ℝ) : ι :=
  (Finset.univ.filter fun i => ∀ j, b j ≤ b i).min' (au_maxSet_nonempty b)

/-- The winner makes a highest bid. -/
theorem auctionWinner_max {ι : Type*} [Fintype ι] [LinearOrder ι] [Nonempty ι] (b : ι → ℝ)
    (j : ι) : b j ≤ b (auctionWinner b) :=
  (Finset.mem_filter.1 (Finset.min'_mem _ (au_maxSet_nonempty b))).2 j

/-- The winner has the lowest index among the highest bidders. -/
theorem auctionWinner_le {ι : Type*} [Fintype ι] [LinearOrder ι] [Nonempty ι] (b : ι → ℝ)
    {i : ι} (hi : ∀ j, b j ≤ b i) : auctionWinner b ≤ i :=
  Finset.min'_le _ _ (Finset.mem_filter.2 ⟨Finset.mem_univ i, hi⟩)

/-- A strictly highest bidder wins. -/
theorem auctionWinner_eq_of_gt {ι : Type*} [Fintype ι] [LinearOrder ι] [Nonempty ι]
    (b : ι → ℝ) {i : ι} (hi : ∀ j, j ≠ i → b j < b i) : auctionWinner b = i := by
  by_contra hne
  exact absurd (auctionWinner_max b i) (not_le.2 (hi _ hne))

/-- With two bidders, bidder `0` wins iff `b₁ ≤ b₀`. -/
theorem auctionWinner_fin_two (b : Fin 2 → ℝ) :
    auctionWinner b = if b 1 ≤ b 0 then 0 else 1 := by
  split_ifs with h
  · refine le_antisymm (auctionWinner_le b fun j => ?_) (Fin.zero_le _)
    fin_cases j
    · exact le_rfl
    · exact h
  · refine auctionWinner_eq_of_gt b fun j hj => ?_
    fin_cases j
    · exact not_le.1 h
    · exact absurd rfl hj

/-- The other bidders are a nonempty set when there are at least two bidders. -/
theorem au_erase_nonempty {ι : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι] (i : ι) :
    (Finset.univ.erase i).Nonempty :=
  let ⟨j, hj⟩ := exists_ne i
  ⟨j, Finset.mem_erase.2 ⟨hj, Finset.mem_univ j⟩⟩

/-- The highest bid of the bidders other than `i`, `max{bⱼ : j ≠ i}`. -/
noncomputable def othersMax {ι : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι]
    (b : ι → ℝ) (i : ι) : ℝ :=
  (Finset.univ.erase i).sup' (au_erase_nonempty i) b

/-- With two bidders, the other bid is the highest other bid. -/
theorem othersMax_fin_two (b : Fin 2 → ℝ) : othersMax b 0 = b 1 ∧ othersMax b 1 = b 0 := by
  refine ⟨le_antisymm (Finset.sup'_le _ _ fun j hj => ?_)
    (Finset.le_sup' b (Finset.mem_erase.2 ⟨by decide, Finset.mem_univ _⟩)),
    le_antisymm (Finset.sup'_le _ _ fun j hj => ?_)
    (Finset.le_sup' b (Finset.mem_erase.2 ⟨by decide, Finset.mem_univ _⟩))⟩
  · fin_cases j
    · exact absurd rfl (Finset.ne_of_mem_erase hj)
    · exact le_rfl
  · fin_cases j
    · exact le_rfl
    · exact absurd rfl (Finset.ne_of_mem_erase hj)

/-- **Section 23.B** (MWG, p. 867). The outcome function of the first-price sealed-bid auction:
the winner `min{j : bⱼ = max b}` gets the good and pays his bid, `tᵢ = -bᵢyᵢ`. An outcome is the
winner and the transfers. -/
noncomputable def firstPriceOutcome {ι : Type*} [Fintype ι] [LinearOrder ι] [Nonempty ι]
    (b : ι → ℝ) : ι × (ι → ℝ) :=
  (auctionWinner b, fun j => if auctionWinner b = j then -b j else 0)

/-- **Section 23.B** (MWG, p. 867). The outcome function of the second-price sealed-bid auction:
the same winner pays the highest other bid, `tᵢ = -max{bⱼ : j ≠ i} yᵢ`. -/
noncomputable def secondPriceOutcome {ι : Type*} [Fintype ι] [LinearOrder ι] [Nonempty ι]
    [Nontrivial ι] (b : ι → ℝ) : ι × (ι → ℝ) :=
  (auctionWinner b, fun j => if auctionWinner b = j then -othersMax b j else 0)

/-- Buyer `i`'s utility `θᵢyᵢ + tᵢ` when the outcome is (winner, transfers). -/
def winU {ι : Type*} [DecidableEq ι] : (i : ι) → ι × (ι → ℝ) → ℝ → ℝ :=
  fun i x θi => (if x.1 = i then θi else 0) + x.2 i

/-- With two bidders, the first-price outcome function is `fpMech2`'s: bidder `i` wins iff
`twoY b i = 1`, and pays `-fullPriceT b i`. -/
theorem firstPriceOutcome_fin_two (b : Fin 2 → ℝ) (i : Fin 2) :
    twoY b i = (if (firstPriceOutcome b).1 = i then 1 else 0) ∧
      fullPriceT b i = (firstPriceOutcome b).2 i := by
  simp only [firstPriceOutcome, auctionWinner_fin_two]
  fin_cases i <;> by_cases h : b 1 ≤ b 0 <;>
    simp [h, twoY, fullPriceT, not_le.1]

/-- **Exercise 23.B.3** (MWG, p. 918), the core: in the second-price sealed-bid auction with any
number `I ≥ 2` of bidders, bidding one's valuation is weakly dominant: whatever (real) bids the
others make, no bid gives bidder `i` a higher utility than `bᵢ = θᵢ`. -/
theorem sp_truth_dominant {ι : Type*} [Fintype ι] [LinearOrder ι] [Nonempty ι] [Nontrivial ι]
    (i : ι) (θi a : ℝ) (σ : ι → ℝ) :
    winU i (secondPriceOutcome (update σ i a)) θi ≤
      winU i (secondPriceOutcome (update σ i θi)) θi := by
  have hm : ∀ β, othersMax (update σ i β) i = othersMax σ i := fun β =>
    Finset.sup'_congr _ rfl fun j hj => update_of_ne (Finset.ne_of_mem_erase hj) _ _
  have hpay : ∀ β, winU i (secondPriceOutcome (update σ i β)) θi =
      if auctionWinner (update σ i β) = i then θi - othersMax σ i else 0 := by
    intro β
    simp only [winU, secondPriceOutcome, hm]
    by_cases h : auctionWinner (update σ i β) = i
    · simp only [h, ↓reduceIte]; ring
    · simp [h]
  have hA : ∀ β, auctionWinner (update σ i β) = i → othersMax σ i ≤ β := by
    intro β h
    rw [← hm β]
    refine Finset.sup'_le _ _ fun j _ => ?_
    have := auctionWinner_max (update σ i β) j
    rwa [h, update_self] at this
  have hB : ∀ β, othersMax σ i < β → auctionWinner (update σ i β) = i := by
    intro β h
    refine auctionWinner_eq_of_gt _ fun j hj => ?_
    rw [update_of_ne hj, update_self]
    exact lt_of_le_of_lt (Finset.le_sup' σ (Finset.mem_erase.2 ⟨hj, Finset.mem_univ j⟩)) h
  rw [hpay, hpay]
  split_ifs with h1 h2 h2
  · exact le_rfl
  · by_contra hlt
    exact h2 (hB θi (by linarith))
  · linarith [hA θi h2]
  · exact le_rfl

/-- **Example 23.B.6** (MWG, p. 866). The second-price sealed-bid auction with MWG's spaces:
types `θᵢ ∈ [0, 1]`, bids `bᵢ ≥ 0`. -/
noncomputable def spMech (ι : Type*) [Fintype ι] [LinearOrder ι] [Nonempty ι] [Nontrivial ι] :
    Mechanism (fun _ : ι => ↥(Ici (0 : ℝ))) (ι × (ι → ℝ)) :=
  ⟨fun b => secondPriceOutcome fun j => (b j : ℝ)⟩

/-- Bid your valuation: `bᵢ(θᵢ) = θᵢ`. -/
def bidValue (ι : Type*) : (i : ι) → ↥(Icc (0 : ℝ) 1) → ↥(Ici (0 : ℝ)) :=
  fun _ θ => ⟨θ, θ.2.1⟩

/-- **Exercise 23.B.3** (MWG, p. 918) and **Example 23.B.6** (p. 866). In the second-price
sealed-bid auction with `I ≥ 2` bidders, valuations `θᵢ ∈ [0, 1]` and bids `bᵢ ≥ 0`, bidding
`bᵢ(θᵢ) = θᵢ` is a weakly dominant strategy for every bidder: truth telling is a dominant
strategy equilibrium. -/
theorem exercise_23_B_3 (ι : Type*) [Fintype ι] [LinearOrder ι] [Nonempty ι] [Nontrivial ι] :
    IsDominantStrategyEquilibrium (fun i x (θi : ↥(Icc (0 : ℝ) 1)) => winU i x (θi : ℝ))
      (spMech ι) (bidValue ι) := by
  intro i θi s' σ
  have e : ∀ c : ↥(Ici (0 : ℝ)), (fun j => ((update σ i c j : ↥(Ici (0 : ℝ))) : ℝ)) =
      update (fun j => (σ j : ℝ)) i (c : ℝ) := by
    intro c
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [update_of_ne hj]
  simp only [spMech, bidValue, e]
  exact sp_truth_dominant i _ _ _

/-- **Example 23.B.6** (MWG, p. 866). With two bidders, the second-price sealed-bid auction
implements in dominant strategies the second-price social choice function: bidder `0` gets the
good iff `θ₁ ≤ θ₀`, and the winner pays the other's valuation (`secondPriceT`). -/
theorem example_23_B_6 :
    ImplementsInDominantStrategies (fun i x (θi : ↥(Icc (0 : ℝ) 1)) => winU i x (θi : ℝ))
      (spMech (Fin 2)) fun θ => (if (θ 1 : ℝ) ≤ θ 0 then 0 else 1,
        secondPriceT fun j => (θ j : ℝ)) := by
  refine ⟨bidValue (Fin 2), exercise_23_B_3 (Fin 2), fun θ => ?_⟩
  obtain ⟨h0, h1⟩ := othersMax_fin_two fun j => (θ j : ℝ)
  simp only [spMech, play, bidValue, secondPriceOutcome, auctionWinner_fin_two, Prod.mk.injEq]
  refine ⟨rfl, funext fun j => ?_⟩
  fin_cases j <;> rcases le_or_gt (θ 1 : ℝ) (θ 0) with h | h
  · simp [h, h0, secondPriceT, twoY]
  · simp [h, not_le.2 h, secondPriceT, twoY]
  · simp [h, not_lt.2 h, secondPriceT, twoY]
  · simp [h, not_le.2 h, h1, secondPriceT, twoY]

/-! ### Exercise 23.B.4: the double auction -/

/-- `x ↦ 1{τ < x}(A + Bx)` is interval integrable on `[0, 1]`. -/
theorem au_ii_gt (τ A B : ℝ) :
    IntervalIntegrable (fun x : ℝ => if τ < x then A + B * x else 0) volume 0 1 := by
  have h : (fun x : ℝ => if τ < x then A + B * x else 0) =
      (Ioi τ).indicator fun x => A + B * x := by
    funext x; simp [indicator_apply]
  rw [h, intervalIntegrable_iff]
  exact ((by fun_prop : Continuous fun x : ℝ => A + B * x).intervalIntegrable 0 1).def'.indicator
    measurableSet_Ioi

/-- **Exercise 23.B.4** (MWG, p. 918). The double auction: the seller (agent `0`) and the buyer
(agent `1`) submit bids; if `b₀ ≥ b₁` the seller keeps the good and no transfer is made, if
`b₁ > b₀` the buyer gets the good and pays the seller `(b₀ + b₁)/2` (`twoY`, `splitT`). -/
noncomputable def daMech : Mechanism (fun _ : Fin 2 => ℝ) ((Fin 2 → ℝ) × (Fin 2 → ℝ)) :=
  ⟨fun b => (twoY b, splitT b)⟩

/-- **Exercise 23.B.4(a)**. The seller's expected utility from bidding `b` when the buyer bids
`p + qθ₁` (`q > 0`): `θ₀ + ((b + p)/2 - θ₀)(1 - c) + (q/4)(1 - c²)`, `c = clamp((b - p)/q)`. -/
theorem da_seller_interim (s : (i : Fin 2) → ℝ → ℝ) {p q : ℝ} (hq : 0 < q)
    (hs : ∀ x, s 1 x = p + q * x) (θ0 b : ℝ) :
    interimUtility (indepBeliefs unif2) (linU allocV) daMech s 0 θ0 b =
      θ0 + ((b + p) / 2 - θ0) * (1 - clamp01 ((b - p) / q)) +
        q / 4 * (1 - clamp01 ((b - p) / q) ^ 2) := by
  unfold interimUtility indepBeliefs
  have e : (fun θ : Fin 2 → ℝ => linU allocV 0 (daMech.outcome (update (play s θ) 0 b)) θ0) =
      fun θ => (fun x => θ0 + if (b - p) / q < x then ((b + p) / 2 - θ0) + q / 2 * x else 0)
        (θ 1) := by
    funext θ
    simp only [daMech, play, linU, allocV, twoY, splitT, update_self,
      update_of_ne (show (1 : Fin 2) ≠ 0 by decide), Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, hs]
    have hiff : b < p + q * θ 1 ↔ (b - p) / q < θ 1 := by
      rw [div_lt_iff₀ hq]; constructor <;> intro h <;> linarith
    by_cases h : b < p + q * θ 1
    · simp only [h, hiff.1 h, not_le.2 h, ↓reduceIte]; ring
    · simp only [h, mt hiff.2 h, not_lt.1 h, ↓reduceIte]; ring
  rw [e, au_eval (H := fun x => θ0 + if (b - p) / q < x then ((b + p) / 2 - θ0) + q / 2 * x
      else 0) (measurable_const.add (au_meas_gt _ _ _)) 1,
    intervalIntegral.integral_add intervalIntegrable_const (au_ii_gt _ _ _),
    intervalIntegral.integral_const, au_int_gt, au_int_affine, smul_eq_mul]
  ring

/-- **Exercise 23.B.4(a)**. The buyer's expected utility from bidding `b` when the seller bids
`p + qθ₀` (`q > 0`): `(θ₁ - (p + b)/2)c - (q/4)c²`, `c = clamp((b - p)/q)`. -/
theorem da_buyer_interim (s : (i : Fin 2) → ℝ → ℝ) {p q : ℝ} (hq : 0 < q)
    (hs : ∀ x, s 0 x = p + q * x) (θ1 b : ℝ) :
    interimUtility (indepBeliefs unif2) (linU allocV) daMech s 1 θ1 b =
      (θ1 - (p + b) / 2) * clamp01 ((b - p) / q) - q / 4 * clamp01 ((b - p) / q) ^ 2 := by
  unfold interimUtility indepBeliefs
  have e : (fun θ : Fin 2 → ℝ => linU allocV 1 (daMech.outcome (update (play s θ) 1 b)) θ1) =
      fun θ => (fun x => if x < (b - p) / q then (θ1 - (p + b) / 2) + (-(q / 2)) * x else 0)
        (θ 0) := by
    funext θ
    simp only [daMech, play, linU, allocV, twoY, splitT, update_self,
      update_of_ne (show (0 : Fin 2) ≠ 1 by decide), Matrix.cons_val_one,
      Matrix.cons_val_fin_one, hs]
    have hiff : p + q * θ 0 < b ↔ θ 0 < (b - p) / q := by
      rw [lt_div_iff₀ hq]; constructor <;> intro h <;> linarith
    by_cases h : p + q * θ 0 < b
    · simp only [h, hiff.1 h, ↓reduceIte]; ring
    · simp only [h, mt hiff.2 h, ↓reduceIte]; ring
  rw [e, au_eval (au_meas_lt _ _ _) 0, au_int_lt, au_int_affine]
  ring

/-- **Exercise 23.B.4(a)**. The seller's optimal bid against `b₁ = 2θ₁/3 + 1/12` is
`2θ₀/3 + 1/4` (for `θ₀ ∈ [0, 1]`; when `θ₀ > 3/4` this bid never trades, which is optimal). -/
theorem da_seller_ineq {θ0 : ℝ} (hθ : θ0 ∈ Icc (0 : ℝ) 1) (b : ℝ) :
    θ0 + ((b + 1 / 12) / 2 - θ0) * (1 - clamp01 ((b - 1 / 12) / (2 / 3))) +
        2 / 3 / 4 * (1 - clamp01 ((b - 1 / 12) / (2 / 3)) ^ 2) ≤
      θ0 + ((2 / 3 * θ0 + 1 / 4 + 1 / 12) / 2 - θ0) *
          (1 - clamp01 ((2 / 3 * θ0 + 1 / 4 - 1 / 12) / (2 / 3))) +
        2 / 3 / 4 * (1 - clamp01 ((2 / 3 * θ0 + 1 / 4 - 1 / 12) / (2 / 3)) ^ 2) := by
  obtain ⟨h0, h1⟩ := hθ
  have e1 : (2 / 3 * θ0 + 1 / 4 - 1 / 12) / (2 / 3) = θ0 + 1 / 4 := by ring
  have e2 : (2 / 3 * θ0 + 1 / 4 + 1 / 12) / 2 = (θ0 + 1 / 4) / 3 + 1 / 12 := by ring
  have e3 : (b + 1 / 12) / 2 = (b - 1 / 12) / (2 / 3) / 3 + 1 / 12 := by ring
  rw [e1, e2, e3]
  generalize (b - 1 / 12) / (2 / 3) = t
  rcases le_or_gt θ0 (3 / 4) with hθ' | hθ'
  · rw [clamp01_of_mem (τ := θ0 + 1 / 4) ⟨by linarith, by linarith⟩]
    rcases le_or_gt t 0 with h | h
    · rw [clamp01_of_nonpos h]; nlinarith
    · rcases le_or_gt t 1 with h' | h'
      · rw [clamp01_of_mem ⟨h.le, h'⟩]; nlinarith [sq_nonneg (t - (θ0 + 1 / 4))]
      · rw [clamp01_of_one_le h'.le]; nlinarith [sq_nonneg (θ0 - 3 / 4)]
  · rw [clamp01_of_one_le (τ := θ0 + 1 / 4) (by linarith)]
    rcases le_or_gt t 0 with h | h
    · rw [clamp01_of_nonpos h]; nlinarith
    · rcases le_or_gt t 1 with h' | h'
      · rw [clamp01_of_mem ⟨h.le, h'⟩]; nlinarith [sq_nonneg (t - 1)]
      · rw [clamp01_of_one_le h'.le]; nlinarith

/-- **Exercise 23.B.4(a)**. The buyer's optimal bid against `b₀ = 2θ₀/3 + 1/4` is
`2θ₁/3 + 1/12` (for `θ₁ ∈ [0, 1]`; when `θ₁ < 1/4` this bid never trades, which is optimal). -/
theorem da_buyer_ineq {θ1 : ℝ} (hθ : θ1 ∈ Icc (0 : ℝ) 1) (b : ℝ) :
    (θ1 - (1 / 4 + b) / 2) * clamp01 ((b - 1 / 4) / (2 / 3)) -
        2 / 3 / 4 * clamp01 ((b - 1 / 4) / (2 / 3)) ^ 2 ≤
      (θ1 - (1 / 4 + (2 / 3 * θ1 + 1 / 12)) / 2) *
          clamp01 ((2 / 3 * θ1 + 1 / 12 - 1 / 4) / (2 / 3)) -
        2 / 3 / 4 * clamp01 ((2 / 3 * θ1 + 1 / 12 - 1 / 4) / (2 / 3)) ^ 2 := by
  obtain ⟨h0, h1⟩ := hθ
  have e1 : (2 / 3 * θ1 + 1 / 12 - 1 / 4) / (2 / 3) = θ1 - 1 / 4 := by ring
  have e2 : (1 / 4 + (2 / 3 * θ1 + 1 / 12)) / 2 = 1 / 4 + (θ1 - 1 / 4) / 3 := by ring
  have e3 : (1 / 4 + b) / 2 = 1 / 4 + (b - 1 / 4) / (2 / 3) / 3 := by ring
  rw [e1, e2, e3]
  generalize (b - 1 / 4) / (2 / 3) = t
  rcases le_or_gt (1 / 4) θ1 with hθ' | hθ'
  · rw [clamp01_of_mem (τ := θ1 - 1 / 4) ⟨by linarith, by linarith⟩]
    rcases le_or_gt t 0 with h | h
    · rw [clamp01_of_nonpos h]; nlinarith
    · rcases le_or_gt t 1 with h' | h'
      · rw [clamp01_of_mem ⟨h.le, h'⟩]; nlinarith [sq_nonneg (t - (θ1 - 1 / 4))]
      · rw [clamp01_of_one_le h'.le]; nlinarith [sq_nonneg (θ1 - 5 / 4)]
  · rw [clamp01_of_nonpos (τ := θ1 - 1 / 4) (by linarith)]
    rcases le_or_gt t 0 with h | h
    · rw [clamp01_of_nonpos h]; nlinarith
    · rcases le_or_gt t 1 with h' | h'
      · rw [clamp01_of_mem ⟨h.le, h'⟩]; nlinarith
      · rw [clamp01_of_one_le h'.le]; nlinarith

/-- **Exercise 23.B.4(a)** (MWG, p. 918). The linear (Chatterjee-Samuelson) strategies
`b₀(θ₀) = 2θ₀/3 + 1/4`, `b₁(θ₁) = 2θ₁/3 + 1/12`. -/
noncomputable def daStrat : (i : Fin 2) → ℝ → ℝ := fun i θ => 2 / 3 * θ + ![1 / 4, 1 / 12] i

/-- **Exercise 23.B.4(a)** (MWG, p. 918). With both types uniform on `[0, 1]`, the linear
strategies `b₀ = 2θ₀/3 + 1/4`, `b₁ = 2θ₁/3 + 1/12` (`αᵢ + βᵢθᵢ` with `β = 2/3`) form a Bayesian
Nash equilibrium of the double auction (types in `[0, 1]`, bids `b ≥ 0`). -/
theorem exercise_23_B_4a :
    IsBNEOn (indepBeliefs unif2) (linU allocV) daMech daStrat (fun _ => Icc 0 1)
      (fun _ => Ici 0) := by
  refine ⟨fun i θi hθ => ?_, fun i θi hθ b _ => ?_⟩
  · fin_cases i <;> simp [daStrat] <;> linarith [hθ.1]
  · fin_cases i
    · have hs : ∀ x, daStrat 1 x = 1 / 12 + 2 / 3 * x := fun x => by simp [daStrat]; ring
      have h0 : daStrat 0 θi = 2 / 3 * θi + 1 / 4 := by simp [daStrat]
      simp only [Fin.zero_eta]
      rw [da_seller_interim daStrat (by norm_num) hs, da_seller_interim daStrat (by norm_num) hs,
        h0]
      exact da_seller_ineq hθ b
    · have hs : ∀ x, daStrat 0 x = 1 / 4 + 2 / 3 * x := fun x => by simp [daStrat]; ring
      have h1 : daStrat 1 θi = 2 / 3 * θi + 1 / 12 := by simp [daStrat]
      simp only [Fin.mk_one]
      rw [da_buyer_interim daStrat (by norm_num) hs, da_buyer_interim daStrat (by norm_num) hs,
        h1]
      exact da_buyer_ineq hθ b

/-- **Exercise 23.B.4(a)** (MWG, p. 918). The social choice function implemented by this
equilibrium: trade iff `θ₁ > θ₀ + 1/4` (MWG: `θ₂ > θ₁ + 1/4`), at the price
`(b₀ + b₁)/2 = (θ₀ + θ₁)/3 + 1/6`. -/
theorem exercise_23_B_4a_outcome (θ : Fin 2 → ℝ) :
    daMech.outcome (play daStrat θ) =
      (![if θ 1 ≤ θ 0 + 1 / 4 then 1 else 0, if θ 0 + 1 / 4 < θ 1 then 1 else 0],
        ![((θ 0 + θ 1) / 3 + 1 / 6) * (if θ 0 + 1 / 4 < θ 1 then 1 else 0),
          -(((θ 0 + θ 1) / 3 + 1 / 6) * (if θ 0 + 1 / 4 < θ 1 then 1 else 0))]) := by
  have hiff : 2 / 3 * θ 0 + 1 / 4 < 2 / 3 * θ 1 + 1 / 12 ↔ θ 0 + 1 / 4 < θ 1 := by
    constructor <;> intro h <;> linarith
  have hiff' : 2 / 3 * θ 1 + 1 / 12 ≤ 2 / 3 * θ 0 + 1 / 4 ↔ θ 1 ≤ θ 0 + 1 / 4 := by
    constructor <;> intro h <;> linarith
  simp only [daMech, play, daStrat, twoY, splitT, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, hiff, hiff', Prod.mk.injEq]
  refine ⟨trivial, ?_⟩
  funext j
  fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one] <;> ring

/-- **Exercise 23.B.4(a)**. The double auction's equilibrium social choice function as an
allocation of the single good (Example 23.B.4): the good ends with the buyer iff
`θ₁ > θ₀ + 1/4`, and the transfers balance. -/
noncomputable def daQL (θ : Fin 2 → ℝ) : QLAlt (Fin 2) (Fin 2) :=
  ⟨(if θ 0 + 1 / 4 < θ 1 then 1 else 0,
    ![((θ 0 + θ 1) / 3 + 1 / 6) * (if θ 0 + 1 / 4 < θ 1 then 1 else 0),
      -(((θ 0 + θ 1) / 3 + 1 / 6) * (if θ 0 + 1 / 4 < θ 1 then 1 else 0))]), by simp⟩

/-- `daQL` represents the outcomes of the double auction equilibrium: every agent's utility is
the same in both representations. -/
theorem daQL_utility (θ : Fin 2 → ℝ) (i : Fin 2) (θi : ℝ) :
    qlU goodV 0 i (daQL θ).1 θi = linU allocV i (daMech.outcome (play daStrat θ)) θi := by
  rw [exercise_23_B_4a_outcome]
  fin_cases i <;> simp [qlU, goodV, linU, allocV, daQL]

/-- **Exercise 23.B.4(a)** (MWG, p. 918). The social choice function implemented by the double
auction equilibrium is not ex post efficient: at `θ = (0, 1/8)` the buyer values the good more
than the seller, but there is no trade. -/
theorem exercise_23_B_4a_not_efficient :
    ¬ExPostEfficient (Θ := fun _ : Fin 2 => ℝ)
      (fun i (x : QLAlt (Fin 2) (Fin 2)) θi => qlU goodV 0 i x.1 θi) daQL := by
  rw [example_23_B_4_efficient_iff]
  rintro ⟨h, -⟩
  have hs : Finset.univ.sup' Finset.univ_nonempty (![0, 1 / 8] : Fin 2 → ℝ) = 1 / 8 := by
    refine le_antisymm (Finset.sup'_le _ _ fun j _ => ?_) ?_
    · fin_cases j <;> norm_num
    · exact Finset.le_sup' (![0, 1 / 8] : Fin 2 → ℝ) (Finset.mem_univ 1)
  have := h ![0, 1 / 8] 0
  rw [hs] at this
  norm_num [daQL] at this

/-- **Exercise 23.B.4(b)** (MWG, p. 918). The social choice function implemented by the double
auction equilibrium (trade iff `θ₁ > θ₀ + 1/4` at price `(θ₀ + θ₁)/3 + 1/6`) is Bayesian
incentive compatible: reporting `θ̂ᵢ` in its direct mechanism is bidding `bᵢ(θ̂ᵢ)` in the double
auction, and the equilibrium bid `bᵢ(θᵢ)` is optimal (the revelation principle). -/
theorem exercise_23_B_4b :
    BayesianICOn unif2 allocV (fun θ => twoY (play daStrat θ)) (fun θ => splitT (play daStrat θ))
      (fun _ => 0) (fun _ => 1) := by
  intro i θi hθi θh hθh
  have hplay : ∀ (θ' : Fin 2 → ℝ) c,
      play daStrat (update θ' i c) = update (play daStrat θ') i (daStrat i c) := by
    intro θ' c
    funext j
    by_cases hj : j = i
    · subst hj; simp [play]
    · simp [play, update_of_ne hj]
  have hnn : daStrat i θh ∈ Ici (0 : ℝ) := exercise_23_B_4a.1 i θh hθh
  have := exercise_23_B_4a.2 i θi hθi (daStrat i θh) hnn
  simp only [interimUtility, indepBeliefs, daMech] at this
  simp only [hplay]
  exact this

end MWG.MechanismDesign
