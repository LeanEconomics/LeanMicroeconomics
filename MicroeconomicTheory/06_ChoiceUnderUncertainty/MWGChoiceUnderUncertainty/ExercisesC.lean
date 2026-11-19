/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGChoiceUnderUncertainty.AssetComparative
import UtilityForMoney.IncomeChoice
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Exercises 6.C.2, 6.C.5, 6.C.12, 6.C.13, 6.C.14, 6.C.16 and 6.C.18

MWG, pp. 209-212. Quadratic and mean-variance utility (6.C.2), risk aversion over commodity
bundles and the derived Bernoulli utility of wealth (6.C.5, using Kreps's Proposition 6.16(c)),
constant relative risk aversion (6.C.12), the risk-neutral firm facing price uncertainty
(6.C.13), "strongly more risk averse" (6.C.14), buying and selling prices of a lottery
(6.C.16) and the square-root utility calculations (6.C.18).

Corrections: in 6.C.12(a) the printed form `βx^{1-ρ} + γ` with `β > 0` is decreasing for
`ρ > 1`; the strictly increasing CRRA utilities are `βx^{1-ρ}/(1-ρ) + γ`, `β > 0`. In
6.C.12(c) the printed limit `x^{1-ρ}/(1-ρ) → ln x` fails (at `x = 1` the expression is
`1/(1-ρ)`); the correct limit is `(x^{1-ρ} - 1)/(1-ρ) → ln x`.
-/

namespace MWG.ChoiceUnderUncertainty

open MeasureTheory Filter Topology Set

/-- **Exercise 6.C.2(a)** (MWG, p. 209). With `u(x) = βx² + γx`, expected utility is
`β(σ² + m²) + γm`, a function of the mean `m` and variance `σ²` alone. -/
theorem exercise_6_C_2a (β γ : ℝ) {μ : Measure ℝ} (hμ : IsMoneyLottery univ μ) :
    ∫ x, (β * x ^ 2 + γ * x) ∂μ =
      β * ((∫ x, x ^ 2 ∂μ - (∫ x, x ∂μ) ^ 2) + (∫ x, x ∂μ) ^ 2) + γ * ∫ x, x ∂μ := by
  have h2 : Integrable (fun x : ℝ => x ^ 2) μ := hμ.integrable (by fun_prop)
  rw [integral_add (h2.const_mul β) (hμ.integrable_id.const_mul γ), integral_const_mul,
    integral_const_mul]
  ring

/-- **Exercise 6.C.2(a)** (MWG, p. 209). Two lotteries with the same mean and variance have the
same quadratic expected utility. -/
theorem exercise_6_C_2a_moments (β γ : ℝ) {μ ν : Measure ℝ} (hμ : IsMoneyLottery univ μ)
    (hν : IsMoneyLottery univ ν) (hm : ∫ x, x ∂μ = ∫ x, x ∂ν)
    (hs : ∫ x, x ^ 2 ∂μ = ∫ x, x ^ 2 ∂ν) :
    ∫ x, (β * x ^ 2 + γ * x) ∂μ = ∫ x, (β * x ^ 2 + γ * x) ∂ν := by
  rw [exercise_6_C_2a β γ hμ, exercise_6_C_2a β γ hν, hm, hs]

/-- **Exercise 6.C.2(a)**, note (MWG, p. 209). For `β < 0` the quadratic is concave, and it is
decreasing for `x > -γ/(2β)`. -/
theorem exercise_6_C_2a_note {β γ : ℝ} (hβ : β < 0) :
    ConcaveOn ℝ univ (fun x : ℝ => β * x ^ 2 + γ * x) ∧
      StrictAntiOn (fun x : ℝ => β * x ^ 2 + γ * x) (Ici (-γ / (2 * β))) := by
  constructor
  · refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    simp only [smul_eq_mul]
    have hb' : b = 1 - a := by linarith
    subst hb'
    nlinarith [mul_nonneg ha hb, sq_nonneg (x - y),
      mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x - y))]
  · intro x hx y hy hxy
    simp only [mem_Ici] at hx hy
    have h1 : -γ / (2 * β) * (2 * β) = -γ := div_mul_cancel₀ _ (by linarith)
    have h2 : 2 * (-γ / (2 * β)) < x + y := by linarith
    have h3 : β * (x + y) < β * (2 * (-γ / (2 * β))) := mul_lt_mul_of_neg_left h2 hβ
    have h4 : β * (x + y) + γ < 0 := by linarith
    have he : (β * y ^ 2 + γ * y) - (β * x ^ 2 + γ * x) = (y - x) * (β * (x + y) + γ) := by
      ring
    change β * y ^ 2 + γ * y < β * x ^ 2 + γ * x
    nlinarith [mul_neg_of_pos_of_neg (sub_pos.mpr hxy) h4]

/-- The mean-variance utility `U(F) = mean - r · variance` of a money lottery. -/
noncomputable def meanVarianceU (r : ℝ) (μ : Measure ℝ) : ℝ :=
  ∫ x, x ∂μ - r * (∫ x, x ^ 2 ∂μ - (∫ x, x ∂μ) ^ 2)

/-- Mean-variance utility of the two-point lottery `0` / `2/r` with probability `p` on `2/r`
is `(2/r)(2p² - p)`. -/
theorem meanVarianceU_binLot {r : ℝ} (hr : 0 < r) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    meanVarianceU r (binLot p (2 / r) 0) = 2 / r * (2 * p ^ 2 - p) := by
  unfold meanVarianceU
  rw [integral_binLot _ _ _ _ hp0 hp1, integral_binLot _ _ _ (fun x => x ^ 2) hp0 hp1]
  field_simp
  ring

/-- **Exercise 6.C.2(b)** (MWG, p. 209). For every `r > 0` the mean-variance utility is not
compatible with any Bernoulli utility: on the lotteries over `x' = 0 < x'' = 2/r`, the lottery
`L` giving `x''` with probability `1/4` is ranked strictly below the lottery `L'` giving `x''`
with probability `0`, and no `u` represents the ranking by expected utility. -/
theorem exercise_6_C_2b {r : ℝ} (hr : 0 < r) :
    meanVarianceU r (binLot (1 / 4) (2 / r) 0) < meanVarianceU r (binLot 0 (2 / r) 0) ∧
    ¬∃ u : ℝ → ℝ, ∀ p q : ℝ, p ∈ Icc (0 : ℝ) 1 → q ∈ Icc (0 : ℝ) 1 →
      (meanVarianceU r (binLot p (2 / r) 0) ≤ meanVarianceU r (binLot q (2 / r) 0) ↔
        ∫ x, u x ∂(binLot p (2 / r) 0) ≤ ∫ x, u x ∂(binLot q (2 / r) 0)) := by
  have hU (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) := meanVarianceU_binLot hr hp.1 hp.2
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h4 : (1 / 4 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have h2 : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  constructor
  · rw [hU _ h4, hU _ h0]
    have : (0 : ℝ) < 2 / r := by positivity
    nlinarith
  · rintro ⟨u, hu⟩
    have hEU (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) :
        ∫ x, u x ∂(binLot p (2 / r) 0) = p * u (2 / r) + (1 - p) * u 0 :=
      integral_binLot _ _ _ _ hp.1 hp.2
    have e1 := (hu 0 (1 / 2) h0 h2).mp (by rw [hU _ h0, hU _ h2]; norm_num)
    have e2 := (hu (1 / 2) 0 h2 h0).mp (by rw [hU _ h0, hU _ h2]; norm_num)
    rw [hEU _ h0, hEU _ h2] at e1 e2
    have e3 := (hu 0 (1 / 4) h0 h4).mpr (by rw [hEU _ h0, hEU _ h4]; nlinarith)
    rw [hU _ h0, hU _ h4] at e3
    have : (0 : ℝ) < 2 / r := by positivity
    nlinarith

/-- **Exercise 6.C.5(a)** (MWG, p. 210). For a utility function on commodity bundles in a convex
set `K` (e.g. `ℝ^L_+`), concavity is equivalent to risk aversion over every finite lottery
whose outcomes are bundles: `∑ w_i u(x_i) ≤ u(∑ w_i x_i)`. -/
theorem exercise_6_C_5a {L : ℕ} {K : Set (Fin L → ℝ)} (hK : Convex ℝ K)
    (u : (Fin L → ℝ) → ℝ) :
    ConcaveOn ℝ K u ↔ ∀ (n : ℕ) (w : Fin n → ℝ) (x : Fin n → Fin L → ℝ), (∀ i, 0 ≤ w i) →
      ∑ i, w i = 1 → (∀ i, x i ∈ K) → ∑ i, w i * u (x i) ≤ u (∑ i, w i • x i) := by
  constructor
  · intro hc n w x hw h1 hx
    simpa only [smul_eq_mul] using hc.le_map_sum (t := Finset.univ) (fun i _ => hw i) h1
      (fun i _ => hx i)
  · intro h
    refine ⟨hK, fun x hx y hy a b ha hb hab => ?_⟩
    have := h 2 ![a, b] ![x, y] (by intro i; fin_cases i <;> simp [ha, hb]) (by simp [hab])
      (by intro i; fin_cases i <;> simp [hx, hy])
    simpa [Fin.sum_univ_two, smul_eq_mul] using this

/-- **Exercise 6.C.5(b)** (MWG, p. 210). At fixed strictly positive prices, if the utility over
commodity bundles is continuous and concave (risk averse), the derived Bernoulli utility of
wealth `v(w) = max {u(x) : p · x ≤ w}` is concave (risk averse); Kreps's Proposition 6.16(c). -/
theorem exercise_6_C_5b {L : ℕ} {u : (Fin L → ℝ) → ℝ} (hu : Continuous u)
    (hc : ConcaveOn ℝ (Ici 0) u) (p : Kreps.UtilityForMoney.Demand.PositivePrices L) :
    ConcaveOn ℝ (Ici 0) (fun w : ℝ => Kreps.UtilityForMoney.Demand.IndirectUtility
      (fun x : Kreps.UtilityForMoney.Demand.NonnegativeOrthant L => u x.val) p w.toNNReal) := by
  apply Kreps.UtilityForMoney.proposition_6_16c (hu.comp continuous_subtype_val)
  intro x y a ha
  change a * u x.val + (1 - a) * u y.val ≤ u (a • x.val + (1 - a) • y.val)
  have := hc.2 x.property y.property ha.1 (sub_nonneg.mpr ha.2) (by ring)
  simpa only [smul_eq_mul] using this

/-- The nonconcave utility of Exercise 6.C.5(c): `x₁ + x₂` minus a bump at `(1,1)`. -/
noncomputable def bumpUtility (x : Kreps.UtilityForMoney.Demand.NonnegativeOrthant 2) : ℝ :=
  x.val 0 + x.val 1 - max 0 (1 / 2 - |x.val 0 - 1| - |x.val 1 - 1|)

/-- **Exercise 6.C.5(c)** (MWG, p. 210). The converse of (b) fails: `bumpUtility` is not
concave, yet for every price vector its derived utility of wealth is `w / min(p₁, p₂)`,
linear and hence concave (risk averse). -/
theorem exercise_6_C_5c :
    ¬Kreps.UtilityForMoney.Demand.ConcaveUtility (convex_Ici (𝕜 := ℝ) (0 : Fin 2 → ℝ))
      bumpUtility ∧
    ∀ (p : Kreps.UtilityForMoney.Demand.PositivePrices 2) (w : NNReal),
      Kreps.UtilityForMoney.Demand.IndirectUtility bumpUtility p w =
        w / min (p.val 0) (p.val 1) := by
  constructor
  · intro hc
    let x : Kreps.UtilityForMoney.Demand.NonnegativeOrthant 2 := ⟨![1 / 2, 1], by
      intro i; fin_cases i <;> norm_num⟩
    let y : Kreps.UtilityForMoney.Demand.NonnegativeOrthant 2 := ⟨![3 / 2, 1], by
      intro i; fin_cases i <;> norm_num⟩
    have := hc x y (1 / 2) ⟨by norm_num, by norm_num⟩
    simp only [bumpUtility, Kreps.UtilityForMoney.Demand.Mix, x, y] at this
    norm_num at this
  · intro p w
    have hp0 := p.property 0
    have hp1 := p.property 1
    set m := min (p.val 0) (p.val 1)
    have hm : 0 < m := lt_min hp0 hp1
    have hbound (x : Kreps.UtilityForMoney.Demand.NonnegativeOrthant 2)
        (hx : x ∈ Kreps.UtilityForMoney.Demand.BudgetSet p w) : bumpUtility x ≤ w / m := by
      have hx0 : 0 ≤ x.val 0 := x.property 0
      have hx1 : 0 ≤ x.val 1 := x.property 1
      have hb : p.val 0 * x.val 0 + p.val 1 * x.val 1 ≤ w := by
        have := hx
        simpa [Kreps.UtilityForMoney.Demand.BudgetSet, Kreps.UtilityForMoney.Demand.Expenditure,
          Fin.sum_univ_two] using this
      have h1 : m * (x.val 0 + x.val 1) ≤ w := by
        have a1 := mul_le_mul_of_nonneg_right (min_le_left (p.val 0) (p.val 1)) hx0
        have a2 := mul_le_mul_of_nonneg_right (min_le_right (p.val 0) (p.val 1)) hx1
        nlinarith
      rw [le_div_iff₀ hm]
      unfold bumpUtility
      nlinarith [le_max_left 0 (1 / 2 - |x.val 0 - 1| - |x.val 1 - 1|)]
    -- a corner bundle buying only the cheaper good attains the bound
    have hwm : 0 ≤ (w : ℝ) / m := by positivity
    obtain ⟨c, hcB, hcv⟩ : ∃ c : Kreps.UtilityForMoney.Demand.NonnegativeOrthant 2,
        c ∈ Kreps.UtilityForMoney.Demand.BudgetSet p w ∧ bumpUtility c = w / m := by
      by_cases h : p.val 0 ≤ p.val 1
      · have hm' : m = p.val 0 := min_eq_left h
        refine ⟨⟨![w / m, 0], by intro j; fin_cases j <;> simp [hwm]⟩, ?_, ?_⟩
        · simp only [Kreps.UtilityForMoney.Demand.BudgetSet,
            Kreps.UtilityForMoney.Demand.Expenditure, Set.mem_ofPred_eq, Fin.sum_univ_two]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, add_zero]
          rw [← hm']; field_simp; exact le_rfl
        · simp only [bumpUtility, Matrix.cons_val_zero, Matrix.cons_val_one, zero_sub, abs_neg,
            abs_one]
          rw [max_eq_left (by linarith [abs_nonneg ((w : ℝ) / m - 1)])]
          ring
      · have hm' : m = p.val 1 := min_eq_right (le_of_not_ge h)
        refine ⟨⟨![0, w / m], by intro j; fin_cases j <;> simp [hwm]⟩, ?_, ?_⟩
        · simp only [Kreps.UtilityForMoney.Demand.BudgetSet,
            Kreps.UtilityForMoney.Demand.Expenditure, Set.mem_ofPred_eq, Fin.sum_univ_two]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, zero_add]
          rw [← hm']; field_simp; exact le_rfl
        · simp only [bumpUtility, Matrix.cons_val_zero, Matrix.cons_val_one, zero_sub, abs_neg,
            abs_one]
          rw [max_eq_left (by linarith [abs_nonneg ((w : ℝ) / m - 1)])]
          ring
    unfold Kreps.UtilityForMoney.Demand.IndirectUtility
    apply le_antisymm
    · apply csSup_le (Set.Nonempty.image _ ⟨c, hcB⟩)
      rintro _ ⟨x, hx, rfl⟩
      exact hbound x hx
    · rw [← hcv]
      apply le_csSup _ (Set.mem_image_of_mem _ hcB)
      refine ⟨(w : ℝ) / m, ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      exact hbound x hx

end MWG.ChoiceUnderUncertainty
