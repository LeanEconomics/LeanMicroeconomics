/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGCompetitiveMarkets.ExercisesF
import MWGProduction.ExercisesD345
import MWGProduction.CobbDouglas
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Exercises 10.F.5-10.F.7 and an instance of Example 10.F.1 (MWG, p. 348)

* `hasDerivAt_comp_pair`: the chain rule for `t ↦ f(g(t), t)` with partial derivatives, used for
  comparative statics with two arguments.
* **Exercise 10.F.5**: (a) the long-run supply response of a firm exceeds the short-run one (Le
  Chatelier; Chapter 5's Exercise 5.D.3); (b) hence the long-run price response to a demand
  shift is smaller, and the quantity response larger, than in the short run.
* **Exercise 10.F.6**: Cobb-Douglas technology `z₁^α z₂^{1-α}`: the long-run price is the unit
  cost (Chapter 5's Example 5.C.1) and the short-run industry supply with capital fixed is
  `K̄((1-α)p/w₂)^{(1-α)/α}`.
* **Exercise 10.F.7** (correction): when a factor can be increased but not decreased in the short
  run, the short-run cost curve has a kink at the long-run equilibrium for fixed proportions
  (Leontief), where short-run supply is vertical over a range of prices, but not in general: for
  a Cobb-Douglas technology it is differentiable there.
* `example_10_F_1_instance`: the hypotheses of Example 10.F.1 are satisfiable.
-/

namespace MWG.CompetitiveMarkets

open Filter Topology MWG.ConsumerChoice

/-- The chain rule for `t ↦ f(g(t), t)` when `f` has partial derivatives `a` (first argument)
and `b` (second argument). -/
theorem hasDerivAt_comp_pair {f : ℝ × ℝ → ℝ} {a b : ℝ} {g : ℝ → ℝ} {g' t₀ : ℝ}
    (hf : HasFDerivAt f (a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (g t₀, t₀))
    (hg : HasDerivAt g g' t₀) : HasDerivAt (fun t => f (g t, t)) (a * g' + b) t₀ := by
  have h := HasFDerivAt.comp_hasDerivAt (f := fun t => (g t, t)) t₀ hf
    (hg.prodMk (hasDerivAt_id t₀))
  simp only [add_apply, smul_apply, ContinuousLinearMap.coe_fst', smul_eq_mul,
    ContinuousLinearMap.coe_snd', mul_one] at h
  exact h

/-! ## Exercise 10.F.5 -/

/-- **Exercise 10.F.5(a)** (MWG, p. 348). If the short-run cost `cₛ` (with factor `k` fixed at its
long-run level) lies above the long-run cost `c` and touches it at the long-run output, the
long-run supply response to the price of good `ℓ` is at least the short-run one (Chapter 5,
Exercise 5.D.3, Le Chatelier). -/
theorem exercise_10_F_5a {c cs qL qS : ℝ → ℝ} {p dL dS : ℝ}
    (hle : ∀ q, 0 ≤ q → c q ≤ cs q) (heq : cs (qL p) = c (qL p)) (hsame : qS p = qL p)
    (hL : ∀ᶠ p' in 𝓝 p, 0 ≤ qL p' ∧ ∀ q, 0 ≤ q → p' * q - c q ≤ p' * qL p' - c (qL p'))
    (hS : ∀ᶠ p' in 𝓝 p, 0 ≤ qS p' ∧ ∀ q, 0 ≤ q → p' * q - cs q ≤ p' * qS p' - cs (qS p'))
    (hcL : ∀ᶠ p' in 𝓝 p, ContinuousAt qL p') (hcS : ∀ᶠ p' in 𝓝 p, ContinuousAt qS p')
    (hdL : HasDerivAt qL dL p) (hdS : HasDerivAt qS dS p) : dS ≤ dL :=
  MWG.Production.exercise_5_D_3 hle heq hsame hL hS hcL hcS hdL hdS

/-- **Exercise 10.F.5(b)** (MWG, p. 348): differentiating the market-clearing condition
`x(p(α), α) = J q(p(α))` gives `p'(α) = x_α / (J q' - x_p)`. -/
theorem exercise_10_F_5b_deriv {x : ℝ × ℝ → ℝ} {q p : ℝ → ℝ} {J xp xα s p' α₀ : ℝ}
    (hx : HasFDerivAt x (xp • ContinuousLinearMap.fst ℝ ℝ ℝ + xα • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (p α₀, α₀))
    (hq : HasDerivAt q s (p α₀)) (hp : HasDerivAt p p' α₀)
    (hclear : ∀ᶠ α in 𝓝 α₀, x (p α, α) = J * q (p α)) (hden : J * s - xp ≠ 0) :
    p' = xα / (J * s - xp) := by
  have h1 := hasDerivAt_comp_pair hx hp
  have h2 : HasDerivAt (fun α => J * q (p α)) (J * (s * p')) α₀ := (hq.comp α₀ hp).const_mul J
  have := (h1.congr_of_eventuallyEq (by filter_upwards [hclear] with α h; exact h.symm)).unique h2
  rw [eq_div_iff hden]
  linarith

/-- **Exercise 10.F.5(b)** (MWG, p. 348). With `x_p < 0`, `x_α > 0` and long-run supply response
`s_L` at least the short-run response `s_S ≥ 0` (part (a)), the long-run price response
`x_α/(J s_L - x_p)` is smaller than the short-run one, and the response of aggregate consumption
`J s x_α/(J s - x_p)` is larger. -/
theorem exercise_10_F_5b {J xp xα sS sL : ℝ} (hJ : 0 < J) (hxp : xp < 0) (hxα : 0 < xα)
    (hsS : 0 ≤ sS) (hSL : sS ≤ sL) :
    xα / (J * sL - xp) ≤ xα / (J * sS - xp) ∧
      J * sS * (xα / (J * sS - xp)) ≤ J * sL * (xα / (J * sL - xp)) := by
  have hS : 0 < J * sS - xp := by nlinarith
  have hL : 0 < J * sL - xp := by nlinarith
  refine ⟨div_le_div_of_nonneg_left hxα.le hS (by nlinarith), ?_⟩
  rw [mul_div_assoc', mul_div_assoc', div_le_div_iff₀ hS hL]
  nlinarith [mul_pos hJ hxα, mul_nonneg (mul_pos hJ hxα).le (sub_nonneg.2 hSL)]

/-! ## Exercise 10.F.6 -/

/-- **Exercise 10.F.6** (MWG, p. 348), long run. With the constant-returns Cobb-Douglas
technology `z₁^α z₂^{1-α}`, the cost is `c(w, q) = c₁(w) q` with unit cost
`c₁(w) = θ φ(w)` (Chapter 5, Example 5.C.1), and with demand `a - bp` (`b ≥ 0`, `a > b c₁`)
the long-run equilibrium price is `c₁(w)` and aggregate output `a - b c₁(w)`. -/
theorem exercise_10_F_6_longRun {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {w : Fin 2 → ℝ}
    (hw : StrictlyPositive w) {a b : ℝ} (hb : 0 ≤ b)
    (ha : b * (MWG.Production.cdTheta α (1 - α) * MWG.Production.cdPhi α (1 - α) w) < a)
    {p q : ℝ} {J : ℕ} :
    (∀ q', 0 < q' → MWG.Production.costFn (MWG.Production.cdProd α (1 - α)) w q' =
      MWG.Production.cdTheta α (1 - α) * MWG.Production.cdPhi α (1 - α) w * q') ∧
    (IsLREqm (fun p => a - b * p)
        (fun q => MWG.Production.cdTheta α (1 - α) * MWG.Production.cdPhi α (1 - α) w * q) p q J ↔
      p = MWG.Production.cdTheta α (1 - α) * MWG.Production.cdPhi α (1 - α) w ∧ 0 ≤ q ∧
        (J : ℝ) * q = a - b * (MWG.Production.cdTheta α (1 - α) *
          MWG.Production.cdPhi α (1 - α) w)) := by
  refine ⟨fun q' hq' => ?_, lr_crs (by linarith) (fun x _ y _ hxy => by nlinarith)⟩
  have h := (MWG.Production.example_5_C_1_cost hα0 (by linarith : 0 < 1 - α) hw hq').1
  rw [h, show α + (1 - α) = 1 by ring, div_one, Real.rpow_one]
  ring

/-- **Exercise 10.F.6** (MWG, p. 348), short run. A firm with capital fixed at `k > 0` chooses
labour `z ≥ 0` to maximize `p k^α z^{1-α} - w₂ z`; the optimum is
`z* = k((1-α)p/w₂)^{1/α}` with output `k((1-α)p/w₂)^{(1-α)/α}`. Summing over firms, the
short-run industry supply is `K̄((1-α)p/w₂)^{(1-α)/α}` with `K̄` the total capital. -/
theorem exercise_10_F_6_shortRun {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {k p w₂ : ℝ} (hk : 0 < k)
    (hp : 0 < p) (hw : 0 < w₂) :
    let r := (1 - α) * p / w₂
    let zs := k * r ^ (1 / α)
    (∀ z, 0 ≤ z → p * k ^ α * z ^ (1 - α) - w₂ * z ≤ p * k ^ α * zs ^ (1 - α) - w₂ * zs) ∧
      k ^ α * zs ^ (1 - α) = k * r ^ ((1 - α) / α) := by
  intro r zs
  have hr : 0 < r := by positivity
  have hzs : 0 < zs := by positivity
  have hzsα : zs ^ (-α) = k ^ (-α) * r⁻¹ := by
    simp only [zs]
    rw [Real.mul_rpow hk.le (by positivity), ← Real.rpow_mul hr.le,
      show 1 / α * -α = -1 by field_simp, Real.rpow_neg_one]
  have hzs1 : zs ^ (1 - α) = k ^ (1 - α) * r ^ ((1 - α) / α) := by
    simp only [zs]
    rw [Real.mul_rpow hk.le (by positivity), ← Real.rpow_mul hr.le]
    congr 2; ring
  -- first-order condition `p k^α (1 - α) zs^{-α} = w₂`
  have hfoc : p * k ^ α * ((1 - α) * zs ^ (-α)) = w₂ := by
    have hk' : k ^ α * k ^ (-α) = 1 := by
      rw [← Real.rpow_add hk, add_neg_cancel, Real.rpow_zero]
    rw [hzsα, show p * k ^ α * ((1 - α) * (k ^ (-α) * r⁻¹)) =
      (k ^ α * k ^ (-α)) * ((1 - α) * p / r) by ring, hk', one_mul]
    have h1 : (1 - α) ≠ 0 := by linarith
    simp only [r]
    field_simp
  refine ⟨fun z hz => ?_, ?_⟩
  · -- tangent line bound from Bernoulli's inequality
    have hb := rpow_one_add_le_one_add_mul_self (s := z / zs - 1) (by
      have : 0 ≤ z / zs := div_nonneg hz hzs.le; linarith) (p := 1 - α) (by linarith)
      (by linarith)
    rw [show 1 + (z / zs - 1) = z / zs by ring, Real.div_rpow hz hzs.le] at hb
    have hzsp : 0 < zs ^ (1 - α) := Real.rpow_pos_of_pos hzs _
    rw [div_le_iff₀ hzsp] at hb
    have hneg : zs ^ (1 - α) = zs * zs ^ (-α) := by
      rw [← Real.rpow_one_add' hzs.le (by linarith), show 1 + -α = 1 - α by ring]
    have hA : 0 ≤ p * k ^ α := by positivity
    have key : z ^ (1 - α) ≤ zs ^ (1 - α) + (1 - α) * zs ^ (-α) * (z - zs) := by
      have : (1 + (1 - α) * (z / zs - 1)) * zs ^ (1 - α) =
          zs ^ (1 - α) + (1 - α) * zs ^ (-α) * (z - zs) := by
        rw [hneg]; field_simp
      linarith
    have := mul_le_mul_of_nonneg_left key hA
    nlinarith [hfoc]
  · rw [hzs1, ← mul_assoc, ← Real.rpow_add hk, show α + (1 - α) = 1 by ring, Real.rpow_one]

/-! ## Exercise 10.F.7 -/

/-- The short-run cost when factor `0` cannot be reduced below `z̄₀`:
`cₛ(q) = inf {w·z : z ≥ 0, z₀ ≥ z̄₀, f(z) ≥ q}`. -/
noncomputable def srCost (f : ℝ → ℝ → ℝ) (w₀ w₁ zbar q : ℝ) : ℝ :=
  sInf {s | ∃ z₀ z₁ : ℝ, zbar ≤ z₀ ∧ 0 ≤ z₁ ∧ q ≤ f z₀ z₁ ∧ s = w₀ * z₀ + w₁ * z₁}

/-- **Exercise 10.F.7** (MWG, p. 348), fixed proportions. For `f(z) = min(z₀, z₁)`, unit factor
prices and `z̄₀ = 1` (the long-run input at `q* = 1`), the short-run cost is
`cₛ(q) = max(q, 1) + q`, which has a kink at `q* = 1`. -/
theorem exercise_10_F_7_leontief {q : ℝ} (hq : 0 ≤ q) :
    srCost (fun z₀ z₁ => min z₀ z₁) 1 1 1 q = max q 1 + q := by
  refine IsLeast.csInf_eq ⟨⟨max q 1, q, le_max_right _ _, hq, by simp, by ring⟩, ?_⟩
  rintro s ⟨z₀, z₁, h₀, h₁, hf, rfl⟩
  have hz0 : q ≤ z₀ := hf.trans (min_le_left _ _)
  have hz1 : q ≤ z₁ := hf.trans (min_le_right _ _)
  have : max q 1 ≤ z₀ := max_le hz0 h₀
  linarith

theorem exercise_10_F_7_leontief_kink :
    ¬ DifferentiableAt ℝ (fun q : ℝ => max q 1 + q) 1 := by
  intro hd
  have h := hd.hasDerivAt
  have hl : HasDerivWithinAt (fun q : ℝ => max q 1 + q) 1 (Set.Iic 1) 1 := by
    have : HasDerivWithinAt (fun q : ℝ => 1 + q) 1 (Set.Iic 1) 1 := by
      simpa using ((hasDerivAt_id (1 : ℝ)).const_add 1).hasDerivWithinAt
    exact this.congr (fun q hq => by simp [max_eq_right (Set.mem_Iic.1 hq)]) (by simp)
  have hr : HasDerivWithinAt (fun q : ℝ => max q 1 + q) 2 (Set.Ici 1) 1 := by
    have : HasDerivWithinAt (fun q : ℝ => 2 * q) 2 (Set.Ici 1) 1 := by
      simpa using ((hasDerivAt_id (1 : ℝ)).const_mul 2).hasDerivWithinAt
    exact this.congr (fun q hq => by rw [max_eq_left (Set.mem_Ici.1 hq)]; ring) (by norm_num)
  have e1 := UniqueDiffWithinAt.eq_deriv _ (uniqueDiffWithinAt_Iic 1) h.hasDerivWithinAt hl
  have e2 := UniqueDiffWithinAt.eq_deriv _ (uniqueDiffWithinAt_Ici 1) h.hasDerivWithinAt hr
  linarith

/-- **Exercise 10.F.7** (MWG, p. 348): with fixed proportions, short-run supply is vertical at
`q* = 1` for every price in `[1, 2]`: demand shifts in this range move the price but not the
quantity (short-run prices more variable than quantities). -/
theorem exercise_10_F_7_vertical_supply {p : ℝ} (hp1 : 1 ≤ p) (hp2 : p ≤ 2) (q : ℝ) :
    p * q - (max q 1 + q) ≤ p * 1 - (max 1 1 + 1) := by
  rcases le_total q 1 with h | h
  · rw [max_eq_right h]; simp; nlinarith
  · rw [max_eq_left h]; simp; nlinarith

/-- The long-run cost for `f(z) = √(z₀z₁)` at unit factor prices is `2q`. -/
theorem exercise_10_F_7_cd_longRun {q : ℝ} (hq : 0 ≤ q) :
    srCost (fun z₀ z₁ => Real.sqrt (z₀ * z₁)) 1 1 0 q = 2 * q := by
  refine IsLeast.csInf_eq ⟨⟨q, q, hq, hq, by
    change q ≤ Real.sqrt (q * q); rw [Real.sqrt_mul_self hq], by ring⟩, ?_⟩
  rintro s ⟨z₀, z₁, h₀, h₁, hf, rfl⟩
  have hf' : q ≤ Real.sqrt (z₀ * z₁) := hf
  have hzz : q ^ 2 ≤ z₀ * z₁ := by
    have := (Real.le_sqrt hq (mul_nonneg h₀ h₁)).1 hf'; nlinarith
  nlinarith [sq_nonneg (z₀ - z₁)]

/-- **Exercise 10.F.7** (MWG, p. 348), correction. For `f(z) = √(z₀z₁)` at unit factor prices with
`z₀ ≥ z̄₀ = 1` (the long-run input at `q* = 1`), the short-run cost is `1 + q²` for `q ≤ 1` and
`2q` for `q ≥ 1`. -/
theorem exercise_10_F_7_cd_shortRun {q : ℝ} (hq : 0 ≤ q) :
    srCost (fun z₀ z₁ => Real.sqrt (z₀ * z₁)) 1 1 1 q = if q ≤ 1 then 1 + q ^ 2 else 2 * q := by
  split_ifs with h
  · refine IsLeast.csInf_eq ⟨⟨1, q ^ 2, le_rfl, sq_nonneg q, by
      change q ≤ Real.sqrt (1 * q ^ 2); rw [one_mul, Real.sqrt_sq hq], by ring⟩, ?_⟩
    rintro s ⟨z₀, z₁, h₀, h₁, hf, rfl⟩
    have hf' : q ≤ Real.sqrt (z₀ * z₁) := hf
    have hzz : q ^ 2 ≤ z₀ * z₁ := by
      have := (Real.le_sqrt hq (mul_nonneg (by linarith) h₁)).1 hf'; nlinarith
    have hq2 : q ^ 2 ≤ 1 := by nlinarith
    have key : z₀ * (1 + q ^ 2) ≤ z₀ * (1 * z₀ + 1 * z₁) := by
      nlinarith [mul_nonneg (sub_nonneg.2 h₀) (sub_nonneg.2 (hq2.trans h₀))]
    exact le_of_mul_le_mul_left key (by linarith)
  · push Not at h
    refine IsLeast.csInf_eq ⟨⟨q, q, h.le, hq, by
      change q ≤ Real.sqrt (q * q); rw [Real.sqrt_mul_self hq], by ring⟩, ?_⟩
    rintro s ⟨z₀, z₁, h₀, h₁, hf, rfl⟩
    have hf' : q ≤ Real.sqrt (z₀ * z₁) := hf
    have hzz : q ^ 2 ≤ z₀ * z₁ := by
      have := (Real.le_sqrt hq (mul_nonneg (by linarith) h₁)).1 hf'; nlinarith
    nlinarith [sq_nonneg (z₀ - z₁)]

/-- **Exercise 10.F.7** (MWG, p. 348), correction: for the Cobb-Douglas technology the
short-run cost is differentiable at the long-run equilibrium output `q* = 1`, with derivative
equal to the long-run marginal cost `2`: the printed claim of a kink fails for smooth
substitution (only the slope of marginal cost jumps, from `2` to `0`). -/
theorem exercise_10_F_7_cd_smooth :
    HasDerivAt (srCost (fun z₀ z₁ => Real.sqrt (z₀ * z₁)) 1 1 1) 2 1 := by
  have hpw : HasDerivAt (fun q : ℝ => if q ≤ 1 then 1 + q ^ 2 else 2 * q) 2 1 := by
    have hl : HasDerivWithinAt (fun q : ℝ => if q ≤ 1 then 1 + q ^ 2 else 2 * q) 2
        (Set.Iic 1) 1 := by
      have : HasDerivWithinAt (fun q : ℝ => 1 + q ^ 2) 2 (Set.Iic 1) 1 := by
        have h := ((hasDerivAt_pow 2 (1 : ℝ)).const_add 1).hasDerivWithinAt (s := Set.Iic 1)
        simpa using h
      exact this.congr (fun q hq => by simp [Set.mem_Iic.1 hq]) (by norm_num)
    have hr : HasDerivWithinAt (fun q : ℝ => if q ≤ 1 then 1 + q ^ 2 else 2 * q) 2
        (Set.Ici 1) 1 := by
      have : HasDerivWithinAt (fun q : ℝ => 2 * q) 2 (Set.Ici 1) 1 := by
        simpa using ((hasDerivAt_id (1 : ℝ)).const_mul 2).hasDerivWithinAt
      refine this.congr (fun q hq => ?_) (by norm_num)
      rcases eq_or_lt_of_le (Set.mem_Ici.1 hq) with h | h
      · rw [← h]; norm_num
      · simp [not_le.2 h]
    have := hl.union hr
    rw [Set.Iic_union_Ici] at this
    exact this.hasDerivAt Filter.univ_mem
  refine hpw.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1)] with q hq
  exact exercise_10_F_7_cd_shortRun (le_of_lt hq)

/-! ## A concrete instance of Example 10.F.1 -/

/-- **Example 10.F.1** (MWG, pp. 340-341), an instance: `K = 1/2`, `ψ(q) = q + q²/2` (so
`q̄ = 1`, `c̄ = 2`), demand falls from `4 - p` (`J₀ = 2` firms) to `3 - p`. The short-run price
is `5/3 < 2`, firms make losses, and in the long run one firm remains. -/
theorem example_10_F_1_instance :
    (5 / 3 : ℝ) < lumpyCost (1 / 2) (quadFirm 1 1 one_pos one_pos).c 1 / 1 ∧
    (5 / 3 : ℝ) * (quadFirm 1 1 one_pos one_pos).supply (5 / 3) -
      (1 / 2 + (quadFirm 1 1 one_pos one_pos).c ((quadFirm 1 1 one_pos one_pos).supply (5 / 3)))
        < 0 ∧
    ∀ J₁ : ℕ, (J₁ : ℝ) * 1 = 3 - lumpyCost (1 / 2) (quadFirm 1 1 one_pos one_pos).c 1 / 1 →
      J₁ < 2 ∧ IsLREqm (fun p => 3 - p) (lumpyCost (1 / 2) (quadFirm 1 1 one_pos one_pos).c)
        (lumpyCost (1 / 2) (quadFirm 1 1 one_pos one_pos).c 1 / 1) 1 J₁ := by
  set F := quadFirm 1 1 one_pos one_pos
  have hcF : lumpyCost (1 / 2) F.c = quadLumpyCost ((1 / 2) * 1 ^ 2) 1 (1 / 2) := by
    funext q
    simp only [quadLumpyCost, lumpyCost, F, quadFirm, QLFirmStrict.c, quadFirmBase]
    split_ifs <;> ring
  obtain ⟨hqb, hcb, -⟩ := quadLumpy_efficientScale (α := 1) (β := 1 / 2) (by norm_num) one_pos
  have hcb2 : lumpyCost (1 / 2) F.c 1 / 1 = 2 := by rw [hcF, hcb]; norm_num
  have hψ0 : F.c 0 = 0 := by simp [F, quadFirm, QLFirmStrict.c, quadFirmBase]
  have hsupp : F.supply (5 / 3) = 2 / 3 := by
    rw [quadFirm_supply one_pos one_pos (by norm_num : (1 : ℝ) < 5 / 3)]; norm_num
  have hqb' : IsEfficientScale (lumpyCost (1 / 2) F.c) 1 := by rw [hcF]; exact hqb
  exact example_10_F_1 (K := 1 / 2) (by norm_num) F hψ0 hqb' (x₀ := fun p => 4 - p)
    (x₁ := fun p => 3 - p) (fun p => by norm_num) (fun a _ b _ hab => by linarith)
    (J₀ := 2) (by change (2 : ℝ) * 1 = 4 - _; rw [hcb2]; norm_num) (ps := 5 / 3) (by norm_num)
    (by change 3 - (5 / 3 : ℝ) = 2 * _; rw [hsupp]; norm_num)

end MWG.CompetitiveMarkets
