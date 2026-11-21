/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMarketPower.Monopoly
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Exercises 12.B.1-12.B.10

MWG, Exercises 12.B.1-12.B.10, pp. 428-430.

* 12.B.1: the Lerner index equals the inverse elasticity; with positive marginal cost demand is
  elastic at the monopoly price.
* 12.B.2: constant-elasticity demand `x(p) = αp^{-ε}`: no optimal price when `ε ≤ 1`; for
  `ε > 1` the optimal price `pᵐ = εc/(ε − 1)`, output, margin `1/ε` and the deadweight loss.
* 12.B.3: comparative statics by the implicit function theorem (cost and demand shifts).
* 12.B.4: revealed preference: the monopoly price is nondecreasing in cost.
* 12.B.6: the per-unit subsidy `−p'(q°)q°` makes the monopolist efficient.
* 12.B.7: men's and women's demands: competition, uniform monopoly price, the efficient split
  of output, discrimination and welfare.
* 12.B.8: learning by doing; 12.B.9: investment in cost reduction; 12.B.10: quality choice.

Exercises 12.B.2(c) and 12.B.5 are in `MonopolyExercises3`.
-/

namespace MWG.MarketPower

open MWG.CompetitiveMarkets Set Filter Topology

/-! ### Exercise 12.B.1 -/

/-- The price elasticity of demand at output `q`, `ε = −(dx/dp)(p/x)`, written with the inverse
demand: since `dx/dp = 1/p'(q)` and `x = q`, `ε = −p(q)/(p'(q)q)`. -/
noncomputable def priceElasticity (p p' : ℝ → ℝ) (q : ℝ) : ℝ := -(p q) / (p' q * q)

/-- The elasticity written with the demand slope `x' = 1/p'(q)` and `x = q`. -/
theorem priceElasticity_eq_demand (p p' : ℝ → ℝ) (q : ℝ) :
    priceElasticity p p' q = -(1 / p' q) * (p q / q) := by
  unfold priceElasticity
  rw [neg_div, neg_mul, div_mul_div_comm, one_mul]

/-- **Exercise 12.B.1(a)** (MWG, p. 428). The monopolist's price-cost margin equals the inverse
of the price elasticity of demand at `pᵐ`: `(pᵐ − c'(qᵐ))/pᵐ = 1/ε`. -/
theorem exercise_12_B_1a {p c p' c' : ℝ → ℝ} {qm : ℝ}
    (hp : HasDerivWithinAt p (p' qm) (Ici 0) qm) (hc : HasDerivWithinAt c (c' qm) (Ici 0) qm)
    (hqm : IsMonopolyOptimum p c qm) (h0 : c' 0 < p 0) :
    (p qm - c' qm) / p qm = 1 / priceElasticity p p' qm := by
  obtain ⟨hpos, heq⟩ := eq_12_B_4 hp hc hqm h0
  unfold priceElasticity
  rw [one_div_div, div_neg, ← neg_div]
  congr 1
  linarith

/-- **Exercise 12.B.1(b)** (MWG, p. 428). If marginal cost is positive (and `p'(qᵐ) < 0`),
demand is elastic at the monopoly price: `ε > 1`. -/
theorem exercise_12_B_1b {p c p' c' : ℝ → ℝ} {qm : ℝ}
    (hp : HasDerivWithinAt p (p' qm) (Ici 0) qm) (hc : HasDerivWithinAt c (c' qm) (Ici 0) qm)
    (hqm : IsMonopolyOptimum p c qm) (h0 : c' 0 < p 0) (hneg : p' qm < 0)
    (hmc : 0 < c' qm) : 1 < priceElasticity p p' qm := by
  obtain ⟨hpos, heq⟩ := eq_12_B_4 hp hc hqm h0
  have hgt := monopoly_price_gt_mc hp hc hqm h0 hneg
  unfold priceElasticity
  have hd : 0 < -(p' qm * qm) := by nlinarith
  rw [neg_div, ← div_neg, lt_div_iff₀ hd]
  linarith

/-! ### Exercise 12.B.2 -/

/-- Profit at price `p` with constant-elasticity demand `x(p) = αp^{-ε}` and unit cost `c`. -/
noncomputable def ceProfit (α ε c p : ℝ) : ℝ := (p - c) * (α * p ^ (-ε))

theorem ceProfit_eq {α ε c p : ℝ} (hp : 0 < p) :
    ceProfit α ε c p = α * (p ^ (1 - ε) - c * p ^ (-ε)) := by
  unfold ceProfit
  have : p ^ (1 - ε) = p ^ (-ε) * p := by
    rw [show 1 - ε = -ε + 1 by ring, Real.rpow_add hp, Real.rpow_one]
  rw [this]; ring

/-- **Exercise 12.B.2(a)** (MWG, p. 429). With `x(p) = αp^{-ε}`, `0 < ε ≤ 1` and `c > 0`, the
monopolist's optimal price is not well defined: every price is beaten by a higher one. -/
theorem exercise_12_B_2a {α ε c : ℝ} (hα : 0 < α) (hε : 0 < ε) (hε1 : ε ≤ 1) (hc : 0 < c) :
    ∀ p, 0 < p → ∃ p', 0 < p' ∧ ceProfit α ε c p < ceProfit α ε c p' := by
  intro p hp
  rcases le_or_gt p c with hpc | hpc
  · refine ⟨c + 1, by linarith, ?_⟩
    unfold ceProfit
    have h1 : 0 < α * (c + 1) ^ (-ε) := mul_pos hα (Real.rpow_pos_of_pos (by linarith) _)
    have h2 : 0 ≤ α * p ^ (-ε) := (mul_pos hα (Real.rpow_pos_of_pos hp _)).le
    nlinarith
  · refine ⟨p + 1, by linarith, ?_⟩
    rw [ceProfit_eq hp, ceProfit_eq (by linarith)]
    have h1 : p ^ (1 - ε) ≤ (p + 1) ^ (1 - ε) :=
      Real.rpow_le_rpow hp.le (by linarith) (by linarith)
    have h2 : (p + 1) ^ (-ε) < p ^ (-ε) :=
      Real.rpow_lt_rpow_of_neg hp (by linarith) (by linarith)
    have h3 := mul_lt_mul_of_pos_left h2 hc
    exact mul_lt_mul_of_pos_left (by linarith) hα

/-- The derivative of the constant-elasticity profit: `α p^{-ε-1}((1 − ε)p + εc)`. -/
theorem ceProfit_hasDerivAt {α ε c p : ℝ} (hp : 0 < p) :
    HasDerivAt (fun r => α * (r ^ (1 - ε) - c * r ^ (-ε)))
      (α * (p ^ (-ε - 1) * ((1 - ε) * p + ε * c))) p := by
  have h1 := Real.hasDerivAt_rpow_const (x := p) (p := 1 - ε) (Or.inl hp.ne')
  have h2 := Real.hasDerivAt_rpow_const (x := p) (p := -ε) (Or.inl hp.ne')
  have h := ((h1.sub (h2.const_mul c)).const_mul α)
  refine h.congr_deriv ?_
  have e1 : p ^ (1 - ε - 1) = p ^ (-ε - 1) * p := by
    rw [show 1 - ε - 1 = -ε - 1 + 1 by ring, Real.rpow_add hp, Real.rpow_one]
  rw [e1]; ring

/-- **Exercise 12.B.2(b)** (MWG, p. 429). With `ε > 1` the optimal price is
`pᵐ = εc/(ε − 1)`: it is the unique maximizer of profit over `p > 0`; the output is
`qᵐ = α(pᵐ)^{-ε}` and the price-cost margin `(pᵐ − c)/pᵐ` is `1/ε`. -/
theorem exercise_12_B_2b {α ε c : ℝ} (hα : 0 < α) (hε : 1 < ε) (hc : 0 < c) :
    (∀ p, 0 < p → p ≠ ε * c / (ε - 1) → ceProfit α ε c p < ceProfit α ε c (ε * c / (ε - 1))) ∧
    (ε * c / (ε - 1) - c) / (ε * c / (ε - 1)) = 1 / ε := by
  set pm := ε * c / (ε - 1) with hpm
  have hε1 : 0 < ε - 1 := by linarith
  have hpm0 : 0 < pm := by positivity
  have hD : ∀ p, 0 < p → (0 < (1 - ε) * p + ε * c ↔ p < pm) := by
    intro p hp
    rw [hpm, lt_div_iff₀ hε1]
    constructor <;> intro h <;> linarith
  have hderiv : ∀ x, 0 < x → HasDerivAt (fun r => α * (r ^ (1 - ε) - c * r ^ (-ε)))
      (α * (x ^ (-ε - 1) * ((1 - ε) * x + ε * c))) x := fun x hx => ceProfit_hasDerivAt hx
  have hcont : ContinuousOn (fun r => α * (r ^ (1 - ε) - c * r ^ (-ε))) (Ioi 0) :=
    fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
  have hmono : StrictMonoOn (fun r => α * (r ^ (1 - ε) - c * r ^ (-ε))) (Ioc 0 pm) := by
    refine strictMonoOn_of_hasDerivWithinAt_pos (convex_Ioc 0 pm)
      (f' := fun x => α * (x ^ (-ε - 1) * ((1 - ε) * x + ε * c)))
      (hcont.mono Ioc_subset_Ioi_self) (fun x hx => ?_) (fun x hx => ?_)
    · rw [interior_Ioc] at hx; exact (hderiv x hx.1).hasDerivWithinAt
    · rw [interior_Ioc] at hx
      have := (hD x hx.1).2 hx.2
      exact mul_pos hα (mul_pos (Real.rpow_pos_of_pos hx.1 _) this)
  have hanti : StrictAntiOn (fun r => α * (r ^ (1 - ε) - c * r ^ (-ε))) (Ici pm) := by
    refine strictAntiOn_of_hasDerivWithinAt_neg (convex_Ici pm)
      (f' := fun x => α * (x ^ (-ε - 1) * ((1 - ε) * x + ε * c)))
      (hcont.mono fun x hx => lt_of_lt_of_le hpm0 hx) (fun x hx => ?_) (fun x hx => ?_)
    · rw [interior_Ici] at hx; exact (hderiv x (hpm0.trans hx)).hasDerivWithinAt
    · rw [interior_Ici] at hx
      have hx0 : 0 < x := hpm0.trans hx
      have : ¬ (0 < (1 - ε) * x + ε * c) := fun h => absurd ((hD x hx0).1 h) (not_lt.2 hx.le)
      push Not at this
      have h3 : (1 - ε) * x + ε * c < 0 := by
        rcases eq_or_lt_of_le this with h | h
        · exfalso; have : x = pm := by rw [hpm]; field_simp; linarith
          exact (ne_of_gt hx) this
        · exact h
      exact mul_neg_of_pos_of_neg hα (mul_neg_of_pos_of_neg (Real.rpow_pos_of_pos hx0 _) h3)
  have hm : ε * c / (ε - 1) - c = c / (ε - 1) := by field_simp; ring
  refine ⟨fun p hp hne => ?_, ?_⟩
  swap
  · rw [hpm, hm, div_div_div_cancel_right₀ hε1.ne', div_mul_cancel_right₀ hc.ne', one_div]
  rw [ceProfit_eq hp, ceProfit_eq hpm0]
  rcases lt_or_gt_of_ne hne with h | h
  · exact hmono ⟨hp, h.le⟩ ⟨hpm0, le_rfl⟩ h
  · exact hanti (mem_Ici.2 le_rfl) (mem_Ici.2 h.le) h

/-- **Exercise 12.B.2(b), the deadweight loss** (MWG, pp. 386 and 429). The inverse demand of
`x(p) = αp^{-ε}` is `p(s) = (s/α)^{-1/ε} = α^{1/ε}s^{-1/ε}`; with `0 < qᵐ < q°` the deadweight loss
`∫_{qᵐ}^{q°} (p(s) − c) ds` equals
`α^{1/ε}((q°)^{1-1/ε} − (qᵐ)^{1-1/ε})/(1 − 1/ε) − c(q° − qᵐ)`. -/
theorem exercise_12_B_2b_dwl {α ε c qm q0 : ℝ} (hα : 0 < α) (hε : 1 < ε) (hqm : 0 < qm)
    (hlt : qm < q0) :
    (∀ s, 0 < s → (s / α) ^ (-(1 / ε)) = α ^ (1 / ε) * s ^ (-(1 / ε))) ∧
    ∫ s in qm..q0, (α ^ (1 / ε) * s ^ (-(1 / ε)) - c) =
      α ^ (1 / ε) * (q0 ^ (1 - 1 / ε) - qm ^ (1 - 1 / ε)) / (1 - 1 / ε) - c * (q0 - qm) := by
  have hε0 : 0 < ε := by linarith
  refine ⟨fun s hs => ?_, ?_⟩
  · rw [Real.div_rpow hs.le hα.le, Real.rpow_neg hs.le, Real.rpow_neg hα.le, div_eq_mul_inv,
      inv_inv, mul_comm]
  have hr : -1 < -(1 / ε) := by
    have : 1 / ε < 1 := by rw [div_lt_one hε0]; exact hε
    linarith
  have hint : IntervalIntegrable (fun s : ℝ => α ^ (1 / ε) * s ^ (-(1 / ε))) MeasureTheory.volume
      qm q0 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hlt.le]
    exact continuousOn_const.mul (fun x hx => (Real.continuousAt_rpow_const x _
      (Or.inl (hqm.trans_le hx.1).ne')).continuousWithinAt)
  rw [intervalIntegral.integral_sub hint intervalIntegrable_const,
    intervalIntegral.integral_const_mul, integral_rpow (Or.inl hr), intervalIntegral.integral_const,
    smul_eq_mul]
  rw [show -(1 / ε) + 1 = 1 - 1 / ε by ring]
  ring

/-! ### Exercise 12.B.3 -/

/-- The slope of an implicitly defined function: if `G(q(t), t) = 0` near `t₀`, `G` has
derivative `L` at `(q(t₀), t₀)` and `q` has derivative `q'` at `t₀`, then
`G_q q' + G_t = 0`, i.e. `q' = −G_t/G_q`. -/
theorem implicit_slope {G : ℝ × ℝ → ℝ} {L : ℝ × ℝ →L[ℝ] ℝ} {q : ℝ → ℝ} {q' t₀ : ℝ}
    (hG : HasFDerivAt G L (q t₀, t₀)) (hq : HasDerivAt q q' t₀)
    (hzero : ∀ᶠ t in 𝓝 t₀, G (q t, t) = 0) : L (1, 0) * q' + L (0, 1) = 0 := by
  have hf : HasDerivAt (fun t => (q t, t)) (q', 1) t₀ := hq.prodMk (hasDerivAt_id t₀)
  have hcomp := HasFDerivAt.comp_hasDerivAt (f := fun t => (q t, t)) t₀ hG hf
  have h0 : HasDerivAt (G ∘ fun t => (q t, t)) 0 t₀ :=
    (hasDerivAt_const t₀ (0 : ℝ)).congr_of_eventuallyEq (hzero.mono fun t ht => ht)
  have heq := hcomp.unique h0
  have hsplit : ((q', 1) : ℝ × ℝ) = q' • ((1 : ℝ), (0 : ℝ)) + ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [hsplit, map_add, map_smul, smul_eq_mul] at heq
  linarith

/-- **Exercise 12.B.3, a cost shift** (MWG, p. 429). Let the monopolist's optimal output `q(φ)`
satisfy the first-order condition `G(q(φ), φ) = 0` near `φ₀`, where
`G(q, φ) = p'(q)q + p(q) − c_q(q, φ)` has partial derivatives `G_q < 0` (second-order
condition) and `G_φ = −c_{qφ}`. Then `q'(φ₀) = −c_{qφ}/G_q · (−1)`, i.e. `G_q q' = c_{qφ}`, and the
price `p(q(φ))` (with `p' < 0`) increases (has positive derivative) iff `c_{qφ} > 0`. -/
theorem exercise_12_B_3_cost {G : ℝ × ℝ → ℝ} {L : ℝ × ℝ →L[ℝ] ℝ} {q p : ℝ → ℝ}
    {q' φ₀ dp cqφ : ℝ} (hG : HasFDerivAt G L (q φ₀, φ₀)) (hq : HasDerivAt q q' φ₀)
    (hzero : ∀ᶠ φ in 𝓝 φ₀, G (q φ, φ) = 0) (hsoc : L (1, 0) < 0) (hGφ : L (0, 1) = -cqφ)
    (hp : HasDerivAt p dp (q φ₀)) (hdp : dp < 0) :
    L (1, 0) * q' = cqφ ∧ HasDerivAt (fun φ => p (q φ)) (dp * q') φ₀ ∧
      (0 < dp * q' ↔ 0 < cqφ) := by
  have h := implicit_slope hG hq hzero
  have h1 : L (1, 0) * q' = cqφ := by linarith
  refine ⟨h1, hp.comp φ₀ hq, ?_⟩
  constructor
  · intro hpos
    have hq' : q' < 0 := by
      by_contra hge; push Not at hge; nlinarith
    nlinarith
  · intro hpos
    have hq' : q' < 0 := by
      by_contra hge; push Not at hge; nlinarith
    nlinarith

/-- **Exercise 12.B.3, a demand shift** (MWG, p. 429). With `G(q, θ) = P_q(q, θ)q + P(q, θ) − c'(q)`
and `G_q < 0`, the output responds by `q' = −G_θ/G_q`, and the price `P(q(θ), θ)` changes at the
rate `P_θ + P_q q'`; it rises iff `P_θ G_q < P_q G_θ`. -/
theorem exercise_12_B_3_demand {G P : ℝ × ℝ → ℝ} {L M : ℝ × ℝ →L[ℝ] ℝ} {q : ℝ → ℝ}
    {q' θ₀ : ℝ} (hG : HasFDerivAt G L (q θ₀, θ₀)) (hq : HasDerivAt q q' θ₀)
    (hzero : ∀ᶠ θ in 𝓝 θ₀, G (q θ, θ) = 0) (hsoc : L (1, 0) < 0)
    (hP : HasFDerivAt P M (q θ₀, θ₀)) :
    q' = -L (0, 1) / L (1, 0) ∧
    HasDerivAt (fun θ => P (q θ, θ)) (M (1, 0) * q' + M (0, 1)) θ₀ ∧
    (0 < M (1, 0) * q' + M (0, 1) ↔ M (0, 1) * L (1, 0) < M (1, 0) * L (0, 1)) := by
  have h := implicit_slope hG hq hzero
  have hne : L (1, 0) ≠ 0 := hsoc.ne
  have hq'eq : q' = -L (0, 1) / L (1, 0) := by
    rw [eq_div_iff hne]; linarith
  have hf : HasDerivAt (fun t => (q t, t)) (q', 1) θ₀ := hq.prodMk (hasDerivAt_id θ₀)
  have hcomp := HasFDerivAt.comp_hasDerivAt (f := fun t => (q t, t)) θ₀ hP hf
  have hsplit : ((q', 1) : ℝ × ℝ) = q' • ((1 : ℝ), (0 : ℝ)) + ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [hsplit, map_add, map_smul, smul_eq_mul] at hcomp
  refine ⟨hq'eq, by rw [mul_comm]; exact hcomp, ?_⟩
  have hval : M (1, 0) * q' + M (0, 1) =
      (M (0, 1) * L (1, 0) - M (1, 0) * L (0, 1)) / L (1, 0) := by
    rw [hq'eq]; field_simp; ring
  rw [hval, lt_div_iff_of_neg hsoc, zero_mul]
  constructor <;> intro h <;> linarith

/-! ### Exercise 12.B.4 -/

/-- **Exercise 12.B.4, constant unit cost** (MWG, p. 429). If `pᵢ` is a monopoly price at unit
cost `cᵢ` and `c₁ < c₂`, then `x(p₂) ≤ x(p₁)` (revealed preference); with demand strictly
decreasing where positive, `p₁ ≤ p₂` whenever `x(p₂) > 0`. -/
theorem exercise_12_B_4_cost (x : ℝ → ℝ) {c₁ c₂ p₁ p₂ : ℝ} (hc : c₁ < c₂)
    (h₁ : ∀ r, (r - c₁) * x r ≤ (p₁ - c₁) * x p₁) (h₂ : ∀ r, (r - c₂) * x r ≤ (p₂ - c₂) * x p₂)
    (hdec : ∀ r s, r < s → 0 < x r → x s < x r) :
    x p₂ ≤ x p₁ ∧ (0 < x p₂ → p₁ ≤ p₂) := by
  have a := h₁ p₂
  have b := h₂ p₁
  have hx : x p₂ ≤ x p₁ := by nlinarith
  refine ⟨hx, fun hpos => ?_⟩
  by_contra hlt
  push Not at hlt
  linarith [hdec p₂ p₁ hlt hpos]

/-- **Exercise 12.B.4, a cost parameter** (MWG, p. 429). Let the cost `C(q, φ)` have strictly
increasing differences: `C(q'', φ) − C(q', φ)` is strictly increasing in `φ` for `q'' > q'`.
If `pᵢ` maximizes `r x(r) − C(x(r), φᵢ)` and `φ₁ < φ₂`, then `x(p₂) ≤ x(p₁)`, and so the monopoly
price is nondecreasing in `φ` (`p₁ ≤ p₂` when `x(p₂) > 0`). In terms of Exercise 12.B.3 the
condition is `c_{qφ} > 0`. -/
theorem exercise_12_B_4_param (x : ℝ → ℝ) (C : ℝ → ℝ → ℝ) {φ₁ φ₂ p₁ p₂ : ℝ} (hφ : φ₁ < φ₂)
    (hinc : ∀ q'' q', q' < q'' → C q'' φ₁ - C q' φ₁ < C q'' φ₂ - C q' φ₂)
    (h₁ : ∀ r, r * x r - C (x r) φ₁ ≤ p₁ * x p₁ - C (x p₁) φ₁)
    (h₂ : ∀ r, r * x r - C (x r) φ₂ ≤ p₂ * x p₂ - C (x p₂) φ₂)
    (hdec : ∀ r s, r < s → 0 < x r → x s < x r) :
    x p₂ ≤ x p₁ ∧ (0 < x p₂ → p₁ ≤ p₂) := by
  have _ := hφ
  have hx : x p₂ ≤ x p₁ := by
    by_contra hlt
    push Not at hlt
    have := hinc (x p₂) (x p₁) hlt
    linarith [h₁ p₂, h₂ p₁]
  refine ⟨hx, fun hpos => ?_⟩
  by_contra hlt
  push Not at hlt
  linarith [hdec p₂ p₁ hlt hpos]

/-! ### Exercise 12.B.6 -/

/-- **Exercise 12.B.6** (MWG, p. 429). Let `p(q)q − c(q)` be concave (antitone derivative) and
let `q° > 0` be efficient, `p(q°) = c'(q°)`. A per-unit subsidy `s` makes `q°` optimal for the
monopolist (who then maximizes `p(q)q − c(q) + sq`) if and only if `s = −p'(q°)q°`. -/
theorem exercise_12_B_6 {p c p' c' : ℝ → ℝ} {q0 : ℝ} (hq0 : 0 < q0)
    (hp : ∀ q ∈ Ici (0 : ℝ), HasDerivWithinAt p (p' q) (Ici 0) q)
    (hc : ∀ q ∈ Ici (0 : ℝ), HasDerivWithinAt c (c' q) (Ici 0) q)
    (hconc : AntitoneOn (fun q => p' q * q + p q - c' q) (Ici 0)) (heff : p q0 = c' q0)
    (s : ℝ) :
    (∀ q, 0 ≤ q → monopolyProfit p c q + s * q ≤ monopolyProfit p c q0 + s * q0) ↔
      s = -(p' q0 * q0) := by
  have hd : ∀ q ∈ Ici (0 : ℝ), HasDerivWithinAt (fun q => monopolyProfit p c q + s * q)
      (p' q * q + p q - c' q + s) (Ici 0) q := by
    intro q hq
    exact ((hasDerivWithinAt_monopolyProfit (hp q hq) (hc q hq)).add
      ((hasDerivWithinAt_id q (Ici 0)).const_mul s)).congr_deriv (by simp)
  have hanti : AntitoneOn (fun q => p' q * q + p q - c' q + s) (Ici 0) :=
    fun a ha b hb hab => by simpa using hconc ha hb hab
  rw [foc_max_iff hd hanti hq0.le]
  constructor
  · rintro ⟨_, h⟩; have := h hq0; linarith
  · intro hs; refine ⟨by rw [hs]; linarith, fun _ => by rw [hs]; linarith⟩

/-! ### Exercise 12.B.7 -/

/-- The gross benefit `∫₀ˣ (a − s)/θ ds = (ax − x²/2)/θ` of a group with demand `a − θp`. -/
noncomputable def groupBenefit (a θ x : ℝ) : ℝ := (a * x - x ^ 2 / 2) / θ

/-- Marshallian aggregate surplus when men consume `xm`, women `xw` and unit cost is `c`. -/
noncomputable def widgetWelfare (a θm θw c xm xw : ℝ) : ℝ :=
  groupBenefit a θm xm + groupBenefit a θw xw - c * (xm + xw)

/-- **Exercise 12.B.7(a)** (MWG, p. 429). In the competitive equilibrium the price is `c`,
men buy `a − θₘc` and women `a − θ_wc`; this maximizes aggregate surplus. -/
theorem exercise_12_B_7a {a θm θw c : ℝ} (hm : 0 < θm) (hw : 0 < θw) :
    ∀ xm xw, widgetWelfare a θm θw c xm xw ≤
      widgetWelfare a θm θw c (a - θm * c) (a - θw * c) := by
  intro xm xw
  unfold widgetWelfare groupBenefit
  rw [div_add_div _ _ hm.ne' hw.ne', div_add_div _ _ hm.ne' hw.ne', div_sub' (by positivity),
    div_sub' (by positivity), div_le_div_iff_of_pos_right (by positivity)]
  nlinarith [mul_nonneg hw.le (sq_nonneg (xm - (a - θm * c))),
    mul_nonneg hm.le (sq_nonneg (xw - (a - θw * c)))]

/-- **Exercise 12.B.7(b)** (MWG, p. 429). Let `θ_w < θₘ` and `Θ = θₘ + θ_w`. On prices
`p ≤ a/θₘ` both groups buy and profit `(p − c)(2a − Θp)` is at most its value at
`p* = (2a + Θc)/(2Θ)`; on `[a/θₘ, a/θ_w]` only women buy and profit `(p − c)(a − θ_wp)` is at most
its value at `(a/θ_w + c)/2`. Hence the profit-maximizing uniform price is `p*` or
`(a/θ_w + c)/2`, and both groups consume when `p* < a/θₘ` and `p*` gives the larger profit. -/
theorem exercise_12_B_7b {a θm θw c : ℝ} (hm : 0 < θm) (hw : 0 < θw) (hθ : θw < θm) :
    (∀ p, (p - c) * (2 * a - (θm + θw) * p) ≤
      ((2 * a + (θm + θw) * c) / (2 * (θm + θw)) - c) *
        (2 * a - (θm + θw) * ((2 * a + (θm + θw) * c) / (2 * (θm + θw))))) ∧
    (∀ p, (p - c) * (a - θw * p) ≤ ((a / θw + c) / 2 - c) * (a - θw * ((a / θw + c) / 2))) ∧
    (∀ p, 0 ≤ p → p ≤ a / θm →
      max (a - θm * p) 0 + max (a - θw * p) 0 = 2 * a - (θm + θw) * p) ∧
    (∀ p, a / θm ≤ p → p ≤ a / θw → max (a - θm * p) 0 + max (a - θw * p) 0 = a - θw * p) := by
  have hΘ : 0 < θm + θw := by linarith
  refine ⟨fun p => ?_, fun p => ?_, fun p hp0 hp => ?_, fun p hp1 hp2 => ?_⟩
  · have key : ((2 * a + (θm + θw) * c) / (2 * (θm + θw)) - c) *
        (2 * a - (θm + θw) * ((2 * a + (θm + θw) * c) / (2 * (θm + θw)))) -
        (p - c) * (2 * a - (θm + θw) * p) =
        (θm + θw) * (p - (2 * a + (θm + θw) * c) / (2 * (θm + θw))) ^ 2 := by
      field_simp; ring
    nlinarith [mul_nonneg hΘ.le (sq_nonneg (p - (2 * a + (θm + θw) * c) / (2 * (θm + θw))))]
  · have key : ((a / θw + c) / 2 - c) * (a - θw * ((a / θw + c) / 2)) - (p - c) * (a - θw * p) =
        θw * (p - (a / θw + c) / 2) ^ 2 := by
      field_simp; ring
    nlinarith [mul_nonneg hw.le (sq_nonneg (p - (a / θw + c) / 2))]
  · have h1 : 0 ≤ a - θm * p := by
      have := mul_le_mul_of_nonneg_left hp hm.le
      rw [mul_div_cancel₀ _ hm.ne'] at this; linarith
    have h2 : 0 ≤ a - θw * p := by nlinarith
    rw [max_eq_left h1, max_eq_left h2]; ring
  · have h1 : a - θm * p ≤ 0 := by
      have := mul_le_mul_of_nonneg_left hp1 hm.le
      rw [mul_div_cancel₀ _ hm.ne'] at this; linarith
    have h2 : 0 ≤ a - θw * p := by
      have := mul_le_mul_of_nonneg_left hp2 hw.le
      rw [mul_div_cancel₀ _ hw.ne'] at this; linarith
    rw [max_eq_right h1, max_eq_left h2]; ring

end MWG.MarketPower
