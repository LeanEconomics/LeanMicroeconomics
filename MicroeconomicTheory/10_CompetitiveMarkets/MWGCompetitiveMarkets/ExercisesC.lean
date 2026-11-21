/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGCompetitiveMarkets.ExercisesF2
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Exercises 10.C.1, 10.C.2, 10.C.8-10.C.11 and 10.D.2 (MWG, pp. 344-346)

* **Exercise 10.C.1**: Cobb-Douglas (log) demand `x_ℓ = w/(L p_ℓ)` and its wealth effect
  `1/(L p_ℓ)`, which vanishes when the number of goods and wealth grow proportionally.
* **Exercise 10.C.2** and **Exercise 10.D.2**: `φ(x) = α + β ln x`, `c(q) = σq`: first-order
  conditions, equilibrium `p = σ`, `x = q = β/σ`, and the same optimal levels.
* **Exercise 10.C.8**: the envelope formula `dπ/dα = p*'q* - c_α`, the weakest sufficient
  condition `c_α > q c_qα` (i.e. `∂MC/∂α < ∂AC/∂α`) for profits to fall for every demand with
  `x' ≤ 0`, and its factor-demand form (`z_k > q ∂z_k/∂q`).
* **Exercise 10.C.9**: a rise in `w_k` lowers the equilibrium price iff `k` is inferior.
* **Exercise 10.C.10**: constant-elasticity demand and marginal cost: equilibrium in logs and
  comparative statics.
* **Exercise 10.C.11**: the difference in profits of two firms with marginally different
  technologies, `-c_α Δα`.
-/

namespace MWG.CompetitiveMarkets

open Filter Topology MWG.ConsumerChoice MWG.ClassicalDemand

/-! ## Exercise 10.C.1 -/

/-- **Exercise 10.C.1(a)** (MWG, p. 344). With `u(x) = ∑ₗ ln xₗ` on strictly positive bundles,
`p ≫ 0` and `w > 0`, the Walrasian demand is `xₗ = w/(L pₗ)`. -/
theorem exercise_10_C_1a {L : ℕ} (hL : 0 < L) {p : Fin L → ℝ} (hp : ∀ l, 0 < p l) {w : ℝ}
    (hw : 0 < w) :
    walrasianDemandOn {x | ∀ l, 0 < x l} (fun x => ∑ l, Real.log (x l)) p w =
      {fun l => w / (L * p l)} := by
  have hL' : (0 : ℝ) < L := Nat.cast_pos.2 hL
  set xs : Fin L → ℝ := fun l => w / (L * p l) with hxs
  have hxs0 : ∀ l, 0 < xs l := fun l => by simp only [hxs]; have := hp l; positivity
  have hbud : p ⬝ᵥ xs = w := by
    simp only [dotProduct, hxs]
    have : ∀ l, p l * (w / (L * p l)) = w / L := fun l => by
      have := (hp l).ne'; field_simp
    simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  -- the key inequality: `∑ log yₗ - ∑ log xsₗ ≤ ∑ (yₗ/xsₗ - 1) = (L/w) p·y - L`
  have hratio : ∀ y : Fin L → ℝ, (∀ l, 0 < y l) →
      ∑ l, (y l / xs l - 1) = L / w * (p ⬝ᵥ y) - L := by
    intro y _
    simp only [dotProduct, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one, Finset.mul_sum, hxs]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    have := (hp l).ne'
    field_simp
  have hlog : ∀ y : Fin L → ℝ, (∀ l, 0 < y l) →
      ∑ l, Real.log (y l) - ∑ l, Real.log (xs l) = ∑ l, Real.log (y l / xs l) := by
    intro y hy
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun l _ => (Real.log_div (hy l).ne' (hxs0 l).ne').symm
  ext y
  simp only [Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨hy, hyb⟩, hmax⟩
    have hy' : ∀ l, 0 < y l := hy
    have hle := hmax xs ⟨hxs0, hbud.le⟩
    simp only at hle
    by_contra hne
    obtain ⟨l, hl⟩ := Function.ne_iff.1 hne
    have hstrict : ∑ k, Real.log (y k / xs k) < ∑ k, (y k / xs k - 1) := by
      refine Finset.sum_lt_sum (fun k _ => Real.log_le_sub_one_of_pos (div_pos (hy' k)
        (hxs0 k))) ⟨l, Finset.mem_univ l, Real.log_lt_sub_one_of_pos (div_pos (hy' l) (hxs0 l))
        fun h => hl ((div_eq_one_iff_eq (hxs0 l).ne').1 h)⟩
    rw [← hlog y hy', hratio y hy'] at hstrict
    have : L / w * (p ⬝ᵥ y) ≤ L := by
      calc L / w * (p ⬝ᵥ y) ≤ L / w * w := mul_le_mul_of_nonneg_left hyb (by positivity)
        _ = L := by field_simp
    linarith
  · rintro rfl
    refine ⟨⟨hxs0, hbud.le⟩, fun y ⟨hy, hyb⟩ => ?_⟩
    have hy' : ∀ l, 0 < y l := hy
    have h1 : ∑ l, Real.log (y l / xs l) ≤ ∑ l, (y l / xs l - 1) :=
      Finset.sum_le_sum fun l _ => Real.log_le_sub_one_of_pos (div_pos (hy' l) (hxs0 l))
    rw [← hlog y hy', hratio y hy'] at h1
    have : L / w * (p ⬝ᵥ y) ≤ L := by
      calc L / w * (p ⬝ᵥ y) ≤ L / w * w := mul_le_mul_of_nonneg_left hyb (by positivity)
        _ = L := by field_simp
    simp only
    linarith

/-- **Exercise 10.C.1(a)** (MWG, p. 344): the wealth effect on good `ℓ` is `∂xₗ/∂w = 1/(L pₗ)`. -/
theorem exercise_10_C_1a_wealth {L : ℕ} {pl w : ℝ} :
    HasDerivAt (fun w => w / (L * pl)) (1 / (L * pl)) w := by
  simpa using (hasDerivAt_id w).div_const ((L : ℝ) * pl)

/-- **Exercise 10.C.1(b)** (MWG, p. 344). If the number of goods `L` and wealth `w = L w₀` grow
proportionally, the demand for good `ℓ` stays `w₀/pₗ` while its wealth effect `1/(L pₗ)` tends
to `0`. -/
theorem exercise_10_C_1b {pl w₀ : ℝ} (hpl : 0 < pl) :
    (∀ L : ℕ, 0 < L → (L * w₀) / (L * pl) = w₀ / pl) ∧
      Tendsto (fun L : ℕ => 1 / ((L : ℝ) * pl)) atTop (𝓝 0) := by
  refine ⟨fun L hL => by
    have : (0 : ℝ) < L := Nat.cast_pos.2 hL
    field_simp, ?_⟩
  refine Tendsto.div_atTop tendsto_const_nhds ?_
  exact Tendsto.atTop_mul_const hpl tendsto_natCast_atTop_atTop

/-! ## Exercises 10.C.2 and 10.D.2 -/

/-- The consumer's problem with `φ(x) = α + β ln x` (`β > 0`) at price `p > 0` is solved uniquely
by `x = β/p` over `x > 0`. -/
theorem logConsumer_max {α β p : ℝ} (hβ : 0 < β) (hp : 0 < p) {x : ℝ} (hx : 0 < x) :
    (∀ y, 0 < y → α + β * Real.log y - p * y ≤ α + β * Real.log x - p * x) ↔ x = β / p := by
  have key : ∀ y, 0 < y → α + β * Real.log y - p * y ≤
      α + β * Real.log (β / p) - p * (β / p) := by
    intro y hy
    have h := Real.log_le_sub_one_of_pos (div_pos (mul_pos hp hy) hβ)
    rw [Real.log_div (mul_pos hp hy).ne' hβ.ne', Real.log_mul hp.ne' hy.ne'] at h
    rw [Real.log_div hβ.ne' hp.ne']
    have e : p * (β / p) = β := by field_simp
    rw [e]
    have : β * (Real.log p + Real.log y - Real.log β) ≤ β * (p * y / β - 1) :=
      mul_le_mul_of_nonneg_left h hβ.le
    have e2 : β * (p * y / β - 1) = p * y - β := by field_simp
    nlinarith
  constructor
  · intro hmax
    by_contra hne
    have h := hmax (β / p) (div_pos hβ hp)
    have hstrict := Real.log_lt_sub_one_of_pos (div_pos (mul_pos hp hx) hβ) (by
      intro h1
      apply hne
      rw [div_eq_one_iff_eq hβ.ne'] at h1
      field_simp; linarith)
    rw [Real.log_div (mul_pos hp hx).ne' hβ.ne', Real.log_mul hp.ne' hx.ne'] at hstrict
    rw [Real.log_div hβ.ne' hp.ne'] at h
    have e : p * (β / p) = β := by field_simp
    rw [e] at h
    have : β * (Real.log p + Real.log x - Real.log β) < β * (p * x / β - 1) :=
      mul_lt_mul_of_pos_left hstrict hβ
    have e2 : β * (p * x / β - 1) = p * x - β := by field_simp
    nlinarith
  · rintro rfl
    exact key

/-- **Exercise 10.C.2(a)** (MWG, p. 344): first-order conditions. The consumer demands
`x = β/p` (and has no optimum if `p ≤ 0`); the firm with `c(q) = σq` maximizes profit at `q ≥ 0`
iff `p ≤ σ`, with equality if `q > 0`. -/
theorem exercise_10_C_2a {α β σ : ℝ} (hβ : 0 < β) :
    (∀ p, p ≤ 0 → ∀ x, 0 < x → ∃ y, 0 < y ∧
      α + β * Real.log x - p * x < α + β * Real.log y - p * y) ∧
    (∀ p q, 0 ≤ q → ((∀ q', 0 ≤ q' → p * q' - σ * q' ≤ p * q - σ * q) ↔
      p ≤ σ ∧ (0 < q → p = σ))) := by
  refine ⟨fun p hp x hx => ⟨x + 1, by linarith, ?_⟩, fun p q hq => ⟨fun h => ?_, ?_⟩⟩
  · have := Real.log_lt_log hx (by linarith : x < x + 1)
    nlinarith
  · have hle : p ≤ σ := by
      by_contra hlt; push Not at hlt
      have := h (q + 1) (by linarith); nlinarith
    refine ⟨hle, fun hq0 => le_antisymm hle ?_⟩
    by_contra hlt; push Not at hlt
    have := h 0 le_rfl; nlinarith
  · rintro ⟨hle, heq⟩ q' hq'
    rcases eq_or_lt_of_le hq with h0 | hpos
    · rw [← h0]; nlinarith
    · rw [heq hpos]; ring_nf; exact le_rfl

/-- **Exercise 10.C.2(b)** (MWG, p. 344). With one consumer (`φ = α + β ln x`) and one firm
(`c = σq`), a price `p` and positive consumption `x` with production `q` form an equilibrium
(utility maximization, profit maximization, `x = q`) iff `p = σ` and `x = q = β/σ`. The
equilibrium does not depend on `α`, increases in `β` and decreases in `σ`. -/
theorem exercise_10_C_2b {α β σ : ℝ} (hβ : 0 < β) (hσ : 0 < σ) {p x q : ℝ} (hx : 0 < x)
    (hq : 0 ≤ q) :
    ((∀ y, 0 < y → α + β * Real.log y - p * y ≤ α + β * Real.log x - p * x) ∧
      (∀ q', 0 ≤ q' → p * q' - σ * q' ≤ p * q - σ * q) ∧ x = q) ↔
      p = σ ∧ x = β / σ ∧ q = β / σ := by
  constructor
  · rintro ⟨hcons, hfirm, hxq⟩
    have hp : 0 < p := by
      by_contra hle; push Not at hle
      obtain ⟨y, hy, hlt⟩ := (exercise_10_C_2a (α := α) (σ := σ) hβ).1 p hle x hx
      have := hcons y hy; linarith
    have hx' := (logConsumer_max hβ hp hx).1 hcons
    have hfoc := ((exercise_10_C_2a (α := α) (σ := σ) hβ).2 p q hq).1 hfirm
    have hpσ : p = σ := hfoc.2 (hxq ▸ hx)
    subst hpσ
    exact ⟨rfl, hx', hxq ▸ hx'⟩
  · rintro ⟨rfl, hx', hq'⟩
    refine ⟨(logConsumer_max hβ hσ hx).2 hx', fun q' _ => by ring_nf; exact le_rfl, ?_⟩
    rw [hx', hq']

/-- **Exercise 10.C.2(b)**: comparative statics of `β/σ`. -/
theorem exercise_10_C_2b_statics {β σ : ℝ} (hβ : 0 < β) (hσ : 0 < σ) :
    HasDerivAt (fun b => b / σ) (1 / σ) β ∧ 0 < 1 / σ ∧
      HasDerivAt (fun s => β / s) (-β / σ ^ 2) σ ∧ -β / σ ^ 2 < 0 := by
  refine ⟨by simpa using (hasDerivAt_id β).div_const σ, by positivity, ?_, ?_⟩
  · have := (hasDerivAt_inv hσ.ne').const_mul β
    convert this using 1
    · ext s; simp [div_eq_mul_inv]
    · field_simp
  · have : 0 < β / σ ^ 2 := by positivity
    rw [neg_div]; linarith

/-- **Exercise 10.D.2** (MWG, p. 346). For the economy of Exercise 10.C.2 the optimal levels
of good `ℓ` (maximize `α + β ln x - σq` subject to `x = q`) are `x = q = β/σ`, the competitive
equilibrium levels. -/
theorem exercise_10_D_2 {α β σ : ℝ} (hβ : 0 < β) (hσ : 0 < σ) {x : ℝ} (hx : 0 < x) :
    (∀ y, 0 < y → α + β * Real.log y - σ * y ≤ α + β * Real.log x - σ * x) ↔ x = β / σ :=
  logConsumer_max hβ hσ hx

/-! ## Exercises 10.C.8 and 10.C.9 -/

/-- **Comparative statics with a cost parameter** (MWG, Exercises 10.C.8-10.C.9). Let `J > 0`
identical firms have marginal cost `MC(q, α)` with partial derivatives `c_qq`, `c_qα`, and let
differentiable paths `p(α)`, `q(α)` satisfy `p = MC(q, α)` and `x(p) = J q` near `α₀`, where
`x'(p) = d`. Then `p'(α₀)(1 - c_qq d/J) = c_qα`. -/
theorem price_response_cost_param {MC : ℝ × ℝ → ℝ} {x p q : ℝ → ℝ} {J cqq cqα d p' q' α₀ : ℝ}
    (hJ : 0 < J)
    (hMC : HasFDerivAt MC (cqq • ContinuousLinearMap.fst ℝ ℝ ℝ +
      cqα • ContinuousLinearMap.snd ℝ ℝ ℝ) (q α₀, α₀))
    (hx : HasDerivAt x d (p α₀)) (hp : HasDerivAt p p' α₀) (hq : HasDerivAt q q' α₀)
    (hfoc : ∀ᶠ α in 𝓝 α₀, p α = MC (q α, α)) (hclear : ∀ᶠ α in 𝓝 α₀, x (p α) = J * q α) :
    p' * (1 - cqq * d / J) = cqα := by
  have h1 := (hasDerivAt_comp_pair hMC hq).congr_of_eventuallyEq
    (by filter_upwards [hfoc] with α h; exact h)
  have e1 := hp.unique h1
  have h2 := (hx.comp α₀ hp).congr_of_eventuallyEq
    (by filter_upwards [hclear] with α h; exact h.symm)
  have e2 := (hq.const_mul J).unique h2
  have hq' : q' = d * p' / J := by rw [eq_div_iff hJ.ne']; linarith
  calc p' * (1 - cqq * d / J) = p' - cqq * (d * p' / J) := by ring
    _ = p' - cqq * q' := by rw [hq']
    _ = cqα := by linarith

/-- **Exercise 10.C.8(a)** (MWG, p. 345). Along the equilibrium path, a firm's profit
`π(α) = p(α)q(α) - c(q(α), α)` changes at rate `dπ/dα = p'(α₀)q(α₀) - c_α` (the envelope
theorem: the effect through `q` vanishes because `p = c_q`). -/
theorem exercise_10_C_8a {c : ℝ × ℝ → ℝ} {p q : ℝ → ℝ} {cq cα p' q' α₀ : ℝ}
    (hc : HasFDerivAt c (cq • ContinuousLinearMap.fst ℝ ℝ ℝ + cα • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (q α₀, α₀))
    (hp : HasDerivAt p p' α₀) (hq : HasDerivAt q q' α₀) (hfoc : p α₀ = cq) :
    HasDerivAt (fun α => p α * q α - c (q α, α)) (p' * q α₀ - cα) α₀ := by
  have h := (hp.mul hq).sub (hasDerivAt_comp_pair hc hq)
  convert h using 1
  rw [hfoc]
  ring

/-- **Exercise 10.C.8(b)** (MWG, p. 345). With `p' = q c_qα/(1 - c_qq x'/J)`... (from
`price_response_cost_param`), `c_qq ≥ 0` and `J > 0`, the profit change
`q c_qα/(1 - c_qq d/J) - c_α` is negative for every demand slope `d ≤ 0` iff
`c_α > q c_qα`, i.e. `∂MC/∂α < ∂AC/∂α = c_α/q`. -/
theorem exercise_10_C_8b {J cqq cqα cα q : ℝ} (hJ : 0 < J) (hcqq : 0 ≤ cqq) (hq : 0 < q)
    (hcα : 0 < cα) :
    (∀ d : ℝ, d ≤ 0 → q * cqα / (1 - cqq * d / J) - cα < 0) ↔ q * cqα < cα := by
  constructor
  · intro h
    have := h 0 le_rfl
    simpa using this
  · intro hlt d hd
    have hD : 1 ≤ 1 - cqq * d / J := by
      have : cqq * d / J ≤ 0 := div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos
        hcqq hd) hJ.le
      linarith
    rcases le_or_gt cqα 0 with hneg | hpos
    · have : q * cqα / (1 - cqq * d / J) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hq.le hneg) (by linarith)
      linarith
    · have : q * cqα / (1 - cqq * d / J) ≤ q * cqα :=
        div_le_self (by positivity) hD
      linarith

/-- **Exercise 10.C.8(b)** (MWG, p. 345), the converse part (corrected): if `q c_qα > c_α`, a
vertical demand (`x' = 0`) makes profits increase with `α`; if `q c_qα = c_α` it leaves them
unchanged to first order (the book's "increase" needs the strict inequality). -/
theorem exercise_10_C_8b_converse {J cqq cqα cα q : ℝ} :
    (cα < q * cqα → 0 < q * cqα / (1 - cqq * 0 / J) - cα) ∧
      (q * cqα = cα → q * cqα / (1 - cqq * 0 / J) - cα = 0) := by
  constructor
  · intro h; simp; linarith
  · intro h; simp [h]

/-- The condition `c_α > q c_qα` is `∂MC/∂α < ∂(c/q)/∂α`. -/
theorem exercise_10_C_8b_AC {cqα cα q : ℝ} (hq : 0 < q) : q * cqα < cα ↔ cqα < cα / q := by
  rw [lt_div_iff₀ hq, mul_comm]

/-- **Exercise 10.C.8(c)** (MWG, p. 346). When `α = w_k`, Shephard's lemma (Chapter 5,
Proposition 5.C.2(vi)) gives `c_α = z_k(w, q)` and `c_qα = ∂z_k/∂q`; the condition becomes
`z_k > q ∂z_k/∂q`: the output elasticity of the conditional demand for factor `k` is below one. -/
theorem exercise_10_C_8c {zk dzk q : ℝ} (hz : 0 < zk) :
    q * dzk < zk ↔ q * dzk / zk < 1 := by
  rw [div_lt_one hz]

/-- **Exercise 10.C.9** (MWG, p. 346). With `J` identical firms (`c_qq ≥ 0`) and demand slope
`x' ≤ 0`, the equilibrium price response to `w_k` is `p' = c_qk/(1 - c_qq x'/J)`; by Shephard's
lemma `c_qk = ∂z_k/∂q`. Hence `p' < 0` iff factor `k` is inferior (`∂z_k/∂q < 0`). -/
theorem exercise_10_C_9 {J cqq dzk d p' : ℝ} (hJ : 0 < J) (hcqq : 0 ≤ cqq) (hd : d ≤ 0)
    (hp : p' * (1 - cqq * d / J) = dzk) : p' < 0 ↔ dzk < 0 := by
  have hD : 0 < 1 - cqq * d / J := by
    have : cqq * d / J ≤ 0 := div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos
      hcqq hd) hJ.le
    linarith
  rw [← hp]
  constructor
  · intro h; exact mul_neg_of_neg_of_pos h hD
  · intro h; by_contra hge; push Not at hge; nlinarith

/-! ## Exercise 10.C.10 -/

/-- **Exercise 10.C.10** (MWG, p. 346). With demand `x(p) = αp^ε` and marginal cost
`c'(q) = βq^η` for each of `J` firms (`α, β, η > 0`, `ε < 0`), the equilibrium conditions
`p = βq^η`, `αp^ε = Jq` are, in logarithms, linear; their unique solution is
`ln p = (ln J - ln α - (1/η) ln β)/(ε - 1/η)`, `ln q = (ln p - ln β)/η`. -/
theorem exercise_10_C_10 {α β η ε J p q : ℝ} (hα : 0 < α) (hβ : 0 < β) (hη : 0 < η)
    (hε : ε < 0) (hJ : 0 < J) (hp : 0 < p) (hq : 0 < q) :
    (p = β * q ^ η ∧ α * p ^ ε = J * q) ↔
      (Real.log p = (Real.log J - Real.log α - Real.log β / η) / (ε - 1 / η) ∧
        Real.log q = (Real.log p - Real.log β) / η) := by
  have hden : ε - 1 / η ≠ 0 := by have : 0 < 1 / η := by positivity
                                  linarith
  have hlogs : (p = β * q ^ η ↔ Real.log p = Real.log β + η * Real.log q) ∧
      (α * p ^ ε = J * q ↔ Real.log α + ε * Real.log p = Real.log J + Real.log q) := by
    constructor
    · constructor
      · intro h; rw [h, Real.log_mul hβ.ne' (Real.rpow_pos_of_pos hq η).ne', Real.log_rpow hq]
      · intro h
        apply Real.log_injOn_pos (Set.mem_Ioi.2 hp)
          (Set.mem_Ioi.2 (mul_pos hβ (Real.rpow_pos_of_pos hq η)))
        rw [h, Real.log_mul hβ.ne' (Real.rpow_pos_of_pos hq η).ne', Real.log_rpow hq]
    · constructor
      · intro h
        have := congrArg Real.log h
        rwa [Real.log_mul hα.ne' (Real.rpow_pos_of_pos hp ε).ne', Real.log_rpow hp,
          Real.log_mul hJ.ne' hq.ne'] at this
      · intro h
        apply Real.log_injOn_pos (Set.mem_Ioi.2 (mul_pos hα (Real.rpow_pos_of_pos hp ε)))
          (Set.mem_Ioi.2 (mul_pos hJ hq))
        rw [Real.log_mul hα.ne' (Real.rpow_pos_of_pos hp ε).ne', Real.log_rpow hp,
          Real.log_mul hJ.ne' hq.ne', h]
  rw [hlogs.1, hlogs.2]
  constructor
  · rintro ⟨h1, h2⟩
    have hq' : Real.log q = (Real.log p - Real.log β) / η := by
      rw [eq_div_iff hη.ne']; linarith
    refine ⟨?_, hq'⟩
    rw [eq_div_iff hden]
    rw [hq'] at h2
    field_simp at h2 ⊢
    linarith
  · rintro ⟨h1, h2⟩
    have e1 : Real.log p = Real.log β + η * Real.log q := by
      rw [h2]; field_simp; ring
    refine ⟨e1, ?_⟩
    rw [eq_div_iff hden] at h1
    rw [h2]
    field_simp at h1 ⊢
    linarith

/-- **Exercise 10.C.10** (MWG, p. 346): comparative statics. The elasticities of the
equilibrium price with respect to `α` and `β` are `η/(1 - εη) > 0` and `1/(1 - εη) > 0` (the
coefficients of `ln α`, `ln β` in `ln p`); those of output per firm are `1/(1 - εη) > 0` and
`ε/(1 - εη) < 0`. Both price elasticities shrink as demand becomes more elastic (`ε` more
negative). -/
theorem exercise_10_C_10_statics {η ε : ℝ} (hη : 0 < η) (hε : ε < 0) :
    -1 / (ε - 1 / η) = η / (1 - ε * η) ∧ -(1 / η) / (ε - 1 / η) = 1 / (1 - ε * η) ∧
      0 < η / (1 - ε * η) ∧ 0 < 1 / (1 - ε * η) ∧
      (1 / η) * (-1 / (ε - 1 / η)) = 1 / (1 - ε * η) ∧
      (1 / η) * (-(1 / η) / (ε - 1 / η) - 1) = ε / (1 - ε * η) ∧ ε / (1 - ε * η) < 0 ∧
      ∀ ε', ε' < ε → η / (1 - ε' * η) < η / (1 - ε * η) := by
  have h1 : 0 < 1 - ε * η := by nlinarith
  have hd : ε - 1 / η ≠ 0 := by
    have : 0 < 1 / η := by positivity
    linarith
  have ha : -1 / (ε - 1 / η) = η / (1 - ε * η) := by
    rw [div_eq_div_iff hd h1.ne']; field_simp; ring
  have hb : -(1 / η) / (ε - 1 / η) = 1 / (1 - ε * η) := by
    rw [div_eq_div_iff hd h1.ne']; field_simp; ring
  refine ⟨ha, hb, by positivity, by positivity, ?_, ?_, div_neg_of_neg_of_pos hε h1,
    fun ε' hε' => ?_⟩
  · rw [ha]; field_simp
  · rw [hb, div_sub_one h1.ne', show 1 - (1 - ε * η) = ε * η by ring, ← mul_div_assoc,
      show 1 / η * (ε * η) = ε by field_simp]
  · have h3 : 0 < 1 - ε' * η := by nlinarith
    rw [div_lt_div_iff₀ h3 h1]
    nlinarith [mul_lt_mul_of_pos_right hε' (by positivity : (0 : ℝ) < η ^ 2)]

/-! ## Exercise 10.C.11 -/

/-- **Exercise 10.C.11** (MWG, p. 346). A price-taking firm with cost `c(q, α)` facing price `p`,
whose output `q(α)` satisfies `p = c_q(q(α), α)`, has profit `π(α) = p q(α) - c(q(α), α)` with
`π'(α) = -c_α(q, α)` (envelope theorem). Hence if `α₁` and `α₂` differ marginally, the two firms'
profits differ by `π₁ - π₂ ≈ -c_α (α₁ - α₂)`. -/
theorem exercise_10_C_11 {c : ℝ × ℝ → ℝ} {q : ℝ → ℝ} {p cα q' α₀ : ℝ}
    (hc : HasFDerivAt c (p • ContinuousLinearMap.fst ℝ ℝ ℝ + cα • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (q α₀, α₀))
    (hq : HasDerivAt q q' α₀) :
    HasDerivAt (fun α => p * q α - c (q α, α)) (-cα) α₀ := by
  have h := (hq.const_mul p).sub (hasDerivAt_comp_pair hc hq)
  convert h using 1
  ring

end MWG.CompetitiveMarkets
