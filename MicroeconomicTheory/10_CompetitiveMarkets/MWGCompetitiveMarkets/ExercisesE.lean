/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGCompetitiveMarkets.ExercisesC

/-!
# Exercises 10.E.1 and 10.E.3; the representative-consumer remarks of Section 10.E

* Small type, pp. 333-334: for a quasilinear consumer the indirect utility is
  `v(p, w) = w + [φ(x(p)) - p x(p)]`, so the compensating and the equivalent variations of a
  price change coincide and equal the change in consumer surplus.
* **Exercise 10.E.1** (tariffs): domestic Marshallian surplus `W(τ)` changes at rate
  `τ Q_f' - s' Q_f`; (a) with strictly convex foreign costs the foreign price falls with a tariff
  and a small tariff raises domestic welfare; (b) with constant-returns foreign costs a small
  tariff lowers it.
* **Exercise 10.E.3** (Ramsey taxes): (a) tax vectors with the same effective prices raise the
  same revenue, so good 1 can be left untaxed; (b) the marginal deadweight loss of a tax on good
  `ℓ` is `-t x'`, and the Lagrange conditions give the inverse elasticity rule
  `t_ℓ/(c_ℓ + t_ℓ) = (λ/(1 + λ))/|ε_ℓ|`; (c) equal rates iff equal elasticities, higher rates on
  less elastic goods, and a tax on good 1 alone is a uniform proportional tax on all goods.
-/

namespace MWG.CompetitiveMarkets

open Filter Topology MeasureTheory

/-! ## Quasilinear indirect utility (pp. 333-334) -/

/-- **(MWG, pp. 333-334)** The indirect utility of a quasilinear consumer (consumption set
`ℝ × ℝ₊`) at price `p > 0` and wealth `w` is `w + [φ(x(p)) - p x(p)]`. -/
theorem ql_indirect_utility (C : QLConsumer) {p : ℝ} (hp : 0 < p) (w : ℝ) :
    IsGreatest {u | ∃ m x : ℝ, 0 ≤ x ∧ m + p * x ≤ w ∧ u = m + C.φ x}
      (w + (C.φ (C.demand p) - p * C.demand p)) := by
  refine ⟨⟨w - p * C.demand p, C.demand p, C.demand_nonneg hp, by linarith, by ring⟩, ?_⟩
  rintro u ⟨m, x, hx, hb, rfl⟩
  have := C.demand_max hp x hx
  linarith

/-- **(MWG, p. 334)** For a quasilinear consumer, the compensating and equivalent variations of a
price change from `p₀` to `p₁` coincide and equal the change in consumer surplus
`[φ(x(p₁)) - p₁x(p₁)] - [φ(x(p₀)) - p₀x(p₀)]`: with this transfer, utility at `p₁` equals utility
at `p₀` without it, at every wealth level. -/
theorem ql_cv_eq_ev (C : QLConsumer) (p₀ p₁ w : ℝ) :
    let v : ℝ → ℝ → ℝ := fun p w => w + (C.φ (C.demand p) - p * C.demand p)
    let Δ := (C.φ (C.demand p₁) - p₁ * C.demand p₁) - (C.φ (C.demand p₀) - p₀ * C.demand p₀)
    v p₁ (w - Δ) = v p₀ w ∧ v p₀ (w + Δ) = v p₁ w := by
  intro v Δ
  constructor <;> simp only [v, Δ] <;> ring

/-! ## A two-path chain rule -/

/-- The chain rule for `t ↦ f(g₁(t), g₂(t))` with partial derivatives `a`, `b`. -/
theorem hasDerivAt_comp_two {f : ℝ × ℝ → ℝ} {a b : ℝ} {g₁ g₂ : ℝ → ℝ} {g₁' g₂' t₀ : ℝ}
    (hf : HasFDerivAt f (a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (g₁ t₀, g₂ t₀))
    (h₁ : HasDerivAt g₁ g₁' t₀) (h₂ : HasDerivAt g₂ g₂' t₀) :
    HasDerivAt (fun t => f (g₁ t, g₂ t)) (a * g₁' + b * g₂') t₀ := by
  have h := HasFDerivAt.comp_hasDerivAt (f := fun t => (g₁ t, g₂ t)) t₀ hf (h₁.prodMk h₂)
  simp only [add_apply, smul_apply, ContinuousLinearMap.coe_fst', smul_eq_mul,
    ContinuousLinearMap.coe_snd'] at h
  exact h

/-! ## Exercise 10.E.1 -/

/-- **Exercise 10.E.1** (MWG, p. 346). Domestic Marshallian surplus with an import tariff `τ`:
`W(τ) = B(X(τ)) - C_d(Q_d(τ)) - s(τ) Q_f(τ)` (domestic consumers' gross benefit, minus domestic
costs, minus payments to foreign firms at their price `s = p - τ`; tariff revenue stays at home),
with `X = Q_d + Q_f`. If consumers and domestic firms are price takers (`B' = C_d' = p`), then
`W'(τ) = τ Q_f'(τ) - s'(τ) Q_f(τ)`. -/
theorem exercise_10_E_1_deriv {B Cd Qd Qf s : ℝ → ℝ} {τ₀ p Qd' Qf' s' : ℝ}
    (hB : HasDerivAt B p (Qd τ₀ + Qf τ₀)) (hC : HasDerivAt Cd p (Qd τ₀))
    (hQd : HasDerivAt Qd Qd' τ₀) (hQf : HasDerivAt Qf Qf' τ₀) (hs : HasDerivAt s s' τ₀)
    (hsp : s τ₀ = p - τ₀) :
    HasDerivAt (fun τ => B (Qd τ + Qf τ) - Cd (Qd τ) - s τ * Qf τ)
      (τ₀ * Qf' - s' * Qf τ₀) τ₀ := by
  have h := ((hB.comp τ₀ (hQd.add hQf)).sub (hC.comp τ₀ hQd)).sub (hs.mul hQf)
  exact h.congr_deriv (by rw [hsp]; ring)

/-- **Exercise 10.E.1** (MWG, p. 346), the foreign price. Differentiating market clearing
`x(s + τ) = q_d(s + τ) + q_f(s)` gives `s'(τ) = -(x' - q_d')/(x' - q_d' - q_f')`; with
`x' ≤ q_d'`... more precisely `x' - q_d' < 0` and a strictly increasing foreign supply
(`q_f' > 0`, strictly convex foreign costs), `-1 < s' < 0`. -/
theorem exercise_10_E_1_foreign_price {x' qd' qf' s' : ℝ} (hd : x' - qd' < 0) (hf : 0 < qf')
    (hclear : x' * (s' + 1) = qd' * (s' + 1) + qf' * s') :
    s' = -(x' - qd') / (x' - qd' - qf') ∧ -1 < s' ∧ s' < 0 := by
  have hden : x' - qd' - qf' < 0 := by linarith
  have hs : s' = -(x' - qd') / (x' - qd' - qf') := by
    rw [eq_div_iff hden.ne]; linarith
  refine ⟨hs, ?_, ?_⟩
  · rw [hs, lt_div_iff_of_neg hden]; linarith
  · rw [hs]; exact div_neg_of_pos_of_neg (by linarith) hden

/-- **Exercise 10.E.1(a)** (MWG, p. 346). With strictly convex foreign costs (`s'(0) < 0`) and
positive imports, `W'(0) = -s'(0)Q_f(0) > 0`, so a small tariff raises domestic welfare. -/
theorem exercise_10_E_1a {W : ℝ → ℝ} {s' Qf0 Qf' : ℝ}
    (hW : HasDerivAt W (0 * Qf' - s' * Qf0) 0) (hs : s' < 0) (hQ : 0 < Qf0) :
    ∃ δ > 0, ∀ τ, 0 < τ → τ < δ → W 0 < W τ := by
  have hpos : 0 < 0 * Qf' - s' * Qf0 := by nlinarith
  have hsl := hW.tendsto_slope_zero_right
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t⁻¹ • (W (0 + t) - W 0) :=
    hsl.eventually (lt_mem_nhds hpos)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hev)
  refine ⟨δ, hδ, fun τ hτ hτδ => ?_⟩
  have := hball (by simpa [Real.dist_eq, abs_of_pos hτ] using hτδ) hτ
  simp only [zero_add, smul_eq_mul] at this
  have := (mul_pos_iff_of_pos_left (inv_pos.2 hτ)).1 this
  linarith

/-- **Exercise 10.E.1(b)** (MWG, p. 346). With constant-returns foreign costs the foreign price is
fixed (`s' = 0`), so `W'(τ) = τ Q_f'(τ)`; if imports fall with the tariff (`Q_f' < 0`) on
`(0, δ)`, then a small tariff lowers domestic welfare: `W(τ) < W(0)` for `0 < τ ≤ δ`. -/
theorem exercise_10_E_1b {W Qf' : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hW : ∀ τ ∈ Set.Icc 0 δ, HasDerivAt W (τ * Qf' τ - 0 * 1) τ)
    (hQ : ∀ τ ∈ Set.Ioo 0 δ, Qf' τ < 0) : ∀ τ, 0 < τ → τ ≤ δ → W τ < W 0 := by
  have hanti : StrictAntiOn W (Set.Icc 0 δ) := by
    refine strictAntiOn_of_hasDerivWithinAt_neg (f' := fun τ => τ * Qf' τ - 0 * 1)
      (convex_Icc 0 δ)
      (fun τ hτ => (hW τ hτ).continuousAt.continuousWithinAt) (fun τ hτ => ?_) (fun τ hτ => ?_)
    · rw [interior_Icc] at hτ
      exact (hW τ (Set.Ioo_subset_Icc_self hτ)).hasDerivWithinAt
    · rw [interior_Icc] at hτ
      have := hQ τ hτ
      nlinarith [hτ.1]
  intro τ hτ hτδ
  exact hanti ⟨le_rfl, hδ.le⟩ ⟨hτ.le, hτδ⟩ hτ

/-! ## Exercise 10.E.3: Ramsey taxes -/

/-- **Exercise 10.E.3(a)** (MWG, p. 347). Effective prices `(1 + t₁)(c_ℓ + t_ℓ)` (in units of
good 1) determine demands and revenue `R = ∑ [(1 + t₁)(c_ℓ + t_ℓ) - c_ℓ] x_ℓ`. If
`c_ℓ + t'_ℓ = a(c_ℓ + t_ℓ)` and `1 + t'₁ = (1/a)(1 + t₁)` (`a > 0`), effective prices, demands and
revenue coincide. In particular `a = 1 + t₁` gives an equivalent tax vector with `t'₁ = 0`. -/
theorem exercise_10_E_3a {n : ℕ} (x : Fin n → ℝ → ℝ) (c t t' : Fin n → ℝ) (t₁ t₁' a : ℝ)
    (ha : 0 < a) (ht : ∀ l, c l + t' l = a * (c l + t l)) (ht₁ : 1 + t₁' = (1 / a) * (1 + t₁)) :
    (∀ l, (1 + t₁') * (c l + t' l) = (1 + t₁) * (c l + t l)) ∧
      ∑ l, ((1 + t₁') * (c l + t' l) - c l) * x l ((1 + t₁') * (c l + t' l)) =
        ∑ l, ((1 + t₁) * (c l + t l) - c l) * x l ((1 + t₁) * (c l + t l)) := by
  have he : ∀ l, (1 + t₁') * (c l + t' l) = (1 + t₁) * (c l + t l) := fun l => by
    rw [ht, ht₁]; field_simp
  exact ⟨he, Finset.sum_congr rfl fun l _ => by rw [he]⟩

/-- **Exercise 10.E.3(a)**: normalization `t'₁ = 0` with `t'_ℓ = (1 + t₁)(c_ℓ + t_ℓ) - c_ℓ`. -/
theorem exercise_10_E_3a_normalize {n : ℕ} (c t : Fin n → ℝ) {t₁ : ℝ} (ht₁ : -1 < t₁) :
    (∀ l, c l + ((1 + t₁) * (c l + t l) - c l) = (1 + t₁) * (c l + t l)) ∧
      1 + 0 = (1 / (1 + t₁)) * (1 + t₁) := by
  refine ⟨fun l => by ring, ?_⟩
  have : 1 + t₁ ≠ 0 := by linarith
  rw [one_div, inv_mul_cancel₀ this]; ring

/-- **Exercise 10.E.3(b)** (MWG, p. 347): the marginal deadweight loss. With `t₁ = 0`,
consumer price `c + t` and continuous demand `x` differentiable at `c + t`, the deadweight loss
`D(t) = ∫_c^{c+t} x - t x(c + t)` of the tax on one good (loss of consumer surplus minus
revenue; constant returns, so no producer surplus) has `D'(t) = -t x'(c + t)`, and revenue
`t x(c + t)` has derivative `x(c + t) + t x'(c + t)`. -/
theorem exercise_10_E_3b_marginal {x : ℝ → ℝ} {c t d : ℝ} (hx : Continuous x)
    (hd : HasDerivAt x d (c + t)) :
    HasDerivAt (fun t => (∫ s in c..c + t, x s) - t * x (c + t)) (-t * d) t ∧
      HasDerivAt (fun t => t * x (c + t)) (x (c + t) + t * d) t := by
  have hshift : HasDerivAt (fun t : ℝ => c + t) 1 t := by
    simpa using (hasDerivAt_id t).const_add c
  have hI : HasDerivAt (fun t => ∫ s in c..c + t, x s) (x (c + t)) t := by
    have h := ((hx.integral_hasStrictDerivAt c (c + t)).hasDerivAt).comp t hshift
    rw [mul_one] at h
    exact h
  have hxc : HasDerivAt (fun t => x (c + t)) d t := by
    have h := hd.comp t hshift
    rw [mul_one] at h
    exact h
  have hR : HasDerivAt (fun t => t * x (c + t)) (x (c + t) + t * d) t := by
    have h := (hasDerivAt_id t).mul hxc
    exact h.congr_deriv (by simp)
  refine ⟨?_, hR⟩
  convert hI.sub hR using 1
  ring

/-- **Exercise 10.E.3(b)** (MWG, p. 347): the Ramsey (inverse elasticity) rule. If at the optimal
taxes the Lagrange condition `D'_ℓ = λ R'_ℓ` holds, i.e. `-t_ℓ x_ℓ' = λ(x_ℓ + t_ℓ x_ℓ')`, with
`x_ℓ > 0`, `x_ℓ' < 0` and `λ ≠ -1`, then
`t_ℓ/p_ℓ = (λ/(1 + λ)) · (1/|ε_ℓ|)` with `p_ℓ = c_ℓ + t_ℓ > 0` and `ε_ℓ = p_ℓ x_ℓ'/x_ℓ`. -/
theorem exercise_10_E_3b {t p xl dxl lam : ℝ} (hp : 0 < p) (hx : 0 < xl) (hd : dxl < 0)
    (hlam : 1 + lam ≠ 0) (hfoc : -t * dxl = lam * (xl + t * dxl)) :
    t / p = lam / (1 + lam) * (1 / |p * dxl / xl|) := by
  have hε : p * dxl / xl < 0 := div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hp hd) hx
  rw [abs_of_neg hε]
  have h1 : (1 + lam) ≠ 0 := hlam
  have h2 : dxl ≠ 0 := hd.ne
  have ht : t = -lam * xl / ((1 + lam) * dxl) := by
    rw [eq_div_iff (mul_ne_zero h1 h2)]; linarith
  rw [ht]
  field_simp

/-- **Exercise 10.E.3(c)** (MWG, p. 347). By the Ramsey rule the optimal proportional rate
`t_ℓ/p_ℓ = k/|ε_ℓ|` (`k = λ/(1+λ) > 0`) is the same for two goods iff their elasticities are
equal, and is higher for the less elastic good. -/
theorem exercise_10_E_3c {k e₁ e₂ : ℝ} (hk : 0 < k) (h₁ : 0 < e₁) :
    (k * (1 / e₁) = k * (1 / e₂) ↔ e₁ = e₂) ∧ (e₁ < e₂ → k * (1 / e₂) < k * (1 / e₁)) := by
  refine ⟨⟨fun h => ?_, fun h => by rw [h]⟩, fun h => ?_⟩
  · have := mul_left_cancel₀ hk.ne' h
    rw [one_div, one_div, inv_inj] at this
    exact this
  · exact mul_lt_mul_of_pos_left (one_div_lt_one_div_of_lt h₁ h) hk

/-- **Exercise 10.E.3(c)** (MWG, p. 347). Taxing only good 1 (`t₁ > 0`, `t_ℓ = 0`) is, by part (a),
equivalent to taxing every good `ℓ ≠ 1` at the uniform proportional rate `t₁/(1 + t₁)` of its
consumer price; by the Ramsey rule it is optimal only if all elasticities are equal at the
optimum. -/
theorem exercise_10_E_3c_good_one {n : ℕ} (c : Fin n → ℝ) (hc : ∀ l, 0 < c l) {t₁ : ℝ}
    (ht₁ : 0 < t₁) (l : Fin n) :
    ((1 + t₁) * (c l + 0) - c l) / ((1 + t₁) * (c l + 0)) = t₁ / (1 + t₁) := by
  have := hc l
  field_simp
  ring

end MWG.CompetitiveMarkets
