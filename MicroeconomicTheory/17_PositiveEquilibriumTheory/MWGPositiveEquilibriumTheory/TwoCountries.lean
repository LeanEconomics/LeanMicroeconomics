/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.IndexSemidefinite

/-!
# Example 17.F.3 computed (MWG Exercise 17.F.13, pp. 615, 646)

Two one-consumer countries; country 1 owns one unit of good 1 (its home good), country 2 one
unit of good 2; `u₁(x) = x₁ - x₂^ρ`, `u₂(x) = x₂ - x₁^ρ`, `-1 < ρ < 0`, on the consumption sets
`{x_H ≥ 0, x_F > 0}` (`tcEconomy`; `x_F^ρ → ∞` as `x_F → 0`).

* **The demand computation** (`exercise_17_F_13_demand`): with `q = -ρ`, `σ = 1/(ρ - 1)` and
  `X(r) = (r/q)^σ` (`tcX`), a consumer facing the relative price `r = p_F/p_H` of the foreign
  good demands `x_F = X(r)` and spends the rest on the home good, whenever this is affordable
  (`p_F X(r) ≤` wealth). The proof is the tangent inequality for `t ↦ t^ρ` (`tc_tangent`, from
  Bernoulli's inequality) and the first-order condition `-ρ X(r)^{ρ-1} = r` (`tcX_foc`).
* **The symmetric equilibrium** `p = (1, 1)` (`exercise_17_F_13_eqm`): each country consumes
  `1 - κ` of its home good and `κ = q^{-σ} < 1` of the foreign good.
* **Its index** (`exercise_17_F_13_index`): near `p = (1, 1)`, `z₁(t, 1) = X(t) - X(1/t)/t`, with
  slope `κ(1 + 2σ) < 0` at `t = 1` (`σ < -1/2` because `ρ > -1`); the equilibrium is regular
  with index `+1`. As `p₁` rises, country 1's demand for good 1 does rise (at the rate
  `κ(1 + σ) > 0`), but by less than country 2's demand falls (rate `κσ`).
  So, for every `ρ ∈ (-1, 0)`, the "wealth effects biased toward the home good" of p. 615 are
  not strong enough and the index is `+1`, not negative (corrections 34); the index argument
  itself is `example_17_F_3_index`, with an index `-1` instance in `ex17F3_index`.
-/

namespace MWG.PositiveEquilibriumTheory

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.GeneralEquilibriumExamples Filter Topology

/-! ### The tangent inequality and the first-order condition -/

/-- The tangent inequality for `t ↦ t^ρ`, `-1 < ρ < 0`: `c^ρ + ρc^{ρ-1}(x - c) ≤ x^ρ` for
`x, c > 0`, strictly for `x ≠ c`. -/
theorem tc_tangent {ρ c x : ℝ} (hρ1 : -1 < ρ) (hρ0 : ρ < 0) (hc : 0 < c) (hx : 0 < x) :
    c ^ ρ + ρ * c ^ (ρ - 1) * (x - c) ≤ x ^ ρ ∧
      (x ≠ c → c ^ ρ + ρ * c ^ (ρ - 1) * (x - c) < x ^ ρ) := by
  set a := x / c with ha
  have ha0 : 0 < a := div_pos hx hc
  have hxa : x = c * a := by rw [ha]; field_simp
  have hcρ : 0 < c ^ ρ := Real.rpow_pos_of_pos hc ρ
  have hsub : c ^ (ρ - 1) = c ^ ρ / c := Real.rpow_sub_one hc.ne' ρ
  have hxρ : x ^ ρ = c ^ ρ * a ^ ρ := by rw [hxa, Real.mul_rpow hc.le ha0.le]
  have hlhs : c ^ ρ + ρ * c ^ (ρ - 1) * (x - c) = c ^ ρ * (1 + ρ * (a - 1)) := by
    rw [hsub, hxa]; field_simp
  -- `a^ρ ≥ 1 + ρ(a - 1)`, strictly for `a ≠ 1`
  have key : ∀ s : ℝ, -1 < s → (1 + s) ^ ρ = ((1 + s) ^ (-ρ))⁻¹ := fun s hs => by
    rw [Real.rpow_neg (by linarith), inv_inv]
  have hweak : 1 + ρ * (a - 1) ≤ a ^ ρ := by
    have hs : -1 < a - 1 := by linarith
    rcases eq_or_ne (a - 1) 0 with h0 | h0
    · have : a = 1 := by linarith
      simp [this]
    have hb := rpow_one_add_lt_one_add_mul_self hs.le h0 (p := -ρ) (by linarith)
      (by linarith)
    have hbpos : 0 < (1 + (a - 1)) ^ (-ρ) := Real.rpow_pos_of_pos (by linarith) _
    have e := key (a - 1) hs
    rw [show 1 + (a - 1) = a by ring] at e hb hbpos
    rw [e]
    rcases le_or_gt (1 + ρ * (a - 1)) 0 with hneg | hpos
    · exact hneg.trans (inv_pos.2 hbpos).le
    · rw [le_inv_comm₀ hpos hbpos]
      rw [inv_eq_one_div, le_div_iff₀ hpos]
      nlinarith [sq_nonneg (ρ * (a - 1))]
  have hstrict : a ≠ 1 → 1 + ρ * (a - 1) < a ^ ρ := by
    intro hne
    have hs : -1 < a - 1 := by linarith
    have h0 : a - 1 ≠ 0 := sub_ne_zero.2 hne
    have hb := rpow_one_add_lt_one_add_mul_self hs.le h0 (p := -ρ) (by linarith)
      (by linarith)
    have hbpos : 0 < (1 + (a - 1)) ^ (-ρ) := Real.rpow_pos_of_pos (by linarith) _
    have e := key (a - 1) hs
    rw [show 1 + (a - 1) = a by ring] at e hb hbpos
    rw [e]
    rcases le_or_gt (1 + ρ * (a - 1)) 0 with hneg | hpos
    · exact hneg.trans_lt (inv_pos.2 hbpos)
    · rw [lt_inv_comm₀ hpos hbpos, inv_eq_one_div, lt_div_iff₀ hpos]
      nlinarith [sq_nonneg (ρ * (a - 1))]
  refine ⟨?_, fun hne => ?_⟩
  · rw [hlhs, hxρ]
    exact mul_le_mul_of_nonneg_left hweak hcρ.le
  · have hne' : a ≠ 1 := by
      intro h1; apply hne; rw [hxa, h1, mul_one]
    rw [hlhs, hxρ]
    exact mul_lt_mul_of_pos_left (hstrict hne') hcρ

/-- **Example 17.F.3** (MWG, p. 615). The demand for the foreign good at the relative price `r`:
`X(r) = (r/q)^σ` with `q = -ρ`, `σ = 1/(ρ - 1)`. -/
noncomputable def tcX (ρ r : ℝ) : ℝ := (r / -ρ) ^ (ρ - 1)⁻¹

theorem tcX_pos {ρ r : ℝ} (hρ0 : ρ < 0) (hr : 0 < r) : 0 < tcX ρ r :=
  Real.rpow_pos_of_pos (div_pos hr (by linarith)) _

/-- The first-order condition `ρ X(r)^{ρ-1} = -r`. -/
theorem tcX_foc {ρ r : ℝ} (hρ0 : ρ < 0) (hr : 0 < r) : ρ * tcX ρ r ^ (ρ - 1) = -r := by
  have hq : 0 < -ρ := by linarith
  have hρ : ρ ≠ 0 := hρ0.ne
  rw [tcX, Real.rpow_inv_rpow (div_pos hr hq).le (by linarith)]
  field_simp

/-- **Exercise 17.F.13**, the consumer's problem (MWG, p. 646). A consumer with utility
`x_H - x_F^ρ` (`-1 < ρ < 0`), prices `p_H, p_F > 0`, wealth `w`: with `x* = X(p_F/p_H)`, every
bundle with `x_F > 0` and `p_H x_H + p_F x_F ≤ w` gives at most the utility of
`((w - p_F x*)/p_H, x*)`, with equality only at that bundle. -/
theorem tc_optimal {ρ pH pF w : ℝ} (hρ1 : -1 < ρ) (hρ0 : ρ < 0) (hpH : 0 < pH) (hpF : 0 < pF)
    {xH xF : ℝ} (hxF : 0 < xF) (hb : pH * xH + pF * xF ≤ w) :
    xH - xF ^ ρ ≤ (w - pF * tcX ρ (pF / pH)) / pH - tcX ρ (pF / pH) ^ ρ ∧
      (xH - xF ^ ρ = (w - pF * tcX ρ (pF / pH)) / pH - tcX ρ (pF / pH) ^ ρ →
        xF = tcX ρ (pF / pH) ∧ xH = (w - pF * tcX ρ (pF / pH)) / pH) := by
  set c := tcX ρ (pF / pH) with hc
  have hr : 0 < pF / pH := div_pos hpF hpH
  have hc0 : 0 < c := tcX_pos hρ0 hr
  have hfoc : ρ * c ^ (ρ - 1) = -(pF / pH) := tcX_foc hρ0 hr
  obtain ⟨htan, htan'⟩ := tc_tangent hρ1 hρ0 hc0 hxF
  rw [hfoc] at htan htan'
  have hxH : xH ≤ (w - pF * xF) / pH := by rw [le_div_iff₀ hpH]; linarith
  have hsplit : (w - pF * xF) / pH = (w - pF * c) / pH - pF / pH * (xF - c) := by
    field_simp; ring
  refine ⟨by linarith, fun heq => ?_⟩
  have hxFc : xF = c := by
    by_contra hne
    have := htan' hne
    linarith
  refine ⟨hxFc, ?_⟩
  rw [hxFc] at heq
  linarith

/-! ### The economy -/

/-- **Example 17.F.3** (MWG, p. 615). The two-country economy: good `0` is country 1's home good,
good `1` country 2's; `u₁ = x₁ - x₂^ρ` on `{x₁ ≥ 0, x₂ > 0}`, `u₂ = x₂ - x₁^ρ` on
`{x₁ > 0, x₂ ≥ 0}`; endowments `(1, 0)` and `(0, 1)`. -/
noncomputable def tcEconomy (ρ : ℝ) : ExchangeEconomy (Fin 2) 2 where
  X := ![{x | 0 ≤ x 0 ∧ 0 < x 1}, {x | 0 < x 0 ∧ 0 ≤ x 1}]
  u := ![fun x => x 0 - x 1 ^ ρ, fun x => x 1 - x 0 ^ ρ]
  ω := ![![1, 0], ![0, 1]]

/-- **Exercise 17.F.13**, the demand computation (MWG, p. 646). At `p ≫ 0`, country 1 demands
`X(p₂/p₁)` of the foreign good and `1 - (p₂/p₁)X(p₂/p₁)` of its home good whenever
`p₂X(p₂/p₁) ≤ p₁`; symmetrically for country 2. -/
theorem exercise_17_F_13_demand {ρ : ℝ} (hρ1 : -1 < ρ) (hρ0 : ρ < 0) {p : Fin 2 → ℝ}
    (hp : StrictlyPositive p) :
    (p 1 * tcX ρ (p 1 / p 0) ≤ p 0 → (tcEconomy ρ).demand 0 p =
      {![1 - p 1 / p 0 * tcX ρ (p 1 / p 0), tcX ρ (p 1 / p 0)]}) ∧
    (p 0 * tcX ρ (p 0 / p 1) ≤ p 1 → (tcEconomy ρ).demand 1 p =
      {![tcX ρ (p 0 / p 1), 1 - p 0 / p 1 * tcX ρ (p 0 / p 1)]}) := by
  have hp0 := hp 0
  have hp1 := hp 1
  constructor
  · intro hint
    set c := tcX ρ (p 1 / p 0) with hc
    have hc0 : 0 < c := tcX_pos hρ0 (div_pos hp1 hp0)
    have hw : p ⬝ᵥ (tcEconomy ρ).ω 0 = p 0 := by
      simp [tcEconomy, dotProduct, Fin.sum_univ_two]
    have hx0 : (p 0 - p 1 * c) / p 0 = 1 - p 1 / p 0 * c := by field_simp
    have hxnn : 0 ≤ 1 - p 1 / p 0 * c := by
      rw [← hx0]; exact div_nonneg (by linarith) hp0.le
    have hmem : ![1 - p 1 / p 0 * c, c] ∈ budgetSetOn ((tcEconomy ρ).X 0) p
        (p ⬝ᵥ (tcEconomy ρ).ω 0) := by
      refine ⟨⟨hxnn, hc0⟩, ?_⟩
      rw [hw]
      simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      field_simp
      linarith
    ext y
    simp only [Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨hy, hb⟩, hmax⟩
      have hb' : p 0 * y 0 + p 1 * y 1 ≤ p 0 := by
        rw [hw] at hb; simpa [dotProduct, Fin.sum_univ_two] using hb
      have hopt := tc_optimal hρ1 hρ0 hp0 hp1 hy.2 hb'
      have h2 := hmax _ hmem
      simp only [tcEconomy, Matrix.cons_val_zero, Matrix.cons_val_one] at h2
      rw [← hx0] at h2
      have := hopt.2 (le_antisymm hopt.1 h2)
      funext l
      fin_cases l
      · simp only [Matrix.cons_val_zero, Fin.zero_eta]
        rw [this.2, hx0]
      · exact this.1
    · rintro rfl
      refine ⟨hmem, fun y hy => ?_⟩
      have hb' : p 0 * y 0 + p 1 * y 1 ≤ p 0 := by
        have h2 := hy.2; rw [hw] at h2; simpa [dotProduct, Fin.sum_univ_two] using h2
      have := (tc_optimal hρ1 hρ0 hp0 hp1 hy.1.2 hb').1
      simp only [tcEconomy, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [← hx0]
      exact this
  · intro hint
    set c := tcX ρ (p 0 / p 1) with hc
    have hc0 : 0 < c := tcX_pos hρ0 (div_pos hp0 hp1)
    have hw : p ⬝ᵥ (tcEconomy ρ).ω 1 = p 1 := by
      simp [tcEconomy, dotProduct, Fin.sum_univ_two]
    have hx1 : (p 1 - p 0 * c) / p 1 = 1 - p 0 / p 1 * c := by field_simp
    have hxnn : 0 ≤ 1 - p 0 / p 1 * c := by
      rw [← hx1]; exact div_nonneg (by linarith) hp1.le
    have hmem : ![c, 1 - p 0 / p 1 * c] ∈ budgetSetOn ((tcEconomy ρ).X 1) p
        (p ⬝ᵥ (tcEconomy ρ).ω 1) := by
      refine ⟨⟨hc0, hxnn⟩, ?_⟩
      rw [hw]
      simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      field_simp
      linarith
    ext y
    simp only [Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨hy, hb⟩, hmax⟩
      have hb' : p 1 * y 1 + p 0 * y 0 ≤ p 1 := by
        rw [hw] at hb; simp only [dotProduct, Fin.sum_univ_two] at hb; linarith
      have hopt := tc_optimal hρ1 hρ0 hp1 hp0 hy.1 hb'
      have h2 := hmax _ hmem
      simp only [tcEconomy, Matrix.cons_val_zero, Matrix.cons_val_one] at h2
      rw [← hx1] at h2
      have := hopt.2 (le_antisymm hopt.1 h2)
      funext l
      fin_cases l
      · exact this.1
      · simp only [Matrix.cons_val_one, Fin.mk_one]
        rw [this.2, hx1]
        rfl
    · rintro rfl
      refine ⟨hmem, fun y hy => ?_⟩
      have hb' : p 1 * y 1 + p 0 * y 0 ≤ p 1 := by
        have h2 := hy.2; rw [hw] at h2; simp only [dotProduct, Fin.sum_univ_two] at h2; linarith
      have := (tc_optimal hρ1 hρ0 hp1 hp0 hy.1.1 hb').1
      simp only [tcEconomy, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [← hx1]
      exact this

/-- `κ = X(1) = q^{-σ} < 1`. -/
theorem tcX_one_lt {ρ : ℝ} (hρ1 : -1 < ρ) (hρ0 : ρ < 0) : tcX ρ 1 < 1 := by
  have hq : 1 < 1 / -ρ := by rw [lt_div_iff₀ (by linarith)]; linarith
  have hσ : (ρ - 1)⁻¹ < 0 := inv_lt_zero.2 (by linarith)
  exact Real.rpow_lt_one_of_one_lt_of_neg hq hσ

/-- Near `p = (1, 1)` the excess demand is `z(t, 1) = (X(t) - X(1/t)/t, X(1/t) - tX(t))`. -/
theorem tc_excessDemand_near {ρ : ℝ} (hρ1 : -1 < ρ) (hρ0 : ρ < 0) :
    ∀ᶠ t in 𝓝 (1 : ℝ), 0 < t ∧ excessDemand (tcEconomy ρ) ![t, 1] =
      ![tcX ρ t - t⁻¹ * tcX ρ t⁻¹, tcX ρ t⁻¹ - t * tcX ρ t] := by
  have hκ := tcX_one_lt hρ1 hρ0
  have hq : 0 < -ρ := by linarith
  have hXc : ContinuousAt (tcX ρ) 1 := by
    unfold tcX
    exact ((continuousAt_id.div_const _).rpow_const (Or.inl (by simp; linarith)))
  have hXinv : ContinuousAt (fun t : ℝ => tcX ρ t⁻¹) 1 := by
    have : ContinuousAt (fun t : ℝ => t⁻¹) 1 := continuousAt_inv₀ one_ne_zero
    exact ContinuousAt.comp (g := tcX ρ) (by simpa using hXc) this
  have h1 : ∀ᶠ t in 𝓝 (1 : ℝ), tcX ρ t⁻¹ < t :=
    hXinv.eventually_lt continuousAt_id (by simpa using hκ)
  have h2 : ∀ᶠ t in 𝓝 (1 : ℝ), t * tcX ρ t < 1 :=
    (continuousAt_id.mul hXc).eventually_lt continuousAt_const (by simpa using hκ)
  filter_upwards [h1, h2, lt_mem_nhds zero_lt_one] with t ht1 ht2 ht0
  refine ⟨ht0, ?_⟩
  have hp : StrictlyPositive (![t, 1] : Fin 2 → ℝ) := fun l => by
    fin_cases l <;> simp [ht0]
  obtain ⟨hd0, hd1⟩ := exercise_17_F_13_demand hρ1 hρ0 hp
  have e0 : (![t, 1] : Fin 2 → ℝ) 1 / ![t, 1] 0 = t⁻¹ := by simp
  have e1 : (![t, 1] : Fin 2 → ℝ) 0 / ![t, 1] 1 = t := by simp
  have hd0' := hd0 (by
    rw [e0]; simp only [Matrix.cons_val_one, Matrix.cons_val_zero, one_mul]; exact ht1.le)
  have hd1' := hd1 (by rw [e1]; simpa using ht2.le)
  rw [e0] at hd0'
  rw [e1] at hd1'
  funext l
  rw [excessDemand_apply, Fin.sum_univ_two, demandFn_eq _ hd0', demandFn_eq _ hd1']
  fin_cases l <;> simp [tcEconomy] <;> ring

/-- The slope `d/dt [X(t) - X(1/t)/t]` at `t = 1` is `κ(1 + 2σ)`, `κ = X(1)`, `σ = 1/(ρ - 1)`. -/
theorem tc_hasDerivAt {ρ : ℝ} (hρ0 : ρ < 0) :
    HasDerivAt (fun t : ℝ => tcX ρ t - t⁻¹ * tcX ρ t⁻¹)
      (tcX ρ 1 * (1 + 2 * (ρ - 1)⁻¹)) 1 := by
  have hq : 0 < -ρ := by linarith
  set σ := (ρ - 1)⁻¹ with hσ
  have hX : HasDerivAt (tcX ρ) (σ * tcX ρ 1) 1 := by
    have h := ((hasDerivAt_id (1 : ℝ)).div_const (-ρ)).rpow_const (p := σ)
      (Or.inl (by simp; linarith))
    have hfun : (fun y => (id y / -ρ) ^ σ) = tcX ρ := by funext y; simp [tcX, hσ]
    rw [hfun] at h
    have e1 : tcX ρ 1 = (1 / -ρ) ^ σ := rfl
    have hρ : ρ ≠ 0 := hρ0.ne
    rw [e1]
    convert h using 1
    simp only [id]
    rw [Real.rpow_sub_one (div_pos one_pos hq).ne']
    field_simp
  have hinv : HasDerivAt (fun t : ℝ => t⁻¹) (-1) 1 := by
    simpa using hasDerivAt_inv (one_ne_zero : (1 : ℝ) ≠ 0)
  have hXi : HasDerivAt (fun t : ℝ => tcX ρ t⁻¹) (σ * tcX ρ 1 * -1) 1 := by
    have h1 : HasDerivAt (tcX ρ) (σ * tcX ρ 1) (1 : ℝ)⁻¹ := by simpa using hX
    exact h1.comp (1 : ℝ) hinv
  have hprod := hinv.mul hXi
  have h := hX.sub hprod
  convert h using 1
  simp only [inv_one, one_mul]
  ring

/-- **Exercise 17.F.13** (MWG, p. 646), the symmetric equilibrium. For `-1 < ρ < 0`, `p = (1, 1)`
is an equilibrium: country `i` consumes `1 - κ` of its home good and `κ = X(1) ∈ (0, 1)` of the
foreign good. -/
theorem exercise_17_F_13_eqm {ρ : ℝ} (hρ1 : -1 < ρ) (hρ0 : ρ < 0) :
    IsEqmPrice (excessDemand (tcEconomy ρ)) ![1, 1] ∧
      (tcEconomy ρ).demand 0 ![1, 1] = {![1 - tcX ρ 1, tcX ρ 1]} ∧
      (tcEconomy ρ).demand 1 ![1, 1] = {![tcX ρ 1, 1 - tcX ρ 1]} ∧
      0 < tcX ρ 1 ∧ tcX ρ 1 < 1 := by
  have hκ := tcX_one_lt hρ1 hρ0
  have hκ0 := tcX_pos hρ0 one_pos
  have hp : StrictlyPositive (![1, 1] : Fin 2 → ℝ) := fun l => by fin_cases l <;> simp
  obtain ⟨hd0, hd1⟩ := exercise_17_F_13_demand hρ1 hρ0 hp
  have hd0' := hd0 (by simpa using hκ.le)
  have hd1' := hd1 (by simpa using hκ.le)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, div_one, one_mul] at hd0' hd1'
  refine ⟨⟨hp, ?_⟩, hd0', hd1', hκ0, hκ⟩
  funext l
  rw [excessDemand_apply, Fin.sum_univ_two, demandFn_eq _ hd0', demandFn_eq _ hd1']
  fin_cases l <;> simp [tcEconomy]

/-- **Exercise 17.F.13** (MWG, p. 646), the index of the symmetric equilibrium. For every
`-1 < ρ < 0`, the slope of `z₁(·, 1)` at `p₁ = 1` is `κ(1 + 2σ) < 0`, so `(1, 1)` is a regular
equilibrium of index `+1` (not `-1`: corrections 34). Its two components: country 1's demand for
good 1 rises with `p₁` at the rate `κ(1 + σ) > 0`, country 2's falls at the rate `κσ`, by more. -/
theorem exercise_17_F_13_index {ρ : ℝ} (hρ1 : -1 < ρ) (hρ0 : ρ < 0) :
    IsRegularEqm (excessDemand (tcEconomy ρ)) (vec1 1) ∧
      eqmIndex (excessDemand (tcEconomy ρ)) (vec1 1) = 1 ∧
      slope2 (excessDemand (tcEconomy ρ)) 1 = tcX ρ 1 * (1 + 2 * (ρ - 1)⁻¹) ∧
      tcX ρ 1 * (1 + 2 * (ρ - 1)⁻¹) < 0 ∧
      0 < tcX ρ 1 * (1 + (ρ - 1)⁻¹) ∧ tcX ρ 1 * (1 + (ρ - 1)⁻¹) < -(tcX ρ 1 * (ρ - 1)⁻¹) := by
  set z := excessDemand (tcEconomy ρ) with hz
  set F : ℝ → ℝ := fun t => tcX ρ t - t⁻¹ * tcX ρ t⁻¹ with hF
  have hκ0 := tcX_pos hρ0 one_pos
  have hmul : (ρ - 1)⁻¹ * (ρ - 1) = 1 := inv_mul_cancel₀ (by linarith)
  have hσ1 : (ρ - 1)⁻¹ < -1 / 2 := by
    by_contra h; push Not at h; nlinarith
  have hσ2 : -1 < (ρ - 1)⁻¹ := by
    by_contra h; push Not at h; nlinarith
  have hslope_neg : tcX ρ 1 * (1 + 2 * (ρ - 1)⁻¹) < 0 :=
    mul_neg_of_pos_of_neg hκ0 (by linarith)
  have hev := tc_excessDemand_near hρ1 hρ0
  -- `ẑ` near `vec1 1`
  have hnear : normED z =ᶠ[𝓝 (vec1 1)] fun v _ => F (v 0) := by
    have hc : Continuous fun v : Fin 1 → ℝ => v 0 := continuous_apply 0
    have : Tendsto (fun v : Fin 1 → ℝ => v 0) (𝓝 (vec1 1)) (𝓝 1) := by
      simpa [vec1] using hc.tendsto (vec1 1)
    filter_upwards [this.eventually hev] with v hv
    funext l
    rw [Subsingleton.elim l 0]
    have hnp : normPrice v = ![v 0, 1] := by
      rw [← vec1_apply_zero v, normPrice_vec1]
      rfl
    simp only [normED, truncExcessDemand, hnp, hz, hv.2]
    rfl
  have hFd : HasDerivAt F (tcX ρ 1 * (1 + 2 * (ρ - 1)⁻¹)) 1 := tc_hasDerivAt hρ0
  have hdiff : DifferentiableAt ℝ (normED z) (vec1 1) := by
    have hg : DifferentiableAt ℝ (fun v : Fin 1 → ℝ => fun _ : Fin 1 => F (v 0)) (vec1 1) := by
      have hc : DifferentiableAt ℝ (F ∘ fun v : Fin 1 → ℝ => v 0) (vec1 1) :=
        hFd.differentiableAt.comp (vec1 1) (by fun_prop)
      exact differentiableAt_pi.2 fun _ => hc
    exact hg.congr_of_eventuallyEq hnear
  have hslope : slope2 z 1 = tcX ρ 1 * (1 + 2 * (ρ - 1)⁻¹) := by
    have h := two_goods_hasDerivAt hdiff
    have hloc : (fun s => z ![s, 1] 0) =ᶠ[𝓝 1] F := by
      filter_upwards [hev] with t ht
      rw [hz, ht.2]; rfl
    exact h.unique (hFd.congr_of_eventuallyEq hloc)
  have heqm : IsNormEqm z (vec1 1) := by
    unfold IsNormEqm
    rw [normPrice_vec1]
    exact (exercise_17_F_13_eqm hρ1 hρ0).1
  refine ⟨⟨heqm, hdiff, ?_⟩, ?_, hslope, hslope_neg, mul_pos hκ0 (by linarith), ?_⟩
  · rw [det_eq_slope2, hslope]; exact hslope_neg.ne
  · rw [eqmIndex_two]
    change -itgSgn (slope2 z 1) = 1
    rw [hslope, itgSgn_neg hslope_neg]; rfl
  · nlinarith

end MWG.PositiveEquilibriumTheory
