/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.ExistenceGeneral
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Exercise 17.BB.8: existence with production externalities (MWG, pp. 650-651)

Goods `0, …, n - 1` are produced, good `n` (`Fin.last n`) is labor. Sector `ℓ` has `J_ℓ`
identical firms, firm `j` turning `v_{ℓj}` units of labor into `α_ℓ v_{ℓj}^{β_ℓ}`, with
`α_ℓ = γ_ℓ (∑ⱼ v_{ℓj})^{ρ_ℓ}`; consumers own only labor and equal profit shares.

* (a) `ExtEconomy.IsWalrasEqm`: firms maximize profit taking `α_ℓ` as given, consumers
  maximize utility on their budget sets, markets clear. (The consumption sets are a field of the
  economy, `ℝ^L₊` in the book; the instance of (e) uses `{x₁ > 0, x₂ ≥ 0}` for log utility.)
* (c) `exercise_17_BB_8c_output`: with total sectoral labor `V`, the maximal sectoral output is
  `γ J^{1-β} V^{ρ+β}` (equal split, by concavity of `v ↦ v^β`), so the aggregate production set
  is `{(-V, q) : V ≥ 0, q ≤ γ J^{1-β} V^{ρ+β}}` (`exercise_17_BB_8c_set`); it has increasing,
  constant or decreasing returns to scale as `ρ + β >, =, < 1`
  (`exercise_17_BB_8c_returns`).
* (d) `exercise_17_BB_8d`: for `ρ + β > 1` the aggregate production set is not convex (while
  each firm's set, given `α`, is convex for `β ≤ 1`, `exercise_17_BB_8_firm_convex`); the
  "internalized" sector is a single firm with a nonconvex technology, outside Proposition
  17.BB.2.
* (e) `exercise_17_BB_8e_eqm`, `exercise_17_BB_8e_optimum`, `exercise_17_BB_8e_bias`: for
  `L = 2`, `β = 1`, one consumer with `u = log x₁ + x₂` (quasilinear in labor), one firm,
  the equilibrium uses labor `V = 1` while the social optimum uses `V = 1 + ρ`: with `ρ > 0`
  equilibrium production `γ` falls short of the optimum `γ(1 + ρ)^{1+ρ}`.
* (b) existence: OPEN (see `docs/source-map.md`).
-/

namespace MWG.PositiveEquilibriumTheory

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.Production MWG.WelfareTheorems

/-! ### (a) The model and Walrasian equilibrium -/

/-- **Exercise 17.BB.8** (MWG, p. 650). An economy with production externalities: `n` produced
goods and labor (`Fin.last n`); sector `ℓ` has `J ℓ` firms with technology parameters
`β ℓ, γ ℓ, ρ ℓ`; consumers have consumption sets, utilities and labor endowments. -/
structure ExtEconomy (ι : Type*) (n : ℕ) where
  /-- The number of firms of each sector. -/
  J : Fin n → ℕ
  /-- The exponent `β_ℓ` of labor. -/
  β : Fin n → ℝ
  /-- The scale `γ_ℓ` of the externality. -/
  γ : Fin n → ℝ
  /-- The exponent `ρ_ℓ` of the externality. -/
  ρ : Fin n → ℝ
  /-- Consumption sets. -/
  X : ι → Set (Fin (n + 1) → ℝ)
  /-- Utilities. -/
  u : ι → (Fin (n + 1) → ℝ) → ℝ
  /-- Labor endowments. -/
  ωL : ι → ℝ

variable {ι : Type*} [Fintype ι] {n : ℕ}

/-- **Exercise 17.BB.8** (MWG, p. 650). The productivity `α_ℓ = γ_ℓ (∑ⱼ v_{ℓj})^{ρ_ℓ}`. -/
noncomputable def ExtEconomy.α (E : ExtEconomy ι n) (v : (ℓ : Fin n) → Fin (E.J ℓ) → ℝ)
    (ℓ : Fin n) : ℝ :=
  E.γ ℓ * (∑ j, v ℓ j) ^ E.ρ ℓ

/-- The profit of a firm of sector `ℓ` using labor `w`, at productivity `a`. -/
noncomputable def ExtEconomy.profitAt (E : ExtEconomy ι n) (p : Fin (n + 1) → ℝ) (ℓ : Fin n)
    (a w : ℝ) : ℝ :=
  p ℓ.castSucc * (a * w ^ E.β ℓ) - p (Fin.last n) * w

/-- Total profits. -/
noncomputable def ExtEconomy.totalProfit (E : ExtEconomy ι n) (p : Fin (n + 1) → ℝ)
    (v : (ℓ : Fin n) → Fin (E.J ℓ) → ℝ) : ℝ :=
  ∑ ℓ, ∑ j, E.profitAt p ℓ (E.α v ℓ) (v ℓ j)

/-- **Exercise 17.BB.8(a)** (MWG, p. 650). A Walrasian equilibrium `(p, v, x)`: (i) every firm's
labor `v_{ℓj} ≥ 0` maximizes its profit `p_ℓ α_ℓ w^{β_ℓ} - p_L w` over `w ≥ 0`, taking
`α_ℓ = γ_ℓ (∑ⱼ v_{ℓj})^{ρ_ℓ}` as given; (ii) every consumer maximizes utility on
`{x ∈ Xᵢ : p·x ≤ p_L ω_{Li} + (total profit)/I}` (equal shares); (iii) each produced good's
market clears, `∑ᵢ x_{ℓi} = ∑ⱼ α_ℓ v_{ℓj}^{β_ℓ}`, and so does labor,
`∑ᵢ x_{Li} + ∑_{ℓ,j} v_{ℓj} = ∑ᵢ ω_{Li}`. -/
def ExtEconomy.IsWalrasEqm (E : ExtEconomy ι n) (p : Fin (n + 1) → ℝ)
    (v : (ℓ : Fin n) → Fin (E.J ℓ) → ℝ) (x : ι → Fin (n + 1) → ℝ) : Prop :=
  (∀ ℓ j, 0 ≤ v ℓ j ∧ ∀ w : ℝ, 0 ≤ w →
      E.profitAt p ℓ (E.α v ℓ) w ≤ E.profitAt p ℓ (E.α v ℓ) (v ℓ j)) ∧
    (∀ i, x i ∈ budgetSetOn (E.X i) p
        (p (Fin.last n) * E.ωL i + E.totalProfit p v / Fintype.card ι) ∧
      ∀ x' ∈ budgetSetOn (E.X i) p
        (p (Fin.last n) * E.ωL i + E.totalProfit p v / Fintype.card ι), E.u i x' ≤ E.u i (x i)) ∧
    (∀ ℓ, ∑ i, x i ℓ.castSucc = ∑ j, E.α v ℓ * v ℓ j ^ E.β ℓ) ∧
    ∑ i, x i (Fin.last n) + ∑ ℓ, ∑ j, v ℓ j = ∑ i, E.ωL i

/-! ### (c) The aggregate production set of a sector -/

/-- **Exercise 17.BB.8(c)** (MWG, p. 651). With `J > 0` firms, `0 < β ≤ 1`, `γ, ρ ≥ 0`, labor
`vⱼ ≥ 0` summing to `V`, sectoral output `∑ⱼ γ V^ρ vⱼ^β` is at most `γ J^{1-β} V^{ρ+β}`, with
equality at the equal split `vⱼ = V/J`. -/
theorem exercise_17_BB_8c_output {J : ℕ} (hJ : 0 < J) {β γ ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hγ : 0 ≤ γ) (hρ : 0 ≤ ρ) {v : Fin J → ℝ} (hv : ∀ j, 0 ≤ v j) :
    ∑ j, γ * (∑ k, v k) ^ ρ * v j ^ β ≤
      γ * (J : ℝ) ^ (1 - β) * (∑ k, v k) ^ (ρ + β) ∧
    ∑ _j : Fin J, γ * (∑ k, v k) ^ ρ * ((∑ k, v k) / J) ^ β =
      γ * (J : ℝ) ^ (1 - β) * (∑ k, v k) ^ (ρ + β) := by
  set V := ∑ k, v k with hV
  have hV0 : 0 ≤ V := Finset.sum_nonneg fun k _ => hv k
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  -- `(V/J)^β · J = J^{1-β} V^β`
  have hsplit : (J : ℝ) * (V / J) ^ β = (J : ℝ) ^ (1 - β) * V ^ β := by
    rw [Real.div_rpow hV0 hJr.le, Real.rpow_sub hJr, Real.rpow_one]
    field_simp
  have hpow : V ^ (ρ + β) = V ^ ρ * V ^ β := by
    rcases hV0.lt_or_eq with hVp | hVz
    · exact Real.rpow_add hVp ρ β
    · rw [← hVz, Real.zero_rpow (by linarith : β ≠ 0), mul_zero]
      rcases eq_or_ne (ρ + β) 0 with h | h
      · exfalso
        linarith
      · exact Real.zero_rpow h
  refine ⟨?_, ?_⟩
  · -- Jensen for the concave `t ↦ t^β`
    have hc := (Real.concaveOn_rpow hβ0.le hβ1)
    have hj := hc.le_map_sum (t := Finset.univ) (w := fun _ => (1 : ℝ) / J) (p := v)
      (fun _ _ => by positivity) (by simp [Finset.card_univ]; field_simp)
      (fun j _ => Set.mem_Ici.mpr (hv j))
    simp only [smul_eq_mul] at hj
    rw [← Finset.mul_sum, ← Finset.mul_sum] at hj
    have hsum : ∑ j, v j ^ β ≤ J * (V / J) ^ β := by
      rw [one_div_mul_eq_div] at hj
      have := mul_le_mul_of_nonneg_left hj hJr.le
      rw [mul_div_cancel₀ _ hJr.ne'] at this
      convert this using 2
      rw [hV, one_div_mul_eq_div]
    calc ∑ j, γ * V ^ ρ * v j ^ β = γ * V ^ ρ * ∑ j, v j ^ β := by rw [Finset.mul_sum]
      _ ≤ γ * V ^ ρ * (J * (V / J) ^ β) :=
          mul_le_mul_of_nonneg_left hsum (mul_nonneg hγ (Real.rpow_nonneg hV0 _))
      _ = γ * (J : ℝ) ^ (1 - β) * V ^ (ρ + β) := by rw [hsplit, hpow]; ring
  · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    calc (J : ℝ) * (γ * V ^ ρ * (V / J) ^ β) = γ * V ^ ρ * (J * (V / J) ^ β) := by ring
      _ = γ * (J : ℝ) ^ (1 - β) * V ^ (ρ + β) := by rw [hsplit, hpow]; ring

/-- The aggregate production set of a sector with `J` firms, in (labor, output) coordinates:
all `(-∑ⱼ vⱼ, q)` with `vⱼ ≥ 0` and `q ≤ ∑ⱼ γ (∑ₖ vₖ)^ρ vⱼ^β`. -/
def extSectorSet (J : ℕ) (β γ ρ : ℝ) : Set (Fin 2 → ℝ) :=
  {y | ∃ v : Fin J → ℝ, (∀ j, 0 ≤ v j) ∧ y 0 = -∑ k, v k ∧
    y 1 ≤ ∑ j, γ * (∑ k, v k) ^ ρ * v j ^ β}

/-- **Exercise 17.BB.8(c)** (MWG, p. 651), "derive and represent": the aggregate production set
of a sector is `{(-V, q) : V ≥ 0, q ≤ γ J^{1-β} V^{ρ+β}}`. -/
theorem exercise_17_BB_8c_set {J : ℕ} (hJ : 0 < J) {β γ ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hγ : 0 ≤ γ) (hρ : 0 ≤ ρ) :
    extSectorSet J β γ ρ = {y | y 0 ≤ 0 ∧ y 1 ≤ γ * (J : ℝ) ^ (1 - β) * (-y 0) ^ (ρ + β)} := by
  ext y
  constructor
  · rintro ⟨v, hv, h0, h1⟩
    have hV0 : 0 ≤ ∑ k, v k := Finset.sum_nonneg fun k _ => hv k
    refine ⟨by rw [h0]; linarith, ?_⟩
    rw [h0, neg_neg]
    exact h1.trans (exercise_17_BB_8c_output hJ hβ0 hβ1 hγ hρ hv).1
  · rintro ⟨h0, h1⟩
    have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
    set V := -y 0 with hVdef
    have hV0 : 0 ≤ V := by rw [hVdef]; linarith
    refine ⟨fun _ => V / J, fun _ => div_nonneg hV0 hJr.le, ?_, ?_⟩
    · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
      rw [hVdef]
      ring
    · have hsum : ∑ _k : Fin J, V / J = V := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp
      have h2 := (exercise_17_BB_8c_output hJ hβ0 hβ1 hγ hρ
        (v := fun _ => V / J) fun _ => div_nonneg hV0 hJr.le).2
      simp only [hsum] at h2 ⊢
      rw [h2]
      exact h1

/-- **Exercise 17.BB.8(c)** (MWG, p. 651), returns to scale: the sectoral frontier
`F(V) = c V^{ρ+β}` (`c = γ J^{1-β} > 0`) satisfies `F(tV) = t^{ρ+β} F(V)`; for `t > 1`, `V > 0`
it has increasing returns `F(tV) > tF(V)` iff `ρ + β > 1`, constant returns `F(tV) = tF(V)` iff
`ρ + β = 1`, and decreasing returns `F(tV) < tF(V)` iff `ρ + β < 1`. -/
theorem exercise_17_BB_8c_returns {c e V t : ℝ} (hc : 0 < c) (hV : 0 < V) (ht : 1 < t) :
    c * (t * V) ^ e = t ^ e * (c * V ^ e) ∧
    (t * (c * V ^ e) < c * (t * V) ^ e ↔ 1 < e) ∧
    (c * (t * V) ^ e = t * (c * V ^ e) ↔ e = 1) ∧
    (c * (t * V) ^ e < t * (c * V ^ e) ↔ e < 1) := by
  have hkey : c * (t * V) ^ e = t ^ e * (c * V ^ e) := by
    rw [Real.mul_rpow (by linarith) hV.le]
    ring
  have hA : 0 < c * V ^ e := mul_pos hc (Real.rpow_pos_of_pos hV e)
  have hlt : ∀ x y : ℝ, t ^ x < t ^ y ↔ x < y := fun x y => Real.rpow_lt_rpow_left_iff ht
  have ht1 : t = t ^ (1 : ℝ) := (Real.rpow_one t).symm
  refine ⟨hkey, ?_, ?_, ?_⟩
  · rw [hkey, mul_lt_mul_iff_left₀ hA]
    have h := hlt 1 e
    rwa [Real.rpow_one] at h
  · rw [hkey]
    constructor
    · intro h
      have h' : t ^ e = t ^ (1 : ℝ) := by
        rw [← ht1]
        exact mul_right_cancel₀ hA.ne' h
      rcases lt_trichotomy e 1 with h1 | h1 | h1
      · exact absurd h' ((hlt e 1).mpr h1).ne
      · exact h1
      · exact absurd h' ((hlt 1 e).mpr h1).ne'
    · rintro rfl
      rw [Real.rpow_one]
  · rw [hkey, mul_lt_mul_iff_left₀ hA]
    have h := hlt e 1
    rwa [Real.rpow_one] at h

/-- **Exercise 17.BB.8** (MWG, p. 650). Given `α ≥ 0` and `0 < β ≤ 1`, a firm's production set
`{(-v, q) : v ≥ 0, q ≤ α v^β}` is convex (so the individual firm's problem is convex even
though, by (d), the aggregate technology need not be). -/
theorem exercise_17_BB_8_firm_convex {α β : ℝ} (hα : 0 ≤ α) (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    Convex ℝ {y : Fin 2 → ℝ | y 0 ≤ 0 ∧ y 1 ≤ α * (-y 0) ^ β} := by
  intro y hy z hz a b ha hb hab
  have hc : a • (-y 0) ^ β + b • (-z 0) ^ β ≤ (a • (-y 0) + b • (-z 0)) ^ β :=
    (Real.concaveOn_rpow hβ0.le hβ1).2 (Set.mem_Ici.mpr (by linarith [hy.1]))
      (Set.mem_Ici.mpr (by linarith [hz.1])) ha hb hab
  simp only [smul_eq_mul] at hc
  refine ⟨?_, ?_⟩ <;> simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  · nlinarith [hy.1, hz.1]
  · have e : -(a * y 0 + b * z 0) = a * -y 0 + b * -z 0 := by ring
    rw [e]
    have h1 := mul_le_mul_of_nonneg_left hy.2 ha
    have h2 := mul_le_mul_of_nonneg_left hz.2 hb
    have h3 := mul_le_mul_of_nonneg_left hc hα
    nlinarith

/-- **Exercise 17.BB.8(d)** (MWG, p. 651). If `ρ + β > 1` (with `γ > 0`, `J > 0`,
`0 < β ≤ 1`, `ρ ≥ 0`) the aggregate production set of the sector is not convex: `(0, 0)` and
`(-2, F(2))` belong to it, but their midpoint `(-1, F(2)/2)` does not, since
`F(2)/2 = 2^{ρ+β-1} F(1) > F(1)`. -/
theorem exercise_17_BB_8d {J : ℕ} (hJ : 0 < J) {β γ ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hγ : 0 < γ) (hρ : 0 ≤ ρ) (hirs : 1 < ρ + β) : ¬ Convex ℝ (extSectorSet J β γ ρ) := by
  rw [exercise_17_BB_8c_set hJ hβ0 hβ1 hγ.le hρ]
  intro hconv
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  set c := γ * (J : ℝ) ^ (1 - β) with hc
  have hc0 : 0 < c := mul_pos hγ (Real.rpow_pos_of_pos hJr _)
  have hA : (![0, 0] : Fin 2 → ℝ) ∈ {y : Fin 2 → ℝ | y 0 ≤ 0 ∧ y 1 ≤ c * (-y 0) ^ (ρ + β)} := by
    refine ⟨by simp, ?_⟩
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, neg_zero]
    rw [Real.zero_rpow (by linarith)]
    simp
  have hB : (![-2, c * 2 ^ (ρ + β)] : Fin 2 → ℝ) ∈
      {y : Fin 2 → ℝ | y 0 ≤ 0 ∧ y 1 ≤ c * (-y 0) ^ (ρ + β)} := by
    refine ⟨by simp, ?_⟩
    simp
  have hmid := hconv hA hB (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)
  have h2 := hmid.2
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_one,
    Matrix.cons_val_zero] at h2
  norm_num at h2
  have hpow : (2 : ℝ) < 2 ^ (ρ + β) := by
    conv_lhs => rw [show (2 : ℝ) = 2 ^ (1 : ℝ) from (Real.rpow_one 2).symm]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hirs
  nlinarith

/-! ### (e) Quasilinear preferences: the bias of equilibrium production -/

/-- **Exercise 17.BB.8(e)** (MWG, p. 651). `L = 2`, one sector with one firm, `β = 1`, scale `γ`,
externality exponent `ρ`; one consumer with labor endowment `ω` and the quasilinear utility
`log x₁ + x₂` on `{x₁ > 0, x₂ ≥ 0}`. -/
noncomputable def ex17BB8eEconomy (γ ρ ω : ℝ) : ExtEconomy Unit 1 where
  J := fun _ => 1
  β := fun _ => 1
  γ := fun _ => γ
  ρ := fun _ => ρ
  X := fun _ => {x | 0 < x 0 ∧ 0 ≤ x 1}
  u := fun _ x => Real.log (x 0) + x 1
  ωL := fun _ => ω

/-- **Exercise 17.BB.8(e)** (MWG, p. 651). For `γ > 0` and `ω ≥ 1` the economy has the Walrasian
equilibrium `p = (1/γ, 1)`, labor `V = 1` (so `α = γ`), consumption `x = (γ, ω - 1)`: the firm
makes zero profit at every scale, and the consumer's first-order condition `1/x₁ = p₁/p₂`
holds. -/
theorem exercise_17_BB_8e_eqm {γ ρ ω : ℝ} (hγ : 0 < γ) (hω : 1 ≤ ω) :
    (ex17BB8eEconomy γ ρ ω).IsWalrasEqm ![1 / γ, 1] (fun _ _ => 1) (fun _ => ![γ, ω - 1]) := by
  have hα : (ex17BB8eEconomy γ ρ ω).α (fun _ _ => 1) 0 = γ := by
    change γ * (∑ _j : Fin 1, (1 : ℝ)) ^ ρ = γ
    simp
  have hprofit : ∀ w : ℝ,
      (ex17BB8eEconomy γ ρ ω).profitAt ![1 / γ, 1] 0 γ w = 0 := fun w => by
    simp only [ExtEconomy.profitAt, ex17BB8eEconomy, Real.rpow_one]
    simp
    field_simp
    ring
  have htot : (ex17BB8eEconomy γ ρ ω).totalProfit ![1 / γ, 1] (fun _ _ => 1) = 0 := by
    refine Finset.sum_eq_zero fun ℓ _ => Finset.sum_eq_zero fun j _ => ?_
    have hℓ : ℓ = 0 := Subsingleton.elim _ _
    subst hℓ
    rw [hα]
    exact hprofit _
  have hwealth : (![1 / γ, 1] : Fin 2 → ℝ) (Fin.last 1) * (ex17BB8eEconomy γ ρ ω).ωL () +
      (ex17BB8eEconomy γ ρ ω).totalProfit ![1 / γ, 1] (fun _ _ => 1) /
        Fintype.card Unit = ω := by
    rw [htot]
    simp [ex17BB8eEconomy]
  refine ⟨fun ℓ j => ?_, fun i => ?_, fun ℓ => ?_, ?_⟩
  · have hℓ : ℓ = 0 := Subsingleton.elim _ _
    subst hℓ
    refine ⟨zero_le_one, fun w _ => ?_⟩
    rw [hα, hprofit, hprofit]
  · rw [hwealth]
    refine ⟨⟨⟨by simpa using hγ, by simpa using hω⟩, ?_⟩, fun x' hx' => ?_⟩
    · simp [dotProduct, Fin.sum_univ_two]
      field_simp
      linarith
    · obtain ⟨⟨h0, h1⟩, hcost⟩ := hx'
      replace hcost : γ⁻¹ * x' 0 + x' 1 ≤ ω := by simpa [dotProduct, Fin.sum_univ_succ] using hcost
      simp only [ex17BB8eEconomy, Matrix.cons_val_zero, Matrix.cons_val_one]
      have hl := Real.log_le_sub_one_of_pos (div_pos h0 hγ)
      rw [Real.log_div h0.ne' hγ.ne'] at hl
      have : x' 0 / γ = γ⁻¹ * x' 0 := by ring
      linarith
  · have hℓ : ℓ = 0 := Subsingleton.elim _ _
    subst hℓ
    change (∑ _i : Unit, (![γ, ω - 1] : Fin 2 → ℝ) 0) =
      ∑ _j : Fin 1, (ex17BB8eEconomy γ ρ ω).α (fun _ _ => 1) 0 * (1 : ℝ) ^ (1 : ℝ)
    rw [hα]
    simp
  · change (∑ _i : Unit, (![γ, ω - 1] : Fin 2 → ℝ) 1) + ∑ _ℓ : Fin 1, ∑ _j : Fin 1, (1 : ℝ) =
      ∑ _i : Unit, ω
    simp

/-- **Exercise 17.BB.8(e)** (MWG, p. 651). The social optimum: with the consumer's utility as
welfare, using labor `V > 0` yields `log(γ V^{1+ρ}) + (ω - V)`, which is maximized exactly at
`V = 1 + ρ` (for `γ > 0`, `ρ ≥ 0`). -/
theorem exercise_17_BB_8e_optimum {γ ρ ω : ℝ} (hγ : 0 < γ) (hρ : 0 ≤ ρ) {V : ℝ} (hV : 0 < V) :
    Real.log (γ * V ^ (1 + ρ)) + (ω - V) ≤
      Real.log (γ * (1 + ρ) ^ (1 + ρ)) + (ω - (1 + ρ)) ∧
    (V ≠ 1 + ρ → Real.log (γ * V ^ (1 + ρ)) + (ω - V) <
      Real.log (γ * (1 + ρ) ^ (1 + ρ)) + (ω - (1 + ρ))) := by
  have hc : 0 < 1 + ρ := by linarith
  have e1 : Real.log (γ * V ^ (1 + ρ)) = Real.log γ + (1 + ρ) * Real.log V := by
    rw [Real.log_mul hγ.ne' (Real.rpow_pos_of_pos hV _).ne', Real.log_rpow hV]
  have e2 : Real.log (γ * (1 + ρ) ^ (1 + ρ)) = Real.log γ + (1 + ρ) * Real.log (1 + ρ) := by
    rw [Real.log_mul hγ.ne' (Real.rpow_pos_of_pos hc _).ne', Real.log_rpow hc]
  have e3 : Real.log (V / (1 + ρ)) = Real.log V - Real.log (1 + ρ) :=
    Real.log_div hV.ne' hc.ne'
  have hdiv : (1 + ρ) * (V / (1 + ρ)) = V := by field_simp
  rw [e1, e2]
  refine ⟨?_, fun hne => ?_⟩
  · have hl := Real.log_le_sub_one_of_pos (div_pos hV hc)
    rw [e3] at hl
    nlinarith [mul_le_mul_of_nonneg_left hl hc.le]
  · have hne' : V / (1 + ρ) ≠ 1 := fun h => hne (by field_simp at h; linarith)
    have hl := Real.log_lt_sub_one_of_pos (div_pos hV hc) hne'
    rw [e3] at hl
    nlinarith [mul_lt_mul_of_pos_left hl hc]

/-- **Exercise 17.BB.8(e)** (MWG, p. 651), the bias: with `ρ > 0` the equilibrium (labor `1`,
output `γ`) produces strictly less than the social optimum (labor `1 + ρ`, output
`γ(1 + ρ)^{1+ρ}`) and yields strictly lower welfare; firms neglect the effect of their labor on
`α`, an external economy, so there is underproduction. -/
theorem exercise_17_BB_8e_bias {γ ρ ω : ℝ} (hγ : 0 < γ) (hρ : 0 < ρ) :
    γ * (1 : ℝ) ^ (1 + ρ) < γ * (1 + ρ) ^ (1 + ρ) ∧
    Real.log (γ * (1 : ℝ) ^ (1 + ρ)) + (ω - 1) <
      Real.log (γ * (1 + ρ) ^ (1 + ρ)) + (ω - (1 + ρ)) := by
  refine ⟨?_, (exercise_17_BB_8e_optimum hγ hρ.le one_pos).2 (by linarith)⟩
  rw [Real.one_rpow, mul_one]
  have : (1 : ℝ) < (1 + ρ) ^ (1 + ρ) := Real.one_lt_rpow (by linarith) (by linarith)
  nlinarith

end MWG.PositiveEquilibriumTheory
