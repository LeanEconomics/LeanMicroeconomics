/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.Existence

/-!
# Exercises 17.C.3-17.C.5 (MWG pp. 643-644)

* **Exercise 17.C.3** (taxes on gross consumption, rebated lump sum). The budget set
  `Bᵢ(p, wᵢ)` and the equilibrium with taxes (`IsTaxEqm`). (a) An explicit equilibrium with
  taxes that is not Pareto optimal (`exercise_17_C_3a`). (c), (d): the budget sets with taxes on
  net trades, with equal (`netTaxBudget`) or different (`buySellTaxBudget`) rates for purchases
  and sales; both are convex, and the first is the second with equal rates
  (`exercise_17_C_3c`, `exercise_17_C_3d`).
* **Exercise 17.C.4** (progressive redistribution). The rule (`progressiveWealth`) gives every
  consumer `(wᵢ + w̄)/2`, `w̄` the mean wealth (`progressiveWealth_eq`). (a) With
  `ω₁ = (1, 2)`, `ω₂ = (2, 1)` the after-tax wealths are `(5p₁ + 7p₂)/4` and `(7p₁ + 5p₂)/4`
  (`exercise_17_C_4a`). (b) Yes: the excess demand satisfies (i)-(v) (`exercise_17_C_4b`), so an
  equilibrium exists.
* **Exercise 17.C.5** (household production). The induced preferences `≿*` are complete and
  transitive (`exercise_17_C_5a`), and convex when `Y` is convex and `≿` is convex
  (`exercise_17_C_5b`).
-/

namespace MWG.PositiveEquilibriumTheory

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.GeneralEquilibriumExamples
open Filter Topology

variable {ι : Type*} [Fintype ι] {L : ℕ}

/-! ### Exercise 17.C.3 -/

/-- **Exercise 17.C.3** (MWG, p. 643). The budget set with taxes `tᵢ` on gross consumption:
`Bᵢ(p, wᵢ) = {xᵢ ∈ ℝ^L₊ : ∑ₗ (1 + t_ℓᵢ) p_ℓ x_ℓᵢ ≤ wᵢ}`. -/
def grossTaxBudget (p t : Fin L → ℝ) (w : ℝ) : Set (Fin L → ℝ) :=
  {x | x ∈ nonnegOrthant L ∧ ∑ l, (1 + t l) * p l * x l ≤ w}

/-- **Exercise 17.C.3** (MWG, p. 643). An equilibrium with taxes: `p ≫ 0`, `∑ᵢ xᵢ* = ∑ᵢ ωᵢ`, and
every `xᵢ*` maximizes `uᵢ` on `Bᵢ(p, p·ωᵢ + (1/I) ∑ᵢ' ∑ₗ t_ℓᵢ' p_ℓ x*_ℓᵢ')`. -/
def IsTaxEqm (u : ι → (Fin L → ℝ) → ℝ) (ω : ι → Fin L → ℝ) (t : ι → Fin L → ℝ)
    (p : Fin L → ℝ) (x : ι → Fin L → ℝ) : Prop :=
  p ∈ posOrthant L ∧ ∑ i, x i = ∑ i, ω i ∧
    ∀ i, x i ∈ grossTaxBudget p (t i)
        (p ⬝ᵥ ω i + (1 / Fintype.card ι) * ∑ i', ∑ l, t i' l * p l * x i' l) ∧
      ∀ y ∈ grossTaxBudget p (t i)
        (p ⬝ᵥ ω i + (1 / Fintype.card ι) * ∑ i', ∑ l, t i' l * p l * x i' l),
        u i y ≤ u i (x i)

/-- The tangent-line bound for `√`: `2√a·√y ≤ y + a` for `y ≥ 0`. -/
theorem sqrt_tangent {a y : ℝ} (hy : 0 ≤ y) (ha : 0 ≤ a) :
    2 * Real.sqrt a * Real.sqrt y ≤ y + a := by
  nlinarith [sq_nonneg (Real.sqrt y - Real.sqrt a), Real.sq_sqrt hy, Real.sq_sqrt ha]

/-- The example of Exercise 17.C.3(a): two consumers with `u = √x₁ + √x₂` and `ω = (1, 1)`;
consumer 1 pays a 100% tax on good 1, consumer 2 on good 2. -/
noncomputable def taxExampleT : Fin 2 → Fin 2 → ℝ := ![![1, 0], ![0, 1]]

/-- The equilibrium allocation of the tax example: `x₁ = (2/5, 8/5)`, `x₂ = (8/5, 2/5)`. -/
noncomputable def taxExampleX : Fin 2 → Fin 2 → ℝ := ![![2 / 5, 8 / 5], ![8 / 5, 2 / 5]]

/-- **Exercise 17.C.3(a)** (MWG, p. 643). An equilibrium with taxes need not be Pareto optimal:
in the example, `p = (1, 1)` and `x₁ = (2/5, 8/5)`, `x₂ = (8/5, 2/5)` form an equilibrium with
taxes (the rebate is `2/5`, each wealth `12/5`), but both consumers prefer the endowment
allocation (`u = 2 > 3√(2/5)`). The Edgeworth box illustration is graphical. -/
theorem exercise_17_C_3a :
    IsTaxEqm (fun _ => sqrtUtility 2) (fun _ _ => 1) taxExampleT ![1, 1] taxExampleX ∧
      ¬ (ExchangeEconomy.ofOrthant (fun _ : Fin 2 => sqrtUtility 2) (fun _ _ => 1)).IsParetoOptimal
        taxExampleX := by
  set c := Real.sqrt (2 / 5) with hc
  have hc0 : 0 < c := Real.sqrt_pos.2 (by norm_num)
  have hc2 : c ^ 2 = 2 / 5 := Real.sq_sqrt (by norm_num)
  have h8 : Real.sqrt (8 / 5) = 2 * c := by
    rw [show (8 / 5 : ℝ) = 2 ^ 2 * (2 / 5) by norm_num, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
  have hux : ∀ i, sqrtUtility 2 (taxExampleX i) = 3 * c := fun i => by
    fin_cases i <;> simp [sqrtUtility, taxExampleX, Fin.sum_univ_two, ← hc, h8] <;> ring
  have hrebate : (1 / (Fintype.card (Fin 2) : ℝ)) * ∑ i', ∑ l, taxExampleT i' l *
      (![1, 1] : Fin 2 → ℝ) l * taxExampleX i' l = 2 / 5 := by
    simp [taxExampleT, taxExampleX, Fin.sum_univ_two]
    norm_num
  refine ⟨⟨fun l => by fin_cases l <;> simp, ?_, fun i => ?_⟩, fun hPO => ?_⟩
  · funext l
    fin_cases l <;> simp [taxExampleX, Fin.sum_univ_two] <;> norm_num
  · rw [hrebate]
    have hw : (![1, 1] : Fin 2 → ℝ) ⬝ᵥ (fun _ => (1 : ℝ)) + 2 / 5 = 12 / 5 := by
      simp [dotProduct, Fin.sum_univ_two]
      norm_num
    rw [hw]
    refine ⟨⟨fun l => ?_, ?_⟩, fun y ⟨hy, hb⟩ => ?_⟩
    · fin_cases i <;> fin_cases l <;> simp [taxExampleX] <;> norm_num
    · fin_cases i <;> simp [taxExampleT, taxExampleX, Fin.sum_univ_two] <;> norm_num
    · change sqrtUtility 2 y ≤ sqrtUtility 2 (taxExampleX i)
      rw [hux i]
      have hy0 := hy 0
      have hy1 := hy 1
      have t0 := sqrt_tangent hy0 (show (0 : ℝ) ≤ 2 / 5 by norm_num)
      have t1 := sqrt_tangent hy1 (show (0 : ℝ) ≤ 2 / 5 by norm_num)
      have t0' := sqrt_tangent hy0 (show (0 : ℝ) ≤ 8 / 5 by norm_num)
      have t1' := sqrt_tangent hy1 (show (0 : ℝ) ≤ 8 / 5 by norm_num)
      rw [← hc] at t0 t1
      rw [h8] at t0' t1'
      simp only [sqrtUtility, Fin.sum_univ_two]
      fin_cases i
      · simp [taxExampleT, Fin.sum_univ_two] at hb
        nlinarith [Real.sqrt_nonneg (y 0), Real.sqrt_nonneg (y 1)]
      · simp [taxExampleT, Fin.sum_univ_two] at hb
        nlinarith [Real.sqrt_nonneg (y 0), Real.sqrt_nonneg (y 1)]
  · refine hPO.2 ⟨fun _ _ => 1, ⟨fun _ _ => zero_le_one, rfl⟩, fun i => ?_, 0, ?_⟩
    · simp only [ExchangeEconomy.ofOrthant]
      rw [hux i]
      simp only [sqrtUtility, Fin.sum_univ_two, Real.sqrt_one]
      nlinarith
    · simp only [ExchangeEconomy.ofOrthant]
      rw [hux 0]
      simp only [sqrtUtility, Fin.sum_univ_two, Real.sqrt_one]
      nlinarith

/-- **Exercise 17.C.3(c)** (MWG, p. 643). The budget set with taxes on net trades, at equal rates
for purchases and sales: `{xᵢ ∈ ℝ^L₊ : p·(xᵢ - ωᵢ) + ∑ₗ t_ℓᵢ p_ℓ |x_ℓᵢ - ω_ℓᵢ| ≤ Tᵢ}`. -/
def netTaxBudget (p t ω : Fin L → ℝ) (T : ℝ) : Set (Fin L → ℝ) :=
  {x | x ∈ nonnegOrthant L ∧ p ⬝ᵥ (x - ω) + ∑ l, t l * p l * |x l - ω l| ≤ T}

/-- **Exercise 17.C.3(d)** (MWG, p. 643). Taxes on net trades with rate `b_ℓ` on purchases and
`s_ℓ` on sales: `{xᵢ ∈ ℝ^L₊ : p·(xᵢ - ωᵢ) + ∑ₗ p_ℓ (b_ℓ (x_ℓ - ω_ℓ)⁺ + s_ℓ (ω_ℓ - x_ℓ)⁺) ≤ Tᵢ}`. -/
def buySellTaxBudget (p b s ω : Fin L → ℝ) (T : ℝ) : Set (Fin L → ℝ) :=
  {x | x ∈ nonnegOrthant L ∧
    p ⬝ᵥ (x - ω) + ∑ l, p l * (b l * max (x l - ω l) 0 + s l * max (ω l - x l) 0) ≤ T}

/-- **Exercise 17.C.3(c)** (MWG, p. 643). The net-trade budget set is the buy/sell budget set with
equal rates; unlike the gross-consumption budget set (a linear constraint), its boundary is
kinked at `x_ℓ = ω_ℓ`; it is convex for `t ≥ 0`, `p ≥ 0`, and contains `ωᵢ` when `Tᵢ ≥ 0`. -/
theorem exercise_17_C_3c (p t ω : Fin L → ℝ) (T : ℝ) :
    netTaxBudget p t ω T = buySellTaxBudget p t t ω T ∧
      ((∀ l, 0 ≤ t l) → (∀ l, 0 ≤ p l) → Convex ℝ (netTaxBudget p t ω T)) ∧
      (ω ∈ nonnegOrthant L → 0 ≤ T → ω ∈ netTaxBudget p t ω T) := by
  have habs : ∀ a : ℝ, |a| = max a 0 + max (-a) 0 := fun a => by
    rcases le_total a 0 with h | h
    · rw [abs_of_nonpos h, max_eq_right h, max_eq_left (by linarith)]; ring
    · rw [abs_of_nonneg h, max_eq_left h, max_eq_right (by linarith)]; ring
  refine ⟨?_, fun ht hp => ?_, fun hω hT => ⟨hω, by simp [hT]⟩⟩
  · ext x
    simp only [netTaxBudget, buySellTaxBudget, Set.mem_ofPred_eq]
    have : ∀ l, t l * p l * |x l - ω l| =
        p l * (t l * max (x l - ω l) 0 + t l * max (ω l - x l) 0) := fun l => by
      rw [habs, neg_sub]; ring
    simp only [this]
  · intro x hx y hy a c ha hc hac
    refine ⟨convex_nonnegOrthant L hx.1 hy.1 ha hc hac, ?_⟩
    have hlin : p ⬝ᵥ (a • x + c • y - ω) = a * p ⬝ᵥ (x - ω) + c * p ⬝ᵥ (y - ω) := by
      have : a • x + c • y - ω = a • (x - ω) + c • (y - ω) := by
        calc a • x + c • y - ω = a • x + c • y - (a + c) • ω := by rw [hac, one_smul]
          _ = a • (x - ω) + c • (y - ω) := by module
      rw [this, dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    have hterm : ∀ l, t l * p l * |(a • x + c • y) l - ω l| ≤
        a * (t l * p l * |x l - ω l|) + c * (t l * p l * |y l - ω l|) := fun l => by
      have h1 : (a • x + c • y) l - ω l = a * (x l - ω l) + c * (y l - ω l) := by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        have : ω l = (a + c) * ω l := by rw [hac, one_mul]
        linarith
      rw [h1]
      have h2 : |a * (x l - ω l) + c * (y l - ω l)| ≤ a * |x l - ω l| + c * |y l - ω l| := by
        calc _ ≤ |a * (x l - ω l)| + |c * (y l - ω l)| := abs_add_le _ _
          _ = a * |x l - ω l| + c * |y l - ω l| := by
            rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hc]
      have h3 : 0 ≤ t l * p l := mul_nonneg (ht l) (hp l)
      nlinarith
    have hsum := Finset.sum_le_sum fun l (_ : l ∈ Finset.univ) => hterm l
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
    have h1 := mul_le_mul_of_nonneg_left hx.2 ha
    have h2 := mul_le_mul_of_nonneg_left hy.2 hc
    have h3 : a * T + c * T = T := by rw [← add_mul, hac, one_mul]
    rw [hlin]
    nlinarith

/-- **Exercise 17.C.3(d)** (MWG, p. 643). With nonnegative purchase and sales tax rates and
`p ≥ 0`, the buy/sell budget set is convex. -/
theorem exercise_17_C_3d {p b s ω : Fin L → ℝ} (T : ℝ) (hb : ∀ l, 0 ≤ b l)
    (hs : ∀ l, 0 ≤ s l) (hp : ∀ l, 0 ≤ p l) : Convex ℝ (buySellTaxBudget p b s ω T) := by
  intro x hx y hy a c ha hc hac
  refine ⟨convex_nonnegOrthant L hx.1 hy.1 ha hc hac, ?_⟩
  have hlin : p ⬝ᵥ (a • x + c • y - ω) = a * p ⬝ᵥ (x - ω) + c * p ⬝ᵥ (y - ω) := by
    have : a • x + c • y - ω = a • (x - ω) + c • (y - ω) := by
      calc a • x + c • y - ω = a • x + c • y - (a + c) • ω := by rw [hac, one_smul]
        _ = a • (x - ω) + c • (y - ω) := by module
    rw [this, dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  have hmax : ∀ u v : ℝ, max (a * u + c * v) 0 ≤ a * max u 0 + c * max v 0 := fun u v => by
    apply max_le
    · nlinarith [le_max_left u 0, le_max_left v 0]
    · nlinarith [le_max_right u 0, le_max_right v 0]
  have hterm : ∀ l, p l * (b l * max ((a • x + c • y) l - ω l) 0 +
      s l * max (ω l - (a • x + c • y) l) 0) ≤
      a * (p l * (b l * max (x l - ω l) 0 + s l * max (ω l - x l) 0)) +
      c * (p l * (b l * max (y l - ω l) 0 + s l * max (ω l - y l) 0)) := fun l => by
    have e1 : (a • x + c • y) l - ω l = a * (x l - ω l) + c * (y l - ω l) := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have : ω l = (a + c) * ω l := by rw [hac, one_mul]
      linarith
    have e2 : ω l - (a • x + c • y) l = a * (ω l - x l) + c * (ω l - y l) := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have : ω l = (a + c) * ω l := by rw [hac, one_mul]
      linarith
    rw [e1, e2]
    have m1 := mul_le_mul_of_nonneg_left (hmax (x l - ω l) (y l - ω l)) (hb l)
    have m2 := mul_le_mul_of_nonneg_left (hmax (ω l - x l) (ω l - y l)) (hs l)
    have m3 := mul_le_mul_of_nonneg_left (add_le_add m1 m2) (hp l)
    nlinarith
  have hsum := Finset.sum_le_sum fun l (_ : l ∈ Finset.univ) => hterm l
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have h1 := mul_le_mul_of_nonneg_left hx.2 ha
  have h2 := mul_le_mul_of_nonneg_left hy.2 hc
  have h3 : a * T + c * T = T := by rw [← add_mul, hac, one_mul]
  rw [hlin]
  nlinarith

/-! ### Exercise 17.C.4 -/

/-- **Exercise 17.C.4** (MWG, p. 643). The progressive redistribution rule applied to wealths
`w`: with mean `w̄`, a consumer above the mean pays half his excess over the mean into a fund,
and a consumer below the mean receives a share of the fund proportional to his deficiency. -/
noncomputable def progressiveWealth (w : ι → ℝ) (i : ι) : ℝ :=
  let m := (∑ j, w j) / Fintype.card ι
  let fund := ∑ j, if m < w j then (w j - m) / 2 else 0
  let D := ∑ j, if w j < m then m - w j else 0
  if m < w i then w i - (w i - m) / 2
  else if w i < m then w i + (m - w i) / D * fund else w i

/-- **Exercise 17.C.4** (MWG, p. 643). The progressive rule gives every consumer
`(wᵢ + w̄)/2`: the fund is half the total excess over the mean, which equals the total
deficiency. -/
theorem progressiveWealth_eq [Nonempty ι] (w : ι → ℝ) (i : ι) :
    progressiveWealth w i = (w i + (∑ j, w j) / Fintype.card ι) / 2 := by
  set m := (∑ j, w j) / Fintype.card ι with hm
  have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hsum0 : ∑ j, (w j - m) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hm]
    field_simp
    ring
  have hsplit : ∀ j, w j - m = (if m < w j then w j - m else 0) -
      (if w j < m then m - w j else 0) := fun j => by
    split_ifs with h1 h2 h2
    · linarith
    · ring
    · ring
    · linarith [not_lt.1 h1, not_lt.1 h2]
  have hAD : ∑ j, (if m < w j then w j - m else 0) = ∑ j, (if w j < m then m - w j else 0) := by
    have := hsum0
    rw [Finset.sum_congr rfl fun j _ => hsplit j, Finset.sum_sub_distrib] at this
    linarith
  have hfund : (∑ j, if m < w j then (w j - m) / 2 else 0) =
      (∑ j, if w j < m then m - w j else 0) / 2 := by
    rw [← hAD, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> ring
  simp only [progressiveWealth]
  rw [← hm, hfund]
  split_ifs with h1 h2
  · ring
  · have hD : 0 < ∑ j, (if w j < m then m - w j else 0) := by
      have hle : ∀ j ∈ Finset.univ, 0 ≤ (if w j < m then m - w j else 0) := fun j _ => by
        split_ifs with h
        · linarith
        · exact le_rfl
      have hi := Finset.single_le_sum hle (Finset.mem_univ i)
      simp only [h2, ↓reduceIte] at hi
      linarith
    field_simp
    ring
  · have : w i = m := le_antisymm (not_lt.1 h1) (not_lt.1 h2)
    rw [this]
    ring

/-- **Exercise 17.C.4(a)** (MWG, p. 643). With `ω₁ = (1, 2)` and `ω₂ = (2, 1)` the after-tax
wealths are `(5p₁ + 7p₂)/4` and `(7p₁ + 5p₂)/4` (whichever consumer is richer). -/
theorem exercise_17_C_4a (p : Fin 2 → ℝ) :
    progressiveWealth (fun i : Fin 2 => p ⬝ᵥ ![![1, 2], ![2, 1]] i) 0 = (5 * p 0 + 7 * p 1) / 4 ∧
      progressiveWealth (fun i : Fin 2 => p ⬝ᵥ ![![1, 2], ![2, 1]] i) 1 =
        (7 * p 0 + 5 * p 1) / 4 := by
  rw [progressiveWealth_eq, progressiveWealth_eq]
  simp [dotProduct, Fin.sum_univ_two]
  constructor <;> ring

/-- **Exercise 17.C.4(b)** (MWG, p. 643). Yes: in a pure exchange economy with continuous,
strictly convex, strongly monotone preferences, `ωᵢ ∈ ℝ^L₊` and `∑ᵢ ωᵢ ≫ 0`, the excess demand
with progressively redistributed wealths satisfies (i)-(v) of Proposition 17.B.2, so by
Proposition 17.C.1 an equilibrium with this redistribution exists. -/
theorem exercise_17_C_4b [Nonempty ι] {u : ι → (Fin L → ℝ) → ℝ} {ω : ι → Fin L → ℝ}
    (hu : ∀ i, StandardUtility (u i)) (hω : ∀ i, ω i ∈ nonnegOrthant L)
    (hpos : ∀ l, 0 < (∑ i, ω i) l) :
    IsStandardExcessDemand (wealthExcessDemand u
      (fun i p => progressiveWealth (fun j => p ⬝ᵥ ω j) i) (fun _ => ∑ i, ω i)) ∧
      ∃ p, IsEqmPrice (wealthExcessDemand u
        (fun i p => progressiveWealth (fun j => p ⬝ᵥ ω j) i) (fun _ => ∑ i, ω i)) p := by
  have hI : (0 : ℝ) < (Fintype.card ι : ℝ) := Nat.cast_pos.2 Fintype.card_pos
  set w' : ι → (Fin L → ℝ) → ℝ :=
    fun i p => (p ⬝ᵥ ω i + (∑ j, p ⬝ᵥ ω j) / (Fintype.card ι : ℝ)) / 2
  have hw : (fun i p => progressiveWealth (fun j => p ⬝ᵥ ω j) i) = w' := by
    funext i p
    exact progressiveWealth_eq _ i
  rw [hw]
  have hstd : IsStandardExcessDemand (wealthExcessDemand u w' (fun _ => ∑ i, ω i)) := by
    rcases Nat.eq_zero_or_pos L with rfl | hL
    · exact isStandardExcessDemand_of_fin_zero _
    have hdot0 : ∀ i, ∀ p ∈ posOrthant L, 0 ≤ p ⬝ᵥ ω i := fun i p hp =>
      Finset.sum_nonneg fun l _ => mul_nonneg (hp l).le (hω i l)
    refine isStandard_wealthExcessDemand hL hu (fun i p hp => ?_) (fun i => ?_)
      continuousOn_const (fun i p _ α _ => ?_) (fun _ _ _ _ => rfl) (fun p _ => ?_)
      ⟨∑ i, ω i, fun _ _ => le_rfl⟩ ?_
    · have := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => hdot0 j p hp
      have := hdot0 i p hp
      simp only [w']
      positivity
    · simp only [w', dotProduct]
      fun_prop
    · simp only [w', smul_dotProduct, smul_eq_mul, ← Finset.mul_sum]
      ring
    · have hS : ∑ i, w' i p = (∑ j, p ⬝ᵥ ω j + (Fintype.card ι : ℝ) *
          ((∑ j, p ⬝ᵥ ω j) / (Fintype.card ι : ℝ))) / 2 := by
        simp only [w', ← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_const,
          Finset.card_univ, nsmul_eq_mul]
        ring
      rw [hS, mul_div_cancel₀ _ hI.ne', dotProduct_sum]
      ring
    · intro ps p hps hlim hp0
      let i : ι := Classical.arbitrary ι
      have hpT := dotProduct_pos_of_ne_zero (nonneg_of_tendsto_pos hps hlim) hp0 hpos
      rw [dotProduct_sum] at hpT
      have hpi : 0 ≤ p ⬝ᵥ ω i := Finset.sum_nonneg fun l _ =>
        mul_nonneg (nonneg_of_tendsto_pos hps hlim l) (hω i l)
      refine ⟨i, w' i p, by simp only [w']; positivity, id, strictMono_id, ?_⟩
      have h1 : ∀ j, Tendsto (fun n => ps n ⬝ᵥ ω j) atTop (𝓝 (p ⬝ᵥ ω j)) := fun j =>
        appendixA_tendsto_dotProduct_seq hlim tendsto_const_nhds
      exact (((h1 i).add ((tendsto_finsetSum _ fun j _ => h1 j).div_const
        (Fintype.card ι : ℝ))).div_const 2)
  exact ⟨hstd, proposition_17_C_1 hstd⟩

/-! ### Exercise 17.C.5 -/

/-- **Exercise 17.C.5** (MWG, p. 643). The induced preference of a consumer with utility `u` on
`ℝ^L₊` and household technology `Y`: `x ≿* x'` iff for every `y' ∈ Y` with `x' + y' ≥ 0` there is
`y ∈ Y` with `x + y ≥ 0` and `x + y ≿ x' + y'`. -/
def inducedPref (u : (Fin L → ℝ) → ℝ) (Y : Set (Fin L → ℝ)) (x x' : Fin L → ℝ) : Prop :=
  ∀ y' ∈ Y, x' + y' ∈ nonnegOrthant L →
    ∃ y ∈ Y, x + y ∈ nonnegOrthant L ∧ u (x' + y') ≤ u (x + y)

/-- **Exercise 17.C.5(a)** (MWG, p. 643). Induced preferences are rational: complete and
transitive. -/
theorem exercise_17_C_5a (u : (Fin L → ℝ) → ℝ) (Y : Set (Fin L → ℝ)) :
    (∀ x x', inducedPref u Y x x' ∨ inducedPref u Y x' x) ∧
      ∀ x x' x'', inducedPref u Y x x' → inducedPref u Y x' x'' → inducedPref u Y x x'' := by
  refine ⟨fun x x' => ?_, fun x x' x'' h1 h2 y'' hy'' hx'' => ?_⟩
  · by_contra h
    simp only [not_or, inducedPref, not_forall, not_exists, not_and, not_le] at h
    obtain ⟨⟨y', hy', hx', h1⟩, ⟨y, hy, hx, h2⟩⟩ := h
    have a := h1 y hy hx
    have b := h2 y' hy' hx'
    linarith
  · obtain ⟨y', hy', hx', hle'⟩ := h2 y'' hy'' hx''
    obtain ⟨y, hy, hx, hle⟩ := h1 y' hy' hx'
    exact ⟨y, hy, hx, hle'.trans hle⟩

/-- **Exercise 17.C.5(b)** (MWG, p. 643). If `Y` is convex and `≿` is convex (a quasiconcave
utility on `ℝ^L₊`), the induced preferences are convex: every upper contour set
`{x : x ≿* x₀}` is convex. -/
theorem exercise_17_C_5b {u : (Fin L → ℝ) → ℝ} (hq : QuasiconcaveOn ℝ (nonnegOrthant L) u)
    {Y : Set (Fin L → ℝ)} (hY : Convex ℝ Y) (x₀ : Fin L → ℝ) :
    Convex ℝ {x | inducedPref u Y x x₀} := by
  intro x hx x' hx' a b ha hb hab y₀ hy₀ hx₀
  obtain ⟨y, hy, hxy, h1⟩ := hx y₀ hy₀ hx₀
  obtain ⟨y', hy', hxy', h2⟩ := hx' y₀ hy₀ hx₀
  refine ⟨a • y + b • y', hY hy hy' ha hb hab, ?_, ?_⟩
  · have : a • x + b • x' + (a • y + b • y') = a • (x + y) + b • (x' + y') := by module
    rw [this]
    exact convex_nonnegOrthant L hxy hxy' ha hb hab
  · have heq : a • x + b • x' + (a • y + b • y') = a • (x + y) + b • (x' + y') := by module
    rw [heq]
    exact (hq (u (x₀ + y₀)) ⟨hxy, h1⟩ ⟨hxy', h2⟩ ha hb hab).2

end MWG.PositiveEquilibriumTheory
