/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.IndexTwoGoods
import MWGClassicalDemand.UMPExamples
import ConsumerDemand.CESDemand

/-!
# Exercise 17.D.1: a CES economy (MWG p. 644)

Two consumers, two goods, `ρ = -4`, `ω₁ = (1, 0)`, `ω₂ = (0, 1)`, and
`u₁ = (α x₁₁^ρ + x₂₁^ρ)^{1/ρ}`, `u₂ = (x₁₂^ρ + α x₂₂^ρ)^{1/ρ}` (`ex17D1Economy α`); the book takes
`α = 2`. With `s = p₁^{1/5}` (normalization `p₂ = 1`) and `c = α^{1/5}` the excess demand is
(`ex17D1_excessDemand`)

  `z₁(p₁, 1) = 1/(s⁵ + c s) - 1/(c s⁴ + 1)`,   `z₂(p₁, 1) = -p₁ z₁(p₁, 1)`,

so `z₁ = 0` iff `(s - 1)(s⁴ + (1 - c)(s³ + s² + s) + 1) = 0`.

* **The printed claim is false** (`exercise_17_D_1_printed`): for `α = 2`, `c = 2^{1/5} < 5/3`, the
  quartic factor is positive for `s > 0`, and the unique normalized equilibrium is `p = (1, 1)`.
* **Corrected** (`exercise_17_D_1_corrected`): with `α = (31/14)⁵` (`c = 31/14`) the quartic is
  `(s - 2)(s - 1/2)(s² + 9s/7 + 1)`, and the economy has exactly three equilibria,
  `p₁ ∈ {1/32, 1, 32}`. (Multiplicity needs `c ≥ 5/3`, i.e. `α ≥ (5/3)⁵ ≈ 12.9`.)
-/

namespace MWG.PositiveEquilibriumTheory

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.GeneralEquilibriumExamples

/-- The CES utility `(∑ⱼ aⱼ xⱼ^ρ)^{1/ρ}` with `ρ = -4` on `ℝ²₊` (Kreps's `CESUtility`, `0` on the
boundary). -/
noncomputable def cesU (a : Fin 2 → ℝ) : (Fin 2 → ℝ) → ℝ :=
  extendOrthant (Kreps.ConsumerDemand.CESUtility a (-4))

/-- The CES weight `(aⱼ/pⱼ)^{1/(1-ρ)} = (aⱼ/pⱼ)^{1/5}`. -/
noncomputable def cesW (a p : Fin 2 → ℝ) (j : Fin 2) : ℝ := (a j / p j) ^ ((5 : ℕ)⁻¹ : ℝ)

/-- The CES demand `xⱼ(p, w) = w (aⱼ/pⱼ)^{1/5} / ∑ₖ pₖ (aₖ/pₖ)^{1/5}` (`ρ = -4`). -/
noncomputable def cesD (a p : Fin 2 → ℝ) (w : ℝ) : Fin 2 → ℝ :=
  fun j => w / (p 0 * cesW a p 0 + p 1 * cesW a p 1) * cesW a p j

/-- The CES Walrasian demand for `ρ = -4` (Kreps `problem_3_7`). -/
theorem walrasianDemand_cesU {a : Fin 2 → ℝ} (ha : ∀ j, 0 < a j) {p : Fin 2 → ℝ}
    (hp : ∀ j, 0 < p j) {w : ℝ} (hw : 0 ≤ w) : walrasianDemand (cesU a) p w = {cesD a p w} := by
  rw [cesU, walrasianDemand_extendOrthant _ hp hw,
    Kreps.ConsumerDemand.problem_3_7 a ha (by norm_num : (-4 : ℝ) < 1) (by norm_num),
    Set.image_singleton]
  congr 1
  funext j
  simp [Kreps.ConsumerDemand.CESBundle, Kreps.ConsumerDemand.CESWeight,
    Kreps.ConsumerDemand.CESDenominator, Fin.sum_univ_two, cesD, cesW,
    Real.coe_toNNReal w hw]
  norm_num

/-- CES demand exhausts wealth. -/
theorem dotProduct_cesD {a p : Fin 2 → ℝ} (ha : ∀ j, 0 < a j) (hp : ∀ j, 0 < p j) (w : ℝ) :
    p ⬝ᵥ cesD a p w = w := by
  have h0 : 0 < p 0 * cesW a p 0 + p 1 * cesW a p 1 := by
    have := Real.rpow_pos_of_pos (div_pos (ha 0) (hp 0)) ((5 : ℕ)⁻¹ : ℝ)
    have := Real.rpow_pos_of_pos (div_pos (ha 1) (hp 1)) ((5 : ℕ)⁻¹ : ℝ)
    have := hp 0
    have := hp 1
    simp only [cesW]
    positivity
  simp only [dotProduct, Fin.sum_univ_two, cesD]
  field_simp

/-- **Exercise 17.D.1** (MWG, p. 644). The economy: `u₁ = (α x₁₁^ρ + x₂₁^ρ)^{1/ρ}`,
`u₂ = (x₁₂^ρ + α x₂₂^ρ)^{1/ρ}`, `ρ = -4`, `ω₁ = (1, 0)`, `ω₂ = (0, 1)` (the book: `α = 2`). -/
noncomputable def ex17D1Economy (α : ℝ) : ExchangeEconomy (Fin 2) 2 :=
  ExchangeEconomy.ofOrthant ![cesU ![α, 1], cesU ![1, α]] ![![1, 0], ![0, 1]]

variable {α : ℝ}

/-- The excess demand of `ex17D1Economy` at `p ≫ 0`. -/
theorem ex17D1_excessDemand_eq (hα : 0 < α) {p : Fin 2 → ℝ} (hp : p ∈ posOrthant 2) :
    excessDemand (ex17D1Economy α) p =
      cesD ![α, 1] p (p 0) + cesD ![1, α] p (p 1) - ![1, 1] := by
  have ha1 : ∀ j, 0 < (![α, 1] : Fin 2 → ℝ) j := fun j => by fin_cases j <;> simp [hα]
  have ha2 : ∀ j, 0 < (![1, α] : Fin 2 → ℝ) j := fun j => by fin_cases j <;> simp [hα]
  have hd0 : (ex17D1Economy α).demand 0 p = {cesD ![α, 1] p (p 0)} := by
    have h := walrasianDemand_cesU ha1 hp (hp 0).le
    have hw : p ⬝ᵥ (![1, 0] : Fin 2 → ℝ) = p 0 := by simp [dotProduct, Fin.sum_univ_two]
    change walrasianDemand (cesU ![α, 1]) p (p ⬝ᵥ ![1, 0]) = _
    rw [hw]
    exact h
  have hd1 : (ex17D1Economy α).demand 1 p = {cesD ![1, α] p (p 1)} := by
    have h := walrasianDemand_cesU ha2 hp (hp 1).le
    have hw : p ⬝ᵥ (![0, 1] : Fin 2 → ℝ) = p 1 := by simp [dotProduct, Fin.sum_univ_two]
    change walrasianDemand (cesU ![1, α]) p (p ⬝ᵥ ![0, 1]) = _
    rw [hw]
    exact h
  rw [excessDemand_eq, Fin.sum_univ_two, demandFn_eq _ hd0, demandFn_eq _ hd1]
  congr 1
  funext l
  fin_cases l <;>
    simp [ExchangeEconomy.totalEndowment, ex17D1Economy, ExchangeEconomy.ofOrthant]

/-- Walras' law for `ex17D1Economy`. -/
theorem ex17D1_walras (hα : 0 < α) : EDWalrasLaw (excessDemand (ex17D1Economy α)) := by
  intro p hp
  have ha1 : ∀ j, 0 < (![α, 1] : Fin 2 → ℝ) j := fun j => by fin_cases j <;> simp [hα]
  have ha2 : ∀ j, 0 < (![1, α] : Fin 2 → ℝ) j := fun j => by fin_cases j <;> simp [hα]
  rw [ex17D1_excessDemand_eq hα hp, dotProduct_sub, dotProduct_add, dotProduct_cesD ha1 hp,
    dotProduct_cesD ha2 hp]
  simp [dotProduct, Fin.sum_univ_two]

/-- **Exercise 17.D.1**: the excess demand for good 1. Writing `p₁ = s⁵` (`s > 0`) and
`c = α^{1/5}`: `z₁(s⁵, 1) = 1/(s⁵ + c s) - 1/(c s⁴ + 1)`. -/
theorem ex17D1_excessDemand (hα : 0 < α) {s : ℝ} (hs : 0 < s) :
    excessDemand (ex17D1Economy α) ![s ^ 5, 1] 0 =
      1 / (s ^ 5 + α ^ ((5 : ℕ)⁻¹ : ℝ) * s) - 1 / (α ^ ((5 : ℕ)⁻¹ : ℝ) * s ^ 4 + 1) := by
  have hp : (![s ^ 5, 1] : Fin 2 → ℝ) ∈ posOrthant 2 := vec2_mem_posOrthant (by positivity) one_pos
  rw [ex17D1_excessDemand_eq hα hp]
  set c := α ^ ((5 : ℕ)⁻¹ : ℝ)
  have hc : 0 < c := Real.rpow_pos_of_pos hα _
  have hs5 : (s ^ 5) ^ ((5 : ℕ)⁻¹ : ℝ) = s := Real.pow_rpow_inv_natCast hs.le (by norm_num)
  have hW1 : (α / s ^ 5) ^ ((5 : ℕ)⁻¹ : ℝ) = c / s := by
    rw [Real.div_rpow hα.le (by positivity), hs5]
  have hW2 : (1 / s ^ 5) ^ ((5 : ℕ)⁻¹ : ℝ) = 1 / s := by
    rw [Real.div_rpow zero_le_one (by positivity), hs5, Real.one_rpow]
  have hW3 : (α / 1) ^ ((5 : ℕ)⁻¹ : ℝ) = c := by rw [div_one]
  have hW4 : ((1 : ℝ) / 1) ^ ((5 : ℕ)⁻¹ : ℝ) = 1 := by rw [div_one, Real.one_rpow]
  simp only [Pi.sub_apply, Pi.add_apply, cesD, cesW, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, hW1, hW2, hW3, hW4]
  field_simp
  ring

/-- With `s = p₁^{1/5}`, `(p₁, 1)` is an equilibrium of `ex17D1Economy α` iff
`c s⁴ + 1 = s⁵ + c s`, `c = α^{1/5}`. -/
theorem ex17D1_eqm_iff (hα : 0 < α) {s : ℝ} (hs : 0 < s) :
    IsNormEqm (excessDemand (ex17D1Economy α)) (vec1 (s ^ 5)) ↔
      α ^ ((5 : ℕ)⁻¹ : ℝ) * s ^ 4 + 1 = s ^ 5 + α ^ ((5 : ℕ)⁻¹ : ℝ) * s := by
  rw [isNormEqm_vec1_iff (ex17D1_walras hα), ex17D1_excessDemand hα hs]
  have hc : 0 < α ^ ((5 : ℕ)⁻¹ : ℝ) := Real.rpow_pos_of_pos hα _
  have h1 : 0 < s ^ 5 + α ^ ((5 : ℕ)⁻¹ : ℝ) * s := by positivity
  have h2 : 0 < α ^ ((5 : ℕ)⁻¹ : ℝ) * s ^ 4 + 1 := by positivity
  constructor
  · rintro ⟨-, h⟩
    rw [sub_eq_zero, div_eq_div_iff h1.ne' h2.ne'] at h
    linarith
  · intro h
    refine ⟨by positivity, ?_⟩
    rw [sub_eq_zero, div_eq_div_iff h1.ne' h2.ne']
    linarith

/-- Every `p₁ > 0` is `s⁵` with `s = p₁^{1/5} > 0`. -/
theorem exists_fifth_root {t : ℝ} (ht : 0 < t) : ∃ s, 0 < s ∧ s ^ 5 = t :=
  ⟨t ^ ((5 : ℕ)⁻¹ : ℝ), Real.rpow_pos_of_pos ht _, Real.rpow_inv_natCast_pow ht.le (by norm_num)⟩

/-- An equilibrium has `p₁ > 0`. -/
theorem ex17D1_pos (hα : 0 < α) {t : ℝ} (h : IsNormEqm (excessDemand (ex17D1Economy α)) (vec1 t)) :
    0 < t :=
  ((isNormEqm_vec1_iff (ex17D1_walras hα)).1 h).1

/-- **Exercise 17.D.1** (MWG, p. 644), as printed: **false**. With `α = 2` and `ρ = -4` the
economy has a unique normalized equilibrium, `p = (1, 1)`: since `c = 2^{1/5} < 5/3`, the factor
`s⁴ + (1 - c)(s³ + s² + s) + 1` of `c s⁴ + 1 - s⁵ - c s = -(s - 1)(…)` is positive for `s > 0`.
(The weight `2` is too small for the complementarity to produce multiple equilibria.) -/
theorem exercise_17_D_1_printed :
    {q : Fin 1 → ℝ | IsNormEqm (excessDemand (ex17D1Economy 2)) q} = {vec1 1} := by
  set c := (2 : ℝ) ^ ((5 : ℕ)⁻¹ : ℝ)
  have hc0 : 0 < c := Real.rpow_pos_of_pos two_pos _
  have hc5 : c ^ 5 = 2 := Real.rpow_inv_natCast_pow zero_le_two (by norm_num)
  have hc53 : c < 5 / 3 := by
    by_contra h
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 5 / 3) (not_lt.1 h) 5
    rw [hc5] at this
    norm_num at this
  ext q
  obtain ⟨t, rfl⟩ : ∃ t, q = vec1 t := ⟨q 0, (vec1_apply_zero q).symm⟩
  change IsNormEqm _ (vec1 t) ↔ vec1 t = vec1 1
  constructor
  · intro h
    obtain ⟨s, hs, hst⟩ := exists_fifth_root (ex17D1_pos two_pos h)
    rw [← hst, ex17D1_eqm_iff two_pos hs] at h
    have hfac : (s - 1) * (s ^ 4 + (1 - c) * (s ^ 3 + s ^ 2 + s) + 1) = 0 := by
      simp only [c] at h ⊢; linear_combination -h
    have hQ : 0 < s ^ 4 + (1 - c) * (s ^ 3 + s ^ 2 + s) + 1 := by
      have h1 : 0 ≤ (s - 1) ^ 2 * (s ^ 2 + 4 / 3 * s + 1) := by positivity
      have h2 : 0 < (5 / 3 - c) * (s ^ 3 + s ^ 2 + s) := by
        have : 0 < 5 / 3 - c := by linarith
        positivity
      nlinarith
    have hs1 : s = 1 := by
      have := (mul_eq_zero.1 hfac).resolve_right hQ.ne'
      linarith
    rw [← hst, hs1]
    norm_num
  · intro h
    rw [h]
    have := (ex17D1_eqm_iff two_pos one_pos).2 (by ring)
    simpa using this

/-- The weight `κ = (31/14)⁵` of the corrected Exercise 17.D.1 (so that `κ^{1/5} = 31/14`). -/
noncomputable def ex17D1Kappa : ℝ := (31 / 14) ^ 5

/-- **Exercise 17.D.1** (MWG, p. 644), corrected: with `α = (31/14)⁵` (still `ρ = -4`) the
economy has exactly three normalized equilibria, `p₁ ∈ {1/32, 1, 32}` (`s ∈ {1/2, 1, 2}`). -/
theorem exercise_17_D_1_corrected :
    {q : Fin 1 → ℝ | IsNormEqm (excessDemand (ex17D1Economy ex17D1Kappa)) q} =
      {vec1 (1 / 32), vec1 1, vec1 32} ∧
    {q : Fin 1 → ℝ | IsNormEqm (excessDemand (ex17D1Economy ex17D1Kappa)) q}.ncard = 3 := by
  have hκ : 0 < ex17D1Kappa := by unfold ex17D1Kappa; positivity
  have hc : ex17D1Kappa ^ ((5 : ℕ)⁻¹ : ℝ) = 31 / 14 :=
    Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)
  have hiff : ∀ s, 0 < s → (IsNormEqm (excessDemand (ex17D1Economy ex17D1Kappa)) (vec1 (s ^ 5))
      ↔ s = 1 / 2 ∨ s = 1 ∨ s = 2) := by
    intro s hs
    rw [ex17D1_eqm_iff hκ hs, hc]
    have hfac : 31 / 14 * s ^ 4 + 1 - (s ^ 5 + 31 / 14 * s) =
        -((s - 1 / 2) * (s - 1) * (s - 2) * (s ^ 2 + 9 / 7 * s + 1)) := by ring
    have hpos : 0 < s ^ 2 + 9 / 7 * s + 1 := by positivity
    constructor
    · intro h
      have h0 : (s - 1 / 2) * (s - 1) * (s - 2) * (s ^ 2 + 9 / 7 * s + 1) = 0 := by linarith
      rcases mul_eq_zero.1 h0 with h0 | h0
      · rcases mul_eq_zero.1 h0 with h0 | h0
        · rcases mul_eq_zero.1 h0 with h0 | h0
          · left; linarith
          · right; left; linarith
        · right; right; linarith
      · exact absurd h0 hpos.ne'
    · rintro (rfl | rfl | rfl) <;> norm_num
  have hset : {q : Fin 1 → ℝ | IsNormEqm (excessDemand (ex17D1Economy ex17D1Kappa)) q} =
      {vec1 (1 / 32), vec1 1, vec1 32} := by
    ext q
    obtain ⟨t, rfl⟩ : ∃ t, q = vec1 t := ⟨q 0, (vec1_apply_zero q).symm⟩
    change IsNormEqm _ (vec1 t) ↔ vec1 t ∈ ({vec1 (1 / 32), vec1 1, vec1 32} : Set _)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro h
      obtain ⟨s, hs, hst⟩ := exists_fifth_root (ex17D1_pos hκ h)
      rw [← hst] at h ⊢
      rcases (hiff s hs).1 h with rfl | rfl | rfl <;> norm_num
    · rintro (h | h | h)
      · have := (hiff (1 / 2) (by norm_num)).2 (Or.inl rfl)
        rw [h]; norm_num at this ⊢; exact this
      · have := (hiff 1 one_pos).2 (Or.inr (Or.inl rfl))
        rw [h]; simpa using this
      · have := (hiff 2 two_pos).2 (Or.inr (Or.inr rfl))
        rw [h]; norm_num at this ⊢; exact this
  refine ⟨hset, ?_⟩
  rw [hset]
  have hinj : ∀ a b : ℝ, vec1 a = vec1 b → a = b := fun a b h => congrFun h 0
  rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_singleton]
  · intro h
    rw [Set.mem_singleton_iff] at h
    have := hinj _ _ h
    norm_num at this
  · intro h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h <;> have := hinj _ _ h <;> norm_num at this

end MWG.PositiveEquilibriumTheory
