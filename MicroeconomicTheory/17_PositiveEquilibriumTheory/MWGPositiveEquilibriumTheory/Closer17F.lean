/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.Exercise17F6

/-!
# Exercise 17.F.6 without homotheticity: a counterexample (MWG p. 645)

Exercise 17.F.6 asks to show that, when the two consumption goods are normal and gross
substitutes in the consumers' demand function, the induced excess demand for factors has the gross
substitute property. `exercise_17_F_6_homothetic` proves this for homothetic consumers. In
general it is false:

* `fgeInducedGen` is the induced factor excess demand for arbitrary demand functions `Dᵢ(q, I)`
  (goods priced at Cobb-Douglas average cost, final demand met, Shephard requirements); for
  homothetic demand it is `fgeInduced` (`fgeInducedGen_homothetic`).
* `fgeLux` is the demand of one consumer spending the share `s = m/(m + r²)` of income on good 0
  (`r = q₀/q₁`, `m = I/q₁`): `x₀ = I²q₁/(q₀(Iq₁ + q₀²))`, `x₁ = q₀²I/(q₁(Iq₁ + q₀²))`. It exhausts
  income and is homogeneous of degree zero (`fgeLux_walras`, `fgeLux_hom`), both goods are
  strictly normal at all prices and incomes (`fgeLux_normal`), they are strict gross substitutes
  (`fgeLux_gs`), and the own compensated price effect of good 0 is negative
  (`fgeLux_slutsky`: `∂x₀/∂q₀ + x₀ ∂x₀/∂I < 0`, the integrability condition with two goods).
  Good 0 is a luxury.
* `exercise_17_F_6_counter`: with technologies `c₀ = √(w₁w₂)`, `c₁ = w₁^{1/4}w₂^{3/4}` (good 0
  factor-1 intensive) and one consumer owning `ω = (1, 1/1000)`, raising `w₂` from `1` to `16`
  (with `w₁ = 1`) lowers the excess demand for factor 1: the induced factor excess demand does not
  have the gross substitute property. Real income falls and spending on the luxury good 0, which
  uses factor 1 intensively, falls with it.
-/

namespace MWG.PositiveEquilibriumTheory

/-- **Exercise 17.F.6** (MWG, p. 645). The induced excess demand for factors for arbitrary demand
functions `Dᵢ(q, I)` of the consumers: goods priced at average cost `q_g = c_g(w)`, final
demand met, factor requirements by Shephard's lemma, minus the factor endowments. -/
noncomputable def fgeInducedGen {ι : Type*} [Fintype ι] (κ β : Fin 2 → ℝ)
    (D : ι → (Fin 2 → ℝ) → ℝ → Fin 2 → ℝ) (ω : ι → Fin 2 → ℝ) (w : Fin 2 → ℝ) : Fin 2 → ℝ :=
  let q : Fin 2 → ℝ := fun g => fgeCost (κ g) (β g) w
  let X : Fin 2 → ℝ := ∑ i, D i q (w ⬝ᵥ ω i)
  ![∑ g, β g * q g / w 0 * X g - ∑ i, ω i 0, ∑ g, (1 - β g) * q g / w 1 * X g - ∑ i, ω i 1]

/-- For homothetic demand `fgeInducedGen` is the induced excess demand `fgeInduced`. -/
theorem fgeInducedGen_homothetic {ι : Type*} [Fintype ι] (κ β : Fin 2 → ℝ)
    (s : ι → ℝ → ℝ) (ω : ι → Fin 2 → ℝ) (w : Fin 2 → ℝ) :
    fgeInducedGen κ β (fun i => fgeDemand (s i)) ω w = fgeInduced κ β s ω w := rfl

/-- **Exercise 17.F.6** (MWG, p. 645). A nonhomothetic demand function for two goods: the share
`I q₁/(I q₁ + q₀²)` of income is spent on good 0. -/
noncomputable def fgeLux (q : Fin 2 → ℝ) (I : ℝ) : Fin 2 → ℝ :=
  ![I ^ 2 * q 1 / (q 0 * (I * q 1 + q 0 ^ 2)), q 0 ^ 2 * I / (q 1 * (I * q 1 + q 0 ^ 2))]

/-- `fgeLux` exhausts income. -/
theorem fgeLux_walras {q : Fin 2 → ℝ} (hq : ∀ g, 0 < q g) {I : ℝ} (hI : 0 < I) :
    q 0 * fgeLux q I 0 + q 1 * fgeLux q I 1 = I := by
  have h0 := hq 0
  have h1 := hq 1
  have hd : 0 < I * q 1 + q 0 ^ 2 := by positivity
  simp only [fgeLux, Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp

/-- `fgeLux` is homogeneous of degree zero in prices and income. -/
theorem fgeLux_hom {q : Fin 2 → ℝ} (hq : ∀ g, 0 < q g) {I t : ℝ} (hI : 0 < I) (ht : 0 < t) :
    fgeLux (t • q) (t * I) = fgeLux q I := by
  have h0 := hq 0
  have h1 := hq 1
  funext g
  fin_cases g
  · simp only [fgeLux, Pi.smul_apply, smul_eq_mul, Fin.zero_eta, Fin.isValue,
      Matrix.cons_val_zero]
    field_simp
  · simp only [fgeLux, Pi.smul_apply, smul_eq_mul, Fin.mk_one, Fin.isValue,
      Matrix.cons_val_one, Matrix.cons_val_zero]
    field_simp

/-- Both goods are strictly normal: demand rises strictly with income, at all prices. -/
theorem fgeLux_normal {q : Fin 2 → ℝ} (hq : ∀ g, 0 < q g) {I I' : ℝ} (hI : 0 < I)
    (hII : I < I') : fgeLux q I 0 < fgeLux q I' 0 ∧ fgeLux q I 1 < fgeLux q I' 1 := by
  have h0 := hq 0
  have h1 := hq 1
  have hI' : 0 < I' := hI.trans hII
  have hd : 0 < I * q 1 + q 0 ^ 2 := by positivity
  have hd' : 0 < I' * q 1 + q 0 ^ 2 := by positivity
  simp only [fgeLux, Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor
  · rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    have : I ^ 2 * (I' * q 1 + q 0 ^ 2) < I' ^ 2 * (I * q 1 + q 0 ^ 2) := by
      have e : I' ^ 2 * (I * q 1 + q 0 ^ 2) - I ^ 2 * (I' * q 1 + q 0 ^ 2) =
          (I' - I) * (I * I' * q 1 + (I + I') * q 0 ^ 2) := by ring
      have : 0 < (I' - I) * (I * I' * q 1 + (I + I') * q 0 ^ 2) := by
        have := sub_pos.2 hII
        positivity
      linarith
    have hq01 : 0 < q 1 * q 0 := by positivity
    nlinarith
  · rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    have : I * (I' * q 1 + q 0 ^ 2) < I' * (I * q 1 + q 0 ^ 2) := by
      nlinarith [mul_lt_mul_of_pos_right hII (pow_pos h0 2)]
    have hq01 : 0 < q 0 ^ 2 * q 1 := by positivity
    nlinarith

/-- The two goods are strict gross substitutes: `x₀` rises strictly with `q₁`, and `x₁` with
`q₀`, at every income `I > 0`. -/
theorem fgeLux_gs {I : ℝ} (hI : 0 < I) {a b b' : ℝ} (ha : 0 < a) (hb : 0 < b) (hbb : b < b') :
    fgeLux ![a, b] I 0 < fgeLux ![a, b'] I 0 ∧ fgeLux ![b, a] I 1 < fgeLux ![b', a] I 1 := by
  have hb' : 0 < b' := hb.trans hbb
  simp only [fgeLux, Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor
  · rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    have : b * (I * b' + a ^ 2) < b' * (I * b + a ^ 2) := by
      nlinarith [mul_lt_mul_of_pos_right hbb (pow_pos ha 2)]
    have hp : 0 < I ^ 2 * a := by positivity
    nlinarith
  · rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    have hsq : b ^ 2 < b' ^ 2 := by nlinarith
    have : b ^ 2 * (I * a + b' ^ 2) < b' ^ 2 * (I * a + b ^ 2) := by
      nlinarith [mul_lt_mul_of_pos_right hsq (mul_pos hI ha)]
    have hp : 0 < I * a := by positivity
    nlinarith

/-- The compensated own-price effect of good 0 is negative:
`∂x₀/∂q₀ + x₀ ∂x₀/∂I = -I²q₁(2Iq₁q₀² + 3q₀⁴)/(q₀²(Iq₁ + q₀²)³) < 0`, with the two partial
derivatives computed as `HasDerivAt` statements. -/
theorem fgeLux_slutsky {q₀ q₁ I : ℝ} (h0 : 0 < q₀) (h1 : 0 < q₁) (hI : 0 < I) :
    ∃ d₀ dI : ℝ,
      HasDerivAt (fun a => fgeLux ![a, q₁] I 0) d₀ q₀ ∧
        HasDerivAt (fun J => fgeLux ![q₀, q₁] J 0) dI I ∧
          d₀ + fgeLux ![q₀, q₁] I 0 * dI < 0 := by
  have hd : 0 < I * q₁ + q₀ ^ 2 := by positivity
  have hf : ∀ a, fgeLux ![a, q₁] I 0 = I ^ 2 * q₁ / (a * (I * q₁ + a ^ 2)) := fun a => rfl
  have hg : ∀ J, fgeLux ![q₀, q₁] J 0 = J ^ 2 * q₁ / (q₀ * (J * q₁ + q₀ ^ 2)) := fun J => rfl
  have hA : HasDerivAt (fun a => I ^ 2 * q₁ / (a * (I * q₁ + a ^ 2)))
      (-(I ^ 2 * q₁) * (1 * (I * q₁ + q₀ ^ 2) + q₀ * (2 * q₀)) / (q₀ * (I * q₁ + q₀ ^ 2)) ^ 2)
      q₀ := by
    have hden : HasDerivAt (fun a => a * (I * q₁ + a ^ 2)) (1 * (I * q₁ + q₀ ^ 2) + q₀ * (2 * q₀))
        q₀ := by
      have := (hasDerivAt_id' q₀).fun_mul ((hasDerivAt_pow 2 q₀).const_add (I * q₁))
      simpa using this
    have := (hden.inv (by positivity)).const_mul (I ^ 2 * q₁)
    convert this using 1
    · funext a; simp [div_eq_mul_inv]
    · field_simp
  have hB : HasDerivAt (fun J => J ^ 2 * q₁ / (q₀ * (J * q₁ + q₀ ^ 2)))
      ((2 * I * q₁ * (q₀ * (I * q₁ + q₀ ^ 2)) - I ^ 2 * q₁ * (q₀ * q₁)) /
        (q₀ * (I * q₁ + q₀ ^ 2)) ^ 2) I := by
    have hnum : HasDerivAt (fun J => J ^ 2 * q₁) (2 * I * q₁) I := by
      simpa using (hasDerivAt_pow 2 I).mul_const q₁
    have hden : HasDerivAt (fun J => q₀ * (J * q₁ + q₀ ^ 2)) (q₀ * q₁) I := by
      simpa using (((hasDerivAt_id I).mul_const q₁).add_const (q₀ ^ 2)).const_mul q₀
    exact hnum.div hden (by positivity)
  refine ⟨_, _, by simpa only [hf] using hA, by simpa only [hg] using hB, ?_⟩
  rw [hg]
  have hq : 0 < q₀ * (I * q₁ + q₀ ^ 2) := by positivity
  have key : -(I ^ 2 * q₁) * (1 * (I * q₁ + q₀ ^ 2) + q₀ * (2 * q₀)) /
        (q₀ * (I * q₁ + q₀ ^ 2)) ^ 2 +
      I ^ 2 * q₁ / (q₀ * (I * q₁ + q₀ ^ 2)) *
        ((2 * I * q₁ * (q₀ * (I * q₁ + q₀ ^ 2)) - I ^ 2 * q₁ * (q₀ * q₁)) /
          (q₀ * (I * q₁ + q₀ ^ 2)) ^ 2) =
      -(I ^ 2 * q₁ * (2 * (I * q₁) * q₀ ^ 2 + 3 * q₀ ^ 4)) /
        (q₀ ^ 2 * (I * q₁ + q₀ ^ 2) ^ 3) := by
    field_simp
    ring
  rw [key]
  apply div_neg_of_neg_of_pos _ (by positivity)
  have : 0 < I ^ 2 * q₁ * (2 * (I * q₁) * q₀ ^ 2 + 3 * q₀ ^ 4) := by positivity
  linarith

/-- `16^{1/2} = 4`. -/
theorem fge_sixteen_half : (16 : ℝ) ^ ((1 : ℝ) / 2) = 4 := by
  rw [show (16 : ℝ) = 4 ^ ((2 : ℕ) : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
  norm_num

/-- `16^{3/4} = 8`. -/
theorem fge_sixteen_threeQuarters : (16 : ℝ) ^ ((3 : ℝ) / 4) = 8 := by
  rw [show (16 : ℝ) = 2 ^ ((4 : ℕ) : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
  norm_num

/-- **Exercise 17.F.6** (MWG, p. 645) is false without homotheticity. One consumer with the
demand `fgeLux` (normal goods, strict gross substitutes, negative compensated own-price effect),
factor endowment `ω = (1, 1/1000)`, technologies `c₀ = √(w₁w₂)` and `c₁ = w₁^{1/4}w₂^{3/4}`:
raising the price of factor 2 from `1` to `16` (with `w₁ = 1`) lowers the excess demand for
factor 1, so the induced factor excess demand does not have the gross substitute property. -/
theorem exercise_17_F_6_counter :
    fgeInducedGen ![1, 1] ![1 / 2, 1 / 4] (fun _ : Fin 1 => fgeLux) (fun _ => ![1, 1 / 1000])
        ![1, 16] 0 <
      fgeInducedGen ![1, 1] ![1 / 2, 1 / 4] (fun _ : Fin 1 => fgeLux) (fun _ => ![1, 1 / 1000])
        ![1, 1] 0 := by
  have h1 : (16 : ℝ) ^ (1 - (1 : ℝ) / 2) = 4 := by
    rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]; exact fge_sixteen_half
  have h2 : (16 : ℝ) ^ (1 - (1 : ℝ) / 4) = 8 := by
    rw [show (1 : ℝ) - 1 / 4 = 3 / 4 by norm_num]; exact fge_sixteen_threeQuarters
  simp only [fgeInducedGen, fgeCost, fgeLux, Fin.sum_univ_two, Finset.univ_unique,
    Finset.sum_singleton, dotProduct, Matrix.cons_val_zero, Matrix.cons_val_one,
    Real.one_rpow, h1, h2, Finset.sum_apply, Fin.isValue]
  norm_num

end MWG.PositiveEquilibriumTheory
