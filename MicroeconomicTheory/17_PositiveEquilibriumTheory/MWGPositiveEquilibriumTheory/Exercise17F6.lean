/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.Complements

/-!
# Exercise 17.F.6 with homothetic consumers (MWG p. 645)

Two consumption goods `g ∈ {0, 1}`, two factors, Cobb-Douglas constant returns technologies:
good `g` has unit cost `c_g(w) = κ_g w₁^{β_g} w₂^{1 - β_g}` (`fgeCost`) and, by Shephard's lemma,
unit factor requirements `a₁g = β_g c_g/w₁`, `a₂g = (1 - β_g) c_g/w₂`. Goods are priced at
average cost and final demand is met: the induced excess demand for factors is
`Z_f(w) = ∑_g a_fg(w) X_g(c(w), I(w)) - ω̄_f` (`fgeInduced`), and since `a₁g X_g = β_g E_g/w₁`
(`E_g` the expenditure on good `g`) only expenditures matter (`fgeInduced_eq`).

Consumers `i` own factors `ωᵢ ≥ 0` (income `Iᵢ = w·ωᵢ`) and have homothetic demand: they spend
the share `sᵢ(q₀/q₁)` of income on good 0 (`fgeDemand`). For two goods, homothetic demand has the
gross substitute property iff `sᵢ` is strictly decreasing, and it is normal
(`fgeDemand_gs_normal`).

**Result** (`exercise_17_F_6_homothetic`): with homothetic gross-substitute consumers and
`ω̄ ≫ 0`, the induced factor excess demand has the gross substitute property and is homogeneous
of degree zero, so (Proposition 17.F.3) there is at most one equilibrium factor price ray
(`exercise_17_F_6_unique`). Raising `w₂` raises `Z₁ = (1/w₁)∑ᵢ Iᵢ(β₁ + (β₀ - β₁)sᵢ(r))`, because
every income rises weakly and the relative price `r = c₀/c₁ = k(w₁/w₂)^{β₀-β₁}` moves so that the
weight `β₁ + (β₀ - β₁)sᵢ(r)` rises (`fge_term_mono`). Instance: `sᵢ(r) = 1/(1 + r)` (CES with
elasticity 2), `fgeShare_instance`.

The exercise as printed assumes only that the goods are normal and gross substitutes; without
homotheticity the income effect of a factor-price change can reverse the conclusion (a luxury good
produced intensively with the factor whose price is unchanged): a counterexample is
`exercise_17_F_6_counter` in `Closer17F.lean` (corrections 33).
-/

namespace MWG.PositiveEquilibriumTheory

open MWG.ConsumerChoice

/-- **Exercise 17.F.6** (MWG, p. 645). The Cobb-Douglas unit cost `κ w₁^β w₂^{1-β}`. -/
noncomputable def fgeCost (κ β : ℝ) (w : Fin 2 → ℝ) : ℝ := κ * w 0 ^ β * w 1 ^ (1 - β)

/-- Homothetic demand for the two goods: the share `s(q₀/q₁)` of income on good 0. -/
noncomputable def fgeDemand (s : ℝ → ℝ) (q : Fin 2 → ℝ) (I : ℝ) : Fin 2 → ℝ :=
  ![s (q 0 / q 1) * I / q 0, (1 - s (q 0 / q 1)) * I / q 1]

/-- **Exercise 17.F.6** (MWG, p. 645). The induced exchange economy for factors: goods priced at
average cost `q_g = c_g(w)`, final demand met, factor demand by Shephard's lemma
(`a₁g = β_g c_g/w₁`, `a₂g = (1 - β_g)c_g/w₂`), minus the factor endowments. -/
noncomputable def fgeInduced {ι : Type*} [Fintype ι] (κ β : Fin 2 → ℝ) (s : ι → ℝ → ℝ)
    (ω : ι → Fin 2 → ℝ) (w : Fin 2 → ℝ) : Fin 2 → ℝ :=
  let q : Fin 2 → ℝ := fun g => fgeCost (κ g) (β g) w
  let X : Fin 2 → ℝ := ∑ i, fgeDemand (s i) q (w ⬝ᵥ ω i)
  ![∑ g, β g * q g / w 0 * X g - ∑ i, ω i 0, ∑ g, (1 - β g) * q g / w 1 * X g - ∑ i, ω i 1]

/-- The relative price `c₀/c₁ = (κ₀/κ₁)(w₁/w₂)^{β₀ - β₁}`. -/
theorem fgeCost_ratio {κ β : Fin 2 → ℝ} (hκ : ∀ g, 0 < κ g) {w : Fin 2 → ℝ}
    (hw : ∀ l, 0 < w l) :
    fgeCost (κ 0) (β 0) w / fgeCost (κ 1) (β 1) w =
      κ 0 / κ 1 * (w 0 / w 1) ^ (β 0 - β 1) := by
  have h0 := hw 0
  have h1 := hw 1
  rw [fgeCost, fgeCost, Real.div_rpow h0.le h1.le, Real.rpow_sub h0, Real.rpow_sub h1,
    Real.rpow_sub h1, Real.rpow_one]
  have := hκ 0
  have := hκ 1
  have : 0 < w 0 ^ β 0 := Real.rpow_pos_of_pos h0 _
  have : 0 < w 0 ^ β 1 := Real.rpow_pos_of_pos h0 _
  have : 0 < w 1 ^ β 0 := Real.rpow_pos_of_pos h1 _
  have : 0 < w 1 ^ β 1 := Real.rpow_pos_of_pos h1 _
  field_simp
  rw [← Real.rpow_add h1]
  congr 1
  ring

/-- In the induced economy only expenditures matter:
`Z₁ = (1/w₁)∑ᵢ Iᵢ(β₁ + (β₀ - β₁)sᵢ(r)) - ω̄₁`, `Z₂ = (1/w₂)∑ᵢ Iᵢ((1-β₁) + (β₁ - β₀)sᵢ(r)) - ω̄₂`. -/
theorem fgeInduced_eq {ι : Type*} [Fintype ι] {κ β : Fin 2 → ℝ} (hκ : ∀ g, 0 < κ g)
    (s : ι → ℝ → ℝ) (ω : ι → Fin 2 → ℝ) {w : Fin 2 → ℝ} (hw : ∀ l, 0 < w l) :
    fgeInduced κ β s ω w =
      ![(∑ i, (w ⬝ᵥ ω i) * (β 1 + (β 0 - β 1) * s i (κ 0 / κ 1 * (w 0 / w 1) ^ (β 0 - β 1)))) /
          w 0 - ∑ i, ω i 0,
        (∑ i, (w ⬝ᵥ ω i) * ((1 - β 1) + (β 1 - β 0) *
          s i (κ 0 / κ 1 * (w 0 / w 1) ^ (β 0 - β 1)))) / w 1 - ∑ i, ω i 1] := by
  have hc : ∀ g, 0 < fgeCost (κ g) (β g) w := fun g =>
    mul_pos (mul_pos (hκ g) (Real.rpow_pos_of_pos (hw 0) _)) (Real.rpow_pos_of_pos (hw 1) _)
  have hr := fgeCost_ratio hκ hw (β := β)
  have h0 := (hc 0).ne'
  have h1 := (hc 1).ne'
  have hw0 := (hw 0).ne'
  have hw1 := (hw 1).ne'
  funext f
  fin_cases f
  · simp only [fgeInduced, fgeDemand, Fin.sum_univ_two, Finset.sum_apply, Fin.zero_eta,
      Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, hr]
    congr 1
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
    ring
  · simp only [fgeInduced, fgeDemand, Fin.sum_univ_two, Finset.sum_apply, Fin.mk_one,
      Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, hr]
    congr 1
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
    ring

/-- **Exercise 17.F.6** (MWG, p. 645). Homothetic two-good demand with a strictly decreasing
share `s ∈ (0, 1)` of good 0 is normal and has the gross substitute property: `x₀` rises with
`q₁`, `x₁` rises with `q₀`, both rise with income. -/
theorem fgeDemand_gs_normal {s : ℝ → ℝ} (hs : StrictAntiOn s (Set.Ioi 0))
    (hs01 : ∀ r, 0 < r → 0 < s r ∧ s r < 1) {q : Fin 2 → ℝ} (hq : ∀ l, 0 < q l) {I : ℝ}
    (hI : 0 < I) :
    (∀ q1', q 1 < q1' → fgeDemand s q I 0 < fgeDemand s ![q 0, q1'] I 0) ∧
      (∀ q0', q 0 < q0' → fgeDemand s q I 1 < fgeDemand s ![q0', q 1] I 1) ∧
      (∀ I', I < I' → fgeDemand s q I 0 < fgeDemand s q I' 0 ∧
        fgeDemand s q I 1 < fgeDemand s q I' 1) := by
  have h0 := hq 0
  have h1 := hq 1
  refine ⟨fun q1' hq1 => ?_, fun q0' hq0 => ?_, fun I' hI' => ⟨?_, ?_⟩⟩
  · have hq1' : 0 < q1' := by linarith
    have hr : q 0 / q1' < q 0 / q 1 := div_lt_div_of_pos_left h0 h1 hq1
    have := hs (div_pos h0 hq1') (div_pos h0 h1) hr
    simp only [fgeDemand, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [div_lt_div_iff_of_pos_right h0]
    exact mul_lt_mul_of_pos_right this hI
  · have hq0' : 0 < q0' := by linarith
    have hr : q 0 / q 1 < q0' / q 1 := div_lt_div_of_pos_right hq0 h1
    have := hs (div_pos h0 h1) (div_pos hq0' h1) hr
    simp only [fgeDemand, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [div_lt_div_iff_of_pos_right h1]
    exact mul_lt_mul_of_pos_right (by linarith) hI
  · simp only [fgeDemand, Matrix.cons_val_zero]
    rw [div_lt_div_iff_of_pos_right h0]
    exact mul_lt_mul_of_pos_left hI' (hs01 _ (div_pos h0 h1)).1
  · simp only [fgeDemand, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [div_lt_div_iff_of_pos_right h1]
    exact mul_lt_mul_of_pos_left hI' (by linarith [(hs01 _ (div_pos h0 h1)).2])

/-- The key monotonicity: for `wₐ > 0` fixed and `w_b < w_b'`, the term
`(wₐωₐ + w_bω_b)(b₁ + (b₀ - b₁)s(k(wₐ/w_b)^{d}))`, `d = ±(b₀ - b₁)` arranged so that the weight
rises, weakly increases, strictly if `ω_b > 0`. Stated for the weight function `φ`. -/
theorem fge_term_mono {I I' φ φ' : ℝ} (hI : 0 ≤ I) (hII : I ≤ I') (hφ : 0 < φ)
    (hφφ : φ ≤ φ') : I * φ ≤ I' * φ' ∧ (I < I' → I * φ < I' * φ') := by
  constructor
  · exact mul_le_mul hII hφφ hφ.le (le_trans hI hII)
  · intro hlt
    calc I * φ < I' * φ := mul_lt_mul_of_pos_right hlt hφ
      _ ≤ I' * φ' := mul_le_mul_of_nonneg_left hφφ (le_trans hI hII)

/-- The weight `b₁ + (b₀ - b₁)s(k x^{b₀ - b₁})` is positive and weakly decreasing in `x > 0`
when `s` is decreasing with values in `(0, 1)` and `b₀, b₁ > 0`. -/
theorem fge_weight {s : ℝ → ℝ} (hs : StrictAntiOn s (Set.Ioi 0))
    (hs01 : ∀ r, 0 < r → 0 < s r ∧ s r < 1) {k b0 b1 : ℝ} (hk : 0 < k) (hb0 : 0 < b0)
    (hb1 : 0 < b1) {x x' : ℝ} (hx : 0 < x) (hxx : x ≤ x') :
    0 < b1 + (b0 - b1) * s (k * x' ^ (b0 - b1)) ∧
      b1 + (b0 - b1) * s (k * x' ^ (b0 - b1)) ≤ b1 + (b0 - b1) * s (k * x ^ (b0 - b1)) := by
  have hx' : 0 < x' := lt_of_lt_of_le hx hxx
  have hr : 0 < k * x ^ (b0 - b1) := mul_pos hk (Real.rpow_pos_of_pos hx _)
  have hr' : 0 < k * x' ^ (b0 - b1) := mul_pos hk (Real.rpow_pos_of_pos hx' _)
  obtain ⟨hs0, hs1⟩ := hs01 _ hr'
  constructor
  · nlinarith [mul_pos hb0 hs0, mul_pos hb1 (by linarith : (0 : ℝ) < 1 - s (k * x' ^ (b0 - b1)))]
  · rcases lt_trichotomy b0 b1 with h | h | h
    · -- `d < 0`: the ratio falls as `x` rises, `s` rises, `(b₀ - b₁)s` falls
      have hle : k * x' ^ (b0 - b1) ≤ k * x ^ (b0 - b1) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hx hxx (by linarith)) hk.le
      have := hs.antitoneOn hr' hr hle
      nlinarith
    · rw [h]; simp
    · have hle : k * x ^ (b0 - b1) ≤ k * x' ^ (b0 - b1) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx.le hxx (by linarith)) hk.le
      have := hs.antitoneOn hr hr' hle
      nlinarith

/-- **Exercise 17.F.6** (MWG, p. 645), corrected: with homothetic consumers. Let `κ ≫ 0`,
`β_g ∈ (0, 1)`, consumers `i` with factor endowments `ωᵢ ≥ 0`, `ω̄ ≫ 0`, and homothetic gross
substitute demand (`sᵢ` strictly decreasing, values in `(0, 1)`). Then the induced aggregate excess
demand for factors has the gross substitute property and is homogeneous of degree zero. -/
theorem exercise_17_F_6_homothetic {ι : Type*} [Fintype ι] {κ β : Fin 2 → ℝ}
    (hκ : ∀ g, 0 < κ g) (hβ : ∀ g, 0 < β g ∧ β g < 1) {s : ι → ℝ → ℝ}
    (hs : ∀ i, StrictAntiOn (s i) (Set.Ioi 0)) (hs01 : ∀ i r, 0 < r → 0 < s i r ∧ s i r < 1)
    {ω : ι → Fin 2 → ℝ} (hω : ∀ i l, 0 ≤ ω i l) (htot : ∀ l, 0 < ∑ i, ω i l) :
    GrossSubstitute (fgeInduced κ β s ω) ∧ EDHomogeneous (fgeInduced κ β s ω) := by
  set k := κ 0 / κ 1 with hk
  have hk0 : 0 < k := div_pos (hκ 0) (hκ 1)
  constructor
  · intro p hp p' hp' l hl he m hm
    rw [fgeInduced_eq hκ s ω hp, fgeInduced_eq hκ s ω hp']
    fin_cases l <;> fin_cases m
    · exact absurd rfl hm
    · -- raising `w₁` raises `Z₂`
      simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue] at hl he ⊢
      have he1 : p' 1 = p 1 := he 1 (by decide)
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero, he1]
      rw [sub_lt_sub_iff_right, div_lt_div_iff_of_pos_right (hp 1)]
      obtain ⟨j, hj⟩ : ∃ j, 0 < ω j 0 := by
        by_contra hcon
        push Not at hcon
        have := Finset.sum_nonpos fun i (_ : i ∈ Finset.univ) => hcon i
        linarith [htot 0]
      have hterm : ∀ i, (p ⬝ᵥ ω i) * ((1 - β 1) + (β 1 - β 0) *
            s i (k * (p 0 / p 1) ^ (β 0 - β 1))) ≤ (p' ⬝ᵥ ω i) * ((1 - β 1) + (β 1 - β 0) *
            s i (k * (p' 0 / p 1) ^ (β 0 - β 1))) ∧
          (p ⬝ᵥ ω i < p' ⬝ᵥ ω i → (p ⬝ᵥ ω i) * ((1 - β 1) + (β 1 - β 0) *
            s i (k * (p 0 / p 1) ^ (β 0 - β 1))) < (p' ⬝ᵥ ω i) * ((1 - β 1) + (β 1 - β 0) *
            s i (k * (p' 0 / p 1) ^ (β 0 - β 1)))) := by
        intro i
        have hI : 0 ≤ p ⬝ᵥ ω i := Finset.sum_nonneg fun l _ => mul_nonneg (hp l).le (hω i l)
        have hII : p ⬝ᵥ ω i ≤ p' ⬝ᵥ ω i := by
          simp only [dotProduct, Fin.sum_univ_two, he1]
          nlinarith [hω i 0]
        -- the weight `(1 - β₁) + (β₁ - β₀)s` written as `b₁ + (b₀ - b₁)s` with `bₓ = 1 - βₓ`,
        -- in the ratio `x = p₁/p₀`, raised to `b₀ - b₁ = β₁ - β₀`
        have hrw : ∀ x : ℝ, 0 < x → k * x ^ (β 0 - β 1) = k * x⁻¹ ^ ((1 - β 0) - (1 - β 1)) :=
          fun x hx => by
            rw [Real.inv_rpow hx.le, ← Real.rpow_neg hx.le]; ring_nf
        have hx : 0 < (p 0 / p 1)⁻¹ := inv_pos.2 (div_pos (hp 0) (hp 1))
        have hxx : (p' 0 / p 1)⁻¹ ≤ (p 0 / p 1)⁻¹ := by
          rw [inv_div, inv_div]
          exact div_le_div_of_nonneg_left (hp 1).le (hp 0) hl.le
        obtain ⟨hpos, hmono⟩ := fge_weight (hs i) (hs01 i) hk0 (b0 := 1 - β 0) (b1 := 1 - β 1)
          (by linarith [(hβ 0).2]) (by linarith [(hβ 1).2])
          (inv_pos.2 (div_pos (hp' 0) (hp 1))) hxx
        rw [← hrw _ (div_pos (hp' 0) (hp 1)), ← hrw _ (div_pos (hp 0) (hp 1))] at hmono
        rw [← hrw _ (div_pos (hp 0) (hp 1))] at hpos
        have e : ∀ S : ℝ, (1 - β 1) + ((1 - β 0) - (1 - β 1)) * S =
            (1 - β 1) + (β 1 - β 0) * S := fun S => by ring
        rw [e, e] at hmono
        rw [e] at hpos
        exact fge_term_mono hI hII hpos hmono
      refine Finset.sum_lt_sum (fun i _ => (hterm i).1) ⟨j, Finset.mem_univ j, (hterm j).2 ?_⟩
      simp only [dotProduct, Fin.sum_univ_two, he1]
      nlinarith [mul_lt_mul_of_pos_right hl hj]
    · -- raising `w₂` raises `Z₁`
      simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue] at hl he ⊢
      have he0 : p' 0 = p 0 := he 0 (by decide)
      simp only [Matrix.cons_val_zero, he0]
      rw [sub_lt_sub_iff_right, div_lt_div_iff_of_pos_right (hp 0)]
      obtain ⟨j, hj⟩ : ∃ j, 0 < ω j 1 := by
        by_contra hcon
        push Not at hcon
        have := Finset.sum_nonpos fun i (_ : i ∈ Finset.univ) => hcon i
        linarith [htot 1]
      have hterm : ∀ i, (p ⬝ᵥ ω i) * (β 1 + (β 0 - β 1) *
            s i (k * (p 0 / p 1) ^ (β 0 - β 1))) ≤ (p' ⬝ᵥ ω i) * (β 1 + (β 0 - β 1) *
            s i (k * (p 0 / p' 1) ^ (β 0 - β 1))) ∧
          (p ⬝ᵥ ω i < p' ⬝ᵥ ω i → (p ⬝ᵥ ω i) * (β 1 + (β 0 - β 1) *
            s i (k * (p 0 / p 1) ^ (β 0 - β 1))) < (p' ⬝ᵥ ω i) * (β 1 + (β 0 - β 1) *
            s i (k * (p 0 / p' 1) ^ (β 0 - β 1)))) := by
        intro i
        have hI : 0 ≤ p ⬝ᵥ ω i := Finset.sum_nonneg fun l _ => mul_nonneg (hp l).le (hω i l)
        have hII : p ⬝ᵥ ω i ≤ p' ⬝ᵥ ω i := by
          simp only [dotProduct, Fin.sum_univ_two, he0]
          nlinarith [hω i 1]
        have hxx : p 0 / p' 1 ≤ p 0 / p 1 := div_le_div_of_nonneg_left (hp 0).le (hp 1) hl.le
        obtain ⟨hpos, hmono⟩ := fge_weight (hs i) (hs01 i) hk0 (hβ 0).1 (hβ 1).1
          (div_pos (hp 0) (hp' 1)) hxx
        exact fge_term_mono hI hII hpos hmono
      refine Finset.sum_lt_sum (fun i _ => (hterm i).1) ⟨j, Finset.mem_univ j, (hterm j).2 ?_⟩
      simp only [dotProduct, Fin.sum_univ_two, he0]
      nlinarith [mul_lt_mul_of_pos_right hl hj]
    · exact absurd rfl hm
  · intro p hp a ha
    have hap := smul_mem_posOrthant hp ha
    rw [fgeInduced_eq hκ s ω hp, fgeInduced_eq hκ s ω hap]
    have h2 : ∀ i, (a • p) ⬝ᵥ ω i = a * (p ⬝ᵥ ω i) := fun i => by rw [smul_dotProduct, smul_eq_mul]
    simp only [h2, mul_assoc, ← Finset.mul_sum, Pi.smul_apply, smul_eq_mul,
      mul_div_mul_left _ _ ha.ne']

/-- **Exercise 17.F.6** (MWG, p. 645), consequence: under the hypotheses of
`exercise_17_F_6_homothetic` there is at most one equilibrium factor price ray (Proposition
17.F.3), hence at most one equilibrium of the overall economy (goods prices are the unit costs). -/
theorem exercise_17_F_6_unique {ι : Type*} [Fintype ι] {κ β : Fin 2 → ℝ}
    (hκ : ∀ g, 0 < κ g) (hβ : ∀ g, 0 < β g ∧ β g < 1) {s : ι → ℝ → ℝ}
    (hs : ∀ i, StrictAntiOn (s i) (Set.Ioi 0)) (hs01 : ∀ i r, 0 < r → 0 < s i r ∧ s i r < 1)
    {ω : ι → Fin 2 → ℝ} (hω : ∀ i l, 0 ≤ ω i l) (htot : ∀ l, 0 < ∑ i, ω i l)
    {w w' : Fin 2 → ℝ} (hw : w ∈ posOrthant 2) (hw' : w' ∈ posOrthant 2)
    (h0 : fgeInduced κ β s ω w = 0) (h0' : fgeInduced κ β s ω w' = 0) :
    ∃ α : ℝ, 0 < α ∧ w' = α • w := by
  obtain ⟨hGS, hH⟩ := exercise_17_F_6_homothetic hκ hβ hs hs01 hω htot
  exact proposition_17_F_3 hH hGS hw hw' (h0.trans h0'.symm)

/-- Instance of the share hypotheses: `s(r) = 1/(1 + r)`, the expenditure share of good 0 for the
CES utility `(√x₀ + √x₁)²` (elasticity of substitution 2). -/
theorem fgeShare_instance :
    StrictAntiOn (fun r : ℝ => 1 / (1 + r)) (Set.Ioi 0) ∧
      ∀ r : ℝ, 0 < r → 0 < 1 / (1 + r) ∧ 1 / (1 + r) < 1 := by
  refine ⟨fun r hr r' hr' hlt => ?_, fun r hr => ⟨by positivity, ?_⟩⟩
  · have : (0 : ℝ) < 1 + r := by have := Set.mem_Ioi.1 hr; linarith
    exact one_div_lt_one_div_of_lt this (by linarith)
  · rw [div_lt_one (by linarith)]; linarith

end MWG.PositiveEquilibriumTheory
