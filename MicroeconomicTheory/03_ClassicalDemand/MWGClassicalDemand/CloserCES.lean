/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.UMPExamples
import MWGClassicalDemand.UtilityMore
import MWGClassicalDemand.ExpBasic
import ConsumerDemand.CESDemand
import ConsumerDemand.CESContinuity

/-!
# CES demand: Exercises 3.D.5 and 3.E.6

MWG, Exercise 3.D.5, p. 97 and Exercise 3.E.6, p. 98: the CES utility
`u(x) = (x₁^ρ + x₂^ρ)^{1/ρ}` of Exercise 3.C.6 with `α₁ = α₂ = 1`, for `ρ < 1`, `ρ ≠ 0`. For
`ρ < 0` the utility is extended by `0` on the boundary of `ℝ²_+` (the limit of the formula),
as in Kreps's `CESUtility`, which this module bridges to and whose demand theorem
(`Kreps.ConsumerDemand.problem_3_7`) it uses.

With `r = ρ/(ρ - 1)` and `S(p) = p₁^r + p₂^r`:

* `x_l(p, w) = w p_l^{r-1} / S(p)` and `v(p, w) = w S(p)^{1/ρ - 1}` (Exercise 3.D.5(a));
* the properties of Propositions 3.D.2 and 3.D.3 (Exercise 3.D.5(b));
* the linear and Leontief limits `ρ → 1` and `ρ → -∞` of demand and indirect utility
  (Exercise 3.D.5(c));
* the elasticity of substitution `ξ₁₂ = 1/(1 - ρ)`, and `1`, `0` for Cobb-Douglas and
  Leontief (Exercise 3.D.5(d));
* `h_l(p, ū) = ū p_l^{r-1} S(p)^{1/r - 1}` and `e(p, ū) = ū S(p)^{1/r}` for `ū > 0`, with the
  properties of Propositions 3.E.2 and 3.E.3 (Exercise 3.E.6).
-/

namespace MWG.ClassicalDemand

open Filter Topology MWG.ConsumerChoice Kreps.PreferenceProperties

/-- **Exercise 3.D.5** (MWG, p. 97). The CES utility `(x₁^ρ + x₂^ρ)^{1/ρ}` (Exercise 3.C.6 with
`α₁ = α₂ = 1`), extended by `0` on the boundary of `ℝ²_+` when `ρ < 0`. -/
noncomputable def cesUtility (ρ : ℝ) (x : Fin 2 → ℝ) : ℝ :=
  if ρ < 0 ∧ ∃ j, x j = 0 then 0 else (x 0 ^ ρ + x 1 ^ ρ) ^ (1 / ρ)

/-- The CES price exponent `r = ρ/(ρ - 1)`. -/
noncomputable def cesR (ρ : ℝ) : ℝ := ρ / (ρ - 1)

/-- The CES price index sum `S(p) = p₁^r + p₂^r`. -/
noncomputable def cesSum (ρ : ℝ) (p : Fin 2 → ℝ) : ℝ := p 0 ^ cesR ρ + p 1 ^ cesR ρ

/-- **Exercise 3.D.5(a)** (MWG, p. 97). The CES Walrasian demand `x_l = w p_l^{r-1} / S(p)`. -/
noncomputable def cesDemand (ρ : ℝ) (p : Fin 2 → ℝ) (w : ℝ) : Fin 2 → ℝ :=
  fun j => w * p j ^ (cesR ρ - 1) / cesSum ρ p

/-- **Exercise 3.D.5(a)** (MWG, p. 97). The CES indirect utility `v = w S(p)^{1/ρ - 1}`. -/
noncomputable def cesIndirect (ρ : ℝ) (p : Fin 2 → ℝ) (w : ℝ) : ℝ :=
  w * cesSum ρ p ^ (1 / ρ - 1)

/-- On `ℝ²_+` the CES utility is the extension of Kreps's `CESUtility ![1, 1] ρ`. -/
theorem cesUtility_eq_extend (ρ : ℝ) {x : Fin 2 → ℝ} (hx : x ∈ nonnegOrthant 2) :
    cesUtility ρ x = extendOrthant (Kreps.ConsumerDemand.CESUtility ![1, 1] ρ) x := by
  rw [extendOrthant_apply _ hx]
  simp [cesUtility, Kreps.ConsumerDemand.CESUtility, Kreps.ConsumerDemand.CESPowerSum,
    Fin.sum_univ_two]

/-- The CES utility is continuous on `ℝ²_+` (Kreps `cesUtility_continuous`). -/
theorem cesUtility_continuousOn {ρ : ℝ} (hρ0 : ρ ≠ 0) :
    ContinuousOn (cesUtility ρ) (nonnegOrthant 2) := by
  have h1 : (∀ j : Fin 2, (0 : ℝ) < ![1, 1] j) := by intro j; fin_cases j <;> simp
  have hc := extendOrthant_continuous (Kreps.ConsumerDemand.cesUtility_continuous ![1, 1] h1 hρ0)
  exact hc.continuousOn.congr fun x hx => cesUtility_eq_extend ρ hx

/-- Power identities behind the CES formulas: for `q > 0`,
`(1/q)^{1/(1-ρ)} = q^{r-1}` and `q · q^{r-1} = q^r`. -/
theorem ces_rpow_identities {ρ : ℝ} (hρ1 : ρ < 1) {q : ℝ} (hq : 0 < q) :
    (1 / q) ^ (1 / (1 - ρ)) = q ^ (cesR ρ - 1) ∧ q * q ^ (cesR ρ - 1) = q ^ cesR ρ := by
  have hr : cesR ρ - 1 = -(1 / (1 - ρ)) := by
    unfold cesR
    have : ρ - 1 ≠ 0 := by linarith
    have : 1 - ρ ≠ 0 := by linarith
    field_simp
    ring
  refine ⟨?_, ?_⟩
  · rw [hr, Real.rpow_neg hq.le, one_div q, Real.inv_rpow hq.le]
  · have := Real.rpow_add hq 1 (cesR ρ - 1)
    rw [Real.rpow_one, show 1 + (cesR ρ - 1) = cesR ρ by ring] at this
    rw [this]

/-- `S(p) > 0` for `p ≫ 0`. -/
theorem cesSum_pos (ρ : ℝ) {p : Fin 2 → ℝ} (hp : StrictlyPositive p) : 0 < cesSum ρ p :=
  add_pos (Real.rpow_pos_of_pos (hp 0) _) (Real.rpow_pos_of_pos (hp 1) _)

/-- **Exercise 3.D.5(a)** (MWG, p. 97). For `ρ < 1`, `ρ ≠ 0`, `p ≫ 0`, `w ≥ 0`, the CES UMP has
the unique solution `x_l(p, w) = w p_l^{r-1} / (p₁^r + p₂^r)`, `r = ρ/(ρ - 1)`. -/
theorem exercise_3_D_5a_demand {ρ : ℝ} (hρ1 : ρ < 1) (hρ0 : ρ ≠ 0) {p : Fin 2 → ℝ}
    (hp : StrictlyPositive p) {w : ℝ} (hw : 0 ≤ w) :
    walrasianDemand (cesUtility ρ) p w = {cesDemand ρ p w} := by
  have hp' : ∀ j, 0 < p j := hp
  have h1 : (∀ j : Fin 2, (0 : ℝ) < ![1, 1] j) := by intro j; fin_cases j <;> simp
  rw [walrasianDemand_congr (fun x hx => cesUtility_eq_extend ρ hx),
    walrasianDemand_extendOrthant _ hp' hw,
    Kreps.ConsumerDemand.problem_3_7 ![1, 1] h1 hρ1 hρ0, Set.image_singleton]
  congr 1
  funext j
  obtain ⟨a0, b0⟩ := ces_rpow_identities hρ1 (hp 0)
  obtain ⟨a1, b1⟩ := ces_rpow_identities hρ1 (hp 1)
  obtain ⟨aj, -⟩ := ces_rpow_identities hρ1 (hp j)
  simp only [Kreps.ConsumerDemand.CESBundle, Kreps.ConsumerDemand.CESWeight,
    Kreps.ConsumerDemand.CESDenominator, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Real.coe_toNNReal w hw, cesDemand, cesSum]
  fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero] at aj ⊢
    rw [a0, a1, b0, b1]
    ring
  · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one] at aj ⊢
    rw [a0, a1, b0, b1]
    ring

/-- The CES utility of the demanded bundle: `u(x(p, w)) = w S(p)^{1/ρ - 1}`. -/
theorem cesUtility_cesDemand {ρ : ℝ} (hρ1 : ρ < 1) (hρ0 : ρ ≠ 0) {p : Fin 2 → ℝ}
    (hp : StrictlyPositive p) {w : ℝ} (hw : 0 ≤ w) :
    cesUtility ρ (cesDemand ρ p w) = cesIndirect ρ p w := by
  have hS := cesSum_pos ρ hp
  rcases hw.lt_or_eq with hw | rfl
  · have hx : ∀ j, 0 < cesDemand ρ p w j := fun j =>
      div_pos (mul_pos hw (Real.rpow_pos_of_pos (hp j) _)) hS
    have hnot : ¬ (ρ < 0 ∧ ∃ j, cesDemand ρ p w j = 0) := by
      rintro ⟨-, j, hj⟩
      exact (hx j).ne' hj
    have hpow : ∀ j, cesDemand ρ p w j ^ ρ = (w / cesSum ρ p) ^ ρ * p j ^ cesR ρ := by
      intro j
      have hr : (cesR ρ - 1) * ρ = cesR ρ := by
        unfold cesR
        have : ρ - 1 ≠ 0 := by linarith
        field_simp
        ring
      rw [show cesDemand ρ p w j = (w / cesSum ρ p) * p j ^ (cesR ρ - 1) by
          simp only [cesDemand]; ring,
        Real.mul_rpow (div_pos hw hS).le (Real.rpow_nonneg (hp j).le _),
        ← Real.rpow_mul (hp j).le, hr]
    simp only [cesUtility, hnot, ↓reduceIte]
    rw [hpow 0, hpow 1, ← mul_add, show p 0 ^ cesR ρ + p 1 ^ cesR ρ = cesSum ρ p from rfl,
      Real.mul_rpow (Real.rpow_nonneg (div_pos hw hS).le _) hS.le, one_div,
      Real.rpow_rpow_inv (div_pos hw hS).le hρ0, cesIndirect, Real.rpow_sub_one hS.ne',
      one_div]
    field_simp
  · have hd : cesDemand ρ p 0 = 0 := by
      funext j
      simp [cesDemand]
    rw [hd]
    simp only [cesUtility, cesIndirect, zero_mul]
    split_ifs with h
    · rfl
    · simp only [Pi.zero_apply]
      rw [Real.zero_rpow hρ0, add_zero, Real.zero_rpow (one_div_ne_zero hρ0)]

/-- **Exercise 3.D.5(a)** (MWG, p. 97). The CES indirect utility `v(p, w) = w S(p)^{1/ρ - 1}`
(equivalently `w (p₁^r + p₂^r)^{-1/r}`). -/
theorem exercise_3_D_5a_indirect {ρ : ℝ} (hρ1 : ρ < 1) (hρ0 : ρ ≠ 0) {p : Fin 2 → ℝ}
    (hp : StrictlyPositive p) {w : ℝ} (hw : 0 ≤ w) :
    indirectUtility (cesUtility ρ) p w = cesIndirect ρ p w := by
  have hx : cesDemand ρ p w ∈ walrasianDemand (cesUtility ρ) p w := by
    rw [exercise_3_D_5a_demand hρ1 hρ0 hp hw]; rfl
  rw [indirectUtility_eq_of_mem hx, cesUtility_cesDemand hρ1 hρ0 hp hw]


/-- `S(αp) = α^r S(p)` and `α • p ≫ 0` for `α > 0`. -/
theorem cesSum_smul (ρ : ℝ) {p : Fin 2 → ℝ} (hp : StrictlyPositive p) {α : ℝ} (hα : 0 < α) :
    StrictlyPositive (α • p) ∧ cesSum ρ (α • p) = α ^ cesR ρ * cesSum ρ p := by
  refine ⟨fun l => by simpa using mul_pos hα (hp l), ?_⟩
  simp only [cesSum, Pi.smul_apply, smul_eq_mul]
  rw [Real.mul_rpow hα.le (hp 0).le, Real.mul_rpow hα.le (hp 1).le]
  ring

/-- **Exercise 3.D.5(b)** (MWG, p. 97), Proposition 3.D.2(i): the CES demand is homogeneous of
degree zero. -/
theorem exercise_3_D_5b_demand_homogeneous {ρ : ℝ} (hρ1 : ρ < 1) (hρ0 : ρ ≠ 0)
    {p : Fin 2 → ℝ} (hp : StrictlyPositive p) {w : ℝ} (hw : 0 ≤ w) {α : ℝ} (hα : 0 < α) :
    cesDemand ρ (α • p) (α * w) = cesDemand ρ p w := by
  have h := proposition_3_D_2_i (cesUtility ρ) p w hα
  rw [exercise_3_D_5a_demand hρ1 hρ0 (cesSum_smul ρ hp hα).1 (mul_nonneg hα.le hw),
    exercise_3_D_5a_demand hρ1 hρ0 hp hw] at h
  exact Set.singleton_eq_singleton_iff.1 h

/-- **Exercise 3.D.5(b)** (MWG, p. 97), Proposition 3.D.2(ii): Walras' law `p·x(p, w) = w`. -/
theorem exercise_3_D_5b_walras (ρ : ℝ) {p : Fin 2 → ℝ} (hp : StrictlyPositive p) (w : ℝ) :
    p ⬝ᵥ cesDemand ρ p w = w := by
  have hρ := cesSum_pos ρ hp
  simp only [dotProduct, Fin.sum_univ_two, cesDemand]
  have h0 : p 0 * p 0 ^ (cesR ρ - 1) = p 0 ^ cesR ρ := by
    have := Real.rpow_add (hp 0) 1 (cesR ρ - 1)
    rw [Real.rpow_one, show 1 + (cesR ρ - 1) = cesR ρ by ring] at this
    rw [this]
  have h1 : p 1 * p 1 ^ (cesR ρ - 1) = p 1 ^ cesR ρ := by
    have := Real.rpow_add (hp 1) 1 (cesR ρ - 1)
    rw [Real.rpow_one, show 1 + (cesR ρ - 1) = cesR ρ by ring] at this
    rw [this]
  have : p 0 * (w * p 0 ^ (cesR ρ - 1) / cesSum ρ p) +
      p 1 * (w * p 1 ^ (cesR ρ - 1) / cesSum ρ p) =
      w * (p 0 * p 0 ^ (cesR ρ - 1) + p 1 * p 1 ^ (cesR ρ - 1)) / cesSum ρ p := by ring
  rw [this, h0, h1, show p 0 ^ cesR ρ + p 1 ^ cesR ρ = cesSum ρ p from rfl]
  field_simp

/-- **Exercise 3.D.5(b)** (MWG, p. 97), Proposition 3.D.2(iii): the CES demand is
single-valued (`exercise_3_D_5a_demand`), and nonnegative. -/
theorem exercise_3_D_5b_nonneg (ρ : ℝ) {p : Fin 2 → ℝ} (hp : StrictlyPositive p) {w : ℝ}
    (hw : 0 ≤ w) : cesDemand ρ p w ∈ nonnegOrthant 2 := fun j =>
  div_nonneg (mul_nonneg hw (Real.rpow_nonneg (hp j).le _)) (cesSum_pos ρ hp).le

/-- **Exercise 3.D.5(b)** (MWG, p. 97), Proposition 3.D.3(i): `v` is homogeneous of degree
zero. -/
theorem exercise_3_D_5b_indirect_homogeneous {ρ : ℝ} (hρ1 : ρ < 1) (hρ0 : ρ ≠ 0)
    {p : Fin 2 → ℝ} (hp : StrictlyPositive p) {w : ℝ} (hw : 0 ≤ w) {α : ℝ} (hα : 0 < α) :
    cesIndirect ρ (α • p) (α * w) = cesIndirect ρ p w := by
  rw [← exercise_3_D_5a_indirect hρ1 hρ0 (cesSum_smul ρ hp hα).1 (mul_nonneg hα.le hw),
    ← exercise_3_D_5a_indirect hρ1 hρ0 hp hw]
  exact proposition_3_D_3_i _ p w hα

/-- **Exercise 3.D.5(b)** (MWG, p. 97), Proposition 3.D.3(ii): `v` is strictly increasing in
`w`. -/
theorem exercise_3_D_5b_indirect_wealth (ρ : ℝ) {p : Fin 2 → ℝ} (hp : StrictlyPositive p)
    {w w' : ℝ} (hww : w < w') : cesIndirect ρ p w < cesIndirect ρ p w' :=
  mul_lt_mul_of_pos_right hww (Real.rpow_pos_of_pos (cesSum_pos ρ hp) _)

/-- **Exercise 3.D.5(b)** (MWG, p. 97), Proposition 3.D.3(ii): `v` is nonincreasing in `p`. -/
theorem exercise_3_D_5b_indirect_prices {ρ : ℝ} (hρ1 : ρ < 1) (hρ0 : ρ ≠ 0)
    {p p' : Fin 2 → ℝ} (hp : StrictlyPositive p) (hp' : StrictlyPositive p') (hpp : p ≤ p')
    {w : ℝ} (hw : 0 ≤ w) : cesIndirect ρ p' w ≤ cesIndirect ρ p w := by
  rw [← exercise_3_D_5a_indirect hρ1 hρ0 hp hw, ← exercise_3_D_5a_indirect hρ1 hρ0 hp' hw]
  exact proposition_3_D_3_ii_prices (cesUtility_continuousOn hρ0) hp hp' hpp hw

/-- **Exercise 3.D.5(b)** (MWG, p. 97), Proposition 3.D.3(iii): `v` is quasiconvex on the
price-wealth domain. -/
theorem exercise_3_D_5b_indirect_quasiconvex {ρ : ℝ} (hρ1 : ρ < 1) (hρ0 : ρ ≠ 0) :
    QuasiconvexOn ℝ (pwDomainSet 2) (fun q => cesIndirect ρ q.1 q.2) := by
  have h := proposition_3_D_3_iii (cesUtility_continuousOn hρ0)
  intro t
  convert h t using 1
  ext q
  simp only [Set.mem_sep_iff]
  constructor
  · rintro ⟨hq, hle⟩
    exact ⟨hq, by rwa [exercise_3_D_5a_indirect hρ1 hρ0 hq.1 hq.2.le]⟩
  · rintro ⟨hq, hle⟩
    exact ⟨hq, by rwa [exercise_3_D_5a_indirect hρ1 hρ0 hq.1 hq.2.le] at hle⟩

/-- **Exercise 3.D.5(b)** (MWG, p. 97), Proposition 3.D.3(iv): `v` is continuous on the
price-wealth domain. -/
theorem exercise_3_D_5b_indirect_continuous {ρ : ℝ} (hρ1 : ρ < 1) (hρ0 : ρ ≠ 0) :
    ContinuousOn (fun q : (Fin 2 → ℝ) × ℝ => cesIndirect ρ q.1 q.2) (pwDomainSet 2) :=
  (proposition_3_D_3_iv (cesUtility_continuousOn hρ0)).congr fun _ hq =>
    (exercise_3_D_5a_indirect hρ1 hρ0 hq.1 hq.2.le).symm

/-- **Exercise 3.D.5(c)** (MWG, p. 97). The Leontief demand `(w/(p₁+p₂), w/(p₁+p₂))`. -/
noncomputable def leontiefDemand (p : Fin 2 → ℝ) (w : ℝ) : Fin 2 → ℝ :=
  fun _ => w / (p 0 + p 1)

/-- **Exercise 3.D.5(c)** (MWG, p. 97). For Leontief utility `min {x₁, x₂}`, `p ≫ 0` and
`w ≥ 0`, the demand is `{(w/(p₁+p₂), w/(p₁+p₂))}` and `v(p, w) = w/(p₁+p₂)`. -/
theorem exercise_3_D_5c_leontief {p : Fin 2 → ℝ} (hp : StrictlyPositive p) {w : ℝ}
    (hw : 0 ≤ w) :
    walrasianDemand leontiefUtility p w = {leontiefDemand p w} ∧
      indirectUtility leontiefUtility p w = w / (p 0 + p 1) := by
  have hP : 0 < p 0 + p 1 := add_pos (hp 0) (hp 1)
  set m := w / (p 0 + p 1) with hm
  have hm0 : 0 ≤ m := div_nonneg hw hP.le
  have hpm : p 0 * m + p 1 * m = w := by rw [hm]; field_simp
  have hbound : ∀ y ∈ budgetSet p w, leontiefUtility y ≤ m := by
    intro y hy
    have hb : p 0 * y 0 + p 1 * y 1 ≤ w := by
      simpa [dotProduct, Fin.sum_univ_two] using hy.2
    simp only [leontiefUtility]
    by_contra hcon
    push Not at hcon
    have h0 : m < y 0 := lt_of_lt_of_le hcon (min_le_left _ _)
    have h1 : m < y 1 := lt_of_lt_of_le hcon (min_le_right _ _)
    nlinarith [mul_lt_mul_of_pos_left h0 (hp 0), mul_lt_mul_of_pos_left h1 (hp 1)]
  have hmem : leontiefDemand p w ∈ budgetSet p w := by
    refine ⟨fun _ => hm0, ?_⟩
    simp only [dotProduct, Fin.sum_univ_two, leontiefDemand]
    rw [← hm, hpm]
  have hval : leontiefUtility (leontiefDemand p w) = m := by
    simp [leontiefUtility, leontiefDemand, hm]
  have hdem : walrasianDemand leontiefUtility p w = {leontiefDemand p w} := by
    ext y
    constructor
    · rintro ⟨hy, hmax⟩
      have hge := hmax _ hmem
      rw [hval] at hge
      have hb : p 0 * y 0 + p 1 * y 1 ≤ w := by
        simpa [dotProduct, Fin.sum_univ_two] using hy.2
      have h0 : m ≤ y 0 := hge.trans (min_le_left _ _)
      have h1 : m ≤ y 1 := hge.trans (min_le_right _ _)
      have e0 : y 0 = m := le_antisymm (le_of_mul_le_mul_left
        (by nlinarith [mul_le_mul_of_nonneg_left h1 (hp 1).le]) (hp 0)) h0
      have e1 : y 1 = m := le_antisymm (le_of_mul_le_mul_left
        (by nlinarith [mul_le_mul_of_nonneg_left h0 (hp 0).le]) (hp 1)) h1
      rw [Set.mem_singleton_iff]
      funext j
      fin_cases j
      · simpa [leontiefDemand] using e0
      · simpa [leontiefDemand] using e1
    · rintro rfl
      exact ⟨hmem, fun y hy => by rw [hval]; exact hbound y hy⟩
  refine ⟨hdem, ?_⟩
  have hx : leontiefDemand p w ∈ walrasianDemand leontiefUtility p w := by rw [hdem]; rfl
  rw [indirectUtility_eq_of_mem hx, hval]

/-- **Exercise 3.D.5(c)** (MWG, p. 97). The linear utility `x₁ + x₂`. -/
def linearUtility2 (x : Fin 2 → ℝ) : ℝ := x 0 + x 1

/-- **Exercise 3.D.5(c)** (MWG, p. 97). For linear utility `x₁ + x₂`, `p ≫ 0` and `w ≥ 0`:
`x ∈ x(p, w)` iff `x ≥ 0`, `p·x = w` and only goods of minimal price are bought; and
`v(p, w) = w / min {p₁, p₂}`. -/
theorem exercise_3_D_5c_linear {p : Fin 2 → ℝ} (hp : StrictlyPositive p) {w : ℝ}
    (hw : 0 ≤ w) (x : Fin 2 → ℝ) :
    (x ∈ walrasianDemand linearUtility2 p w ↔
      x ∈ nonnegOrthant 2 ∧ p ⬝ᵥ x = w ∧ ∀ i, 0 < x i → ∀ j, p i ≤ p j) ∧
      indirectUtility linearUtility2 p w = w / min (p 0) (p 1) := by
  set c := min (p 0) (p 1) with hc
  have hc0 : 0 < c := lt_min (hp 0) (hp 1)
  have hbound : ∀ y ∈ nonnegOrthant 2, c * linearUtility2 y ≤ p ⬝ᵥ y := by
    intro y hy
    simp only [linearUtility2, dotProduct, Fin.sum_univ_two]
    nlinarith [mul_le_mul_of_nonneg_right (min_le_left (p 0) (p 1)) (hy 0),
      mul_le_mul_of_nonneg_right (min_le_right (p 0) (p 1)) (hy 1)]
  -- a cheapest single-good bundle
  obtain ⟨k, hk⟩ : ∃ k : Fin 2, p k = c := by
    rcases le_total (p 0) (p 1) with h | h
    · exact ⟨0, by rw [hc, min_eq_left h]⟩
    · exact ⟨1, by rw [hc, min_eq_right h]⟩
  set z : Fin 2 → ℝ := Pi.single k (w / c) with hz
  have hz0 : z ∈ nonnegOrthant 2 := by
    intro j
    by_cases hj : j = k
    · subst hj; simp [hz, div_nonneg hw hc0.le]
    · simp [hz, hj]
  have hzp : p ⬝ᵥ z = w := by
    rw [hz, dotProduct_single, hk]
    field_simp
  have hzu : linearUtility2 z = w / c := by
    simp only [linearUtility2, hz]
    fin_cases k <;> simp
  have hzmem : z ∈ budgetSet p w := ⟨hz0, hzp.le⟩
  have hmaxval : ∀ y ∈ budgetSet p w, linearUtility2 y ≤ w / c := by
    intro y hy
    rw [le_div_iff₀ hc0, mul_comm]
    exact (hbound y hy.1).trans hy.2
  have hdem : ∀ y, y ∈ walrasianDemand linearUtility2 p w ↔
      y ∈ budgetSet p w ∧ linearUtility2 y = w / c := by
    intro y
    constructor
    · rintro ⟨hy, hmax⟩
      exact ⟨hy, le_antisymm (hmaxval y hy) (hzu ▸ hmax z hzmem)⟩
    · rintro ⟨hy, heq⟩
      exact ⟨hy, fun y' hy' => heq ▸ hmaxval y' hy'⟩
  refine ⟨?_, ?_⟩
  · rw [hdem]
    constructor
    · rintro ⟨⟨hx0, hxw⟩, hxu⟩
      have hb := hbound x hx0
      rw [hxu] at hb
      have hpx : p ⬝ᵥ x = w := le_antisymm hxw (by
        rwa [show c * (w / c) = w by field_simp] at hb)
      refine ⟨hx0, hpx, fun i hi j => ?_⟩
      have hsum : (p 0 - c) * x 0 + (p 1 - c) * x 1 = 0 := by
        have : p 0 * x 0 + p 1 * x 1 = w := by
          simpa [dotProduct, Fin.sum_univ_two] using hpx
        have h2 : x 0 + x 1 = w / c := hxu
        have : c * (x 0 + x 1) = w := by rw [h2]; field_simp
        linarith
      have t0 : 0 ≤ (p 0 - c) * x 0 :=
        mul_nonneg (sub_nonneg.2 (min_le_left _ _)) (hx0 0)
      have t1 : 0 ≤ (p 1 - c) * x 1 :=
        mul_nonneg (sub_nonneg.2 (min_le_right _ _)) (hx0 1)
      have hpi : p i = c := by
        fin_cases i
        · have : (p 0 - c) * x 0 = 0 := by linarith
          have := (mul_eq_zero.1 this).resolve_right hi.ne'
          simp only [Fin.zero_eta, Fin.isValue]; linarith
        · have : (p 1 - c) * x 1 = 0 := by linarith
          have := (mul_eq_zero.1 this).resolve_right hi.ne'
          simp only [Fin.mk_one, Fin.isValue]; linarith
      rw [hpi]
      fin_cases j
      · exact min_le_left _ _
      · exact min_le_right _ _
    · rintro ⟨hx0, hpx, hcheap⟩
      refine ⟨⟨hx0, hpx.le⟩, ?_⟩
      have hi : ∀ i, p i * x i = c * x i := by
        intro i
        rcases (hx0 i).lt_or_eq with h | h
        · have hpi : p i ≤ c := le_min (hcheap i h 0) (hcheap i h 1)
          have : c ≤ p i := by fin_cases i <;> simp [hc]
          rw [le_antisymm hpi this]
        · rw [← h]; ring
      have : p ⬝ᵥ x = c * linearUtility2 x := by
        simp only [dotProduct, Fin.sum_univ_two, linearUtility2, hi 0, hi 1]
        ring
      rw [hpx] at this
      rw [this]
      field_simp
  · have hx : z ∈ walrasianDemand linearUtility2 p w := (hdem z).2 ⟨hzmem, hzu⟩
    rw [indirectUtility_eq_of_mem hx, hzu]


/-- `r = ρ/(ρ - 1) → 1` as `ρ → -∞`. -/
theorem cesR_tendsto_atBot : Tendsto cesR atBot (𝓝 1) := by
  have hsub : Tendsto (fun ρ : ℝ => ρ - 1) atBot atBot := by
    simpa [sub_eq_add_neg] using tendsto_atBot_add_const_right atBot (-1 : ℝ) tendsto_id
  have h : Tendsto (fun ρ : ℝ => 1 + (ρ - 1)⁻¹) atBot (𝓝 (1 + 0)) :=
    tendsto_const_nhds.add (tendsto_inv_atBot_zero.comp hsub)
  rw [add_zero] at h
  apply h.congr'
  filter_upwards [eventually_lt_atBot (0 : ℝ)] with ρ hρ
  have : ρ - 1 ≠ 0 := by linarith
  unfold cesR
  field_simp
  ring

/-- `r = ρ/(ρ - 1) → -∞` as `ρ → 1⁻`. -/
theorem cesR_tendsto_one_left : Tendsto cesR (𝓝[<] 1) atBot := by
  have h1 : Tendsto (fun ρ : ℝ => ρ - 1) (𝓝[<] 1) (𝓝[<] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have : Tendsto (fun ρ : ℝ => ρ - 1) (𝓝 1) (𝓝 (1 - 1)) :=
        (continuous_id.sub continuous_const).tendsto 1
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ρ hρ
      exact sub_neg.2 (Set.mem_Iio.1 hρ)
  have h2 : Tendsto (fun ρ : ℝ => ρ) (𝓝[<] 1) (𝓝 1) := tendsto_nhdsWithin_of_tendsto_nhds
    continuous_id.continuousAt.tendsto
  have := h2.pos_mul_atBot one_pos (tendsto_inv_nhdsLT_zero.comp h1)
  exact this.congr fun ρ => by simp [cesR, div_eq_mul_inv]

/-- For `0 < a < b`, `(b/a)^r → 0` as `r → -∞`. -/
theorem ces_ratio_rpow_tendsto {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    Tendsto (fun r : ℝ => (b / a) ^ r) atBot (𝓝 0) := by
  have hc : 1 < b / a := (one_lt_div ha).2 hab
  have hlog : 0 < Real.log (b / a) := Real.log_pos hc
  have : Tendsto (fun r : ℝ => Real.exp (Real.log (b / a) * r)) atBot (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atBot hlog)
  apply this.congr'
  filter_upwards with r
  rw [Real.rpow_def_of_pos (by linarith)]

/-- For `0 < a < b`, as `r → -∞`, `w a^{r-1}/(a^r + b^r) → w/a` and
`w b^{r-1}/(a^r + b^r) → 0`. -/
theorem ces_two_good_limit {a b : ℝ} (ha : 0 < a) (hab : a < b) (w : ℝ) :
    Tendsto (fun r : ℝ => w * a ^ (r - 1) / (a ^ r + b ^ r)) atBot (𝓝 (w / a)) ∧
      Tendsto (fun r : ℝ => w * b ^ (r - 1) / (a ^ r + b ^ r)) atBot (𝓝 0) := by
  have hb : 0 < b := ha.trans hab
  have ht := ces_ratio_rpow_tendsto ha hab
  have hden : Tendsto (fun r : ℝ => 1 + (b / a) ^ r) atBot (𝓝 (1 + 0)) :=
    tendsto_const_nhds.add ht
  rw [add_zero] at hden
  have key : ∀ r : ℝ, b ^ r = a ^ r * (b / a) ^ r := by
    intro r
    rw [Real.div_rpow hb.le ha.le]
    field_simp [(Real.rpow_pos_of_pos ha r).ne']
  refine ⟨?_, ?_⟩
  · have := (tendsto_const_nhds (x := w / a)).div hden one_ne_zero
    rw [div_one] at this
    apply this.congr
    intro r
    have har := Real.rpow_pos_of_pos ha r
    have h1 : 0 < 1 + (b / a) ^ r := by positivity
    simp only [Pi.div_apply]
    rw [key r, Real.rpow_sub_one ha.ne']
    field_simp
  · have := ((tendsto_const_nhds (x := w / b)).mul ht).div hden one_ne_zero
    rw [mul_zero, zero_div] at this
    apply this.congr
    intro r
    have har := Real.rpow_pos_of_pos ha r
    have h1 : 0 < 1 + (b / a) ^ r := by positivity
    simp only [Pi.div_apply]
    rw [key r, Real.rpow_sub_one hb.ne', key r]
    field_simp

/-- **Exercise 3.D.5(c)** (MWG, p. 97). As `ρ → 1⁻` with `p₁ < p₂`, the CES demand converges to
`(w/p₁, 0)`, which is the linear demand. -/
theorem exercise_3_D_5c_limit_linear_lt {p : Fin 2 → ℝ} (hp : StrictlyPositive p)
    (h01 : p 0 < p 1) {w : ℝ} (hw : 0 ≤ w) :
    Tendsto (fun ρ => cesDemand ρ p w) (𝓝[<] 1) (𝓝 ![w / p 0, 0]) ∧
      walrasianDemand linearUtility2 p w = {![w / p 0, 0]} := by
  obtain ⟨l0, l1⟩ := ces_two_good_limit (hp 0) h01 w
  refine ⟨tendsto_pi_nhds.2 fun j => ?_, ?_⟩
  · fin_cases j
    · exact l0.comp cesR_tendsto_one_left
    · exact l1.comp cesR_tendsto_one_left
  · ext x
    rw [(exercise_3_D_5c_linear hp hw x).1, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hx0, hpx, hcheap⟩
      have hx1 : x 1 = 0 := by
        rcases (hx0 1).lt_or_eq with h | h
        · exact absurd (hcheap 1 h 0) (not_le.2 h01)
        · exact h.symm
      have hpx' : p 0 * x 0 + p 1 * x 1 = w := by
        simpa [dotProduct, Fin.sum_univ_two] using hpx
      rw [hx1, mul_zero, add_zero] at hpx'
      funext j
      fin_cases j
      · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
        rw [← hpx']
        field_simp [(hp 0).ne']
      · simpa using hx1
    · rintro rfl
      refine ⟨fun j => ?_, ?_, fun i hi j => ?_⟩
      · fin_cases j
        · exact div_nonneg hw (hp 0).le
        · simp
      · simp [dotProduct, Fin.sum_univ_two]
        field_simp [(hp 0).ne']
      · fin_cases i
        · fin_cases j
          · exact le_rfl
          · exact h01.le
        · simp at hi

/-- **Exercise 3.D.5(c)** (MWG, p. 97). As `ρ → 1⁻` with `p₂ < p₁`, the CES demand converges to
`(0, w/p₂)`, which is the linear demand. -/
theorem exercise_3_D_5c_limit_linear_gt {p : Fin 2 → ℝ} (hp : StrictlyPositive p)
    (h10 : p 1 < p 0) {w : ℝ} (hw : 0 ≤ w) :
    Tendsto (fun ρ => cesDemand ρ p w) (𝓝[<] 1) (𝓝 ![0, w / p 1]) ∧
      walrasianDemand linearUtility2 p w = {![0, w / p 1]} := by
  obtain ⟨l1, l0⟩ := ces_two_good_limit (hp 1) h10 w
  refine ⟨tendsto_pi_nhds.2 fun j => ?_, ?_⟩
  · fin_cases j
    · refine (l0.comp cesR_tendsto_one_left).congr fun ρ => ?_
      simp [cesDemand, cesSum, add_comm]
    · refine (l1.comp cesR_tendsto_one_left).congr fun ρ => ?_
      simp [cesDemand, cesSum, add_comm]
  · ext x
    rw [(exercise_3_D_5c_linear hp hw x).1, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hx0, hpx, hcheap⟩
      have hx1 : x 0 = 0 := by
        rcases (hx0 0).lt_or_eq with h | h
        · exact absurd (hcheap 0 h 1) (not_le.2 h10)
        · exact h.symm
      have hpx' : p 0 * x 0 + p 1 * x 1 = w := by
        simpa [dotProduct, Fin.sum_univ_two] using hpx
      rw [hx1, mul_zero, zero_add] at hpx'
      funext j
      fin_cases j
      · simpa using hx1
      · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
        rw [← hpx']
        field_simp [(hp 1).ne']
    · rintro rfl
      refine ⟨fun j => ?_, ?_, fun i hi j => ?_⟩
      · fin_cases j
        · simp
        · exact div_nonneg hw (hp 1).le
      · simp [dotProduct, Fin.sum_univ_two]
        field_simp [(hp 1).ne']
      · fin_cases i
        · simp at hi
        · fin_cases j
          · exact h10.le
          · exact le_rfl

/-- **Exercise 3.D.5(c)** (MWG, p. 97). With `p₁ = p₂` the CES demand is `(w/(2p₁), w/(2p₁))`
for every `ρ`, an element of the linear demand correspondence. -/
theorem exercise_3_D_5c_limit_linear_eq {p : Fin 2 → ℝ} (hp : StrictlyPositive p)
    (h01 : p 0 = p 1) {w : ℝ} (hw : 0 ≤ w) (ρ : ℝ) :
    cesDemand ρ p w = (fun _ => w / (2 * p 0)) ∧
      cesDemand ρ p w ∈ walrasianDemand linearUtility2 p w := by
  have hd : cesDemand ρ p w = (fun _ => w / (2 * p 0)) := by
    funext j
    have h0 := Real.rpow_pos_of_pos (hp 0) (cesR ρ)
    have hj : p j = p 0 := by fin_cases j <;> simp [h01]
    simp only [cesDemand, cesSum, hj, ← h01, Real.rpow_sub_one (hp 0).ne']
    field_simp
    ring
  refine ⟨hd, ?_⟩
  rw [(exercise_3_D_5c_linear hp hw _).1, hd]
  refine ⟨fun _ => div_nonneg hw (by linarith [hp 0]), ?_, fun i _ j => ?_⟩
  · simp only [dotProduct, Fin.sum_univ_two, ← h01]
    field_simp [(hp 0).ne']
    ring
  · have hi : p i = p 0 := by fin_cases i <;> simp [h01]
    have hj : p j = p 0 := by fin_cases j <;> simp [h01]
    rw [hi, hj]

/-- **Exercise 3.D.5(c)** (MWG, p. 97). As `ρ → -∞`, the CES demand converges to the Leontief
demand `(w/(p₁+p₂), w/(p₁+p₂))`. -/
theorem exercise_3_D_5c_limit_leontief {p : Fin 2 → ℝ} (hp : StrictlyPositive p) (w : ℝ) :
    Tendsto (fun ρ => cesDemand ρ p w) atBot (𝓝 (leontiefDemand p w)) := by
  have hr := cesR_tendsto_atBot
  have hpow : ∀ j : Fin 2, ∀ c : ℝ,
      Tendsto (fun ρ => p j ^ (cesR ρ + c)) atBot (𝓝 (p j ^ (1 + c))) := fun j c =>
    (tendsto_const_nhds (x := p j)).rpow (hr.add_const c) (Or.inl (hp j).ne')
  refine tendsto_pi_nhds.2 fun j => ?_
  have hS : Tendsto (fun ρ => cesSum ρ p) atBot (𝓝 (p 0 + p 1)) := by
    have := (hpow 0 0).add (hpow 1 0)
    simpa [cesSum] using this
  have hnum := (hpow j (-1)).const_mul w
  have := hnum.div hS (add_pos (hp 0) (hp 1)).ne'
  simp only [add_neg_cancel, Real.rpow_zero, mul_one] at this
  refine this.congr fun ρ => ?_
  simp [cesDemand, sub_eq_add_neg]

/-- **Exercise 3.D.5(c)** (MWG, p. 97). As `ρ → -∞`, the CES indirect utility converges to the
Leontief indirect utility `w/(p₁+p₂)`. -/
theorem exercise_3_D_5c_limit_leontief_indirect {p : Fin 2 → ℝ} (hp : StrictlyPositive p)
    (w : ℝ) : Tendsto (fun ρ => cesIndirect ρ p w) atBot (𝓝 (w / (p 0 + p 1))) := by
  have hr := cesR_tendsto_atBot
  have hS : Tendsto (fun ρ => cesSum ρ p) atBot (𝓝 (p 0 + p 1)) := by
    have h0 := (tendsto_const_nhds (x := p 0)).rpow hr (Or.inl (hp 0).ne')
    have h1 := (tendsto_const_nhds (x := p 1)).rpow hr (Or.inl (hp 1).ne')
    simpa [cesSum] using h0.add h1
  have he : Tendsto (fun ρ : ℝ => 1 / ρ - 1) atBot (𝓝 (0 - 1)) := by
    simpa [one_div] using tendsto_inv_atBot_zero.sub_const (1 : ℝ)
  have := (hS.rpow he (Or.inl (add_pos (hp 0) (hp 1)).ne')).const_mul w
  rw [zero_sub, Real.rpow_neg_one, ← div_eq_mul_inv] at this
  exact this

/-- **Exercise 3.D.5(c)** (MWG, p. 97). As `ρ → 1⁻`, the CES indirect utility converges to the
linear indirect utility `w / min {p₁, p₂}`. -/
theorem exercise_3_D_5c_limit_linear_indirect {p : Fin 2 → ℝ} (hp : StrictlyPositive p)
    (w : ℝ) : Tendsto (fun ρ => cesIndirect ρ p w) (𝓝[<] 1) (𝓝 (w / min (p 0) (p 1))) := by
  have hmin := (exercise_3_C_6c one_pos one_pos (hp 0) (hp 1)).comp cesR_tendsto_one_left
  have hm0 : 0 < min (p 0) (p 1) := lt_min (hp 0) (hp 1)
  have := (hmin.inv₀ hm0.ne').const_mul w
  rw [← div_eq_mul_inv] at this
  apply this.congr'
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with ρ hρ
  have hρ0 : ρ ≠ 0 := hρ.1.ne'
  have hρ1 : ρ - 1 ≠ 0 := by linarith [hρ.2]
  have hS := cesSum_pos ρ hp
  have hexp : 1 / ρ - 1 = -(1 / cesR ρ) := by
    unfold cesR
    field_simp
    ring
  simp only [Function.comp_apply, one_mul, cesIndirect]
  rw [hexp, Real.rpow_neg hS.le]
  rfl

/-- **Exercise 3.D.5(d)** (MWG, p. 97). The elasticity of substitution of a demand-ratio function
`g(s)` of the price ratio `s = p₁/p₂`: `ξ = -g'(s) · s / g(s)`. -/
noncomputable def elasticityOfSubstitution (g : ℝ → ℝ) (s : ℝ) : ℝ := -(deriv g s) * s / g s

/-- **Exercise 3.D.5(d)** (MWG, p. 97). For the CES demand at `w > 0`,
`x₁(p, w)/x₂(p, w) = (p₁/p₂)^{r-1}`: a function of the price ratio. -/
theorem exercise_3_D_5d_ratio (ρ : ℝ) {p : Fin 2 → ℝ} (hp : StrictlyPositive p) {w : ℝ}
    (hw : 0 < w) : cesDemand ρ p w 0 / cesDemand ρ p w 1 = (p 0 / p 1) ^ (cesR ρ - 1) := by
  have hS := cesSum_pos ρ hp
  have h1 := Real.rpow_pos_of_pos (hp 1) (cesR ρ - 1)
  rw [Real.div_rpow (hp 0).le (hp 1).le]
  simp only [cesDemand]
  field_simp

/-- **Exercise 3.D.5(d)** (MWG, p. 97). For the CES utility, `ξ₁₂(p, w) = 1/(1 - ρ)`. -/
theorem exercise_3_D_5d {ρ : ℝ} (hρ1 : ρ < 1) {s : ℝ} (hs : 0 < s) :
    elasticityOfSubstitution (fun s => s ^ (cesR ρ - 1)) s = 1 / (1 - ρ) := by
  have hd := (Real.hasDerivAt_rpow_const (p := cesR ρ - 1) (Or.inl hs.ne')).deriv
  have hpos := Real.rpow_pos_of_pos hs (cesR ρ - 1)
  unfold elasticityOfSubstitution
  rw [hd, Real.rpow_sub_one hs.ne']
  have h1 : 1 - ρ ≠ 0 := by linarith
  have h2 : ρ - 1 ≠ 0 := by linarith
  unfold cesR
  field_simp
  ring

/-- **Exercise 3.D.5(d)** (MWG, p. 97). The CES elasticity `1/(1 - ρ)` tends to `∞` in the linear
limit `ρ → 1⁻` and to `0` in the Leontief limit `ρ → -∞` (and is `1` at the Cobb-Douglas
value `ρ = 0`). -/
theorem exercise_3_D_5d_limits :
    Tendsto (fun ρ : ℝ => 1 / (1 - ρ)) (𝓝[<] 1) atTop ∧
      Tendsto (fun ρ : ℝ => 1 / (1 - ρ)) atBot (𝓝 0) ∧ (1 : ℝ) / (1 - 0) = 1 := by
  refine ⟨?_, ?_, by norm_num⟩
  · have h1 : Tendsto (fun ρ : ℝ => 1 - ρ) (𝓝[<] 1) (𝓝[>] 0) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have : Tendsto (fun ρ : ℝ => 1 - ρ) (𝓝 1) (𝓝 (1 - 1)) :=
          (continuous_const.sub continuous_id).tendsto 1
        rw [sub_self] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with ρ hρ
        exact sub_pos.2 (Set.mem_Iio.1 hρ)
    exact (tendsto_inv_nhdsGT_zero.comp h1).congr fun ρ => by simp [one_div]
  · have h1 : Tendsto (fun ρ : ℝ => 1 - ρ) atBot atTop :=
      ((tendsto_const_nhds (x := (1 : ℝ))).add_atTop tendsto_neg_atBot_atTop).congr
        fun ρ => by ring
    exact (tendsto_inv_atTop_zero.comp h1).congr fun ρ => by simp [one_div]

/-- **Exercise 3.D.5(d)** (MWG, p. 97). Cobb-Douglas: `x₁/x₂ = (α/(1-α)) (p₁/p₂)^{-1}`, so
`ξ₁₂ = 1`. -/
theorem exercise_3_D_5d_cobbDouglas {α : ℝ} {p : Fin 2 → ℝ} (hp : StrictlyPositive p) {w : ℝ}
    (hw : 0 < w) (hα0 : 0 < α) (hα1 : α < 1) {s : ℝ} (hs : 0 < s) :
    cobbDouglasDemand α p w 0 / cobbDouglasDemand α p w 1 =
        (α / (1 - α)) * (p 0 / p 1)⁻¹ ∧
      elasticityOfSubstitution (fun s => (α / (1 - α)) * s⁻¹) s = 1 := by
  have h1 : 1 - α ≠ 0 := by linarith
  refine ⟨?_, ?_⟩
  · simp only [cobbDouglasDemand, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp [(hp 0).ne', (hp 1).ne', hw.ne']
  · have hd := ((hasDerivAt_inv hs.ne').const_mul (α / (1 - α))).deriv
    unfold elasticityOfSubstitution
    rw [hd]
    field_simp

/-- **Exercise 3.D.5(d)** (MWG, p. 97). Leontief: `x₁/x₂ = 1` whatever the prices, so
`ξ₁₂ = 0`. -/
theorem exercise_3_D_5d_leontief {p : Fin 2 → ℝ} (hp : StrictlyPositive p) {w : ℝ}
    (hw : 0 < w) (s : ℝ) :
    leontiefDemand p w 0 / leontiefDemand p w 1 = 1 ∧
      elasticityOfSubstitution (fun _ => (1 : ℝ)) s = 0 := by
  refine ⟨div_self (div_pos hw (add_pos (hp 0) (hp 1))).ne', ?_⟩
  simp [elasticityOfSubstitution]


/-- **Exercise 3.E.6** (MWG, p. 98). The CES expenditure function `e(p, ū) = ū S(p)^{1/r}`. -/
noncomputable def cesExpenditure (ρ : ℝ) (p : Fin 2 → ℝ) (ub : ℝ) : ℝ :=
  ub * cesSum ρ p ^ (1 / cesR ρ)

/-- **Exercise 3.E.6** (MWG, p. 98). The CES Hicksian demand `h(p, ū) = x(p, e(p, ū))`. -/
noncomputable def cesHicks (ρ : ℝ) (p : Fin 2 → ℝ) (ub : ℝ) : Fin 2 → ℝ :=
  cesDemand ρ p (cesExpenditure ρ p ub)

/-- **Exercise 3.E.6** (MWG, p. 98). Explicitly, `h_l(p, ū) = ū p_l^{r-1} S(p)^{1/r - 1}`. -/
theorem cesHicks_apply {ρ : ℝ} {p : Fin 2 → ℝ} (hp : StrictlyPositive p) (ub : ℝ) (l : Fin 2) :
    cesHicks ρ p ub l = ub * p l ^ (cesR ρ - 1) * cesSum ρ p ^ (1 / cesR ρ - 1) := by
  have hS := cesSum_pos ρ hp
  simp only [cesHicks, cesDemand, cesExpenditure, Real.rpow_sub_one hS.ne']
  ring

/-- `v(p, e(p, ū)) = ū`: `S^{1/r} S^{1/ρ - 1} = 1`. -/
theorem cesIndirect_cesExpenditure {ρ : ℝ} (hρ1 : ρ < 1) (hρ0 : ρ ≠ 0) {p : Fin 2 → ℝ}
    (hp : StrictlyPositive p) (ub : ℝ) : cesIndirect ρ p (cesExpenditure ρ p ub) = ub := by
  have hS := cesSum_pos ρ hp
  have he : 1 / cesR ρ + (1 / ρ - 1) = 0 := by
    have : ρ - 1 ≠ 0 := by linarith
    unfold cesR
    field_simp
    ring
  simp only [cesIndirect, cesExpenditure]
  rw [mul_assoc, ← Real.rpow_add hS, he, Real.rpow_zero, mul_one]

/-- For every `y ∈ ℝ²_+`, `u(y) ≤ v(p, p·y) = (p·y) S(p)^{1/ρ - 1}`. -/
theorem cesUtility_le_indirect {ρ : ℝ} (hρ1 : ρ < 1) (hρ0 : ρ ≠ 0) {p : Fin 2 → ℝ}
    (hp : StrictlyPositive p) {y : Fin 2 → ℝ} (hy : y ∈ nonnegOrthant 2) :
    cesUtility ρ y ≤ cesIndirect ρ p (p ⬝ᵥ y) := by
  have hpy : 0 ≤ p ⬝ᵥ y := Finset.sum_nonneg fun l _ => mul_nonneg (hp l).le (hy l)
  have hx : cesDemand ρ p (p ⬝ᵥ y) ∈ walrasianDemand (cesUtility ρ) p (p ⬝ᵥ y) := by
    rw [exercise_3_D_5a_demand hρ1 hρ0 hp hpy]; rfl
  rw [← cesUtility_cesDemand hρ1 hρ0 hp hpy]
  exact hx.2 y ⟨hy, le_rfl⟩

/-- **Exercise 3.E.6** (MWG, p. 98). For `ρ < 1`, `ρ ≠ 0`, `p ≫ 0` and `ū ≥ 0` (the range of
`u` on `ℝ²_+`), the CES Hicksian demand is the single bundle
`h(p, ū) = ū (p_l^{r-1}) S(p)^{1/r - 1}`. -/
theorem exercise_3_E_6_hicksian {ρ : ℝ} (hρ1 : ρ < 1) (hρ0 : ρ ≠ 0) {p : Fin 2 → ℝ}
    (hp : StrictlyPositive p) {ub : ℝ} (hub : 0 ≤ ub) :
    hicksianDemand (cesUtility ρ) p ub = {cesHicks ρ p ub} := by
  have hS := cesSum_pos ρ hp
  have hc : 0 < cesSum ρ p ^ (1 / ρ - 1) := Real.rpow_pos_of_pos hS _
  set W := cesExpenditure ρ p ub with hW
  have hW0 : 0 ≤ W := mul_nonneg hub (Real.rpow_nonneg hS.le _)
  have hdem := exercise_3_D_5a_demand hρ1 hρ0 hp hW0
  have hxu : cesUtility ρ (cesHicks ρ p ub) = ub := by
    rw [cesHicks, cesUtility_cesDemand hρ1 hρ0 hp hW0, cesIndirect_cesExpenditure hρ1 hρ0 hp]
  have hx0 : cesHicks ρ p ub ∈ nonnegOrthant 2 := exercise_3_D_5b_nonneg ρ hp hW0
  have hxp : p ⬝ᵥ cesHicks ρ p ub = W := exercise_3_D_5b_walras ρ hp W
  have hval : ub = W * cesSum ρ p ^ (1 / ρ - 1) := by
    have := cesIndirect_cesExpenditure hρ1 hρ0 hp ub
    rw [cesIndirect] at this
    exact this.symm
  have hcheap : ∀ z ∈ nonnegOrthant 2, ub ≤ cesUtility ρ z → W ≤ p ⬝ᵥ z := by
    intro z hz hzu
    have h := hzu.trans (cesUtility_le_indirect hρ1 hρ0 hp hz)
    rw [cesIndirect, hval] at h
    exact le_of_mul_le_mul_right h hc
  ext y
  rw [mem_hicksianDemand_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨hy0, hyu⟩, hmin⟩
    have hle : p ⬝ᵥ y ≤ W := hxp ▸ hmin _ hx0 hxu.ge
    have hy : y ∈ walrasianDemand (cesUtility ρ) p W := by
      refine ⟨⟨hy0, hle⟩, fun z hz => ?_⟩
      have hx : cesHicks ρ p ub ∈ walrasianDemand (cesUtility ρ) p W := by
        rw [hdem]; rfl
      exact (hx.2 z hz).trans (by rw [hxu]; exact hyu)
    rw [hdem] at hy
    exact hy
  · rintro rfl
    exact ⟨⟨hx0, hxu.ge⟩, fun z hz hzu => hxp ▸ hcheap z hz hzu⟩

/-- **Exercise 3.E.6** (MWG, p. 98). The CES expenditure function
`e(p, ū) = ū (p₁^r + p₂^r)^{1/r}` for `ū ≥ 0`. -/
theorem exercise_3_E_6_expenditure {ρ : ℝ} (hρ1 : ρ < 1) (hρ0 : ρ ≠ 0) {p : Fin 2 → ℝ}
    (hp : StrictlyPositive p) {ub : ℝ} (hub : 0 ≤ ub) :
    expenditure (cesUtility ρ) p ub = cesExpenditure ρ p ub := by
  have hx : cesHicks ρ p ub ∈ hicksianDemand (cesUtility ρ) p ub := by
    rw [exercise_3_E_6_hicksian hρ1 hρ0 hp hub]; rfl
  rw [expenditure_eq_of_mem hx, cesHicks, exercise_3_D_5b_walras ρ hp]

/-- **Exercise 3.E.6** (MWG, p. 98), Proposition 3.E.2(i): `e` is homogeneous of degree one in
`p`. -/
theorem exercise_3_E_6_homogeneous {ρ : ℝ} (hρ1 : ρ < 1) (hρ0 : ρ ≠ 0) {p : Fin 2 → ℝ}
    (hp : StrictlyPositive p) {ub : ℝ} (hub : 0 ≤ ub) {α : ℝ} (hα : 0 < α) :
    cesExpenditure ρ (α • p) ub = α * cesExpenditure ρ p ub := by
  rw [← exercise_3_E_6_expenditure hρ1 hρ0 (cesSum_smul ρ hp hα).1 hub,
    ← exercise_3_E_6_expenditure hρ1 hρ0 hp hub]
  exact proposition_3_E_2_i _ p ub hα

/-- **Exercise 3.E.6** (MWG, p. 98), Proposition 3.E.2(ii): `e` is strictly increasing in `ū`
and nondecreasing in each price. -/
theorem exercise_3_E_6_monotone {ρ : ℝ} (hρ1 : ρ < 1) (hρ0 : ρ ≠ 0) {p p' : Fin 2 → ℝ}
    (hp : StrictlyPositive p) (hpp : p ≤ p') {ub ub' : ℝ} (hub : 0 ≤ ub) (hlt : ub < ub') :
    cesExpenditure ρ p ub < cesExpenditure ρ p ub' ∧
      cesExpenditure ρ p ub ≤ cesExpenditure ρ p' ub := by
  have hp' : StrictlyPositive p' := fun l => lt_of_lt_of_le (hp l) (hpp l)
  refine ⟨mul_lt_mul_of_pos_right hlt (Real.rpow_pos_of_pos (cesSum_pos ρ hp) _), ?_⟩
  rw [← exercise_3_E_6_expenditure hρ1 hρ0 hp hub, ← exercise_3_E_6_expenditure hρ1 hρ0 hp' hub]
  exact proposition_3_E_2_ii_prices _ hp hpp ub

/-- **Exercise 3.E.6** (MWG, p. 98), Proposition 3.E.2(iii): `e` is concave in `p`. -/
theorem exercise_3_E_6_concave {ρ : ℝ} (hρ1 : ρ < 1) (hρ0 : ρ ≠ 0) {ub : ℝ} (hub : 0 ≤ ub) :
    ConcaveOn ℝ {p : Fin 2 → ℝ | StrictlyPositive p} (fun p => cesExpenditure ρ p ub) :=
  (proposition_3_E_2_iii (cesUtility ρ) ub).congr fun _ hp =>
    exercise_3_E_6_expenditure hρ1 hρ0 hp hub

/-- **Exercise 3.E.6** (MWG, p. 98), Proposition 3.E.2(iv): `e` is continuous in `(p, ū)` on
`{p ≫ 0} × ℝ`. -/
theorem exercise_3_E_6_continuous (ρ : ℝ) :
    ContinuousOn (fun q : (Fin 2 → ℝ) × ℝ => cesExpenditure ρ q.1 q.2)
      {q | StrictlyPositive q.1} := by
  intro q hq
  have hS := cesSum_pos ρ hq
  apply ContinuousAt.continuousWithinAt
  have hsum : ContinuousAt (fun q : (Fin 2 → ℝ) × ℝ => cesSum ρ q.1) q := by
    have h0 : ContinuousAt (fun q : (Fin 2 → ℝ) × ℝ => q.1 0 ^ cesR ρ) q :=
      ((continuous_apply 0).comp continuous_fst).continuousAt.rpow_const (Or.inl (hq 0).ne')
    have h1 : ContinuousAt (fun q : (Fin 2 → ℝ) × ℝ => q.1 1 ^ cesR ρ) q :=
      ((continuous_apply 1).comp continuous_fst).continuousAt.rpow_const (Or.inl (hq 1).ne')
    exact h0.add h1
  exact continuous_snd.continuousAt.mul (hsum.rpow_const (Or.inl hS.ne'))

/-- **Exercise 3.E.6** (MWG, p. 98), Proposition 3.E.3: `h` is homogeneous of degree zero in
`p`, has no excess utility (`u(h(p, ū)) = ū`) and is single-valued
(`exercise_3_E_6_hicksian`). -/
theorem exercise_3_E_6_hicks_properties {ρ : ℝ} (hρ1 : ρ < 1) (hρ0 : ρ ≠ 0) {p : Fin 2 → ℝ}
    (hp : StrictlyPositive p) {ub : ℝ} (hub : 0 ≤ ub) {α : ℝ} (hα : 0 < α) :
    cesHicks ρ (α • p) ub = cesHicks ρ p ub ∧ cesUtility ρ (cesHicks ρ p ub) = ub := by
  refine ⟨?_, ?_⟩
  · have h := proposition_3_E_3_i (cesUtility ρ) p ub hα
    rw [exercise_3_E_6_hicksian hρ1 hρ0 (cesSum_smul ρ hp hα).1 hub,
      exercise_3_E_6_hicksian hρ1 hρ0 hp hub] at h
    exact Set.singleton_eq_singleton_iff.1 h
  · have hS := cesSum_pos ρ hp
    have hW : 0 ≤ cesExpenditure ρ p ub := mul_nonneg hub (Real.rpow_nonneg hS.le _)
    rw [cesHicks, cesUtility_cesDemand hρ1 hρ0 hp hW, cesIndirect_cesExpenditure hρ1 hρ0 hp]

end MWG.ClassicalDemand
