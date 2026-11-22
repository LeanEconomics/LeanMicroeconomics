/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGAdverseSelection.Uniform
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Exercise 13.C.4: signaling with a continuum of types

MWG, Exercise 13.C.4, p. 475. Types are distributed on `[θ̲, θ̄]` (`0 < θ̲`) with a positive
density; education costs `c(e, θ) = e²/θ`; `r = 0`. The exercise asks for "the (unique)
perfect Bayesian equilibrium".

As in Section 13.C the competing firms pay the expected productivity under their beliefs
(`bertrand_wage`), so a PBE is described by the education strategy `e*(θ)` and the wage
schedule `w(e)`, the mean of the firms' belief after `e` (`IsPBEC4`): every wage lies in
`[θ̲, θ̄]` (off the path any such mean is the mean of some belief), each type's education is
optimal, and on the path the wage is the conditional mean of the types choosing `e`, or, when
these have probability zero, the mean of a belief concentrated on them.

* `exercise_13_C_4_separating`: `e*(θ) = √((θ² - θ̲²)/2)` with `w(e) = min(√(2e² + θ̲²), θ̄)` is
  a separating PBE.
* `exercise_13_C_4_pooling`: everybody choosing `e = 0`, paid `E[θ]`, with wage `θ̲` after any
  `e > 0`, is also a PBE. The PBE is not unique (`exercise_13_C_4_not_unique`, instance
  `exercise_13_C_4_instance` with types uniform on `[1, 2]`).
* Corrected statement, `exercise_13_C_4_unique_separating`: every separating PBE (`e*`
  injective) has `e*(θ) = √((θ² - θ̲²)/2)` and wage `θ` for type `θ`.
-/

namespace MWG.AdverseSelection

open MeasureTheory

/-- **Exercise 13.C.4** (MWG, p. 475). A pure strategy PBE of the continuum-of-types signaling
game with cost `e²/θ`, in reduced form: the education strategy `eS` and the wage schedule `w`
(the mean of the firms' belief). -/
def IsPBEC4 (μ : Measure ℝ) (θl θh : ℝ) (eS w : ℝ → ℝ) : Prop :=
  (∀ θ ∈ Set.Icc θl θh, 0 ≤ eS θ) ∧ (∀ e, 0 ≤ e → θl ≤ w e ∧ w e ≤ θh) ∧
    (∀ θ ∈ Set.Icc θl θh, ∀ e, 0 ≤ e → w e - e ^ 2 / θ ≤ w (eS θ) - eS θ ^ 2 / θ) ∧
    ∀ e, (∃ θ ∈ Set.Icc θl θh, eS θ = e) →
      (0 < μ {θ | θ ∈ Set.Icc θl θh ∧ eS θ = e} →
        w e = condMean μ θl θh {θ | θ ∈ Set.Icc θl θh ∧ eS θ = e}) ∧
      (μ {θ | θ ∈ Set.Icc θl θh ∧ eS θ = e} = 0 →
        ∃ θ₁ ∈ {θ | θ ∈ Set.Icc θl θh ∧ eS θ = e}, ∃ θ₂ ∈ {θ | θ ∈ Set.Icc θl θh ∧ eS θ = e},
          θ₁ ≤ w e ∧ w e ≤ θ₂)

/-- **Exercise 13.C.4**. The separating education strategy `√((θ² - θ̲²)/2)`. -/
noncomputable def sepEduc (θl : ℝ) (θ : ℝ) : ℝ := Real.sqrt ((θ ^ 2 - θl ^ 2) / 2)

/-- **Exercise 13.C.4**. The separating wage schedule `min(√(2e² + θ̲²), θ̄)`. -/
noncomputable def sepWage (θl θh : ℝ) (e : ℝ) : ℝ := min (Real.sqrt (2 * e ^ 2 + θl ^ 2)) θh

theorem sepEduc_sq {θl θ : ℝ} (h0 : 0 ≤ θl) (h : θl ≤ θ) :
    sepEduc θl θ ^ 2 = (θ ^ 2 - θl ^ 2) / 2 :=
  Real.sq_sqrt (by nlinarith)

theorem sepWage_sepEduc {θl θh θ : ℝ} (h0 : 0 ≤ θl) (h : θ ∈ Set.Icc θl θh) :
    sepWage θl θh (sepEduc θl θ) = θ := by
  unfold sepWage
  rw [sepEduc_sq h0 h.1, show 2 * ((θ ^ 2 - θl ^ 2) / 2) + θl ^ 2 = θ ^ 2 by ring,
    Real.sqrt_sq (h0.trans h.1)]
  exact min_eq_left h.2

theorem sepEduc_injOn {θl θh : ℝ} (h0 : 0 ≤ θl) : Set.InjOn (sepEduc θl) (Set.Icc θl θh) := by
  intro θ hθ θ' hθ' he
  have h1 := sepEduc_sq h0 hθ.1
  have h2 := sepEduc_sq h0 hθ'.1
  rw [he] at h1
  nlinarith [hθ.1, hθ'.1]

/-- **Exercise 13.C.4** (MWG, p. 475). The separating PBE. -/
theorem exercise_13_C_4_separating {μ : Measure ℝ} {θl θh : ℝ} (hden : HasPosDensity μ θl θh)
    (hθl : 0 < θl) (hlt : θl < θh) :
    IsPBEC4 μ θl θh (sepEduc θl) (sepWage θl θh) := by
  refine ⟨fun θ _ => Real.sqrt_nonneg _, fun e _ => ⟨?_, min_le_right _ _⟩, ?_, ?_⟩
  · refine le_min ?_ hlt.le
    calc θl = Real.sqrt (θl ^ 2) := (Real.sqrt_sq hθl.le).symm
      _ ≤ Real.sqrt (2 * e ^ 2 + θl ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg e])
  · intro θ hθ e he
    have hθ0 : 0 < θ := hθl.trans_le hθ.1
    rw [sepWage_sepEduc hθl.le hθ, sepEduc_sq hθl.le hθ.1]
    set v := sepWage θl θh e
    have hv2 : v ^ 2 ≤ 2 * e ^ 2 + θl ^ 2 := by
      have hv0 : 0 ≤ v := le_min (Real.sqrt_nonneg _) (hθl.le.trans hlt.le)
      have hvs : v ≤ Real.sqrt (2 * e ^ 2 + θl ^ 2) := min_le_left _ _
      calc v ^ 2 ≤ Real.sqrt (2 * e ^ 2 + θl ^ 2) ^ 2 := pow_le_pow_left₀ hv0 hvs 2
        _ = 2 * e ^ 2 + θl ^ 2 := Real.sq_sqrt (by positivity)
    have hkey : v - e ^ 2 / θ ≤ θ - (θ ^ 2 - θl ^ 2) / 2 / θ := by
      rw [← sub_nonneg]
      have : θ - (θ ^ 2 - θl ^ 2) / 2 / θ - (v - e ^ 2 / θ) =
          ((θ - v) ^ 2 + (2 * e ^ 2 + θl ^ 2 - v ^ 2)) / (2 * θ) := by
        field_simp; ring
      rw [this]
      exact div_nonneg (by nlinarith [sq_nonneg (θ - v)]) (by linarith)
    exact hkey
  · rintro e ⟨θ0, hθ0, rfl⟩
    have hP : {θ | θ ∈ Set.Icc θl θh ∧ sepEduc θl θ = sepEduc θl θ0} = {θ0} := by
      ext θ
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hθ, he⟩; exact sepEduc_injOn hθl.le hθ hθ0 he
      · rintro rfl; exact ⟨hθ0, rfl⟩
    rw [hP, hden.noAtom θ0]
    refine ⟨fun h => absurd h (lt_irrefl _), fun _ => ⟨θ0, rfl, θ0, rfl, ?_⟩⟩
    rw [sepWage_sepEduc hθl.le hθ0]
    exact ⟨le_rfl, le_rfl⟩

/-- **Exercise 13.C.4**. The pooling wage schedule: `E[θ]` at `e = 0`, `θ̲` after any `e ≠ 0`. -/
noncomputable def poolWage (μ : Measure ℝ) (θl : ℝ) (e : ℝ) : ℝ := if e = 0 then meanType μ else θl

/-- **Exercise 13.C.4** (MWG, p. 475). Everybody choosing `e = 0` is also a PBE: firms pay
`E[θ]` at `e = 0` and believe any `e > 0` comes from type `θ̲`. -/
theorem exercise_13_C_4_pooling {μ : Measure ℝ} {θl θh : ℝ} (hd : TypeDist μ θl θh)
    (hθl : 0 < θl) : IsPBEC4 μ θl θh (fun _ => 0) (poolWage μ θl) := by
  have hm := hd.meanType_mem
  refine ⟨fun _ _ => le_rfl, fun e _ => ?_, fun θ hθ e he => ?_, ?_⟩
  · unfold poolWage; split_ifs
    · exact hm
    · exact ⟨le_rfl, hd.lt.le⟩
  · have hθ0 : 0 < θ := hθl.trans_le hθ.1
    simp only [poolWage, ↓reduceIte]
    split_ifs with he0
    · subst he0; simp
    · have : 0 ≤ e ^ 2 / θ := by positivity
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, sub_zero]
      linarith [hm.1]
  · rintro e ⟨θ0, hθ0, rfl⟩
    have hP : {θ | θ ∈ Set.Icc θl θh ∧ (fun _ : ℝ => (0 : ℝ)) θ = (fun _ : ℝ => (0 : ℝ)) θ0} =
        Set.Icc θl θh := by
      ext θ; simp
    rw [hP]
    refine ⟨fun _ => ?_, fun _ => ⟨θl, ⟨le_rfl, hd.lt.le⟩, θh, ⟨hd.lt.le, le_rfl⟩, ?_⟩⟩
    · simp only [poolWage, ↓reduceIte]
      exact (condMean_of_superset hd subset_rfl).symm
    · simp only [poolWage, ↓reduceIte]; exact hm

/-- **Exercise 13.C.4** (MWG, p. 475). The PBE is not unique: the separating and the pooling
PBE differ (the highest type's education). -/
theorem exercise_13_C_4_not_unique {θl θh : ℝ} (hθl : 0 < θl) (hlt : θl < θh) :
    sepEduc θl θh ≠ 0 := by
  intro h
  have := sepEduc_sq hθl.le hlt.le
  rw [h] at this
  nlinarith

/-- A function on `[a, b]` with `|f x - f y| ≤ (x - y)²` is constant. -/
theorem eq_of_sq_bound {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, |f x - f y| ≤ (x - y) ^ 2) : f b = f a := by
  have key : ∀ n : ℕ, 0 < n → |f b - f a| ≤ (b - a) ^ 2 / n := by
    intro n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    set h := (b - a) / n with hhdef
    have hh : 0 ≤ h := div_nonneg (by linarith) hn'.le
    have hnh : (n : ℝ) * h = b - a := by rw [hhdef]; field_simp
    have ind : ∀ k : ℕ, k ≤ n → |f (a + k * h) - f a| ≤ k * h ^ 2 := by
      intro k
      induction k with
      | zero => intro _; simp
      | succ k ih =>
        intro hk
        have hk' : (k : ℝ) + 1 ≤ n := by exact_mod_cast hk
        have ih' := ih (Nat.le_of_succ_le hk)
        have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        have hmem1 : a + ((k : ℝ) + 1) * h ∈ Set.Icc a b :=
          ⟨by nlinarith, by nlinarith⟩
        have hmem2 : a + (k : ℝ) * h ∈ Set.Icc a b := ⟨by nlinarith, by nlinarith⟩
        have hstep := hf _ hmem1 _ hmem2
        rw [show a + ((k : ℝ) + 1) * h - (a + k * h) = h by ring] at hstep
        push_cast
        calc |f (a + ((k : ℝ) + 1) * h) - f a|
            ≤ |f (a + ((k : ℝ) + 1) * h) - f (a + k * h)| + |f (a + k * h) - f a| :=
              abs_sub_le _ _ _
          _ ≤ h ^ 2 + k * h ^ 2 := add_le_add hstep ih'
          _ = ((k : ℝ) + 1) * h ^ 2 := by ring
    have := ind n le_rfl
    rw [hnh, show a + (b - a) = b by ring] at this
    calc |f b - f a| ≤ n * h ^ 2 := this
      _ = (b - a) ^ 2 / n := by rw [hhdef]; field_simp
  by_contra hne
  have hd : 0 < |f b - f a| := abs_pos.2 (sub_ne_zero.2 hne)
  obtain ⟨n, hn⟩ := exists_nat_gt ((b - a) ^ 2 / |f b - f a|)
  have hn0 : (0 : ℝ) < n := lt_of_le_of_lt (by positivity) hn
  have h1 := key n (by exact_mod_cast hn0)
  rw [div_lt_iff₀ hd] at hn
  rw [le_div_iff₀ hn0] at h1
  linarith

/-- **Exercise 13.C.4** (MWG, p. 475), corrected statement: every separating PBE (`e*` one-to-one
on `[θ̲, θ̄]`) has `e*(θ) = √((θ² - θ̲²)/2)`, and type `θ` is paid `θ`. -/
theorem exercise_13_C_4_unique_separating {μ : Measure ℝ} {θl θh : ℝ}
    (hden : HasPosDensity μ θl θh) (hθl : 0 < θl) {eS w : ℝ → ℝ} (h : IsPBEC4 μ θl θh eS w)
    (hinj : Set.InjOn eS (Set.Icc θl θh)) :
    ∀ θ ∈ Set.Icc θl θh, eS θ = sepEduc θl θ ∧ w (eS θ) = θ := by
  obtain ⟨hpos, hw, hic, hbayes⟩ := h
  -- each type is paid her productivity
  have hpay : ∀ θ ∈ Set.Icc θl θh, w (eS θ) = θ := by
    intro θ hθ
    have hP : {θ' | θ' ∈ Set.Icc θl θh ∧ eS θ' = eS θ} = {θ} := by
      ext θ'
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hθ', he⟩; exact hinj hθ' hθ he
      · rintro rfl; exact ⟨hθ, rfl⟩
    obtain ⟨θ₁, h₁, θ₂, h₂, hle1, hle2⟩ := (hbayes (eS θ) ⟨θ, hθ, rfl⟩).2
      (by rw [hP]; exact hden.noAtom θ)
    rw [hP] at h₁ h₂
    rw [Set.mem_singleton_iff] at h₁ h₂
    subst h₁ h₂
    exact le_antisymm hle2 hle1
  -- incentive compatibility in terms of `E(θ) = e*(θ)²`
  have hIC : ∀ θ ∈ Set.Icc θl θh, ∀ θ' ∈ Set.Icc θl θh,
      eS θ ^ 2 - eS θ' ^ 2 ≤ θ * (θ - θ') := by
    intro θ hθ θ' hθ'
    have hθ0 : 0 < θ := hθl.trans_le hθ.1
    have := hic θ hθ (eS θ') (hpos θ' hθ')
    rw [hpay θ hθ, hpay θ' hθ'] at this
    have h1 : eS θ' ^ 2 / θ * θ = eS θ' ^ 2 := div_mul_cancel₀ _ hθ0.ne'
    have h2 : eS θ ^ 2 / θ * θ = eS θ ^ 2 := div_mul_cancel₀ _ hθ0.ne'
    nlinarith
  -- `D(θ) = E(θ) - θ²/2` is constant
  set D : ℝ → ℝ := fun θ => eS θ ^ 2 - θ ^ 2 / 2 with hD
  have hDb : ∀ x ∈ Set.Icc θl θh, ∀ y ∈ Set.Icc θl θh, |D x - D y| ≤ (x - y) ^ 2 := by
    intro x hx y hy
    have h1 := hIC x hx y hy
    have h2 := hIC y hy x hx
    rw [abs_le]
    simp only [hD]
    constructor <;> nlinarith [sq_nonneg (x - y)]
  -- the lowest type does not signal
  have hlow : eS θl = 0 := by
    have hl : θl ∈ Set.Icc θl θh := ⟨le_rfl, (hw 0 le_rfl).1.trans (hw 0 le_rfl).2⟩
    have := hic θl hl 0 le_rfl
    rw [hpay θl hl] at this
    have hw0 := (hw 0 le_rfl).1
    have hq : 0 ≤ eS θl ^ 2 / θl := by positivity
    have hz : eS θl ^ 2 / θl ≤ 0 := by
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
        sub_zero] at this
      linarith
    have : eS θl ^ 2 = 0 := by
      have := le_antisymm hz hq
      rwa [div_eq_zero_iff, or_iff_left hθl.ne'] at this
    exact pow_eq_zero_iff (two_ne_zero) |>.1 this
  intro θ hθ
  refine ⟨?_, hpay θ hθ⟩
  have hc : D θ = D θl := eq_of_sq_bound hθ.1 fun x hx y hy =>
    hDb x ⟨hx.1, hx.2.trans hθ.2⟩ y ⟨hy.1, hy.2.trans hθ.2⟩
  simp only [hD, hlow] at hc
  have hsq : eS θ ^ 2 = (θ ^ 2 - θl ^ 2) / 2 := by linarith
  unfold sepEduc
  rw [← hsq, Real.sqrt_sq (hpos θ hθ)]

/-- **Exercise 13.C.4**, an instance: with types uniform on `[1, 2]` both the separating and the
pooling PBE exist, so "the (unique) PBE" is false. -/
theorem exercise_13_C_4_instance :
    IsPBEC4 (unifMeas 1 2) 1 2 (sepEduc 1) (sepWage 1 2) ∧
      IsPBEC4 (unifMeas 1 2) 1 2 (fun _ => 0) (poolWage (unifMeas 1 2) 1) ∧
      sepEduc 1 2 ≠ 0 :=
  ⟨exercise_13_C_4_separating (unifMeas_density (by norm_num)) one_pos (by norm_num),
    exercise_13_C_4_pooling (unifMeas_typeDist zero_le_one (by norm_num)) one_pos,
    exercise_13_C_4_not_unique one_pos (by norm_num)⟩

end MWG.AdverseSelection
