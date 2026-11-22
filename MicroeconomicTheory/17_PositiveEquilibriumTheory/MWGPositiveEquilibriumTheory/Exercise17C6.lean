/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.Exercise17B3

/-!
# Exercise 17.C.6: each condition of Proposition 17.B.2 is needed (MWG p. 644)

The exercise asks, for `L = 2`, for four examples in each of which exactly one of the conditions
(i), (iii), (iv), (v) of Proposition 17.B.2 fails (the printed list reads "(i), (iii), and (iv)",
but asks for four examples; the fourth condition is (v)) and `z(p) = 0` has no solution, and asks
why (ii) is not in the list. All four examples are homogeneous of degree zero and are written
with `t = p₁/p₂`.

* (i) fails: `ex17C6NotCont`, `z(p) = (p₂/p₁, -1)` if `p₁ ≤ p₂` and `(-1, p₁/p₂)` otherwise
  (`exercise_17_C_6_i`).
* (iii) fails: `ex17C6NotWalras`, `z(p) = (p₂/p₁, p₁/p₂)` (`exercise_17_C_6_iii`).
* (iv) fails: `ex17C6NotBdd`, `z(p) = (p₂/p₁ + p₁/p₂, -(1 + (p₁/p₂)²))` (`exercise_17_C_6_iv`).
* (v) fails: `ex17C6NotBdry`, `z(p) = (p₂, -p₁)/(p₁ + p₂)` (`exercise_17_C_6_v`).
* Why not (ii): conditions (i), (iii), (iv), (v) alone already give an equilibrium, for every
  `L`: `z(p/∑ₗ pₗ)` satisfies (i)-(v) (`homogenize_isStandard`), so Proposition 17.C.1 applies
  (`exercise_17_C_6_ii`). No example can violate only (ii).

`edBoundary_two` is a sufficient condition for (v) with two goods.
-/

namespace MWG.PositiveEquilibriumTheory

open Filter Topology

/-- A sufficient condition for the boundary condition (v) with two goods: some excess demand is
large whenever `p₁/p₂` or `p₂/p₁` is small. -/
theorem edBoundary_two {z : (Fin 2 → ℝ) → Fin 2 → ℝ}
    (h0 : ∀ M : ℝ, ∃ δ > 0, ∀ p ∈ posOrthant 2, p 0 < δ * p 1 → ∃ l, M < z p l)
    (h1 : ∀ M : ℝ, ∃ δ > 0, ∀ p ∈ posOrthant 2, p 1 < δ * p 0 → ∃ l, M < z p l) :
    EDBoundary z := by
  intro ps p hps hlim hp0 hpl M
  have hnn := nonneg_of_tendsto_pos hps hlim
  have hc : ∀ k, Tendsto (fun n => ps n k) atTop (𝓝 (p k)) := fun k =>
    ((continuous_apply k).tendsto p).comp hlim
  obtain ⟨l, hl⟩ := hpl
  have hne : ∀ k, p k = 0 → ∀ k', k' ≠ k → 0 < p k' := by
    intro k hk k' hk'
    rcases (hnn k').lt_or_eq with h | h
    · exact h
    · exfalso
      apply hp0
      funext j
      fin_cases j <;> fin_cases k <;> fin_cases k' <;> simp_all
  fin_cases l
  · have hl' : p 0 = 0 := hl
    have hp1 := hne 0 hl' 1 (by decide)
    obtain ⟨δ, hδ, hM⟩ := h0 M
    have ht : Tendsto (fun n => ps n 0 - δ * ps n 1) atTop (𝓝 (p 0 - δ * p 1)) :=
      (hc 0).sub ((hc 1).const_mul δ)
    have hneg : p 0 - δ * p 1 < 0 := by rw [hl']; nlinarith
    filter_upwards [ht.eventually (gt_mem_nhds hneg)] with n hn
    exact hM _ (hps n) (by linarith)
  · have hl' : p 1 = 0 := hl
    have hp0' := hne 1 hl' 0 (by decide)
    obtain ⟨δ, hδ, hM⟩ := h1 M
    have ht : Tendsto (fun n => ps n 1 - δ * ps n 0) atTop (𝓝 (p 1 - δ * p 0)) :=
      (hc 1).sub ((hc 0).const_mul δ)
    have hneg : p 1 - δ * p 0 < 0 := by rw [hl']; nlinarith
    filter_upwards [ht.eventually (gt_mem_nhds hneg)] with n hn
    exact hM _ (hps n) (by linarith)

/-- `1/δ` beats `M` for `δ = 1/(|M| + 1)`: if `0 < a < δ b` then `M < b/a`. -/
theorem ex17C6_ratio_large {M a b : ℝ} (ha : 0 < a) (hab : a < 1 / (|M| + 1) * b) :
    M < b / a := by
  have hM : 0 < |M| + 1 := by positivity
  rw [lt_div_iff₀ ha]
  have h1 : a * (|M| + 1) < b := by
    have := mul_lt_mul_of_pos_right hab hM
    rwa [show 1 / (|M| + 1) * b * (|M| + 1) = b by field_simp] at this
  nlinarith [le_abs_self M, abs_nonneg M]

/-! ### Condition (i) fails -/

open Classical in
/-- **Exercise 17.C.6**, the example violating only (i): `z(p) = (p₂/p₁, -1)` if `p₁ ≤ p₂`,
`z(p) = (-1, p₁/p₂)` if `p₁ > p₂`. -/
noncomputable def ex17C6NotCont (p : Fin 2 → ℝ) : Fin 2 → ℝ :=
  if p 0 ≤ p 1 then ![p 1 / p 0, -1] else ![-1, p 0 / p 1]

/-- **Exercise 17.C.6** (MWG, p. 644), condition (i). `ex17C6NotCont` satisfies (ii)-(v) but is
discontinuous (at `(1, 1)`), and `z(p) = 0` has no solution. -/
theorem exercise_17_C_6_i :
    EDHomogeneous ex17C6NotCont ∧ EDWalrasLaw ex17C6NotCont ∧ EDBoundedBelow ex17C6NotCont ∧
      EDBoundary ex17C6NotCont ∧ ¬ EDContinuous ex17C6NotCont ∧
      ∀ p, ¬ IsEqmPrice ex17C6NotCont p := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp α hα
    have h0 := (hp 0).ne'
    have h1 := (hp 1).ne'
    have hiff : α * p 0 ≤ α * p 1 ↔ p 0 ≤ p 1 := mul_le_mul_iff_right₀ hα
    unfold ex17C6NotCont
    simp only [Pi.smul_apply, smul_eq_mul, hiff]
    split_ifs
    · rw [mul_div_mul_left _ _ hα.ne']
    · rw [mul_div_mul_left _ _ hα.ne']
  · intro p hp
    have h0 := (hp 0).ne'
    have h1 := (hp 1).ne'
    unfold ex17C6NotCont
    split_ifs <;> simp [dotProduct, Fin.sum_univ_two] <;> field_simp <;> ring
  · refine ⟨2, two_pos, fun p hp l => ?_⟩
    have hq0 : 0 < p 1 / p 0 := div_pos (hp 1) (hp 0)
    have hq1 : 0 < p 0 / p 1 := div_pos (hp 0) (hp 1)
    unfold ex17C6NotCont
    split_ifs <;> fin_cases l <;> simp <;> linarith
  · refine edBoundary_two (fun M => ⟨1 / (|M| + 1), by positivity, fun p hp h => ⟨0, ?_⟩⟩)
      (fun M => ⟨1 / (|M| + 1), by positivity, fun p hp h => ⟨1, ?_⟩⟩)
    · have hle : p 0 ≤ p 1 := by
        have : 1 / (|M| + 1) ≤ 1 := by
          rw [div_le_one (by positivity)]; linarith [abs_nonneg M]
        nlinarith [hp 1]
      simp only [ex17C6NotCont, hle, ↓reduceIte, Matrix.cons_val_zero]
      exact ex17C6_ratio_large (hp 0) h
    · have hle : ¬ p 0 ≤ p 1 := by
        have : 1 / (|M| + 1) ≤ 1 := by
          rw [div_le_one (by positivity)]; linarith [abs_nonneg M]
        nlinarith [hp 0]
      simp only [ex17C6NotCont, hle, ↓reduceIte, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      exact ex17C6_ratio_large (hp 1) h
  · intro hc
    have hvec : Continuous fun t : ℝ => (![t, 1] : Fin 2 → ℝ) := by
      refine continuous_pi fun l => ?_
      fin_cases l
      · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
        exact continuous_id'
      · simpa using continuous_const
    have hat : ContinuousAt ex17C6NotCont ![1, 1] :=
      hc.continuousAt ((isOpen_posOrthant 2).mem_nhds (vec2_mem_posOrthant one_pos one_pos))
    have hg : ContinuousAt (fun t : ℝ => ex17C6NotCont ![t, 1] 0) 1 :=
      (continuous_apply 0).continuousAt.comp (ContinuousAt.comp (g := ex17C6NotCont)
        (f := fun t : ℝ => (![t, 1] : Fin 2 → ℝ)) hat hvec.continuousAt)
    have hval : ex17C6NotCont ![1, 1] 0 = 1 := by simp [ex17C6NotCont]
    have hev : ∀ᶠ t in 𝓝 (1 : ℝ), 0 < ex17C6NotCont ![t, 1] 0 :=
      hg.eventually (lt_mem_nhds (by simp only at hval ⊢; rw [hval]; exact one_pos))
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
    have hd : dist (1 + ε / 2) (1 : ℝ) < ε := by
      rw [Real.dist_eq, show 1 + ε / 2 - 1 = ε / 2 by ring, abs_of_pos (by positivity)]
      linarith
    have h := hball hd
    have hnot : ¬ (1 + ε / 2 ≤ (1 : ℝ)) := by linarith
    simp [ex17C6NotCont, hnot] at h
    linarith
  · rintro p ⟨-, hz⟩
    have h := congrFun hz 0
    have h' := congrFun hz 1
    unfold ex17C6NotCont at h h'
    split_ifs at h h' <;> simp at h h'

/-! ### Condition (iii) fails -/

/-- **Exercise 17.C.6**, the example violating only (iii): `z(p) = (p₂/p₁, p₁/p₂)`. -/
noncomputable def ex17C6NotWalras (p : Fin 2 → ℝ) : Fin 2 → ℝ := ![p 1 / p 0, p 0 / p 1]

/-- **Exercise 17.C.6** (MWG, p. 644), condition (iii). `ex17C6NotWalras` satisfies (i), (ii),
(iv), (v) but not Walras' law, and `z(p) = 0` has no solution (excess demand is positive). -/
theorem exercise_17_C_6_iii :
    EDContinuous ex17C6NotWalras ∧ EDHomogeneous ex17C6NotWalras ∧
      EDBoundedBelow ex17C6NotWalras ∧ EDBoundary ex17C6NotWalras ∧
      ¬ EDWalrasLaw ex17C6NotWalras ∧ ∀ p, ¬ IsEqmPrice ex17C6NotWalras p := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine continuousOn_pi.2 fun l => ?_
    fin_cases l
    · simp only [ex17C6NotWalras, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      exact (continuous_apply 1).continuousOn.div (continuous_apply 0).continuousOn
        fun p hp => (hp 0).ne'
    · simp only [ex17C6NotWalras, Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
      exact (continuous_apply 0).continuousOn.div (continuous_apply 1).continuousOn
        fun p hp => (hp 1).ne'
  · intro p hp α hα
    funext l
    fin_cases l <;> simp [ex17C6NotWalras, mul_div_mul_left _ _ hα.ne']
  · refine ⟨1, one_pos, fun p hp l => ?_⟩
    have h0 := hp 0
    have h1 := hp 1
    have : 0 < ex17C6NotWalras p l := by
      fin_cases l
      · exact div_pos h1 h0
      · exact div_pos h0 h1
    linarith
  · exact edBoundary_two (fun M => ⟨1 / (|M| + 1), by positivity, fun p hp h =>
      ⟨0, by simpa [ex17C6NotWalras] using ex17C6_ratio_large (hp 0) h⟩⟩)
      (fun M => ⟨1 / (|M| + 1), by positivity, fun p hp h =>
      ⟨1, by simpa [ex17C6NotWalras] using ex17C6_ratio_large (hp 1) h⟩⟩)
  · intro hW
    have h := hW _ (vec2_mem_posOrthant one_pos one_pos)
    norm_num [ex17C6NotWalras, dotProduct, Fin.sum_univ_two] at h
  · rintro p ⟨hp, hz⟩
    have h := congrFun hz 0
    simp only [ex17C6NotWalras, Matrix.cons_val_zero, Pi.zero_apply] at h
    exact (div_pos (hp 1) (hp 0)).ne' h

/-! ### Condition (iv) fails -/

/-- **Exercise 17.C.6**, the example violating only (iv):
`z(p) = (p₂/p₁ + p₁/p₂, -(1 + (p₁/p₂)²))`. -/
noncomputable def ex17C6NotBdd (p : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![p 1 / p 0 + p 0 / p 1, -(1 + (p 0 / p 1) ^ 2)]

/-- **Exercise 17.C.6** (MWG, p. 644), condition (iv). `ex17C6NotBdd` satisfies (i), (ii),
(iii), (v), but good 2's excess supply is unbounded, and `z(p) = 0` has no solution. -/
theorem exercise_17_C_6_iv :
    EDContinuous ex17C6NotBdd ∧ EDHomogeneous ex17C6NotBdd ∧ EDWalrasLaw ex17C6NotBdd ∧
      EDBoundary ex17C6NotBdd ∧ ¬ EDBoundedBelow ex17C6NotBdd ∧
      ∀ p, ¬ IsEqmPrice ex17C6NotBdd p := by
  have hr0 : ContinuousOn (fun p : Fin 2 → ℝ => p 1 / p 0) (posOrthant 2) :=
    (continuous_apply 1).continuousOn.div (continuous_apply 0).continuousOn
      fun p hp => (hp 0).ne'
  have hr1 : ContinuousOn (fun p : Fin 2 → ℝ => p 0 / p 1) (posOrthant 2) :=
    (continuous_apply 0).continuousOn.div (continuous_apply 1).continuousOn
      fun p hp => (hp 1).ne'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine continuousOn_pi.2 fun l => ?_
    fin_cases l
    · simp only [ex17C6NotBdd, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      exact hr0.add hr1
    · simp only [ex17C6NotBdd, Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
      exact (continuousOn_const.add (hr1.pow 2)).neg
  · intro p hp α hα
    funext l
    fin_cases l <;> simp [ex17C6NotBdd, mul_div_mul_left _ _ hα.ne']
  · intro p hp
    have h0 := (hp 0).ne'
    have h1 := (hp 1).ne'
    simp only [ex17C6NotBdd, dotProduct, Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    field_simp
    ring
  · exact edBoundary_two (fun M => ⟨1 / (|M| + 1), by positivity, fun p hp h => ⟨0, by
      have := ex17C6_ratio_large (hp 0) h
      have : 0 < p 0 / p 1 := div_pos (hp 0) (hp 1)
      simp only [ex17C6NotBdd, Matrix.cons_val_zero]
      linarith⟩⟩)
      (fun M => ⟨1 / (|M| + 1), by positivity, fun p hp h => ⟨0, by
      have := ex17C6_ratio_large (hp 1) h
      have : 0 < p 1 / p 0 := div_pos (hp 1) (hp 0)
      simp only [ex17C6NotBdd, Matrix.cons_val_zero]
      linarith⟩⟩)
  · rintro ⟨s, hs, hb⟩
    have h := hb _ (vec2_mem_posOrthant hs one_pos) 1
    simp only [ex17C6NotBdd, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      div_one] at h
    nlinarith [sq_nonneg (s - 1)]
  · rintro p ⟨hp, hz⟩
    have h := congrFun hz 0
    simp only [ex17C6NotBdd, Matrix.cons_val_zero, Pi.zero_apply] at h
    have := div_pos (hp 1) (hp 0)
    have := div_pos (hp 0) (hp 1)
    linarith

/-! ### Condition (v) fails -/

/-- **Exercise 17.C.6**, the example violating only (v): `z(p) = (p₂, -p₁)/(p₁ + p₂)`. -/
noncomputable def ex17C6NotBdry (p : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![p 1 / (p 0 + p 1), -(p 0 / (p 0 + p 1))]

/-- **Exercise 17.C.6** (MWG, p. 644), condition (v). `ex17C6NotBdry` satisfies (i)-(iv), but
excess demand stays bounded (below `1`) as `p → (1, 0)`, and `z(p) = 0` has no solution. -/
theorem exercise_17_C_6_v :
    EDContinuous ex17C6NotBdry ∧ EDHomogeneous ex17C6NotBdry ∧ EDWalrasLaw ex17C6NotBdry ∧
      EDBoundedBelow ex17C6NotBdry ∧ ¬ EDBoundary ex17C6NotBdry ∧
      ∀ p, ¬ IsEqmPrice ex17C6NotBdry p := by
  have hden : ContinuousOn (fun p : Fin 2 → ℝ => p 0 + p 1) (posOrthant 2) :=
    ((continuous_apply 0).add (continuous_apply 1)).continuousOn
  have hne : ∀ p ∈ posOrthant 2, p 0 + p 1 ≠ 0 := fun p hp => by
    have := hp 0; have := hp 1; positivity
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine continuousOn_pi.2 fun l => ?_
    fin_cases l
    · simp only [ex17C6NotBdry, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      exact (continuous_apply 1).continuousOn.div hden hne
    · simp only [ex17C6NotBdry, Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
      exact ((continuous_apply 0).continuousOn.div hden hne).neg
  · intro p hp α hα
    funext l
    fin_cases l <;> simp [ex17C6NotBdry, ← mul_add, mul_div_mul_left _ _ hα.ne']
  · intro p hp
    have := hne p hp
    simp only [ex17C6NotBdry, dotProduct, Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    field_simp
    ring
  · refine ⟨1, one_pos, fun p hp l => ?_⟩
    have h0 := hp 0
    have h1 := hp 1
    fin_cases l
    · have : 0 < p 1 / (p 0 + p 1) := by positivity
      simp only [ex17C6NotBdry, Fin.zero_eta, Matrix.cons_val_zero]
      linarith
    · have : p 0 / (p 0 + p 1) < 1 := by rw [div_lt_one (by positivity)]; linarith
      simp only [ex17C6NotBdry, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      linarith
  · intro hB
    have hps : ∀ n : ℕ, (![1, 1 / ((n : ℝ) + 1)] : Fin 2 → ℝ) ∈ posOrthant 2 := fun n =>
      vec2_mem_posOrthant one_pos (by positivity)
    have hlim : Tendsto (fun n : ℕ => (![1, 1 / ((n : ℝ) + 1)] : Fin 2 → ℝ)) atTop
        (𝓝 (![1, 0] : Fin 2 → ℝ)) := by
      refine tendsto_pi_nhds.2 fun l => ?_
      fin_cases l
      · simp
      · simpa using (tendsto_one_div_add_atTop_nhds_zero_nat :
          Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0))
    have hne0 : (![1, 0] : Fin 2 → ℝ) ≠ 0 := fun h => by simpa using congrFun h 0
    obtain ⟨n, l, hl⟩ := (hB _ _ hps hlim hne0 ⟨1, by simp⟩ 1).exists
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    fin_cases l
    · simp only [ex17C6NotBdry, Fin.zero_eta, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one] at hl
      rw [lt_div_iff₀ (by positivity)] at hl
      linarith
    · simp only [ex17C6NotBdry, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one] at hl
      have : 0 < 1 / (1 + 1 / ((n : ℝ) + 1)) := by positivity
      linarith
  · rintro p ⟨hp, hz⟩
    have h := congrFun hz 0
    simp only [ex17C6NotBdry, Matrix.cons_val_zero, Pi.zero_apply] at h
    have h0 := hp 0
    have h1 := hp 1
    exact (div_pos h1 (by positivity : 0 < p 0 + p 1)).ne' h

/-! ### Why (ii) is not in the list -/

/-- The homogenization `z(p/∑ₗ pₗ)` of a function `z`. -/
noncomputable def homogenize {L : ℕ} (z : (Fin L → ℝ) → Fin L → ℝ) (p : Fin L → ℝ) :
    Fin L → ℝ :=
  z ((∑ l, p l)⁻¹ • p)

/-- **Exercise 17.C.6**, why (ii) is not included. If `z` satisfies (i), (iii), (iv) and (v)
(and `L ≥ 1`), its homogenization `p ↦ z(p/∑ₗ pₗ)` satisfies all of (i)-(v). -/
theorem homogenize_isStandard {L : ℕ} (hL : 0 < L) {z : (Fin L → ℝ) → Fin L → ℝ}
    (hc : EDContinuous z) (hW : EDWalrasLaw z) (hb : EDBoundedBelow z) (hB : EDBoundary z) :
    IsStandardExcessDemand (homogenize z) := by
  have hS : ∀ p ∈ posOrthant L, 0 < ∑ l, p l := fun p hp => sum_pos_of_pos hL hp
  have hmaps : ∀ p ∈ posOrthant L, (∑ l, p l)⁻¹ • p ∈ posOrthant L := fun p hp =>
    smul_mem_posOrthant hp (inv_pos.2 (hS p hp))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hin : ContinuousOn (fun p : Fin L → ℝ => (∑ l, p l)⁻¹ • p) (posOrthant L) :=
      ((continuousOn_finsetSum _ fun l _ => (continuous_apply l).continuousOn).inv₀
        fun p hp => (hS p hp).ne').smul continuousOn_id
    exact hc.comp hin hmaps
  · intro p hp α hα
    have hsum : ∑ l, (α • p) l = α * ∑ l, p l := by
      simp [Finset.mul_sum]
    have : (∑ l, (α • p) l)⁻¹ • (α • p) = (∑ l, p l)⁻¹ • p := by
      have := (hS p hp).ne'
      rw [hsum, smul_smul]
      congr 1
      field_simp
    simp only [homogenize, this]
  · intro p hp
    have h := hW _ (hmaps p hp)
    rw [smul_dotProduct, smul_eq_mul] at h
    exact (mul_eq_zero.mp h).resolve_left (inv_pos.2 (hS p hp)).ne'
  · obtain ⟨s, hs, hsb⟩ := hb
    exact ⟨s, hs, fun p hp l => hsb _ (hmaps p hp) l⟩
  · intro ps p hps hlim hp0 hpl M
    have hnn := nonneg_of_tendsto_pos hps hlim
    have hSp : 0 < ∑ l, p l := by
      have := dotProduct_pos_of_ne_zero hnn hp0 (x := fun _ => 1) (fun _ => one_pos)
      simpa [dotProduct] using this
    have hsum : Tendsto (fun n => ∑ l, ps n l) atTop (𝓝 (∑ l, p l)) :=
      tendsto_finsetSum _ fun k _ => ((continuous_apply k).tendsto p).comp hlim
    have hq : Tendsto (fun n => (∑ l, ps n l)⁻¹ • ps n) atTop (𝓝 ((∑ l, p l)⁻¹ • p)) :=
      (hsum.inv₀ hSp.ne').smul hlim
    have hq0 : (∑ l, p l)⁻¹ • p ≠ 0 := smul_ne_zero (inv_ne_zero hSp.ne') hp0
    obtain ⟨l, hl⟩ := hpl
    exact hB _ _ (fun n => hmaps _ (hps n)) hq hq0 ⟨l, by simp [hl]⟩ M

/-- **Exercise 17.C.6** (MWG, p. 644), the question why (ii) is not in the list: for any number
of goods, conditions (i), (iii), (iv) and (v) alone imply that `z(p) = 0` has a solution
`p ≫ 0` (apply Proposition 17.C.1 to the homogenization). So no example violating only (ii)
can lack an equilibrium. -/
theorem exercise_17_C_6_ii {L : ℕ} {z : (Fin L → ℝ) → Fin L → ℝ} (hc : EDContinuous z)
    (hW : EDWalrasLaw z) (hb : EDBoundedBelow z) (hB : EDBoundary z) :
    ∃ p, IsEqmPrice z p := by
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · exact ⟨0, fun l => l.elim0, funext fun l => l.elim0⟩
  obtain ⟨p, hp, hz⟩ := proposition_17_C_1 (homogenize_isStandard hL hc hW hb hB)
  exact ⟨(∑ l, p l)⁻¹ • p, smul_mem_posOrthant hp (inv_pos.2 (sum_pos_of_pos hL hp)), hz⟩

end MWG.PositiveEquilibriumTheory
