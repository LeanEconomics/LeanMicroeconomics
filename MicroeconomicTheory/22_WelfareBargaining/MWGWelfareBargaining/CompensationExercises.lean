/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGWelfareBargaining.SocialWelfare
import MWGWelfareBargaining.UtilityPossibility

/-!
# Exercises on the compensation principle

MWG, Exercises 22.C.6 and 22.C.7 (pp. 851-852).

* `exercise_22_C_6a`: `U'` may pass the strong compensation test over `U` while the chosen
  Pareto optimal outcome in `U'` is utilitarian-worse than that in `U`.
* `exercise_22_C_6b`: for quasilinear utility possibility sets `{∑ uᵢ ≤ s}`, passing the weak
  test over a Pareto optimal outcome implies passing the strong test, and every Pareto optimal
  outcome of `U'` is a utilitarian improvement; `exercise_22_C_6b_maximin`: this fails for the
  maximin social welfare function.
* `exercise_22_C_7`: two two-good exchange economies with linear utilities, each with a
  competitive equilibrium, such that each utility possibility set passes the weak compensation
  test over the other's equilibrium outcome (the Scitovsky reversal);
  `exercise_22_C_7_same_total`: if the economies have the same aggregate endowment, their utility
  possibility sets coincide, so the property holds trivially. The example therefore has
  different aggregate endowments (the endowment vectors, not only their split, differ).
-/

namespace MWG.WelfareBargaining

/-- **Exercise 22.C.6(a)** (MWG, p. 851). `U = {u ≤ (1, 1)}`, `U' = U ∪ {u ≤ (-1, 3/2)}`:
`U'` passes the strong compensation test over `U`, `(1, 1)` is Pareto optimal in `U` and
`(-1, 3/2)` in `U'`, but the latter has the lower utilitarian welfare. -/
theorem exercise_22_C_6a :
    let U : Set (Fin 2 → ℝ) := {u | u ≤ ![1, 1]}
    let U' : Set (Fin 2 → ℝ) := {u | u ≤ ![1, 1]} ∪ {u | u ≤ ![-1, 3 / 2]}
    StrongCompensation U U' ∧ IsParetoFrontier U ![1, 1] ∧ IsParetoFrontier U' ![-1, 3 / 2] ∧
      ∑ i, (![-1, 3 / 2] : Fin 2 → ℝ) i < ∑ i, (![1, 1] : Fin 2 → ℝ) i := by
  intro U U'
  refine ⟨fun u hu => ⟨u, Or.inl hu, le_rfl⟩,
    ⟨show (![1, 1] : Fin 2 → ℝ) ≤ ![1, 1] from le_rfl, ?_⟩,
    ⟨Or.inr (show (![-1, 3 / 2] : Fin 2 → ℝ) ≤ ![-1, 3 / 2] from le_rfl), ?_⟩, by
    simp [Fin.sum_univ_two]; norm_num⟩
  · rintro ⟨v, hv, hle, i, hi⟩
    have h0 := hv 0; have h1 := hv 1
    fin_cases i <;> simp at hi h0 h1 <;> linarith
  · rintro ⟨v, hv, hle, i, hi⟩
    have l0 := hle 0; have l1 := hle 1
    simp at l0 l1
    rcases hv with hv | hv
    · have := hv 1; simp at this; linarith
    · have h0 := hv 0; have h1 := hv 1
      fin_cases i <;> simp at hi h0 h1 <;> linarith

/-- The quasilinear utility possibility set `{u : ∑ uᵢ ≤ s}`. -/
def qlUPS {n : ℕ} (s : ℝ) : Set (Fin n → ℝ) := {u | ∑ i, u i ≤ s}

/-- A Pareto optimal point of `{∑ uᵢ ≤ s}` is on its boundary `∑ uᵢ = s`. -/
theorem qlUPS_pareto {n : ℕ} [NeZero n] {s : ℝ} {u : Fin n → ℝ}
    (hu : IsParetoFrontier (qlUPS s) u) : ∑ i, u i = s := by
  obtain ⟨hmem, hno⟩ := hu
  by_contra hne
  have hlt : ∑ i, u i < s := lt_of_le_of_ne hmem hne
  classical
  set v := Function.update u 0 (u 0 + (s - ∑ i, u i)) with hv
  refine hno ⟨v, ?_, fun i => ?_, 0, by simp [hv]; linarith⟩
  · change ∑ i, v i ≤ s
    rw [hv, Finset.sum_update_of_mem (Finset.mem_univ 0), ← Finset.add_sum_erase _ _
      (Finset.mem_univ (0 : Fin n))]
    simp only [Finset.sdiff_singleton_eq_erase]
    linarith
  · by_cases h : i = 0
    · subst h; simp [hv]; linarith
    · simp [hv, h]

/-- **Exercise 22.C.6(b)** (MWG, p. 851). Quasilinear economies: `U = {∑ uᵢ ≤ s}`,
`U' = {∑ uᵢ ≤ s'}`. If `ū` is Pareto optimal in `U` and `U'` passes the weak compensation
test over `(U, ū)`, then `U'` passes the strong test, and every Pareto optimal `ū' ∈ U'` is a
(weak) utilitarian improvement over `ū`. -/
theorem exercise_22_C_6b {n : ℕ} [NeZero n] {s s' : ℝ} {ū ū' : Fin n → ℝ}
    (hū : IsParetoFrontier (qlUPS s) ū) (hw : WeakCompensation (qlUPS s') ū)
    (hū' : IsParetoFrontier (qlUPS s') ū') :
    StrongCompensation (qlUPS (n := n) s) (qlUPS s') ∧ ∑ i, ū i ≤ ∑ i, ū' i := by
  have hs := qlUPS_pareto hū
  have hs' := qlUPS_pareto hū'
  obtain ⟨u', hu', hle⟩ := hw
  have hss : s ≤ s' := by
    have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hle i
    change ∑ i, u' i ≤ s' at hu'
    linarith
  exact ⟨fun u hu => ⟨u, le_trans (show ∑ i, u i ≤ s from hu) hss, le_rfl⟩, by linarith⟩

/-- **Exercise 22.C.6(b)**, instance (MWG, p. 851): `s = 2`, `s' = 3`, `ū = (1, 1)`,
`ū' = (3/2, 3/2)`. -/
theorem exercise_22_C_6b_instance :
    IsParetoFrontier (qlUPS 2) (![1, 1] : Fin 2 → ℝ) ∧
      WeakCompensation (qlUPS 3) (![1, 1] : Fin 2 → ℝ) ∧
      IsParetoFrontier (qlUPS 3) (![3 / 2, 3 / 2] : Fin 2 → ℝ) := by
  refine ⟨⟨by norm_num [qlUPS, Fin.sum_univ_two], ?_⟩,
    ⟨![3 / 2, 3 / 2], by norm_num [qlUPS, Fin.sum_univ_two],
      fun i => by fin_cases i <;> norm_num⟩,
    ⟨by norm_num [qlUPS, Fin.sum_univ_two], ?_⟩⟩
  · rintro ⟨v, hv, hle, i, hi⟩
    simp only [qlUPS, Set.mem_ofPred_eq, Fin.sum_univ_two] at hv
    have := hle 0; have := hle 1
    fin_cases i <;> simp at * <;> linarith
  · rintro ⟨v, hv, hle, i, hi⟩
    simp only [qlUPS, Set.mem_ofPred_eq, Fin.sum_univ_two] at hv
    have := hle 0; have := hle 1
    fin_cases i <;> simp at * <;> linarith

/-- **Exercise 22.C.6(b)** (MWG, p. 851), last question. The conclusion fails for a
nonutilitarian social welfare function: with `U = {∑ uᵢ ≤ 2}`, `ū = (1, 1)` and
`U' = {∑ uᵢ ≤ 3}`, `ū' = (3, 0)`, `U'` passes the weak test and `ū'` is Pareto optimal in `U'`,
but the maximin welfare falls from `1` to `0`. -/
theorem exercise_22_C_6b_maximin :
    IsParetoFrontier (qlUPS 2) (![1, 1] : Fin 2 → ℝ) ∧
      WeakCompensation (qlUPS 3) (![1, 1] : Fin 2 → ℝ) ∧
      IsParetoFrontier (qlUPS 3) (![3, 0] : Fin 2 → ℝ) ∧
      min ((![3, 0] : Fin 2 → ℝ) 0) ((![3, 0] : Fin 2 → ℝ) 1) <
        min ((![1, 1] : Fin 2 → ℝ) 0) ((![1, 1] : Fin 2 → ℝ) 1) := by
  refine ⟨exercise_22_C_6b_instance.1, exercise_22_C_6b_instance.2.1,
    ⟨by simp [qlUPS, Fin.sum_univ_two], ?_⟩, by norm_num⟩
  rintro ⟨v, hv, hle, i, hi⟩
  simp only [qlUPS, Set.mem_ofPred_eq, Fin.sum_univ_two] at hv
  have := hle 0; have := hle 1
  fin_cases i <;> simp at * <;> linarith

/-! ### Exercise 22.C.7 -/

/-- A two-consumer, two-good exchange economy: utilities `uᵢ` and endowments `ωᵢ`. -/
structure Exchange22 where
  /-- Utility functions. -/
  u : Fin 2 → (Fin 2 → ℝ) → ℝ
  /-- Endowments. -/
  ω : Fin 2 → Fin 2 → ℝ

/-- Feasible allocations: nonnegative bundles adding up to the aggregate endowment. -/
def Exchange22.feasible (E : Exchange22) : Set (Fin 2 → Fin 2 → ℝ) :=
  {x | (∀ i l, 0 ≤ x i l) ∧ ∀ l, x 0 l + x 1 l = E.ω 0 l + E.ω 1 l}

/-- The (first-best) utility possibility set of the economy (Definition 22.B.1). -/
def Exchange22.UPS (E : Exchange22) : Set (Fin 2 → ℝ) := ups E.feasible fun i x => E.u i (x i)

/-- A competitive (Walrasian) equilibrium `(x, p)`, `p ≫ 0`: `x` is feasible and each `xᵢ`
maximizes `uᵢ` on the budget set `{y ≥ 0 : p·y ≤ p·ωᵢ}`. -/
def Exchange22.IsEquilibrium (E : Exchange22) (x : Fin 2 → Fin 2 → ℝ) (p : Fin 2 → ℝ) : Prop :=
  (∀ l, 0 < p l) ∧ x ∈ E.feasible ∧
    ∀ i, p 0 * x i 0 + p 1 * x i 1 ≤ p 0 * E.ω i 0 + p 1 * E.ω i 1 ∧
    ∀ y : Fin 2 → ℝ, (∀ l, 0 ≤ y l) → p 0 * y 0 + p 1 * y 1 ≤ p 0 * E.ω i 0 + p 1 * E.ω i 1 →
      E.u i y ≤ E.u i (x i)

/-- **Exercise 22.C.7** (MWG, pp. 851-852). If two exchange economies have the same utilities
and the same aggregate endowment, their utility possibility sets coincide; then each passes the
weak compensation test over any outcome of the other, so the requested property is trivial in
that case. -/
theorem exercise_22_C_7_same_total (E E' : Exchange22) (hu : E.u = E'.u)
    (hω : ∀ l, E.ω 0 l + E.ω 1 l = E'.ω 0 l + E'.ω 1 l) :
    E.UPS = E'.UPS ∧ ∀ v ∈ E.UPS, WeakCompensation E'.UPS v := by
  have hf : E.feasible = E'.feasible := by
    ext x; simp only [Exchange22.feasible, Set.mem_ofPred_eq, hω]
  have : E.UPS = E'.UPS := by simp only [Exchange22.UPS, hf, hu]
  exact ⟨this, fun v hv => ⟨v, this ▸ hv, le_rfl⟩⟩

/-- Economy A of `exercise_22_C_7`: `u₁ = 2y₁ + y₂`, `u₂ = y₁ + 2y₂`, endowments
`ω₁ = (1/2, 0)`, `ω₂ = (3/2, 0)`. -/
noncomputable def econA : Exchange22 where
  u := fun i y => if i = 0 then 2 * y 0 + y 1 else y 0 + 2 * y 1
  ω := fun i => if i = 0 then ![1 / 2, 0] else ![3 / 2, 0]

/-- Economy B of `exercise_22_C_7`: the same utilities, endowments `ω₁ = (0, 3/2)`,
`ω₂ = (0, 1/2)`. -/
noncomputable def econB : Exchange22 where
  u := fun i y => if i = 0 then 2 * y 0 + y 1 else y 0 + 2 * y 1
  ω := fun i => if i = 0 then ![0, 3 / 2] else ![0, 1 / 2]

/-- **Exercise 22.C.7** (MWG, pp. 851-852), the Scitovsky reversal. In economy A the endowment
is a competitive equilibrium at prices `(1, 3)` with utilities `(1, 3/2)`; in economy B the
endowment is an equilibrium at prices `(3, 1)` with utilities `(3/2, 1)`. Each utility
possibility set passes the weak compensation test over the other economy's equilibrium
outcome: `(1, 3/2) ≤ (1, 2) ∈ U_B` and `(3/2, 1) ≤ (2, 1) ∈ U_A`. -/
theorem exercise_22_C_7 :
    econA.IsEquilibrium econA.ω ![1, 3] ∧ econB.IsEquilibrium econB.ω ![3, 1] ∧
      (fun i => econA.u i (econA.ω i)) = ![1, 3 / 2] ∧
      (fun i => econB.u i (econB.ω i)) = ![3 / 2, 1] ∧
      WeakCompensation econB.UPS ![1, 3 / 2] ∧ WeakCompensation econA.UPS ![3 / 2, 1] := by
  refine ⟨⟨fun l => by fin_cases l <;> norm_num, ⟨fun i l => ?_, fun l => ?_⟩, fun i => ?_⟩,
    ⟨fun l => by fin_cases l <;> norm_num, ⟨fun i l => ?_, fun l => ?_⟩, fun i => ?_⟩,
    ?_, ?_, ?_, ?_⟩
  · fin_cases i <;> fin_cases l <;> norm_num [econA]
  · rfl
  · refine ⟨le_rfl, fun y hy hb => ?_⟩
    have h0 := hy 0; have h1 := hy 1
    fin_cases i <;> simp [econA] at hb ⊢ <;> linarith
  · fin_cases i <;> fin_cases l <;> norm_num [econB]
  · rfl
  · refine ⟨le_rfl, fun y hy hb => ?_⟩
    have h0 := hy 0; have h1 := hy 1
    fin_cases i <;> simp [econB] at hb ⊢ <;> linarith
  · funext i; fin_cases i <;> norm_num [econA]
  · funext i; fin_cases i <;> norm_num [econB]
  · -- in B, give consumer 1 one unit of good 2 and consumer 2 the other unit: `(1, 2)`
    refine ⟨![1, 2], ⟨![![0, 1], ![0, 1]], ⟨fun i l => ?_, fun l => ?_⟩, fun i => ?_⟩,
      fun i => ?_⟩
    · fin_cases i <;> fin_cases l <;> simp
    · fin_cases l <;> norm_num [econB]
    · fin_cases i <;> simp [econB]
    · fin_cases i <;> norm_num
  · -- in A, give each consumer one unit of good 1: `(2, 1)`
    refine ⟨![2, 1], ⟨![![1, 0], ![1, 0]], ⟨fun i l => ?_, fun l => ?_⟩, fun i => ?_⟩,
      fun i => ?_⟩
    · fin_cases i <;> fin_cases l <;> simp
    · fin_cases l <;> norm_num [econA]
    · fin_cases i <;> simp [econA]
    · fin_cases i <;> norm_num

end MWG.WelfareBargaining
