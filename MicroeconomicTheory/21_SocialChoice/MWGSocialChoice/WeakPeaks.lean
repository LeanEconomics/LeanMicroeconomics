/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGSocialChoice.IntervalPreferences

/-!
# Single-peakedness cannot be weakened to weak monotonicity

MWG, Exercise 21.D.14, p. 815.

Five agents and five alternatives `x, y, z, v, w` (here `0, …, 4`) with the printed
preferences (indifferences allowed). (a) There is no Condorcet winner. (b) For the order
`x < y < z < v < w`, every agent's preference is weakly increasing as the agent's (unique) most
preferred alternative is approached. (c) Placing the alternatives at `0, 1/4, 1/2, 3/4, 1`,
the preferences are induced by quasiconcave utility functions on `[0, 1]`. (d) The same five
utility functions on the whole interval `[0, 1]` are quasiconcave, each has a single maximal
alternative, and there is no Condorcet winner in `[0, 1]`.
-/

namespace MWG.SocialChoice

open Kreps.ChoicePreferenceUtility Finset

/-- The utilities of Exercise 21.D.14 on `x, y, z, v, w = 0, …, 4`:
`x ≻₁ y ∼₁ z ∼₁ v ∼₁ w`, `y ≻₂ x ≻₂ z ≻₂ v ≻₂ w`, `z ≻₃ y ∼₃ v ∼₃ w ≻₃ x`,
`v ≻₄ w ≻₄ x ∼₄ y ∼₄ z`, `w ≻₅ x ∼₅ y ∼₅ z ∼₅ v`. -/
def e2114 : Fin 5 → Fin 5 → ℕ :=
  ![![1, 0, 0, 0, 0], ![4, 5, 3, 2, 1], ![0, 1, 2, 1, 1], ![0, 0, 0, 2, 1], ![0, 0, 0, 0, 1]]

/-- **Exercise 21.D.14(a)** (MWG, p. 815). There is no Condorcet winner: every alternative is
defeated by majority voting by some other alternative. -/
theorem exercise_21_D_14a :
    ∀ m : Fin 5, ∃ y, Strict (majorityRel fun i => natPref (e2114 i)) y m := by
  simp only [Strict, majorityRel_natPref]
  decide

/-- Weak single-peakedness: `x` is a most preferred alternative and preference is weakly
increasing as `x` is approached from either side (Exercise 21.D.14). -/
def WeaklySinglePeaked {X : Type*} [LinearOrder X] (r : X → X → Prop) (x : X) : Prop :=
  (∀ y, r x y) ∧ ∀ y z, (z ≤ x → y < z → r z y) ∧ (x ≤ z → z < y → r z y)

/-- **Exercise 21.D.14(b)** (MWG, p. 815). For the order `x < y < z < v < w`, each agent's
preference is weakly increasing towards the agent's most preferred alternative, which is
unique. -/
theorem exercise_21_D_14b :
    ∀ i : Fin 5, WeaklySinglePeaked (natPref (e2114 i)) i ∧
      ∀ y, y ≠ i → Strict (natPref (e2114 i)) i y := by
  simp only [WeaklySinglePeaked, natPref, Strict]
  decide

/-- The five utility functions on `[0, 1]` of Exercise 21.D.14(c)-(d). -/
noncomputable def e2114u (i : Fin 5) (t : ℝ) : ℝ :=
  match i with
  | 0 => if t = 0 then 1 else 0
  | 1 => min (t - 1 / 4) (1 / 2 - 2 * t)
  | 2 => if t = 0 then 0 else if t = 1 / 2 then 2 else 1
  | 3 => if t ≤ 1 / 2 then 0 else if t = 3 / 4 then 2 else 1
  | 4 => if t = 1 then 1 else 0

/-- The location of alternative `j` in `[0, 1]`: `x, y, z, v, w ↦ 0, 1/4, 1/2, 3/4, 1`. -/
noncomputable def e2114pos (j : Fin 5) : ℝ := ![0, 1 / 4, 1 / 2, 3 / 4, 1] j

/-- A function on `[0, 1]` that is weakly increasing up to `p` and weakly decreasing after `p`
is quasiconcave. -/
theorem quasiconcaveOn_of_unimodal {u : ℝ → ℝ} {p : ℝ}
    (hup : ∀ s t, 0 ≤ s → s ≤ t → t ≤ p → u s ≤ u t)
    (hdown : ∀ s t, p ≤ s → s ≤ t → t ≤ 1 → u t ≤ u s) :
    QuasiconcaveOn ℝ (Set.Icc (0 : ℝ) 1) u := by
  intro γ
  rw [convex_iff_ordConnected]
  refine ⟨fun s hs t ht m hm => ⟨⟨le_trans hs.1.1 hm.1, le_trans hm.2 ht.1.2⟩, ?_⟩⟩
  by_cases hmp : m ≤ p
  · exact le_trans hs.2 (hup s m hs.1.1 hm.1 hmp)
  · push Not at hmp
    exact le_trans ht.2 (hdown m t hmp.le hm.2 ht.1.2)

/-- **Exercise 21.D.14(c)-(d)** (MWG, p. 815). Each of the five utility functions is
quasiconcave on `[0, 1]` and has a single maximal alternative there, at `0, 1/4, 1/2, 3/4, 1`
respectively. -/
theorem exercise_21_D_14_quasiconcave (i : Fin 5) :
    QuasiconcaveOn ℝ (Set.Icc (0 : ℝ) 1) (e2114u i) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, t ≠ e2114pos i → e2114u i t < e2114u i (e2114pos i) := by
  fin_cases i
  · refine ⟨quasiconcaveOn_of_unimodal (p := 0) (fun s t hs hst ht => ?_)
      (fun s t hs hst ht => ?_), fun t ht hne => ?_⟩
    · have : s = t := by linarith
      rw [this]
    · simp only [e2114u]
      split_ifs <;> grind
    · simp only [e2114pos] at hne ⊢
      norm_num at hne ⊢
      simp [e2114u, hne]
  · refine ⟨quasiconcaveOn_of_unimodal (p := 1 / 4) (fun s t hs hst ht => ?_)
      (fun s t hs hst ht => ?_), fun t ht hne => ?_⟩
    · simp only [e2114u]
      rw [min_eq_left (by linarith), min_eq_left (by linarith)]
      linarith
    · simp only [e2114u]
      rw [min_eq_right (by linarith), min_eq_right (by linarith)]
      linarith
    · simp only [e2114pos, e2114u] at hne ⊢
      norm_num at hne ⊢
      rcases lt_or_gt_of_ne hne with h | h
      · left
        linarith
      · right
        linarith
  · refine ⟨quasiconcaveOn_of_unimodal (p := 1 / 2) (fun s t hs hst ht => ?_)
      (fun s t hs hst ht => ?_), fun t ht hne => ?_⟩
    · simp only [e2114u]
      split_ifs <;> grind
    · simp only [e2114u]
      split_ifs <;> grind
    · simp only [e2114pos, e2114u] at hne ⊢
      norm_num at hne ⊢
      split_ifs <;> norm_num
  · refine ⟨quasiconcaveOn_of_unimodal (p := 3 / 4) (fun s t hs hst ht => ?_)
      (fun s t hs hst ht => ?_), fun t ht hne => ?_⟩
    · simp only [e2114u]
      split_ifs <;> grind
    · simp only [e2114u]
      split_ifs <;> grind
    · simp only [e2114pos, e2114u] at hne ⊢
      norm_num at hne ⊢
      split_ifs <;> norm_num
  · refine ⟨quasiconcaveOn_of_unimodal (p := 1) (fun s t hs hst ht => ?_)
      (fun s t hs hst ht => ?_), fun t ht hne => ?_⟩
    · simp only [e2114u]
      split_ifs <;> grind
    · have : s = t := by linarith
      rw [this]
    · simp only [e2114pos, e2114u] at hne ⊢
      norm_num at hne ⊢
      simp [hne]

/-- **Exercise 21.D.14(c)** (MWG, p. 815). Restricted to the five points
`0, 1/4, 1/2, 3/4, 1`, the quasiconcave utilities induce exactly the preferences of the
exercise. -/
theorem exercise_21_D_14c (i j k : Fin 5) :
    e2114u i (e2114pos k) ≤ e2114u i (e2114pos j) ↔ e2114 i k ≤ e2114 i j := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num [e2114u, e2114pos, e2114]

/-- `s` defeats `t` by majority voting under the utilities `e2114u`. -/
def e2114Defeats (s t : ℝ) : Prop :=
  (univ.filter fun i : Fin 5 => e2114u i s < e2114u i t).card <
    (univ.filter fun i : Fin 5 => e2114u i t < e2114u i s).card

/-- **Exercise 21.D.14(d)** (MWG, p. 815). With five agents, alternatives `[0, 1]` and the
quasiconcave utilities `e2114u` (each with a single maximal alternative), there is no Condorcet
winner: every `t ∈ [0, 1]` is defeated by some `s ∈ [0, 1]`. -/
theorem exercise_21_D_14d : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ s ∈ Set.Icc (0 : ℝ) 1, e2114Defeats s t := by
  intro t ht
  have count : ∀ s (A B : Finset (Fin 5)),
      (univ.filter fun i : Fin 5 => e2114u i s < e2114u i t) = A →
      (univ.filter fun i : Fin 5 => e2114u i t < e2114u i s) = B → A.card < B.card →
      e2114Defeats s t := fun s A B hA hB hAB => by
    unfold e2114Defeats
    rw [hA, hB]
    exact hAB
  rcases eq_or_lt_of_le ht.1 with h0 | h0
  · subst h0
    refine ⟨1 / 4, by norm_num, count _ {0} {1, 2} ?_ ?_ (by decide)⟩ <;>
      ext i <;> rw [mem_filter] <;> fin_cases i <;> norm_num [e2114u]
  have key : ∀ s, e2114Defeats s t ↔
      (∑ i : Fin 5, if e2114u i s < e2114u i t then 1 else 0) <
        ∑ i : Fin 5, if e2114u i t < e2114u i s then 1 else 0 := by
    intro s
    simp only [e2114Defeats, card_filter]
  by_cases hhalf : t < 1 / 2
  · have ht1 : t ≠ 1 := by linarith
    have a0 : e2114u 0 t = 0 := by simp only [e2114u, h0.ne', ↓reduceIte]
    have a0s : e2114u 0 1 = 0 := by norm_num [e2114u]
    have a1 : e2114u 1 1 < e2114u 1 t := by
      simp only [e2114u]
      rw [lt_min_iff]
      constructor <;> norm_num <;> linarith
    have a1' := not_lt.2 a1.le
    have a2 : e2114u 2 t = 1 := by simp only [e2114u, h0.ne', hhalf.ne, ↓reduceIte]
    have a2s : e2114u 2 1 = 1 := by norm_num [e2114u]
    have a3 : e2114u 3 t = 0 := by simp only [e2114u, hhalf.le, ↓reduceIte]
    have a3s : e2114u 3 1 = 1 := by norm_num [e2114u]
    have a4 : e2114u 4 t = 0 := by simp only [e2114u, ht1, ↓reduceIte]
    have a4s : e2114u 4 1 = 1 := by norm_num [e2114u]
    refine ⟨1, by norm_num, (key 1).2 ?_⟩
    simp only [Fin.sum_univ_five, a0, a0s, a1, a1', a2, a2s, a3, a3s, a4, a4s,
      lt_self_iff_false, ↓reduceIte]
    norm_num
  by_cases hh : t = 1 / 2
  · subst hh
    refine ⟨0, by norm_num, count _ {2} {0, 1} ?_ ?_ (by decide)⟩ <;>
      ext i <;> rw [mem_filter] <;> fin_cases i <;> norm_num [e2114u]
  have hgt : 1 / 2 < t := lt_of_le_of_ne (not_lt.1 hhalf) (Ne.symm hh)
  by_cases h1 : t = 1
  · subst h1
    refine ⟨3 / 4, by norm_num, count _ {4} {1, 3} ?_ ?_ (by decide)⟩ <;>
      ext i <;> rw [mem_filter] <;> fin_cases i <;> norm_num [e2114u]
  · have e0 : e2114u 0 t = 0 := by simp only [e2114u, h0.ne', ↓reduceIte]
    have e0s : e2114u 0 (1 / 2) = 0 := by norm_num [e2114u]
    have e1 : e2114u 1 t < e2114u 1 (1 / 2) := by
      simp only [e2114u]
      rw [min_lt_iff]
      right
      norm_num
      linarith
    have e1' := not_lt.2 e1.le
    have e2 : e2114u 2 t = 1 := by simp only [e2114u, h0.ne', hh, ↓reduceIte]
    have e2s : e2114u 2 (1 / 2) = 2 := by norm_num [e2114u]
    have e3 : e2114u 3 (1 / 2) < e2114u 3 t := by
      have : e2114u 3 (1 / 2) = 0 := by norm_num [e2114u]
      rw [this]
      simp only [e2114u, not_le.2 hgt, ↓reduceIte]
      split_ifs <;> norm_num
    have e3' := not_lt.2 e3.le
    have e4 : e2114u 4 t = 0 := by simp only [e2114u, h1, ↓reduceIte]
    have e4s : e2114u 4 (1 / 2) = 0 := by norm_num [e2114u]
    refine ⟨1 / 2, by norm_num, (key (1 / 2)).2 ?_⟩
    simp only [Fin.sum_univ_five, e0, e0s, e1, e1', e2, e2s, e3, e3', e4, e4s,
      lt_self_iff_false, ↓reduceIte]
    norm_num

end MWG.SocialChoice
