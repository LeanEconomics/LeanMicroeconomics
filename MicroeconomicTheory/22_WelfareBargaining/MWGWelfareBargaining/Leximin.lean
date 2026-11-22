/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGWelfareBargaining.SocialWelfare
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Order.PiLex
import Mathlib.Order.Interval.Finset.Fin

/-!
# The leximin ordering for any number of agents

MWG, footnote 11 (p. 827) and Exercise 22.C.4 (p. 851), for general `I` (the case `I = 2` is
`leximin2` and `exercise_22_C_4a`-`exercise_22_C_4c` in `SocialWelfare`).

The nondecreasing rearrangement of `u ∈ ℝ^I` is `sortVec u = u ∘ Tuple.sort u`; `u` is at least
as good as `u'` in the leximin order if `sortVec u'` is lexicographically below `sortVec u`
(Example 3.C.1's order, in `ℝ^I`).

* `sortVec_le_sortVec`: rearrangement is monotone (`u ≤ u'` implies the `k`-th smallest entry of
  `u` is at most that of `u'`), by a counting argument.
* `exercise_22_C_4a_general`: leximin is complete and transitive and refines maximin.
* `exercise_22_C_4b_general`: for `I ≥ 2` the leximin ordering has no utility representation,
  via the embedding `x ↦ (x₀ + k(1 + x₁))ₖ` of the lexicographic order of Example 3.C.1.
* `exercise_22_C_4c_general`: a leximin optimum is a Pareto optimum, for any `I`.
-/

namespace MWG.WelfareBargaining

variable {n : ℕ}

/-- **Exercise 22.C.4** (MWG, p. 851). The nondecreasing rearrangement of `u`. -/
noncomputable def sortVec (u : Fin n → ℝ) : Fin n → ℝ := u ∘ Tuple.sort u

/-- **Exercise 22.C.4** (MWG, p. 851). The leximin ordering on `ℝ^I`: `u` is at least as good
as `u'` iff the rearrangement of `u'` is lexicographically at most that of `u`. -/
def leximin (u u' : Fin n → ℝ) : Prop := toLex (sortVec u') ≤ toLex (sortVec u)

theorem sortVec_monotone (u : Fin n → ℝ) : Monotone (sortVec u) := Tuple.monotone_sort u

theorem sortVec_of_monotone {u : Fin n → ℝ} (hu : Monotone u) : sortVec u = u := by
  simp [sortVec, (Tuple.sort_eq_refl_iff_monotone).2 hu]

theorem sum_sortVec (u : Fin n → ℝ) : ∑ i, sortVec u i = ∑ i, u i :=
  Equiv.sum_comp (Tuple.sort u) u

/-- **Exercise 22.C.4** (MWG, p. 851). The `k`-th smallest entry is monotone in the vector: if
`u ≤ u'` then `sortVec u ≤ sortVec u'`. If not, the `k + 1` indices carrying the `k + 1`
smallest entries of `u'` would all carry entries of `u` below the `k`-th smallest one. -/
theorem sortVec_le_sortVec {u u' : Fin n → ℝ} (h : ∀ i, u i ≤ u' i) (k : Fin n) :
    sortVec u k ≤ sortVec u' k := by
  by_contra hlt
  have hlt : sortVec u' k < sortVec u k := not_le.1 hlt
  set σ := Tuple.sort u with hσ
  set σ' := Tuple.sort u' with hσ'
  have hmap : ∀ j ≤ k, σ.symm (σ' j) < k := by
    intro j hj
    by_contra hge
    have hge : k ≤ σ.symm (σ' j) := not_lt.1 hge
    have h1 : sortVec u k ≤ sortVec u (σ.symm (σ' j)) := sortVec_monotone u hge
    have h2 : sortVec u (σ.symm (σ' j)) = u (σ' j) := by
      simp [sortVec, ← hσ]
    have h5 : sortVec u' j ≤ sortVec u' k := sortVec_monotone u' hj
    have h4 : u' (σ' j) = sortVec u' j := rfl
    linarith [h (σ' j)]
  have hcard := Finset.card_le_card_of_injOn (fun j => σ.symm (σ' j)) (s := Finset.Iic k)
    (t := Finset.Iio k) (fun j hj => by
      simp only [Finset.coe_Iic, Set.mem_Iic, Finset.coe_Iio, Set.mem_Iio] at hj ⊢
      exact hmap j hj) (fun a _ b _ hab => by simpa using hab)
  simp only [Fin.card_Iic, Fin.card_Iio] at hcard
  omega

/-- **Exercise 22.C.4(a)** (MWG, p. 851), any number of agents. The leximin ordering is complete
and transitive, and it refines the Rawlsian ordering: a strictly larger minimum (the first
entry of the rearrangement) is leximin-better, and leximin-weakly-better implies a weakly larger
minimum. -/
theorem exercise_22_C_4a_general {m : ℕ} :
    (∀ u u' : Fin (m + 1) → ℝ, leximin u u' ∨ leximin u' u) ∧
    (∀ u u' u'' : Fin (m + 1) → ℝ, leximin u u' → leximin u' u'' → leximin u u'') ∧
    ∀ u u' : Fin (m + 1) → ℝ, (sortVec u' 0 < sortVec u 0 → leximin u u') ∧
      (leximin u u' → sortVec u' 0 ≤ sortVec u 0) := by
  refine ⟨fun u u' => le_total _ _, fun u u' u'' h1 h2 => h2.trans h1, fun u u' => ⟨?_, ?_⟩⟩
  · intro h
    exact le_of_lt ⟨0, fun j hj => absurd hj (Fin.not_lt_zero j), h⟩
  · intro h
    exact Pi.apply_le_of_toLex h fun j hj => absurd hj (Fin.not_lt_zero j)

/-- The embedding `x ↦ (x₀ + k(1 + x₁))ₖ` of `ℝ²₊` into `ℝ^I` used for Exercise 22.C.4(b). -/
def lexEmbed {m : ℕ} (x : Fin 2 → ℝ) : Fin (m + 2) → ℝ := fun k => x 0 + (k : ℕ) * (1 + x 1)

theorem lexEmbed_monotone {m : ℕ} {x : Fin 2 → ℝ} (hx : 0 ≤ x 1) :
    Monotone (lexEmbed (m := m) x) := by
  intro a b hab
  simp only [lexEmbed]
  have : ((a : ℕ) : ℝ) ≤ ((b : ℕ) : ℝ) := by exact_mod_cast hab
  nlinarith

/-- On the nonnegative orthant, the leximin comparison of embedded vectors is the lexicographic
order of Example 3.C.1. -/
theorem leximin_lexEmbed {m : ℕ} {x y : Fin 2 → ℝ} (hx : 0 ≤ x 1) (hy : 0 ≤ y 1) :
    leximin (lexEmbed (m := m) x) (lexEmbed y) ↔ MWG.ClassicalDemand.lexPref x y := by
  simp only [leximin, sortVec_of_monotone (lexEmbed_monotone hx),
    sortVec_of_monotone (lexEmbed_monotone hy), MWG.ClassicalDemand.lexPref]
  have e0 : ∀ z : Fin 2 → ℝ, lexEmbed (m := m) z 0 = z 0 := fun z => by simp [lexEmbed]
  have e1 : ∀ z : Fin 2 → ℝ, lexEmbed (m := m) z 1 = z 0 + 1 + z 1 := fun z => by
    simp [lexEmbed]; ring
  constructor
  · intro h
    have h0 := Pi.apply_le_of_toLex (i := 0) h fun j hj => absurd hj (Fin.not_lt_zero j)
    rw [e0, e0] at h0
    rcases h0.lt_or_eq with h0 | h0
    · exact Or.inl h0
    · refine Or.inr ⟨h0.symm, ?_⟩
      have h1 := Pi.apply_le_of_toLex (i := 1) h fun j hj => by
        have : j = 0 := by
          rcases j with ⟨j, hj'⟩
          simp only [Fin.lt_def, Fin.val_one] at hj
          ext; simp; omega
        subst this; rw [e0, e0, h0]
      rw [e1, e1] at h1
      linarith
  · rintro (h | ⟨h0, h1⟩)
    · exact le_of_lt ⟨0, fun j hj => absurd hj (Fin.not_lt_zero j), by
        simp only [Pi.toLex_apply, e0]; exact h⟩
    · rcases h1.lt_or_eq with h1 | h1
      · refine le_of_lt ⟨1, fun j hj => ?_, ?_⟩
        · have : j = 0 := by
            rcases j with ⟨j, hj'⟩
            simp only [Fin.lt_def, Fin.val_one] at hj
            ext; simp; omega
          subst this; simp only [Pi.toLex_apply, e0, h0]
        · simp only [Pi.toLex_apply, e1, h0]; linarith
      · have : x = y := by
          funext i; fin_cases i
          · exact h0
          · exact h1.symm
        rw [this]

/-- **Exercise 22.C.4(b)** (MWG, p. 851), any number `I ≥ 2` of agents. The leximin ordering
cannot be represented by a utility function: composing a representation with `lexEmbed` would
represent the lexicographic order of Example 3.C.1 (`example_3_C_1_not_representable`). -/
theorem exercise_22_C_4b_general {m : ℕ} :
    ¬∃ W : (Fin (m + 2) → ℝ) → ℝ, ∀ u u', leximin u u' ↔ W u' ≤ W u := by
  rintro ⟨W, hW⟩
  apply MWG.ClassicalDemand.example_3_C_1_not_representable
  refine ⟨fun x => W (lexEmbed x), fun x hx y hy => ?_⟩
  rw [← hW, leximin_lexEmbed (hx 1) (hy 1)]

/-- **Exercise 22.C.4(c)** (MWG, p. 851), any number of agents. A leximin optimum is a Pareto
optimum: a Pareto improvement weakly raises every entry of the rearrangement (`sortVec_le_sortVec`)
and strictly raises their sum, so it is strictly leximin-better. -/
theorem exercise_22_C_4c_general {U : Set (Fin n → ℝ)} {u : Fin n → ℝ} (hu : u ∈ U)
    (hopt : ∀ u' ∈ U, leximin u u') : IsParetoFrontier U u := by
  refine ⟨hu, fun ⟨v, hv, hle, i, hi⟩ => ?_⟩
  have hsle : sortVec u ≤ sortVec v := fun k => sortVec_le_sortVec hle k
  have hne : sortVec u ≠ sortVec v := by
    intro heq
    have hs : ∑ k, u k < ∑ k, v k :=
      Finset.sum_lt_sum (fun k _ => hle k) ⟨i, Finset.mem_univ i, hi⟩
    rw [← sum_sortVec u, ← sum_sortVec v, heq] at hs
    exact lt_irrefl _ hs
  have hlt : toLex (sortVec u) < toLex (sortVec v) :=
    Pi.toLex_strictMono (lt_of_le_of_ne hsle hne)
  exact absurd (hopt v hv) (not_le.2 hlt)

/-- **Exercise 22.C.4(c)**, a concrete instance (MWG, p. 851): on `U = {u ≤ (1, 2, 3)}` the
vector `(1, 2, 3)` is a leximin optimum. -/
theorem exercise_22_C_4c_instance :
    ∀ u' ∈ {u : Fin 3 → ℝ | u ≤ ![1, 2, 3]}, leximin ![1, 2, 3] u' := by
  intro u' hu'
  exact Pi.toLex_monotone (fun k => (sortVec_le_sortVec hu' k))

end MWG.WelfareBargaining
