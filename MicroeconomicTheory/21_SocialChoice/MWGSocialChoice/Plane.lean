/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGSocialChoice.Euclidean
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic.LinearCombination

/-!
# Majority voting in the plane: finitely many types of Euclidean voters

MWG, Exercise 21.D.13, p. 815.

The plane `ℝ²` is modelled by `ℂ` with its real inner product (an isometric copy of the
Euclidean plane). A continuum of agents with Euclidean preferences falls into `J` types with
peaks `xⱼ` and masses `αⱼ ≥ 0`. `y` is a Condorcet winner if for every `z` the mass preferring
`z` to `y` is at most the mass preferring `y` to `z`.

The key lemma (`condorcet_halfplane`): if `y` is a Condorcet winner then for every direction
`w ≠ 0` the mass of types with `⟪xⱼ - y, w⟫ > 0` is at most the mass of the others (move from
`y` by a small step in direction `w`).

(a) With `J` odd and equal masses, a Condorcet winner is a peak (general position is not
needed); for `J` even this fails (`exercise_21_D_13a_even`). (b) (De Marzo) With a dominant type
and peaks in general position, the only possible Condorcet winner is the dominant type's peak.
-/

namespace MWG.SocialChoice

open Finset Filter Topology

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

/-- The mass of the types preferring `y` to `z` (`xⱼ` closer to `y` than to `z`). -/
noncomputable def typeMass {J : ℕ} (x : Fin J → ℂ) (α : Fin J → ℝ) (y z : ℂ) : ℝ :=
  ∑ j ∈ univ.filter (fun j => ‖x j - y‖ < ‖x j - z‖), α j

/-- **Exercise 21.D.13** (MWG, p. 815). `y` is a Condorcet winning alternative. -/
def IsTypeCondorcetWinner {J : ℕ} (x : Fin J → ℂ) (α : Fin J → ℝ) (y : ℂ) : Prop :=
  ∀ z, typeMass x α z y ≤ typeMass x α y z

/-- A small step from `y` in a direction `w ≠ 0` attracts exactly the types with
`⟪xⱼ - y, w⟫ > 0`. -/
theorem eventually_small_step {J : ℕ} (x : Fin J → ℂ) (y w : ℂ) (hw : w ≠ 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ j, (‖x j - (y + ε • w)‖ < ‖x j - y‖ ↔ 0 < ⟪x j - y, w⟫) ∧
      (‖x j - y‖ < ‖x j - (y + ε • w)‖ ↔ ⟪x j - y, w⟫ ≤ 0) := by
  rw [eventually_all]
  intro j
  set v := x j - y
  set c := ⟪v, w⟫
  have hw2 : 0 < ‖w‖ ^ 2 := pow_pos (norm_pos_iff.2 hw) 2
  have key : ∀ ε : ℝ, ‖x j - (y + ε • w)‖ ^ 2 = ‖v‖ ^ 2 - 2 * ε * c + ε ^ 2 * ‖w‖ ^ 2 := by
    intro ε
    have : x j - (y + ε • w) = v - ε • w := by simp only [v]; abel
    rw [this, norm_sub_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    ring
  have sqlt : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → (a < b ↔ a ^ 2 < b ^ 2) := fun a b ha hb =>
    ⟨fun h => by nlinarith, fun h => by nlinarith⟩
  by_cases hc : 0 < c
  · filter_upwards [Ioo_mem_nhdsGT (div_pos (mul_pos two_pos hc) hw2)] with ε hε
    obtain ⟨h0, h1⟩ := hε
    rw [lt_div_iff₀ hw2] at h1
    rw [sqlt _ _ (norm_nonneg _) (norm_nonneg _), sqlt _ _ (norm_nonneg _) (norm_nonneg _),
      key]
    constructor
    · exact iff_of_true (by nlinarith) hc
    · exact iff_of_false (by nlinarith) (not_le.2 hc)
  · push Not at hc
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have h0 : (0 : ℝ) < ε := hε
    rw [sqlt _ _ (norm_nonneg _) (norm_nonneg _), sqlt _ _ (norm_nonneg _) (norm_nonneg _),
      key]
    have hpos : 0 < ε ^ 2 * ‖w‖ ^ 2 := mul_pos (pow_pos h0 2) hw2
    have hnn : 0 ≤ ε * -c := mul_nonneg h0.le (neg_nonneg.2 hc)
    constructor
    · exact iff_of_false (by nlinarith) (not_lt.2 hc)
    · exact iff_of_true (by nlinarith) hc

/-- **Exercise 21.D.13**, key lemma. If `y` is a Condorcet winner, then for every direction
`w ≠ 0` the mass of types with `⟪xⱼ - y, w⟫ > 0` is at most the mass of the remaining types. -/
theorem condorcet_halfplane {J : ℕ} {x : Fin J → ℂ} {α : Fin J → ℝ} {y : ℂ}
    (hy : IsTypeCondorcetWinner x α y) (w : ℂ) (hw : w ≠ 0) :
    ∑ j ∈ univ.filter (fun j => 0 < ⟪x j - y, w⟫), α j ≤
      ∑ j ∈ univ.filter (fun j => ⟪x j - y, w⟫ ≤ 0), α j := by
  obtain ⟨ε, hε⟩ := (eventually_small_step x y w hw).exists
  have h := hy (y + ε • w)
  unfold typeMass at h
  have e1 : (univ.filter fun j => ‖x j - (y + ε • w)‖ < ‖x j - y‖) =
      univ.filter fun j => 0 < ⟪x j - y, w⟫ := by
    ext j
    simp only [mem_filter, mem_univ, true_and]
    exact (hε j).1
  have e2 : (univ.filter fun j => ‖x j - y‖ < ‖x j - (y + ε • w)‖) =
      univ.filter fun j => ⟪x j - y, w⟫ ≤ 0 := by
    ext j
    simp only [mem_filter, mem_univ, true_and]
    exact (hε j).2
  rwa [e1, e2] at h

/-- The real inner product on `ℂ` in coordinates. -/
theorem complex_inner_eq (v w : ℂ) : ⟪v, w⟫ = v.re * w.re + v.im * w.im := by
  rw [Complex.inner]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- Finitely many nonzero vectors of the plane admit a direction `w ≠ 0` orthogonal to none of
them (one of `1 + kI`, `k = 0, …, J`, works). -/
theorem exists_generic_direction {J : ℕ} (v : Fin J → ℂ) (hv : ∀ j, v j ≠ 0) :
    ∃ w : ℂ, w ≠ 0 ∧ ∀ j, ⟪v j, w⟫ ≠ 0 := by
  by_contra hc
  push Not at hc
  have hk : ∀ k : Fin (J + 1), ∃ j, ⟪v j, 1 + (k : ℝ) * Complex.I⟫ = 0 := by
    intro k
    refine hc _ fun h0 => ?_
    have := congrArg Complex.re h0
    simp at this
  choose f hf using hk
  obtain ⟨k, k', hne, hkk⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simp)
  have h1 := hf k
  have h2 := hf k'
  rw [hkk, complex_inner_eq] at h1
  rw [complex_inner_eq] at h2
  simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
    Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero,
    Complex.add_im, Complex.one_im, Complex.mul_im, zero_add] at h1 h2
  have hk' : ((k : ℕ) : ℝ) ≠ ((k' : ℕ) : ℝ) := by
    intro e
    exact hne (Fin.ext (by exact_mod_cast e))
  have him : (v (f k')).im = 0 := by
    have : ((k : ℕ) - (k' : ℕ) : ℝ) * (v (f k')).im = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) hk'
    · exact h
  have hre : (v (f k')).re = 0 := by rw [him] at h2; linarith
  exact hv (f k') (Complex.ext hre him)

/-- **Exercise 21.D.13(a)** (MWG, p. 815). With an odd number `J` of types of equal mass, a
Condorcet winning alternative must be the peak of some type. (General position is not used.) -/
theorem exercise_21_D_13a {J : ℕ} (hJ : Odd J) (x : Fin J → ℂ) {a : ℝ} (ha : 0 < a) {y : ℂ}
    (hy : IsTypeCondorcetWinner x (fun _ => a) y) : ∃ j, y = x j := by
  by_contra hc
  push Not at hc
  obtain ⟨w, hw0, hw⟩ := exists_generic_direction (fun j => x j - y)
    fun j h => hc j (sub_eq_zero.1 h).symm
  have h1 := condorcet_halfplane hy w hw0
  have h2 := condorcet_halfplane hy (-w) (neg_ne_zero.2 hw0)
  simp only [sum_const, nsmul_eq_mul, inner_neg_right, neg_pos, neg_nonpos] at h1 h2
  have e1 : (univ.filter fun j => ⟪x j - y, w⟫ ≤ 0) = univ.filter fun j => ⟪x j - y, w⟫ < 0 := by
    ext j
    simp only [mem_filter, mem_univ, true_and]
    exact ⟨fun h => lt_of_le_of_ne h (hw j), le_of_lt⟩
  have e2 : (univ.filter fun j => 0 ≤ ⟪x j - y, w⟫) = univ.filter fun j => 0 < ⟪x j - y, w⟫ := by
    ext j
    simp only [mem_filter, mem_univ, true_and]
    exact ⟨fun h => lt_of_le_of_ne h (Ne.symm (hw j)), le_of_lt⟩
  rw [e1] at h1
  rw [e2] at h2
  have c1 := le_of_mul_le_mul_right h1 ha
  have c2 := le_of_mul_le_mul_right h2 ha
  have heq : (univ.filter fun j => 0 < ⟪x j - y, w⟫).card =
      (univ.filter fun j => ⟪x j - y, w⟫ < 0).card := by exact_mod_cast le_antisymm c1 c2
  have hsplit : (univ.filter fun j => 0 < ⟪x j - y, w⟫).card +
      (univ.filter fun j => ⟪x j - y, w⟫ < 0).card = J := by
    have := card_filter_add_card_filter_not (s := (univ : Finset (Fin J)))
      (fun j => 0 < ⟪x j - y, w⟫)
    have e : (univ.filter fun j => ¬0 < ⟪x j - y, w⟫) = univ.filter fun j => ⟪x j - y, w⟫ < 0 := by
      ext j
      simp only [mem_filter, mem_univ, true_and, not_lt]
      exact ⟨fun h => lt_of_le_of_ne h (hw j), le_of_lt⟩
    rw [e, card_univ, Fintype.card_fin] at this
    exact this
  obtain ⟨m, hm⟩ := hJ
  omega

/-- **Exercise 21.D.13(a)**, even `J` (MWG, p. 815). The conclusion fails for an even number of
types: with two types of mass `1/2` at `0` and `1`, the midpoint `1/2` is a Condorcet winner but
not a peak. -/
theorem exercise_21_D_13a_even :
    IsTypeCondorcetWinner ![(0 : ℂ), 1] (fun _ => 1 / 2) (1 / 2) ∧
      ∀ j, (1 / 2 : ℂ) ≠ ![(0 : ℂ), 1] j := by
  refine ⟨fun z => ?_, fun j => ?_⟩
  · unfold typeMass
    simp only [sum_filter, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    have h0 : ‖(0 : ℂ) - 1 / 2‖ = 1 / 2 := by norm_num
    have h1 : ‖(1 : ℂ) - 1 / 2‖ = 1 / 2 := by norm_num
    have tri : ‖(0 : ℂ) - z‖ + ‖(1 : ℂ) - z‖ ≥ 1 := by
      have := norm_sub_le ((1 : ℂ) - z) ((0 : ℂ) - z)
      simp only [sub_sub_sub_cancel_right, sub_zero, norm_one] at this
      linarith
    by_cases hA : ‖(0 : ℂ) - z‖ < ‖(0 : ℂ) - 1 / 2‖ <;>
      by_cases hB : ‖(1 : ℂ) - z‖ < ‖(1 : ℂ) - 1 / 2‖ <;>
      by_cases hC : ‖(0 : ℂ) - 1 / 2‖ < ‖(0 : ℂ) - z‖ <;>
      by_cases hD : ‖(1 : ℂ) - 1 / 2‖ < ‖(1 : ℂ) - z‖ <;>
      simp only [hA, hB, hC, hD, ↓reduceIte] <;> linarith
  · fin_cases j
    · norm_num
    · intro h
      have := congrArg Complex.re h
      norm_num at this

/-- `⟪a, I b⟫ = Im(a b̄)`, the (signed) area spanned by `a` and `b`; zero iff `a, b` are
collinear with `0`. -/
theorem inner_I_mul (a b : ℂ) : ⟪a, Complex.I * b⟫ = a.im * b.re - a.re * b.im := by
  rw [complex_inner_eq]
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub,
    Complex.mul_im]
  ring

/-- Two vectors orthogonal to `I u` (i.e. on the line `ℝu`, `u ≠ 0`) are collinear. -/
theorem collinear_of_orth {u a b : ℂ} (hu : u ≠ 0) (ha : ⟪a, Complex.I * u⟫ = 0)
    (hb : ⟪b, Complex.I * u⟫ = 0) : ⟪a, Complex.I * b⟫ = 0 := by
  rw [inner_I_mul] at ha hb ⊢
  have h1 : (a.im * b.re - a.re * b.im) * u.re = 0 := by linear_combination b.re * ha - a.re * hb
  have h2 : (a.im * b.re - a.re * b.im) * u.im = 0 := by linear_combination b.im * ha - a.im * hb
  by_contra hne
  have hre : u.re = 0 := (mul_eq_zero.1 h1).resolve_left hne
  have him : u.im = 0 := (mul_eq_zero.1 h2).resolve_left hne
  exact hu (Complex.ext hre him)

/-- **Exercise 21.D.13(b)** (MWG, p. 815). Peaks are in general position: no three peaks of
distinct types lie on a line. -/
def GeneralPosition {J : ℕ} (x : Fin J → ℂ) : Prop :=
  ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ⟪x j - x i, Complex.I * (x k - x i)⟫ ≠ 0

/-- **Exercise 21.D.13(b) (De Marzo)** (MWG, p. 815). With peaks in general position, masses
`αⱼ ≥ 0` summing to one and a dominant type `h` (`αₕ > αⱼ` for `j ≠ h`), a Condorcet winning
alternative can only be the dominant type's peak. -/
theorem exercise_21_D_13b {J : ℕ} {x : Fin J → ℂ} {α : Fin J → ℝ} (hα : ∀ j, 0 ≤ α j)
    (hsum : ∑ j, α j = 1) (hgp : GeneralPosition x) {h : Fin J}
    (hdom : ∀ j, j ≠ h → α j < α h) {y : ℂ} (hy : IsTypeCondorcetWinner x α y) : y = x h := by
  classical
  by_contra hne
  set u := x h - y with hu
  have hu0 : u ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
  set n := Complex.I * u with hn
  have hun : ⟪u, n⟫ = 0 := by rw [hn, inner_I_mul]; ring
  have huu : 0 < ⟪u, u⟫ := by
    rw [real_inner_self_eq_norm_sq]
    exact pow_pos (norm_pos_iff.2 hu0) 2
  have hαh : 0 < α h := by
    have : ∑ j, α j ≤ ∑ _j : Fin J, α h := sum_le_sum fun j _ => by
      by_cases hj : j = h
      · rw [hj]
      · exact (hdom j hj).le
    rw [hsum, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    by_contra hc
    push Not at hc
    nlinarith [Nat.cast_nonneg (α := ℝ) J]
  set v : Fin J → ℂ := fun j => x j - y with hv
  have hsmall : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ j, ⟪v j, n⟫ ≠ 0 →
      |δ * ⟪v j, u⟫| < |⟪v j, n⟫| := by
    rw [eventually_all]
    intro j
    by_cases hc : ⟪v j, n⟫ = 0
    · exact Eventually.of_forall fun _ h' => absurd hc h'
    · have hcpos : 0 < |⟪v j, n⟫| := abs_pos.2 hc
      filter_upwards [Ioo_mem_nhdsGT (div_pos hcpos (by positivity :
        (0 : ℝ) < |⟪v j, u⟫| + 1))] with δ hδ _
      obtain ⟨h0, h1⟩ := hδ
      rw [lt_div_iff₀ (by positivity)] at h1
      rw [abs_mul, abs_of_pos h0]
      nlinarith [abs_nonneg ⟪v j, u⟫]
  obtain ⟨δ, hδ, hδpos⟩ := (hsmall.and self_mem_nhdsWithin).exists
  have hδ0 : (0 : ℝ) < δ := hδpos
  set wp := n + δ • u
  set wm := -n + δ • u
  have hwp : wp ≠ 0 := by
    intro h0
    have : ⟪u, wp⟫ = 0 := by rw [h0, inner_zero_right]
    rw [inner_add_right, hun, inner_smul_right] at this
    nlinarith
  have hwm : wm ≠ 0 := by
    intro h0
    have : ⟪u, wm⟫ = 0 := by rw [h0, inner_zero_right]
    rw [inner_add_right, inner_neg_right, hun, inner_smul_right] at this
    nlinarith
  have c1 := condorcet_halfplane hy wp hwp
  have c2 := condorcet_halfplane hy wm hwm
  simp only [sum_filter] at c1 c2
  have hsum2 := add_le_add c1 c2
  rw [← sum_add_distrib, ← sum_add_distrib] at hsum2
  set Lp := univ.filter fun j => ⟪v j, n⟫ = 0 ∧ 0 < ⟪v j, u⟫
  set Lr := univ.filter fun j => ⟪v j, n⟫ = 0 ∧ ⟪v j, u⟫ ≤ 0
  have hpoint : ∀ j, ((if 0 < ⟪x j - y, wp⟫ then α j else 0) +
      (if 0 < ⟪x j - y, wm⟫ then α j else 0)) - ((if ⟪x j - y, wp⟫ ≤ 0 then α j else 0) +
      (if ⟪x j - y, wm⟫ ≤ 0 then α j else 0)) =
      2 * (if j ∈ Lp then α j else 0) - 2 * (if j ∈ Lr then α j else 0) := by
    intro j
    have ep : ⟪x j - y, wp⟫ = ⟪v j, n⟫ + δ * ⟪v j, u⟫ := by
      simp only [wp, inner_add_right, inner_smul_right, v]
    have em : ⟪x j - y, wm⟫ = -⟪v j, n⟫ + δ * ⟪v j, u⟫ := by
      simp only [wm, inner_add_right, inner_neg_right, inner_smul_right, v]
    rw [ep, em]
    simp only [Lp, Lr, mem_filter, mem_univ, true_and]
    by_cases hc : ⟪v j, n⟫ = 0
    · rw [hc]
      by_cases hd : 0 < ⟪v j, u⟫
      · have : 0 < δ * ⟪v j, u⟫ := mul_pos hδ0 hd
        simp only [zero_add, neg_zero, true_and, hd, this, not_le.2 this, not_le.2 hd,
          ↓reduceIte]
        ring
      · push Not at hd
        have : δ * ⟪v j, u⟫ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hδ0.le hd
        simp only [zero_add, neg_zero, true_and, not_lt.2 hd, not_lt.2 this, this, hd,
          ↓reduceIte]
        ring
    · have hb := hδ j hc
      rw [abs_lt] at hb
      simp only [hc, false_and, ↓reduceIte, mul_zero, sub_zero]
      rcases lt_or_gt_of_ne hc with hlt | hgt
      · rw [abs_of_neg hlt] at hb
        have a1 : ¬0 < ⟪v j, n⟫ + δ * ⟪v j, u⟫ := by linarith
        have a2 : 0 < -⟪v j, n⟫ + δ * ⟪v j, u⟫ := by linarith
        simp only [a1, a2, not_lt.1 a1, not_le.2 a2, ↓reduceIte]
        ring
      · rw [abs_of_pos hgt] at hb
        have a1 : 0 < ⟪v j, n⟫ + δ * ⟪v j, u⟫ := by linarith
        have a2 : ¬0 < -⟪v j, n⟫ + δ * ⟪v j, u⟫ := by linarith
        simp only [a1, a2, not_lt.1 a2, not_le.2 a1, ↓reduceIte]
        ring
  have hLpLr : ∑ j ∈ Lp, α j ≤ ∑ j ∈ Lr, α j := by
    have hdiff : ∑ j, (((if 0 < ⟪x j - y, wp⟫ then α j else 0) +
        (if 0 < ⟪x j - y, wm⟫ then α j else 0)) - ((if ⟪x j - y, wp⟫ ≤ 0 then α j else 0) +
        (if ⟪x j - y, wm⟫ ≤ 0 then α j else 0))) ≤ 0 := by
      rw [sum_sub_distrib]
      linarith
    simp only [hpoint] at hdiff
    rw [sum_sub_distrib, ← mul_sum, ← mul_sum, sum_ite_mem, sum_ite_mem, univ_inter,
      univ_inter] at hdiff
    linarith
  have hhLp : h ∈ Lp := by
    simp only [Lp, mem_filter, mem_univ, true_and]
    exact ⟨hun, huu⟩
  have hLp_ge : α h ≤ ∑ j ∈ Lp, α j := single_le_sum (fun j _ => hα j) hhLp
  have hLr_sub : ∀ j ∈ Lr, ∀ k ∈ Lr, j = k := by
    intro j hj k hk
    simp only [Lr, mem_filter, mem_univ, true_and] at hj hk
    by_contra hjk
    have hjh : j ≠ h := fun e => by rw [e] at hj; linarith [hj.2]
    have hkh : k ≠ h := fun e => by rw [e] at hk; linarith [hk.2]
    apply hgp h j k (Ne.symm hjh) (Ne.symm hkh) hjk
    have hj' : ⟪x j - x h, n⟫ = 0 := by
      have : x j - x h = v j - u := by simp only [v, hu]; abel
      rw [this, inner_sub_left, hj.1, hun, sub_zero]
    have hk' : ⟪x k - x h, n⟫ = 0 := by
      have : x k - x h = v k - u := by simp only [v, hu]; abel
      rw [this, inner_sub_left, hk.1, hun, sub_zero]
    exact collinear_of_orth hu0 hj' hk'
  rcases Lr.eq_empty_or_nonempty with he | ⟨k, hk⟩
  · rw [he, sum_empty] at hLpLr
    linarith
  · have hsub : Lr ⊆ {k} := fun j hj => mem_singleton.2 (hLr_sub j hj k hk)
    have hkh : k ≠ h := by
      intro e
      simp only [Lr, mem_filter, mem_univ, true_and] at hk
      rw [e] at hk
      linarith [hk.2]
    have := sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => hα j
    rw [sum_singleton] at this
    linarith [hdom k hkh]

end MWG.SocialChoice
