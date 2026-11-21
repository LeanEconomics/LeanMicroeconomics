/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPrincipalAgent.ExerciseC1Opt
import MWGPrincipalAgent.ExerciseC4

/-!
# Exercise 14.C.1: strict downward distortion with `N` states

MWG, Exercise 14.C.1, p. 508 (model of `ExerciseC1` and `ExerciseC1Opt`).

* `c1_VS_update`: changing the effort of state `k` changes the virtual surplus by
  `p_k [S_k(y) - S_k(e_k)] - (Σ_{i>k} p_i) [D_k(y) - D_k(e_k)]`.
* `exercise_14_C_1_strict`: if the first-best efforts are strictly increasing, `e*_k > 0`,
  `π - g(·, θ_k)` and `D_k` are differentiable at `e*_k` with `D_k'(e*_k) > 0`, then every optimal
  contract has `e_k < e*_k` for every state below the top: the distortion is strict.
* `exercise_14_C_1_strict_instance`: the instance of `exercise_14_C_1_instance`.
-/

namespace MWG.PrincipalAgent

open Finset Set Filter Topology

/-- Changing the effort of one state `k < N` changes the virtual surplus by
`p_k [S_k(y) - S_k(e_k)] - (Σ_{k<i<N} p_i) [D_k(y) - D_k(e_k)]`. -/
theorem c1_VS_update {g : ℝ → ℝ → ℝ} {θ p e : ℕ → ℝ} {prof : ℝ → ℝ} {c : ℝ} {N k : ℕ}
    (hk : k < N) (y : ℝ) :
    c1VS g θ p prof c N (Function.update e k y) - c1VS g θ p prof c N e =
      p k * ((prof y - g y (θ k)) - (prof (e k) - g (e k) (θ k))) -
        (∑ i ∈ (range N).filter (k < ·), p i) * (c1D g θ k y - c1D g θ k (e k)) := by
  unfold c1VS
  rw [← sum_sub_distrib]
  have hterm : ∀ i ∈ range N,
      p i * (prof (Function.update e k y i) - g (Function.update e k y i) (θ i) - c -
        c1Rent g θ (Function.update e k y) i) -
        p i * (prof (e i) - g (e i) (θ i) - c - c1Rent g θ e i) =
      (if i = k then p k * ((prof y - g y (θ k)) - (prof (e k) - g (e k) (θ k))) else 0) -
        (if k < i then p i * (c1D g θ k y - c1D g θ k (e k)) else 0) := by
    intro i hi
    have hR : c1Rent g θ (Function.update e k y) i - c1Rent g θ e i =
        if k < i then c1D g θ k y - c1D g θ k (e k) else 0 := by
      unfold c1Rent
      rw [← sum_sub_distrib]
      by_cases hki : k < i
      · simp only [hki, ↓reduceIte]
        rw [← sum_erase_add _ _ (mem_range.2 hki)]
        rw [sum_eq_zero fun j hj => by
          rw [Function.update_of_ne (ne_of_mem_erase hj)]; ring]
        simp
      · simp only [hki, ↓reduceIte]
        refine sum_eq_zero fun j hj => ?_
        have : j ≠ k := by have := mem_range.1 hj; omega
        rw [Function.update_of_ne this]; ring
    by_cases hik : i = k
    · subst hik
      have hR' := hR
      simp only [lt_irrefl, ↓reduceIte] at hR'
      simp only [Function.update_self, ↓reduceIte, lt_irrefl]
      linear_combination (-p i) * hR'
    · simp only [Function.update_of_ne hik, hik, ↓reduceIte]
      by_cases hki : k < i
      · simp only [hki, ↓reduceIte] at hR ⊢
        linear_combination (-p i) * hR
      · simp only [hki, ↓reduceIte] at hR ⊢
        linear_combination (-p i) * hR
  rw [sum_congr rfl hterm, sum_sub_distrib, sum_ite_eq' (range N) k]
  simp only [mem_range.2 hk, ↓reduceIte]
  rw [← sum_filter, sum_mul]

/-- **Exercise 14.C.1** (MWG, p. 508), strict downward distortion. In addition to the assumptions
of `exercise_14_C_1_distortion`, let the first-best efforts be strictly increasing, and for a
state `k` below the top (`k + 1 < N`) let `e*_k > 0`, `π - g(·, θ_k)` be differentiable at `e*_k`
and `D_k` differentiable at `e*_k` with `D_k'(e*_k) > 0`. Then every optimal contract has
`e_k < e*_k`. -/
theorem exercise_14_C_1_strict {g : ℝ → ℝ → ℝ} {θ p w e estar : ℕ → ℝ} {prof : ℝ → ℝ}
    {c : ℝ} {N : ℕ} (hN : 0 < N) (hp : ∀ i < N, 0 < p i) (hg0 : ∀ t, g 0 t = 0)
    (hsc : ∀ i j, i < j → StrictMonoOn (fun x => g x (θ i) - g x (θ j)) (Ici 0))
    (hs0 : ∀ i < N, 0 ≤ estar i)
    (hsmax : ∀ i < N, ∀ x, 0 ≤ x → x ≠ estar i →
      prof x - g x (θ i) < prof (estar i) - g (estar i) (θ i))
    (hss : ∀ i j, i < j → j < N → estar i < estar j)
    (hf : C1Feas g θ c N w e)
    (hopt : ∀ w' e', C1Feas g θ c N w' e' → c1Prof p prof N w' e' ≤ c1Prof p prof N w e)
    {k : ℕ} {sk dD : ℝ} (hk : k + 1 < N) (hpos : 0 < estar k)
    (hSd : HasDerivAt (fun x => prof x - g x (θ k)) sk (estar k))
    (hDd : HasDerivAt (c1D g θ k) dD (estar k)) (hdD : 0 < dD) : e k < estar k := by
  have hsm : ∀ i j, i ≤ j → j < N → estar i ≤ estar j := fun i j hij hj => by
    rcases hij.lt_or_eq with h | h
    · exact (hss i j h hj).le
    · rw [h]
  obtain ⟨hdown, -⟩ := exercise_14_C_1_distortion hN hp hg0 hsc hs0 hsmax hsm hf hopt
  obtain ⟨hmono, -, -, hmax⟩ := exercise_14_C_1_opt hN hp hg0 hsc hf hopt
  rcases (hdown k (by omega)).lt_or_eq with h | h
  · exact h
  exfalso
  have hsk : sk = 0 := by
    refine IsLocalMax.hasDerivAt_eq_zero ?_ hSd
    filter_upwards [Ioi_mem_nhds hpos] with x hx
    rcases eq_or_ne x (estar k) with rfl | hne
    · exact le_rfl
    · exact (hsmax k (by omega) x (le_of_lt hx) hne).le
  set P := ∑ i ∈ (range N).filter (k < ·), p i
  have hP : 0 < P := by
    have hmem : k + 1 ∈ (range N).filter (k < ·) := mem_filter.2 ⟨mem_range.2 hk, by omega⟩
    have := single_le_sum (f := p) (fun i hi => (hp i (mem_range.1 (mem_filter.1 hi).1)).le)
      hmem
    linarith [hp (k + 1) hk]
  have hψ : HasDerivAt (fun x => p k * (prof x - g x (θ k)) - P * c1D g θ k x)
      (p k * sk - P * dD) (estar k) := (hSd.const_mul _).sub (hDd.const_mul _)
  have hneg : p k * sk - P * dD < 0 := by rw [hsk]; nlinarith
  set L : ℝ := if k = 0 then 0 else max 0 (e (k - 1))
  have hL0 : 0 ≤ L := by simp only [L]; split_ifs <;> simp
  have hL : L < estar k := by
    simp only [L]
    split_ifs with hk0
    · exact hpos
    · exact max_lt hpos (lt_of_le_of_lt (hdown (k - 1) (by omega)) (hss _ _ (by omega) (by omega)))
  obtain ⟨y, hy1, hy2⟩ := ((c4_left_gt hψ hneg).and (Ioo_mem_nhdsLT hL)).exists
  set e' := Function.update e k y
  have he' : ∀ i < N, 0 ≤ e' i := by
    intro i hi
    by_cases hik : i = k
    · subst hik; simp only [e', Function.update_self]; linarith [hy2.1]
    · simp only [e', Function.update_of_ne hik]; exact hf.1 i hi
  have hm' : ∀ i j, i ≤ j → j < N → e' i ≤ e' j := by
    intro i j hij hj
    by_cases hik : i = k
    · subst hik
      by_cases hjk : j = i
      · subst hjk; exact le_rfl
      · simp only [e', Function.update_self, Function.update_of_ne hjk]
        rw [← h] at hy2
        exact hy2.2.le.trans (hmono _ _ hij hj)
    · by_cases hjk : j = k
      · subst hjk
        simp only [e', Function.update_self, Function.update_of_ne hik]
        have hj0 : j ≠ 0 := by omega
        have h1 : e i ≤ e (j - 1) := hmono _ _ (by omega) (by omega)
        have h2 : e (j - 1) ≤ L := by simp only [L, hj0, ↓reduceIte]; exact le_max_right _ _
        linarith [hy2.1]
      · simp only [e', Function.update_of_ne hik, Function.update_of_ne hjk]
        exact hmono i j hij hj
  have hup := c1_VS_update (g := g) (θ := θ) (p := p) (e := e) (prof := prof) (c := c)
    (show k < N by omega) y
  have hle := hmax e' he' hm'
  rw [← h] at hy1
  linarith

/-- **Exercise 14.C.1, strict distortion in the instance** (MWG, p. 508): in the instance of
`exercise_14_C_1_instance` (`e*_i = i + 1`), the theorem gives `e_0 < e*_0 = 1` for the optimal
contract (whose effort is `2/3`). -/
theorem exercise_14_C_1_strict_instance :
    let e : ℕ → ℝ := fun i => if i = 0 then 2 / 3 else 2
    c1Ext 2 e 0 < (fun i : ℕ => (i : ℝ) + 1) 0 := by
  intro e
  obtain ⟨hf, hopt, -, -⟩ := exercise_14_C_1_instance
  set g : ℝ → ℝ → ℝ := fun x t => x ^ 2 / (2 * t)
  set θ : ℕ → ℝ := fun i => (i : ℝ) + 1
  have hg0 : ∀ t, g 0 t = 0 := fun t => by simp [g]
  have hsc : ∀ i j, i < j → StrictMonoOn (fun x => g x (θ i) - g x (θ j)) (Ici 0) := by
    intro i j hij x hx y hy hxy
    have hij' : (i : ℝ) < j := by exact_mod_cast hij
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    simp only [g, θ, Set.mem_Ici] at hx hy ⊢
    have hk : 1 / (2 * ((j : ℝ) + 1)) < 1 / (2 * ((i : ℝ) + 1)) :=
      one_div_lt_one_div_of_lt (by positivity) (by linarith)
    have hxy2 : x ^ 2 < y ^ 2 := by nlinarith
    rw [div_eq_mul_one_div (x ^ 2), div_eq_mul_one_div (x ^ 2), div_eq_mul_one_div (y ^ 2),
      div_eq_mul_one_div (y ^ 2)]
    nlinarith
  have hsmax : ∀ i < 2, ∀ x : ℝ, 0 ≤ x → x ≠ (fun i : ℕ => (i : ℝ) + 1) i →
      id x - g x (θ i) < id ((fun i : ℕ => (i : ℝ) + 1) i) -
        g ((fun i : ℕ => (i : ℝ) + 1) i) (θ i) := by
    intro i _ x _ hne
    have hpos : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    simp only [id, g, θ]
    have : ((i : ℝ) + 1) - ((i : ℝ) + 1) ^ 2 / (2 * ((i : ℝ) + 1)) -
        (x - x ^ 2 / (2 * ((i : ℝ) + 1))) = (x - ((i : ℝ) + 1)) ^ 2 / (2 * ((i : ℝ) + 1)) := by
      field_simp; ring
    have h2 : 0 < (x - ((i : ℝ) + 1)) ^ 2 / (2 * ((i : ℝ) + 1)) :=
      div_pos (by positivity) (by positivity)
    linarith
  refine exercise_14_C_1_strict (g := g) (θ := θ) (p := fun _ => 1 / 2) (prof := id) (c := 0)
    (N := 2) (k := 0) (sk := 1 - 1) (dD := 1 / 2) (by norm_num) (fun _ _ => by norm_num) hg0
    hsc (fun i _ => by positivity) hsmax (fun i j hij _ => by
      have : (i : ℝ) < j := by exact_mod_cast hij
      change (i : ℝ) + 1 < (j : ℝ) + 1
      linarith) hf hopt (by norm_num) (by norm_num) ?_ ?_ (by norm_num)
  · have hfun : (fun x => id x - g x (θ 0)) = fun x : ℝ => x - x ^ 2 / 2 := by
      funext x; simp [g, θ]
    rw [hfun]
    have h := (hasDerivAt_id' (1 : ℝ)).sub ((hasDerivAt_pow 2 (1 : ℝ)).div_const 2)
    convert h using 1 <;> norm_num
  · have := (hasDerivAt_pow 2 (1 : ℝ)).div_const 4
    have hfun : c1D g θ 0 = fun x : ℝ => x ^ 2 / 4 := by
      funext x; simp only [c1D, g, θ]; norm_num; ring
    rw [hfun]
    convert this using 1 <;> norm_num

end MWG.PrincipalAgent
