/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMarketPower.RepeatedGames
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Exact average payoffs from pure action sequences

A tool for the folk theorem (MWG, Proposition 12.AA.5, p. 422): a feasible payoff vector
`v = ∑ₗ λₗ π(aₗ)` (a convex combination of pure stage payoffs with weights `λₗ > 0`) is the exact
discounted average payoff of a deterministic sequence of the profiles `aₗ`, and all continuation
payoffs stay within `(1 − δ)C` of `v`, for `δ` close to `1` (this is how the folk theorem
dispenses with public randomization; compare Fudenberg and Maskin 1991).

The sequence is built greedily. A "lag" vector `G_t` with `∑ₗ λₗ G_t(l) = 0` starts at `0`; each
period plays a profile `a_k` whose lag is `G_t(k) ≤ 0`, and updates
`G_{t+1}(l) = (G_t(l) − 1 + [l = k]/λ_k)/δ` (`schedG`). The continuation target
`w_t = v − (1 − δ)∑ₗ λₗ G_t(l) π(aₗ)` then satisfies `w_t = (1 − δ)π(a_{k_t}) + δw_{t+1}`
(`schedCont_rec`), and `G_t(l) ≤ U` throughout (`sched_invariant`), so
`|w_t − v| ≤ (1 − δ)(n + 1)UM` (`schedCont_close`).
-/

namespace MWG.MarketPower

open Finset

variable {n : ℕ}

open Classical in
/-- The profile index chosen at lag vector `G`: some `k` with `G(k) ≤ 0` (if any). -/
noncomputable def schedK (G : Fin (n + 1) → ℝ) : Fin (n + 1) :=
  if h : ∃ k, G k ≤ 0 then h.choose else 0

/-- One step of the lag recursion. -/
noncomputable def schedStep (wt : Fin (n + 1) → ℝ) (δ : ℝ) (G : Fin (n + 1) → ℝ) :
    Fin (n + 1) → ℝ :=
  fun l => (G l - 1 + (if l = schedK G then 1 / wt l else 0)) / δ

/-- The lag vectors `G_t`. -/
noncomputable def schedG (wt : Fin (n + 1) → ℝ) (δ : ℝ) : ℕ → Fin (n + 1) → ℝ
  | 0 => 0
  | t + 1 => schedStep wt δ (schedG wt δ t)

/-- The index played in period `t`. -/
noncomputable def schedIdx (wt : Fin (n + 1) → ℝ) (δ : ℝ) (t : ℕ) : Fin (n + 1) :=
  schedK (schedG wt δ t)

theorem schedK_spec {G : Fin (n + 1) → ℝ} (h : ∃ k, G k ≤ 0) : G (schedK G) ≤ 0 := by
  classical
  have e : schedK G = h.choose := by unfold schedK; simp [h]
  rw [e]
  exact h.choose_spec

/-- **The invariant of the schedule.** If `λ > 0`, `∑ λ = 1`, `1/λₗ ≤ U/2`, `δ ∈ [1/2, 1)` and
`(1 − δ)U ≤ 1`, then `∑ₗ λₗ G_t(l) = 0` and `G_t(l) ≤ U` for all `t` and `l`. -/
theorem sched_invariant {wt : Fin (n + 1) → ℝ} (hwt : ∀ l, 0 < wt l) (hsum : ∑ l, wt l = 1)
    {δ U : ℝ} (hδ : 1 / 2 ≤ δ) (hU : ∀ l, 1 / wt l ≤ U / 2) (hUδ : (1 - δ) * U ≤ 1) :
    ∀ t, (∑ l, wt l * schedG wt δ t l = 0) ∧ ∀ l, schedG wt δ t l ≤ U := by
  have hδ0 : 0 < δ := by linarith
  have hU0 : 0 ≤ U := by have := hU 0; have := one_div_pos.2 (hwt 0); linarith
  intro t
  induction t with
  | zero => simp [schedG, hU0]
  | succ t ih =>
    obtain ⟨hs, hle⟩ := ih
    set G := schedG wt δ t with hG
    have hex : ∃ k, G k ≤ 0 := by
      by_contra hno
      push Not at hno
      have : 0 < ∑ l, wt l * G l :=
        Finset.sum_pos (fun l _ => mul_pos (hwt l) (hno l)) Finset.univ_nonempty
      linarith
    have hk := schedK_spec hex
    set k := schedK G with hkdef
    have hstep : schedG wt δ (t + 1) = schedStep wt δ G := rfl
    rw [hstep]
    constructor
    · unfold schedStep
      have : ∑ l, wt l * ((G l - 1 + (if l = k then 1 / wt l else 0)) / δ) =
          (∑ l, wt l * G l - ∑ l, wt l + ∑ l, wt l * (if l = k then 1 / wt l else 0)) / δ := by
        rw [eq_div_iff hδ0.ne', Finset.sum_mul, ← Finset.sum_sub_distrib,
          ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun l _ => ?_
        field_simp
      have h1 : ∑ l, wt l * (if l = k then 1 / wt l else 0) = 1 := by
        rw [Finset.sum_eq_single k (fun l _ hl => by simp [hl]) (by simp)]
        simp [(hwt k).ne']
      rw [← hkdef, this, hs, hsum, h1]
      simp
    · intro l
      unfold schedStep
      rw [← hkdef]
      by_cases hl : l = k
      · simp only [hl, ite_true]
        rw [div_le_iff₀ hδ0]
        have := hU k
        nlinarith
      · simp only [hl, ite_false, add_zero]
        rw [div_le_iff₀ hδ0]
        have := hle l
        nlinarith

/-- The lower bound `λₗ G_t(l) ≥ −U` that follows from the invariant. -/
theorem sched_lower {wt : Fin (n + 1) → ℝ} (hwt : ∀ l, 0 < wt l) (hsum : ∑ l, wt l = 1)
    {G : Fin (n + 1) → ℝ} {U : ℝ} (hU0 : 0 ≤ U) (hs : ∑ l, wt l * G l = 0)
    (hle : ∀ l, G l ≤ U) (l : Fin (n + 1)) : -U ≤ wt l * G l := by
  have hsplit := Finset.add_sum_erase Finset.univ (fun m => wt m * G m) (Finset.mem_univ l)
  have h1 : ∑ m ∈ Finset.univ.erase l, wt m * G m ≤ ∑ m ∈ Finset.univ.erase l, wt m * U :=
    Finset.sum_le_sum fun m _ => mul_le_mul_of_nonneg_left (hle m) (hwt m).le
  have h2 : ∑ m ∈ Finset.univ.erase l, wt m * U ≤ ∑ m, wt m * U :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun m _ _ =>
      mul_nonneg (hwt m).le hU0
  have h3 : ∑ m, wt m * U = U := by rw [← Finset.sum_mul, hsum, one_mul]
  linarith

/-- The continuation target `w_t(i) = v_i − (1 − δ)∑ₗ λₗ G_t(l) π_i(aₗ)`. -/
noncomputable def schedCont (wt : Fin (n + 1) → ℝ) (δ : ℝ) (u : Fin (n + 1) → ℝ) (v : ℝ)
    (t : ℕ) : ℝ :=
  v - (1 - δ) * ∑ l, wt l * schedG wt δ t l * u l

/-- **The recursion of the continuation targets**: `w_t = (1 − δ)π(a_{k_t}) + δw_{t+1}`, when
`v = ∑ₗ λₗ uₗ`. -/
theorem schedCont_rec {wt : Fin (n + 1) → ℝ} (hwt : ∀ l, 0 < wt l) {δ : ℝ} (hδ0 : 0 < δ)
    (u : Fin (n + 1) → ℝ) {v : ℝ} (hv : v = ∑ l, wt l * u l) (t : ℕ) :
    schedCont wt δ u v t = (1 - δ) * u (schedIdx wt δ t) + δ * schedCont wt δ u v (t + 1) := by
  unfold schedCont schedIdx
  set G := schedG wt δ t with hG
  set k := schedK G with hk
  have hstep : schedG wt δ (t + 1) = schedStep wt δ G := rfl
  rw [hstep]
  have hsum : δ * ∑ l, wt l * schedStep wt δ G l * u l =
      ∑ l, wt l * G l * u l - ∑ l, wt l * u l + u k := by
    rw [Finset.mul_sum]
    have : ∀ l, δ * (wt l * schedStep wt δ G l * u l) =
        wt l * G l * u l - wt l * u l + (if l = k then u l else 0) := by
      intro l
      unfold schedStep
      rw [← hk]
      by_cases hl : l = k
      · simp only [hl, ite_true]; have := (hwt k).ne'; field_simp
      · simp only [hl, ite_false, add_zero]; field_simp
    rw [Finset.sum_congr rfl fun l _ => this l, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_ite_eq']
    simp
  have e : δ * (v - (1 - δ) * ∑ l, wt l * schedStep wt δ G l * u l) =
      δ * v - (1 - δ) * (δ * ∑ l, wt l * schedStep wt δ G l * u l) := by ring
  rw [e, hsum, ← hv]
  ring

/-- **Continuation targets stay close to `v`**: `|w_t − v| ≤ (1 − δ)(n + 1)UM` when
`|uₗ| ≤ M`. -/
theorem schedCont_close {wt : Fin (n + 1) → ℝ} (hwt : ∀ l, 0 < wt l) (hsum : ∑ l, wt l = 1)
    {δ U M : ℝ} (hδ : 1 / 2 ≤ δ) (hδ1 : δ < 1) (hU : ∀ l, 1 / wt l ≤ U / 2)
    (hUδ : (1 - δ) * U ≤ 1) (u : Fin (n + 1) → ℝ) (hu : ∀ l, |u l| ≤ M) (v : ℝ) (t : ℕ) :
    |schedCont wt δ u v t - v| ≤ (1 - δ) * ((n + 1) * U * M) := by
  obtain ⟨hs, hle⟩ := sched_invariant hwt hsum hδ hU hUδ t
  have hU0 : 0 ≤ U := by have := hU 0; have := one_div_pos.2 (hwt 0); linarith
  have hM : 0 ≤ M := (abs_nonneg _).trans (hu 0)
  have hwt1 : ∀ l, wt l ≤ 1 := fun l => by
    rw [← hsum]
    exact Finset.single_le_sum (fun m _ => (hwt m).le) (Finset.mem_univ l)
  have hterm : ∀ l, |wt l * schedG wt δ t l * u l| ≤ U * M := by
    intro l
    have h1 := sched_lower hwt hsum hU0 hs hle l
    have h2 : wt l * schedG wt δ t l ≤ U := by
      have := hle l
      have := mul_le_mul_of_nonneg_left this (hwt l).le
      nlinarith [hwt1 l]
    rw [abs_mul]
    exact mul_le_mul (abs_le.2 ⟨h1, h2⟩) (hu l) (abs_nonneg _) hU0
  unfold schedCont
  rw [show v - (1 - δ) * ∑ l, wt l * schedG wt δ t l * u l - v =
    -((1 - δ) * ∑ l, wt l * schedG wt δ t l * u l) by ring, abs_neg, abs_mul,
    abs_of_pos (by linarith : (0 : ℝ) < 1 - δ)]
  refine mul_le_mul_of_nonneg_left ?_ (by linarith)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun l _ => hterm l).trans ?_
  simp [mul_assoc]

end MWG.MarketPower
