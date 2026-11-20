/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGNoncooperativeGames.Mixed
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Mixed strategies as plans contingent on a private uniform signal

MWG, Section 7.E, small type on p. 232: a player can form a mixed strategy by observing a
private signal `θ` uniformly distributed on `[0, 1]` and choosing a pure strategy `s(θ)` for
each realization. `mixedStrategy_signal` proves that every mixed strategy `σ` on a finite set
`S` arises this way: `[0, 1)` (which has full measure in `[0, 1]`) splits into pairwise
disjoint measurable sets `A s`, the plan plays `s` on `A s`, and `A s` has Lebesgue measure
`σ(s)`. The sets are consecutive intervals of lengths `σ(s)`.
-/

namespace MWG.NoncooperativeGames

open MeasureTheory

/-- Partial sums `c n = ∑_{j < n} σ j` of a probability vector on `Fin M`. -/
noncomputable def signalCut {M : ℕ} (σ : Fin M → ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin M => j.val < n), σ j

theorem signalCut_zero {M : ℕ} (σ : Fin M → ℝ) : signalCut σ 0 = 0 := by
  simp [signalCut]

theorem signalCut_mono {M : ℕ} {σ : Fin M → ℝ} (hσ : ∀ j, 0 ≤ σ j) {n n' : ℕ}
    (h : n ≤ n') : signalCut σ n ≤ signalCut σ n' := by
  unfold signalCut
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun j _ _ => hσ j
  intro j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  omega

theorem signalCut_full {M : ℕ} (σ : Fin M → ℝ) : signalCut σ M = ∑ j, σ j := by
  unfold signalCut
  congr 1
  ext j
  simp

theorem signalCut_succ {M : ℕ} (σ : Fin M → ℝ) (j : Fin M) :
    signalCut σ (j.val + 1) = signalCut σ j.val + σ j := by
  unfold signalCut
  simp only [Finset.sum_filter]
  have hj : σ j = ∑ i, if i = j then σ i else 0 := by simp
  rw [hj, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : i = j
  · subst h
    simp
  · have : i.val ≠ j.val := fun he => h (Fin.ext he)
    by_cases hi : i.val < j.val
    · simp [hi, h, show i.val < j.val + 1 by omega]
    · simp [hi, h, show ¬ i.val < j.val + 1 by omega]

/-- **Section 7.E, small type** (MWG, p. 232). Every mixed strategy `σ` over a finite set `S`
can be generated from a private signal uniformly distributed on `[0, 1]`: there are pairwise
disjoint measurable sets `A s` covering `[0, 1)` with Lebesgue measure `σ(s)`, and the plan
"play `s` when `θ ∈ A s`" selects each `s` with probability `σ(s)`. -/
theorem mixedStrategy_signal {S : Type*} [Fintype S] {σ : S → ℝ} (hσ : IsMixedStrategy σ) :
    ∃ A : S → Set ℝ, (∀ s, MeasurableSet (A s)) ∧ (∀ s s', s ≠ s' → Disjoint (A s) (A s')) ∧
      (⋃ s, A s) = Set.Ico 0 1 ∧ ∀ s, volume (A s) = ENNReal.ofReal (σ s) := by
  set e := Fintype.equivFin S
  set M := Fintype.card S
  let τ : Fin M → ℝ := fun j => σ (e.symm j)
  have hτ : ∀ j, 0 ≤ τ j := fun j => hσ.1 _
  have hsum : ∑ j, τ j = 1 := by
    rw [← hσ.2]
    exact Fintype.sum_equiv e.symm _ _ fun _ => rfl
  let c := signalCut τ
  refine ⟨fun s => Set.Ico (c (e s).val) (c ((e s).val + 1)), fun s => measurableSet_Ico,
    fun s s' hne => ?_, ?_, fun s => ?_⟩
  · have hne' : (e s).val ≠ (e s').val := fun h => hne (e.injective (Fin.ext h))
    rw [Set.disjoint_left]
    rintro θ ⟨h1, h2⟩ ⟨h3, h4⟩
    rcases lt_or_gt_of_ne hne' with h | h
    · have := signalCut_mono hτ (show (e s).val + 1 ≤ (e s').val by omega)
      linarith
    · have := signalCut_mono hτ (show (e s').val + 1 ≤ (e s).val by omega)
      linarith
  · ext θ
    simp only [Set.mem_iUnion, Set.mem_Ico]
    constructor
    · rintro ⟨s, h1, h2⟩
      have h0 := signalCut_mono hτ (Nat.zero_le (e s).val)
      have hM := signalCut_mono hτ (show (e s).val + 1 ≤ M from (e s).isLt)
      rw [signalCut_zero] at h0
      rw [signalCut_full, hsum] at hM
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨h0, h1⟩
      have hex : ∃ n, θ < c (n + 1) := ⟨M, by
        have := signalCut_mono hτ (show M ≤ M + 1 by omega)
        rw [signalCut_full, hsum] at this
        linarith⟩
      let m := Nat.find hex
      have hm : θ < c (m + 1) := Nat.find_spec hex
      have hM1 : 0 < M := by
        refine Fintype.card_pos_iff.2 ?_
        by_contra hne
        rw [not_nonempty_iff] at hne
        have := hσ.2
        simp at this
      have hθM : θ < c ((M - 1) + 1) := by
        rw [Nat.sub_add_cancel hM1]
        change θ < signalCut τ M
        rw [signalCut_full, hsum]
        exact h1
      have hmM : m < M := by
        have : m ≤ M - 1 := Nat.find_min' hex hθM
        omega
      have hcm : c m ≤ θ := by
        rcases Nat.eq_zero_or_pos m with h | h
        · rw [h]
          change signalCut τ 0 ≤ θ
          rw [signalCut_zero]
          exact h0
        · have := Nat.find_min hex (show m - 1 < m by omega)
          rw [show m - 1 + 1 = m by omega] at this
          exact not_lt.1 this
      refine ⟨e.symm ⟨m, hmM⟩, ?_, ?_⟩ <;> simp only [Equiv.apply_symm_apply] <;> assumption
  · rw [Real.volume_Ico]
    congr 1
    change signalCut τ ((e s).val + 1) - signalCut τ (e s).val = σ s
    rw [signalCut_succ]
    simp [τ]

/-- A concrete instance: the degenerate mixed strategy on heads (`0 : Fin 2`) is generated by
a uniform signal. -/
theorem mixedStrategy_signal_pure :
    ∃ A : Fin 2 → Set ℝ, (∀ s, MeasurableSet (A s)) ∧
      (∀ s s', s ≠ s' → Disjoint (A s) (A s')) ∧ (⋃ s, A s) = Set.Ico 0 1 ∧
      ∀ s, volume (A s) = ENNReal.ofReal (pureMixed (0 : Fin 2) s) :=
  mixedStrategy_signal (isMixedStrategy_pureMixed 0)

end MWG.NoncooperativeGames
