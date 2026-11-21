/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation

/-!
# Off-path beliefs after an informed player's move are unrestricted by consistency

MWG, Exercise 9.C.6 for Exercise 9.C.5 (p. 304), Definition 9.C.4 (p. 290). When a player
with finitely many types (prior `p`, full support) moves first and the move `m` is off the
equilibrium path, type-dependent trembles can generate any belief `q` after `m` as a limit of
Bayes posteriors (`signal_belief_consistent`): type `t` trembles to `m` with probability
`εₙ(t) = (q(t) + 1/(n+1)) / (p(t) (n+1))`. So consistency imposes nothing beyond Bayes' rule on
the path, and in a game in which the informed player moves once (as Ms. P in Exercise 9.C.5)
the sequential equilibria are the weak PBE. The model of Exercise 9.C.5 in `Informed.lean`
has a continuum of types, for which Definition 9.C.4 is not defined; this module proves the
finite-type statement.
-/

namespace MWG.DynamicGames

open Filter Topology

/-- **Exercise 9.C.6 for 9.C.5** (MWG, pp. 290 and 304). With finitely many types of full
prior support `p`, every belief `q` about the type after an off-path move is the limit of the
Bayes posteriors `p(t) εₙ(t) / ∑ₛ p(s) εₙ(s)` for some totally mixed trembles `εₙ → 0`. -/
theorem signal_belief_consistent {T : Type*} [Fintype T] (p q : T → ℝ) (hp : ∀ t, 0 < p t)
    (hq0 : ∀ t, 0 ≤ q t) (hq1 : ∑ t, q t = 1) :
    ∃ e : ℕ → T → ℝ, (∀ n t, 0 < e n t) ∧ (∀ t, Tendsto (fun n => e n t) atTop (𝓝 0)) ∧
      ∀ t, Tendsto (fun n => p t * e n t / ∑ s, p s * e n s) atTop (𝓝 (q t)) := by
  set c : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hc
  have hc0 : ∀ n, 0 < c n := fun n => by simp only [hc]; positivity
  have hclim : Tendsto c atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨fun n t => (q t + c n) * c n / p t, fun n t => ?_, fun t => ?_, fun t => ?_⟩
  · have := hq0 t
    have := hc0 n
    have := hp t
    positivity
  · have h := ((tendsto_const_nhds (x := q t)).add hclim).mul hclim
    rw [add_zero, mul_zero] at h
    simpa using h.div_const (p t)
  · have hterm : ∀ n s, p s * ((q s + c n) * c n / p s) = (q s + c n) * c n := fun n s => by
      field_simp [(hp s).ne']
    have hsum : ∀ n, ∑ s, p s * ((q s + c n) * c n / p s) =
        (1 + Fintype.card T * c n) * c n := by
      intro n
      simp only [hterm, ← Finset.sum_mul, Finset.sum_add_distrib, hq1, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
    have hratio : ∀ n, p t * ((q t + c n) * c n / p t) /
        ∑ s, p s * ((q s + c n) * c n / p s) = (q t + c n) / (1 + Fintype.card T * c n) := by
      intro n
      rw [hterm, hsum]
      have := hc0 n
      have : 0 < 1 + Fintype.card T * c n := by positivity
      field_simp
    simp only [hratio]
    have h : Tendsto (fun n => (q t + c n) / (1 + Fintype.card T * c n)) atTop
        (𝓝 ((q t + 0) / (1 + Fintype.card T * 0))) :=
      ((tendsto_const_nhds (x := q t)).add hclim).div
        ((tendsto_const_nhds (x := (1 : ℝ))).add (hclim.const_mul (Fintype.card T : ℝ)))
        (by norm_num)
    rwa [add_zero, mul_zero, add_zero, div_one] at h

/-- **Exercise 9.C.6 for 9.C.5, an instance** (MWG, p. 304): two types with prior `(1/2, 1/2)`;
the belief putting probability one on the first type is a limit of Bayes posteriors. -/
theorem signal_belief_consistent_instance :
    ∃ e : ℕ → Fin 2 → ℝ, (∀ n t, 0 < e n t) ∧ (∀ t, Tendsto (fun n => e n t) atTop (𝓝 0)) ∧
      ∀ t, Tendsto (fun n => (1 / 2 : ℝ) * e n t / ∑ s, (1 / 2 : ℝ) * e n s) atTop
        (𝓝 (![1, 0] t)) :=
  signal_belief_consistent (fun _ => 1 / 2) ![1, 0] (fun _ => by norm_num)
    (fun t => by fin_cases t <;> norm_num) (by simp [Fin.sum_univ_two])

end MWG.DynamicGames
