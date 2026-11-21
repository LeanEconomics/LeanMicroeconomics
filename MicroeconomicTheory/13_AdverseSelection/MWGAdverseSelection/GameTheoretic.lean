/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGAdverseSelection.Regular
import MWGAdverseSelection.WageGame

/-!
# The game-theoretic approach: Proposition 13.B.1

MWG, Section 13.B, pp. 443-445.

Two firms announce wages; workers then accept a highest wage if it is at least `r(θ)` (and are
indifferent otherwise only on ties, footnote 12). `worker_best` records that this is optimal for
the workers, so the pure SPNE are the pure Nash equilibria of `wageGame (firmProfit μ r)`.

* `proposition_13_B_1_i`: if `w* = Max W* > r(θ̲)` and `E[θ | r(θ) ≤ w'] > w'` just below `w*`,
  the unique pure SPNE has both firms offering `w*`; then exactly the types in `Θ(w*)` are
  employed and each earns `w*` (`proposition_13_B_1_i_outcome`).
* `proposition_13_B_1_ii`: if `w* = r(θ̲)`, the pure SPNE are exactly the wage pairs with both
  wages at most `w*`; there are several (`proposition_13_B_1_ii_multiple`) and in each firms earn
  zero and a worker of type `θ` earns `r(θ)`, as in the highest-wage competitive equilibrium.

Departure (correction 2). The proposition assumes only that `r` is strictly increasing. We add
that `r` is continuous on `[θ̲, θ̄]` (part of `RegularModel`): the proof's deviation to a wage just
below `w*` is profitable only if it attracts workers of positive probability. Without continuity
part (i) is false: `counterexample_13_B_1_i` (types uniform on `[1, 2]`, `r(1) = 0` and
`r(θ) = θ` for `θ > 1`) satisfies every printed hypothesis with `W* = {1}`, yet `(1/2, 1/2)` is
also a pure SPNE.
-/

namespace MWG.AdverseSelection

open MeasureTheory MWG.SimultaneousMoveGames

/-- **Section 13.B** (MWG, p. 444). In stage 2 a worker of type `θ` facing wages `w₀, w₁` earns at
most `max (max w₀ w₁) (r θ)`, which she attains by accepting a highest wage when it is at least
`r(θ)` and staying home otherwise. -/
theorem worker_best (rθ w₀ w₁ : ℝ) :
    (w₀ ≤ max (max w₀ w₁) rθ ∧ w₁ ≤ max (max w₀ w₁) rθ ∧ rθ ≤ max (max w₀ w₁) rθ) ∧
      (rθ ≤ max w₀ w₁ → max (max w₀ w₁) rθ = max w₀ w₁) ∧
      (max w₀ w₁ < rθ → max (max w₀ w₁) rθ = rθ) := by
  refine ⟨⟨?_, ?_, le_max_right _ _⟩, fun h => max_eq_left h, fun h => max_eq_right h.le⟩
  · exact (le_max_left _ _).trans (le_max_left _ _)
  · exact (le_max_right _ _).trans (le_max_left _ _)

/-- **Proposition 13.B.1(i)** (MWG, pp. 443-444). In the adverse selection model (with `r`
continuous, see correction 2), let `w* = Max W* > r(θ̲)` and suppose `E[θ | r(θ) ≤ w'] > w'` for
`w' ∈ (w* - ε, w*)`. Then the unique pure strategy SPNE has both firms offering `w*`. -/
theorem proposition_13_B_1_i {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ} (h : RegularModel μ θl θh r)
    {ws : ℝ} (hmax : IsGreatest (eqWages μ θl θh r) ws) (hws : r θl < ws) {ε : ℝ} (hε : 0 < ε)
    (hgap : ∀ w', ws - ε < w' → w' < ws → w' < condMean μ θl θh (acceptSet r w'))
    (w : Fin 2 → ℝ) :
    IsNashEquilibrium (wageGame (firmProfit μ r)) w ↔ w 0 = ws ∧ w 1 = ws := by
  have := h.dist.prob
  refine wageGame_unique (fun x => h.continuous.continuousAt.continuousWithinAt)
    (firmProfit_zero_nonneg h.dist h.meas)
    (ε := min ε (ws - r θl)) (lt_min hε (by linarith)) ((h.mem_eqWages_iff hws).1 hmax.1)
    (fun w hw => h.firmProfit_neg_of_gt_max hmax hw) ?_ w
  intro w' h1 h2
  have h1' : ws - ε < w' := lt_of_le_of_lt (by linarith [min_le_left ε (ws - r θl)]) h1
  have hr' : r θl < w' := lt_of_le_of_lt (by linarith [min_le_right ε (ws - r θl)]) h1
  have hpos := measure_acceptSet_pos h.dist h.dens h.cont hr'
  rw [firmProfit_eq h.dist h.meas hpos]
  exact mul_pos (ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _))
    (sub_pos.2 (hgap w' h1' h2))

/-- **Proposition 13.B.1(i)** (MWG, pp. 443-444), the outcome: in the SPNE employed workers
receive `w*` and a worker of type `θ` accepts employment iff `θ ∈ Θ(w*)`. -/
theorem proposition_13_B_1_i_outcome {r : ℝ → ℝ} {ws : ℝ} (w : Fin 2 → ℝ)
    (hw : w 0 = ws ∧ w 1 = ws) (θ : ℝ) :
    max (w 0) (w 1) = ws ∧ (r θ ≤ max (w 0) (w 1) ↔ θ ∈ acceptSet r ws) := by
  rw [hw.1, hw.2, max_self]
  exact ⟨rfl, Iff.rfl⟩

/-- **Proposition 13.B.1(ii)** (MWG, pp. 444-445). In the adverse selection model, if
`w* = Max W* = r(θ̲)`, the pure strategy SPNE are exactly the wage pairs `(w₁, w₂)` with
`wⱼ ≤ w*`. -/
theorem proposition_13_B_1_ii {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ}
    (h : RegularModel μ θl θh r) {ws : ℝ} (hmax : IsGreatest (eqWages μ θl θh r) ws)
    (hws : ws = r θl) (w : Fin 2 → ℝ) :
    IsNashEquilibrium (wageGame (firmProfit μ r)) w ↔ w 0 ≤ ws ∧ w 1 ≤ ws := by
  refine wageGame_flat (fun t ht => ?_) (fun t ht => h.firmProfit_neg_of_gt_max hmax ht) w
  rcases eq_or_lt_of_le (hws ▸ ht) with heq | hlt
  · rw [heq]; exact firmProfit_rl h.dist h.mono h.dens h.meas
  · exact firmProfit_of_lt h.dist h.mono.monotoneOn h.meas hlt

/-- **Proposition 13.B.1(ii)** (MWG, p. 444). There are multiple pure SPNEs. -/
theorem proposition_13_B_1_ii_multiple {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ}
    (h : RegularModel μ θl θh r) {ws : ℝ} (hmax : IsGreatest (eqWages μ θl θh r) ws)
    (hws : ws = r θl) :
    IsNashEquilibrium (wageGame (firmProfit μ r)) ![ws, ws] ∧
      IsNashEquilibrium (wageGame (firmProfit μ r)) ![ws - 1, ws] ∧
      (![ws, ws] : Fin 2 → ℝ) ≠ ![ws - 1, ws] := by
  refine ⟨(proposition_13_B_1_ii h hmax hws _).2 (by simp),
    (proposition_13_B_1_ii h hmax hws _).2 (by simp), fun he => ?_⟩
  have := congrFun he 0
  simp at this
  linarith

/-- **Proposition 13.B.1(ii)** (MWG, p. 445). In every pure SPNE both firms earn zero and a
worker of type `θ ∈ [θ̲, θ̄]` earns `r(θ)`, exactly her payoff in the competitive equilibrium
with wage `w*`. -/
theorem proposition_13_B_1_ii_payoffs {μ : Measure ℝ} {θl θh : ℝ} {r : ℝ → ℝ}
    (h : RegularModel μ θl θh r) {ws : ℝ} (hmax : IsGreatest (eqWages μ θl θh r) ws)
    (hws : ws = r θl) (w : Fin 2 → ℝ)
    (hne : IsNashEquilibrium (wageGame (firmProfit μ r)) w) :
    (∀ i, (wageGame (firmProfit μ r)).payoff i w = 0) ∧
      ∀ θ ∈ Set.Icc θl θh, max (max (w 0) (w 1)) (r θ) = r θ ∧ max ws (r θ) = r θ := by
  obtain ⟨h0, h1⟩ := (proposition_13_B_1_ii h hmax hws w).1 hne
  have hP : ∀ t, t ≤ ws → firmProfit μ r t = 0 := fun t ht => by
    rcases eq_or_lt_of_le (hws ▸ ht) with heq | hlt
    · rw [heq]; exact firmProfit_rl h.dist h.mono h.dens h.meas
    · exact firmProfit_of_lt h.dist h.mono.monotoneOn h.meas hlt
  refine ⟨fun i => ?_, fun θ hθ => ?_⟩
  · have hi : w i ≤ ws := by fin_cases i <;> simpa
    simp only [wageGame, hP _ hi]
    unfold wageShare; split_ifs <;> simp
  · have hl : θl ∈ Set.Icc θl θh := ⟨le_rfl, h.dist.lt.le⟩
    have hrθ : ws ≤ r θ := hws ▸ h.mono.monotoneOn hl hθ hθ.1
    exact ⟨max_eq_right ((max_le h0 h1).trans hrθ), max_eq_right hrθ⟩

end MWG.AdverseSelection
