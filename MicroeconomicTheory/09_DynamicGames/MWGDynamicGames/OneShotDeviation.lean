/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# The one-shot deviation principle for infinite-horizon discounted games

MWG, Appendix A of Chapter 9 (pp. 296-299): the subgame perfection of the stationary profile
of the infinite horizon bargaining game is checked by one-stage deviations; this module states
and proves the principle behind that check in general.

A multi-stage game with observed actions: players `i ∈ I` choose actions `a_i ∈ A i`
simultaneously in every period `t = 0, 1, 2, …`; a history is the list of the action profiles
played so far (most recent first); a pure strategy of player `i` (`OSProfile`) maps histories
to actions. Player `i`'s per-period payoff `u i h x` may depend on the history `h` and the
current profile `x`; payoffs are bounded (`|u| ≤ M`) and discounted by `δ ∈ [0, 1)`.
`osValue u δ σ h i = ∑ₙ δⁿ u_i(hₙ, σ(hₙ))` is player `i`'s continuation payoff from history `h`.

* `osValue_succ`: the recursion `V(h) = u_i(h, σ(h)) + δ V(σ(h) :: h)`.
* `oneShot_deviation_principle_discounted`: if player `i` cannot gain at any history by a one-period
  deviation (deviating now and following `σ_i` afterwards), then no strategy of player `i`
  (deviating at finitely or infinitely many histories) gains at any history.
* `oneShot_deviation_principle_discounted_iff`: hence `σ` is subgame perfect (no player gains by any
  change of strategy at any history) iff there is no profitable one-shot deviation.
* Instance: the infinitely repeated prisoners' dilemma (`(C, C) ↦ 2`, `(D, C) ↦ 3`, `(C, D) ↦
  0`, `(D, D) ↦ 1`) with grim trigger strategies: subgame perfect iff `δ ≥ 1/2`
  (`grim_trigger_spe_iff`).
-/

namespace MWG.DynamicGames

variable {I : Type*} [DecidableEq I] {A : I → Type*}

/-- A history: the action profiles played so far, the most recent first. -/
abbrev OSHist (A : I → Type*) := List ((i : I) → A i)

/-- A pure strategy profile of the multi-stage game. -/
abbrev OSProfile (A : I → Type*) := (i : I) → OSHist A → A i

/-- The action profile played at history `h`. -/
def osPlay (σ : OSProfile A) (h : OSHist A) : (i : I) → A i := fun i => σ i h

/-- The history after `n` further periods of play according to `σ`. -/
def osPath (σ : OSProfile A) : OSHist A → ℕ → OSHist A
  | h, 0 => h
  | h, n + 1 => osPath σ (osPlay σ h :: h) n

/-- Player `i`'s discounted payoff from history `h` on when `σ` is played. -/
noncomputable def osValue (u : I → OSHist A → ((i : I) → A i) → ℝ) (δ : ℝ) (σ : OSProfile A)
    (h : OSHist A) (i : I) : ℝ :=
  ∑' n : ℕ, δ ^ n * u i (osPath σ h n) (osPlay σ (osPath σ h n))

omit [DecidableEq I] in
theorem osPath_length (σ : OSProfile A) (n : ℕ) (h : OSHist A) :
    (osPath σ h n).length = h.length + n := by
  induction n generalizing h with
  | zero => rfl
  | succ n ih =>
    simp only [osPath, ih, List.length_cons]
    omega

omit [DecidableEq I] in
/-- Bounded discounted payoffs are summable. -/
theorem osValue_summable {u : I → OSHist A → ((i : I) → A i) → ℝ} {δ M : ℝ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (hu : ∀ i h x, |u i h x| ≤ M) (σ : OSProfile A) (h : OSHist A) (i : I) :
    Summable fun n : ℕ => δ ^ n * u i (osPath σ h n) (osPlay σ (osPath σ h n)) := by
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hδ0 hδ1).mul_right M)
    fun n => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hδ0 n)]
  exact mul_le_mul_of_nonneg_left (hu _ _ _) (pow_nonneg hδ0 n)

omit [DecidableEq I] in
/-- The continuation payoff is bounded by `M/(1 − δ)`. -/
theorem osValue_abs_le {u : I → OSHist A → ((i : I) → A i) → ℝ} {δ M : ℝ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (hu : ∀ i h x, |u i h x| ≤ M) (σ : OSProfile A) (h : OSHist A) (i : I) :
    |osValue u δ σ h i| ≤ M / (1 - δ) := by
  have hs := osValue_summable hδ0 hδ1 hu σ h i
  have hg := (summable_geometric_of_lt_one hδ0 hδ1).mul_right M
  have hle : ∀ n : ℕ, |δ ^ n * u i (osPath σ h n) (osPlay σ (osPath σ h n))| ≤ δ ^ n * M := by
    intro n
    rw [abs_mul, abs_of_nonneg (pow_nonneg hδ0 n)]
    exact mul_le_mul_of_nonneg_left (hu _ _ _) (pow_nonneg hδ0 n)
  have h1 : |osValue u δ σ h i| ≤ ∑' n : ℕ, δ ^ n * M := by
    unfold osValue
    rw [abs_le]
    constructor
    · rw [← tsum_neg]
      exact hg.neg.tsum_le_tsum (fun n => neg_le_of_abs_le (hle n)) hs
    · exact hs.tsum_le_tsum (fun n => le_of_abs_le (hle n)) hg
  rw [tsum_mul_right, tsum_geometric_of_lt_one hδ0 hδ1] at h1
  rw [div_eq_inv_mul]
  exact h1

omit [DecidableEq I] in
/-- **The recursion** `V(h) = u_i(h, σ(h)) + δ V(σ(h) :: h)`. -/
theorem osValue_succ {u : I → OSHist A → ((i : I) → A i) → ℝ} {δ M : ℝ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (hu : ∀ i h x, |u i h x| ≤ M) (σ : OSProfile A) (h : OSHist A) (i : I) :
    osValue u δ σ h i = u i h (osPlay σ h) + δ * osValue u δ σ (osPlay σ h :: h) i := by
  unfold osValue
  rw [(osValue_summable hδ0 hδ1 hu σ h i).tsum_eq_zero_add, ← tsum_mul_left]
  simp only [pow_zero, one_mul, osPath, pow_succ]
  congr 1
  refine tsum_congr fun n => ?_
  ring

/-- Changing player `i`'s strategy changes only her action. -/
theorem osPlay_update (σ : OSProfile A) (i : I) (τ : OSHist A → A i) (h : OSHist A) :
    osPlay (Function.update σ i τ) h = Function.update (osPlay σ h) i (τ h) := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp [osPlay]
  · simp [osPlay, Function.update_of_ne hj]

omit [DecidableEq I] in
/-- Profiles that agree on all histories of length at least `L` give the same continuation
payoffs from such histories. -/
theorem osValue_congr {u : I → OSHist A → ((i : I) → A i) → ℝ} {δ : ℝ} {σ σ' : OSProfile A}
    {L : ℕ} (hag : ∀ h : OSHist A, L ≤ h.length → osPlay σ' h = osPlay σ h) {h : OSHist A}
    (hh : L ≤ h.length) (i : I) : osValue u δ σ' h i = osValue u δ σ h i := by
  have hpath : ∀ n (h : OSHist A), L ≤ h.length → osPath σ' h n = osPath σ h n := by
    intro n
    induction n with
    | zero => intro h _; rfl
    | succ n ih =>
      intro h hh
      simp only [osPath, hag h hh]
      exact ih _ (by simp only [List.length_cons]; omega)
  unfold osValue
  refine tsum_congr fun n => ?_
  rw [hpath n h hh, hag _ (by rw [osPath_length]; omega)]

/-- **The one-shot deviation principle** (MWG, Appendix A, pp. 296-299). In a multi-stage game
with observed actions, bounded per-period payoffs and discount factor `δ ∈ [0, 1)`: if player
`i` cannot gain at any history `h` by deviating to any action `a` for one period and then
following `σ_i`, then no strategy `τ` of player `i` gains at any history. -/
theorem oneShot_deviation_principle_discounted {u : I → OSHist A → ((i : I) → A i) → ℝ} {δ M : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hu : ∀ i h x, |u i h x| ≤ M) (σ : OSProfile A) (i : I)
    (hos : ∀ (h : OSHist A) (a : A i),
      u i h (Function.update (osPlay σ h) i a) +
        δ * osValue u δ σ (Function.update (osPlay σ h) i a :: h) i ≤ osValue u δ σ h i)
    (τ : OSHist A → A i) (h : OSHist A) :
    osValue u δ (Function.update σ i τ) h i ≤ osValue u δ σ h i := by
  set σ' := Function.update σ i τ with hσ'
  set C := 2 * (M / (1 - δ)) with hC
  have key : ∀ T : ℕ, ∀ h, osValue u δ σ' h i ≤ osValue u δ σ h i + δ ^ T * C := by
    intro T
    induction T with
    | zero =>
      intro h
      have h1 := osValue_abs_le hδ0 hδ1 hu σ' h i
      have h2 := osValue_abs_le hδ0 hδ1 hu σ h i
      rw [abs_le] at h1 h2
      rw [pow_zero, one_mul, hC]
      linarith
    | succ T ih =>
      intro h
      rw [osValue_succ hδ0 hδ1 hu σ' h i, hσ', osPlay_update σ i τ h, ← hσ']
      have h1 := ih (Function.update (osPlay σ h) i (τ h) :: h)
      have h2 := hos h (τ h)
      have h3 := mul_le_mul_of_nonneg_left h1 hδ0
      rw [pow_succ]
      nlinarith
  have hlim : Filter.Tendsto (fun T : ℕ => osValue u δ σ h i + δ ^ T * C) Filter.atTop
      (nhds (osValue u δ σ h i + 0 * C)) :=
    tendsto_const_nhds.add ((tendsto_pow_atTop_nhds_zero_of_lt_one hδ0 hδ1).mul_const C)
  rw [zero_mul, add_zero] at hlim
  exact ge_of_tendsto' hlim fun T => key T h

/-- **The one-shot deviation principle, characterisation** (MWG, Appendix A, pp. 296-299). With
bounded per-period payoffs and `δ ∈ [0, 1)`, a pure profile `σ` is subgame perfect (at every
history no player gains by any change of her strategy) iff no player has a profitable one-shot
deviation at any history. -/
theorem oneShot_deviation_principle_discounted_iff
    {u : I → OSHist A → ((i : I) → A i) → ℝ} {δ M : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hu : ∀ i h x, |u i h x| ≤ M) (σ : OSProfile A) :
    (∀ i (τ : OSHist A → A i) h, osValue u δ (Function.update σ i τ) h i ≤ osValue u δ σ h i) ↔
      ∀ i (h : OSHist A) (a : A i),
        u i h (Function.update (osPlay σ h) i a) +
          δ * osValue u δ σ (Function.update (osPlay σ h) i a :: h) i ≤ osValue u δ σ h i := by
  constructor
  · intro hspe i h a
    -- the strategy that plays `a` at histories of the length of `h` and follows `σ_i` otherwise
    set τ : OSHist A → A i := fun h' => if h'.length = h.length then a else σ i h' with hτ
    have hspe' := hspe i τ h
    rw [osValue_succ hδ0 hδ1 hu _ h i, osPlay_update σ i τ h] at hspe'
    have hτh : τ h = a := by simp [hτ]
    rw [hτh] at hspe'
    have hcong : osValue u δ (Function.update σ i τ) (Function.update (osPlay σ h) i a :: h) i =
        osValue u δ σ (Function.update (osPlay σ h) i a :: h) i := by
      refine osValue_congr (L := h.length + 1) (fun h' hh' => ?_) (by simp) i
      rw [osPlay_update]
      have : τ h' = σ i h' := by
        simp only [hτ]
        split_ifs with hl
        · omega
        · rfl
      rw [this]
      funext j
      by_cases hj : j = i
      · subst hj; simp [osPlay]
      · simp [Function.update_of_ne hj]
    rw [hcong] at hspe'
    exact hspe'
  · intro hos i τ h
    exact oneShot_deviation_principle_discounted hδ0 hδ1 hu σ i (hos i) τ h

/-! ### Instance: grim trigger in the infinitely repeated prisoners' dilemma -/

/-- The prisoners' dilemma stage payoffs (`true` = cooperate): `(C, C) ↦ 2`, `(D, C) ↦ 3` for
the defector, `(C, D) ↦ 0`, `(D, D) ↦ 1`. -/
def pdStage (i : Fin 2) (x : Fin 2 → Bool) : ℝ :=
  if x i then (if x (1 - i) then 2 else 0) else (if x (1 - i) then 3 else 1)

/-- A history in which both players always cooperated. -/
def pdClean (h : OSHist fun _ : Fin 2 => Bool) : Bool := h.all fun x => x 0 && x 1

/-- Grim trigger: cooperate iff both have always cooperated. -/
def grimTrigger : OSProfile fun _ : Fin 2 => Bool := fun _ h => pdClean h

/-- The repeated prisoners' dilemma payoff (history independent). -/
def pdU (i : Fin 2) (_ : OSHist fun _ : Fin 2 => Bool) (x : Fin 2 → Bool) : ℝ := pdStage i x

theorem pdU_bound (i : Fin 2) (h : OSHist fun _ : Fin 2 => Bool) (x : Fin 2 → Bool) :
    |pdU i h x| ≤ 3 := by
  unfold pdU pdStage
  split_ifs <;> norm_num

theorem grim_value_clean {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) {h : OSHist fun _ : Fin 2 => Bool}
    (hc : pdClean h = true) (i : Fin 2) : osValue pdU δ grimTrigger h i = 2 / (1 - δ) := by
  have hpath : ∀ n (h : OSHist fun _ : Fin 2 => Bool), pdClean h = true →
      pdClean (osPath grimTrigger h n) = true := by
    intro n
    induction n with
    | zero => intro h hc; exact hc
    | succ n ih =>
      intro h hc
      refine ih _ ?_
      simp only [pdClean, List.all_cons] at hc ⊢
      simp [osPlay, grimTrigger, pdClean, hc]
  have hterm : ∀ n, δ ^ n * pdU i (osPath grimTrigger h n)
      (osPlay grimTrigger (osPath grimTrigger h n)) = 2 * δ ^ n := by
    intro n
    have := hpath n h hc
    have hp : osPlay grimTrigger (osPath grimTrigger h n) = fun _ => true := by
      funext j
      simp [osPlay, grimTrigger, this]
    rw [hp]
    simp [pdU, pdStage]
    ring
  unfold osValue
  simp only [hterm]
  rw [tsum_mul_left, tsum_geometric_of_lt_one hδ0 hδ1, div_eq_mul_inv]

theorem grim_value_dirty {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) {h : OSHist fun _ : Fin 2 => Bool}
    (hc : pdClean h = false) (i : Fin 2) : osValue pdU δ grimTrigger h i = 1 / (1 - δ) := by
  have hpath : ∀ n (h : OSHist fun _ : Fin 2 => Bool), pdClean h = false →
      pdClean (osPath grimTrigger h n) = false := by
    intro n
    induction n with
    | zero => intro h hc; exact hc
    | succ n ih =>
      intro h hc
      refine ih _ ?_
      simp only [pdClean, List.all_cons] at hc ⊢
      simp [hc]
  have hterm : ∀ n, δ ^ n * pdU i (osPath grimTrigger h n)
      (osPlay grimTrigger (osPath grimTrigger h n)) = 1 * δ ^ n := by
    intro n
    have := hpath n h hc
    have hp : osPlay grimTrigger (osPath grimTrigger h n) = fun _ => false := by
      funext j
      simp [osPlay, grimTrigger, this]
    rw [hp]
    simp [pdU, pdStage]
  unfold osValue
  simp only [hterm]
  rw [tsum_mul_left, tsum_geometric_of_lt_one hδ0 hδ1, div_eq_mul_inv]

/-- **The one-shot deviation principle, an instance** (MWG, Appendix A). In the infinitely
repeated prisoners' dilemma with discount factor `δ ∈ [0, 1)`, grim trigger is subgame perfect
iff `δ ≥ 1/2`: by `oneShot_deviation_principle_discounted_iff` it suffices to check one-period
deviations, and the only one that can gain is defecting after a clean history, which gives
`3 + δ/(1 − δ)` against `2/(1 − δ)`. -/
theorem grim_trigger_spe_iff {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    (∀ i (τ : OSHist (fun _ : Fin 2 => Bool) → Bool) h,
      osValue pdU δ (Function.update grimTrigger i τ) h i ≤ osValue pdU δ grimTrigger h i) ↔
      1 / 2 ≤ δ := by
  have h1 : 0 < 1 - δ := by linarith
  rw [oneShot_deviation_principle_discounted_iff hδ0 hδ1 pdU_bound]
  constructor
  · intro hos
    have := hos 0 [] false
    have hc : pdClean ([] : OSHist fun _ : Fin 2 => Bool) = true := rfl
    rw [grim_value_clean hδ0 hδ1 hc] at this
    have hd : pdClean (Function.update (osPlay grimTrigger []) 0 false :: []) = false := by
      simp [pdClean]
    rw [grim_value_dirty hδ0 hδ1 hd] at this
    have hs : pdU 0 [] (Function.update (osPlay grimTrigger []) 0 false) = 3 := by
      simp [pdU, pdStage, osPlay, grimTrigger, pdClean]
    rw [hs] at this
    rw [div_eq_mul_inv, div_eq_mul_inv] at this
    have hinv : (1 - δ)⁻¹ * (1 - δ) = 1 := inv_mul_cancel₀ h1.ne'
    nlinarith [inv_pos.2 h1]
  · intro hδ i h a
    cases hc : pdClean h with
    | false =>
      have hd : pdClean (Function.update (osPlay grimTrigger h) i a :: h) = false := by
        simp only [pdClean, List.all_cons] at hc ⊢
        simp [hc]
      rw [grim_value_dirty hδ0 hδ1 hc, grim_value_dirty hδ0 hδ1 hd]
      have hs : pdU i h (Function.update (osPlay grimTrigger h) i a) ≤ 1 := by
        have hp : osPlay grimTrigger h = fun _ => false := by
          funext j; simp [osPlay, grimTrigger, hc]
        rw [hp]
        fin_cases i <;> cases a <;> simp [pdU, pdStage]
      have e1 : 1 / (1 - δ) * (1 - δ) = 1 := div_mul_cancel₀ 1 h1.ne'
      linarith
    | true =>
      have hp : osPlay grimTrigger h = fun _ => true := by
        funext j; simp [osPlay, grimTrigger, hc]
      cases a with
      | true =>
        have hu : Function.update (osPlay grimTrigger h) i true = fun _ => true := by
          rw [hp]; funext j; by_cases hj : j = i
          · subst hj; simp
          · simp [Function.update_of_ne hj]
        have hd : pdClean ((fun _ => true) :: h) = true := by
          simp only [pdClean, List.all_cons] at hc ⊢
          simp [hc]
        rw [hu, grim_value_clean hδ0 hδ1 hc, grim_value_clean hδ0 hδ1 hd]
        have hs : pdU i h (fun _ => true) = 2 := by simp [pdU, pdStage]
        rw [hs]
        have e2 : 2 / (1 - δ) * (1 - δ) = 2 := div_mul_cancel₀ 2 h1.ne'
        linarith
      | false =>
        have hd : pdClean (Function.update (osPlay grimTrigger h) i false :: h) = false := by
          rw [hp]
          fin_cases i <;> simp [pdClean]
        rw [grim_value_clean hδ0 hδ1 hc, grim_value_dirty hδ0 hδ1 hd]
        have hs : pdU i h (Function.update (osPlay grimTrigger h) i false) = 3 := by
          rw [hp]
          fin_cases i <;> simp [pdU, pdStage]
        rw [hs, div_eq_mul_inv, div_eq_mul_inv]
        have hinv : (1 - δ)⁻¹ * (1 - δ) = 1 := inv_mul_cancel₀ h1.ne'
        nlinarith [inv_pos.2 h1]

end MWG.DynamicGames
