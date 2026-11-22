/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGEquilibriumUncertainty.ExercisesFH

/-!
# Exercise 19.H.6(b)-(e): non-contingent markets and the value of information (MWG p. 730)

Consumer 1 has `u₁ = x₁₁ + x₂₁` and `ω₂₁` units of good 2; consumer 2 has `u₂ = √x₁₂ + x₂₂` and
`w_s` units of good 1 in state `s` (three equally likely states).

* **(b), (c)**: trade in non-contingent deliveries within an event `E` of states that the
  consumers know (`E` = all states in (b); `{1}` and `{2, 3}` in (c)) is `IsNCEqm19H6`. If `t ≤ 0`
  solves `∑_{s ∈ E} 1/√(w_s + t) = 2|E|`, the prices `(1, 1)` and the trades `(-t, t)` for
  consumer 1 and `(t, -t)` for consumer 2 form an equilibrium (`ncEqm19H6`): consumer 2's
  good-1 consumption is `w_s + t`, which varies with `s` when `w_s` does, so the allocation of (b)
  is not Pareto optimal (`exercise_19_H_6b_not_po` in the instance). In (c), after state 1,
  `t = 1/4 - w₁`.
* **(d)**: contingent trade within an event: prices `1` and the allocation of (a) form an
  equilibrium in every event (`cEqm19H6`).
* **(e)**: consumer 1's ex ante utility is `ω₂₁` in all four equilibria; consumer 2's satisfies
  `(b) ≤ (c) ≤ (a) = (d) = ∑_s w_s/3 + 1/4` (`exercise_19_H_6e`). So the information of (c) is
  (weakly) socially valuable with non-contingent markets, and the information of (d) has no value
  with contingent markets (the allocation is that of (a)).
* An instance with every equilibrium in closed form (`w = (1205/1156, 13/4, 541/100)`,
  `ω₂₁ = 6`): `t = -1` in (b), `t = -229/289` and `t = -79/25` in (c); consumer 2's ex ante
  utilities are strictly increasing from (b) to (c) to (a) (`exercise_19_H_6_instance`).

The equilibria are constructed (sufficiency); uniqueness is not claimed.
-/

namespace MWG.EquilibriumUncertainty

open Matrix

/-- The Bernoulli utilities of Exercise 19.H.6: `u₁(y) = y₁ + y₂`, `u₂(y) = √y₁ + y₂`. -/
noncomputable def bern19H6 : Fin 2 → (Fin 2 → ℝ) → ℝ :=
  ![fun y => y 0 + y 1, fun y => √(y 0) + y 1]

/-- **Exercise 19.H.6(b), (c)** (MWG, p. 730): the budget for non-contingent trade `τ` (a net
trade of the two goods, delivered whatever the state) at prices `P`, when the consumers know that
the state is in `E`: `P·τ ≤ 0` and `ωᵢₛ + τ ≥ 0` for every `s ∈ E`. -/
def ncFeasible19H6 (E : Finset (Fin 3)) (P : Fin 2 → ℝ) (ωi : CVec 3 2) (τ : Fin 2 → ℝ) :
    Prop :=
  P ⬝ᵥ τ ≤ 0 ∧ ∀ s ∈ E, ∀ l, 0 ≤ ωi s l + τ l

/-- **Exercise 19.H.6(b), (c)** (MWG, p. 730): equilibrium with non-contingent markets within the
event `E` (the conditional expected utility is proportional to the sum over `E`). -/
def IsNCEqm19H6 (w21 : ℝ) (w : Fin 3 → ℝ) (E : Finset (Fin 3)) (P : Fin 2 → ℝ)
    (τ : Fin 2 → Fin 2 → ℝ) : Prop :=
  (∀ i, ncFeasible19H6 E P (omega19H6 w21 w i) (τ i) ∧
    ∀ τ', ncFeasible19H6 E P (omega19H6 w21 w i) τ' →
      ∑ s ∈ E, bern19H6 i (omega19H6 w21 w i s + τ') ≤
        ∑ s ∈ E, bern19H6 i (omega19H6 w21 w i s + τ i)) ∧
    ∑ i, τ i = 0

/-- The trades `(-t, t)` (consumer 1) and `(t, -t)` (consumer 2). -/
def ncTrade19H6 (t : ℝ) : Fin 2 → Fin 2 → ℝ := ![![-t, t], ![t, -t]]

/-- The tangent-line bound for `√`: `√a ≤ √b + (a - b)/2 · (1/√b)` for `a ≥ 0`, `b > 0`. -/
theorem sqrt_le_tangent {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    √a ≤ √b + (a - b) / 2 * (1 / √b) := by
  have hs : 0 < √b := Real.sqrt_pos.mpr hb
  have h1 := Real.sq_sqrt ha
  have h2 := Real.sq_sqrt hb.le
  have : √a - √b ≤ (a - b) / 2 * (1 / √b) := by
    rw [div_mul_div_comm, mul_one, le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (√a - √b)]
  linarith

/-- **Exercise 19.H.6(b), (c)** (MWG, p. 730), the equilibrium problem solved. If `t ≤ 0` solves
consumer 2's first-order condition `∑_{s ∈ E} 1/√(w_s + t) = 2|E|` (with `w_s + t > 0` on `E`)
and consumer 1 can deliver `-t` of good 2, then prices `(1, 1)` and the trades
`ncTrade19H6 t` form an equilibrium with non-contingent markets within `E`. -/
theorem ncEqm19H6 {w21 t : ℝ} {w : Fin 3 → ℝ} {E : Finset (Fin 3)} (ht : t ≤ 0)
    (hw21 : 0 ≤ w21 + t) (hy : ∀ s ∈ E, 0 < w s + t)
    (hfoc : ∑ s ∈ E, 1 / √(w s + t) = 2 * E.card) :
    IsNCEqm19H6 w21 w E ![1, 1] (ncTrade19H6 t) := by
  refine ⟨Fin.forall_fin_two.mpr ⟨?_, ?_⟩, ?_⟩
  · · refine ⟨⟨by simp [ncTrade19H6, dotProduct], fun s _ l => ?_⟩, fun τ' hf => ?_⟩
      · fin_cases l <;> simp [omega19H6, ncTrade19H6] <;> linarith
      · have hb := hf.1
        simp [dotProduct] at hb
        refine Finset.sum_le_sum fun s _ => ?_
        simp [bern19H6, omega19H6, ncTrade19H6, Matrix.vecHead, Matrix.vecTail]
        linarith
  · · refine ⟨⟨by simp [ncTrade19H6, dotProduct], fun s hs l => ?_⟩, fun τ' hf => ?_⟩
      · fin_cases l <;> simp [omega19H6, ncTrade19H6] <;> linarith [hy s hs]
      · obtain ⟨hb, hnn⟩ := hf
        simp only [dotProduct, Fin.sum_univ_two, Fin.isValue, cons_val_zero, one_mul, cons_val_one,
            cons_val_fin_one] at hb
        have key : ∀ s ∈ E, bern19H6 1 (omega19H6 w21 w 1 s + τ') ≤
            (√(w s + t) - t) + ((τ' 0 - t) / 2 * (1 / √(w s + t)) + (τ' 1 + t)) := by
          intro s hs
          have h0 := hnn s hs 0
          simp only [omega19H6, Fin.isValue, cons_val', Nat.succ_eq_add_one, Nat.reduceAdd,
              cons_val_fin_one, cons_val_zero, cons_val_one] at h0
          have := sqrt_le_tangent h0 (hy s hs)
          rw [show w s + τ' 0 - (w s + t) = τ' 0 - t by ring, one_div] at this
          simp [bern19H6, omega19H6, Matrix.vecHead, Matrix.vecTail]
          linarith
        have hval : ∀ s ∈ E, bern19H6 1 (omega19H6 w21 w 1 s + ncTrade19H6 t 1) =
            √(w s + t) - t := by
          intro s _
          simp [bern19H6, omega19H6, ncTrade19H6]
          ring
        rw [Finset.sum_congr rfl hval]
        refine (Finset.sum_le_sum key).trans ?_
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hfoc,
          Finset.sum_const, nsmul_eq_mul]
        have hc : (0 : ℝ) ≤ E.card := Nat.cast_nonneg _
        nlinarith
  · funext l
    fin_cases l <;> simp [ncTrade19H6]

/-- **Exercise 19.H.6(d)** (and (a)) (MWG, p. 730): contingent trade within the event `E`, at
contingent prices `p` (only the states of `E` are traded). -/
def IsCEqm19H6 (w21 : ℝ) (w : Fin 3 → ℝ) (E : Finset (Fin 3)) (p : CVec 3 2)
    (x : Fin 2 → CVec 3 2) : Prop :=
  (∀ i, ((∀ s ∈ E, ∀ l, 0 ≤ x i s l) ∧
      ∑ s ∈ E, p s ⬝ᵥ (x i s - omega19H6 w21 w i s) ≤ 0) ∧
    ∀ x' : CVec 3 2, (∀ s ∈ E, ∀ l, 0 ≤ x' s l) →
      ∑ s ∈ E, p s ⬝ᵥ (x' s - omega19H6 w21 w i s) ≤ 0 →
        ∑ s ∈ E, bern19H6 i (x' s) ≤ ∑ s ∈ E, bern19H6 i (x i s)) ∧
    ∀ s ∈ E, ∑ i, x i s = ∑ i, omega19H6 w21 w i s

/-- **Exercise 19.H.6(d)** (MWG, p. 730). After the information is revealed, contingent trade
within either event (`{1}` or `{2, 3}`) at prices `1` gives the allocation of (a), in which
consumer 2 consumes `1/4` of good 1 in every state (interior parameters on `E`). -/
theorem cEqm19H6 {w21 : ℝ} {w : Fin 3 → ℝ} {E : Finset (Fin 3)} (hw : ∀ s ∈ E, 1 / 4 ≤ w s)
    (hw21 : ∀ s ∈ E, w s - 1 / 4 ≤ w21) :
    IsCEqm19H6 w21 w E (fun _ _ => 1) (x19H6 w21 w) := by
  have hq : √(1 / 4 : ℝ) = 1 / 2 := by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  refine ⟨fun i => ?_, fun s _ => ?_⟩
  · fin_cases i
    · refine ⟨⟨fun s hs l => ?_, ?_⟩, fun x' _ hb => ?_⟩
      · fin_cases l <;> simp [x19H6] <;> linarith [hw s hs, hw21 s hs]
      · refine le_of_eq (Finset.sum_eq_zero fun s _ => ?_)
        simp [x19H6, omega19H6, dotProduct]
      · simp only [dotProduct, Fin.sum_univ_two, one_mul] at hb
        refine le_of_sub_nonpos ?_
        rw [← Finset.sum_sub_distrib]
        refine le_trans (le_of_eq (Finset.sum_congr rfl fun s _ => ?_)) hb
        simp [bern19H6, x19H6, omega19H6]
        ring
    · refine ⟨⟨fun s hs l => ?_, ?_⟩, fun x' hx' hb => ?_⟩
      · fin_cases l
        · simp [x19H6]
        · simp [x19H6]; linarith [hw s hs]
      · refine le_of_eq (Finset.sum_eq_zero fun s _ => ?_)
        simp [x19H6, omega19H6, dotProduct]
      · simp only [dotProduct, Fin.sum_univ_two, one_mul] at hb
        refine le_of_sub_nonpos ?_
        rw [← Finset.sum_sub_distrib]
        refine le_trans (Finset.sum_le_sum fun s hs => ?_) hb
        have := sqrt_le_add_quarter (x' s 0) (hx' s hs 0)
        simp [bern19H6, x19H6, omega19H6]
        linarith
  · funext l
    fin_cases l <;> simp [x19H6, omega19H6, Fin.sum_univ_two]

/-- Ex ante expected utility `∑_s ⅓ uᵢ(x_s)` in Exercise 19.H.6. -/
noncomputable def exAnte19H6 (i : Fin 2) (x : CVec 3 2) : ℝ := ∑ s, (1 / 3) * bern19H6 i (x s)

/-- The allocation of (b): `ωᵢₛ + τᵢ` with the trades `ncTrade19H6 t`. -/
def xB19H6 (w21 : ℝ) (w : Fin 3 → ℝ) (t : ℝ) : Fin 2 → CVec 3 2 :=
  fun i s => omega19H6 w21 w i s + ncTrade19H6 t i

/-- The allocation of (c): after state 1 the trade `ncTrade19H6 (1/4 - w₁)`, after `{2, 3}` the
trade `ncTrade19H6 t'`. -/
noncomputable def xC19H6 (w21 : ℝ) (w : Fin 3 → ℝ) (t' : ℝ) : Fin 2 → CVec 3 2 :=
  fun i s => omega19H6 w21 w i s + ncTrade19H6 (if s = 0 then 1 / 4 - w 0 else t') i

/-- **Exercise 19.H.6(e)** (MWG, p. 730). Ex ante utilities in the equilibria of (a)-(d):
consumer 1 obtains `ω₂₁` in all of them (the allocation of (a) is also that of (d)); consumer 2
obtains `∑_s w_s/3 + 1/4` in (a) and (d), and less in (c), and less again in (b). Hence
information in (c) is socially valuable (weakly Pareto improving) relative to (b), while with
contingent markets (d) it has no value relative to (a). Only consumer 2's first-order condition
in the event `{2, 3}` of (c) is used. -/
theorem exercise_19_H_6e {w21 t t' : ℝ} {w : Fin 3 → ℝ} (hy : ∀ s, 0 ≤ w s + t)
    (hy1 : 0 < w 1 + t') (hy2 : 0 < w 2 + t')
    (hfoc : 1 / √(w 1 + t') + 1 / √(w 2 + t') = 4) :
    exAnte19H6 0 (xB19H6 w21 w t 0) = w21 ∧ exAnte19H6 0 (xC19H6 w21 w t' 0) = w21 ∧
      exAnte19H6 0 (x19H6 w21 w 0) = w21 ∧
      exAnte19H6 1 (x19H6 w21 w 1) = ∑ s, (1 / 3) * w s + 1 / 4 ∧
      exAnte19H6 1 (xB19H6 w21 w t 1) ≤ exAnte19H6 1 (xC19H6 w21 w t' 1) ∧
      exAnte19H6 1 (xC19H6 w21 w t' 1) ≤ exAnte19H6 1 (x19H6 w21 w 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [exAnte19H6, bern19H6, xB19H6, omega19H6, ncTrade19H6]
  · simp [exAnte19H6, bern19H6, xC19H6, omega19H6, ncTrade19H6]
  · simp [exAnte19H6, bern19H6, x19H6]
  · simp [exAnte19H6, bern19H6, x19H6, Fin.sum_univ_three]; ring
  · have t1 := sqrt_le_tangent (hy 1) hy1
    have t2 := sqrt_le_tangent (hy 2) hy2
    have q0 := sqrt_le_add_quarter (w 0 + t) (hy 0)
    have hsum : (w 1 + t - (w 1 + t')) / 2 * (1 / √(w 1 + t')) +
        (w 2 + t - (w 2 + t')) / 2 * (1 / √(w 2 + t')) = 2 * (t - t') := by
      rw [show w 1 + t - (w 1 + t') = t - t' by ring, show w 2 + t - (w 2 + t') = t - t' by ring,
        ← mul_add, hfoc]
      ring
    simp [exAnte19H6, bern19H6, xB19H6, xC19H6, omega19H6, ncTrade19H6, Fin.sum_univ_three]
    linarith
  · have q1 := sqrt_le_add_quarter (w 1 + t') hy1.le
    have q2 := sqrt_le_add_quarter (w 2 + t') hy2.le
    simp [exAnte19H6, bern19H6, xC19H6, x19H6, omega19H6, ncTrade19H6, Fin.sum_univ_three]
    linarith

/-! ## An instance with every equilibrium in closed form -/

/-- Consumer 2's good-1 endowments of the instance: `(1205/1156, 13/4, 541/100)`. -/
noncomputable def wInst19H6 : Fin 3 → ℝ := ![1205 / 1156, 13 / 4, 541 / 100]

theorem wInst19H6_sqrt :
    √(wInst19H6 0 + -1) = 7 / 34 ∧ √(wInst19H6 1 + -1) = 3 / 2 ∧
      √(wInst19H6 2 + -1) = 21 / 10 ∧ √(wInst19H6 1 + -79 / 25) = 3 / 10 ∧
      √(wInst19H6 2 + -79 / 25) = 3 / 2 ∧ √(wInst19H6 0 + (1 / 4 - wInst19H6 0)) = 1 / 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show wInst19H6 0 + -1 = (7 / 34) ^ 2 by norm_num [wInst19H6]]
    exact Real.sqrt_sq (by norm_num)
  · rw [show wInst19H6 1 + -1 = (3 / 2) ^ 2 by norm_num [wInst19H6]]
    exact Real.sqrt_sq (by norm_num)
  · rw [show wInst19H6 2 + -1 = (21 / 10) ^ 2 by norm_num [wInst19H6]]
    exact Real.sqrt_sq (by norm_num)
  · rw [show wInst19H6 1 + -79 / 25 = (3 / 10) ^ 2 by norm_num [wInst19H6]]
    exact Real.sqrt_sq (by norm_num)
  · rw [show wInst19H6 2 + -79 / 25 = (3 / 2) ^ 2 by norm_num [wInst19H6]]
    exact Real.sqrt_sq (by norm_num)
  · rw [show wInst19H6 0 + (1 / 4 - wInst19H6 0) = (1 / 2) ^ 2 by ring]
    exact Real.sqrt_sq (by norm_num)

/-- **Exercise 19.H.6(b)-(e)** (MWG, p. 730), an instance computed in closed form (`ω₂₁ = 6`,
`w = (1205/1156, 13/4, 541/100)`, interior for (a)). (b): `t = -1`, so consumer 2 consumes
`(49/1156, 9/4, 441/100)` of good 1. (c): after state 1, `t = 1/4 - w₁ = -229/289`; after
`{2, 3}`, `t = -79/25`, so he consumes `(1/4, 9/100, 9/4)`. (d): the allocation of (a) in both
events. Consumer 2's ex ante utility rises strictly from (b) to (c) to (a) = (d). -/
theorem exercise_19_H_6_instance :
    IsNCEqm19H6 6 wInst19H6 Finset.univ ![1, 1] (ncTrade19H6 (-1)) ∧
      IsNCEqm19H6 6 wInst19H6 {0} ![1, 1] (ncTrade19H6 (1 / 4 - wInst19H6 0)) ∧
      IsNCEqm19H6 6 wInst19H6 {1, 2} ![1, 1] (ncTrade19H6 (-79 / 25)) ∧
      IsCEqm19H6 6 wInst19H6 {0} (fun _ _ => 1) (x19H6 6 wInst19H6) ∧
      IsCEqm19H6 6 wInst19H6 {1, 2} (fun _ _ => 1) (x19H6 6 wInst19H6) ∧
      exAnte19H6 1 (xB19H6 6 wInst19H6 (-1) 1) < exAnte19H6 1 (xC19H6 6 wInst19H6 (-79 / 25) 1) ∧
      exAnte19H6 1 (xC19H6 6 wInst19H6 (-79 / 25) 1) < exAnte19H6 1 (x19H6 6 wInst19H6 1) := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := wInst19H6_sqrt
  have h4' : √(4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hw : ∀ s, 1 / 4 ≤ wInst19H6 s := by
    intro s; fin_cases s <;> norm_num [wInst19H6]
  have hw21 : ∀ s, wInst19H6 s - 1 / 4 ≤ 6 := by
    intro s; fin_cases s <;> norm_num [wInst19H6]
  refine ⟨?_, ?_, ?_, cEqm19H6 (fun s _ => hw s) (fun s _ => hw21 s),
    cEqm19H6 (fun s _ => hw s) (fun s _ => hw21 s), ?_, ?_⟩
  · refine ncEqm19H6 (by norm_num) (by norm_num) (fun s _ => ?_) ?_
    · fin_cases s <;> norm_num [wInst19H6]
    · rw [Fin.sum_univ_three, h0, h1, h2]; norm_num
  · refine ncEqm19H6 (by norm_num [wInst19H6]) (by norm_num [wInst19H6]) (fun s hs => ?_) ?_
    · rw [Finset.mem_singleton.mp hs]; norm_num
    · rw [Finset.sum_singleton, h5]; norm_num
  · refine ncEqm19H6 (by norm_num) (by norm_num) (fun s hs => ?_) ?_
    · fin_cases s <;> simp at hs <;> norm_num [wInst19H6]
    · rw [Finset.sum_pair (by decide), h3, h4]; norm_num
  · simp only [exAnte19H6, one_div, bern19H6, Fin.isValue, xB19H6, omega19H6, cons_val',
      Nat.succ_eq_add_one, Nat.reduceAdd, cons_val_fin_one, cons_val_one, ncTrade19H6, neg_neg,
      add_cons, head_cons, tail_cons, zero_add, empty_add_empty, cons_val_zero,
      neg_add_cancel_right, Fin.sum_univ_three, xC19H6, add_neg_cancel_right, ↓reduceIte,
      add_sub_cancel, Real.sqrt_inv, neg_sub, one_ne_zero, Fin.reduceEq]
    rw [h0, h1, h2, h3, h4, h4']
    norm_num [wInst19H6]
  · simp only [exAnte19H6, one_div, bern19H6, Fin.isValue, xC19H6, omega19H6, cons_val',
      Nat.succ_eq_add_one, Nat.reduceAdd, cons_val_fin_one, cons_val_one, ncTrade19H6, add_cons,
      head_cons, tail_cons, zero_add, empty_add_empty, cons_val_zero, add_neg_cancel_right,
      Fin.sum_univ_three, ↓reduceIte, add_sub_cancel, Real.sqrt_inv, neg_sub, one_ne_zero,
      Fin.reduceEq, x19H6]
    rw [h3, h4, h4']
    norm_num [wInst19H6]

/-- **Exercise 19.H.6(b)** (MWG, p. 730), Pareto optimality: in the instance, the equilibrium
allocation with non-contingent markets is not Pareto optimal (consumer 2's good-1 consumption
`49/1156` in state 1 is not `1/4`; `exercise_19_H_6_not_po`). -/
theorem exercise_19_H_6b_not_po :
    ¬ IsParetoOptimalU ![U1_19H6, U2_19H6] (omega19H6 6 wInst19H6) (xB19H6 6 wInst19H6 (-1)) := by
  intro hpo
  obtain ⟨h0, h1, h2, -, -, -⟩ := wInst19H6_sqrt
  refine exercise_19_H_6_not_po hpo (s₀ := 0) ?_ fun s => ?_
  · simp [xB19H6, omega19H6, ncTrade19H6]
    norm_num [wInst19H6]
  · fin_cases s
    · simp only [xB19H6, omega19H6, Fin.isValue, Fin.zero_eta, cons_val', Nat.succ_eq_add_one,
        Nat.reduceAdd, cons_val_fin_one, cons_val_one, ncTrade19H6, neg_neg, Pi.add_apply, zero_add,
        cons_val_zero, one_div, sub_nonneg, add_neg_cancel_comm_assoc]
      rw [h0]
      norm_num [wInst19H6]
    · simp only [xB19H6, omega19H6, Fin.isValue, Fin.mk_one, cons_val', Nat.succ_eq_add_one,
        Nat.reduceAdd, cons_val_fin_one, cons_val_one, ncTrade19H6, neg_neg, Pi.add_apply, zero_add,
        cons_val_zero, one_div, sub_nonneg, add_neg_cancel_comm_assoc]
      rw [h1]
      norm_num [wInst19H6]
    · simp only [xB19H6, omega19H6, Fin.isValue, Fin.reduceFinMk, cons_val', Nat.succ_eq_add_one,
        Nat.reduceAdd, cons_val_fin_one, cons_val_one, ncTrade19H6, neg_neg, Pi.add_apply, zero_add,
        cons_val_zero, one_div, sub_nonneg, add_neg_cancel_comm_assoc]
      rw [h2]
      norm_num [wInst19H6]

/-- **Exercise 19.H.6(e)** (MWG, p. 730) in the instance: the hypotheses of `exercise_19_H_6e`
hold, so its comparisons apply (consumer 1 obtains `6` throughout). -/
theorem exercise_19_H_6e_instance :
    exAnte19H6 0 (xB19H6 6 wInst19H6 (-1) 0) = 6 ∧
      exAnte19H6 0 (xC19H6 6 wInst19H6 (-79 / 25) 0) = 6 ∧
      exAnte19H6 0 (x19H6 6 wInst19H6 0) = 6 ∧
      exAnte19H6 1 (x19H6 6 wInst19H6 1) = ∑ s, (1 / 3) * wInst19H6 s + 1 / 4 ∧
      exAnte19H6 1 (xB19H6 6 wInst19H6 (-1) 1) ≤ exAnte19H6 1 (xC19H6 6 wInst19H6 (-79 / 25) 1) ∧
      exAnte19H6 1 (xC19H6 6 wInst19H6 (-79 / 25) 1) ≤ exAnte19H6 1 (x19H6 6 wInst19H6 1) := by
  obtain ⟨-, -, -, h3, h4, -⟩ := wInst19H6_sqrt
  refine exercise_19_H_6e (fun s => ?_) (by norm_num [wInst19H6]) (by norm_num [wInst19H6]) ?_
  · fin_cases s <;> norm_num [wInst19H6]
  · rw [h3, h4]; norm_num

end MWG.EquilibriumUncertainty
