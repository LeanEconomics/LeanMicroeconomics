/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPrincipalAgent.Basic

/-!
# Exercise 14.C.8 (Air Shangri-la)

MWG, Exercise 14.C.8, pp. 509-510.

A traveller of type `θ` (`θ_B` business, `θ_T` tourist, `0 < θ_B < θ_T`) buying a ticket at price
`P ≥ 0` a time `W ≥ 0` before the flight gets `v - θP - W` (`0` if he does not fly); a fraction
`λ` are tourists; each passenger costs `c`. The airline offers `(P_B, W_B)`, `(P_T, W_T)` to carry
both types (part (a), the formulation, is `C8Feas`; the indifference curves are graphical).

* `exercise_14_C_8_IRB`: the business traveller's participation constraint is implied.
* `exercise_14_C_8b`: at an optimum tourists are indifferent between flying and not.
* `exercise_14_C_8c`: business travellers buy at the last moment (`W_B = 0`) and are indifferent
  between this and the tourists' ticket.
* `exercise_14_C_8d`: the optimal scheme. With `κ = (1 - λ)/θ_B - 1/θ_T`, the profit of every
  feasible scheme is at most `(v - W)/θ_T + (1 - λ) W/θ_B - c` for some `W ∈ [0, v]`; if `κ < 0`
  the optimum is a single price `v/θ_T` with no advance purchase; if `κ > 0` it is `P_T = 0`,
  `W_T = v`, `P_B = v/θ_B`.
* `exercise_14_C_8e`: serving only business travellers is better when `κ ≥ 0`.
-/

namespace MWG.PrincipalAgent

/-- The feasible schemes carrying both types (MWG, Exercise 14.C.8(a)). -/
def C8Feas (v θB θT PB WB PT WT : ℝ) : Prop :=
  0 ≤ PB ∧ 0 ≤ WB ∧ 0 ≤ PT ∧ 0 ≤ WT ∧ 0 ≤ v - θB * PB - WB ∧ 0 ≤ v - θT * PT - WT ∧
    v - θB * PT - WT ≤ v - θB * PB - WB ∧ v - θT * PB - WB ≤ v - θT * PT - WT

/-- The airline's profit. -/
def C8Profit (lam c PB PT : ℝ) : ℝ := lam * (PT - c) + (1 - lam) * (PB - c)

/-- An optimal scheme carrying both types. -/
def C8Opt (v θB θT lam c PB WB PT WT : ℝ) : Prop :=
  C8Feas v θB θT PB WB PT WT ∧ ∀ PB' WB' PT' WT', C8Feas v θB θT PB' WB' PT' WT' →
    C8Profit lam c PB' PT' ≤ C8Profit lam c PB PT

/-- The business traveller's participation follows from the tourists' participation and the
business traveller's self-selection constraint. -/
theorem exercise_14_C_8_IRB {v θB θT PB WB PT WT : ℝ} (hθ : θB < θT) (hPT : 0 ≤ PT)
    (hT : 0 ≤ v - θT * PT - WT) (hB : v - θB * PT - WT ≤ v - θB * PB - WB) :
    0 ≤ v - θB * PB - WB := by nlinarith

/-- **Exercise 14.C.8(b)** (MWG, p. 510). At an optimal scheme tourists are indifferent between
buying a ticket and not going (raising both prices by the slack keeps all constraints). -/
theorem exercise_14_C_8b {v θB θT lam c PB WB PT WT : ℝ} (hθB : 0 < θB) (hθ : θB < θT)
    (h : C8Opt v θB θT lam c PB WB PT WT) :
    v - θT * PT - WT = 0 := by
  obtain ⟨⟨h1, h2, h3, h4, -, h6, h7, h8⟩, hopt⟩ := h
  by_contra hne
  have hs : 0 < v - θT * PT - WT := lt_of_le_of_ne h6 (Ne.symm hne)
  set δ := (v - θT * PT - WT) / θT
  have hθT : 0 < θT := hθB.trans hθ
  have hδ : 0 < δ := div_pos hs hθT
  have hδT : θT * δ = v - θT * PT - WT := by simp only [δ]; field_simp
  clear_value δ
  have hfeas : C8Feas v θB θT (PB + δ) WB (PT + δ) WT := by
    refine ⟨by linarith, h2, by linarith, h4, ?_, by nlinarith, by nlinarith, by nlinarith⟩
    exact exercise_14_C_8_IRB (PT := PT + δ) (WT := WT) hθ (by linarith) (by nlinarith)
      (by nlinarith)
  have := hopt _ _ _ _ hfeas
  unfold C8Profit at this
  nlinarith

/-- **Exercise 14.C.8(c)** (MWG, p. 510). At an optimal scheme business travellers never buy in
advance (`W_B = 0`) and are indifferent between their ticket and the tourists'. -/
theorem exercise_14_C_8c {v θB θT lam c PB WB PT WT : ℝ} (hθB : 0 < θB) (hθ : θB < θT)
    (hl1 : lam < 1) (h : C8Opt v θB θT lam c PB WB PT WT) :
    WB = 0 ∧ v - θB * PB - WB = v - θB * PT - WT := by
  obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8⟩, hopt⟩ := h
  constructor
  · by_contra hne
    have hW : 0 < WB := lt_of_le_of_ne h2 (Ne.symm hne)
    -- move the business ticket along the business indifference curve: `W_B ↦ 0`,
    -- `P_B ↦ P_B + W_B/θ_B`
    have hfeas : C8Feas v θB θT (PB + WB / θB) 0 PT WT := by
      have e1 : θB * (PB + WB / θB) = θB * PB + WB := by field_simp
      have hT : θT * (WB / θB) ≥ WB := by
        rw [ge_iff_le, ← mul_div_assoc, le_div_iff₀ hθB]; nlinarith
      refine ⟨by positivity, le_rfl, h3, h4, by rw [e1]; linarith, h6, by rw [e1]; linarith, ?_⟩
      nlinarith
    have := hopt _ _ _ _ hfeas
    unfold C8Profit at this
    have : 0 < (1 - lam) * (WB / θB) := mul_pos (by linarith) (div_pos hW hθB)
    linarith
  · by_contra hne
    have hs : 0 < (v - θB * PB - WB) - (v - θB * PT - WT) := by
      rcases lt_or_eq_of_le h7 with h | h
      · linarith
      · exact absurd h.symm hne
    set δ := ((v - θB * PB - WB) - (v - θB * PT - WT)) / θB
    have hδ : 0 < δ := div_pos hs hθB
    have hδB : θB * δ = (v - θB * PB - WB) - (v - θB * PT - WT) := by simp only [δ]; field_simp
    clear_value δ
    have hfeas : C8Feas v θB θT (PB + δ) WB PT WT := by
      refine ⟨by linarith, h2, h3, h4, ?_, h6, by nlinarith, by nlinarith⟩
      exact exercise_14_C_8_IRB (PT := PT) (WT := WT) hθ h3 h6 (by nlinarith)
    have := hopt _ _ _ _ hfeas
    unfold C8Profit at this
    nlinarith

/-- The tourists' and business tickets determined by `W_T = W`: `P_T = (v - W)/θ_T`, `W_B = 0`,
`P_B = P_T + W/θ_B`. -/
theorem exercise_14_C_8d_feas {v θB θT W : ℝ} (hθB : 0 < θB) (hθ : θB < θT) (hW : 0 ≤ W)
    (hWv : W ≤ v) :
    C8Feas v θB θT ((v - W) / θT + W / θB) 0 ((v - W) / θT) W := by
  have hθT : 0 < θT := hθB.trans hθ
  have eT : θT * ((v - W) / θT) = v - W := by field_simp
  have eB : θB * ((v - W) / θT + W / θB) = θB * ((v - W) / θT) + W := by field_simp
  have eTB : θT * ((v - W) / θT + W / θB) = v - W + θT * (W / θB) := by
    rw [mul_add, eT]
  have hTB : W ≤ θT * (W / θB) := by
    rw [← mul_div_assoc, le_div_iff₀ hθB]; nlinarith
  have hPT : 0 ≤ (v - W) / θT := div_nonneg (by linarith) hθT.le
  refine ⟨by positivity, le_rfl, hPT, hW, ?_, by rw [eT]; linarith, by rw [eB]; linarith,
    by rw [eTB, eT]; linarith⟩
  rw [eB]
  have : θB * ((v - W) / θT) ≤ v - W := by
    have := mul_le_mul_of_nonneg_right hθ.le hPT
    rwa [eT] at this
  linarith

/-- **Exercise 14.C.8(d)** (MWG, p. 510), the bound. Every feasible scheme earns at most
`(v - W_T)/θ_T + (1 - λ) W_T/θ_B - c`, attained by `exercise_14_C_8d_feas` with `W = W_T`. -/
theorem exercise_14_C_8d_bound {v θB θT lam c PB WB PT WT : ℝ} (hθB : 0 < θB) (hθ : θB < θT)
    (hl1 : lam ≤ 1) (h : C8Feas v θB θT PB WB PT WT) :
    C8Profit lam c PB PT ≤ (v - WT) / θT + (1 - lam) * (WT / θB) - c ∧ WT ≤ v ∧
      C8Profit lam c ((v - WT) / θT + WT / θB) ((v - WT) / θT) =
        (v - WT) / θT + (1 - lam) * (WT / θB) - c := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  have hθT : 0 < θT := hθB.trans hθ
  have hPT : PT ≤ (v - WT) / θT := by rw [le_div_iff₀ hθT]; linarith
  have hPB : PB ≤ PT + WT / θB := by
    rw [← sub_le_iff_le_add', le_div_iff₀ hθB]; nlinarith
  refine ⟨?_, by nlinarith, by unfold C8Profit; ring⟩
  unfold C8Profit
  nlinarith [mul_le_mul_of_nonneg_left hPB (by linarith : (0:ℝ) ≤ 1 - lam)]

/-- **Exercise 14.C.8(d)** (MWG, p. 510), the optimal scheme. With `κ = (1 - λ)/θ_B - 1/θ_T`:
if `κ < 0` the single price `v/θ_T` (`W = 0`) for both types is optimal; if `κ > 0` the scheme
`P_T = 0`, `W_T = v`, `P_B = v/θ_B`, `W_B = 0` is optimal. The cost `c` does not matter. -/
theorem exercise_14_C_8d {v θB θT lam c : ℝ} (hθB : 0 < θB) (hθ : θB < θT)
    (hl1 : lam ≤ 1) (hv : 0 ≤ v) :
    ((1 - lam) / θB - 1 / θT < 0 → C8Opt v θB θT lam c (v / θT) 0 (v / θT) 0) ∧
      (0 < (1 - lam) / θB - 1 / θT → C8Opt v θB θT lam c (v / θB) 0 0 v) := by
  have hθT : 0 < θT := hθB.trans hθ
  have key : ∀ W, (v - W) / θT + (1 - lam) * (W / θB) - c =
      v / θT - c + W * ((1 - lam) / θB - 1 / θT) := fun W => by ring
  constructor
  · intro hκ
    have hf := exercise_14_C_8d_feas hθB hθ le_rfl hv
    simp only [sub_zero, zero_div, add_zero] at hf
    refine ⟨hf, fun PB' WB' PT' WT' h' => ?_⟩
    obtain ⟨hb, hWv, -⟩ := exercise_14_C_8d_bound (c := c) hθB hθ hl1 h'
    rw [key] at hb
    have : C8Profit lam c (v / θT) (v / θT) = v / θT - c := by unfold C8Profit; ring
    rw [this]; nlinarith [h'.2.2.2.1]
  · intro hκ
    have hf := exercise_14_C_8d_feas hθB hθ hv le_rfl
    simp only [sub_self, zero_div, zero_add] at hf
    refine ⟨hf, fun PB' WB' PT' WT' h' => ?_⟩
    obtain ⟨hb, hWv, -⟩ := exercise_14_C_8d_bound (c := c) hθB hθ hl1 h'
    rw [key] at hb
    have : C8Profit lam c (v / θB) 0 = v / θT - c + v * ((1 - lam) / θB - 1 / θT) := by
      unfold C8Profit; ring
    rw [this]; nlinarith

/-- **Exercise 14.C.8(e)** (MWG, p. 510). Serving only business travellers (at `P = v/θ_B`,
`W = 0`) earns `(1 - λ)(v/θ_B - c)`. When `κ = (1 - λ)/θ_B - 1/θ_T ≥ 0` and `c > 0` this beats
every scheme carrying both types. (When `κ < 0` the best scheme carrying both types earns
`v/θ_T - c` by `exercise_14_C_8d`, so serving only business travellers is better iff
`(1 - λ)(v/θ_B - c) > v/θ_T - c`.) -/
theorem exercise_14_C_8e {v θB θT lam c : ℝ} (hθB : 0 < θB) (hθ : θB < θT) (hl0 : 0 < lam)
    (hl1 : lam ≤ 1) (hc : 0 < c) (hκ : 0 ≤ (1 - lam) / θB - 1 / θT) :
    ∀ PB WB PT WT, C8Feas v θB θT PB WB PT WT →
      C8Profit lam c PB PT < (1 - lam) * (v / θB - c) := by
  intro PB WB PT WT h
  obtain ⟨hb, hWv, -⟩ := exercise_14_C_8d_bound (c := c) hθB hθ hl1 h
  have key : (v - WT) / θT + (1 - lam) * (WT / θB) - c =
      v / θT - c + WT * ((1 - lam) / θB - 1 / θT) := by ring
  rw [key] at hb
  have h2 : WT * ((1 - lam) / θB - 1 / θT) ≤ v * ((1 - lam) / θB - 1 / θT) :=
    mul_le_mul_of_nonneg_right hWv hκ
  have : v / θT + v * ((1 - lam) / θB - 1 / θT) = (1 - lam) * (v / θB) := by ring
  nlinarith

end MWG.PrincipalAgent
