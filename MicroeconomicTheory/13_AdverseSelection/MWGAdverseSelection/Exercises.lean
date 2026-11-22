/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGAdverseSelection.Constrained
import MWGAdverseSelection.Unraveling
import MWGAdverseSelection.Signaling
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# End-of-chapter exercises

MWG, Chapter 13 exercises, pp. 473-476.

* `exercise_13_B_4`: the no-trade theorem: if trade at price `p` requires both parties to be
  strictly better off given their private signals, trade has probability zero (finite
  probability space).
* `exercise_13_B_5a`-`exercise_13_B_5d`: `r(θ) = r` with the belief `E[θ | Θ = ∅] = θ̲`:
  the equilibrium wages, Pareto ranking, SPNE of the wage game, constrained optimality.
* `exercise_13_C_5a`, `exercise_13_C_5b`: the consumer buys iff `λv_H + (1 - λ)v_L ≥ p`; no
  separating PBE with advertising exists.
* `exercise_13_C_6a`: the pooling loan rate `R = (1 + r)/(λp_G + (1 - λ)p_B)` and its comparative
  statics; good projects may go unfinanced.
-/

namespace MWG.AdverseSelection

open Finset

/-- Fiberwise positivity: if every fiber of `Yf` with positive mass has a positive weighted sum
of `g`, and `A` has positive mass, the weighted sum of `g` over `A` is positive. -/
theorem sum_pos_of_fibers {Ω Y : Type*} [DecidableEq Y] (P g : Ω → ℝ) (hP : ∀ ω, 0 ≤ P ω)
    (A : Finset Ω) (Yf : Ω → Y)
    (hg : ∀ y, 0 < ∑ ω ∈ A.filter (fun ω => Yf ω = y), P ω →
      0 < ∑ ω ∈ A.filter (fun ω => Yf ω = y), P ω * g ω)
    (hA : 0 < ∑ ω ∈ A, P ω) : 0 < ∑ ω ∈ A, P ω * g ω := by
  rw [← sum_fiberwise_of_maps_to (g := Yf) (t := A.image Yf)
    (fun ω hω => mem_image_of_mem _ hω)]
  have hnn : ∀ y ∈ A.image Yf, 0 ≤ ∑ ω ∈ A.filter (fun ω => Yf ω = y), P ω * g ω := by
    intro y _
    rcases eq_or_lt_of_le (sum_nonneg (fun ω _ => hP ω) :
      0 ≤ ∑ ω ∈ A.filter (fun ω => Yf ω = y), P ω) with h0 | hpos
    · have hz : ∀ ω ∈ A.filter (fun ω => Yf ω = y), P ω = 0 :=
        (sum_eq_zero_iff_of_nonneg (fun ω _ => hP ω)).1 h0.symm
      rw [sum_eq_zero fun ω hω => by rw [hz ω hω, zero_mul]]
    · exact (hg y hpos).le
  obtain ⟨y, hy, hpos⟩ : ∃ y ∈ A.image Yf, 0 < ∑ ω ∈ A.filter (fun ω => Yf ω = y), P ω := by
    by_contra hno
    push Not at hno
    have : ∑ ω ∈ A, P ω ≤ 0 := by
      rw [← sum_fiberwise_of_maps_to (g := Yf) (t := A.image Yf)
        (fun ω hω => mem_image_of_mem _ hω)]
      exact sum_nonpos hno
    linarith
  exact lt_of_lt_of_le (hg y hpos) (single_le_sum hnn hy)

/-- **Exercise 13.B.4** (MWG, p. 473). The no-trade theorem. On a finite probability space
(`P ≥ 0`) the asset is worth `V`, Ms. 1 observes `Y₁`, individual 2 observes `Y₂`, and each says
"trade" according to her signal (`T₁`, `T₂`); trade at price `p` happens when both do. If every
signal of Ms. 1 that leads to trade with positive probability makes her expected gain
`p - V` from trading strictly positive, and likewise for 2 with gain `V - p`, then trade has
probability zero. -/
theorem exercise_13_B_4 {Ω Y₁ Y₂ : Type*} [Fintype Ω] [DecidableEq Y₁] [DecidableEq Y₂]
    (P V : Ω → ℝ) (hP : ∀ ω, 0 ≤ P ω) (Y1 : Ω → Y₁) (Y2 : Ω → Y₂) (T1 : Y₁ → Bool)
    (T2 : Y₂ → Bool) (p : ℝ)
    (h1 : ∀ y, 0 < ∑ ω ∈ univ.filter (fun ω => T1 (Y1 ω) ∧ T2 (Y2 ω) ∧ Y1 ω = y), P ω →
      0 < ∑ ω ∈ univ.filter (fun ω => T1 (Y1 ω) ∧ T2 (Y2 ω) ∧ Y1 ω = y), P ω * (p - V ω))
    (h2 : ∀ y, 0 < ∑ ω ∈ univ.filter (fun ω => T1 (Y1 ω) ∧ T2 (Y2 ω) ∧ Y2 ω = y), P ω →
      0 < ∑ ω ∈ univ.filter (fun ω => T1 (Y1 ω) ∧ T2 (Y2 ω) ∧ Y2 ω = y), P ω * (V ω - p)) :
    ∑ ω ∈ univ.filter (fun ω => T1 (Y1 ω) ∧ T2 (Y2 ω)), P ω = 0 := by
  set A := univ.filter (fun ω => T1 (Y1 ω) ∧ T2 (Y2 ω))
  have hf1 : ∀ y, A.filter (fun ω => Y1 ω = y) =
      univ.filter (fun ω => T1 (Y1 ω) ∧ T2 (Y2 ω) ∧ Y1 ω = y) := by
    intro y; ext ω; simp [A, and_assoc]
  have hf2 : ∀ y, A.filter (fun ω => Y2 ω = y) =
      univ.filter (fun ω => T1 (Y1 ω) ∧ T2 (Y2 ω) ∧ Y2 ω = y) := by
    intro y; ext ω; simp [A, and_assoc]
  by_contra hne
  have hA : 0 < ∑ ω ∈ A, P ω := lt_of_le_of_ne (sum_nonneg fun ω _ => hP ω) (Ne.symm hne)
  have s1 := sum_pos_of_fibers P (fun ω => p - V ω) hP A Y1
    (fun y hy => by rw [hf1] at hy ⊢; exact h1 y hy) hA
  have s2 := sum_pos_of_fibers P (fun ω => V ω - p) hP A Y2
    (fun y hy => by rw [hf2] at hy ⊢; exact h2 y hy) hA
  have : ∑ ω ∈ A, P ω * (p - V ω) + ∑ ω ∈ A, P ω * (V ω - p) = 0 := by
    rw [← sum_add_distrib]; exact sum_eq_zero fun ω _ => by ring
  linarith

/-- **Exercise 13.C.5(a)** (MWG, p. 475). A risk-neutral consumer who cannot observe quality buys
at price `p` iff her expected valuation is at least `p`. -/
theorem exercise_13_C_5a (lam vH vL p : ℝ) :
    (p ≤ lam * vH + (1 - lam) * vL ↔ 0 ≤ lam * (vH - p) + (1 - lam) * (vL - p)) := by
  constructor <;> intro h <;> linarith

/-- **Exercise 13.C.5(b)** (MWG, p. 475). With `v_H > p > v_L > c_H > c_L`, there is no separating
PBE in which the two qualities choose different advertising levels `A_H ≠ A_L`: in such an
equilibrium the consumer buys only after `A_H` (she believes the quality is low after `A_L` and
`p > v_L`), so the low-quality firm must prefer not selling to mimicking
(`-A_L ≥ p - c_L - A_H`), and the high-quality firm must prefer selling
(`p - c_H - A_H ≥ -A_L`), which requires `c_H ≤ c_L`. -/
theorem exercise_13_C_5b {p cH cL : ℝ} (hc : cL < cH) :
    ¬ ∃ AH AL : ℝ, 0 ≤ AH ∧ 0 ≤ AL ∧ p - cL - AH ≤ -AL ∧ -AL ≤ p - cH - AH := by
  rintro ⟨AH, AL, -, -, hL, hH⟩
  linarith

/-- **Exercise 13.C.6(a)** (MWG, p. 475). Banks break even at `R(λp_G + (1 - λ)p_B) = 1 + r`
when both types borrow; entrepreneurs borrow iff `R ≤ Π`. So all projects are financed at
`R = (1 + r)/p̄` if `p̄Π ≥ 1 + r` and none otherwise, `p̄ = λp_G + (1 - λ)p_B`. `R` falls when
`p_G` or `λ` rise and rises with `r`; when `p̄Π < 1 + r < p_GΠ` no project is financed
although good projects are worth financing. -/
theorem exercise_13_C_6a {pG pB lam r Pf : ℝ} (hB : 0 < pB) (hBG : pB < pG) (hlam0 : 0 < lam)
    (hlam1 : lam < 1) (hr : 0 ≤ r) :
    let pbar := lam * pG + (1 - lam) * pB
    0 < pbar ∧ (1 + r) / pbar * pbar = 1 + r ∧
      ((1 + r) / pbar ≤ Pf ↔ 1 + r ≤ pbar * Pf) ∧
      (∀ pG', pG < pG' → (1 + r) / (lam * pG' + (1 - lam) * pB) < (1 + r) / pbar) ∧
      (∀ lam', lam < lam' → (1 + r) / (lam' * pG + (1 - lam') * pB) < (1 + r) / pbar) ∧
      (∀ r', r < r' → (1 + r) / pbar < (1 + r') / pbar) := by
  intro pbar
  have hp : 0 < pbar := by simp only [pbar]; nlinarith
  refine ⟨hp, div_mul_cancel₀ _ hp.ne', ?_, fun pG' h => ?_, fun lam' h => ?_, fun r' h => ?_⟩
  · rw [div_le_iff₀ hp, mul_comm]
  · exact div_lt_div_of_pos_left (by linarith) hp (by simp only [pbar]; nlinarith)
  · exact div_lt_div_of_pos_left (by linarith) hp (by simp only [pbar]; nlinarith)
  · exact div_lt_div_of_pos_right (by linarith) hp

/-- **Exercise 13.B.5** (MWG, p. 473). With `r(θ) = r` and the belief `E[θ | Θ = ∅] = θ̲`, a wage
`w` is a competitive equilibrium wage iff `w = E[θ]` when `w ≥ r` and `w = θ̲` when `w < r`. -/
def eqWagesB5 (m θl r : ℝ) : Set ℝ := {w | (r ≤ w → w = m) ∧ (w < r → w = θl)}

/-- **Exercise 13.B.5(a)** (MWG, p. 473). If `E[θ] ≥ r > θ̲` there are two equilibria,
`w* = E[θ]` (everybody employed) and `w* = θ̲` (nobody); if `θ̲ ≥ r` the only one is `E[θ]`; if
`r > E[θ]` the only one is `θ̲`. -/
theorem exercise_13_B_5a {m θl r : ℝ} (hθm : θl ≤ m) :
    (r ≤ m → θl < r → eqWagesB5 m θl r = {m, θl}) ∧ (r ≤ θl → eqWagesB5 m θl r = {m}) ∧
      (m < r → eqWagesB5 m θl r = {θl}) := by
  refine ⟨fun h1 h2 => ?_, fun h => ?_, fun h => ?_⟩ <;> ext w <;>
    simp only [eqWagesB5, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  · constructor
    · rintro ⟨ha, hb⟩
      rcases le_or_gt r w with hw | hw
      · exact Or.inl (ha hw)
      · exact Or.inr (hb hw)
    · rintro (rfl | rfl)
      · exact ⟨fun _ => rfl, fun hw => absurd h1 (not_le.2 hw)⟩
      · exact ⟨fun hw => absurd hw (not_le.2 h2), fun _ => rfl⟩
  · constructor
    · rintro ⟨ha, hb⟩
      rcases le_or_gt r w with hw | hw
      · exact ha hw
      · have := hb hw; linarith
    · rintro rfl; exact ⟨fun _ => rfl, fun hw => by linarith⟩
  · constructor
    · rintro ⟨ha, hb⟩
      rcases le_or_gt r w with hw | hw
      · have := ha hw; linarith
      · exact hb hw
    · rintro rfl; exact ⟨fun hw => by linarith, fun _ => rfl⟩

/-- **Exercise 13.B.5(b)** (MWG, p. 473). If `E[θ] > r` the full-employment equilibrium Pareto
dominates the no-employment one: firms earn zero in both, and every worker earns
`E[θ] > r` instead of `r`. -/
theorem exercise_13_B_5b {m θl r : ℝ} (hm : r < m) (hθl : θl < r) :
    max θl r < max m r ∧ max m r = m := by
  rw [max_eq_right hθl.le, max_eq_left hm.le]; exact ⟨hm, rfl⟩

/-- **Exercise 13.B.5(c)** (MWG, p. 473). The SPNE of the two-firm wage game when every type
accepts any wage `≥ r` (profit `E[θ] - w` for the firm with the highest wage): if `E[θ] > r`,
both firms offer `E[θ]` (the full-employment equilibrium); if `E[θ] = r`, any wages `≤ r`; if
`E[θ] < r`, any wages `< r` (nobody is employed). -/
theorem exercise_13_B_5c {m r : ℝ} (hm : 0 ≤ m) (w : Fin 2 → ℝ) :
    MWG.SimultaneousMoveGames.IsNashEquilibrium
        (wageGame (({ θL := 0, θH := 0, lam := 0, r := r, c := fun _ _ => 0 } :
          SigModel).offerProfit m)) w ↔
      (r < m → w 0 = m ∧ w 1 = m) ∧ (r = m → w 0 ≤ m ∧ w 1 ≤ m) ∧
        (m < r → w 0 < r ∧ w 1 < r) :=
  SigModel.bertrand_iff _ hm w

/-- **Exercise 13.B.5(d)** (MWG, p. 473). With `r(θ) = r`, the highest-wage competitive
equilibrium (`E[θ]` if `E[θ] ≥ r`, otherwise `θ̲` with nobody employed) is a constrained Pareto
optimum. -/
theorem exercise_13_B_5d {μ : MeasureTheory.Measure ℝ} {θl θh : ℝ} (hd : TypeDist μ θl θh)
    (r : ℝ) :
    IsConstrainedPO μ θl θh (fun _ => r) (if r ≤ meanType μ then meanType μ else θl) := by
  have := hd.prob
  intro we wu hb ⟨_, θ0, _, hstrict⟩
  simp only at hstrict
  have hl : θl ≤ meanType μ := hd.meanType_mem.1
  have heqpay : max r (meanType μ) ≤ max (if r ≤ meanType μ then meanType μ else θl) r := by
    split_ifs with h
    · rw [max_comm]
    · rw [max_eq_left (not_le.1 h).le]; exact le_max_right _ _
  unfold BudgetOK at hb
  by_cases hd' : r ≤ we - wu
  · have huniv : acceptSet (fun _ => r) (we - wu) = Set.univ := by
      ext θ; simp [acceptSet, hd']
    rw [huniv, MeasureTheory.Measure.real, MeasureTheory.measure_univ, ENNReal.toReal_one,
      MeasureTheory.setIntegral_univ] at hb
    have hwe : we ≤ meanType μ := by unfold meanType; linarith
    have : max we (wu + r) = we := max_eq_left (by linarith)
    rw [this] at hstrict
    linarith [le_max_right r (meanType μ)]
  · have hemp : acceptSet (fun _ => r) (we - wu) = ∅ := by
      ext θ; simp [acceptSet, not_le.1 hd']
    rw [hemp] at hb
    simp at hb
    have : max we (wu + r) = wu + r := max_eq_right (by linarith [not_le.1 hd'])
    rw [this] at hstrict
    linarith [le_max_left r (meanType μ),
      le_max_right (if r ≤ meanType μ then meanType μ else θl) r]

/-- **Proposition 13.B.2**, an instance (MWG, p. 447): with `r(θ) = θ/4` and `θ` uniform on
`[0, 2]`, `W* = {0, 1}` and the highest-wage equilibrium `w* = 1` is a constrained Pareto
optimum, while the Pareto-dominated equilibrium `w* = 0` is not. -/
theorem proposition_13_B_2_instance :
    IsConstrainedPO (unifMeas 0 2) 0 2 (akerlofR (1 / 4)) 1 ∧
      ¬ IsConstrainedPO (unifMeas 0 2) 0 2 (akerlofR (1 / 4)) 0 := by
  have hreg := akerlof_regular (α := 1 / 4) (by norm_num) (by norm_num)
  have hW := example_13_B_1_lowα (α := 1 / 4) (by norm_num) (by norm_num)
  have h1 : (1 : ℝ) ∈ eqWages (unifMeas 0 2) 0 2 (akerlofR (1 / 4)) := by rw [hW]; simp
  refine ⟨proposition_13_B_2 hreg ⟨h1, fun x hx => ?_⟩, ?_⟩
  · rw [hW] at hx; rcases hx with rfl | rfl <;> norm_num
  · refine dominated_not_constrainedPO hreg.dist hreg.meas h1
      (measure_acceptSet_pos hreg.dist hreg.dens hreg.cont (by simp [akerlofR])) one_pos
      ⟨0, ⟨le_rfl, zero_le_two⟩, by simp [akerlofR]⟩

end MWG.AdverseSelection
