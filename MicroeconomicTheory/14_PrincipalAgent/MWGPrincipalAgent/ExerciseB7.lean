/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPrincipalAgent.ExerciseC4
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Order.MonotoneContinuity

/-!
# Exercise 14.B.7: two periods

MWG, Exercise 14.B.7, p. 508. Two repetitions of the two-effort hidden-action model, no
discounting; the manager's utility is the sum of the two periods' `v(w) - g(e)`, with `v' > 0`,
`v'' < 0`. A contract pays `w₁(π₁)` in period 1 and `w₂(π₁, π₂)` in period 2; the manager chooses
`e₁` and, after observing `π₁`, `e₂(π₁)`. Profits take finitely many values (footnote 6;
corrections 7), with probabilities `f(π | e) > 0`.

* `b7U`, `B7Feas`, `b7Cost`: the manager's expected utility of a plan, the constraints for
  implementing `e_H` in both periods (participation and incentive compatibility against every
  plan `(e₁, e₂(·))`), and the owner's expected wage bill.
* `b7_local_inv`: a local inverse of `v`, with derivative `1/v'`.
* `b7_shift`: moving utility between the periods after a given `π₁` (period-1 utility down by
  `Δ`, period-2 utility up by `Δ` at every `π₂`) leaves the manager's payoff from every plan
  unchanged.
* `b7_improve`: **the "inverse Euler" condition**. If a feasible contract violates
  `1 / v'(w₁(π₁)) = Σ_{π₂} f(π₂|e_H) / v'(w₂(π₁, π₂))` at some `π₁`, a feasible contract with a
  strictly lower expected wage exists. So every optimal contract satisfies it at every `π₁`.
* `exercise_14_B_7`: **the answer: yes.** If `g(e_H) > g(e_L)` and `v` is strictly concave, no
  feasible contract whose period-2 wages do not depend on period-1 profits is optimal: the
  inverse Euler condition would make `w₁` constant, and then the manager would choose `e_L` in
  period 1.
* `exercise_14_B_7_instance`: repeating the optimal one-period scheme of Figure 14.B.1
  (`exA`, `exW`) in both periods is feasible and memoryless, hence not optimal.
-/

namespace MWG.PrincipalAgent

open Finset Filter Topology

/-- The manager's expected utility over the two periods from the plan `(e₁, e₂(·))`. -/
noncomputable def b7U {ε : Type*} {n : ℕ} (f : ε → Fin n → ℝ) (v : ℝ → ℝ) (g : ε → ℝ)
    (w1 : Fin n → ℝ) (w2 : Fin n → Fin n → ℝ) (e1 : ε) (e2 : Fin n → ε) : ℝ :=
  ∑ i, f e1 i * (v (w1 i) - g e1 + (∑ j, f (e2 i) j * v (w2 i j) - g (e2 i)))

/-- The constraints for implementing `e_H` in both periods: participation (two-period reservation
utility `ū`) and incentive compatibility against every plan. -/
def B7Feas {ε : Type*} {n : ℕ} (f : ε → Fin n → ℝ) (v : ℝ → ℝ) (g : ε → ℝ) (ubar : ℝ) (eH : ε)
    (w1 : Fin n → ℝ) (w2 : Fin n → Fin n → ℝ) : Prop :=
  ubar ≤ b7U f v g w1 w2 eH (fun _ => eH) ∧
    ∀ e1 e2, b7U f v g w1 w2 e1 e2 ≤ b7U f v g w1 w2 eH (fun _ => eH)

/-- The owner's expected wage bill when `e_H` is chosen in both periods. -/
noncomputable def b7Cost {ε : Type*} {n : ℕ} (f : ε → Fin n → ℝ) (eH : ε) (w1 : Fin n → ℝ)
    (w2 : Fin n → Fin n → ℝ) : ℝ :=
  ∑ i, f eH i * (w1 i + ∑ j, f eH j * w2 i j)

/-- A local inverse of `v` at `v(x₀)` (`v' > 0`), with derivative `1 / v'(x₀)`. -/
theorem b7_local_inv {v dv : ℝ → ℝ} (hv : ∀ x, HasDerivAt v (dv x) x) (hdv : ∀ x, 0 < dv x)
    (x0 : ℝ) : ∃ G : ℝ → ℝ, G (v x0) = x0 ∧ (∀ᶠ y in 𝓝 (v x0), v (G y) = y) ∧
      HasDerivAt G (dv x0)⁻¹ (v x0) := by
  classical
  have hmono : StrictMono v := strictMono_of_hasDerivAt_pos hv hdv
  have hc : Continuous v := continuous_iff_continuousAt.2 fun x => (hv x).continuousAt
  set a := v (x0 - 1)
  set b := v (x0 + 1)
  have hex : ∀ y ∈ Set.Ioo a b, ∃ x ∈ Set.Ioo (x0 - 1) (x0 + 1), v x = y := fun y hy =>
    intermediate_value_Ioo (by linarith) hc.continuousOn hy
  let G : ℝ → ℝ := fun y => if h : y ∈ Set.Ioo a b then Classical.choose (hex y h) else x0
  have hG : ∀ y (h : y ∈ Set.Ioo a b), G y ∈ Set.Ioo (x0 - 1) (x0 + 1) ∧ v (G y) = y := by
    intro y h
    simp only [G, h, ↓reduceDIte]
    exact Classical.choose_spec (hex y h)
  have hmem : v x0 ∈ Set.Ioo a b := ⟨hmono (by linarith), hmono (by linarith)⟩
  have hGx0 : G (v x0) = x0 := hmono.injective (hG _ hmem).2
  have hnhds : Set.Ioo a b ∈ 𝓝 (v x0) := Ioo_mem_nhds hmem.1 hmem.2
  have hev : ∀ᶠ y in 𝓝 (v x0), v (G y) = y := by
    filter_upwards [hnhds] with y hy
    exact (hG y hy).2
  have hcont : ContinuousAt G (v x0) := by
    refine continuousAt_of_monotoneOn_of_image_mem_nhds (s := Set.Ioo a b) ?_ hnhds ?_
    · intro y hy y' hy' hyy'
      exact hmono.le_iff_le.1 (by rw [(hG y hy).2, (hG y' hy').2]; exact hyy')
    · rw [hGx0]
      refine mem_of_superset (Ioo_mem_nhds (show x0 - 1 < x0 by linarith)
        (show x0 < x0 + 1 by linarith)) fun x hx => ?_
      have hy : v x ∈ Set.Ioo a b := ⟨hmono hx.1, hmono hx.2⟩
      exact ⟨v x, hy, hmono.injective (hG _ hy).2⟩
  refine ⟨G, hGx0, hev, ?_⟩
  exact HasDerivAt.of_local_left_inverse hcont (by rw [hGx0]; exact hv x0) (hdv x0).ne' hev

/-- Moving utility between the periods after `π₁ = i₀` leaves the manager's payoff from every plan
unchanged. -/
theorem b7_shift {ε : Type*} {n : ℕ} {f : ε → Fin n → ℝ} {v : ℝ → ℝ} {g : ε → ℝ}
    (hsum : ∀ e, ∑ j, f e j = 1) (w1 : Fin n → ℝ) (w2 : Fin n → Fin n → ℝ) (i0 : Fin n)
    {x Δ : ℝ} {W : Fin n → ℝ} (hx : v x = v (w1 i0) - Δ) (hW : ∀ j, v (W j) = v (w2 i0 j) + Δ)
    (e1 : ε) (e2 : Fin n → ε) :
    b7U f v g (Function.update w1 i0 x) (Function.update w2 i0 W) e1 e2 =
      b7U f v g w1 w2 e1 e2 := by
  unfold b7U
  refine sum_congr rfl fun i _ => ?_
  by_cases hi : i = i0
  · subst hi
    simp only [Function.update_self, hx, hW]
    have : ∑ j, f (e2 i) j * (v (w2 i j) + Δ) = ∑ j, f (e2 i) j * v (w2 i j) + Δ := by
      simp only [mul_add, sum_add_distrib, ← sum_mul, hsum, one_mul]
    rw [this]; ring
  · simp only [Function.update_of_ne hi]

/-- **Exercise 14.B.7** (MWG, p. 508), the inverse Euler condition. With `v` differentiable,
`v' > 0` and positive probabilities, if a feasible contract violates
`1 / v'(w₁(i₀)) = Σ_j f(j|e_H) / v'(w₂(i₀, j))` at some `i₀`, then shifting utility between the
periods after `i₀` gives a feasible contract with a strictly lower expected wage. -/
theorem b7_improve {ε : Type*} {n : ℕ} {f : ε → Fin n → ℝ} {v dv : ℝ → ℝ} {g : ε → ℝ}
    {ubar : ℝ} {eH : ε} (hv : ∀ x, HasDerivAt v (dv x) x) (hdv : ∀ x, 0 < dv x)
    (hf : ∀ e i, 0 < f e i) (hsum : ∀ e, ∑ j, f e j = 1) {w1 : Fin n → ℝ}
    {w2 : Fin n → Fin n → ℝ} (hfeas : B7Feas f v g ubar eH w1 w2) {i0 : Fin n}
    (hne : 1 / dv (w1 i0) ≠ ∑ j, f eH j / dv (w2 i0 j)) :
    ∃ w1' w2', B7Feas f v g ubar eH w1' w2' ∧ b7Cost f eH w1' w2' < b7Cost f eH w1 w2 := by
  obtain ⟨G1, hG1, hev1, hd1⟩ := b7_local_inv hv hdv (w1 i0)
  have hj : ∀ j, ∃ G : ℝ → ℝ, G (v (w2 i0 j)) = w2 i0 j ∧
      (∀ᶠ y in 𝓝 (v (w2 i0 j)), v (G y) = y) ∧ HasDerivAt G (dv (w2 i0 j))⁻¹ (v (w2 i0 j)) :=
    fun j => b7_local_inv hv hdv (w2 i0 j)
  choose G2 hG2 hev2 hd2 using hj
  let C : ℝ → ℝ := fun Δ => (G1 (v (w1 i0) - Δ) - w1 i0) +
    ∑ j, f eH j * (G2 j (v (w2 i0 j) + Δ) - w2 i0 j)
  have hC0 : C 0 = 0 := by simp [C, hG1, hG2]
  have hdC : HasDerivAt C (-(dv (w1 i0))⁻¹ + ∑ j, f eH j * (dv (w2 i0 j))⁻¹) 0 := by
    have h1 : HasDerivAt (fun Δ => G1 (v (w1 i0) - Δ)) (-(dv (w1 i0))⁻¹) 0 :=
      HasDerivAt.comp_const_sub (v (w1 i0)) 0 (by simpa using hd1)
    have h2 : ∀ j ∈ (univ : Finset (Fin n)), HasDerivAt
        (fun Δ => f eH j * (G2 j (v (w2 i0 j) + Δ) - w2 i0 j)) (f eH j * (dv (w2 i0 j))⁻¹) 0 :=
      fun j _ => ((HasDerivAt.comp_const_add (v (w2 i0 j)) 0
        (by simpa using hd2 j)).sub_const _).const_mul _
    exact (h1.sub_const _).add (HasDerivAt.fun_sum h2)
  have hD : -(dv (w1 i0))⁻¹ + ∑ j, f eH j * (dv (w2 i0 j))⁻¹ ≠ 0 := by
    intro h
    apply hne
    have : ∑ j, f eH j / dv (w2 i0 j) = ∑ j, f eH j * (dv (w2 i0 j))⁻¹ :=
      sum_congr rfl fun j _ => div_eq_mul_inv _ _
    rw [this, one_div]
    linarith
  have hfreq : ∃ᶠ Δ in 𝓝 (0 : ℝ), C Δ < 0 := by
    by_contra hcon
    rw [Filter.not_frequently] at hcon
    have hmin : IsLocalMin C 0 := by
      filter_upwards [hcon] with Δ hΔ
      rw [hC0]; exact not_lt.1 hΔ
    exact hD (hmin.hasDerivAt_eq_zero hdC)
  have hE1 : ∀ᶠ Δ in 𝓝 (0 : ℝ), v (G1 (v (w1 i0) - Δ)) = v (w1 i0) - Δ := by
    have ht : Tendsto (fun Δ : ℝ => v (w1 i0) - Δ) (𝓝 0) (𝓝 (v (w1 i0))) :=
      (continuous_const.sub continuous_id).tendsto' 0 _ (by simp)
    exact ht.eventually hev1
  have hE2 : ∀ᶠ Δ in 𝓝 (0 : ℝ), ∀ j, v (G2 j (v (w2 i0 j) + Δ)) = v (w2 i0 j) + Δ := by
    rw [Filter.eventually_all]
    intro j
    have ht : Tendsto (fun Δ : ℝ => v (w2 i0 j) + Δ) (𝓝 0) (𝓝 (v (w2 i0 j))) :=
      (continuous_const.add continuous_id).tendsto' 0 _ (by simp)
    exact ht.eventually (hev2 j)
  obtain ⟨Δ, hCΔ, h1, h2⟩ := (hfreq.and_eventually (hE1.and hE2)).exists
  refine ⟨Function.update w1 i0 (G1 (v (w1 i0) - Δ)),
    Function.update w2 i0 (fun j => G2 j (v (w2 i0 j) + Δ)), ⟨?_, fun e1 e2 => ?_⟩, ?_⟩
  · rw [b7_shift hsum w1 w2 i0 h1 h2]; exact hfeas.1
  · rw [b7_shift hsum w1 w2 i0 h1 h2, b7_shift hsum w1 w2 i0 h1 h2]; exact hfeas.2 e1 e2
  · unfold b7Cost
    have hCd : C Δ = (G1 (v (w1 i0) - Δ) + ∑ j, f eH j * G2 j (v (w2 i0 j) + Δ)) -
        (w1 i0 + ∑ j, f eH j * w2 i0 j) := by
      simp only [C, mul_sub, sum_sub_distrib]; ring
    have key : ∀ i, f eH i * (Function.update w1 i0 (G1 (v (w1 i0) - Δ)) i +
        ∑ j, f eH j * Function.update w2 i0 (fun j => G2 j (v (w2 i0 j) + Δ)) i j) =
        f eH i * (w1 i + ∑ j, f eH j * w2 i j) + if i = i0 then f eH i0 * C Δ else 0 := by
      intro i
      by_cases hi : i = i0
      · subst hi
        simp only [Function.update_self, ↓reduceIte, hCd]
        ring
      · simp only [Function.update_of_ne hi, hi, ↓reduceIte, add_zero]
    rw [sum_congr rfl fun i _ => key i, sum_add_distrib, sum_ite_eq' univ i0]
    simp only [mem_univ, ↓reduceIte]
    have := mul_lt_mul_of_pos_left (show C Δ < 0 from hCΔ) (hf eH i0)
    linarith

/-- **Exercise 14.B.7** (MWG, p. 508): **yes, period-2 wages depend on period-1 profits in the
optimal contract.** Suppose `g(e_L) < g(e_H)`, `v` is strictly concave and differentiable with
`v' > 0`, and all probabilities are positive. If a feasible contract (implementing `e_H` in both
periods) has period-2 wages `w₂(π₁, π₂) = h(π₂)` independent of `π₁`, then a feasible contract
with a strictly lower expected wage exists. (Otherwise the inverse Euler condition `b7_improve`
would hold at every `π₁`, forcing `w₁` to be constant, and then the manager would choose `e_L` in
period 1.) -/
theorem exercise_14_B_7 {ε : Type*} {n : ℕ} {f : ε → Fin n → ℝ} {v dv : ℝ → ℝ} {g : ε → ℝ}
    {ubar : ℝ} {eL eH : ε} (hv : StrictConcaveOn ℝ Set.univ v)
    (hdv : ∀ x, HasDerivAt v (dv x) x) (hdvpos : ∀ x, 0 < dv x) (hf : ∀ e i, 0 < f e i)
    (hsum : ∀ e, ∑ j, f e j = 1) (hg : g eL < g eH) {w1 : Fin n → ℝ}
    {w2 : Fin n → Fin n → ℝ} (hfeas : B7Feas f v g ubar eH w1 w2)
    (hmem : ∃ h : Fin n → ℝ, ∀ i j, w2 i j = h j) :
    ∃ w1' w2', B7Feas f v g ubar eH w1' w2' ∧ b7Cost f eH w1' w2' < b7Cost f eH w1 w2 := by
  by_cases hIE : ∀ i, 1 / dv (w1 i) = ∑ j, f eH j / dv (w2 i j)
  · exfalso
    obtain ⟨h, hh⟩ := hmem
    have hn : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · subst h0; have := hsum eH; simp at this
      · exact h0
    set i0 : Fin n := ⟨0, hn⟩
    have hw1 : ∀ i, w1 i = w1 i0 := by
      intro i
      have h1 := hIE i
      have h2 := hIE i0
      simp only [hh] at h1 h2
      have hd : dv (w1 i) = dv (w1 i0) := by
        rw [← h2, one_div, one_div] at h1
        exact inv_injective h1
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · exact (c4_dv_lt hv hdv hlt).ne' hd
      · exact (c4_dv_lt hv hdv hlt).ne hd
    have hU : ∀ e, b7U f v g w1 w2 e (fun _ => eH) =
        v (w1 i0) - g e + (∑ j, f eH j * v (h j) - g eH) := by
      intro e
      unfold b7U
      simp only [hw1, hh]
      rw [← sum_mul, hsum, one_mul]
    have := hfeas.2 eL (fun _ => eH)
    rw [hU, hU] at this
    linarith
  · push Not at hIE
    obtain ⟨i0, hne⟩ := hIE
    exact b7_improve hdv hdvpos hf hsum hfeas hne

/-- The probabilities of the instance: `f(·|e_L) = (1/2, 1/4, 1/4)`, `f(·|e_H) = (1/4, 1/2, 1/4)`
(those of `exA`). -/
noncomputable def b7f (b : Bool) : Fin 3 → ℝ :=
  if b then ![1 / 4, 1 / 2, 1 / 4] else ![1 / 2, 1 / 4, 1 / 4]

/-- The period-1 scheme of the instance: the optimal one-period scheme `exW` of Figure 14.B.1,
`(0, log (5/2), log 2)`. -/
noncomputable def b7w : Fin 3 → ℝ := ![0, Real.log (5 / 2), Real.log 2]

/-- **Exercise 14.B.7, an instance** (MWG, p. 508). Repeating the optimal one-period scheme of
Figure 14.B.1 in both periods (`v(w) = -exp(-w)`, `g(e_H) = 3/20`, `g(e_L) = 0`, two-period
reservation utility `2 · (-29/40)`) is feasible and memoryless; by `exercise_14_B_7` a strictly
cheaper feasible contract exists. -/
theorem exercise_14_B_7_instance :
    B7Feas b7f (fun w => -Real.exp (-w)) (fun b => if b then 3 / 20 else 0) (-29 / 20) true
      b7w (fun _ j => b7w j) ∧
    ∃ w1' w2', B7Feas b7f (fun w => -Real.exp (-w)) (fun b => if b then 3 / 20 else 0)
      (-29 / 20) true w1' w2' ∧
      b7Cost b7f true w1' w2' < b7Cost b7f true b7w (fun _ j => b7w j) := by
  have hsum : ∀ e, ∑ j, b7f e j = 1 := by
    intro e; cases e <;> simp [b7f, Fin.sum_univ_three] <;> norm_num
  have hf : ∀ e i, 0 < b7f e i := by
    intro e i; cases e <;> fin_cases i <;> simp [b7f]
  have e1 : Real.exp (-Real.log (5 / 2)) = 2 / 5 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have e2 : Real.exp (-Real.log 2) = 1 / 2 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have hinner : ∀ e : Bool, ∑ j, b7f e j * -Real.exp (-b7w j) - (if e then 3 / 20 else 0) =
      -29 / 40 := by
    intro e
    cases e <;> simp [b7f, b7w, Fin.sum_univ_three, e1, e2] <;> norm_num
  have hU : ∀ e1 e2, b7U b7f (fun w => -Real.exp (-w)) (fun b => if b then 3 / 20 else 0) b7w
      (fun _ j => b7w j) e1 e2 = -29 / 20 := by
    intro e1 e2
    unfold b7U
    have : ∀ i, b7f e1 i * (-Real.exp (-b7w i) - (if e1 then 3 / 20 else 0) +
        (∑ j, b7f (e2 i) j * -Real.exp (-b7w j) - (if e2 i then 3 / 20 else 0))) =
        b7f e1 i * -Real.exp (-b7w i) - b7f e1 i * (if e1 then 3 / 20 else 0) +
          b7f e1 i * (-29 / 40) := fun i => by rw [hinner]; ring
    simp only [this, sum_add_distrib, sum_sub_distrib, ← sum_mul, hsum, one_mul]
    have := hinner e1
    linarith
  have hfeas : B7Feas b7f (fun w => -Real.exp (-w)) (fun b => if b then 3 / 20 else 0)
      (-29 / 20) true b7w (fun _ j => b7w j) :=
    ⟨by rw [hU], fun e1 e2 => by rw [hU, hU]⟩
  refine ⟨hfeas, exercise_14_B_7 (eL := false) exA_strictConcave exA_hasDeriv
    (fun _ => Real.exp_pos _) hf hsum (by norm_num) hfeas ⟨b7w, fun _ _ => rfl⟩⟩

end MWG.PrincipalAgent
