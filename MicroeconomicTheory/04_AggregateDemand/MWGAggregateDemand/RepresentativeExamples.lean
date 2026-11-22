/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGAggregateDemand.Representative
import MWGAggregateDemand.AggregateWealth
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Examples 4.D.1 and 4.D.2: homothetic and Gorman economies

MWG, Section 4.D, pp. 118-120, and Exercises 4.D.6 and 4.D.7 (p. 126).

* **Example 4.D.1 / Exercise 4.D.6**: with utilities homogeneous of degree one and the social
  welfare function `W(u) = ∑ᵢ αᵢ ln uᵢ`, the optimal distribution in (4.D.1) is the
  price-independent rule `wᵢ = αᵢ w`, and it is the unique optimum (`exercise_4_D_6`). The
  logarithm makes `W` defined only for positive utilities, so distributions are positive here
  (correction 7).
* **Example 4.D.2 / Exercise 4.D.7**: with Gorman-form indirect utilities
  `vᵢ(p, w) = aᵢ(p) + b(p) w` and the utilitarian `W = ∑ᵢ uᵢ`, every distribution of `w` solves
  (4.D.1) and `v(p, w) = ∑ᵢ aᵢ(p) + b(p) w`.
* p. 119: `∑ᵢ aᵢ(p) + b(p) w` orders price-wealth pairs exactly as the value function of (4.D.1)
  for any strictly increasing `W` (`example_4_D_2_any_W`).
* p. 120: `(p', w')` passes the potential compensation test over `(p, w)` iff
  `∑ᵢ aᵢ(p') + b(p') w' > ∑ᵢ aᵢ(p) + b(p) w` (`example_4_D_2_compensation`).

As in the book (footnotes 17 and 20), the Gorman statements neglect nonnegativity of wealth:
the indirect utilities are the functions `aᵢ(p) + b(p) w` of real `w`.
-/

namespace MWG.AggregateDemand

open MWG.ConsumerChoice MWG.ClassicalDemand

variable {L I : ℕ}

/-- **Example 4.D.1** (MWG, pp. 118-119; Exercise 4.D.6, p. 126). Suppose every `uᵢ` is
homogeneous of degree one (so `vᵢ(p, wᵢ) = wᵢ vᵢ(p, 1)`), `vᵢ(p, 1) > 0`, and
`W(u) = ∑ᵢ αᵢ ln uᵢ` with `αᵢ > 0`, `∑ αᵢ = 1`. Then among positive distributions with
`∑ᵢ wᵢ ≤ w`, the price-independent rule `wᵢ = αᵢ w` maximizes `W(v₁(p, w₁), …)`, and it is
the only maximizer. -/
theorem exercise_4_D_6 {us : Fin I → (Fin L → ℝ) → ℝ} (hu : ∀ i, HomogeneousOneOn (us i))
    {α : Fin I → ℝ} (hα : ∀ i, 0 < α i) (hα1 : ∑ i, α i = 1) {p : Fin L → ℝ}
    (hb : ∀ i, 0 < indirectUtility (us i) p 1) {w : ℝ} (hw : 0 < w) (ws : Fin I → ℝ)
    (hws : ∀ i, 0 < ws i) (hsum : ∑ i, ws i ≤ w) :
    ∑ i, α i * Real.log (indirectUtility (us i) p (ws i)) ≤
        ∑ i, α i * Real.log (indirectUtility (us i) p (α i * w)) ∧
      (∑ i, α i * Real.log (indirectUtility (us i) p (ws i)) =
          ∑ i, α i * Real.log (indirectUtility (us i) p (α i * w)) →
        ws = fun i => α i * w) := by
  have hv : ∀ i t, 0 < t → indirectUtility (us i) p t = t * indirectUtility (us i) p 1 :=
    fun i t ht => indirectUtility_homothetic (hu i) p ht
  have hαw : ∀ i, 0 < α i * w := fun i => mul_pos (hα i) hw
  -- the difference of the two objectives
  have hdiff : ∀ i, α i * Real.log (indirectUtility (us i) p (ws i)) -
      α i * Real.log (indirectUtility (us i) p (α i * w)) =
        α i * Real.log (ws i / (α i * w)) := by
    intro i
    rw [hv i _ (hws i), hv i _ (hαw i), Real.log_mul (hws i).ne' (hb i).ne',
      Real.log_mul (hαw i).ne' (hb i).ne', Real.log_div (hws i).ne' (hαw i).ne']
    ring
  have hlog : ∀ i, α i * Real.log (ws i / (α i * w)) ≤ ws i / w - α i := by
    intro i
    have := Real.log_le_sub_one_of_pos (div_pos (hws i) (hαw i))
    have h2 : α i * (ws i / (α i * w) - 1) = ws i / w - α i := by
      have := (hα i).ne'
      have := hw.ne'
      field_simp
    nlinarith [hα i]
  have htot : ∑ i, (ws i / w - α i) ≤ 0 := by
    rw [Finset.sum_sub_distrib, hα1, ← Finset.sum_div]
    have := (div_le_one hw).mpr hsum
    linarith
  have hle : ∑ i, (α i * Real.log (indirectUtility (us i) p (ws i)) -
      α i * Real.log (indirectUtility (us i) p (α i * w))) ≤ 0 := by
    rw [Finset.sum_congr rfl fun i _ => hdiff i]
    exact (Finset.sum_le_sum fun i _ => hlog i).trans htot
  rw [Finset.sum_sub_distrib] at hle
  refine ⟨by linarith, fun heq => ?_⟩
  funext i
  by_contra hne
  have hne1 : ws i / (α i * w) ≠ 1 := by
    intro h
    exact hne ((div_eq_one_iff_eq (hαw i).ne').mp h)
  have hlt : α i * Real.log (ws i / (α i * w)) < ws i / w - α i := by
    have := Real.log_lt_sub_one_of_pos (div_pos (hws i) (hαw i)) hne1
    have h2 : α i * (ws i / (α i * w) - 1) = ws i / w - α i := by
      have := (hα i).ne'
      have := hw.ne'
      field_simp
    nlinarith [hα i]
  have hstrict : ∑ i, α i * Real.log (ws i / (α i * w)) < ∑ i, (ws i / w - α i) :=
    Finset.sum_lt_sum (fun j _ => hlog j) ⟨i, Finset.mem_univ i, hlt⟩
  have h0 : ∑ i, α i * Real.log (ws i / (α i * w)) = 0 := by
    rw [← Finset.sum_congr rfl fun i _ => hdiff i, Finset.sum_sub_distrib, heq, sub_self]
  linarith

/-- **Example 4.D.2** (MWG, p. 119; Exercise 4.D.7, p. 126). With Gorman-form indirect utilities
`vᵢ(p, wᵢ) = aᵢ(p) + b(p) wᵢ` (common `b(p) ≥ 0`) and the utilitarian social welfare function,
every distribution `(wᵢ)` of `w` (`∑ᵢ wᵢ = w`) solves (4.D.1), and the optimal value is
`v(p, w) = ∑ᵢ aᵢ(p) + b(p) w`. -/
theorem exercise_4_D_7 (a : Fin I → (Fin L → ℝ) → ℝ) (b : (Fin L → ℝ) → ℝ) {p : Fin L → ℝ}
    (hb : 0 ≤ b p) {w : ℝ} {ws : Fin I → ℝ} (hws : ∑ i, ws i = w) :
    (∑ i, (a i p + b p * ws i) = ∑ i, a i p + b p * w) ∧
      ∀ ws' : Fin I → ℝ, ∑ i, ws' i ≤ w →
        ∑ i, (a i p + b p * ws' i) ≤ ∑ i, (a i p + b p * ws i) := by
  have hval : ∀ v : Fin I → ℝ, ∑ i, (a i p + b p * v i) = ∑ i, a i p + b p * ∑ i, v i := by
    intro v
    rw [Finset.sum_add_distrib, Finset.mul_sum]
  refine ⟨by rw [hval, hws], fun ws' h' => ?_⟩
  rw [hval, hval, hws]
  nlinarith

/-- **Example 4.D.2** (MWG, pp. 119-120), the compensating distribution. With Gorman-form
indirect utilities and `b(p') ≠ 0`, for any distribution `(wᵢ)` of `w` and any `c`, the
distribution `w'ᵢ = (aᵢ(p) + b(p) wᵢ + c/I - aᵢ(p'))/b(p')` raises every consumer's utility by
`c/I`, and it distributes `w'` exactly when `c = V(p', w') - V(p, w)`, where
`V(p, w) = ∑ᵢ aᵢ(p) + b(p) w`. -/
theorem gorman_compensating_distribution (hI : 0 < I) (a : Fin I → (Fin L → ℝ) → ℝ)
    (b : (Fin L → ℝ) → ℝ) {p p' : Fin L → ℝ} (hb' : b p' ≠ 0) {w w' : ℝ} (ws : Fin I → ℝ)
    (hws : ∑ i, ws i = w) :
    let c := (∑ i, a i p' + b p' * w') - (∑ i, a i p + b p * w)
    let ws' : Fin I → ℝ := fun i => (a i p + b p * ws i + c / I - a i p') / b p'
    (∀ i, a i p' + b p' * ws' i = a i p + b p * ws i + c / I) ∧ ∑ i, ws' i = w' := by
  intro c ws'
  have hIr : (I : ℝ) ≠ 0 := by exact_mod_cast hI.ne'
  refine ⟨fun i => by simp only [ws']; field_simp; ring, ?_⟩
  simp only [ws']
  rw [← Finset.sum_div, div_eq_iff hb']
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hws,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp only [c]
  field_simp
  ring

/-- **Example 4.D.2** (MWG, p. 119). When indirect utilities have the Gorman form with common
`b(p) > 0`, `V(p, w) = ∑ᵢ aᵢ(p) + b(p) w` is an indirect utility function for the normative
representative consumer relative to *any* strictly increasing social welfare function `W`: if
the rule `(wᵢ(p, w))` (a distribution of `w`) solves (4.D.1) for `W` at every `(p, w)`, then the
value `v*(p, w)` satisfies `v*(p, w) < v*(p', w') ⟺ V(p, w) < V(p', w')`. (The book proves
this from first-order conditions and the concavity of `W`; the potential-compensation argument
here needs neither.) -/
theorem example_4_D_2_any_W (hI : 0 < I) {W : SocialWelfareFunction I} (hWs : StrictMono W)
    (a : Fin I → (Fin L → ℝ) → ℝ) (b : (Fin L → ℝ) → ℝ) (hb : ∀ p, 0 < b p)
    {wr : Fin I → (Fin L → ℝ) → ℝ → ℝ} (hrule : IsWealthDistributionRule wr)
    (hopt : ∀ p w (ws : Fin I → ℝ), ∑ i, ws i ≤ w →
      (W fun i => a i p + b p * ws i) ≤ W fun i => a i p + b p * wr i p w)
    (p : Fin L → ℝ) (w : ℝ) (p' : Fin L → ℝ) (w' : ℝ) :
    ((W fun i => a i p + b p * wr i p w) < W fun i => a i p' + b p' * wr i p' w') ↔
      ∑ i, a i p + b p * w < ∑ i, a i p' + b p' * w' := by
  have hIr : (0 : ℝ) < I := by exact_mod_cast hI
  -- compensating from `(q, v)` to `(q', v')` when `V(q, v) ≤ V(q', v')`
  have key : ∀ (q : Fin L → ℝ) (v : ℝ) (q' : Fin L → ℝ) (v' : ℝ),
      ∑ i, a i q + b q * v ≤ ∑ i, a i q' + b q' * v' →
      ∃ c, (∑ i, a i q' + b q' * v') - (∑ i, a i q + b q * v) = c ∧
        (W fun i => a i q + b q * wr i q v + c / I) ≤ W fun i => a i q' + b q' * wr i q' v' := by
    intro q v q' v' _
    obtain ⟨h1, h2⟩ := gorman_compensating_distribution hI a b (hb q').ne' (w' := v')
      (fun i => wr i q v) (hrule q v)
    refine ⟨_, rfl, ?_⟩
    have := hopt q' v' _ h2.le
    simp only [h1] at this
    exact this
  constructor
  · intro hlt
    by_contra hge
    push Not at hge
    obtain ⟨c, hc, hle⟩ := key p' w' p w hge
    have hc0 : 0 ≤ c := by linarith
    have hmono : (W fun i => a i p' + b p' * wr i p' w') ≤
        W fun i => a i p' + b p' * wr i p' w' + c / I :=
      hWs.monotone fun i => le_add_of_nonneg_right (div_nonneg hc0 hIr.le)
    linarith
  · intro hlt
    obtain ⟨c, hc, hle⟩ := key p w p' w' hlt.le
    have hc0 : 0 < c := by linarith
    have hstrict : (W fun i => a i p + b p * wr i p w) <
        W fun i => a i p + b p * wr i p w + c / I :=
      hWs (Pi.lt_def.mpr ⟨fun i => le_add_of_nonneg_right (div_nonneg hc0.le hIr.le),
        ⟨⟨0, hI⟩, lt_add_of_pos_right _ (div_pos hc0 hIr)⟩⟩)
    exact hstrict.trans_le hle

/-- **Example 4.D.2** (MWG, p. 120). With Gorman-form indirect utilities and common `b > 0`,
`(p', w')` passes the potential compensation test over `(p, w)` (for every distribution of `w`
there is a distribution of `w'` making everybody strictly better off) if and only if
`∑ᵢ aᵢ(p') + b(p') w' > ∑ᵢ aᵢ(p) + b(p) w`. -/
theorem example_4_D_2_compensation (hI : 0 < I) (a : Fin I → (Fin L → ℝ) → ℝ)
    (b : (Fin L → ℝ) → ℝ) (hb : ∀ p, 0 < b p) (p : Fin L → ℝ) (w : ℝ) (p' : Fin L → ℝ)
    (w' : ℝ) :
    (∀ ws : Fin I → ℝ, ∑ i, ws i = w → ∃ ws' : Fin I → ℝ, ∑ i, ws' i = w' ∧
      ∀ i, a i p + b p * ws i < a i p' + b p' * ws' i) ↔
      ∑ i, a i p + b p * w < ∑ i, a i p' + b p' * w' := by
  have hIr : (0 : ℝ) < I := by exact_mod_cast hI
  constructor
  · intro h
    -- apply the test to the equal split
    obtain ⟨ws', hsum', hlt⟩ := h (fun _ => w / I) (by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp)
    have := Finset.sum_lt_sum_of_nonempty ⟨⟨0, hI⟩, Finset.mem_univ _⟩ fun i _ => hlt i
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hsum', Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    have e : (I : ℝ) * (w / I) = w := by field_simp
    rw [e] at this
    exact this
  · intro hlt ws hws
    obtain ⟨h1, h2⟩ := gorman_compensating_distribution hI a b (p := p) (hb p').ne' (w' := w')
      ws hws
    refine ⟨_, h2, fun i => ?_⟩
    rw [h1 i]
    have : 0 < ((∑ i, a i p' + b p' * w') - (∑ i, a i p + b p * w)) / I :=
      div_pos (by linarith) hIr
    linarith

end MWG.AggregateDemand
