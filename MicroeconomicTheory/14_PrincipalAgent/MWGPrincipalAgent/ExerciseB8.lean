/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPrincipalAgent.KuhnTucker
import MWGPrincipalAgent.ExerciseB7
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Exercise 14.B.8: costly investigation

MWG, Exercise 14.B.8, p. 508. Profits `π` and a signal `y` have a joint distribution
`f(π, y | e) > 0`; here both take finitely many values (footnote 6; corrections 7), `f(π|e)` is
the marginal of `π`. After observing `π` the owner investigates with probability `p(π)` at cost
`c`; the contract pays `w(π)` without investigation and `w(π, y)` after one. The manager has
utility `v(w) - g(e)`, two effort levels, reservation utility `ū`.

* `b8EV`, `b8Cost`, `B8Feas`: expected utility of income, the owner's expected cost (wages and
  investigation), and the constraints for implementing `e_H`.
* `b8_persp`: the program is convex in the variables `((1 - p) v(w), p, p v(w(·, y)))` (a
  perspective argument): mixtures of contracts can be matched in utility at no higher cost.
* `b8_lag`: the Lagrangian separates across profit levels:
  `Σ_π [(1 - p(π)) A_π(w(π)) + p(π) B_π(w(π, ·))]`, with `A_π`, `B_π` the pointwise Lagrangians
  without and with investigation (`B_π` includes the cost `c f(π|e_H)`).
* `exercise_14_B_8`: **the characterization.** At every optimal contract for implementing `e_H`
  there are multipliers `γ, μ ≥ 0` with complementary slackness such that, at every profit level:
  without investigation (`p < 1`) `1/v'(w(π)) = γ + μ [1 - f(π|e_L)/f(π|e_H)]`; after
  investigation (`p > 0`) `1/v'(w(π, y)) = γ + μ [1 - f(π, y|e_L)/f(π, y|e_H)]`; the owner does not
  investigate (`p < 1`) only if `A_π(w(π)) ≤ B_π(w')` for every `w'`, and investigates (`p > 0`)
  only if `B_π(w(π, ·)) ≤ A_π(w')` for every `w'`: investigation happens exactly where its
  Lagrangian saving exceeds its cost, and randomization only under indifference.
* `exercise_14_B_8_instance`: with an uninformative signal and `c ≥ 0`, never investigating and
  paying the scheme of Figure 14.B.1 is optimal; the theorem applies to it.
-/

namespace MWG.PrincipalAgent

open Finset Set

variable {ε : Type*} {n m : ℕ}

/-- The marginal probability `f(π_i | e) = Σ_y f(π_i, y | e)`. -/
noncomputable def b8F (fq : ε → Fin n → Fin m → ℝ) (e : ε) (i : Fin n) : ℝ := ∑ k, fq e i k

/-- Expected utility of income under effort `e`:
`Σ_π [(1 - p(π)) f(π|e) v(w(π)) + p(π) Σ_y f(π, y|e) v(w(π, y))]`. -/
noncomputable def b8EV (fq : ε → Fin n → Fin m → ℝ) (v : ℝ → ℝ) (e : ε) (p w0 : Fin n → ℝ)
    (w1 : Fin n → Fin m → ℝ) : ℝ :=
  ∑ i, ((1 - p i) * b8F fq e i * v (w0 i) + p i * ∑ k, fq e i k * v (w1 i k))

/-- The owner's expected cost when `e_H` is chosen: wages plus `c` per investigation. -/
noncomputable def b8Cost (fq : ε → Fin n → Fin m → ℝ) (c : ℝ) (eH : ε) (p w0 : Fin n → ℝ)
    (w1 : Fin n → Fin m → ℝ) : ℝ :=
  ∑ i, ((1 - p i) * b8F fq eH i * w0 i + p i * (∑ k, fq eH i k * w1 i k + c * b8F fq eH i))

/-- The constraints for implementing `e_H` (two effort levels): probabilities in `[0, 1]`,
participation and incentive compatibility. -/
def B8Feas (fq : ε → Fin n → Fin m → ℝ) (v : ℝ → ℝ) (g : ε → ℝ) (ubar : ℝ) (eL eH : ε)
    (p w0 : Fin n → ℝ) (w1 : Fin n → Fin m → ℝ) : Prop :=
  (∀ i, 0 ≤ p i ∧ p i ≤ 1) ∧ ubar ≤ b8EV fq v eH p w0 w1 - g eH ∧
    b8EV fq v eL p w0 w1 - g eL ≤ b8EV fq v eH p w0 w1 - g eH

/-- The pointwise Lagrangian without investigation at profit level `i`. -/
noncomputable def b8A (fq : ε → Fin n → Fin m → ℝ) (v : ℝ → ℝ) (eL eH : ε) (γ μ : ℝ)
    (i : Fin n) (x : ℝ) : ℝ :=
  b8F fq eH i * x - (γ + μ) * (b8F fq eH i * v x) + μ * (b8F fq eL i * v x)

/-- The pointwise Lagrangian with investigation at profit level `i` (including its cost). -/
noncomputable def b8B (fq : ε → Fin n → Fin m → ℝ) (v : ℝ → ℝ) (c : ℝ) (eL eH : ε) (γ μ : ℝ)
    (i : Fin n) (z : Fin m → ℝ) : ℝ :=
  ∑ k, (fq eH i k * z k - (γ + μ) * (fq eH i k * v (z k)) + μ * (fq eL i k * v (z k))) +
    c * b8F fq eH i

/-- **The perspective step** (Exercise 14.B.8). For weights `s₀, s₁ ≥ 0` and wages `a, b`, some
wage `x` has `(s₀ + s₁) v(x) = s₀ v(a) + s₁ v(b)` and `(s₀ + s₁) x ≤ s₀ a + s₁ b` (`v` concave,
continuous and strictly increasing). -/
theorem b8_persp {v : ℝ → ℝ} (hv : ConcaveOn ℝ univ v) (hvc : Continuous v)
    (hvm : StrictMono v) {s0 s1 : ℝ} (h0 : 0 ≤ s0) (h1 : 0 ≤ s1) (a b : ℝ) :
    ∃ x, (s0 + s1) * v x = s0 * v a + s1 * v b ∧ (s0 + s1) * x ≤ s0 * a + s1 * b := by
  rcases (add_nonneg h0 h1).lt_or_eq with hs | hs
  · set α := s0 / (s0 + s1)
    set β := s1 / (s0 + s1)
    have hα : 0 ≤ α := div_nonneg h0 hs.le
    have hβ : 0 ≤ β := div_nonneg h1 hs.le
    have hαβ : α + β = 1 := by simp only [α, β]; field_simp
    have hmem : α * v a + β * v b ∈ Icc (v (min a b)) (v (max a b)) := by
      have a1 := hvm.monotone (min_le_left a b)
      have a2 := hvm.monotone (min_le_right a b)
      have a3 := hvm.monotone (le_max_left a b)
      have a4 := hvm.monotone (le_max_right a b)
      have e1 : v (min a b) = α * v (min a b) + β * v (min a b) := by
        rw [← add_mul, hαβ, one_mul]
      have e2 : v (max a b) = α * v (max a b) + β * v (max a b) := by
        rw [← add_mul, hαβ, one_mul]
      constructor
      · linarith [mul_le_mul_of_nonneg_left a1 hα, mul_le_mul_of_nonneg_left a2 hβ]
      · linarith [mul_le_mul_of_nonneg_left a3 hα, mul_le_mul_of_nonneg_left a4 hβ]
    obtain ⟨x, -, hx⟩ := intermediate_value_Icc min_le_max hvc.continuousOn hmem
    refine ⟨x, ?_, ?_⟩
    · rw [hx]; simp only [α, β]; field_simp
    · have hc := hv.2 (mem_univ a) (mem_univ b) hα hβ hαβ
      simp only [smul_eq_mul] at hc
      rw [← hx] at hc
      have hle := hvm.le_iff_le.1 hc
      have : (s0 + s1) * (α * a + β * b) = s0 * a + s1 * b := by
        simp only [α, β]; field_simp
      nlinarith
  · have hs0 : s0 = 0 := by linarith
    have hs1 : s1 = 0 := by linarith
    exact ⟨0, by rw [hs0, hs1]; ring, by rw [hs0, hs1]; simp⟩

/-- **The Lagrangian separates** across profit levels. -/
theorem b8_lag (fq : ε → Fin n → Fin m → ℝ) (v : ℝ → ℝ) (c : ℝ) (eL eH : ε) (γ μ : ℝ)
    (p w0 : Fin n → ℝ) (w1 : Fin n → Fin m → ℝ) :
    b8Cost fq c eH p w0 w1 - (γ + μ) * b8EV fq v eH p w0 w1 + μ * b8EV fq v eL p w0 w1 =
      ∑ i, ((1 - p i) * b8A fq v eL eH γ μ i (w0 i) + p i * b8B fq v c eL eH γ μ i (w1 i)) := by
  unfold b8Cost b8EV b8A b8B
  rw [mul_sum, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum]
  ring

/-- Changing a sum at one index. -/
theorem b8_upd {k : ℕ} (T T' : Fin k → ℝ) (i0 : Fin k) (h : ∀ i, i ≠ i0 → T' i = T i) :
    ∑ i, T' i = ∑ i, T i + (T' i0 - T i0) := by
  have : ∀ i, T' i = T i + if i = i0 then T' i0 - T i0 else 0 := by
    intro i
    by_cases hi : i = i0
    · subst hi; simp
    · simp [hi, h i hi]
  rw [sum_congr rfl fun i _ => this i, sum_add_distrib, sum_ite_eq' univ i0]
  simp

/-- A minimizer of `x ↦ P x - K (Q v(x))` type expressions: if `x ↦ a x - b v(x)` is minimized
at `x₀` with `a > 0` and `v'(x₀) > 0`, then `1 / v'(x₀) = b / a`. -/
theorem b8_foc {v dv : ℝ → ℝ} (hdv : ∀ x, HasDerivAt v (dv x) x) (hdvpos : ∀ x, 0 < dv x)
    {a b x0 : ℝ} (ha : 0 < a) (hmin : ∀ x, a * x0 - b * v x0 ≤ a * x - b * v x) :
    1 / dv x0 = b / a := by
  have hd : HasDerivAt (fun x => a * x - b * v x) (a * 1 - b * dv x0) x0 :=
    ((hasDerivAt_id' x0).const_mul a).sub ((hdv x0).const_mul b)
  have h0 := IsLocalMin.hasDerivAt_eq_zero (Filter.Eventually.of_forall hmin) hd
  have := hdvpos x0
  field_simp
  linarith

/-- **Exercise 14.B.8** (MWG, p. 508), the characterization of the optimal contract for
implementing `e_H` with costly investigation. Assumptions: `v` concave and differentiable with
`v' > 0`; positive joint probabilities; the profit distributions under `e_L` and `e_H` differ
(`f(π|e_L) < f(π|e_H)` at some `π`). At every optimal contract there are multipliers
`γ, μ ≥ 0` with complementary slackness such that at every profit level `π_i`:
(a) if `p_i < 1`, `1/v'(w(π_i)) = γ + μ [1 - f(π_i|e_L)/f(π_i|e_H)]`;
(b) if `p_i > 0`, `1/v'(w(π_i, y)) = γ + μ [1 - f(π_i, y|e_L)/f(π_i, y|e_H)]` for every `y`;
(c) if `p_i < 1`, not investigating is optimal: `A_i(w(π_i)) ≤ B_i(z)` for every wage schedule `z`
after investigation; (d) if `p_i > 0`, investigating is optimal: `B_i(w(π_i, ·)) ≤ A_i(x)` for
every wage `x`. -/
theorem exercise_14_B_8 {fq : ε → Fin n → Fin m → ℝ} {v dv : ℝ → ℝ} {g : ε → ℝ} {c ubar : ℝ}
    {eL eH : ε} (hv : ConcaveOn ℝ univ v) (hdv : ∀ x, HasDerivAt v (dv x) x)
    (hdvpos : ∀ x, 0 < dv x) (hfq : ∀ e i k, 0 < fq e i k)
    (hdiff : ∃ i, b8F fq eL i < b8F fq eH i) {p w0 : Fin n → ℝ} {w1 : Fin n → Fin m → ℝ}
    (hf : B8Feas fq v g ubar eL eH p w0 w1)
    (hopt : ∀ p' w0' w1', B8Feas fq v g ubar eL eH p' w0' w1' →
      b8Cost fq c eH p w0 w1 ≤ b8Cost fq c eH p' w0' w1') :
    ∃ γ μ : ℝ, 0 ≤ γ ∧ 0 ≤ μ ∧ γ * (b8EV fq v eH p w0 w1 - g eH - ubar) = 0 ∧
      μ * ((b8EV fq v eH p w0 w1 - g eH) - (b8EV fq v eL p w0 w1 - g eL)) = 0 ∧
      ∀ i, (p i < 1 → 1 / dv (w0 i) = γ + μ * (1 - b8F fq eL i / b8F fq eH i)) ∧
        (0 < p i → ∀ k, 1 / dv (w1 i k) = γ + μ * (1 - fq eL i k / fq eH i k)) ∧
        (p i < 1 → ∀ z, b8A fq v eL eH γ μ i (w0 i) ≤ b8B fq v c eL eH γ μ i z) ∧
        (0 < p i → ∀ x, b8B fq v c eL eH γ μ i (w1 i) ≤ b8A fq v eL eH γ μ i x) := by
  classical
  have hvm : StrictMono v := strictMono_of_hasDerivAt_pos hdv hdvpos
  have hvc : Continuous v := continuous_iff_continuousAt.2 fun x => (hdv x).continuousAt
  obtain ⟨id0, hid0⟩ := hdiff
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp [b8F] at hid0
    · exact h
  have hF : ∀ e i, 0 < b8F fq e i := fun e i =>
    sum_pos (fun k _ => hfq e i k) ⟨⟨0, hm⟩, mem_univ _⟩
  let X := {x : (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → Fin m → ℝ) // ∀ i, 0 ≤ x.1 i ∧ x.1 i ≤ 1}
  let EV : ε → X → ℝ := fun e x => b8EV fq v e x.1.1 x.1.2.1 x.1.2.2
  let J : X → ℝ := fun x => b8Cost fq c eH x.1.1 x.1.2.1 x.1.2.2
  let G : Fin 2 → X → ℝ := ![fun x => ubar - (EV eH x - g eH),
    fun x => (EV eL x - g eL) - (EV eH x - g eH)]
  have hG0 : ∀ x, G 0 x = ubar - (EV eH x - g eH) := fun x => rfl
  have hG1 : ∀ x, G 1 x = (EV eL x - g eL) - (EV eH x - g eH) := fun x => rfl
  let xs : X := ⟨(p, w0, w1), hf.1⟩
  -- the convex-like property
  have hconv : ∀ x0 x1 : X, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∃ x : X,
      J x ≤ (1 - t) * J x0 + t * J x1 ∧ ∀ e, EV e x = (1 - t) * EV e x0 + t * EV e x1 := by
    intro x0 x1 t ht0 ht1
    obtain ⟨⟨p0, a0, b0⟩, hp0⟩ := x0
    obtain ⟨⟨p1, a1, b1⟩, hp1⟩ := x1
    have hA : ∀ i, ∃ x, ((1 - t) * (1 - p0 i) + t * (1 - p1 i)) * v x =
        (1 - t) * (1 - p0 i) * v (a0 i) + t * (1 - p1 i) * v (a1 i) ∧
        ((1 - t) * (1 - p0 i) + t * (1 - p1 i)) * x ≤
          (1 - t) * (1 - p0 i) * a0 i + t * (1 - p1 i) * a1 i := fun i =>
      b8_persp hv hvc hvm (mul_nonneg (by linarith) (by linarith [(hp0 i).2]))
        (mul_nonneg ht0 (by linarith [(hp1 i).2])) _ _
    have hB : ∀ i k, ∃ x, ((1 - t) * p0 i + t * p1 i) * v x =
        (1 - t) * p0 i * v (b0 i k) + t * p1 i * v (b1 i k) ∧
        ((1 - t) * p0 i + t * p1 i) * x ≤ (1 - t) * p0 i * b0 i k + t * p1 i * b1 i k :=
      fun i k => b8_persp hv hvc hvm (mul_nonneg (by linarith) (hp0 i).1)
        (mul_nonneg ht0 (hp1 i).1) _ _
    choose a hav hac using hA
    choose b hbv hbc using hB
    have hpm : ∀ i, 0 ≤ (1 - t) * p0 i + t * p1 i ∧ (1 - t) * p0 i + t * p1 i ≤ 1 := fun i =>
      ⟨by nlinarith [(hp0 i).1, (hp1 i).1], by nlinarith [(hp0 i).2, (hp1 i).2]⟩
    refine ⟨⟨(fun i => (1 - t) * p0 i + t * p1 i, a, b), hpm⟩, ?_, fun e => ?_⟩
    · simp only [J, b8Cost]
      rw [mul_sum, mul_sum, ← sum_add_distrib]
      refine sum_le_sum fun i _ => ?_
      have e1 : 1 - ((1 - t) * p0 i + t * p1 i) = (1 - t) * (1 - p0 i) + t * (1 - p1 i) := by
        ring
      rw [e1]
      have h1 := mul_le_mul_of_nonneg_left (hac i) (hF eH i).le
      have h2 : ∑ k, fq eH i k * b i k * ((1 - t) * p0 i + t * p1 i) ≤
          ∑ k, fq eH i k * ((1 - t) * p0 i * b0 i k + t * p1 i * b1 i k) :=
        sum_le_sum fun k _ => by
          have := mul_le_mul_of_nonneg_left (hbc i k) (hfq eH i k).le
          linarith
      have h3 : ((1 - t) * p0 i + t * p1 i) * ∑ k, fq eH i k * b i k =
          ∑ k, fq eH i k * b i k * ((1 - t) * p0 i + t * p1 i) := by
        rw [mul_sum]; exact sum_congr rfl fun k _ => by ring
      have h4 : ∑ k, fq eH i k * ((1 - t) * p0 i * b0 i k + t * p1 i * b1 i k) =
          (1 - t) * p0 i * ∑ k, fq eH i k * b0 i k + t * p1 i * ∑ k, fq eH i k * b1 i k := by
        rw [mul_sum, mul_sum, ← sum_add_distrib]; exact sum_congr rfl fun k _ => by ring
      nlinarith
    · simp only [EV, b8EV]
      rw [mul_sum, mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun i _ => ?_
      have e1 : 1 - ((1 - t) * p0 i + t * p1 i) = (1 - t) * (1 - p0 i) + t * (1 - p1 i) := by
        ring
      rw [e1]
      have h1 : ((1 - t) * (1 - p0 i) + t * (1 - p1 i)) * b8F fq e i * v (a i) =
          b8F fq e i * (((1 - t) * (1 - p0 i) + t * (1 - p1 i)) * v (a i)) := by ring
      have h2 : ((1 - t) * p0 i + t * p1 i) * ∑ k, fq e i k * v (b i k) =
          ∑ k, fq e i k * (((1 - t) * p0 i + t * p1 i) * v (b i k)) := by
        rw [mul_sum]; exact sum_congr rfl fun k _ => by ring
      rw [h1, h2, hav i]
      simp only [hbv]
      have h3 : ∑ k, fq e i k * ((1 - t) * p0 i * v (b0 i k) + t * p1 i * v (b1 i k)) =
          (1 - t) * p0 i * ∑ k, fq e i k * v (b0 i k) + t * p1 i * ∑ k, fq e i k * v (b1 i k) := by
        rw [mul_sum, mul_sum, ← sum_add_distrib]; exact sum_congr rfl fun k _ => by ring
      rw [h3]
      ring
  -- Slater's condition
  have hslater : ∃ x : X, ∀ i, G i x < 0 := by
    have hG0s : ubar - (b8EV fq v eH p w0 w1 - g eH) ≤ 0 := by linarith [hf.2.1]
    have hG1s : (b8EV fq v eL p w0 w1 - g eL) - (b8EV fq v eH p w0 w1 - g eH) ≤ 0 := by
      linarith [hf.2.2]
    have hΔv : ∀ y, 0 < v (y + 1) - v y := fun y => sub_pos.2 (hvm (by linarith))
    by_cases hp1 : p id0 < 1
    · have hEV : ∀ e, b8EV fq v e p (Function.update w0 id0 (w0 id0 + 1)) w1 =
          b8EV fq v e p w0 w1 + (1 - p id0) * b8F fq e id0 * (v (w0 id0 + 1) - v (w0 id0)) := by
        intro e
        unfold b8EV
        rw [b8_upd (fun i => (1 - p i) * b8F fq e i * v (w0 i) + p i * ∑ k, fq e i k * v (w1 i k))
          (fun i => (1 - p i) * b8F fq e i * v (Function.update w0 id0 (w0 id0 + 1) i) +
            p i * ∑ k, fq e i k * v (w1 i k)) id0
          (fun i hi => by simp only [Function.update_of_ne hi])]
        simp only [Function.update_self]
        ring
      refine ⟨⟨(p, Function.update w0 id0 (w0 id0 + 1), w1), hf.1⟩, Fin.forall_fin_two.2 ⟨?_, ?_⟩⟩
      · rw [hG0]; simp only [EV]; rw [hEV]
        have := mul_pos (mul_pos (sub_pos.2 hp1) (hF eH id0)) (hΔv (w0 id0))
        linarith
      · rw [hG1]; simp only [EV]; rw [hEV, hEV]
        have := mul_pos (mul_pos (sub_pos.2 hp1) (sub_pos.2 hid0)) (hΔv (w0 id0))
        nlinarith
    · have hp1' : p id0 = 1 := le_antisymm (hf.1 id0).2 (not_lt.1 hp1)
      obtain ⟨k0, hk0⟩ : ∃ k, fq eL id0 k < fq eH id0 k := by
        by_contra hc
        push Not at hc
        have : b8F fq eH id0 ≤ b8F fq eL id0 := sum_le_sum fun k _ => hc k
        linarith
      set z := Function.update (w1 id0) k0 (w1 id0 k0 + 1)
      have hEV : ∀ e, b8EV fq v e p w0 (Function.update w1 id0 z) =
          b8EV fq v e p w0 w1 + p id0 * (fq e id0 k0 * (v (w1 id0 k0 + 1) - v (w1 id0 k0))) := by
        intro e
        unfold b8EV
        rw [b8_upd (fun i => (1 - p i) * b8F fq e i * v (w0 i) + p i * ∑ k, fq e i k * v (w1 i k))
          (fun i => (1 - p i) * b8F fq e i * v (w0 i) +
            p i * ∑ k, fq e i k * v (Function.update w1 id0 z i k)) id0
          (fun i hi => by simp only [Function.update_of_ne hi])]
        simp only [Function.update_self]
        rw [b8_upd (fun k => fq e id0 k * v (w1 id0 k)) (fun k => fq e id0 k * v (z k)) k0
          (fun k hk => by simp only [z, Function.update_of_ne hk])]
        simp only [z, Function.update_self]
        ring
      refine ⟨⟨(p, w0, Function.update w1 id0 z), hf.1⟩, Fin.forall_fin_two.2 ⟨?_, ?_⟩⟩
      · rw [hG0]; simp only [EV]; rw [hEV, hp1']
        have := mul_pos (hfq eH id0 k0) (hΔv (w1 id0 k0))
        linarith
      · rw [hG1]; simp only [EV]; rw [hEV, hEV, hp1']
        have := mul_pos (sub_pos.2 hk0) (hΔv (w1 id0 k0))
        nlinarith
  obtain ⟨lam, hlam, hcs, hlag⟩ := kt_convexlike J G xs
    (Fin.forall_fin_two.2 ⟨by rw [hG0]; simp only [EV, xs]; linarith [hf.2.1],
      by rw [hG1]; simp only [EV, xs]; linarith [hf.2.2]⟩)
    (fun x hx => hopt x.1.1 x.1.2.1 x.1.2.2 ⟨x.2, by linarith [hG0 x ▸ hx 0],
      by linarith [hG1 x ▸ hx 1]⟩)
    (fun x0 x1 t ht0 ht1 => by
      obtain ⟨x, hJ, hEVx⟩ := hconv x0 x1 t ht0 ht1
      refine ⟨x, hJ, Fin.forall_fin_two.2 ⟨?_, ?_⟩⟩
      · rw [hG0, hG0, hG0, hEVx]; apply le_of_eq; ring
      · rw [hG1, hG1, hG1, hEVx, hEVx]; apply le_of_eq; ring)
    hslater
  set γ := lam 0
  set μ := lam 1
  have hcs0 : γ * (ubar - (EV eH xs - g eH)) = 0 := hcs 0
  have hcs1 : μ * ((EV eL xs - g eL) - (EV eH xs - g eH)) = 0 := hcs 1
  -- the Lagrangian is minimized at the optimum
  let ℓ : Fin n → ℝ → ℝ → (Fin m → ℝ) → ℝ := fun i q x z =>
    (1 - q) * b8A fq v eL eH γ μ i x + q * b8B fq v c eL eH γ μ i z
  have hsep : ∀ x : X, ∑ i, ℓ i (p i) (w0 i) (w1 i) ≤
      ∑ i, ℓ i (x.1.1 i) (x.1.2.1 i) (x.1.2.2 i) := by
    intro x
    have h1 := hlag x
    rw [Fin.sum_univ_two, hG0, hG1] at h1
    have l1 := b8_lag fq v c eL eH γ μ p w0 w1
    have l2 := b8_lag fq v c eL eH γ μ x.1.1 x.1.2.1 x.1.2.2
    simp only [ℓ]
    rw [← l1, ← l2]
    simp only [J, EV, xs] at h1 hcs0 hcs1
    nlinarith
  have hloc : ∀ i0 q x z, 0 ≤ q → q ≤ 1 → ℓ i0 (p i0) (w0 i0) (w1 i0) ≤ ℓ i0 q x z := by
    intro i0 q x z hq0 hq1
    have hX : ∀ j, 0 ≤ Function.update p i0 q j ∧ Function.update p i0 q j ≤ 1 := by
      intro j
      by_cases hj : j = i0
      · subst hj; simp only [Function.update_self]; exact ⟨hq0, hq1⟩
      · simp only [Function.update_of_ne hj]; exact hf.1 j
    have h := hsep ⟨(Function.update p i0 q, Function.update w0 i0 x, Function.update w1 i0 z), hX⟩
    simp only at h
    rw [b8_upd (fun i => ℓ i (p i) (w0 i) (w1 i)) (fun i => ℓ i (Function.update p i0 q i)
      (Function.update w0 i0 x i) (Function.update w1 i0 z i)) i0
      (fun i hi => by simp only [Function.update_of_ne hi])] at h
    simp only [Function.update_self] at h
    linarith
  refine ⟨γ, μ, hlam 0, hlam 1, ?_, ?_, fun i => ⟨fun hp => ?_, fun hp k => ?_, fun hp z => ?_,
    fun hp x => ?_⟩⟩
  · simp only [EV, xs] at hcs0; linear_combination -hcs0
  · simp only [EV, xs] at hcs1; linear_combination -hcs1
  · -- first-order condition without investigation
    have hmin : ∀ x, b8F fq eH i * w0 i - ((γ + μ) * b8F fq eH i - μ * b8F fq eL i) * v (w0 i) ≤
        b8F fq eH i * x - ((γ + μ) * b8F fq eH i - μ * b8F fq eL i) * v x := by
      intro x
      have h := hloc i (p i) x (w1 i) (hf.1 i).1 (hf.1 i).2
      simp only [ℓ, b8A] at h
      have h' : (1 - p i) * (b8F fq eH i * w0 i - (γ + μ) * (b8F fq eH i * v (w0 i)) +
          μ * (b8F fq eL i * v (w0 i))) ≤ (1 - p i) * (b8F fq eH i * x -
          (γ + μ) * (b8F fq eH i * v x) + μ * (b8F fq eL i * v x)) := by linarith
      have := le_of_mul_le_mul_left h' (sub_pos.2 hp)
      linarith
    rw [b8_foc hdv hdvpos (hF eH i) hmin]
    have := (hF eH i).ne'
    field_simp
    ring
  · -- first-order condition after investigation
    have hmin : ∀ y, fq eH i k * w1 i k - ((γ + μ) * fq eH i k - μ * fq eL i k) * v (w1 i k) ≤
        fq eH i k * y - ((γ + μ) * fq eH i k - μ * fq eL i k) * v y := by
      intro y
      have h := hloc i (p i) (w0 i) (Function.update (w1 i) k y) (hf.1 i).1 (hf.1 i).2
      simp only [ℓ, b8B] at h
      rw [b8_upd (fun k => fq eH i k * w1 i k - (γ + μ) * (fq eH i k * v (w1 i k)) +
          μ * (fq eL i k * v (w1 i k)))
        (fun k' => fq eH i k' * Function.update (w1 i) k y k' -
          (γ + μ) * (fq eH i k' * v (Function.update (w1 i) k y k')) +
          μ * (fq eL i k' * v (Function.update (w1 i) k y k'))) k
        (fun k' hk => by simp only [Function.update_of_ne hk])] at h
      simp only [Function.update_self] at h
      have h' : p i * (fq eH i k * w1 i k - (γ + μ) * (fq eH i k * v (w1 i k)) +
          μ * (fq eL i k * v (w1 i k))) ≤ p i * (fq eH i k * y - (γ + μ) * (fq eH i k * v y) +
          μ * (fq eL i k * v y)) := by linarith
      have := le_of_mul_le_mul_left h' hp
      linarith
    rw [b8_foc hdv hdvpos (hfq eH i k) hmin]
    have := (hfq eH i k).ne'
    field_simp
    ring
  · -- not investigating is optimal
    have h1 := hloc i 1 (w0 i) z zero_le_one le_rfl
    have h2 := hloc i 1 (w0 i) (w1 i) zero_le_one le_rfl
    simp only [ℓ] at h1 h2
    rcases (hf.1 i).1.lt_or_eq with hp0 | hp0
    · have : b8A fq v eL eH γ μ i (w0 i) ≤ b8B fq v c eL eH γ μ i (w1 i) := by
        have h3 : (1 - p i) * b8A fq v eL eH γ μ i (w0 i) ≤
            (1 - p i) * b8B fq v c eL eH γ μ i (w1 i) := by linarith
        exact le_of_mul_le_mul_left h3 (sub_pos.2 hp)
      nlinarith
    · rw [← hp0] at h1; linarith
  · -- investigating is optimal
    have h1 := hloc i 0 x (w1 i) le_rfl zero_le_one
    have h2 := hloc i 0 (w0 i) (w1 i) le_rfl zero_le_one
    simp only [ℓ] at h1 h2
    rcases (hf.1 i).2.lt_or_eq with hp1 | hp1
    · have : b8B fq v c eL eH γ μ i (w1 i) ≤ b8A fq v eL eH γ μ i (w0 i) := by
        have h3 : p i * b8B fq v c eL eH γ μ i (w1 i) ≤ p i * b8A fq v eL eH γ μ i (w0 i) := by
          linarith
        exact le_of_mul_le_mul_left h3 hp
      nlinarith
    · rw [hp1] at h1; linarith

/-- The exponential bound for the instance: if `K e^{-w*} = F`, then
`F x + K e^{-x} ≥ F w* + K e^{-w*}` (`e^t ≥ 1 + t`). -/
theorem b8_exp_bound {F K x ws : ℝ} (hK : 0 ≤ K) (hws : K * Real.exp (-ws) = F) :
    F * ws + K * Real.exp (-ws) ≤ F * x + K * Real.exp (-x) := by
  have h1 := Real.add_one_le_exp (-(x - ws))
  have h2 : Real.exp (-x) = Real.exp (-ws) * Real.exp (-(x - ws)) := by
    rw [← Real.exp_add]; ring_nf
  have h3 : K * Real.exp (-ws) * (-(x - ws) + 1) ≤ K * Real.exp (-ws) * Real.exp (-(x - ws)) :=
    mul_le_mul_of_nonneg_left h1 (mul_nonneg hK (Real.exp_pos _).le)
  rw [h2, ← mul_assoc]
  rw [hws] at h3 ⊢
  nlinarith

/-- The joint distribution of the instance: profits as in Figure 14.B.1 (`b7f`) and an
independent, uninformative signal taking two values with probability `1/2` each. -/
noncomputable def b8fq (e : Bool) (i : Fin 3) (_k : Fin 2) : ℝ := b7f e i / 2

/-- **Exercise 14.B.8, an instance** (MWG, p. 508). With an uninformative signal, investigation
cost `c ≥ 0`, `v(w) = -exp(-w)`, `g(e_H) = 3/20`, `g(e_L) = 0` and `ū = -29/40`, never
investigating and paying the scheme `(0, log (5/2), log 2)` of Figure 14.B.1 is optimal (a
Lagrangian certificate with `γ = 2`, `μ = 1`), and `exercise_14_B_8` applies to it. -/
theorem exercise_14_B_8_instance {c : ℝ} (hc : 0 ≤ c) :
    B8Feas b8fq (fun w => -Real.exp (-w)) (fun b => if b then 3 / 20 else 0) (-29 / 40) false
      true (fun _ => 0) b7w (fun _ _ => 0) ∧
    (∀ p' w0' w1', B8Feas b8fq (fun w => -Real.exp (-w)) (fun b => if b then 3 / 20 else 0)
      (-29 / 40) false true p' w0' w1' →
      b8Cost b8fq c true (fun _ => 0) b7w (fun _ _ => 0) ≤ b8Cost b8fq c true p' w0' w1') := by
  have hF : ∀ e i, b8F b8fq e i = b7f e i := fun e i => by
    simp only [b8F, b8fq, Fin.sum_univ_two]; ring
  have e1 : Real.exp (-Real.log (5 / 2)) = 2 / 5 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have e2 : Real.exp (-Real.log 2) = 1 / 2 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have hEV : ∀ e, b8EV b8fq (fun w => -Real.exp (-w)) e (fun _ => 0) b7w (fun _ _ => 0) =
      ∑ i, b7f e i * -Real.exp (-b7w i) := fun e => by
    simp only [b8EV, hF, sub_zero, one_mul, zero_mul, add_zero]
  have hEVL : ∑ i, b7f false i * -Real.exp (-b7w i) = -29 / 40 := by
    simp [b7f, b7w, Fin.sum_univ_three, e1, e2]; norm_num
  have hEVH : ∑ i, b7f true i * -Real.exp (-b7w i) = -23 / 40 := by
    simp [b7f, b7w, Fin.sum_univ_three, e1, e2]; norm_num
  have hfeas : B8Feas b8fq (fun w => -Real.exp (-w)) (fun b => if b then 3 / 20 else 0)
      (-29 / 40) false true (fun _ => 0) b7w (fun _ _ => 0) := by
    refine ⟨fun _ => ⟨le_rfl, zero_le_one⟩, ?_, ?_⟩ <;> simp only [hEV, hEVL, hEVH] <;> norm_num
  refine ⟨hfeas, fun p' w0' w1' hf' => ?_⟩
  -- the pointwise bound `A_i(x) ≥ A_i(w*_i)`
  have hA : ∀ i x, b8A b8fq (fun w => -Real.exp (-w)) false true 2 1 i (b7w i) ≤
      b8A b8fq (fun w => -Real.exp (-w)) false true 2 1 i x := by
    intro i x
    have hform : ∀ y, b8A b8fq (fun w => -Real.exp (-w)) false true 2 1 i y =
        b7f true i * y + (3 * b7f true i - b7f false i) * Real.exp (-y) := fun y => by
      simp only [b8A, hF]; ring
    rw [hform, hform]
    refine b8_exp_bound ?_ ?_
    · fin_cases i <;> simp [b7f] <;> norm_num
    · fin_cases i <;> simp [b7f, b7w, e1, e2] <;> norm_num
  have hB : ∀ i z, b8A b8fq (fun w => -Real.exp (-w)) false true 2 1 i (b7w i) ≤
      b8B b8fq (fun w => -Real.exp (-w)) c false true 2 1 i z := by
    intro i z
    have hform : b8B b8fq (fun w => -Real.exp (-w)) c false true 2 1 i z =
        (b8A b8fq (fun w => -Real.exp (-w)) false true 2 1 i (z 0) +
          b8A b8fq (fun w => -Real.exp (-w)) false true 2 1 i (z 1)) / 2 +
          c * b8F b8fq true i := by
      simp only [b8B, b8A, hF, b8fq, Fin.sum_univ_two]; ring
    rw [hform]
    have := hA i (z 0)
    have := hA i (z 1)
    have : 0 ≤ c * b8F b8fq true i := mul_nonneg hc (by rw [hF]; fin_cases i <;> norm_num [b7f])
    linarith
  have hl' := b8_lag b8fq (fun w => -Real.exp (-w)) c false true 2 1 p' w0' w1'
  have hl0 := b8_lag b8fq (fun w => -Real.exp (-w)) c false true 2 1 (fun _ => 0) b7w
    (fun _ _ => 0)
  have hsum : ∑ i, ((1 - (fun _ => (0 : ℝ)) i) *
      b8A b8fq (fun w => -Real.exp (-w)) false true 2 1 i (b7w i) +
      (fun _ => (0 : ℝ)) i * b8B b8fq (fun w => -Real.exp (-w)) c false true 2 1 i
        ((fun _ _ => (0 : ℝ)) i)) ≤
      ∑ i, ((1 - p' i) * b8A b8fq (fun w => -Real.exp (-w)) false true 2 1 i (w0' i) +
        p' i * b8B b8fq (fun w => -Real.exp (-w)) c false true 2 1 i (w1' i)) := by
    refine sum_le_sum fun i _ => ?_
    have h1 := hA i (w0' i)
    have h2 := hB i (w1' i)
    have hp0 := (hf'.1 i).1
    have hp1 := (hf'.1 i).2
    simp only [sub_zero, one_mul, zero_mul, add_zero]
    nlinarith
  rw [← hl', ← hl0, hEV, hEV, hEVL, hEVH] at hsum
  obtain ⟨_, hIR, hIC⟩ := hf'
  simp only [Bool.false_eq_true, ↓reduceIte] at hIR hIC
  nlinarith

/-- **Exercise 14.B.8, the theorem applied to the instance**: the multipliers exist and the
characterization holds for the contract of `exercise_14_B_8_instance` (with `c = 1/10`). -/
theorem exercise_14_B_8_instance_applied :
    ∃ γ μ : ℝ, 0 ≤ γ ∧ 0 ≤ μ ∧ ∀ i, ((fun _ => (0 : ℝ)) i < 1 → 1 / Real.exp (-b7w i) =
      γ + μ * (1 - b8F b8fq false i / b8F b8fq true i)) := by
  obtain ⟨hf, hopt⟩ := exercise_14_B_8_instance (c := 1 / 10) (by norm_num)
  have hF : ∀ e i, b8F b8fq e i = b7f e i := fun e i => by
    simp only [b8F, b8fq, Fin.sum_univ_two]; ring
  obtain ⟨γ, μ, hγ, hμ, -, -, h⟩ := exercise_14_B_8 (c := 1 / 10) exA_strictConcave.concaveOn
    exA_hasDeriv (fun _ => Real.exp_pos _)
    (fun e i k => by unfold b8fq; cases e <;> fin_cases i <;> norm_num [b7f])
    ⟨1, by rw [hF, hF]; norm_num [b7f]⟩ hf hopt
  exact ⟨γ, μ, hγ, hμ, fun i => (h i).1⟩

end MWG.PrincipalAgent
