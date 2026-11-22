/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPrincipalAgent.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Fin

/-!
# Exercises 14.B.5 and 14.B.6

MWG, p. 508. Both exercises are formalized with finitely many profit (revenue) levels
`a 0 < a 1 < ⋯` (MWG, footnote 6); a scheme is `w : Fin n → ℝ`.

* Exercise 14.B.5: the manager can unobservably reduce profits. Facing `w`, he effectively
  receives `ŵ(i) = max_{j ≤ i} w(j)` (`effw`). `exercise_14_B_5`: `ŵ` is nondecreasing, gives the
  manager the same expected utility under every effort as `w` (so it implements the same effort),
  needs no disposal, and gives the owner at least as much as `w` with any optimal disposal: there is
  always an optimal scheme that is nondecreasing in observed profits.
* Exercise 14.B.6: revenue `R` and cost `C` independent given effort. (a) `exercise_14_B_6a`: under
  the monotone likelihood ratio property, a scheme satisfying the first-order condition for
  implementing `e_C` is nonincreasing in both `R` and `C`. (b) `exercise_14_B_6b`: if the manager
  can
  reduce revenues, such a scheme is effectively independent of `R`. (c) `exercise_14_B_6c`: if pay
  can depend only on revenues (and revenues can be reduced), `e_C` cannot be implemented
  (`mlrp_expect_mono`: a nondecreasing function has a higher expectation under `e_R`).
-/

namespace MWG.PrincipalAgent

open Finset

/-- The effective payment `max_{j ≤ i} w(j)` when the manager can reduce observed profits. -/
noncomputable def effw {n : ℕ} (w : Fin n → ℝ) (i : Fin n) : ℝ :=
  (univ.filter (· ≤ i)).sup' (show (univ.filter (· ≤ i)).Nonempty from ⟨i, by simp⟩) w

theorem effw_ge {n : ℕ} (w : Fin n → ℝ) (i : Fin n) : w i ≤ effw w i :=
  le_sup' w (by simp)

theorem effw_le_iff {n : ℕ} (w : Fin n → ℝ) (i : Fin n) (c : ℝ) :
    effw w i ≤ c ↔ ∀ j, j ≤ i → w j ≤ c := by
  unfold effw
  rw [Finset.sup'_le_iff]
  simp

theorem effw_exists {n : ℕ} (w : Fin n → ℝ) (i : Fin n) : ∃ j, j ≤ i ∧ w j = effw w i := by
  obtain ⟨j, hj, h⟩ := exists_mem_eq_sup' (s := univ.filter (· ≤ i)) ⟨i, by simp⟩ w
  exact ⟨j, by simpa using hj, h.symm⟩

/-- The effective scheme is nondecreasing. -/
theorem effw_mono {n : ℕ} (w : Fin n → ℝ) : Monotone (effw w) := by
  intro i i' hii
  rw [effw_le_iff]
  intro j hj
  exact le_sup' w (by simp [hj.trans hii])

/-- A nondecreasing scheme is its own effective scheme. -/
theorem effw_of_mono {n : ℕ} {w : Fin n → ℝ} (hw : Monotone w) : effw w = w := by
  funext i
  exact le_antisymm ((effw_le_iff w i _).2 fun j hj => hw hj) (effw_ge w i)

/-- The effective scheme of the effective scheme is itself. -/
theorem effw_idem {n : ℕ} (w : Fin n → ℝ) : effw (effw w) = effw w :=
  effw_of_mono (effw_mono w)

/-- An optimal disposal rule for `w`: from profit level `i` report `d i ≤ i` with the highest
pay. -/
def IsDisp {n : ℕ} (w : Fin n → ℝ) (d : Fin n → Fin n) : Prop :=
  ∀ i, d i ≤ i ∧ w (d i) = effw w i

/-- **Exercise 14.B.5** (MWG, p. 508). Let profit levels `a` be increasing, effort `e` give
profit level `i` with probability `q e i ≥ 0`, and let the manager have utility
`Σᵢ q e i v(pay) - g e`. For any scheme `w` and any optimal disposal rule `d` for `w`, the
nondecreasing scheme `ŵ = effw w`: (i) gives the manager the same expected utility under every
effort (so implements the same effort and meets the same participation constraint); (ii) makes not
disposing optimal; (iii) gives the owner at least as much as `w` with disposal `d`. -/
theorem exercise_14_B_5 {n : ℕ} {E : Type*} (a : Fin n → ℝ) (ha : Monotone a)
    (q : E → Fin n → ℝ) (hq : ∀ e i, 0 ≤ q e i) (v : ℝ → ℝ) (g : E → ℝ) (w : Fin n → ℝ)
    (d : Fin n → Fin n) (hd : IsDisp w d) :
    Monotone (effw w) ∧
      (∀ e, ∑ i, q e i * v (effw (effw w) i) - g e = ∑ i, q e i * v (effw w i) - g e) ∧
      IsDisp (effw w) id ∧
      ∀ e, ∑ i, q e i * (a (d i) - w (d i)) ≤ ∑ i, q e i * (a i - effw w i) := by
  refine ⟨effw_mono w, fun e => by rw [effw_idem], fun i => ⟨le_rfl, by rw [effw_idem]; rfl⟩,
    fun e => ?_⟩
  refine sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (hq e i)
  rw [(hd i).2]
  linarith [ha (hd i).1]

/-- **Exercise 14.B.6(a)** (MWG, p. 508). With `R` and `C` independent given effort, the likelihood
ratio for implementing `e_C` against `e_R` is `ℓ_R(R) ℓ_C(C)` with
`ℓ_R = f_R(·|e_R)/f_R(·|e_C)` and `ℓ_C = f_C(·|e_R)/f_C(·|e_C)` positive and (MLRP) nondecreasing.
A scheme satisfying `1 / v'(w(R, C)) = γ + μ [1 - ℓ_R(R) ℓ_C(C)]` with `μ > 0` and `v'` strictly
decreasing is nonincreasing in `R` and in `C`. -/
theorem exercise_14_B_6a {dv : ℝ → ℝ} (hda : StrictAnti dv) (hdv : ∀ w, 0 < dv w)
    {lR lC : ℝ → ℝ} (hR : Monotone lR) (hC : Monotone lC) (hR0 : ∀ r, 0 < lR r)
    (hC0 : ∀ c, 0 < lC c) {w : ℝ → ℝ → ℝ} {γ μ : ℝ} (hμ : 0 < μ)
    (hfoc : ∀ r c, 1 / dv (w r c) = γ + μ * (1 - lR r * lC c)) :
    (∀ c, Antitone fun r => w r c) ∧ ∀ r, Antitone fun c => w r c := by
  have key : ∀ r c r' c', lR r * lC c ≤ lR r' * lC c' → w r' c' ≤ w r c := by
    intro r c r' c' h
    have h1 : 1 / dv (w r' c') ≤ 1 / dv (w r c) := by
      rw [hfoc, hfoc]; nlinarith
    rw [one_div_le_one_div (hdv _) (hdv _)] at h1
    exact hda.le_iff_ge.1 h1
  refine ⟨fun c r r' hrr => key r c r' c ?_, fun r c c' hcc => key r c r c' ?_⟩
  · exact mul_le_mul_of_nonneg_right (hR hrr) (hC0 c).le
  · exact mul_le_mul_of_nonneg_left (hC hcc) (hR0 r).le

/-- **Exercise 14.B.6(b)** (MWG, p. 508). If the manager can reduce revenues, a scheme that is
nonincreasing in the revenue level (as in part (a)) pays effectively the same at every revenue
level: `ŵ(R, C) = w(R_min, C)`. -/
theorem exercise_14_B_6b {n : ℕ} (w : Fin (n + 1) → ℝ) (hw : Antitone w) (i : Fin (n + 1)) :
    effw w i = w 0 := by
  refine le_antisymm ((effw_le_iff w i _).2 fun j _ => hw (Fin.zero_le j)) ?_
  exact (le_sup' w (by simp : (0 : Fin (n + 1)) ∈ univ.filter (· ≤ i)))

/-- **Monotone likelihood ratio and expectations** (used in Exercise 14.B.6(c)). If `q₁, q₀` are
positive probability vectors with `q₁ i / q₀ i` nondecreasing in `i`, every nondecreasing `φ` has
`Σ q₀ φ ≤ Σ q₁ φ`. -/
theorem mlrp_expect_mono {n : ℕ} {q1 q0 φ : Fin n → ℝ} (h1 : ∀ i, 0 < q1 i) (h0 : ∀ i, 0 < q0 i)
    (hs : ∑ i, q1 i = ∑ i, q0 i) (hl : Monotone fun i => q1 i / q0 i) (hφ : Monotone φ) :
    ∑ i, q0 i * φ i ≤ ∑ i, q1 i * φ i := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  -- a threshold index
  have hne : (univ.filter fun i : Fin n => 1 ≤ q1 i / q0 i).Nonempty := by
    by_contra hc
    rw [not_nonempty_iff_eq_empty, filter_eq_empty_iff] at hc
    have : ∑ i, q1 i < ∑ i, q0 i := by
      refine sum_lt_sum_of_nonempty ⟨⟨0, hn⟩, mem_univ _⟩ fun i _ => ?_
      have := hc (mem_univ i)
      rw [not_le, div_lt_one (h0 i)] at this; exact this
    linarith
  set i0 := (univ.filter fun i : Fin n => 1 ≤ q1 i / q0 i).min' hne
  have hi0 : 1 ≤ q1 i0 / q0 i0 := (mem_filter.1 (min'_mem _ hne)).2
  set κ := φ i0
  have hterm : ∀ i, 0 ≤ (q1 i - q0 i) * (φ i - κ) := by
    intro i
    rcases le_or_gt i0 i with h | h
    · have hl' : 1 ≤ q1 i / q0 i := hi0.trans (hl h)
      rw [le_div_iff₀ (h0 i), one_mul] at hl'
      exact mul_nonneg (by linarith) (by linarith [hφ h])
    · have hl' : q1 i / q0 i < 1 := by
        by_contra hc
        have hmem : i ∈ univ.filter (fun i : Fin n => 1 ≤ q1 i / q0 i) :=
          mem_filter.2 ⟨mem_univ i, le_of_not_gt hc⟩
        have := min'_le _ i hmem
        exact absurd h (not_lt_of_ge this)
      rw [div_lt_one (h0 i)] at hl'
      exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith [hφ h.le])
  have hsum := sum_nonneg fun i (_ : i ∈ univ) => hterm i
  have : ∑ i, (q1 i - q0 i) * (φ i - κ) = ∑ i, q1 i * φ i - ∑ i, q0 i * φ i -
      κ * (∑ i, q1 i - ∑ i, q0 i) := by
    rw [mul_sub, ← sum_sub_distrib, mul_sum, mul_sum, ← sum_sub_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun i _ => by ring
  rw [this, hs, sub_self, mul_zero, sub_zero] at hsum
  linarith

/-- **Exercise 14.B.6(c)** (MWG, p. 508). If pay can depend only on revenues and the manager can
reduce revenues, the effective scheme is nondecreasing in revenue; under the monotone likelihood
ratio property for revenues the manager's expected utility of income is then at least as high
under `e_R` as under `e_C`, and since `g(e_C) > g(e_R)` he strictly prefers `e_R`: `e_C` cannot be
implemented. -/
theorem exercise_14_B_6c {n : ℕ} {qR qC : Fin n → ℝ} (hR : ∀ i, 0 < qR i) (hC : ∀ i, 0 < qC i)
    (hs : ∑ i, qR i = ∑ i, qC i) (hl : Monotone fun i => qR i / qC i) {v : ℝ → ℝ}
    (hv : Monotone v) {gR gC : ℝ} (hg : gR < gC) (w : Fin n → ℝ) :
    ∑ i, qC i * v (effw w i) - gC < ∑ i, qR i * v (effw w i) - gR := by
  have := mlrp_expect_mono hR hC hs hl (hv.comp (effw_mono w))
  simp only [Function.comp] at this
  linarith

end MWG.PrincipalAgent
