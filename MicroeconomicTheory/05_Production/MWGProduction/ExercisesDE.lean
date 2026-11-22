/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGProduction.Geometry

/-!
# Exercises 5.D.4, 5.D.5 and 5.E.5 (MWG, pp. 163-164)

* **Exercise 5.D.4(a)**: with one output, decreasing average cost implies subadditivity.
* **Exercise 5.D.5(b)-(c)**: with a representative consumer `u(q) - z`, an interior optimum has
  `u'(q̄) = 1/f'(z̄)` (marginal utility equals marginal cost), and this condition is not
  sufficient under increasing returns.
* **Exercise 5.E.5** (Weitzman): with `AC_j(q_j) = α + β_j q_j`, (a) if all `β_j > 0` output is
  allocated in proportion to `1/β_j`; (b) if all `β_j < 0` it is concentrated in the plant with
  the most negative `β_j`; (c) in general a cost-minimizing allocation uses at most one plant with
  `β_j < 0`.
-/

namespace MWG.Production

open MWG.ClassicalDemand MWG.ConsumerChoice Filter Topology

/-- **Exercise 5.D.4(a)** (MWG, p. 163). With one output, if average cost `C(q)/q` is nonincreasing
on `q > 0` and `C(0) ≥ 0`, then `C` is subadditive: splitting `q = Σ_j q_j` among `J` firms never
lowers total cost. -/
theorem exercise_5_D_4a {J : ℕ} (hJ : 0 < J) {C : ℝ → ℝ} (h0 : 0 ≤ C 0)
    (hdec : ∀ q q', 0 < q → q ≤ q' → C q' / q' ≤ C q / q) (qs : Fin J → ℝ) (hqs : 0 ≤ qs) :
    C (∑ j, qs j) ≤ ∑ j, C (qs j) := by
  set Q := ∑ j, qs j with hQ
  rcases (Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => hqs j).lt_or_eq with hpos | hzero
  · have hQ0 : 0 < Q := hpos
    have hle : ∀ j, C Q / Q * qs j ≤ C (qs j) := by
      intro j
      rcases (hqs j).lt_or_eq with hj | hj
      · have hjQ : qs j ≤ Q := Finset.single_le_sum (fun i _ => hqs i) (Finset.mem_univ j)
        have := hdec (qs j) Q hj hjQ
        rw [div_le_div_iff₀ hQ0 hj] at this
        rw [div_mul_eq_mul_div, div_le_iff₀ hQ0]
        linarith
      · have hj' : qs j = 0 := hj.symm
        rw [hj', mul_zero]; exact h0
    calc C Q = C Q / Q * Q := by rw [div_mul_cancel₀ _ hQ0.ne']
      _ = ∑ j, C Q / Q * qs j := by rw [hQ, Finset.mul_sum]
      _ ≤ ∑ j, C (qs j) := Finset.sum_le_sum fun j _ => hle j
  · have hall : ∀ j, qs j = 0 := fun j =>
      (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hqs i).mp hzero.symm j (Finset.mem_univ j)
    have hQz : Q = 0 := hzero.symm
    rw [hQz]
    have : ∑ j, C (qs j) = J * C 0 := by simp [hall]
    rw [this]
    have : (1 : ℝ) ≤ J := by exact_mod_cast hJ
    nlinarith

/-- **Exercise 5.D.5(b)** (MWG, p. 163). With a representative consumer `u(q) - z` and
`q = f(z)`, an interior maximizer `z̄` of `u(f(z)) - z` satisfies `u'(f(z̄)) f'(z̄) = 1`: marginal
utility equals marginal cost `1/f'(z̄)` (the inverse function `C = f⁻¹` has `C'(q̄) = 1/f'(z̄)`). -/
theorem exercise_5_D_5b {u f : ℝ → ℝ} {z mu mf : ℝ} (hu : HasDerivAt u mu (f z))
    (hf : HasDerivAt f mf z) (hmax : IsLocalMax (fun t => u (f t) - t) z) :
    mu * mf = 1 ∧ (mf ≠ 0 → mu = 1 / mf) := by
  have hd : HasDerivAt (fun t => u (f t) - t) (mu * mf - 1) z :=
    (hu.comp z hf).sub (hasDerivAt_id z)
  have h := hmax.hasDerivAt_eq_zero hd
  refine ⟨by linarith, fun hne => ?_⟩
  field_simp
  linarith

/-- **Exercise 5.D.5(c)** (MWG, p. 163). "MU = MC is sufficient" is wrong under increasing returns:
for `f(z) = z²` and `u(q) = q/2`, at `z̄ = 1` marginal utility `1/2` equals marginal cost
`(√q)' = 1/2`, but `u(f(z)) - z = z²/2 - z` is larger at `z = 4` (it is unbounded). -/
theorem exercise_5_D_5c :
    HasDerivAt (fun q : ℝ => q / 2) (1 / 2) 1 ∧ HasDerivAt Real.sqrt (1 / 2) 1 ∧
      (fun z : ℝ => z ^ 2 / 2 - z) 1 < (fun z : ℝ => z ^ 2 / 2 - z) 4 := by
  refine ⟨?_, ?_, by norm_num⟩
  · simpa using (hasDerivAt_id (1 : ℝ)).div_const 2
  · have := Real.hasDerivAt_sqrt (x := 1) one_ne_zero
    simpa using this

/-- **Exercise 5.E.5(a)** (MWG, p. 164). With `C_j(q_j) = αq_j + β_jq_j²` and all `β_j > 0`, the
allocation `q_j = (q/β_j)/Σ_k(1/β_k)` (equal marginal costs) minimizes total cost among all
allocations of `q` with `q_j ≥ 0`. -/
theorem exercise_5_E_5a {J : ℕ} {α q : ℝ} {β : Fin J → ℝ} (hβ : ∀ j, 0 < β j)
    (hJ : 0 < J) (qs : Fin J → ℝ) (hsum : ∑ j, qs j = q) :
    let B := ∑ k, 1 / β k
    ∑ j, (α * (q / β j / B) + β j * (q / β j / B) ^ 2) ≤ ∑ j, (α * qs j + β j * qs j ^ 2) := by
  intro B
  have hB : 0 < B := Finset.sum_pos (fun k _ => by have := hβ k; positivity)
    ⟨⟨0, hJ⟩, Finset.mem_univ _⟩
  -- tangent inequality with the common marginal cost `μ = α + 2q/B`
  have key : ∀ j, α * (q / β j / B) + β j * (q / β j / B) ^ 2 + (α + 2 * q / B) *
      (qs j - q / β j / B) ≤ α * qs j + β j * qs j ^ 2 := by
    intro j
    have hb := hβ j
    have hsq : β j * (qs j - q / β j / B) ^ 2 ≥ 0 := by positivity
    have e : β j * (q / β j / B) = q / B := by field_simp
    have e2 : 2 * q / B = 2 * (β j * (q / β j / B)) := by rw [e]; ring
    have : α * (q / β j / B) + β j * (q / β j / B) ^ 2 + (α + 2 * q / B) * (qs j - q / β j / B) =
        α * qs j + β j * qs j ^ 2 - β j * (qs j - q / β j / B) ^ 2 := by rw [e2]; ring
    linarith
  have hsum2 : ∑ j, (qs j - q / β j / B) = 0 := by
    rw [Finset.sum_sub_distrib, hsum]
    have : ∑ j, q / β j / B = q / B * B := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [this, div_mul_cancel₀ _ hB.ne', sub_self]
  calc ∑ j, (α * (q / β j / B) + β j * (q / β j / B) ^ 2)
      = ∑ j, (α * (q / β j / B) + β j * (q / β j / B) ^ 2 + (α + 2 * q / B) *
          (qs j - q / β j / B)) := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hsum2, mul_zero, add_zero]
    _ ≤ _ := Finset.sum_le_sum fun j _ => key j

/-- **Exercise 5.E.5(b)** (MWG, p. 164). With all `β_j < 0` (concave costs), producing all of
`q ≥ 0` in a plant `j*` with the most negative `β_{j*}` minimizes total cost. -/
theorem exercise_5_E_5b {J : ℕ} {α q : ℝ} {β : Fin J → ℝ} (hβ : ∀ j, β j < 0) {js : Fin J}
    (hmin : ∀ j, β js ≤ β j) (qs : Fin J → ℝ) (hqs : 0 ≤ qs) (hsum : ∑ j, qs j = q) :
    α * q + β js * q ^ 2 ≤ ∑ j, (α * qs j + β j * qs j ^ 2) := by
  have h1 : ∑ j, β js * qs j ^ 2 ≤ ∑ j, β j * qs j ^ 2 :=
    Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hmin j) (sq_nonneg _)
  have h2 : ∑ j, qs j ^ 2 ≤ q ^ 2 := by
    rw [← hsum, sq, Finset.sum_mul]
    exact Finset.sum_le_sum fun j _ => by
      rw [sq]
      exact mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun i _ => hqs i)
        (Finset.mem_univ j)) (hqs j)
  have h3 : β js * q ^ 2 ≤ β js * ∑ j, qs j ^ 2 :=
    mul_le_mul_of_nonpos_left h2 (hβ js).le
  rw [← Finset.mul_sum] at h1
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsum]
  linarith

/-- **Exercise 5.E.5(c)** (MWG, p. 164). In general, a cost-minimizing allocation never uses two
plants with `β_i, β_k < 0`: moving both outputs to the plant with the smaller `β` strictly lowers
cost. -/
theorem exercise_5_E_5c {α βi βk qi qk : ℝ} (hi : βi < 0) (hle : βi ≤ βk)
    (hqi : 0 < qi) (hqk : 0 < qk) :
    α * (qi + qk) + βi * (qi + qk) ^ 2 < (α * qi + βi * qi ^ 2) + (α * qk + βk * qk ^ 2) := by
  have : βi * qk ^ 2 ≤ βk * qk ^ 2 := mul_le_mul_of_nonneg_right hle (sq_nonneg _)
  nlinarith [mul_pos hqi hqk]

end MWG.Production
