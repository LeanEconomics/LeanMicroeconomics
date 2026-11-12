/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGConsumerChoice.AppendixMDBasic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Productive input–output matrices

MWG, Mathematical Appendix, Theorem M.D.5(v) (p. 940). If all entries of `M` are nonnegative
and `Mz ≪ z` for some `z ≫ 0`, then `(I - M)⁻¹` exists and equals `∑_{k=0}^∞ Mᵏ`.

The book refers to the Appendix of Chapter 5 for the proof. Here: with `θ = maxᵢ (Mz)ᵢ/zᵢ < 1`,
`Mᵏz ≤ θᵏz`, so each entry of `Mᵏ` is bounded by a geometric sequence and `∑ Mᵏ` converges
entrywise to some `T`; telescoping gives `(I - M)T = T(I - M) = I`.
-/

namespace MWG.ConsumerChoice

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Powers of an entrywise nonnegative matrix are entrywise nonnegative. -/
theorem pow_entry_nonneg {M : Matrix n n ℝ} (hM : ∀ i j, 0 ≤ M i j) (k : ℕ) (i j : n) :
    0 ≤ (M ^ k) i j := by
  induction k generalizing i j with
  | zero => simp [Matrix.one_apply]; split_ifs <;> norm_num
  | succ k ih =>
    rw [pow_succ', Matrix.mul_apply]
    exact Finset.sum_nonneg fun l _ => mul_nonneg (hM i l) (ih l j)

/-- **Theorem M.D.5(v)** (MWG, p. 940). If `M` has nonnegative entries and `Mz ≪ z` for some
`z ≫ 0`, then `∑ₖ Mᵏ` converges, `I - M` is invertible, and `(I - M)⁻¹ = ∑ₖ Mᵏ`. -/
theorem theorem_M_D_5_v {M : Matrix n n ℝ} (hM : ∀ i j, 0 ≤ M i j) {z : n → ℝ}
    (hz : ∀ i, 0 < z i) (hMz : ∀ i, (M *ᵥ z) i < z i) :
    Summable (fun k : ℕ => M ^ k) ∧ IsUnit (1 - M) ∧ (1 - M)⁻¹ = ∑' k : ℕ, M ^ k := by
  -- a uniform contraction factor
  obtain ⟨θ, hθ0, hθ1, hθ⟩ : ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧ ∀ i, (M *ᵥ z) i ≤ θ * z i := by
    rcases isEmpty_or_nonempty n with hn | hn
    · exact ⟨0, le_rfl, one_pos, fun i => (hn.false i).elim⟩
    obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ
      (fun i => (M *ᵥ z) i / z i) Finset.univ_nonempty
    refine ⟨(M *ᵥ z) i₀ / z i₀, ?_, ?_, fun i => ?_⟩
    · apply div_nonneg _ (hz i₀).le
      exact Finset.sum_nonneg fun j _ => mul_nonneg (hM i₀ j) (hz j).le
    · rw [div_lt_one (hz i₀)]; exact hMz i₀
    · have := hi₀ i (Finset.mem_univ i)
      rw [div_le_iff₀ (hz i)] at this
      exact this
  -- `Mᵏ z ≤ θᵏ z`
  have hpow : ∀ k : ℕ, ∀ i, (M ^ k *ᵥ z) i ≤ θ ^ k * z i := by
    intro k
    induction k with
    | zero => intro i; simp
    | succ k ih =>
      intro i
      rw [pow_succ', ← mulVec_mulVec]
      calc (M *ᵥ (M ^ k *ᵥ z)) i ≤ (M *ᵥ (θ ^ k • z)) i := by
            simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
            exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (ih j) (hM i j)
        _ = θ ^ k * (M *ᵥ z) i := by rw [mulVec_smul, Pi.smul_apply, smul_eq_mul]
        _ ≤ θ ^ k * (θ * z i) := mul_le_mul_of_nonneg_left (hθ i) (pow_nonneg hθ0 k)
        _ = θ ^ (k + 1) * z i := by ring
  -- entrywise geometric bounds
  have hentry : ∀ k : ℕ, ∀ i j, (M ^ k) i j ≤ z i / z j * θ ^ k := by
    intro k i j
    have h1 : (M ^ k) i j * z j ≤ (M ^ k *ᵥ z) i :=
      Finset.single_le_sum (f := fun l => (M ^ k) i l * z l)
        (fun l _ => mul_nonneg (pow_entry_nonneg hM k i l) (hz l).le) (Finset.mem_univ j)
    have h2 := (h1.trans (hpow k i))
    rw [div_mul_eq_mul_div, le_div_iff₀ (hz j)]
    linarith
  have hsum : Summable (fun k : ℕ => M ^ k) := by
    exact Pi.summable.mpr fun i => Pi.summable.mpr fun j =>
      Summable.of_nonneg_of_le (fun k => pow_entry_nonneg hM k i j) (fun k => hentry k i j)
        ((summable_geometric_of_lt_one hθ0 hθ1).mul_left _)
  set T := ∑' k : ℕ, M ^ k with hT
  have hT' : HasSum (fun k : ℕ => M ^ k) T := hsum.hasSum
  have hshift : HasSum (fun k : ℕ => M ^ (k + 1)) (T - 1) := by
    have := (hasSum_nat_add_iff' 1).mpr hT'
    simpa using this
  have htel : HasSum (fun k : ℕ => M ^ k - M ^ (k + 1)) 1 := by
    have := hT'.sub hshift
    simpa using this
  have hleft : (1 - M) * T = 1 := by
    have h := hT'.mul_left (1 - M)
    have e : (fun k : ℕ => (1 - M) * M ^ k) = fun k => M ^ k - M ^ (k + 1) := by
      funext k
      rw [sub_mul, one_mul, pow_succ']
    rw [e] at h
    exact h.unique htel
  have hright : T * (1 - M) = 1 := by
    have h := hT'.mul_right (1 - M)
    have e : (fun k : ℕ => M ^ k * (1 - M)) = fun k => M ^ k - M ^ (k + 1) := by
      funext k
      rw [mul_sub, mul_one, pow_succ]
    rw [e] at h
    exact h.unique htel
  refine ⟨hsum, ?_, Matrix.inv_eq_right_inv hleft⟩
  exact (Matrix.isUnit_iff_isUnit_det _).mpr
    (Matrix.isUnit_det_of_right_inverse hleft)

end MWG.ConsumerChoice
