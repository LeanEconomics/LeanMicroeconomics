/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.RelationsExercises
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Exercise 3.G.16: a given expenditure function

MWG, Exercise 3.G.16, p. 101: `e(p, u) = exp{∑_l α_l log p_l + (∏_l p_l^{β_l}) u}`.
Write `Π(p) = ∏ p_l^{β_l}` and `A(p) = ∑ α_l log p_l`.

* **(a)** Homogeneity of degree one in `p` holds iff `∑ α_l = 1` and `∑ β_l = 0`
  (`exercise_3_G_16a_homogeneous`); `e` is strictly increasing in `u` (`Π > 0`); and `e`
  nondecreasing in prices at `u = 0` forces `α_l ≥ 0` (`exercise_3_G_16a_alpha_nonneg`).
* **(b)** The indirect utility is `v(p, w) = (log w - A(p))/Π(p)`: it inverts `e` in `u`
  (`exercise_3_G_16b`).
* **(c)** Roy's identity: with `x_l(p, w) = ∂e/∂p_l` at `u = v(p, w)`, i.e.
  `x_l = w (α_l + β_l Π(p) v(p, w))/p_l`, the partial derivatives of `v` satisfy
  `x_l = -(∂v/∂p_l)/(∂v/∂w)` (`exercise_3_G_16c_roy`). The Slutsky equation part of (c) is not
  formalized (see `docs/source-map-E.md`).
-/

namespace MWG.ClassicalDemand

open Filter Topology MWG.ConsumerChoice

variable {L : ℕ}

/-- **Exercise 3.G.16** (MWG, p. 101). The expenditure function
`exp{∑ α_l log p_l + (∏ p_l^{β_l}) u}`. -/
noncomputable def givenExp (α β p : Fin L → ℝ) (u : ℝ) : ℝ :=
  Real.exp (∑ l, α l * Real.log (p l) + (∏ l, p l ^ β l) * u)

/-- **Exercise 3.G.16(b)** (MWG, p. 101). The indirect utility
`(log w - ∑ α_l log p_l)/∏ p_l^{β_l}`. -/
noncomputable def givenIndirect (α β p : Fin L → ℝ) (w : ℝ) : ℝ :=
  (Real.log w - ∑ l, α l * Real.log (p l)) / ∏ l, p l ^ β l

/-- `Π(p) > 0` for `p ≫ 0`. -/
theorem givenPi_pos (β : Fin L → ℝ) {p : Fin L → ℝ} (hp : StrictlyPositive p) :
    0 < ∏ l, p l ^ β l :=
  Finset.prod_pos fun l _ => Real.rpow_pos_of_pos (hp l) _

/-- **Exercise 3.G.16(a)** (MWG, p. 101). `e` is homogeneous of degree one in `p` (for all
`p ≫ 0`, `u` and `t > 0`) iff `∑ α_l = 1` and `∑ β_l = 0`. -/
theorem exercise_3_G_16a_homogeneous (α β : Fin L → ℝ) :
    (∀ p : Fin L → ℝ, StrictlyPositive p → ∀ (u t : ℝ), 0 < t →
        givenExp α β (t • p) u = t * givenExp α β p u) ↔
      ∑ l, α l = 1 ∧ ∑ l, β l = 0 := by
  have hsmul : ∀ p : Fin L → ℝ, StrictlyPositive p → ∀ t : ℝ, 0 < t → ∀ u : ℝ,
      givenExp α β (t • p) u =
        Real.exp ((∑ l, α l) * Real.log t + ∑ l, α l * Real.log (p l) +
          t ^ (∑ l, β l) * (∏ l, p l ^ β l) * u) := by
    intro p hp t ht u
    unfold givenExp
    congr 1
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_congr rfl fun l _ => by rw [Real.log_mul ht.ne' (hp l).ne', mul_add],
      Finset.sum_add_distrib, ← Finset.sum_mul,
      Finset.prod_congr rfl fun l _ => Real.mul_rpow ht.le (hp l).le, Finset.prod_mul_distrib,
      ← Real.rpow_sum_of_pos ht]
  constructor
  · intro h
    have h1 : StrictlyPositive (fun _ : Fin L => (1 : ℝ)) := fun _ => one_pos
    have key : ∀ u : ℝ, (∑ l, α l) * Real.log (Real.exp 1) + Real.exp 1 ^ (∑ l, β l) * u =
        Real.log (Real.exp 1) + u := by
      intro u
      have ht := Real.exp_pos 1
      have := h _ h1 u (Real.exp 1) ht
      rw [hsmul _ h1 _ ht] at this
      have hg1 : givenExp α β (fun _ => 1) u = Real.exp u := by simp [givenExp]
      have h2 : Real.exp 1 * Real.exp u = Real.exp (Real.log (Real.exp 1) + u) := by
        rw [Real.exp_add, Real.exp_log ht]
      rw [hg1, h2] at this
      have := Real.exp_injective this
      simp only [Real.log_one, mul_zero, Finset.sum_const_zero, add_zero, Real.one_rpow,
        Finset.prod_const_one, mul_one] at this
      exact this
    have k0 := key 0
    have k1 := key 1
    simp only [Real.log_exp, mul_one, mul_zero, add_zero] at k0 k1
    refine ⟨k0, ?_⟩
    have : Real.exp 1 ^ (∑ l, β l) = 1 := by linarith
    rw [← Real.exp_mul, one_mul, Real.exp_eq_one_iff] at this
    exact this
  · rintro ⟨hα, hβ⟩ p hp u t ht
    rw [hsmul p hp t ht, hα, hβ, Real.rpow_zero, one_mul, one_mul, givenExp,
      show Real.log t + ∑ l, α l * Real.log (p l) + (∏ l, p l ^ β l) * u =
        Real.log t + (∑ l, α l * Real.log (p l) + (∏ l, p l ^ β l) * u) by ring,
      Real.exp_add, Real.exp_log ht]

/-- **Exercise 3.G.16(a)** (MWG, p. 101). `e` is strictly increasing in `u` (since `Π(p) > 0`). -/
theorem exercise_3_G_16a_increasing (α β : Fin L → ℝ) {p : Fin L → ℝ} (hp : StrictlyPositive p)
    {u u' : ℝ} (huu : u < u') : givenExp α β p u < givenExp α β p u' := by
  unfold givenExp
  apply Real.exp_lt_exp.2
  nlinarith [givenPi_pos β hp]

/-- **Exercise 3.G.16(a)** (MWG, p. 101). If `e` is nondecreasing in prices at `u = 0`, then
every `α_l ≥ 0`. -/
theorem exercise_3_G_16a_alpha_nonneg (α β : Fin L → ℝ)
    (hmono : ∀ p p' : Fin L → ℝ, StrictlyPositive p → p ≤ p' →
      givenExp α β p 0 ≤ givenExp α β p' 0) (l : Fin L) : 0 ≤ α l := by
  have h1 : StrictlyPositive (fun _ : Fin L => (1 : ℝ)) := fun _ => one_pos
  have hle : (fun _ : Fin L => (1 : ℝ)) ≤ Function.update (fun _ => 1) l 2 := by
    intro k
    by_cases hk : k = l
    · subst hk; simp
    · simp [Function.update_of_ne hk]
  have := hmono _ _ h1 hle
  simp only [givenExp, mul_zero, add_zero, Real.log_one, Finset.sum_const_zero,
    Real.exp_le_exp] at this
  have hs : ∑ k, α k * Real.log (Function.update (fun _ : Fin L => (1 : ℝ)) l 2 k) =
      α l * Real.log 2 := by
    rw [Finset.sum_eq_single l]
    · simp
    · intro k _ hk
      simp [Function.update_of_ne hk]
    · simp
  rw [hs] at this
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  nlinarith

/-- **Exercise 3.G.16(b)** (MWG, p. 101). `v(p, w) = (log w - A(p))/Π(p)` is the indirect
utility corresponding to `e`: `e(p, v(p, w)) = w` for `w > 0` and `v(p, e(p, u)) = u`. -/
theorem exercise_3_G_16b (α β : Fin L → ℝ) {p : Fin L → ℝ} (hp : StrictlyPositive p) :
    (∀ w : ℝ, 0 < w → givenExp α β p (givenIndirect α β p w) = w) ∧
      ∀ u : ℝ, givenIndirect α β p (givenExp α β p u) = u := by
  have hPi := givenPi_pos β hp
  refine ⟨fun w hw => ?_, fun u => ?_⟩
  · unfold givenExp givenIndirect
    rw [mul_div_cancel₀ _ hPi.ne', add_sub_cancel, Real.exp_log hw]
  · unfold givenExp givenIndirect
    rw [Real.log_exp]
    field_simp
    ring

/-- `Π` along the `l`th price: `Π(p with p_l = t) = t^{β_l} ∏_{k ≠ l} p_k^{β_k}`. -/
theorem givenPi_update (β p : Fin L → ℝ) (l : Fin L) (t : ℝ) :
    ∏ k, Function.update p l t k ^ β k = t ^ β l * ∏ k ∈ Finset.univ.erase l, p k ^ β k := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ l), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun k hk => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]

/-- `A` along the `l`th price: `A(p with p_l = t) = α_l log t + ∑_{k ≠ l} α_k log p_k`. -/
theorem givenA_update (α p : Fin L → ℝ) (l : Fin L) (t : ℝ) :
    ∑ k, α k * Real.log (Function.update p l t k) =
      α l * Real.log t + ∑ k ∈ Finset.univ.erase l, α k * Real.log (p k) := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ l), Function.update_self]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]

/-- **Exercise 3.G.16(c)** (MWG, p. 101), Roy's identity. For `p ≫ 0`, `w > 0`, with
`v = v(p, w)` and `Π = Π(p)`: `∂v/∂w = 1/(wΠ)`, `∂v/∂p_l = -α_l/(p_lΠ) - β_l v/p_l`, and
`x_l(p, w) = w (α_l + β_l Π v)/p_l = -(∂v/∂p_l)/(∂v/∂w)`; this `x_l` is `∂e/∂p_l` at
`u = v(p, w)`. -/
theorem exercise_3_G_16c_roy (α β : Fin L → ℝ) {p : Fin L → ℝ} (hp : StrictlyPositive p)
    {w : ℝ} (hw : 0 < w) (l : Fin L) :
    HasDerivAt (fun w' => givenIndirect α β p w') (1 / (w * ∏ k, p k ^ β k)) w ∧
      HasDerivAt (fun t => givenIndirect α β (Function.update p l t) w)
        (-(α l / (p l * ∏ k, p k ^ β k)) - β l * givenIndirect α β p w / p l) (p l) ∧
      HasDerivAt (fun t => givenExp α β (Function.update p l t) (givenIndirect α β p w))
        (w * (α l + β l * (∏ k, p k ^ β k) * givenIndirect α β p w) / p l) (p l) ∧
      w * (α l + β l * (∏ k, p k ^ β k) * givenIndirect α β p w) / p l =
        -((-(α l / (p l * ∏ k, p k ^ β k)) - β l * givenIndirect α β p w / p l) /
          (1 / (w * ∏ k, p k ^ β k))) := by
  have hPi := givenPi_pos β hp
  have hpl := hp l
  set R := ∏ k ∈ Finset.univ.erase l, p k ^ β k with hR
  set S := ∑ k ∈ Finset.univ.erase l, α k * Real.log (p k) with hS
  have hPiR : ∏ k, p k ^ β k = p l ^ β l * R := by
    have := givenPi_update β p l (p l)
    rwa [Function.update_eq_self] at this
  have hAS : ∑ k, α k * Real.log (p k) = α l * Real.log (p l) + S := by
    have := givenA_update α p l (p l)
    rwa [Function.update_eq_self] at this
  have hR0 : 0 < R := Finset.prod_pos fun k _ => Real.rpow_pos_of_pos (hp k) _
  have hPpos := Real.rpow_pos_of_pos hpl (β l)
  -- derivative of `Π` along `p_l`
  have hPid : HasDerivAt (fun t => ∏ k, Function.update p l t k ^ β k)
      (β l * (∏ k, p k ^ β k) / p l) (p l) := by
    have h := ((Real.hasDerivAt_rpow_const (p := β l) (Or.inl hpl.ne')).mul_const R)
    refine (h.congr_deriv ?_).congr_of_eventuallyEq ?_
    · rw [hPiR, Real.rpow_sub_one hpl.ne']
      field_simp
    · filter_upwards with t
      exact givenPi_update β p l t
  -- derivative of `A` along `p_l`
  have hAd : HasDerivAt (fun t => ∑ k, α k * Real.log (Function.update p l t k))
      (α l / p l) (p l) := by
    have h := ((Real.hasDerivAt_log hpl.ne').const_mul (α l)).add_const S
    refine (h.congr_deriv (by field_simp)).congr_of_eventuallyEq ?_
    filter_upwards with t
    exact givenA_update α p l t
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := ((Real.hasDerivAt_log hw.ne').sub_const (∑ k, α k * Real.log (p k))).div_const
      (∏ k, p k ^ β k)
    refine h.congr_deriv ?_
    field_simp
  · have hnum := (hasDerivAt_const (p l) (Real.log w)).sub hAd
    have h := hnum.div hPid (by rw [Function.update_eq_self]; exact hPi.ne')
    refine (h.congr_deriv ?_).congr_of_eventuallyEq ?_
    · simp only [givenIndirect, Pi.sub_apply, Function.update_eq_self]
      field_simp
      ring
    · filter_upwards with t
      rfl
  · have hinner := hAd.add (hPid.mul_const (givenIndirect α β p w))
    have h := (Real.hasDerivAt_exp _).comp (p l) hinner
    refine (h.congr_deriv ?_).congr_of_eventuallyEq ?_
    · have he : Real.exp (∑ k, α k * Real.log (Function.update p l (p l) k) +
          (∏ k, Function.update p l (p l) k ^ β k) * givenIndirect α β p w) = w := by
        simp only [Function.update_eq_self]
        exact (exercise_3_G_16b α β hp).1 w hw
      simp only [Function.update_eq_self] at he
      simp only [Pi.add_apply, Function.update_eq_self]
      rw [he]
      field_simp
    · filter_upwards with t
      rfl
  · field_simp
    ring

end MWG.ClassicalDemand
