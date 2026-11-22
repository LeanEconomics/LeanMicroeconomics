/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.CloserGivenExpenditure

/-!
# Exercise 3.G.16(c): the Slutsky equation for a given expenditure function

MWG, Exercise 3.G.16(c), p. 101, for `e(p, u) = exp{∑ α_l log p_l + (∏ p_l^{β_l}) u}`
(`givenExp`). Write `A(p) = ∑ α_l log p_l` and `Π(p) = ∏ p_l^{β_l}`. The Hicksian demand is
`h_l(p, u) = ∂e/∂p_l = e(p, u)(α_l + β_l Π(p) u)/p_l` (`econ_givenHicks_hasDerivAt`), and the
Walrasian demand `x_l(p, w) = h_l(p, v(p, w)) = w(α_l + β_l(log w - A(p)))/p_l`
(`econ_givenDemand_eq`). The Slutsky equation
`∂h_l/∂p_k(p, u) = ∂x_l/∂p_k(p, w) + ∂x_l/∂w(p, w) x_k(p, w)`, `w = e(p, u)`,
holds for all `l`, `k`, `p ≫ 0` and `u` (`exercise_3_G_16c_slutsky`), with the derivatives
computed explicitly. Roy's identity is `exercise_3_G_16c_roy` (earlier module).
-/

namespace MWG.ClassicalDemand

open Filter Topology MWG.ConsumerChoice

variable {L : ℕ}

/-- **Exercise 3.G.16(c)** (MWG, p. 101). The Hicksian demand
`h_l(p, u) = e(p, u)(α_l + β_l Π(p) u)/p_l` of `givenExp`. -/
noncomputable def givenHicks (α β p : Fin L → ℝ) (u : ℝ) (l : Fin L) : ℝ :=
  givenExp α β p u * (α l + β l * (∏ k, p k ^ β k) * u) / p l

/-- **Exercise 3.G.16(c)** (MWG, p. 101). The Walrasian demand
`x_l(p, w) = w(α_l + β_l(log w - A(p)))/p_l` of `givenExp`. -/
noncomputable def givenDemand (α β p : Fin L → ℝ) (w : ℝ) (l : Fin L) : ℝ :=
  w * (α l + β l * (Real.log w - ∑ k, α k * Real.log (p k))) / p l

/-- `Π` along the `k`th price has derivative `β_k Π(p)/p_k`. -/
theorem econ_givenPi_hasDerivAt (β : Fin L → ℝ) {p : Fin L → ℝ} (hp : StrictlyPositive p)
    (k : Fin L) : HasDerivAt (fun t => ∏ j, Function.update p k t j ^ β j)
      (β k * (∏ j, p j ^ β j) / p k) (p k) := by
  have hpk := hp k
  set R := ∏ j ∈ Finset.univ.erase k, p j ^ β j with hR
  have hPiR : ∏ j, p j ^ β j = p k ^ β k * R := by
    have := givenPi_update β p k (p k)
    rwa [Function.update_eq_self] at this
  have h := (Real.hasDerivAt_rpow_const (p := β k) (Or.inl hpk.ne')).mul_const R
  refine (h.congr_deriv ?_).congr_of_eventuallyEq ?_
  · rw [hPiR, Real.rpow_sub_one hpk.ne']
    field_simp
  · filter_upwards with t
    exact givenPi_update β p k t

/-- `A` along the `k`th price has derivative `α_k/p_k`. -/
theorem econ_givenA_hasDerivAt (α : Fin L → ℝ) {p : Fin L → ℝ} (hp : StrictlyPositive p)
    (k : Fin L) : HasDerivAt (fun t => ∑ j, α j * Real.log (Function.update p k t j))
      (α k / p k) (p k) := by
  have hpk := hp k
  set S := ∑ j ∈ Finset.univ.erase k, α j * Real.log (p j)
  have h := ((Real.hasDerivAt_log hpk.ne').const_mul (α k)).add_const S
  refine (h.congr_deriv (by field_simp)).congr_of_eventuallyEq ?_
  filter_upwards with t
  exact givenA_update α p k t

/-- `e` along the `k`th price has derivative `h_k(p, u)` (Shephard's lemma for `givenExp`). -/
theorem econ_givenHicks_hasDerivAt (α β : Fin L → ℝ) {p : Fin L → ℝ} (hp : StrictlyPositive p)
    (u : ℝ) (k : Fin L) : HasDerivAt (fun t => givenExp α β (Function.update p k t) u)
      (givenHicks α β p u k) (p k) := by
  have hinner := (econ_givenA_hasDerivAt α hp k).add
    ((econ_givenPi_hasDerivAt β hp k).mul_const u)
  have h := (Real.hasDerivAt_exp _).comp (p k) hinner
  refine (h.congr_deriv ?_).congr_of_eventuallyEq ?_
  · simp only [Pi.add_apply, Function.update_eq_self, givenHicks, givenExp]
    field_simp
  · filter_upwards with t
    rfl

/-- **Exercise 3.G.16(c)** (MWG, p. 101). The Walrasian demand is the Hicksian demand at the
indirect utility: `x_l(p, w) = h_l(p, v(p, w))` for `w > 0`. -/
theorem econ_givenDemand_eq (α β : Fin L → ℝ) {p : Fin L → ℝ} (hp : StrictlyPositive p)
    {w : ℝ} (hw : 0 < w) (l : Fin L) :
    givenDemand α β p w l = givenHicks α β p (givenIndirect α β p w) l := by
  have hPi := givenPi_pos β hp
  unfold givenHicks
  rw [(exercise_3_G_16b α β hp).1 w hw]
  unfold givenDemand givenIndirect
  congr 2
  field_simp

/-- **Exercise 3.G.16(c)** (MWG, p. 101), the Slutsky equation. For `p ≫ 0`, any `u` and
`w = e(p, u)`, the derivatives `∂h_l/∂p_k(p, u)`, `∂x_l/∂p_k(p, w)` and `∂x_l/∂w(p, w)` exist
and `∂h_l/∂p_k = ∂x_l/∂p_k + (∂x_l/∂w) x_k(p, w)`. -/
theorem exercise_3_G_16c_slutsky (α β : Fin L → ℝ) {p : Fin L → ℝ} (hp : StrictlyPositive p)
    (u : ℝ) (l k : Fin L) :
    ∃ Dh Dx Dw : ℝ,
      HasDerivAt (fun t => givenHicks α β (Function.update p k t) u l) Dh (p k) ∧
      HasDerivAt (fun t => givenDemand α β (Function.update p k t) (givenExp α β p u) l) Dx
        (p k) ∧
      HasDerivAt (fun w' => givenDemand α β p w' l) Dw (givenExp α β p u) ∧
      Dh = Dx + Dw * givenDemand α β p (givenExp α β p u) k := by
  set w := givenExp α β p u with hwdef
  have hw : 0 < w := Real.exp_pos _
  set P := ∏ j, p j ^ β j with hPdef
  set A := ∑ j, α j * Real.log (p j) with hAdef
  have hPi : 0 < P := givenPi_pos β hp
  have hpk := hp k
  have hpl := hp l
  have hlog : Real.log w = A + P * u := by
    rw [hwdef, givenExp, Real.log_exp]
  have hE := econ_givenHicks_hasDerivAt α β hp u k
  have hPd := econ_givenPi_hasDerivAt β hp k
  have hAd := econ_givenA_hasDerivAt α hp k
  have hE0 : givenExp α β (Function.update p k (p k)) u = w := by
    rw [Function.update_eq_self]
  have hP0 : ∏ j, Function.update p k (p k) j ^ β j = P := by rw [Function.update_eq_self]
  have hA0 : ∑ j, α j * Real.log (Function.update p k (p k) j) = A := by
    rw [Function.update_eq_self]
  -- the derivative in `w`
  have hDw : HasDerivAt (fun w' => givenDemand α β p w' l)
      ((α l + β l * (Real.log w - A) + β l) / p l) w := by
    have h1 := ((Real.hasDerivAt_log hw.ne').sub_const A).const_mul (β l) |>.const_add (α l)
    have h2 := ((hasDerivAt_id w).mul h1).div_const (p l)
    refine (h2.congr_deriv ?_).congr_of_eventuallyEq ?_
    · simp only [id]
      field_simp
    · filter_upwards with w'
      rfl
  have hxk : givenDemand α β p w k = w * (α k + β k * (P * u)) / p k := by
    unfold givenDemand
    rw [hlog]
    ring
  by_cases hlk : l = k
  · subst hlk
    -- own-price effects
    have hden : HasDerivAt (fun t : ℝ => Function.update p l t l) 1 (p l) := by
      refine (hasDerivAt_id (p l)).congr_of_eventuallyEq ?_
      filter_upwards with t
      simp
    have hnum := hE.mul (((hPd.mul_const u).const_mul (β l)).const_add (α l))
    have hh := hnum.div hden (by rw [Function.update_self]; exact hpl.ne')
    have hxn := (((hAd.const_sub (Real.log w)).const_mul (β l)).const_add (α l)).const_mul w
    have hx := hxn.div hden (by rw [Function.update_self]; exact hpl.ne')
    refine ⟨_, _, _, hh.congr_of_eventuallyEq ?_, hx.congr_of_eventuallyEq ?_, hDw, ?_⟩
    · filter_upwards with t
      simp only [givenHicks, Pi.mul_apply, Pi.div_apply]
      ring
    · filter_upwards with t
      simp only [givenDemand, Pi.div_apply]
    · rw [hxk]
      simp only [Pi.mul_apply, hE0, hP0, hA0, Function.update_self, givenHicks, ← hwdef,
        ← hPdef, hlog]
      field_simp
      ring
  · -- cross-price effects
    have hpl' : ∀ t, Function.update p k t l = p l := fun t => Function.update_of_ne hlk _ _
    have hh := (hE.mul (((hPd.mul_const u).const_mul (β l)).const_add (α l))).div_const (p l)
    have hx := ((((hAd.const_sub (Real.log w)).const_mul (β l)).const_add (α l)).const_mul
      w).div_const (p l)
    refine ⟨_, _, _, hh.congr_of_eventuallyEq ?_, hx.congr_of_eventuallyEq ?_, hDw, ?_⟩
    · filter_upwards with t
      simp only [givenHicks, hpl', Pi.mul_apply]
      ring
    · filter_upwards with t
      simp only [givenDemand, hpl']
    · rw [hxk]
      simp only [hE0, hP0, givenHicks, ← hwdef, ← hPdef, hlog]
      field_simp
      ring

end MWG.ClassicalDemand
