/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGExternalitiesPublicGoods.Multilateral
import MWGExternalitiesPublicGoods.PrivateInfo
import MWGExternalitiesPublicGoods.ExercisesB
import MWGExternalitiesPublicGoods.ExercisesD1
import MWGExternalitiesPublicGoods.ExercisesD2

/-!
# Concrete instances of the hypotheses

Non-vacuity checks for theorems whose hypotheses are not instantiated in their own modules:

* the depletable optimum of `mlEx` via (11.D.3)-(11.D.4) (`mlEx_depl`);
* a binding quota (`quota_binds_instance`);
* Exercise 11.B.2(b) and (c) with explicit utility functions and paths;
* Exercise 11.B.4 with `φ₂(h, e) = -h - (e - h)²/2`;
* Exercise 11.D.2 with `φᵢ(x, H) = x - H²/2`;
* Exercise 11.D.3 with `c(q, Q) = q²/2 - Q` and `P(Q) = 10 - Q`;
* Exercise 11.D.4 with linear damages.
-/

namespace MWG.ExternalitiesPublicGoods

open MWG.CompetitiveMarkets

/-- The depletable version of `mlEx` (two consumers `φᵢ(h̃) = -h̃ - h̃²/2`, firms with
`πⱼ(h) = aⱼh - h²/2`, `a = (4, 6)`): absorptions `(2, 2)` and generation `(1, 3)` solve
(11.D.2), with
multiplier `μ = -3`. -/
theorem mlEx_depl : mlEx.IsDeplOpt ![2, 2] ![1, 3] := by
  refine mlEx.deplKKT_sufficient (μ := -3) ⟨fun i => ?_, fun j => ?_, ?_⟩
    ⟨fun i => ?_, fun j => ?_⟩
  · fin_cases i <;> norm_num
  · fin_cases j <;> norm_num
  · simp [Fin.sum_univ_two]; norm_num
  · fin_cases i <;> norm_num [mlEx]
  · fin_cases j <;> norm_num [mlEx]

/-- An instance of `quota_binds`: profit `3h - h²/2`, quota `1` (marginal profit `2 > 0`). -/
theorem quota_binds_instance : IsQuotaChoice (fun h => 3 * h - h ^ 2 / 2) 1 1 := by
  have hd : ∀ x : ℝ, HasDerivAt (fun h => 3 * h - h ^ 2 / 2) (3 - x) x := fun x => by
    have h' := ((hasDerivAt_id x).const_mul 3).sub ((hasDerivAt_pow 2 x).div_const 2)
    exact (h'.congr_deriv (by simp only [Nat.cast_ofNat]; ring) :
      HasDerivAt (fun h : ℝ => 3 * h - h ^ 2 / 2) (3 - x) x)
  exact (quota_binds hd (fun a _ b _ hab => by linarith) zero_le_one (by norm_num) 1).2 rfl

/-- An instance of Exercise 11.B.2(b): `φ₂(h, w) = w h`, so `φ₂ₕ(h, z) = z`, `φ₂_w(h, z) = h`;
consumer 2's demand at price `p = 1` is `h(w) = w/2`, with wealth effect `1/2`. -/
theorem exercise_11_B_2b_instance :
    (1 / 2 : ℝ) * (0 - 2 * 1 * 1 + 1 ^ 2 * 0) + (1 - 1 * 0) = 0 := by
  have hF₁ : ∀ x : ℝ × ℝ, HasFDerivAt (fun x : ℝ × ℝ => x.2)
      ((0 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ + (1 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ) x :=
    fun x => by simpa using hasFDerivAt_snd
  have hF₂ : ∀ x : ℝ × ℝ, HasFDerivAt (fun x : ℝ × ℝ => x.1)
      ((1 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ + (0 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ) x :=
    fun x => by simpa using hasFDerivAt_fst
  have hh : HasDerivAt (fun w : ℝ => w / 2) (1 / 2) 2 := by
    simpa using (hasDerivAt_id (2 : ℝ)).div_const 2
  exact exercise_11_B_2b (fun x => x.2) (fun x => x.1) (fun w => w / 2) 1 2 (1 / 2) 0 1 0
    (hF₁ _) (hF₂ _) hh (fun w => by ring)

/-- An instance of Exercise 11.B.2(c) (corrected comparative statics): `φ₂(h, z) = z + 2h - h²/2`
(`φ₂ₕ = 2 - h`, `φ₂_w = 1`), `φ₁(h) = -h²/2`; the optimum is `h° ≡ 1`, `z°(w₂) = w₂ - 1/2`, so
`dh°/dw₂ = 0`, consistent with the zero wealth effect of a quasilinear `φ₂`. -/
theorem exercise_11_B_2c_instance :
    (0 : ℝ) * (-1 - 2 * (-(-(1 : ℝ))) * 0 + (-(-(1 : ℝ))) ^ 2 * 0 + -1 * 1) +
      (0 - (-(-(1 : ℝ))) * 0) = 0 := by
  have hF₁ : ∀ x : ℝ × ℝ, HasFDerivAt (fun x : ℝ × ℝ => 2 - x.1)
      ((-1 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ + (0 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ) x :=
    fun x => by
      have := (hasFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := x)).const_sub 2
      convert this using 1
      ext <;> simp
  have hF₂ : ∀ x : ℝ × ℝ, HasFDerivAt (fun _ : ℝ × ℝ => (1 : ℝ))
      ((0 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ + (0 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ) x :=
    fun x => by simpa using hasFDerivAt_const (1 : ℝ) x
  have hφ₁ : ∀ x : ℝ, HasDerivAt (fun h : ℝ => -(h ^ 2 / 2)) (-x) x := fun x => by
    have h' := ((hasDerivAt_pow 2 x).div_const 2).neg
    exact (h'.congr_deriv (by simp only [Nat.cast_ofNat]; ring) :
      HasDerivAt (fun h : ℝ => -(h ^ 2 / 2)) (-x) x)
  have hd₁ : HasDerivAt (fun x : ℝ => -x) (-1) ((fun _ : ℝ => (1 : ℝ)) 0) := hasDerivAt_neg 1
  have hh : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 0 := hasDerivAt_const _ _
  have hz : HasDerivAt (fun w : ℝ => -((1 : ℝ) ^ 2 / 2) + w + 0) 1 0 :=
    ((hasDerivAt_id (0 : ℝ)).const_add (-((1 : ℝ) ^ 2 / 2))).add_const 0
  exact exercise_11_B_2c_corrected (fun x => 2 - x.1) (fun _ => 1) (fun h => -(h ^ 2 / 2))
    (fun x => -x) (fun _ => 1) (fun w => -((1 : ℝ) ^ 2 / 2) + w + 0) 0 0 1 (-1) (-1) 0 0 0
    (hF₁ _) (hF₂ _) hφ₁ hd₁ hh hz (fun w => by ring) (fun w => by ring)

/-- An instance of Exercise 11.B.4: `φ₁(h) = 4h - h²/2`, `φ₂(h, e) = -h - (e - h)²/2`; the optimum
is
`(h°, e°) = (3, 3)` and `∂φ₂/∂h(3, 3) = -1`. -/
theorem exercise_11_B_4_instance :
    (∀ y, 0 ≤ y → 4 * y - y ^ 2 / 2 - (-(-1 : ℝ)) * y ≤
      4 * 3 - (3 : ℝ) ^ 2 / 2 - (-(-1)) * 3) ∧
      ∀ e, -(3 : ℝ) - (e - 3) ^ 2 / 2 ≤ -3 - (3 - 3) ^ 2 / 2 := by
  have hφ₁ : ∀ x : ℝ, HasDerivAt (fun h : ℝ => 4 * h - h ^ 2 / 2) (4 - x) x := fun x => by
    have h' := ((hasDerivAt_id x).const_mul 4).sub ((hasDerivAt_pow 2 x).div_const 2)
    exact (h'.congr_deriv (by simp only [Nat.cast_ofNat]; ring) :
      HasDerivAt (fun h : ℝ => 4 * h - h ^ 2 / 2) (4 - x) x)
  have hg : HasDerivAt (fun h : ℝ => -h - (3 - h) ^ 2 / 2) (-1) 3 := by
    have h' := (hasDerivAt_id (3 : ℝ)).neg.sub
      ((((hasDerivAt_id (3 : ℝ)).const_sub 3).pow 2).div_const 2)
    exact (h'.congr_deriv (by norm_num) :
      HasDerivAt (fun h : ℝ => -h - (3 - h) ^ 2 / 2) (-1) 3)
  exact exercise_11_B_4 (fun h e => -h - (e - h) ^ 2 / 2) hφ₁
    (fun a _ b _ hab => by linarith) hg
    ⟨by norm_num, fun h e _ => by nlinarith [sq_nonneg (h - 3), sq_nonneg (e - h)]⟩

/-- An instance of Exercise 11.D.2: two consumers with `φᵢ(x, H) = x - H²/2` (`∂₁ = 1`,
`∂₂ = -H`); the optimal total is `H° = 1/2`, attained at `(1/4, 1/4)`. -/
theorem exercise_11_D_2_instance :
    ∀ y ∈ orthant (Fin 2), d2Obj (fun _ (x : ℝ × ℝ) => x.1 - x.2 ^ 2 / 2) y ≤
      d2Obj (fun _ (x : ℝ × ℝ) => x.1 - x.2 ^ 2 / 2) ![1 / 4, 1 / 4] := by
  have hφ : ∀ (i : Fin 2) (x : ℝ × ℝ), HasFDerivAt (fun x : ℝ × ℝ => x.1 - x.2 ^ 2 / 2)
      ((fun _ _ => (1 : ℝ)) i x • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (fun _ (x : ℝ × ℝ) => -x.2) i x • ContinuousLinearMap.snd ℝ ℝ ℝ) x := fun _ x => by
    have h1 := hasFDerivAt_fst (𝕜 := ℝ) (p := x) (E := ℝ) (F := ℝ)
    have h2 : HasFDerivAt (fun x : ℝ × ℝ => x.2 ^ 2)
        ((2 * x.2) • ContinuousLinearMap.snd ℝ ℝ ℝ) x := by
      have := (hasFDerivAt_snd (𝕜 := ℝ) (p := x) (E := ℝ) (F := ℝ)).mul
        (hasFDerivAt_snd (𝕜 := ℝ) (p := x) (E := ℝ) (F := ℝ))
      convert this using 1
      · ext y; simp [sq]
      · ext
        · simp
        · simp; ring
    have h3 := HasFDerivAt.const_mul h2 (1 / 2 : ℝ)
    convert h1.sub h3 using 1
    · ext y; simp only [Pi.sub_apply]; ring
    · ext <;> simp
  have hconc : ∀ i : Fin 2, ConcaveOn ℝ Set.univ (fun x : ℝ × ℝ => x.1 - x.2 ^ 2 / 2) := by
    intro _
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul]
    have hb' : b = 1 - a := by linarith
    subst hb'
    nlinarith [mul_nonneg ha hb, mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x.2 - y.2))]
  have hmem : ![(1 : ℝ) / 4, 1 / 4] ∈ orthant (Fin 2) := fun i => by fin_cases i <;> norm_num
  refine (exercise_11_D_2_opt _ (fun _ _ => 1) (fun _ x => -x.2) hφ hconc hmem).2 fun j => ?_
  simp [Fin.sum_univ_two]
  norm_num

/-- An instance of Exercise 11.D.3: `c(q, Q) = q²/2 - Q` (`c_q = q`, `c_Q = -1 < 0`), `J = 2`,
inverse demand `P(Q) = 10 - Q`: the equilibrium `Q* = 20/3` is below the optimum `Q° = 8`. -/
theorem exercise_11_D_3_instance : (20 / 3 : ℝ) < 8 := by
  refine exercise_11_D_3 (P := fun Q => 10 - Q) (cq := fun x => x.1) (cQ := fun _ => -1)
    (J := 2) (fun a b hab => by simp only; linarith) (fun a b hab => by simp only; linarith)
    two_pos (fun _ => by norm_num) (by norm_num) (by norm_num)

/-- An instance of Exercise 11.D.4: one consumer with linear damage `-(h₁ + h₂)` and firms with
`πⱼ(h) = 3h - h²/2`: the optimum is `(2, 2)`. -/
theorem exercise_11_D_4_instance :
    ∀ y ∈ orthant (Fin 2),
      d4Obj (fun (_ : Fin 1) (h : Fin 2 → ℝ) => -(h 0 + h 1)) (fun _ h => 3 * h - h ^ 2 / 2) y ≤
        d4Obj (fun (_ : Fin 1) (h : Fin 2 → ℝ) => -(h 0 + h 1)) (fun _ h => 3 * h - h ^ 2 / 2)
          ![2, 2] := by
  set D : (Fin 2 → ℝ) →L[ℝ] ℝ :=
    -(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0 +
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1)
  have hD : ∀ h : Fin 2 → ℝ, D h = -(h 0 + h 1) := fun h => by simp [D]
  have hφ : ∀ _i : Fin 1, HasFDerivAt (fun h : Fin 2 → ℝ => -(h 0 + h 1)) D ![2, 2] := by
    intro _
    have := D.hasFDerivAt (x := ![2, 2])
    have e : (⇑D) = fun h : Fin 2 → ℝ => -(h 0 + h 1) := funext hD
    rw [e] at this
    exact this
  have hconc : ∀ _i : Fin 1, ConcaveOn ℝ (orthant (Fin 2)) fun h : Fin 2 → ℝ => -(h 0 + h 1) := by
    intro _
    refine ⟨convex_orthant _, fun x _ y _ a b _ _ _ => ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith
  have hpr : ∀ (_j : Fin 2) (x : ℝ), HasDerivAt (fun h : ℝ => 3 * h - h ^ 2 / 2) (3 - x) x :=
    fun _ x => by
      have h' := ((hasDerivAt_id x).const_mul 3).sub ((hasDerivAt_pow 2 x).div_const 2)
      exact (h'.congr_deriv (by simp only [Nat.cast_ofNat]; ring) :
        HasDerivAt (fun h : ℝ => 3 * h - h ^ 2 / 2) (3 - x) x)
  have hmem : ![(2 : ℝ), 2] ∈ orthant (Fin 2) := fun i => by fin_cases i <;> norm_num
  refine (exercise_11_D_4_opt _ (fun _ => D) _ (fun _ x => 3 - x) hφ hconc hpr
    (fun _ a _ b _ hab => by linarith) hmem).2 fun j => ?_
  fin_cases j <;> simp [hD] <;> norm_num

end MWG.ExternalitiesPublicGoods
