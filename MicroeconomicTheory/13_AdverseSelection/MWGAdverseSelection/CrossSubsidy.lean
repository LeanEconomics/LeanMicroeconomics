/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGAdverseSelection.SignalingEq

/-!
# Second-best intervention: cross-subsidization (Exercise 13.C.3)

MWG, Section 13.C, pp. 458-459, Figure 13.C.11 and Exercise 13.C.3.

`crossModel`: `θ_L = 1`, `θ_H = 2`, `λ = 1/3`, `r = 0`, and `c(e, θ) = (2 - θ)e + (θ - 1)e²/(1 + e)`
(so `c(e, θ_L) = e`, `c(e, θ_H) = e²/(1 + e)`; `c_θ < 0`, `c_{eθ} = -(1 + e)⁻² < 0`).

* `crossModel_valid`: it satisfies the assumptions, giving concrete instances of the separating
  and pooling characterizations (`crossModel_separating`, `crossModel_pooling`).
* `exercise_13_C_3`: in the best separating equilibrium (`(θ_L, 0)`, `(θ_H, ẽ = 1)`) banning
  signaling (everybody gets `(E[θ], 0) = (4/3, 0)`) makes the high type worse off, while the
  cross-subsidizing wage schedule `ŵ_L = 11/10` for `e < 71/100`, `ŵ_H = 9/5` for `e ≥ 71/100`
  makes both types strictly better off, with firms breaking even on average.

Departure. With linear indifference curves for both types (the exercise's hint, e.g.
`c(e, θ) = e/θ`) a cross-subsidy that improves on the best separating equilibrium exists exactly
when banning does, because all payoffs are linear in the subsidy; the example therefore keeps
the low type's curve linear and makes the high type's strictly convex (`c_{ee} > 0` fails for
the low type; the chapter's results do not use it).
-/

namespace MWG.AdverseSelection

open Set

namespace SigModel

/-- **Exercise 13.C.3** (MWG, p. 459). The model of the example. -/
noncomputable def crossModel : SigModel where
  θL := 1
  θH := 2
  lam := 1 / 3
  r := 0
  c := fun e θ => (2 - θ) * e + (θ - 1) * (e ^ 2 / (1 + e))

theorem crossModel_cL (e : ℝ) : crossModel.c e crossModel.θL = e := by
  simp [crossModel]; ring

theorem crossModel_cH (e : ℝ) : crossModel.c e crossModel.θH = e ^ 2 / (1 + e) := by
  simp [crossModel]; norm_num

theorem crossModel_cH_lt {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    a ^ 2 / (1 + a) < b ^ 2 / (1 + b) := by
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith [mul_pos (sub_pos.2 hab) (by nlinarith : 0 < a + b + a * b)]

/-- **Exercise 13.C.3** (MWG, p. 459). The example satisfies the assumptions of Section 13.C. -/
theorem crossModel_valid : crossModel.Valid where
  θL_pos := by norm_num [crossModel]
  lt := by norm_num [crossModel]
  lam_pos := by norm_num [crossModel]
  lam_lt := by norm_num [crossModel]
  r_nonneg := by norm_num [crossModel]
  r_lt := by norm_num [crossModel]
  c_zero := fun θ => by simp [crossModel]
  c_mono := fun b => by
    cases b
    · intro a _ b _ hab; simp only [θ_false, crossModel_cL]; exact hab
    · intro a ha b _ hab; simp only [θ_true, crossModel_cH]; exact crossModel_cH_lt ha hab
  c_cont := fun b => by
    cases b
    · simp only [θ_false, crossModel_cL]; exact continuousOn_id
    · simp only [θ_true, crossModel_cH]
      exact ((continuous_pow 2).continuousOn).div (continuous_const.add continuous_id).continuousOn
        fun x hx => by have : (0 : ℝ) ≤ x := hx; positivity
  sc := fun e e' he hlt => by
    rw [crossModel_cH, crossModel_cH, crossModel_cL, crossModel_cL]
    have hne' : (1 + e') ≠ 0 := by linarith
    have hne : (1 + e) ≠ 0 := by linarith
    have h1 : e' - e' ^ 2 / (1 + e') = e' / (1 + e') := by field_simp; ring
    have h2 : e - e ^ 2 / (1 + e) = e / (1 + e) := by field_simp; ring
    have : e / (1 + e) < e' / (1 + e') := by
      rw [div_lt_div_iff₀ (by linarith) (by linarith)]; nlinarith
    linarith

/-- **Section 13.C** (MWG, pp. 454-455), an instance: in `crossModel` the best separating
equilibrium `(e*(θ_L), e*(θ_H)) = (0, ẽ) = (0, 1)` is a PBE. -/
theorem crossModel_separating :
    ∃ μ wO, crossModel.IsPBE (fun b => if b then 1 else 0) μ wO ∧
      Separating fun b : Bool => if b then (1 : ℝ) else 0 := by
  have h := (separating_iff crossModel_valid (e := 1) zero_le_one).2 (by
    rw [crossModel_cL, crossModel_cH]; simp [crossModel]; norm_num)
  obtain ⟨μ, hμ, hsep⟩ := h
  exact ⟨μ, _, crossModel_valid.isPBE_of_isPBERed hμ, hsep⟩

/-- **Section 13.C** (MWG, pp. 456-457), an instance: pooling at `e = 0` is a PBE outcome. -/
theorem crossModel_pooling : ∃ μ, crossModel.IsPBERed (fun _ => 0) μ := by
  refine (pooling_iff crossModel_valid le_rfl).2 ?_
  simp [crossModel, Eθ]; norm_num

/-- **Exercise 13.C.3** (MWG, p. 459), the cross-subsidizing wage schedule of Figure 13.C.11. -/
noncomputable def crossWage (e : ℝ) : ℝ := if 71 / 100 ≤ e then 9 / 5 else 11 / 10

/-- **Exercise 13.C.3** (MWG, p. 459). In `crossModel`:
(1) banning signaling (everyone at `(E[θ], 0)`) leaves the high type strictly worse off than in
the best separating equilibrium, so it is not a Pareto improvement;
(2) under the mandated schedule `crossWage` the low type optimally chooses `e = 0` and the high
type `e = 71/100`; both are strictly better off than in the best separating equilibrium
(`θ_L` and `θ_H - c(1, θ_H) = 3/2`), and firms break even on average (they lose on low types
and gain on high types). -/
theorem exercise_13_C_3 :
    crossModel.Eθ < crossModel.θH - crossModel.c 1 crossModel.θH ∧
      (∀ e, 0 ≤ e → crossWage e - crossModel.c e crossModel.θL ≤
        crossWage 0 - crossModel.c 0 crossModel.θL) ∧
      (∀ e, 0 ≤ e → crossWage e - crossModel.c e crossModel.θH ≤
        crossWage (71 / 100) - crossModel.c (71 / 100) crossModel.θH) ∧
      (1 - crossModel.lam) * (crossModel.θL - crossWage 0) +
        crossModel.lam * (crossModel.θH - crossWage (71 / 100)) = 0 ∧
      crossModel.θL < crossWage 0 - crossModel.c 0 crossModel.θL ∧
      crossModel.θH - crossModel.c 1 crossModel.θH <
        crossWage (71 / 100) - crossModel.c (71 / 100) crossModel.θH ∧
      crossModel.θL - crossWage 0 < 0 ∧ 0 < crossModel.θH - crossWage (71 / 100) := by
  simp only [crossModel_cL, crossModel_cH]
  refine ⟨by simp [crossModel, Eθ]; norm_num, fun e he => ?_, fun e he => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold crossWage; split_ifs with h <;> norm_num <;> linarith
  · have hv : (71 / 100 : ℝ) ^ 2 / (1 + 71 / 100) = 5041 / 17100 := by norm_num
    have hw : crossWage (71 / 100) = 9 / 5 := by simp [crossWage]
    rw [hv, hw]
    unfold crossWage
    split_ifs with h
    · have hm : (71 / 100 : ℝ) ^ 2 / (1 + 71 / 100) ≤ e ^ 2 / (1 + e) := by
        rcases eq_or_lt_of_le h with h' | h'
        · rw [h']
        · exact (crossModel_cH_lt (by norm_num) h').le
      rw [hv] at hm
      norm_num
      linarith
    · have : 0 ≤ e ^ 2 / (1 + e) := by positivity
      norm_num
      linarith
  · simp [crossModel, crossWage]; norm_num
  · simp [crossModel, crossWage]; norm_num
  · simp [crossModel, crossWage]; norm_num
  · simp [crossModel, crossWage]; norm_num
  · simp [crossModel, crossWage]; norm_num

end SigModel

end MWG.AdverseSelection
