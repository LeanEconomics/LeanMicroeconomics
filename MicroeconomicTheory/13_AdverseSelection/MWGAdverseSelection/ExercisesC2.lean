/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGAdverseSelection.Signaling

/-!
# Exercise 13.C.2: productive education

MWG, Exercise 13.C.2, p. 475. The two-type signaling model of Section 13.C (`SigModel`,
`SigModel.Valid`) with `r(θ_L) = r(θ_H) = 0`, but a worker of type `θ` with education `e`
produces `θ(1 + μe)`, `μ > 0`.

The game is that of Section 13.C with the firms' expected productivity after `e` now
`(μ(e)θ_H + (1 - μ(e))θ_L)(1 + μe)` (`SigModel.prodWage`; here the belief is called `bel` and
`μ` is the productivity parameter). `SigModel.IsPBEProd` is the PBE with the Chapter 8 wage game
after every `e`; `SigModel.exists_isPBEProd_iff` reduces it, by `bertrand_wage`, to
`SigModel.IsPBEProdRed` (wage = expected productivity).

The full information outcome: type `θ` chooses `e` to maximise `θ(1 + μe) - c(e, θ)`
(`SigModel.fullPay`, `SigModel.IsFullInfoChoice`).

* `exercise_13_C_2_separating`: `(e_L, e_H)`, `e_L ≠ e_H`, is a separating PBE iff `e_L` is the
  low type's full information choice, the low type does not want to mimic
  (`θ_H(1 + μe_H) - c(e_H, θ_L) ≤` its full information payoff), and the high type prefers
  `e_H` to being taken for a low type at any `e`.
* `exercise_13_C_2_full_info`: if the high type's full information choice already deters
  mimicking, the full information outcome is a separating PBE.
* `exercise_13_C_2_distorted`: otherwise the high type is strictly worse off in every
  separating PBE than under full information.
* `exercise_13_C_2_pooling`: pooling at `e_p` is a PBE iff for both types
  `E[θ](1 + μe_p) - c(e_p, θ) ≥ θ_L(1 + μe) - c(e, θ)` for all `e ≥ 0`; in it the low type does
  at least as well as under full information (`exercise_13_C_2_pooling_low`).
* `exercise_13_C_2_instance`: `θ_L = 1`, `θ_H = 2`, `λ = 1/2`, `μ = 1`, `c(e, θ) = e²/θ`: full
  information `e = 1/2, 2`; the full information outcome is not a PBE, `(1/2, 3)` is a
  separating PBE with the high type strictly worse off, and pooling at `1/2` is a PBE.
-/

namespace MWG.AdverseSelection

open MWG.SimultaneousMoveGames

namespace SigModel

/-- **Exercise 13.C.2** (MWG, p. 475). Expected productivity `(bθ_H + (1 - b)θ_L)(1 + μe)` of a
worker with education `e` believed to be of high ability with probability `b`. -/
def prodWage (M : SigModel) (μ b e : ℝ) : ℝ := M.expProd b * (1 + μ * e)

/-- **Exercise 13.C.2** (MWG, p. 475). A type's payoff from `e` against the wage schedule
`prodWage μ (bel e) e`. -/
def prodPay (M : SigModel) (μ : ℝ) (bel : ℝ → ℝ) (t : Bool) (e : ℝ) : ℝ :=
  M.prodWage μ (bel e) e - M.c e (M.θ t)

/-- **Exercise 13.C.2** (MWG, p. 475). A pure strategy PBE of the productive education game:
education choices, beliefs, and after every `e` a Nash equilibrium of the firms' wage game with
expected productivity `prodWage μ (bel e) e`. -/
def IsPBEProd (M : SigModel) (μ : ℝ) (eS : Bool → ℝ) (bel : ℝ → ℝ) (wO : ℝ → Fin 2 → ℝ) :
    Prop :=
  (∀ t, 0 ≤ eS t) ∧ (∀ e, 0 ≤ bel e ∧ bel e ≤ 1) ∧
    (∀ t e, 0 ≤ e → M.workerPay t (wO e) e ≤ M.workerPay t (wO (eS t)) (eS t)) ∧
    M.BayesOnPath eS bel ∧
    ∀ e, 0 ≤ e → IsNashEquilibrium (wageGame (M.offerProfit (M.prodWage μ (bel e) e))) (wO e)

/-- **Exercise 13.C.2** (MWG, p. 475). The reduced form: the wage is the expected productivity. -/
def IsPBEProdRed (M : SigModel) (μ : ℝ) (eS : Bool → ℝ) (bel : ℝ → ℝ) : Prop :=
  (∀ t, 0 ≤ eS t) ∧ (∀ e, 0 ≤ bel e ∧ bel e ≤ 1) ∧
    (∀ t e, 0 ≤ e → M.prodPay μ bel t e ≤ M.prodPay μ bel t (eS t)) ∧ M.BayesOnPath eS bel

/-- **Exercise 13.C.2** (MWG, p. 475). The full information payoff `θ(1 + μe) - c(e, θ)`. -/
def fullPay (M : SigModel) (μ : ℝ) (t : Bool) (e : ℝ) : ℝ := M.θ t * (1 + μ * e) - M.c e (M.θ t)

/-- **Exercise 13.C.2** (MWG, p. 475). `e` is a full information choice of type `t`. -/
def IsFullInfoChoice (M : SigModel) (μ : ℝ) (t : Bool) (e : ℝ) : Prop :=
  0 ≤ e ∧ ∀ e', 0 ≤ e' → M.fullPay μ t e' ≤ M.fullPay μ t e

variable {M : SigModel}

theorem Valid.prodWage_nonneg (hM : M.Valid) {μ b e : ℝ} (hμ : 0 < μ) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (he : 0 ≤ e) : 0 ≤ M.prodWage μ b e :=
  mul_nonneg (hM.θL_pos.le.trans (hM.expProd_mem hb hb1).1) (by nlinarith)

/-- The wage after `e` is at least `θ_L(1 + μe)`. -/
theorem Valid.prodWage_ge (hM : M.Valid) {μ b e : ℝ} (hμ : 0 < μ) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (he : 0 ≤ e) : M.θL * (1 + μ * e) ≤ M.prodWage μ b e :=
  mul_le_mul_of_nonneg_right (hM.expProd_mem hb hb1).1 (by nlinarith)

/-- **Exercise 13.C.2** (MWG, p. 475). With `r = 0`, strategies and beliefs are part of a PBE iff
they form a reduced-form PBE. -/
theorem Valid.exists_isPBEProd_iff (hM : M.Valid) (hr : M.r = 0) {μ : ℝ} (hμ : 0 < μ)
    (eS : Bool → ℝ) (bel : ℝ → ℝ) :
    (∃ wO, M.IsPBEProd μ eS bel wO) ↔ M.IsPBEProdRed μ eS bel := by
  constructor
  · rintro ⟨wO, h0, hb, hopt, hB, hNE⟩
    have hw : ∀ e, 0 ≤ e →
        max (max (wO e 0) (wO e 1)) M.r = M.prodWage μ (bel e) e := fun e he => by
      rw [M.bertrand_wage (hM.prodWage_nonneg hμ (hb e).1 (hb e).2 he) _ (hNE e he), hr,
        max_eq_left (hM.prodWage_nonneg hμ (hb e).1 (hb e).2 he)]
    refine ⟨h0, hb, fun t e he => ?_, hB⟩
    have := hopt t e he
    unfold workerPay at this
    rw [hw e he, hw _ (h0 t)] at this
    exact this
  · rintro ⟨h0, hb, hopt, hB⟩
    have hw : ∀ e, 0 ≤ e → max (max (M.bertrandOffer (M.prodWage μ (bel e) e) 0)
        (M.bertrandOffer (M.prodWage μ (bel e) e) 1)) M.r = M.prodWage μ (bel e) e :=
      fun e he => by
        rw [bertrandOffer_max, hr, max_eq_left (hM.prodWage_nonneg hμ (hb e).1 (hb e).2 he)]
    refine ⟨fun e => M.bertrandOffer (M.prodWage μ (bel e) e), h0, hb, fun t e he => ?_, hB,
      fun e he => M.bertrandOffer_nash (hM.prodWage_nonneg hμ (hb e).1 (hb e).2 he)⟩
    unfold workerPay
    rw [hw e he, hw _ (h0 t)]
    exact hopt t e he

/-- **Exercise 13.C.2** (MWG, p. 475). Separating PBE: `(e_L, e_H)` with `e_L ≠ e_H` is the
outcome of a PBE iff (i) `e_L` is the low type's full information choice, (ii) the low type does
not gain by mimicking, `θ_H(1 + μe_H) - c(e_H, θ_L) ≤ θ_L(1 + μe_L) - c(e_L, θ_L)`, and (iii)
`θ_L(1 + μe) - c(e, θ_H) ≤ θ_H(1 + μe_H) - c(e_H, θ_H)` for every `e ≥ 0`. -/
theorem exercise_13_C_2_separating (hM : M.Valid) {μ : ℝ} (hμ : 0 < μ) {eL eH : ℝ}
    (hL : 0 ≤ eL) (hH : 0 ≤ eH) (hne : eL ≠ eH) :
    (∃ bel, M.IsPBEProdRed μ (fun t => if t then eH else eL) bel) ↔
      M.IsFullInfoChoice μ false eL ∧
        M.θH * (1 + μ * eH) - M.c eH M.θL ≤ M.fullPay μ false eL ∧
        ∀ e, 0 ≤ e → M.θL * (1 + μ * e) - M.c e M.θH ≤ M.fullPay μ true eH := by
  constructor
  · rintro ⟨bel, -, hb, hopt, hB⟩
    obtain ⟨h1, h0⟩ := hB.1 (by simpa using hne)
    simp only [ite_true, Bool.false_eq_true, ite_false] at h1 h0 hopt
    have hlow : M.prodPay μ bel false eL = M.fullPay μ false eL := by
      simp [prodPay, fullPay, prodWage, h0, expProd_zero, θ_false]
    have hhigh : M.prodPay μ bel true eH = M.fullPay μ true eH := by
      simp [prodPay, fullPay, prodWage, h1, expProd_one, θ_true]
    refine ⟨⟨hL, fun e he => ?_⟩, ?_, fun e he => ?_⟩
    · have := hopt false e he
      have hg := hM.prodWage_ge hμ (hb e).1 (hb e).2 he
      simp only [Bool.false_eq_true, ite_false] at this
      rw [hlow] at this
      unfold prodPay at this
      unfold fullPay at this ⊢
      rw [θ_false] at this ⊢
      linarith
    · have := hopt false eH hH
      simp only [Bool.false_eq_true, ite_false] at this
      rw [hlow] at this
      simpa [prodPay, prodWage, h1, expProd_one, θ_false] using this
    · have := hopt true e he
      have hg := hM.prodWage_ge hμ (hb e).1 (hb e).2 he
      simp only [ite_true] at this
      rw [hhigh] at this
      unfold prodPay at this
      rw [θ_true] at this
      linarith
  · rintro ⟨⟨-, hfi⟩, hmim, hhi⟩
    refine ⟨fun x => if x = eH then 1 else 0, ?_, fun x => ?_, fun t e he => ?_, ?_, ?_⟩
    · intro t; cases t <;> simpa
    · dsimp only
      split_ifs <;> norm_num
    · cases t
      · simp only [Bool.false_eq_true, ite_false]
        by_cases heH : e = eH
        · subst heH
          simpa [prodPay, prodWage, hne, expProd_one, expProd_zero, θ_false, fullPay] using hmim
        · have := hfi e he
          simpa [prodPay, prodWage, heH, hne, expProd_zero, θ_false, fullPay] using this
      · simp only [ite_true]
        by_cases heH : e = eH
        · rw [heH]
        · have := hhi e he
          simpa [prodPay, prodWage, heH, expProd_zero, expProd_one, θ_true, fullPay] using this
    · intro hsep
      simp only [ite_true, Bool.false_eq_true, ite_false, hne, and_self]
    · intro hpool
      simp only [ite_true, Bool.false_eq_true, ite_false] at hpool
      exact absurd hpool hne

/-- **Exercise 13.C.2** (MWG, p. 475). If the full information choices `e_L**`, `e_H**` are such
that the low type does not want to mimic `e_H**`, the full information outcome is a separating
PBE outcome. -/
theorem exercise_13_C_2_full_info (hM : M.Valid) {μ : ℝ} (hμ : 0 < μ) {eL eH : ℝ}
    (hL : M.IsFullInfoChoice μ false eL) (hH : M.IsFullInfoChoice μ true eH)
    (hmim : M.θH * (1 + μ * eH) - M.c eH M.θL ≤ M.fullPay μ false eL) :
    eL ≠ eH ∧ ∃ bel, M.IsPBEProdRed μ (fun t => if t then eH else eL) bel := by
  have hne : eL ≠ eH := by
    rintro rfl
    unfold fullPay at hmim
    rw [θ_false] at hmim
    have : 0 < 1 + μ * eL := by nlinarith [hL.1]
    nlinarith [hM.lt]
  refine ⟨hne, (exercise_13_C_2_separating hM hμ hL.1 hH.1 hne).2 ⟨hL, hmim, fun e he => ?_⟩⟩
  have := hH.2 e he
  unfold fullPay at this ⊢
  rw [θ_true] at this ⊢
  have : M.θL * (1 + μ * e) ≤ M.θH * (1 + μ * e) :=
    mul_le_mul_of_nonneg_right hM.lt.le (by nlinarith)
  linarith

/-- **Exercise 13.C.2** (MWG, p. 475). If no full information choice of the high type deters the
low type from mimicking, the high type is strictly worse off in every separating PBE than under
full information (the low type gets exactly its full information payoff,
`exercise_13_C_2_separating`). -/
theorem exercise_13_C_2_distorted (hM : M.Valid) {μ : ℝ} (hμ : 0 < μ) {eL eH eHs : ℝ}
    (hL : 0 ≤ eL) (hH : 0 ≤ eH) (hne : eL ≠ eH)
    (hpbe : ∃ bel, M.IsPBEProdRed μ (fun t => if t then eH else eL) bel)
    (hHs : M.IsFullInfoChoice μ true eHs)
    (hno : ∀ e, M.IsFullInfoChoice μ true e →
      M.fullPay μ false eL < M.θH * (1 + μ * e) - M.c e M.θL) :
    M.fullPay μ true eH < M.fullPay μ true eHs := by
  obtain ⟨-, hmim, -⟩ := (exercise_13_C_2_separating hM hμ hL hH hne).1 hpbe
  rcases eq_or_lt_of_le (hHs.2 eH hH) with heq | hlt
  · have hfi : M.IsFullInfoChoice μ true eH :=
      ⟨hH, fun e' he' => heq ▸ hHs.2 e' he'⟩
    exact absurd hmim (not_le.2 (hno eH hfi))
  · exact hlt

/-- **Exercise 13.C.2** (MWG, p. 475). Pooling PBE: both types choosing `e_p` is a PBE outcome iff
for each type `E[θ](1 + μe_p) - c(e_p, θ) ≥ θ_L(1 + μe) - c(e, θ)` for all `e ≥ 0`. -/
theorem exercise_13_C_2_pooling (hM : M.Valid) {μ : ℝ} (hμ : 0 < μ) {ep : ℝ} (hp : 0 ≤ ep) :
    (∃ bel, M.IsPBEProdRed μ (fun _ => ep) bel) ↔
      ∀ t e, 0 ≤ e → M.θL * (1 + μ * e) - M.c e (M.θ t) ≤
        M.Eθ * (1 + μ * ep) - M.c ep (M.θ t) := by
  constructor
  · rintro ⟨bel, -, hb, hopt, hB⟩ t e he
    have hlam := hB.2 rfl
    have := hopt t e he
    have hg := hM.prodWage_ge hμ (hb e).1 (hb e).2 he
    unfold prodPay at this
    rw [show M.prodWage μ (bel ep) ep = M.Eθ * (1 + μ * ep) by
      rw [prodWage, hlam, expProd_lam]] at this
    linarith
  · intro h
    refine ⟨fun x => if x = ep then M.lam else 0, fun _ => hp, fun x => ?_, fun t e he => ?_,
      ⟨fun hs => absurd rfl hs, fun _ => by simp⟩⟩
    · dsimp only
      split_ifs
      · exact ⟨hM.lam_pos.le, hM.lam_lt.le⟩
      · norm_num
    · have hep : M.prodPay μ (fun x => if x = ep then M.lam else 0) t ep =
          M.Eθ * (1 + μ * ep) - M.c ep (M.θ t) := by
        simp [prodPay, prodWage, expProd_lam]
      rw [hep]
      by_cases he' : e = ep
      · subst he'; rw [hep]
      · have := h t e he
        simpa [prodPay, prodWage, he', expProd_zero] using this

/-- **Exercise 13.C.2** (MWG, p. 475). In a pooling PBE the low type does at least as well as
under full information. -/
theorem exercise_13_C_2_pooling_low (hM : M.Valid) {μ : ℝ} (hμ : 0 < μ) {ep : ℝ} (hp : 0 ≤ ep)
    (h : ∃ bel, M.IsPBEProdRed μ (fun _ => ep) bel) (e : ℝ) (he : 0 ≤ e) :
    M.fullPay μ false e ≤ M.Eθ * (1 + μ * ep) - M.c ep M.θL := by
  have := (exercise_13_C_2_pooling hM hμ hp).1 h false e he
  simpa [fullPay, θ_false] using this

/-- **Exercise 13.C.2**, the instance: `θ_L = 1`, `θ_H = 2`, `λ = 1/2`, `r = 0`,
`c(e, θ) = e²/θ`. -/
noncomputable def prodSigModel : SigModel where
  θL := 1
  θH := 2
  lam := 1 / 2
  r := 0
  c := fun e θ => e ^ 2 / θ

theorem prodSigModel_valid : prodSigModel.Valid where
  θL_pos := one_pos
  lt := one_lt_two
  lam_pos := by norm_num [prodSigModel]
  lam_lt := by norm_num [prodSigModel]
  r_nonneg := le_rfl
  r_lt := two_pos
  c_zero θ := by simp [prodSigModel]
  c_mono b := by
    have hθ : 0 < prodSigModel.θ b := by
      cases b <;> norm_num [θ, prodSigModel]
    intro x hx y hy hxy
    change x ^ 2 / prodSigModel.θ b < y ^ 2 / prodSigModel.θ b
    exact div_lt_div_of_pos_right (pow_lt_pow_left₀ hxy hx two_ne_zero) hθ
  c_cont b := (continuous_pow 2).continuousOn.div_const _
  sc e e' he hee' := by
    change e' ^ 2 / 2 - e ^ 2 / 2 < e' ^ 2 / 1 - e ^ 2 / 1
    nlinarith

/-- **Exercise 13.C.2**, instance (MWG, p. 475). With `μ = 1`: the full information choices are
`e_L** = 1/2` and `e_H** = 2` (`e_H** = 2` is the only one); the full information outcome is not
a PBE (the low type would mimic `e = 2`); `(1/2, 3)` is a separating PBE outcome, in which the
high type earns `7/2 < 4`, its full information payoff; pooling at `e = 1/2` is a PBE outcome. -/
theorem exercise_13_C_2_instance :
    prodSigModel.IsFullInfoChoice 1 false (1 / 2) ∧ prodSigModel.IsFullInfoChoice 1 true 2 ∧
      (∀ e, prodSigModel.IsFullInfoChoice 1 true e → e = 2) ∧
      ¬ (∃ bel, prodSigModel.IsPBEProdRed 1 (fun t => if t then 2 else 1 / 2) bel) ∧
      (∃ bel, prodSigModel.IsPBEProdRed 1 (fun t => if t then 3 else 1 / 2) bel) ∧
      prodSigModel.fullPay 1 true 3 < prodSigModel.fullPay 1 true 2 ∧
      (∃ bel, prodSigModel.IsPBEProdRed 1 (fun _ => 1 / 2) bel) ∧
      (∃ bel wO, prodSigModel.IsPBEProd 1 (fun _ => 1 / 2) bel wO) := by
  have hM := prodSigModel_valid
  have hfL : prodSigModel.IsFullInfoChoice 1 false (1 / 2) := ⟨by norm_num, fun e he => by
    simp only [fullPay, θ, prodSigModel, Bool.false_eq_true, ite_false]
    nlinarith [sq_nonneg (e - 1 / 2)]⟩
  have hfH : prodSigModel.IsFullInfoChoice 1 true 2 := ⟨by norm_num, fun e he => by
    simp only [fullPay, θ, prodSigModel, ite_true]
    nlinarith [sq_nonneg (e - 2)]⟩
  have huniq : ∀ e, prodSigModel.IsFullInfoChoice 1 true e → e = 2 := by
    intro e he
    have := he.2 2 (by norm_num)
    simp only [fullPay, θ, prodSigModel, ite_true] at this
    nlinarith [sq_nonneg (e - 2)]
  have hsep : ∃ bel, prodSigModel.IsPBEProdRed 1 (fun t => if t then 3 else 1 / 2) bel := by
    refine (exercise_13_C_2_separating hM one_pos (by norm_num) (by norm_num)
      (by norm_num)).2 ⟨hfL, ?_, fun e he => ?_⟩
    · simp only [fullPay, θ, prodSigModel, Bool.false_eq_true, ite_false]
      norm_num
    · simp only [fullPay, θ, prodSigModel, ite_true]
      nlinarith [sq_nonneg (e - 1)]
  have hpool : ∃ bel, prodSigModel.IsPBEProdRed 1 (fun _ => 1 / 2) bel := by
    refine (exercise_13_C_2_pooling hM one_pos (by norm_num)).2 fun t e he => ?_
    simp only [Eθ, prodSigModel]
    cases t
    · simp only [θ, Bool.false_eq_true, ite_false]
      nlinarith [sq_nonneg (e - 1 / 2)]
    · simp only [θ, ite_true]
      nlinarith [sq_nonneg (e - 1)]
  obtain ⟨bel, hbel⟩ := hpool
  refine ⟨hfL, hfH, huniq, fun h => ?_, hsep, ?_, ⟨bel, hbel⟩,
    ⟨bel, (hM.exists_isPBEProd_iff rfl one_pos _ _).2 hbel⟩⟩
  · obtain ⟨-, hmim, -⟩ :=
      (exercise_13_C_2_separating hM one_pos (by norm_num) (by norm_num) (by norm_num)).1 h
    simp only [fullPay, θ, prodSigModel, Bool.false_eq_true, ite_false] at hmim
    norm_num at hmim
  · exact exercise_13_C_2_distorted hM one_pos (by norm_num) (by norm_num) (by norm_num) hsep hfH
      fun e he => by
        rw [huniq e he]
        simp only [fullPay, θ, prodSigModel, Bool.false_eq_true, ite_false]
        norm_num

/-- **Exercise 13.C.2**, a second instance: `θ_L = 1`, `θ_H = 3`, `λ = 1/2`, `c(e, θ) = e²/θ`. -/
noncomputable def prodSigModel3 : SigModel where
  θL := 1
  θH := 3
  lam := 1 / 2
  r := 0
  c := fun e θ => e ^ 2 / θ

theorem prodSigModel3_valid : prodSigModel3.Valid where
  θL_pos := one_pos
  lt := by norm_num [prodSigModel3]
  lam_pos := by norm_num [prodSigModel3]
  lam_lt := by norm_num [prodSigModel3]
  r_nonneg := le_rfl
  r_lt := by norm_num [prodSigModel3]
  c_zero θ := by simp [prodSigModel3]
  c_mono b := by
    have hθ : 0 < prodSigModel3.θ b := by
      cases b <;> norm_num [θ, prodSigModel3]
    intro x hx y hy hxy
    change x ^ 2 / prodSigModel3.θ b < y ^ 2 / prodSigModel3.θ b
    exact div_lt_div_of_pos_right (pow_lt_pow_left₀ hxy hx two_ne_zero) hθ
  c_cont b := (continuous_pow 2).continuousOn.div_const _
  sc e e' he hee' := by
    change e' ^ 2 / 3 - e ^ 2 / 3 < e' ^ 2 / 1 - e ^ 2 / 1
    nlinarith

/-- **Exercise 13.C.2**, instance of `exercise_13_C_2_full_info` (MWG, p. 475). With `θ_H = 3`
and `μ = 1` the full information choices are `1/2` and `9/2`, and the low type does not want to
mimic `9/2`: the full information outcome is a separating PBE outcome. -/
theorem exercise_13_C_2_full_info_instance :
    prodSigModel3.IsFullInfoChoice 1 false (1 / 2) ∧ prodSigModel3.IsFullInfoChoice 1 true (9 / 2) ∧
      ∃ bel, prodSigModel3.IsPBEProdRed 1 (fun t => if t then 9 / 2 else 1 / 2) bel := by
  have hfL : prodSigModel3.IsFullInfoChoice 1 false (1 / 2) := ⟨by norm_num, fun e he => by
    simp only [fullPay, θ, prodSigModel3, Bool.false_eq_true, ite_false]
    nlinarith [sq_nonneg (e - 1 / 2)]⟩
  have hfH : prodSigModel3.IsFullInfoChoice 1 true (9 / 2) := ⟨by norm_num, fun e he => by
    simp only [fullPay, θ, prodSigModel3, ite_true]
    nlinarith [sq_nonneg (e - 9 / 2)]⟩
  refine ⟨hfL, hfH, (exercise_13_C_2_full_info prodSigModel3_valid one_pos hfL hfH ?_).2⟩
  simp only [fullPay, θ, prodSigModel3, Bool.false_eq_true, ite_false]
  norm_num

end SigModel

end MWG.AdverseSelection
