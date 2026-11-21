/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGAdverseSelection.ScreeningGen
import MWGAdverseSelection.ScreeningWelfare

/-!
# Exercise 13.D.1: screening with productive tasks

MWG, Exercise 13.D.1, p. 476 (the model of Section 13.D, pp. 460-465).

A type `θ` worker produces `θ(1 + μt)` at task level `t`, `μ > 0`. Contracts `(w, t)`, utility
`w - c(t, θ)`, home earnings `0`, the book's tie-breaking rules; the game is the
`ScrGame` `prodGame M μ` (`P b (w, t) = θ_b(1 + μt) - w`). Write `S_θ(t) = θ(1 + μt) - c(t, θ)`
for the surplus (`surplus`).

* `exercise_13_D_1` (the analogue of Proposition 13.D.2): in every SPNE both types work, both
  firms earn zero, no contract earns or loses money (`w_θ = θ(1 + μt_θ)`), the low type's task
  maximizes `S_L` (her full-information contract), the low type does not strictly prefer the high
  type's contract, the high type's task maximizes `S_H` among the tasks whose zero-profit contract
  the low type strictly dislikes, and there is no pooling.
* Observable types (the analogue of Proposition 13.D.1): `exercise_13_D_1_observable`,
  `exercise_13_D_1_observable_exists`: type `θ` gets `(θ(1 + μt), t)` with `t` maximizing `S_θ`.
* Comparison: `exercise_13_D_1_compare`. The low type gets her full-information utility; the high
  type at most hers, exactly hers when her full-information contract does not attract the low
  type, and strictly less when every full-information contract of hers does.
* Existence: `prod_isEq` (an existence criterion). Instances: `quadModel` with `μ = 4`
  (`c(t, θ) = t²/θ`): the full-information contracts `(9, 2)`, `(66, 8)` are the unique SPNE
  outcome (`exercise_13_D_1_fullinfo`); `linModel` with `μ = 1/8`: the unique SPNE outcome is
  `(1, 0)`, `(7/3, 4/3)`, the high type's task is distorted upward from `0` and she is worse off
  than with observable types (`exercise_13_D_1_distorted`); with `λ = 9/10` instead no SPNE exists
  (`exercise_13_D_1_nonexistence`).

Departure: the results hold for `μ ≥ 0` (`μ = 0` is Proposition 13.D.2).
-/

namespace MWG.AdverseSelection

namespace SigModel

variable {M : SigModel}

/-- **Exercise 13.D.1** (MWG, p. 476). The screening game with productive tasks: type `θ`
produces `θ(1 + μt)`. -/
noncomputable def prodGame (M : SigModel) (μ : ℝ) : ScrGame where
  U b k := M.util (M.θ b) k
  P b k := M.θ b * (1 + μ * k.2) - k.1
  ρ _ := 0
  key k := k.2
  lam := M.lam
  adm k := 0 ≤ k.2

/-- The surplus `S_θ(t) = θ(1 + μt) - c(t, θ)` of type `θ` at task level `t`. -/
def surplus (M : SigModel) (μ : ℝ) (b : Bool) (t : ℝ) : ℝ := M.θ b * (1 + μ * t) - M.c t (M.θ b)

theorem prodGame_inj (M : SigModel) (μ : ℝ) : (M.prodGame μ).Inj := by
  intro b k k' hu hk
  simp only [prodGame, util] at hu hk
  exact Prod.ext (by rw [hk] at hu; linarith) hk

/-- Profit = surplus - utility. -/
theorem prodGame_P (M : SigModel) (μ : ℝ) (b : Bool) (k : ℝ × ℝ) :
    (M.prodGame μ).P b k = M.surplus μ b k.2 - (M.prodGame μ).U b k := by
  simp only [prodGame, surplus, util]; ring

/-- **Lemma 13.D.1** for productive tasks: zero profits in every SPNE. -/
theorem prodGame_zero (hM : M.Valid) {μ : ℝ} {A₁ A₂ : Finset (ℝ × ℝ)}
    (h : (M.prodGame μ).IsEq A₁ A₂) :
    (M.prodGame μ).profit A₁ A₂ = 0 ∧ (M.prodGame μ).profit A₂ A₁ = 0 := by
  refine ScrGame.IsEq.zero (prodGame_inj M μ) hM.lam_pos.le hM.lam_lt.le
    (fun δ k => (k.1 + δ, k.2)) (fun _ _ _ hk => hk) (fun δ b k => ?_) (fun _ _ => rfl)
    (fun b k η hη => ⟨η / 2, half_pos hη, fun δ _ hδ => ?_⟩) h
  · simp only [prodGame, util]; ring
  · simp only [prodGame]; linarith

theorem θ_pos (hM : M.Valid) (b : Bool) : 0 < M.θ b := by
  cases b
  · exact hM.θL_pos
  · exact hM.θL_pos.trans hM.lt

/-- **Exercise 13.D.1** (MWG, p. 476). The SPNE of the screening game with productive tasks:
both types work; the low type takes `(θ_L(1 + μt_L), t_L)` with `t_L` maximizing her surplus
(her full-information contract); the high type takes `(θ_H(1 + μt_H), t_H)`, which the low type
does not strictly prefer, with `t_H` maximizing the high type's surplus among the tasks whose
zero-profit contract the low type strictly dislikes; no pooling; both firms earn zero. -/
theorem exercise_13_D_1 (hM : M.Valid) {μ : ℝ} (hμ : 0 ≤ μ) {A₁ A₂ : Finset (ℝ × ℝ)}
    (h : (M.prodGame μ).IsEq A₁ A₂) :
    ∃ kL kH, (M.prodGame μ).Chooses false (A₁ ∪ A₂) kL ∧
      (M.prodGame μ).Chooses true (A₁ ∪ A₂) kH ∧ 0 ≤ kL.2 ∧ 0 ≤ kH.2 ∧
      kL.1 = M.θL * (1 + μ * kL.2) ∧ kH.1 = M.θH * (1 + μ * kH.2) ∧
      (∀ t, 0 ≤ t → M.surplus μ false t ≤ M.surplus μ false kL.2) ∧
      M.util M.θL kH ≤ M.util M.θL kL ∧
      (∀ t, 0 ≤ t → M.θH * (1 + μ * t) - M.c t M.θL < M.util M.θL kL →
        M.surplus μ true t ≤ M.surplus μ true kH.2) ∧
      kL ≠ kH ∧ (M.prodGame μ).profit A₁ A₂ = 0 ∧ (M.prodGame μ).profit A₂ A₁ = 0 := by
  have hI := prodGame_inj M μ
  have hz := prodGame_zero hM h
  have hθL := hM.θL_pos
  have hθ := hM.lt
  have hl0 := hM.lam_pos
  have hl1 := hM.lam_lt
  have hval : ∀ k ∈ A₁ ∪ A₂, 0 ≤ k.2 := fun k hk => by
    rcases Finset.mem_union.1 hk with hk | hk
    · exact h.1 k hk
    · exact h.2.1 k hk
  have hUf : ∀ k, (M.prodGame μ).U false k = k.1 - M.c k.2 M.θL := fun _ => rfl
  have hUt : ∀ k, (M.prodGame μ).U true k = k.1 - M.c k.2 M.θH := fun _ => rfl
  have hPf : ∀ k, (M.prodGame μ).P false k = M.θL * (1 + μ * k.2) - k.1 := fun _ => rfl
  have hPt : ∀ k, (M.prodGame μ).P true k = M.θH * (1 + μ * k.2) - k.1 := fun _ => rfl
  have hSf : ∀ t, M.surplus μ false t = M.θL * (1 + μ * t) - M.c t M.θL := fun _ => rfl
  have hSt : ∀ t, M.surplus μ true t = M.θH * (1 + μ * t) - M.c t M.θH := fun _ => rfl
  have hρ : ∀ b, (M.prodGame μ).ρ b = 0 := fun _ => rfl
  -- a contract on the low type's zero-profit line, slightly cheaper, that the low type prefers
  have devL : ∀ t ε, 0 ≤ t → 0 < ε → 0 ≤ M.surplus μ false t - ε →
      (∀ k ∈ A₁ ∪ A₂, (M.prodGame μ).U false k < M.surplus μ false t - ε) → False := by
    intro t ε ht hε h0 hlt
    have hμt : 0 ≤ μ * t := mul_nonneg hμ ht
    refine ScrGame.IsEq.dev_false hI hl1 hl0.le h hz.1 (k' := (M.θL * (1 + μ * t) - ε, t)) ht
      ?_ (fun k hk => ?_) ?_ ?_
    · rw [hρ, hUf]; rw [hSf] at h0; linarith
    · have := hlt k (Finset.mem_union_right _ hk)
      simp only [hUf, hSf] at this ⊢; linarith
    · rw [hPf]; linarith
    · rw [hPt]; nlinarith
  -- the low type works
  obtain ⟨kL, hkL⟩ : ∃ kL, (M.prodGame μ).Chooses false (A₁ ∪ A₂) kL := by
    by_contra hno
    refine devL 0 (M.θL / 2) le_rfl (by linarith) ?_ fun k hk => ?_
    · rw [hSf, hM.c_zero]; linarith
    · rw [hSf, hM.c_zero]
      by_contra hle
      exact hno (ScrGame.exists_chooses false ⟨k, hk, by rw [hρ]; linarith⟩)
  have hLv := hval kL hkL.1
  -- the low type gets at least her maximal surplus
  have hLeff : ∀ t, 0 ≤ t → M.surplus μ false t ≤ (M.prodGame μ).U false kL := by
    intro t ht
    by_contra hlt
    rw [not_le] at hlt
    have h0 := hkL.2.1
    rw [hρ] at h0
    refine devL t ((M.surplus μ false t - (M.prodGame μ).U false kL) / 2) ht (by linarith)
      (by linarith)
      fun k hk => ?_
    have := hkL.2.2.1 k hk
    linarith
  -- the high type works
  obtain ⟨kH, hkH⟩ : ∃ kH, (M.prodGame μ).Chooses true (A₁ ∪ A₂) kH := by
    refine ScrGame.exists_chooses true ⟨kL, hkL.1, ?_⟩
    have h0 := hkL.2.1
    rw [hρ, hUf] at h0
    rw [hρ, hUt]
    linarith [hM.c_le hLv]
  have hHv := hval kH hkH.1
  -- no profit on the high type
  have hPH : (M.prodGame μ).P true kH ≤ 0 := by
    by_contra hpos
    rw [not_le] at hpos
    obtain ⟨k', hk'0, hH, hL, hw⟩ := exists_high_dev hM hHv hpos
    have hHL : M.util M.θL k' < M.util M.θL kL := hL.trans_le (hkL.2.2.1 kH hkH.1)
    have ht : kH.2 < k'.2 := by
      by_contra hle
      rw [not_lt] at hle
      simp only [util] at hH hL
      rcases eq_or_lt_of_le hle with he | hlt
      · rw [he] at hH hL; linarith
      · have := hM.sc k'.2 kH.2 hk'0 hlt
        linarith
    refine ScrGame.IsEq.dev_true hI hl0 h hz hkL hkH hk'0 hH hHL ?_
    rw [hPt]; rw [hPt] at hpos hw
    have : M.θH * (1 + μ * kH.2) ≤ M.θH * (1 + μ * k'.2) := by
      have := mul_le_mul_of_nonneg_left ht.le hμ
      nlinarith
    linarith
  have hPL : (M.prodGame μ).P false kL ≤ 0 := by
    rw [prodGame_P]; linarith [hLeff kL.2 hLv]
  -- both contracts break even
  have htot := ScrGame.profit_add (G := (M.prodGame μ)) A₁ A₂
  rw [hz.1, hz.2, ScrGame.typeProfit_add hI hkL, ScrGame.typeProfit_add hI hkH] at htot
  have hlam : (M.prodGame μ).lam = M.lam := rfl
  rw [hlam] at htot
  have hPL0 : (M.prodGame μ).P false kL = 0 := by nlinarith
  have hPH0 : (M.prodGame μ).P true kH = 0 := by nlinarith
  rw [hPf] at hPL0
  rw [hPt] at hPH0
  have hwL : kL.1 = M.θL * (1 + μ * kL.2) := by linarith
  have hwH : kH.1 = M.θH * (1 + μ * kH.2) := by linarith
  refine ⟨kL, kH, hkL, hkH, hLv, hHv, hwL, hwH, fun t ht => ?_, hkL.2.2.1 kH hkH.1,
    fun t ht hcon => ?_, fun he => ?_, hz.1, hz.2⟩
  · have := hLeff t ht
    rw [hUf, hwL] at this
    rw [hSf, hSf]; rw [hSf] at this; linarith
  · by_contra hlt
    rw [not_le] at hlt
    set ε := min ((M.surplus μ true t - M.surplus μ true kH.2) / 2)
      ((M.util M.θL kL - (M.θH * (1 + μ * t) - M.c t M.θL)) / 2)
    have hε1 : ε ≤ (M.surplus μ true t - M.surplus μ true kH.2) / 2 := min_le_left _ _
    have hε2 : ε ≤ (M.util M.θL kL - (M.θH * (1 + μ * t) - M.c t M.θL)) / 2 :=
      min_le_right _ _
    have hε : 0 < ε := lt_min (by linarith) (by linarith)
    refine ScrGame.IsEq.dev_true hI hl0 h hz hkL hkH (k' := (M.θH * (1 + μ * t) - ε, t)) ht
      ?_ ?_ ?_
    · rw [hUt, hUt, hwH]; rw [hSt, hSt] at hε1; simp only; linarith
    · rw [hUf, hUf]; simp only [util] at hε2 ⊢; linarith
    · rw [hPt]; simp only; linarith
  · have h2 : kL.2 = kH.2 := by rw [he]
    have hpos : 0 < 1 + μ * kL.2 := by nlinarith [mul_nonneg hμ hLv]
    rw [he, hwH, ← h2] at hwL
    nlinarith

/-- **Exercise 13.D.1** (MWG, p. 476), observable types (the analogue of Section 13.D's
Proposition 13.D.1): the game in which firms compete for type `θ_b` alone. -/
noncomputable def obsGame (M : SigModel) (μ : ℝ) (b : Bool) : ScrGame where
  U _ k := M.util (M.θ b) k
  P _ k := M.θ b * (1 + μ * k.2) - k.1
  ρ _ := 0
  key k := k.2
  lam := 1
  adm k := 0 ≤ k.2

theorem obsGame_inj (M : SigModel) (μ : ℝ) (b : Bool) : (M.obsGame μ b).Inj := by
  intro _ k k' hu hk
  simp only [obsGame, util] at hu hk
  exact Prod.ext (by rw [hk] at hu; linarith) hk

/-- **Exercise 13.D.1** (MWG, p. 476), observable types: in every SPNE of the game for type
`θ_b` she takes `(θ_b(1 + μt), t)` with `t` maximizing her surplus, and firms earn zero. -/
theorem exercise_13_D_1_observable (hM : M.Valid) {μ : ℝ} (b : Bool)
    {A₁ A₂ : Finset (ℝ × ℝ)} (h : (M.obsGame μ b).IsEq A₁ A₂) :
    ∃ k, (M.obsGame μ b).Chooses true (A₁ ∪ A₂) k ∧ 0 ≤ k.2 ∧ k.1 = M.θ b * (1 + μ * k.2) ∧
      (∀ t, 0 ≤ t → M.surplus μ b t ≤ M.surplus μ b k.2) ∧
      (M.obsGame μ b).profit A₁ A₂ = 0 ∧ (M.obsGame μ b).profit A₂ A₁ = 0 := by
  have hI := obsGame_inj M μ b
  have hθ := θ_pos hM b
  have hz : (M.obsGame μ b).profit A₁ A₂ = 0 ∧ (M.obsGame μ b).profit A₂ A₁ = 0 :=
    ScrGame.IsEq.zero hI zero_le_one le_rfl (fun δ k => (k.1 + δ, k.2)) (fun _ _ _ hk => hk)
      (fun δ _ k => by simp only [obsGame, util]; ring) (fun _ _ => rfl)
      (fun _ k η hη => ⟨η / 2, half_pos hη, fun δ _ hδ => by simp only [obsGame]; linarith⟩) h
  have hval : ∀ k ∈ A₁ ∪ A₂, 0 ≤ k.2 := fun k hk => by
    rcases Finset.mem_union.1 hk with hk | hk
    · exact h.1 k hk
    · exact h.2.1 k hk
  have hU : ∀ k, (M.obsGame μ b).U true k = k.1 - M.c k.2 (M.θ b) := fun _ => rfl
  have hP : ∀ k, (M.obsGame μ b).P true k = M.θ b * (1 + μ * k.2) - k.1 := fun _ => rfl
  have hS : ∀ t, M.surplus μ b t = M.θ b * (1 + μ * t) - M.c t (M.θ b) := fun _ => rfl
  have hprof : ∀ B other, (M.obsGame μ b).profit B other =
      (M.obsGame μ b).typeProfit true B other := fun B other => by
    simp [ScrGame.profit, obsGame]
  have dev : ∀ t ε, 0 ≤ t → 0 < ε → 0 ≤ M.surplus μ b t - ε →
      (∀ k ∈ A₁ ∪ A₂, (M.obsGame μ b).U true k < M.surplus μ b t - ε) → False := by
    intro t ε ht hε h0 hlt
    have hc := ScrGame.typeProfit_capture hI (b := true) (other := A₂)
      (Finset.mem_singleton_self (M.θ b * (1 + μ * t) - ε, t))
      (by change (0 : ℝ) ≤ _; rw [hU]; rw [hS] at h0; linarith)
      (fun k hk => by
        have := hlt k (Finset.mem_union_right _ hk)
        simp only [hU, hS] at this ⊢; linarith)
      (fun k hk hne => absurd (Finset.mem_singleton.1 hk) hne)
    have := h.2.2.1 {(M.θ b * (1 + μ * t) - ε, t)}
      (fun k hk => by rw [Finset.mem_singleton.1 hk]; exact ht)
    rw [hz.1, hprof, hc, hP] at this
    simp only at this
    linarith
  obtain ⟨k, hk⟩ : ∃ k, (M.obsGame μ b).Chooses true (A₁ ∪ A₂) k := by
    by_contra hno
    refine dev 0 (M.θ b / 2) le_rfl (by linarith) ?_ fun k hk => ?_
    · rw [hS, hM.c_zero]; linarith
    · rw [hS, hM.c_zero]
      by_contra hle
      exact hno (ScrGame.exists_chooses true ⟨k, hk, by change (0 : ℝ) ≤ _; linarith⟩)
  have hkv := hval k hk.1
  have heff : ∀ t, 0 ≤ t → M.surplus μ b t ≤ (M.obsGame μ b).U true k := by
    intro t ht
    by_contra hlt
    rw [not_le] at hlt
    have h0 : (0 : ℝ) ≤ (M.obsGame μ b).U true k := hk.2.1
    refine dev t ((M.surplus μ b t - (M.obsGame μ b).U true k) / 2) ht (by linarith) (by linarith)
      fun k' hk' => ?_
    have := hk.2.2.1 k' hk'
    linarith
  have htot := ScrGame.profit_add (G := (M.obsGame μ b)) A₁ A₂
  rw [hz.1, hz.2, ScrGame.typeProfit_add hI hk] at htot
  have hl : (M.obsGame μ b).lam = 1 := rfl
  rw [hl] at htot
  have hP0 : (M.obsGame μ b).P true k ≤ 0 := by
    have := heff k.2 hkv
    rw [hP]; rw [hU, hS] at this; linarith
  have hw : k.1 = M.θ b * (1 + μ * k.2) := by
    have hfalse : ∀ A B, (M.obsGame μ b).typeProfit false A B =
        (M.obsGame μ b).typeProfit true A B := fun _ _ => rfl
    rw [hfalse, hfalse, ScrGame.typeProfit_add hI hk] at htot
    rw [hP] at htot hP0
    linarith
  refine ⟨k, hk, hkv, hw, fun t ht => ?_, hz.1, hz.2⟩
  have := heff t ht
  rw [hU, hw] at this
  simp only [hS] at this ⊢; linarith

/-- **Exercise 13.D.1** (MWG, p. 476), observable types, existence: if `t*` maximizes type
`θ_b`'s surplus, both firms offering `(θ_b(1 + μt*), t*)` is an SPNE. -/
theorem exercise_13_D_1_observable_exists (hM : M.Valid) {μ : ℝ} (b : Bool)
    {ts : ℝ} (hts : 0 ≤ ts) (hmax : ∀ t, 0 ≤ t → M.surplus μ b t ≤ M.surplus μ b ts) :
    (M.obsGame μ b).IsEq {(M.θ b * (1 + μ * ts), ts)} {(M.θ b * (1 + μ * ts), ts)} := by
  have hI := obsGame_inj M μ b
  set ks : ℝ × ℝ := (M.θ b * (1 + μ * ts), ts)
  have hv : (M.obsGame μ b).Menu {ks} := fun k hk => by rw [Finset.mem_singleton.1 hk]; exact hts
  have hprof : ∀ B other, (M.obsGame μ b).profit B other =
      (M.obsGame μ b).typeProfit true B other := fun B other => by
    simp [ScrGame.profit, obsGame]
  have hS0 : 0 ≤ M.surplus μ b ts := by
    have := hmax 0 le_rfl
    simp only [surplus, hM.c_zero] at this ⊢
    linarith [θ_pos hM b]
  have hUs : (M.obsGame μ b).U true ks = M.surplus μ b ts := by simp [obsGame, util, surplus, ks]
  have hzero : (M.obsGame μ b).profit {ks} {ks} = 0 := by
    have hch : (M.obsGame μ b).Chooses true ({ks} ∪ {ks}) ks := by
      rw [Finset.union_self]
      exact ScrGame.chooses_of_strict (Finset.mem_singleton_self _)
        (by change (0 : ℝ) ≤ _; rw [hUs]; exact hS0)
        (fun k hk hne => absurd (Finset.mem_singleton.1 hk) hne)
    rw [hprof, ScrGame.typeProfit_of_chooses hI hch]
    simp [obsGame, ks]
  have hdev : ∀ B, (M.obsGame μ b).Menu B →
      (M.obsGame μ b).profit B {ks} ≤ (M.obsGame μ b).profit {ks} {ks} := by
    intro B hB
    rw [hzero, hprof]
    by_cases hex : ∃ k, (M.obsGame μ b).Chooses true (B ∪ {ks}) k
    · obtain ⟨k, hk⟩ := hex
      rw [ScrGame.typeProfit_of_chooses hI hk]
      have hge := hk.2.2.1 ks (by simp)
      have hk2 : 0 ≤ k.2 := by
        rcases Finset.mem_union.1 hk.1 with h' | h'
        · exact hB k h'
        · rw [Finset.mem_singleton.1 h']; exact hts
      have := hmax k.2 hk2
      have hPk : (M.obsGame μ b).P true k ≤ 0 := by
        rw [hUs] at hge
        simp only [obsGame, util, surplus] at hge this ⊢
        linarith
      exact mul_nonpos_of_nonneg_of_nonpos (SigModel.share_nonneg _ _ _) hPk
    · rw [ScrGame.typeProfit_of_not hex]
  exact ⟨hv, hv, hdev, hdev⟩

/-- **Exercise 13.D.1** (MWG, p. 476), comparison with observable types. In every SPNE the low
type gets her full-information utility `max S_L = S_L(t_L)`; if `t*` maximizes the high type's
surplus, the high type gets at most `S_H(t*)`, exactly `S_H(t*)` when the low type strictly
dislikes the contract `(θ_H(1 + μt*), t*)`, and strictly less when the low type weakly prefers
every such full-information contract of the high type to her own. -/
theorem exercise_13_D_1_compare (hM : M.Valid) {μ : ℝ} (hμ : 0 ≤ μ) {A₁ A₂ : Finset (ℝ × ℝ)}
    (h : (M.prodGame μ).IsEq A₁ A₂) {ts : ℝ} (hts : 0 ≤ ts)
    (hmax : ∀ t, 0 ≤ t → M.surplus μ true t ≤ M.surplus μ true ts) :
    ∃ kL kH, (M.prodGame μ).Chooses false (A₁ ∪ A₂) kL ∧
      (M.prodGame μ).Chooses true (A₁ ∪ A₂) kH ∧
      M.util M.θL kL = M.surplus μ false kL.2 ∧
      (∀ t, 0 ≤ t → M.surplus μ false t ≤ M.util M.θL kL) ∧
      M.util M.θH kH ≤ M.surplus μ true ts ∧
      (M.θH * (1 + μ * ts) - M.c ts M.θL < M.util M.θL kL →
        M.util M.θH kH = M.surplus μ true ts) ∧
      ((∀ t, 0 ≤ t → M.surplus μ true t = M.surplus μ true ts →
        M.util M.θL kL < M.θH * (1 + μ * t) - M.c t M.θL) →
        M.util M.θH kH < M.surplus μ true ts) := by
  obtain ⟨kL, kH, hkL, hkH, hLv, hHv, hwL, hwH, hLeff, hLH, hHopt, -, -, -⟩ :=
    exercise_13_D_1 hM hμ h
  have hUL : M.util M.θL kL = M.surplus μ false kL.2 := by
    simp only [util, surplus, θ_false, hwL]
  have hUH : M.util M.θH kH = M.surplus μ true kH.2 := by
    simp only [util, surplus, θ_true, hwH]
  refine ⟨kL, kH, hkL, hkH, hUL, fun t ht => hUL ▸ hLeff t ht, hUH ▸ hmax _ hHv,
    fun hlt => ?_, fun hall => ?_⟩
  · exact le_antisymm (hUH ▸ hmax _ hHv) (hUH ▸ hHopt ts hts hlt)
  · rcases lt_or_eq_of_le (hUH ▸ hmax _ hHv : M.util M.θH kH ≤ M.surplus μ true ts) with hl | he
    · exact hl
    · exfalso
      have := hall kH.2 hHv (hUH ▸ he)
      simp only [util] at hLH this
      rw [hwH] at hLH
      linarith

/-- **Exercise 13.D.1** (MWG, p. 476), an existence criterion. Let `t_L` maximize the low type's
surplus, and let the contracts `k_L = (θ_L(1 + μt_L), t_L)` and `k_H = (θ_H(1 + μt_H), t_H)`
self-select (the low type weakly prefers `k_L`, with the tie-breaking rule; the high type
strictly prefers `k_H`). If `t_H` is constrained optimal for the high type (every contract she
weakly prefers to `k_H` that the low type does not strictly prefer to `k_L` makes no profit on
her) and no contract that the high type weakly prefers and the low type strictly prefers is
profitable even when it attracts both types, then both firms offering `{k_L, k_H}` is an SPNE. -/
theorem prod_isEq (hM : M.Valid) {μ : ℝ} {tL tH : ℝ} (htL : 0 ≤ tL) (htH : 0 ≤ tH)
    (hLmax : ∀ t, 0 ≤ t → M.surplus μ false t ≤ M.surplus μ false tL)
    (hLH : M.θH * (1 + μ * tH) - M.c tH M.θL ≤ M.surplus μ false tL)
    (hLtie : M.θH * (1 + μ * tH) - M.c tH M.θL = M.surplus μ false tL → tL ≤ tH)
    (hHL : M.θL * (1 + μ * tL) - M.c tL M.θH < M.surplus μ true tH)
    (hcon : ∀ w t, 0 ≤ t → M.surplus μ true tH ≤ w - M.c t M.θH →
      w - M.c t M.θL ≤ M.surplus μ false tL → M.θH * (1 + μ * t) ≤ w)
    (hN : ∀ w t, 0 ≤ t → M.surplus μ true tH ≤ w - M.c t M.θH →
      M.surplus μ false tL < w - M.c t M.θL →
      (1 - M.lam) * (M.surplus μ false tL - (w - M.c t M.θL)) +
        M.lam * (M.θH * (1 + μ * t) - w) ≤ 0) :
    (M.prodGame μ).IsEq {(M.θL * (1 + μ * tL), tL), (M.θH * (1 + μ * tH), tH)}
      {(M.θL * (1 + μ * tL), tL), (M.θH * (1 + μ * tH), tH)} := by
  have hI := prodGame_inj M μ
  have hl0 := hM.lam_pos
  have hl1 := hM.lam_lt
  have hθL := hM.θL_pos
  have hθ := hM.lt
  set kL : ℝ × ℝ := (M.θL * (1 + μ * tL), tL) with hkLdef
  set kH : ℝ × ℝ := (M.θH * (1 + μ * tH), tH) with hkHdef
  set A : Finset (ℝ × ℝ) := {kL, kH} with hA
  have hUf : ∀ k, (M.prodGame μ).U false k = k.1 - M.c k.2 M.θL := fun _ => rfl
  have hUt : ∀ k, (M.prodGame μ).U true k = k.1 - M.c k.2 M.θH := fun _ => rfl
  have hPf : ∀ k, (M.prodGame μ).P false k = M.θL * (1 + μ * k.2) - k.1 := fun _ => rfl
  have hPt : ∀ k, (M.prodGame μ).P true k = M.θH * (1 + μ * k.2) - k.1 := fun _ => rfl
  have hSf : ∀ t, M.surplus μ false t = M.θL * (1 + μ * t) - M.c t M.θL := fun _ => rfl
  have hSt : ∀ t, M.surplus μ true t = M.θH * (1 + μ * t) - M.c t M.θH := fun _ => rfl
  have hρ : ∀ b, (M.prodGame μ).ρ b = 0 := fun _ => rfl
  have hSL0 : M.θL ≤ M.surplus μ false tL := by
    have := hLmax 0 le_rfl; rw [hSf, hM.c_zero] at this; linarith
  have hAv : (M.prodGame μ).Menu A := by
    intro k hk
    simp only [hA, Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · exact htL
    · exact htH
  have hmemL : kL ∈ A := by simp [hA]
  have hmemH : kH ∈ A := by simp [hA]
  have hULL : (M.prodGame μ).U false kL = M.surplus μ false tL := by rw [hUf, hSf]
  have hUHH : (M.prodGame μ).U true kH = M.surplus μ true tH := by rw [hUt, hSt]
  have hULH : (M.prodGame μ).U false kH = M.θH * (1 + μ * tH) - M.c tH M.θL := by rw [hUf]
  have hUHL : (M.prodGame μ).U true kL = M.θL * (1 + μ * tL) - M.c tL M.θH := by rw [hUt]
  have hchL : (M.prodGame μ).Chooses false (A ∪ A) kL := by
    rw [Finset.union_self]
    refine ⟨hmemL, by rw [hρ, hULL]; linarith, fun k hk => ?_, fun k hk hu => ?_⟩
    · simp only [hA, Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl
      · exact le_rfl
      · rw [hULH, hULL]; exact hLH
    · simp only [hA, Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl
      · exact le_rfl
      · rw [hULH, hULL] at hu; exact hLtie hu
  have hchH : (M.prodGame μ).Chooses true (A ∪ A) kH := by
    rw [Finset.union_self]
    have hcL := hM.c_le htL
    refine ScrGame.chooses_of_strict hmemH ?_ fun k hk hne => ?_
    · rw [hρ, hUHH]; rw [hSf] at hSL0; linarith
    · simp only [hA, Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl
      · rw [hUHL, hUHH]; exact hHL
      · exact absurd rfl hne
  have hzero : (M.prodGame μ).profit A A = 0 := by
    unfold ScrGame.profit
    rw [ScrGame.typeProfit_of_chooses hI hchL, ScrGame.typeProfit_of_chooses hI hchH, hPf, hPt]
    simp [hkLdef, hkHdef]
  have hval : ∀ B, (M.prodGame μ).Menu B → ∀ k ∈ B ∪ A, 0 ≤ k.2 := fun B hB k hk => by
    rcases Finset.mem_union.1 hk with hk | hk
    · exact hB k hk
    · exact hAv k hk
  have hdev : ∀ B, (M.prodGame μ).Menu B → (M.prodGame μ).profit B A ≤ 0 := by
    intro B hB
    -- the profit from the low type is never positive
    have hLle : ∀ k', (M.prodGame μ).Chooses false (B ∪ A) k' →
        (M.prodGame μ).P false k' ≤ M.surplus μ false tL - (M.prodGame μ).U false k' := by
      intro k' hk'
      have := hLmax k'.2 (hval B hB k' hk'.1)
      simp only [hPf, hUf, hSf] at this ⊢; linarith
    have hLnp : (M.prodGame μ).typeProfit false B A ≤ 0 := by
      by_cases hex : ∃ k', (M.prodGame μ).Chooses false (B ∪ A) k'
      · obtain ⟨k', hk'⟩ := hex
        rw [ScrGame.typeProfit_of_chooses hI hk']
        have h1 := hLle k' hk'
        have h2 := hk'.2.2.1 kL (Finset.mem_union_right _ hmemL)
        rw [hULL] at h2
        exact mul_nonpos_of_nonneg_of_nonpos (SigModel.share_nonneg _ _ _) (by linarith)
      · rw [ScrGame.typeProfit_of_not hex]
    unfold ScrGame.profit
    have hlam : (M.prodGame μ).lam = M.lam := rfl
    rw [hlam]
    by_cases hexH : ∃ k, (M.prodGame μ).Chooses true (B ∪ A) k
    · obtain ⟨k, hk⟩ := hexH
      rw [ScrGame.typeProfit_of_chooses hI hk]
      rcases le_or_gt ((M.prodGame μ).P true k) 0 with hP | hP
      · have := mul_nonpos_of_nonneg_of_nonpos (SigModel.share_nonneg B A k) hP
        nlinarith
      · have hkv := hval B hB k hk.1
        have hgeH := hk.2.2.1 kH (Finset.mem_union_right _ hmemH)
        rw [hUHH] at hgeH
        have hkA : k ∉ A := by
          intro hm
          simp only [hA, Finset.mem_insert, Finset.mem_singleton] at hm
          rcases hm with rfl | rfl
          · rw [hUHL] at hgeH; linarith
          · rw [hPt] at hP; simp [hkHdef] at hP
        have hkB : k ∈ B := by
          rcases Finset.mem_union.1 hk.1 with hm | hm
          · exact hm
          · exact absurd hm hkA
        have hsh : SigModel.share B A k = 1 := by simp [SigModel.share, hkB, hkA]
        rw [hUt] at hgeH
        have hLk : M.surplus μ false tL < k.1 - M.c k.2 M.θL := by
          by_contra hle
          rw [not_lt] at hle
          have := hcon k.1 k.2 hkv hgeH hle
          rw [hPt] at hP; linarith
        obtain ⟨k', hk'⟩ := ScrGame.exists_chooses (G := M.prodGame μ) false
          ⟨k, hk.1, by rw [hρ, hUf]; linarith⟩
        have hk'k := hk'.2.2.1 k hk.1
        have hk'A : k' ∉ A := by
          intro hm
          simp only [hA, Finset.mem_insert, Finset.mem_singleton] at hm
          rcases hm with rfl | rfl
          · rw [hULL, hUf] at hk'k; linarith
          · rw [hULH, hUf] at hk'k; linarith
        have hk'B : k' ∈ B := by
          rcases Finset.mem_union.1 hk'.1 with hm | hm
          · exact hm
          · exact absurd hm hk'A
        have hpL : (M.prodGame μ).typeProfit false B A = (M.prodGame μ).P false k' := by
          rw [ScrGame.typeProfit_of_chooses hI hk']
          simp [SigModel.share, hk'B, hk'A]
        have h1 := hLle k' hk'
        rw [hpL, hsh, one_mul]
        have hn := hN k.1 k.2 hkv hgeH hLk
        rw [hUf] at hk'k
        rw [hPt] at hP ⊢
        nlinarith
    · rw [ScrGame.typeProfit_of_not hexH]
      nlinarith
  refine ⟨hAv, hAv, fun B hB => ?_, fun B hB => ?_⟩ <;> rw [hzero] <;> exact hdev B hB

/-- **Exercise 13.D.1**, a model for the instances: `θ_L = 1`, `θ_H = 2`, `λ = 1/2`,
`c(t, θ) = t²/θ`. -/
noncomputable def quadModel : SigModel where
  θL := 1
  θH := 2
  lam := 1 / 2
  r := 0
  c := fun t θ => t ^ 2 / θ

theorem quadModel_cL (t : ℝ) : quadModel.c t quadModel.θL = t ^ 2 := by
  simp [quadModel]

theorem quadModel_cH (t : ℝ) : quadModel.c t quadModel.θH = t ^ 2 / 2 := by
  simp [quadModel]

theorem quadModel_valid : quadModel.Valid where
  θL_pos := by norm_num [quadModel]
  lt := by norm_num [quadModel]
  lam_pos := by norm_num [quadModel]
  lam_lt := by norm_num [quadModel]
  r_nonneg := by norm_num [quadModel]
  r_lt := by norm_num [quadModel]
  c_zero := fun θ => by simp [quadModel]
  c_mono := fun b => by
    cases b
    · intro a ha b _ hab
      simp only [θ_false, quadModel_cL]
      have : (0 : ℝ) ≤ a := ha
      nlinarith
    · intro a ha b _ hab
      simp only [θ_true, quadModel_cH]
      have : (0 : ℝ) ≤ a := ha
      nlinarith
  c_cont := fun b => by
    cases b
    · simp only [θ_false, quadModel_cL]; exact (continuous_pow 2).continuousOn
    · simp only [θ_true, quadModel_cH]; exact ((continuous_pow 2).div_const 2).continuousOn
  sc := fun e e' he hlt => by
    rw [quadModel_cH, quadModel_cH, quadModel_cL, quadModel_cL]
    nlinarith

/-- **Exercise 13.D.1** (MWG, p. 476), an instance where screening costs nothing: in
`quadModel` with `μ = 4` both firms offering the full-information contracts `{(9, 2), (66, 8)}`
is an SPNE, and in every SPNE the low type takes `(9, 2)` and the high type `(66, 8)`; these
maximize the types' surpluses (`5` and `34`), i.e. they are the observable-types outcome. -/
theorem exercise_13_D_1_fullinfo :
    (quadModel.prodGame 4).IsEq {(9, 2), (66, 8)} {(9, 2), (66, 8)} ∧
      (∀ A₁ A₂, (quadModel.prodGame 4).IsEq A₁ A₂ →
        (quadModel.prodGame 4).Chooses false (A₁ ∪ A₂) (9, 2) ∧
          (quadModel.prodGame 4).Chooses true (A₁ ∪ A₂) (66, 8)) ∧
      (∀ t, 0 ≤ t → quadModel.surplus 4 false t ≤ quadModel.surplus 4 false 2) ∧
      (∀ t, 0 ≤ t → quadModel.surplus 4 true t ≤ quadModel.surplus 4 true 8) := by
  have hv := quadModel_valid
  have hSf : ∀ t, quadModel.surplus 4 false t = 1 + 4 * t - t ^ 2 := fun t => by
    simp only [surplus, θ_false, quadModel_cL]; simp only [quadModel]; ring
  have hSt : ∀ t, quadModel.surplus 4 true t = 2 + 8 * t - t ^ 2 / 2 := fun t => by
    simp only [surplus, θ_true, quadModel_cH]; simp only [quadModel]; ring
  have hLmax : ∀ t, 0 ≤ t → quadModel.surplus 4 false t ≤ quadModel.surplus 4 false 2 :=
    fun t _ => by rw [hSf, hSf]; nlinarith [sq_nonneg (t - 2)]
  have hHmax : ∀ t, 0 ≤ t → quadModel.surplus 4 true t ≤ quadModel.surplus 4 true 8 :=
    fun t _ => by rw [hSt, hSt]; nlinarith [sq_nonneg (t - 8)]
  have hcL := quadModel_cL
  have hcH := quadModel_cH
  have hθL : quadModel.θL = 1 := rfl
  have hθH : quadModel.θH = 2 := rfl
  have hlam : quadModel.lam = 1 / 2 := rfl
  refine ⟨?_, fun A₁ A₂ h => ?_, hLmax, hHmax⟩
  · have := prod_isEq hv (μ := 4) (tL := 2) (tH := 8) (by norm_num) (by norm_num)
      hLmax ?_ ?_ ?_ ?_ ?_
    · convert this using 2 <;> simp [hθL, hθH] <;> norm_num
    all_goals simp only [hSf, hSt, hcL, hcH]
    all_goals simp only [hθL, hθH, hlam]
    · norm_num
    · norm_num
    · norm_num
    · intro w t _ h1 _; nlinarith [sq_nonneg (t - 8)]
    · intro w t _ h1 h2; nlinarith [sq_nonneg (t - 8)]
  · obtain ⟨kL, kH, hkL, hkH, hLv, hHv, hwL, hwH, hLeff, -, hHopt, -⟩ :=
      exercise_13_D_1 hv (μ := 4) (by norm_num) h
    have hx : kL.2 = 2 := by
      have := hLeff 2 (by norm_num)
      rw [hSf, hSf] at this
      nlinarith [sq_nonneg (kL.2 - 2)]
    have hkL' : kL = (9, 2) := by
      refine Prod.ext ?_ hx
      rw [hwL, hx, hθL]; norm_num
    have hULk : quadModel.util quadModel.θL kL = 5 := by
      rw [hkL']; simp only [util, hcL]; norm_num
    have hy : kH.2 = 8 := by
      have := hHopt 8 (by norm_num) (by rw [hULk, hcL, hθH]; norm_num)
      rw [hSt, hSt] at this
      nlinarith [sq_nonneg (kH.2 - 8)]
    have hkH' : kH = (66, 8) := by
      refine Prod.ext ?_ hy
      rw [hwH, hy, hθH]; norm_num
    exact ⟨hkL' ▸ hkL, hkH' ▸ hkH⟩

/-- **Exercise 13.D.1** (MWG, p. 476), an instance with distortion: in `linModel`
(`c(t, θ_L) = t`, `c(t, θ_H) = t/2`, `λ = 1/2`) with `μ = 1/8`, both firms offering
`{(1, 0), (7/3, 4/3)}` is an SPNE, and in every SPNE the low type takes `(1, 0)` and the high
type `(7/3, 4/3)`. With observable types the high type would choose `t = 0` and get `2`; here
she gets `5/3`. -/
theorem exercise_13_D_1_distorted :
    (linModel.prodGame (1 / 8)).IsEq {(1, 0), (7 / 3, 4 / 3)} {(1, 0), (7 / 3, 4 / 3)} ∧
      (∀ A₁ A₂, (linModel.prodGame (1 / 8)).IsEq A₁ A₂ →
        (linModel.prodGame (1 / 8)).Chooses false (A₁ ∪ A₂) (1, 0) ∧
          (linModel.prodGame (1 / 8)).Chooses true (A₁ ∪ A₂) (7 / 3, 4 / 3)) ∧
      (∀ t, 0 ≤ t → linModel.surplus (1 / 8) true t ≤ linModel.surplus (1 / 8) true 0) ∧
      linModel.util linModel.θH (7 / 3, 4 / 3) = 5 / 3 ∧
      linModel.surplus (1 / 8) true 0 = 2 := by
  have hv := linModel_valid
  have hcL := linModel_cL
  have hcH := linModel_cH
  have hθL : linModel.θL = 1 := rfl
  have hθH : linModel.θH = 2 := rfl
  have hlam : linModel.lam = 1 / 2 := rfl
  have hSf : ∀ t, linModel.surplus (1 / 8) false t = 1 - 7 * t / 8 := fun t => by
    simp only [surplus, θ_false, hcL]; rw [hθL]; ring
  have hSt : ∀ t, linModel.surplus (1 / 8) true t = 2 - t / 4 := fun t => by
    simp only [surplus, θ_true, hcH]; rw [hθH]; ring
  refine ⟨?_, fun A₁ A₂ h => ?_, fun t ht => by rw [hSt, hSt]; linarith, ?_, ?_⟩
  · have := prod_isEq hv (μ := 1 / 8) (tL := 0) (tH := 4 / 3) le_rfl
      (by norm_num) (fun t ht => by rw [hSf, hSf]; linarith) ?_ ?_ ?_ ?_ ?_
    · convert this using 2 <;> simp [hθL, hθH] <;> norm_num
    all_goals simp only [hSf, hSt, hcL, hcH]
    all_goals simp only [hθL, hθH, hlam]
    · norm_num
    · norm_num
    · norm_num
    · intro w t _ h1 h2; linarith
    · intro w t ht h1 h2
      rcases le_or_gt t (4 / 3) with h3 | h3 <;> linarith
  · obtain ⟨kL, kH, hkL, hkH, hLv, hHv, hwL, hwH, hLeff, hLH, hHopt, -⟩ :=
      exercise_13_D_1 hv (μ := 1 / 8) (by norm_num) h
    have hx : kL.2 = 0 := by
      have := hLeff 0 le_rfl
      rw [hSf, hSf] at this
      linarith
    have hkL' : kL = (1, 0) := by
      refine Prod.ext ?_ hx
      rw [hwL, hx, hθL]; norm_num
    have hULk : linModel.util linModel.θL kL = 1 := by
      rw [hkL']; simp only [util, hcL]; norm_num
    have hy1 : 4 / 3 ≤ kH.2 := by
      rw [hULk] at hLH
      simp only [util, hcL] at hLH
      rw [hwH, hθH] at hLH
      linarith
    have hy2 : kH.2 ≤ 4 / 3 := by
      by_contra hlt
      rw [not_le] at hlt
      have := hHopt ((kH.2 + 4 / 3) / 2) (by linarith)
        (by rw [hULk, hcL, hθH]; linarith)
      rw [hSt, hSt] at this
      linarith
    have hkH' : kH = (7 / 3, 4 / 3) := by
      have hy : kH.2 = 4 / 3 := le_antisymm hy2 hy1
      refine Prod.ext ?_ hy
      rw [hwH, hy, hθH]; norm_num
    exact ⟨hkL' ▸ hkL, hkH' ▸ hkH⟩
  · simp only [util, hcH]; norm_num
  · rw [hSt]; norm_num

/-- The linear model of `linModel` with `λ = 9/10`. -/
noncomputable def linModel9 : SigModel := { linModel with lam := 9 / 10 }

theorem linModel9_valid : linModel9.Valid where
  θL_pos := linModel_valid.θL_pos
  lt := linModel_valid.lt
  lam_pos := by norm_num [linModel9]
  lam_lt := by norm_num [linModel9]
  r_nonneg := linModel_valid.r_nonneg
  r_lt := linModel_valid.r_lt
  c_zero := linModel_valid.c_zero
  c_mono := linModel_valid.c_mono
  c_cont := linModel_valid.c_cont
  sc := linModel_valid.sc

/-- **Exercise 13.D.1** (MWG, p. 476), nonexistence: with `λ = 9/10` (and `μ = 1/8`) the pooling
contract `(9/5, 0)` breaks every candidate equilibrium: no SPNE exists. -/
theorem exercise_13_D_1_nonexistence :
    ¬ ∃ A₁ A₂, (linModel9.prodGame (1 / 8)).IsEq A₁ A₂ := by
  rintro ⟨A₁, A₂, h⟩
  have hv := linModel9_valid
  have hcL : ∀ t, linModel9.c t linModel9.θL = t := linModel_cL
  have hcH : ∀ t, linModel9.c t linModel9.θH = t / 2 := linModel_cH
  have hθL : linModel9.θL = 1 := rfl
  have hθH : linModel9.θH = 2 := rfl
  have hlam : linModel9.lam = 9 / 10 := rfl
  obtain ⟨kL, kH, hkL, hkH, hLv, hHv, hwL, hwH, -, hLH, -, -, hz, -⟩ :=
    exercise_13_D_1 hv (μ := 1 / 8) (by norm_num) h
  have hUL : linModel9.util linModel9.θL kL ≤ 1 := by
    simp only [util, hcL]; rw [hwL, hθL]; linarith
  have hUH : linModel9.util linModel9.θH kH ≤ 5 / 3 := by
    have h1 := hLH.trans hUL
    simp only [util, hcL, hcH] at h1 ⊢
    rw [hwH, hθH] at h1 ⊢
    linarith
  refine ScrGame.IsEq.dev_both (prodGame_inj _ _) h hz (k' := (9 / 5, 0)) le_rfl
    (fun b => ?_) (fun b k hk => ?_) ?_
  · change (0 : ℝ) ≤ _
    cases b <;> simp [prodGame, util, hv.c_zero] <;> norm_num
  · cases b
    · have := hkL.2.2.1 k (Finset.mem_union_right _ hk)
      change k.1 - linModel9.c k.2 linModel9.θL ≤ kL.1 - linModel9.c kL.2 linModel9.θL at this
      change k.1 - linModel9.c k.2 linModel9.θL < (9 / 5 : ℝ) - linModel9.c 0 linModel9.θL
      rw [hv.c_zero]
      simp only [util] at hUL; linarith
    · have := hkH.2.2.1 k (Finset.mem_union_right _ hk)
      change k.1 - linModel9.c k.2 linModel9.θH ≤ kH.1 - linModel9.c kH.2 linModel9.θH at this
      change k.1 - linModel9.c k.2 linModel9.θH < (9 / 5 : ℝ) - linModel9.c 0 linModel9.θH
      rw [hv.c_zero]
      simp only [util] at hUH; linarith
  · simp only [prodGame, θ_false, θ_true, hθL, hθH, hlam]; norm_num

/-- **Exercise 13.D.1** (MWG, p. 476), observable types, an instance: in `quadModel` with
`μ = 4` the low type's full-information contract `(9, 2)` is an SPNE of her game. -/
theorem exercise_13_D_1_observable_instance :
    (quadModel.obsGame 4 false).IsEq {(9, 2)} {(9, 2)} := by
  have h := exercise_13_D_1_observable_exists quadModel_valid (μ := 4) false (ts := 2)
    (by norm_num) fun t _ => by
      simp only [surplus, θ_false, quadModel_cL]; simp only [quadModel]
      nlinarith [sq_nonneg (t - 2)]
  have e : (quadModel.θ false * (1 + 4 * 2), (2 : ℝ)) = (9, 2) := by
    simp only [θ_false, quadModel]; norm_num
  rwa [e] at h

end SigModel

end MWG.AdverseSelection
