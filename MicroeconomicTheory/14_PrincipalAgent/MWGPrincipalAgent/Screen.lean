/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPrincipalAgent.Basic

/-!
# The two-type screening program

MWG, Section 14.C, pp. 494-499, problems (14.C.8) and (14.C.10); Appendix B, problem (14.BB.1);
Exercise 14.BB.1.

The owner (or firm) offers wage-effort pairs `(w_H, e_H)`, `(w_L, e_L)` with `e ≥ 0`; type `θ_i`
(probability `λ` for `θ_H`) gets `w - g(e, θ_i)`, and must get at least `c` (`c = v⁻¹(ū)` in
(14.C.8) for the infinitely risk-averse manager, `c = ū` in (14.C.10)). The owner's profit in state
`θ_i` is `π_i(e) - w`. This module proves the structure of the program using only that
`D(e) = g(e, θ_L) - g(e, θ_H)` vanishes at `0` and is strictly increasing on `[0, ∞)` (the
single-crossing property), and that the full-information efforts `e*_i` are the unique maximizers
of `S_i(e) = π_i(e) - g(e, θ_i)`, with `e*_L ≤ e*_H`. Derivative versions are in `HiddenInfo`.

* `lemma_14_C_1`: constraint (ii) is implied by (i) and (iii).
* `screen_Pi_le`, `screen_Pi_bind`: every contract satisfying (i) and (iii) earns at most
  `R(e_H, e_L) = λ S_H(e_H) + (1 - λ) S_L(e_L) - λ D(e_L) - c`, with equality iff (i) and (iii)
  bind; the binding contract `bind e_H e_L` attains it.
* `lemma_14_C_2`, `screen_iii_binds`: (i) and (iii) bind at an optimum.
* `lemma_14_C_3`: `e_L ≤ e*_L` and `e_H = e*_H`.
* `screen_opt_iff`: the optimal contracts are exactly `bind e*_H e_L` with `e_L` maximizing
  `Q(e) = (1 - λ) S_L(e) - λ D(e)` on `[0, ∞)`.
* `screen_iv_slack`, `screen_H_rent`, `screen_loss`: only (iii) binds (p. 497); the `θ_H` manager
  gets a rent; the owner loses relative to full information (Proposition 14.C.3).
* `screen_fb_violates_iii`: the full-information contract violates (iii) (p. 495).
* `exercise_14_BB_1`: the relaxed program without (iv) has the same solutions.
-/

namespace MWG.PrincipalAgent

open Set

/-- **(14.C.8), (14.C.10)** (MWG, pp. 494, 500). The data of the two-type screening program:
the owner's profit functions in the two states, the disvalue of effort `g(e, θ)`, the two states,
the probability `λ` of `θ_H`, and the reservation level `c` of `w - g(e, θ)`. -/
structure Screen where
  pH : ℝ → ℝ
  pL : ℝ → ℝ
  g : ℝ → ℝ → ℝ
  θL : ℝ
  θH : ℝ
  lam : ℝ
  c : ℝ

/-- A contract (revelation mechanism) `[(w_H, e_H), (w_L, e_L)]`. -/
structure HIContract where
  wH : ℝ
  eH : ℝ
  wL : ℝ
  eL : ℝ

namespace Screen

/-- The owner's expected profit `λ[π_H(e_H) - w_H] + (1 - λ)[π_L(e_L) - w_L]`. -/
def Pi (P : Screen) (K : HIContract) : ℝ :=
  P.lam * (P.pH K.eH - K.wH) + (1 - P.lam) * (P.pL K.eL - K.wL)

/-- Constraint (i): reservation utility in state `θ_L`. -/
def C1 (P : Screen) (K : HIContract) : Prop := P.c ≤ K.wL - P.g K.eL P.θL

/-- Constraint (ii): reservation utility in state `θ_H`. -/
def C2 (P : Screen) (K : HIContract) : Prop := P.c ≤ K.wH - P.g K.eH P.θH

/-- Constraint (iii): truth-telling in state `θ_H`. -/
def C3 (P : Screen) (K : HIContract) : Prop :=
  K.wL - P.g K.eL P.θH ≤ K.wH - P.g K.eH P.θH

/-- Constraint (iv): truth-telling in state `θ_L`. -/
def C4 (P : Screen) (K : HIContract) : Prop :=
  K.wH - P.g K.eH P.θL ≤ K.wL - P.g K.eL P.θL

/-- The feasible set of (14.C.8). -/
def Feas (P : Screen) (K : HIContract) : Prop :=
  0 ≤ K.eH ∧ 0 ≤ K.eL ∧ P.C1 K ∧ P.C2 K ∧ P.C3 K ∧ P.C4 K

/-- The feasible set of (14.BB.1): (14.C.8) without constraint (ii). -/
def Feas3 (P : Screen) (K : HIContract) : Prop := 0 ≤ K.eH ∧ 0 ≤ K.eL ∧ P.C1 K ∧ P.C3 K ∧ P.C4 K

/-- The relaxed feasible set of Exercise 14.BB.1: (14.BB.1) without constraint (iv). -/
def FeasRelax (P : Screen) (K : HIContract) : Prop := 0 ≤ K.eH ∧ 0 ≤ K.eL ∧ P.C1 K ∧ P.C3 K

/-- An optimal contract: a solution of (14.C.8). -/
def IsOpt (P : Screen) (K : HIContract) : Prop := P.Feas K ∧ ∀ K', P.Feas K' → P.Pi K' ≤ P.Pi K

/-- A solution of the relaxed program of Exercise 14.BB.1. -/
def IsOptRelax (P : Screen) (K : HIContract) : Prop :=
  P.FeasRelax K ∧ ∀ K', P.FeasRelax K' → P.Pi K' ≤ P.Pi K

/-- `D(e) = g(e, θ_L) - g(e, θ_H)`, the information rent per unit of `θ_L` effort. -/
def D (P : Screen) (e : ℝ) : ℝ := P.g e P.θL - P.g e P.θH

/-- The full-information surplus in state `θ_H`. -/
def SH (P : Screen) (e : ℝ) : ℝ := P.pH e - P.g e P.θH

/-- The full-information surplus in state `θ_L`. -/
def SL (P : Screen) (e : ℝ) : ℝ := P.pL e - P.g e P.θL

/-- The virtual surplus of the `θ_L` effort, `(1 - λ) S_L(e) - λ D(e)`. -/
def Q (P : Screen) (e : ℝ) : ℝ := (1 - P.lam) * P.SL e - P.lam * P.D e

/-- The profit bound `R(e_H, e_L) = λ S_H(e_H) + Q(e_L) - c`. -/
def R (P : Screen) (eH eL : ℝ) : ℝ := P.lam * P.SH eH + P.Q eL - P.c

/-- The contract in which (i) and (iii) bind. -/
def bind (P : Screen) (eH eL : ℝ) : HIContract :=
  ⟨P.c + P.D eL + P.g eH P.θH, eH, P.c + P.g eL P.θL, eL⟩

/-- Standing assumptions of the screening program: `0 < λ < 1`, and `D(0) = 0` with `D` strictly
increasing on `[0, ∞)` (the single-crossing property, p. 490). -/
structure Hyp (P : Screen) : Prop where
  lam_pos : 0 < P.lam
  lam_lt : P.lam < 1
  D_zero : P.D 0 = 0
  D_mono : StrictMonoOn P.D (Ici 0)

/-- `D(e) ≥ 0` for `e ≥ 0`, strictly for `e > 0`. -/
theorem screen_D_pos {P : Screen} (h : P.Hyp) {e : ℝ} (he : 0 < e) : 0 < P.D e := by
  have := h.D_mono (mem_Ici.2 le_rfl) (mem_Ici.2 he.le) he
  rwa [h.D_zero] at this

theorem screen_D_nonneg {P : Screen} (h : P.Hyp) {e : ℝ} (he : 0 ≤ e) : 0 ≤ P.D e := by
  rcases he.lt_or_eq with he | rfl
  · exact (screen_D_pos h he).le
  · rw [h.D_zero]

/-- **Lemma 14.C.1** (MWG, p. 495). Constraint (ii) can be ignored: a contract is feasible for
(14.C.8) iff it satisfies the other constraints. -/
theorem lemma_14_C_1 {P : Screen} (h : P.Hyp) (K : HIContract) : P.Feas K ↔ P.Feas3 K := by
  constructor
  · rintro ⟨h1, h2, h3, -, h5, h6⟩; exact ⟨h1, h2, h3, h5, h6⟩
  · rintro ⟨h1, h2, h3, h5, h6⟩
    refine ⟨h1, h2, h3, ?_, h5, h6⟩
    have := screen_D_nonneg h h2
    unfold C1 at h3; unfold C3 at h5; unfold D at this; unfold C2
    linarith

/-- Feasibility (in fact (iii) and (iv)) forces `e_L ≤ e_H` (MWG, p. 497; Appendix B, Step 4). -/
theorem screen_eL_le_eH {P : Screen} (h : P.Hyp) {K : HIContract} (hK : P.Feas3 K) :
    K.eL ≤ K.eH := by
  obtain ⟨h1, h2, -, h5, h6⟩ := hK
  have : P.D K.eL ≤ P.D K.eH := by unfold C3 at h5; unfold C4 at h6; unfold D; linarith
  exact (h.D_mono.le_iff_le h2 h1).1 this

/-- Every contract satisfying (i) and (iii) earns at most `R(e_H, e_L)`. -/
theorem screen_Pi_le {P : Screen} (h : P.Hyp) {K : HIContract} (h1 : P.C1 K) (h3 : P.C3 K) :
    P.Pi K ≤ P.R K.eH K.eL := by
  unfold C1 at h1; unfold C3 at h3
  have hl := h.lam_pos; have hl' := h.lam_lt
  have a : 0 ≤ P.lam * (K.wH - (P.c + P.D K.eL + P.g K.eH P.θH)) :=
    mul_nonneg hl.le (by unfold D; linarith)
  have b : 0 ≤ (1 - P.lam) * (K.wL - (P.c + P.g K.eL P.θL)) :=
    mul_nonneg (by linarith) (by linarith)
  unfold Pi R Q SH SL; nlinarith

/-- Equality in `screen_Pi_le` holds iff (i) and (iii) bind. -/
theorem screen_Pi_eq_iff {P : Screen} (h : P.Hyp) {K : HIContract} (h1 : P.C1 K)
    (h3 : P.C3 K) : P.Pi K = P.R K.eH K.eL ↔
      K.wL = P.c + P.g K.eL P.θL ∧ K.wH = P.c + P.D K.eL + P.g K.eH P.θH := by
  unfold C1 at h1; unfold C3 at h3
  have hl := h.lam_pos; have hl' := h.lam_lt
  constructor
  · intro heq
    have a : 0 ≤ P.lam * (K.wH - (P.c + P.D K.eL + P.g K.eH P.θH)) :=
      mul_nonneg hl.le (by unfold D; linarith)
    have b : 0 ≤ (1 - P.lam) * (K.wL - (P.c + P.g K.eL P.θL)) :=
      mul_nonneg (by linarith) (by linarith)
    have hsum : P.lam * (K.wH - (P.c + P.D K.eL + P.g K.eH P.θH)) +
        (1 - P.lam) * (K.wL - (P.c + P.g K.eL P.θL)) = 0 := by
      unfold Pi R Q SH SL at heq; linarith
    have ha : P.lam * (K.wH - (P.c + P.D K.eL + P.g K.eH P.θH)) = 0 := by linarith
    have hb : (1 - P.lam) * (K.wL - (P.c + P.g K.eL P.θL)) = 0 := by linarith
    rcases mul_eq_zero.1 ha with ha | ha
    · linarith
    rcases mul_eq_zero.1 hb with hb | hb
    · linarith
    constructor <;> linarith
  · rintro ⟨hL, hH⟩
    unfold Pi R Q SH SL; rw [hL, hH]; ring

/-- The binding contract earns exactly `R(e_H, e_L)`. -/
theorem screen_Pi_bind (P : Screen) (eH eL : ℝ) : P.Pi (P.bind eH eL) = P.R eH eL := by
  unfold Pi R Q SH SL bind D; ring

/-- The binding contract is feasible when `0 ≤ e_L ≤ e_H`. -/
theorem screen_bind_feas {P : Screen} (h : P.Hyp) {eH eL : ℝ} (hL : 0 ≤ eL) (hLH : eL ≤ eH) :
    P.Feas (P.bind eH eL) := by
  have hle : P.D eL ≤ P.D eH := h.D_mono.monotoneOn hL (hL.trans hLH) hLH
  refine (lemma_14_C_1 h _).2 ⟨hL.trans hLH, hL, ?_, ?_, ?_⟩
  · unfold C1 bind; simp
  · unfold C3 bind D; simp only; linarith
  · unfold C4 bind D; unfold D at hle; simp only; linarith

/-- **Lemma 14.C.2** (MWG, p. 495) and the binding of (iii) (p. 497): at an optimal contract
constraints (i) and (iii) bind. -/
theorem lemma_14_C_2 {P : Screen} (h : P.Hyp) {K : HIContract} (hK : P.IsOpt K) :
    K.wL = P.c + P.g K.eL P.θL ∧ K.wH = P.c + P.D K.eL + P.g K.eH P.θH := by
  have h3 := (lemma_14_C_1 h K).1 hK.1
  have hle := screen_Pi_le h h3.2.2.1 h3.2.2.2.1
  have hge := hK.2 _ (screen_bind_feas h hK.1.2.1 (screen_eL_le_eH h h3))
  rw [screen_Pi_bind] at hge
  exact (screen_Pi_eq_iff h h3.2.2.1 h3.2.2.2.1).1 (le_antisymm hle hge)

/-- The full-information efforts: `e*` uniquely maximizes the surplus `S` on `[0, ∞)`. -/
def IsFB (S : ℝ → ℝ) (estar : ℝ) : Prop :=
  0 ≤ estar ∧ ∀ e, 0 ≤ e → e ≠ estar → S e < S estar

/-- Lowering `e_L` to `min e_L e*_L` raises the virtual surplus `Q`, strictly if `e_L > e*_L`. -/
theorem screen_Q_min {P : Screen} (h : P.Hyp) {eLs : ℝ} (hL : IsFB P.SL eLs) {e : ℝ}
    (he : 0 ≤ e) : P.Q e ≤ P.Q (min e eLs) ∧ (eLs < e → P.Q e < P.Q (min e eLs)) := by
  rcases le_or_gt e eLs with hle | hlt
  · rw [min_eq_left hle]; exact ⟨le_rfl, fun h' => absurd h' (not_lt.2 hle)⟩
  · rw [min_eq_right hlt.le]
    have hS := hL.2 e he hlt.ne'
    have hD := h.D_mono hL.1 he hlt
    have hl := h.lam_pos; have hl' := h.lam_lt
    have : P.Q e < P.Q eLs := by
      unfold Q; nlinarith [mul_lt_mul_of_pos_left hS (by linarith : (0:ℝ) < 1 - P.lam),
        mul_lt_mul_of_pos_left hD hl]
    exact ⟨this.le, fun _ => this⟩

/-- **Lemma 14.C.3** (MWG, p. 496). In any optimal contract (i) `e_L ≤ e*_L` and
(ii) `e_H = e*_H`. -/
theorem lemma_14_C_3 {P : Screen} (h : P.Hyp) {eHs eLs : ℝ} (hH : IsFB P.SH eHs)
    (hL : IsFB P.SL eLs) (hord : eLs ≤ eHs) {K : HIContract} (hK : P.IsOpt K) :
    K.eL ≤ eLs ∧ K.eH = eHs := by
  have h3 := (lemma_14_C_1 h K).1 hK.1
  have hle := screen_Pi_le h h3.2.2.1 h3.2.2.2.1
  set e' := min K.eL eLs
  have he' : 0 ≤ e' := le_min hK.1.2.1 hL.1
  have hfeas := screen_bind_feas h he' ((min_le_right _ _).trans hord)
  have hge := hK.2 _ hfeas
  rw [screen_Pi_bind] at hge
  obtain ⟨hQ, hQs⟩ := screen_Q_min h hL hK.1.2.1
  have hl := h.lam_pos
  have hSH : P.SH K.eH ≤ P.SH eHs := by
    rcases eq_or_ne K.eH eHs with heq | hne
    · rw [heq]
    · exact (hH.2 _ hK.1.1 hne).le
  unfold R at hle hge
  have hLle : K.eL ≤ eLs := by
    by_contra hc
    have := hQs (not_le.1 hc)
    nlinarith [mul_le_mul_of_nonneg_left hSH hl.le]
  refine ⟨hLle, ?_⟩
  by_contra hne
  have hlt := hH.2 _ hK.1.1 hne
  have hm : e' = K.eL := min_eq_left hLle
  rw [hm] at hge
  nlinarith [mul_lt_mul_of_pos_left hlt hl]

/-- **Lemma 14.C.3 and Appendix B** (MWG, pp. 496-499, 504-506): the optimal contracts are exactly
the binding contracts `bind e*_H e_L` where `e_L ≥ 0` maximizes the virtual surplus
`Q(e) = (1 - λ)[π_L(e) - g(e, θ_L)] - λ[g(e, θ_L) - g(e, θ_H)]` on `[0, ∞)`. -/
theorem screen_opt_iff {P : Screen} (h : P.Hyp) {eHs eLs : ℝ} (hH : IsFB P.SH eHs)
    (hL : IsFB P.SL eLs) (hord : eLs ≤ eHs) (K : HIContract) :
    P.IsOpt K ↔ 0 ≤ K.eL ∧ (∀ e, 0 ≤ e → P.Q e ≤ P.Q K.eL) ∧ K = P.bind eHs K.eL := by
  constructor
  · intro hK
    obtain ⟨hLle, hHe⟩ := lemma_14_C_3 h hH hL hord hK
    obtain ⟨hwL, hwH⟩ := lemma_14_C_2 h hK
    have hKb : K = P.bind eHs K.eL := by
      obtain ⟨wH, eH, wL, eL⟩ := K
      simp only at hHe hwL hwH
      subst hHe
      simp only [bind, hwL, hwH]
    refine ⟨hK.1.2.1, fun e he => ?_, hKb⟩
    obtain ⟨hQ, -⟩ := screen_Q_min h hL he
    have hfeas := screen_bind_feas h (le_min he hL.1) ((min_le_right e eLs).trans hord)
    have := hK.2 _ hfeas
    rw [screen_Pi_bind, hKb, screen_Pi_bind] at this
    unfold R at this
    linarith
  · rintro ⟨h0, hmax, hKb⟩
    have hLle : K.eL ≤ eLs := by
      by_contra hc
      have := (screen_Q_min h hL h0).2 (not_le.1 hc)
      have := hmax _ (le_min h0 hL.1)
      linarith
    refine ⟨hKb ▸ screen_bind_feas h h0 (hLle.trans hord), fun K' hK' => ?_⟩
    have h3 := (lemma_14_C_1 h K').1 hK'
    have hle := screen_Pi_le h h3.2.2.1 h3.2.2.2.1
    rw [hKb, screen_Pi_bind]
    have hSH : P.SH K'.eH ≤ P.SH eHs := by
      rcases eq_or_ne K'.eH eHs with heq | hne
      · rw [heq]
      · exact (hH.2 _ hK'.1 hne).le
    have := hmax _ hK'.2.1
    unfold R at hle ⊢
    nlinarith [mul_le_mul_of_nonneg_left hSH h.lam_pos.le]

/-- The truth-telling constraint (iv) is slack at an optimal contract with `e_L < e_H` (MWG,
p. 497: "only the truth-telling constraint for state `θ_H` is binding"). -/
theorem screen_iv_slack {P : Screen} (h : P.Hyp) {K : HIContract} (hK : P.IsOpt K)
    (hlt : K.eL < K.eH) : K.wH - P.g K.eH P.θL < K.wL - P.g K.eL P.θL := by
  obtain ⟨hwL, hwH⟩ := lemma_14_C_2 h hK
  have := h.D_mono hK.1.2.1 hK.1.1 hlt
  unfold D at this hwH; rw [hwL, hwH]; linarith

/-- **Proposition 14.C.3** (MWG, p. 499): at an optimal contract the manager gets exactly `c` in
state `θ_L` and the rent `c + D(e_L)` in state `θ_H`, which exceeds `c` when `e_L > 0`. -/
theorem screen_H_rent {P : Screen} (h : P.Hyp) {K : HIContract} (hK : P.IsOpt K) :
    K.wL - P.g K.eL P.θL = P.c ∧ K.wH - P.g K.eH P.θH = P.c + P.D K.eL ∧
      (0 < K.eL → P.c < K.wH - P.g K.eH P.θH) := by
  obtain ⟨hwL, hwH⟩ := lemma_14_C_2 h hK
  refine ⟨by rw [hwL]; ring, by rw [hwH]; ring, fun hpos => ?_⟩
  have := screen_D_pos h hpos
  rw [hwH]; linarith

/-- The full-information payoff of the owner with an infinitely risk-averse manager:
`λ S_H(e*_H) + (1 - λ) S_L(e*_L) - c`. -/
def FBval (P : Screen) (eHs eLs : ℝ) : ℝ := P.lam * P.SH eHs + (1 - P.lam) * P.SL eLs - P.c

/-- **Proposition 14.C.3, the owner's loss** (MWG, p. 499). If `e_L > 0` at an optimal contract,
the owner's expected payoff is strictly below its full-information value. -/
theorem screen_loss {P : Screen} (h : P.Hyp) {eHs eLs : ℝ} (hH : IsFB P.SH eHs)
    (hL : IsFB P.SL eLs) (hord : eLs ≤ eHs) {K : HIContract} (hK : P.IsOpt K)
    (hpos : 0 < K.eL) : P.Pi K < P.FBval eHs eLs := by
  obtain ⟨-, -, hKb⟩ := (screen_opt_iff h hH hL hord K).1 hK
  rw [hKb, screen_Pi_bind]
  have hS : P.SL K.eL ≤ P.SL eLs := by
    rcases eq_or_ne K.eL eLs with heq | hne
    · rw [heq]
    · exact (hL.2 _ hpos.le hne).le
  have hD := screen_D_pos h hpos
  have hl := h.lam_pos; have hl' := h.lam_lt
  unfold R Q FBval
  nlinarith [mul_le_mul_of_nonneg_left hS (by linarith : (0:ℝ) ≤ 1 - P.lam),
    mul_pos hl hD]

/-- The full-information contract `w_i = c + g(e*_i, θ_i)` violates the truth-telling constraint
(iii) when `e*_L > 0` (MWG, pp. 492, 495). -/
theorem screen_fb_violates_iii {P : Screen} (h : P.Hyp) {eHs eLs : ℝ} (hpos : 0 < eLs) :
    ¬ P.C3 ⟨P.c + P.g eHs P.θH, eHs, P.c + P.g eLs P.θL, eLs⟩ := by
  intro h3
  have := screen_D_pos h hpos
  unfold C3 at h3; unfold D at this; simp only at h3; linarith

/-- **Exercise 14.BB.1** (MWG, p. 510). The relaxed program ignoring (iv) (and (ii)) has exactly
the same solutions as (14.C.8): its solutions satisfy (iv). -/
theorem exercise_14_BB_1 {P : Screen} (h : P.Hyp) {eHs eLs : ℝ} (hH : IsFB P.SH eHs)
    (hL : IsFB P.SL eLs) (hord : eLs ≤ eHs) (K : HIContract) :
    P.IsOptRelax K ↔ P.IsOpt K := by
  rw [screen_opt_iff h hH hL hord]
  have hbound : ∀ K', P.FeasRelax K' → P.Pi K' ≤ P.R K'.eH K'.eL :=
    fun K' hK' => screen_Pi_le h hK'.2.2.1 hK'.2.2.2
  constructor
  · intro hK
    have h0 := hK.1.2.1
    have hle := hbound K hK.1
    have hSHmax : ∀ e', 0 ≤ e' → P.Q e' ≤ P.Q K.eL ∧ P.SH K.eH = P.SH eHs ∧
        P.Pi K = P.R K.eH K.eL := by
      intro e' he'
      have hrel : P.FeasRelax (P.bind eHs e') := by
        refine ⟨hH.1, he', ?_, ?_⟩
        · unfold C1 bind; simp
        · unfold C3 bind D; simp only; linarith
      have hge := hK.2 _ hrel
      rw [screen_Pi_bind] at hge
      have hSH : P.SH K.eH ≤ P.SH eHs := by
        rcases eq_or_ne K.eH eHs with heq | hne
        · rw [heq]
        · exact (hH.2 _ hK.1.1 hne).le
      have hrel0 : P.FeasRelax (P.bind eHs K.eL) := by
        refine ⟨hH.1, h0, ?_, ?_⟩
        · unfold C1 bind; simp
        · unfold C3 bind D; simp only; linarith
      have hge0 := hK.2 _ hrel0
      rw [screen_Pi_bind] at hge0
      have hl := h.lam_pos
      unfold R at hle hge hge0
      refine ⟨?_, ?_, ?_⟩
      · nlinarith [mul_le_mul_of_nonneg_left hSH hl.le]
      · by_contra hne
        have : P.SH K.eH < P.SH eHs := lt_of_le_of_ne hSH hne
        nlinarith [mul_lt_mul_of_pos_left this hl]
      · unfold R; nlinarith [mul_le_mul_of_nonneg_left hSH hl.le]
    have hHe : K.eH = eHs := by
      by_contra hne
      have := (hSHmax 0 le_rfl).2.1
      exact absurd this (hH.2 _ hK.1.1 hne).ne
    obtain ⟨hwL, hwH⟩ := (screen_Pi_eq_iff h hK.1.2.2.1 hK.1.2.2.2).1 (hSHmax 0 le_rfl).2.2
    refine ⟨h0, fun e he => (hSHmax e he).1, ?_⟩
    obtain ⟨wH, eH, wL, eL⟩ := K
    simp only at hHe hwL hwH
    subst hHe
    simp only [bind, hwL, hwH]
  · rintro ⟨h0, hmax, hKb⟩
    have hLle : K.eL ≤ eLs := by
      by_contra hc
      have := (screen_Q_min h hL h0).2 (not_le.1 hc)
      have := hmax _ (le_min h0 hL.1)
      linarith
    refine ⟨?_, fun K' hK' => ?_⟩
    · have := screen_bind_feas h h0 (hLle.trans hord)
      rw [← hKb] at this
      exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.2.1⟩
    · have hle := hbound K' hK'
      rw [hKb, screen_Pi_bind]
      have hSH : P.SH K'.eH ≤ P.SH eHs := by
        rcases eq_or_ne K'.eH eHs with heq | hne
        · rw [heq]
        · exact (hH.2 _ hK'.1 hne).le
      have := hmax _ hK'.2.1
      unfold R at hle ⊢
      nlinarith [mul_le_mul_of_nonneg_left hSH h.lam_pos.le]

end Screen

end MWG.PrincipalAgent
