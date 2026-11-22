/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGAdverseSelection.ScreeningEq

/-!
# Existence and welfare of screening equilibria

MWG, Section 13.D, pp. 465-466, Figure 13.D.7(a) and footnote 25.

* `isScreenEq_sepMenu`: an existence criterion. If no contract `(w, t)` with `w < θ_H` that the
  high type likes at least as much as `(θ_H, t̂_H)` can be paired with a low-type contract on the
  low type's indifference curve through it at a positive profit (`NoProfitableDeviation`), both
  firms offering `{(θ_L, 0), (θ_H, t̂_H)}` is an SPNE. Instances: `figure_13_D_7a`
  (`screenModel (1/5)`, the costs of Exercise 13.C.3), and the linear model `linModel`.
* Welfare (p. 466): `screening_low_worse`, `screening_inefficient` (the high type's task is
  wasteful), `screening_high_better` (when an SPNE exists the high type gets at least `E[θ]`),
  `screening_no_strict_improvement` (when an SPNE exists, no incentive compatible allocation
  gives both types strictly more at a positive profit).
* Footnote 25 and a correction: `footnote_25_counterexample`. In `linModel` an SPNE exists, the
  high type gets exactly `E[θ]` (not strictly more), and the pooling allocation `(3/2, 0)` is a
  constrained Pareto improvement: the equilibrium is not a constrained Pareto optimum.
-/

namespace MWG.AdverseSelection

namespace SigModel

variable {M : SigModel}

/-- **Section 13.D** (MWG, p. 465). The menu `{(θ_L, 0), (θ_H, t̂_H)}` of Proposition 13.D.2. -/
noncomputable def sepMenu (M : SigModel) (th : ℝ) : Finset (ℝ × ℝ) := {(M.θL, 0), (M.θH, th)}

/-- **Section 13.D** (MWG, pp. 465-466, Figure 13.D.7(a)). No deviation breaks the separating
contracts: for every contract `(w, t)` with `w < θ_H` that the high type weakly prefers to
`(θ_H, t̂_H)`, pairing it with the low type's indifferent wage at `t = 0` loses money. -/
def NoProfitableDeviation (M : SigModel) (th : ℝ) : Prop :=
  ∀ w t, 0 ≤ t → M.θH - M.c th M.θH ≤ w - M.c t M.θH → w < M.θH →
    (1 - M.lam) * (M.θL - w + M.c t M.θL) + M.lam * (M.θH - w) ≤ 0

/-- **Section 13.D** (MWG, p. 465, Figure 13.D.7(a)). The existence criterion: under
`NoProfitableDeviation`, both firms offering `{(θ_L, 0), (θ_H, t̂_H)}` is a pure SPNE. -/
theorem isScreenEq_sepMenu (hM : M.Valid) {th : ℝ} (hth : 0 ≤ th)
    (hcth : M.θH - M.c th M.θL = M.θL - M.c 0 M.θL) (hN : M.NoProfitableDeviation th) :
    M.IsScreenEq (M.sepMenu th) (M.sepMenu th) := by
  rw [hM.c_zero, sub_zero] at hcth
  have hlam0 := hM.lam_pos
  have hlam1 := hM.lam_lt
  have hθL := hM.θL_pos
  have hθ := hM.lt
  set A := M.sepMenu th with hA
  have hcL : ∀ t, 0 ≤ t → 0 ≤ M.c t M.θL := fun t ht => by
    have := hM.c_nonneg false ht; simpa only [θ_false] using this
  have hthpos : 0 < th := by
    rcases eq_or_lt_of_le hth with h0 | h0
    · rw [← h0, hM.c_zero] at hcth; linarith
    · exact h0
  have hcHL := hM.c_lt_of_pos hthpos
  have hAval : ValidMenu A := by
    intro k hk
    simp only [hA, sepMenu, Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with hk | hk <;> rw [hk]
    exact hth
  have hAL : ∀ k ∈ A, M.util M.θL k = M.θL := by
    intro k hk
    simp only [hA, sepMenu, Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with hk | hk <;> rw [hk] <;> simp only [util, hM.c_zero] <;> linarith
  have huH : M.util M.θH (M.θH, th) = M.θH - M.c th M.θH := rfl
  have hHgt : M.θL < M.θH - M.c th M.θH := by linarith
  have hmemL : (M.θL, (0 : ℝ)) ∈ A := by simp [hA, sepMenu]
  have hmemH : (M.θH, th) ∈ A := by simp [hA, sepMenu]
  have hu0 : ∀ θ w, M.util θ (w, 0) = w := fun θ w => by simp [util, hM.c_zero]
  -- the equilibrium profit is zero
  have hzero : M.screenProfit A A = 0 := by
    have hchL : M.Chooses M.θL (A ∪ A) (M.θL, 0) := by
      rw [Finset.union_self]
      refine ⟨hmemL, by rw [hu0]; exact hθL.le, fun k hk => by rw [hAL k hk, hu0],
        fun k hk _ => hAval k hk⟩
    have hchH : M.Chooses M.θH (A ∪ A) (M.θH, th) := by
      rw [Finset.union_self]
      refine chooses_of_strict hmemH (by rw [huH]; linarith) fun k hk hne => ?_
      simp only [hA, sepMenu, Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with hk | hk
      · rw [hk, hu0, huH]; exact hHgt
      · exact absurd hk hne
    unfold screenProfit
    rw [typeProfit_of_chooses hchL, typeProfit_of_chooses hchH]
    simp
  refine ⟨hAval, hAval, fun B hB => ?_, fun B hB => ?_⟩ <;> rw [hzero] <;>
  · have hval : ∀ k ∈ B ∪ A, 0 ≤ k.2 := fun k hk => by
      rcases Finset.mem_union.1 hk with hk | hk
      · exact hB k hk
      · exact hAval k hk
    -- the low type yields no profit
    have hπL : M.typeProfit M.θL B A ≤ 0 := by
      by_cases hex : ∃ k, M.Chooses M.θL (B ∪ A) k
      · obtain ⟨k, hk⟩ := hex
        rw [typeProfit_of_chooses hk]
        have hge := hk.2.2.1 _ (Finset.mem_union_right _ hmemL)
        rw [hu0] at hge
        have := hcL _ (hval k hk.1)
        simp only [util] at hge
        exact mul_nonpos_of_nonneg_of_nonpos (share_nonneg _ _ _) (by linarith)
      · rw [typeProfit_of_not hex]
    by_cases hexH : ∃ k, M.Chooses M.θH (B ∪ A) k
    · obtain ⟨kH, hkH⟩ := hexH
      have hπH : M.typeProfit M.θH B A = share B A kH * (M.θH - kH.1) :=
        typeProfit_of_chooses hkH
      rcases le_or_gt M.θH kH.1 with hw | hw
      · have : M.typeProfit M.θH B A ≤ 0 := by
          rw [hπH]; exact mul_nonpos_of_nonneg_of_nonpos (share_nonneg _ _ _) (by linarith)
        unfold screenProfit; nlinarith
      · have hgeH := hkH.2.2.1 _ (Finset.mem_union_right _ hmemH)
        rw [huH] at hgeH
        have hkv := hval kH hkH.1
        have hdev := hN kH.1 kH.2 hkv hgeH hw
        -- the high type's contract has a lower task level, so the low type likes it more
        have hlt : kH.2 < th := by
          by_contra hle
          rw [not_lt] at hle
          have hm := (hM.c_mono true).le_iff_le hth hkv
          simp only [θ_true] at hm
          have := hm.2 hle
          simp only [util] at hgeH
          linarith
        have hsc := hM.sc kH.2 th hkv hlt
        have hLkH : M.θL < M.util M.θL kH := by
          simp only [util] at hgeH ⊢; linarith
        obtain ⟨kL, hkL⟩ := exists_chooses (M := M) M.θL ⟨kH, hkH.1, by linarith⟩
        have hkLu := hkL.2.2.1 kH hkH.1
        have hkLA : kL ∉ A := fun hm => by rw [hAL kL hm] at hkLu; linarith
        have hkLB : kL ∈ B := by
          rcases Finset.mem_union.1 hkL.1 with hm | hm
          · exact hm
          · exact absurd hm hkLA
        have hπL' : M.typeProfit M.θL B A = M.θL - kL.1 := by
          rw [typeProfit_of_chooses hkL]; simp [share, hkLB, hkLA]
        have hcLk := hcL _ (hval kL hkL.1)
        have hshH : share B A kH * (M.θH - kH.1) ≤ M.θH - kH.1 := by
          have := share_le_one B A kH
          nlinarith
        simp only [util] at hkLu
        unfold screenProfit
        rw [hπL', hπH]
        nlinarith
    · unfold screenProfit
      rw [typeProfit_of_not hexH]
      nlinarith

/-- **Section 13.D** (MWG, p. 466). The low type is worse off with screening (`θ_L`) than
without it (`E[θ]`). -/
theorem screening_low_worse (hM : M.Valid) : M.θL < M.Eθ := hM.Eθ_mem.1

/-- **Section 13.D** (MWG, p. 466). Screening equilibria are Pareto inefficient: the high type
performs the unproductive task `t̂_H > 0` and would be strictly better off at `(θ_H, 0)`. -/
theorem screening_inefficient (hM : M.Valid) {th : ℝ} (hth : 0 ≤ th)
    (hcth : M.θH - M.c th M.θL = M.θL - M.c 0 M.θL) :
    0 < th ∧ M.θH - M.c th M.θH < M.θH := by
  rw [hM.c_zero, sub_zero] at hcth
  have hthpos : 0 < th := by
    rcases eq_or_lt_of_le hth with h0 | h0
    · rw [← h0, hM.c_zero] at hcth; linarith [hM.lt]
    · exact h0
  refine ⟨hthpos, ?_⟩
  have := hM.c_pos true hthpos
  simp only [θ_true] at this
  linarith

/-- **Section 13.D** (MWG, p. 466). When an SPNE exists the high type is at least as well off as
without screening: `E[θ] ≤ θ_H - c(t̂_H, θ_H)` (otherwise a pooling contract breaks the
separating contracts). The inequality can be an equality (`footnote_25_counterexample`). -/
theorem screening_high_better (hM : M.Valid) {th : ℝ} (hth : 0 ≤ th)
    (hcth : M.θH - M.c th M.θL = M.θL - M.c 0 M.θL) (h : ∃ A₁ A₂, M.IsScreenEq A₁ A₂) :
    M.Eθ ≤ M.θH - M.c th M.θH := by
  by_contra hlt
  rw [not_le] at hlt
  have hL := hM.Eθ_mem.1
  set m := max M.θL (M.θH - M.c th M.θH)
  have hm1 := le_max_left M.θL (M.θH - M.c th M.θH)
  have hm2 := le_max_right M.θL (M.θH - M.c th M.θH)
  have hmE : m < M.Eθ := max_lt hL hlt
  refine no_eq_of_pooling_deviation hM hth hcth (p := ((m + M.Eθ) / 2, 0)) le_rfl ?_ ?_ ?_ h
  all_goals simp only [util, hM.c_zero, sub_zero]
  all_goals linarith

/-- **Section 13.D** (MWG, p. 466, footnote 25). An allocation `(q_L, q_H)` a central authority
that cannot observe types can implement: nonnegative task levels, incentive compatibility, and
a nonnegative expected profit (budget). -/
def ScreenFeasible (M : SigModel) (qL qH : ℝ × ℝ) : Prop :=
  0 ≤ qL.2 ∧ 0 ≤ qH.2 ∧ M.util M.θL qH ≤ M.util M.θL qL ∧ M.util M.θH qL ≤ M.util M.θH qH ∧
    0 ≤ (1 - M.lam) * (M.θL - qL.1) + M.lam * (M.θH - qH.1)

/-- **Section 13.D** (MWG, p. 466). Constrained optimality of screening equilibria, in the form
that holds: if an SPNE exists, no incentive compatible allocation gives both types strictly
more than their Proposition 13.D.2 contracts at a strictly positive expected profit. (The
book's unqualified claim fails, `footnote_25_counterexample`.) -/
theorem screening_no_strict_improvement (hM : M.Valid) {th : ℝ} (hth : 0 ≤ th)
    (hcth : M.θH - M.c th M.θL = M.θL - M.c 0 M.θL) (h : ∃ A₁ A₂, M.IsScreenEq A₁ A₂)
    {qL qH : ℝ × ℝ} (hq : M.ScreenFeasible qL qH) (hLL : M.θL < M.util M.θL qL)
    (hHH : M.θH - M.c th M.θH < M.util M.θH qH)
    (hprof : 0 < (1 - M.lam) * (M.θL - qL.1) + M.lam * (M.θH - qH.1)) : False := by
  obtain ⟨hqL, hqH, hLH, hHL, -⟩ := hq
  obtain ⟨k', hk'0, hH, hL, hw⟩ := exists_high_dev hM hqH hprof
  have hlam0 := hM.lam_pos
  have hlam1 := hM.lam_lt
  refine no_eq_of_pair_deviation hM hth hcth (qL := qL) (qH := k') hqL hk'0 hLL
    (hL.le.trans hLH) (hHH.trans hH) (hHL.trans hH.le)
    (fun he => absurd he (ne_of_lt (hL.trans_le hLH))) (fun he => absurd he
      (ne_of_lt (lt_of_le_of_lt hHL hH))) ?_ h
  nlinarith [mul_lt_mul_of_pos_left hw hlam0]

/-- **Section 13.D**. A linear screening model: `θ_L = 1`, `θ_H = 2`, `λ = 1/2`,
`c(t, θ) = (3 - θ)t/2` (so `c(t, θ_L) = t`, `c(t, θ_H) = t/2`). -/
noncomputable def linModel : SigModel where
  θL := 1
  θH := 2
  lam := 1 / 2
  r := 0
  c := fun e θ => (3 - θ) * e / 2

theorem linModel_cL (e : ℝ) : linModel.c e linModel.θL = e := by
  simp only [linModel]; ring

theorem linModel_cH (e : ℝ) : linModel.c e linModel.θH = e / 2 := by
  simp only [linModel]; ring

theorem linModel_valid : linModel.Valid where
  θL_pos := by norm_num [linModel]
  lt := by norm_num [linModel]
  lam_pos := by norm_num [linModel]
  lam_lt := by norm_num [linModel]
  r_nonneg := by norm_num [linModel]
  r_lt := by norm_num [linModel]
  c_zero := fun θ => by simp [linModel]
  c_mono := fun b => by
    cases b
    · intro a _ b _ hab; simp only [θ_false, linModel_cL]; exact hab
    · intro a _ b _ hab; simp only [θ_true, linModel_cH]; linarith
  c_cont := fun b => by
    cases b
    · simp only [θ_false, linModel_cL]; exact continuousOn_id
    · simp only [θ_true, linModel_cH]; exact (continuous_id.div_const 2).continuousOn
  sc := fun e e' _ hlt => by
    rw [linModel_cH, linModel_cH, linModel_cL, linModel_cL]; linarith

/-- **Section 13.D** (MWG, p. 466, footnote 25), counterexample. In `linModel` (`t̂_H = 1`) both
firms offering `{(1, 0), (2, 1)}` is an SPNE; the high type's equilibrium utility `3/2` equals
`E[θ]`; and the pooling allocation `(3/2, 0)` is feasible for a central authority, gives the low
type `3/2 > 1` and the high type `3/2`: a constrained Pareto improvement. -/
theorem footnote_25_counterexample :
    linModel.IsScreenEq (linModel.sepMenu 1) (linModel.sepMenu 1) ∧
      linModel.θH - linModel.c 1 linModel.θH = linModel.Eθ ∧
      linModel.ScreenFeasible (3 / 2, 0) (3 / 2, 0) ∧
      linModel.θL < linModel.util linModel.θL (3 / 2, 0) ∧
      linModel.util linModel.θH (3 / 2, 0) = linModel.θH - linModel.c 1 linModel.θH := by
  have hv := linModel_valid
  refine ⟨isScreenEq_sepMenu hv zero_le_one ?_ ?_, ?_, ?_, ?_, ?_⟩
  · rw [linModel_cL, hv.c_zero]; norm_num [linModel]
  · intro w t _ hge _
    rw [linModel_cH, linModel_cH] at hge
    rw [linModel_cL]
    simp only [linModel] at hge ⊢
    linarith
  · rw [linModel_cH]; norm_num [linModel, Eθ]
  · refine ⟨le_rfl, le_rfl, le_rfl, le_rfl, ?_⟩; norm_num [linModel]
  · simp only [util, hv.c_zero]; norm_num [linModel]
  · simp only [util, hv.c_zero, linModel_cH]; norm_num [linModel]

theorem screenModel_cL (l e : ℝ) : (screenModel l).c e (screenModel l).θL = e := crossModel_cL e

theorem screenModel_cH (l e : ℝ) :
    (screenModel l).c e (screenModel l).θH = e ^ 2 / (1 + e) := crossModel_cH e

/-- **Section 13.D** (MWG, p. 465, Figure 13.D.7(a)), an instance: with the costs of
`screenModel` (`c(t, θ_L) = t`, `c(t, θ_H) = t²/(1 + t)`, `t̂_H = 1`) and `λ = 1/5`, both firms
offering `{(1, 0), (2, 1)}` is an SPNE, so the hypotheses of Lemmas 13.D.1-13.D.5 and
Proposition 13.D.2 are satisfiable; the high type strictly gains from screening (`3/2 > 6/5`). -/
theorem figure_13_D_7a :
    (screenModel (1 / 5)).IsScreenEq ((screenModel (1 / 5)).sepMenu 1)
      ((screenModel (1 / 5)).sepMenu 1) ∧
      (screenModel (1 / 5)).Eθ < (screenModel (1 / 5)).θH -
        (screenModel (1 / 5)).c 1 (screenModel (1 / 5)).θH := by
  have hv := screenModel_valid (l := 1 / 5) (by norm_num) (by norm_num)
  refine ⟨isScreenEq_sepMenu hv zero_le_one ?_ ?_, ?_⟩
  · rw [screenModel_cL, hv.c_zero]; norm_num [screenModel, crossModel]
  · intro w t ht hge hw
    rw [screenModel_cH, screenModel_cH] at hge
    rw [screenModel_cL]
    simp only [screenModel, crossModel] at hge hw ⊢
    set g := t ^ 2 / (1 + t) with hg
    have hgt : g * (1 + t) = t ^ 2 := by rw [hg]; field_simp
    have ht1 : t < 1 := by nlinarith
    have hkey : 4 * t / 5 - 3 / 10 ≤ g := by
      by_contra hlt
      rw [not_le] at hlt
      nlinarith [mul_pos (sub_pos.2 hlt) (by linarith : (0 : ℝ) < 1 + t),
        mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - t) (by linarith : (0 : ℝ) ≤ 3 - 2 * t)]
    norm_num at hge ⊢
    linarith
  · rw [screenModel_cH]; norm_num [screenModel, crossModel, Eθ]

/-- **Proposition 13.D.2** (MWG, p. 465), the instance: in the SPNE of `figure_13_D_7a` the low
type takes `(1, 0)` and the high type `(2, 1)`, and both firms earn zero. -/
theorem proposition_13_D_2_instance :
    (screenModel (1 / 5)).Chooses (screenModel (1 / 5)).θL
        ((screenModel (1 / 5)).sepMenu 1 ∪ (screenModel (1 / 5)).sepMenu 1) (1, 0) ∧
      (screenModel (1 / 5)).Chooses (screenModel (1 / 5)).θH
        ((screenModel (1 / 5)).sepMenu 1 ∪ (screenModel (1 / 5)).sepMenu 1) (2, 1) ∧
      (screenModel (1 / 5)).screenProfit ((screenModel (1 / 5)).sepMenu 1)
        ((screenModel (1 / 5)).sepMenu 1) = 0 := by
  have hv := screenModel_valid (l := 1 / 5) (by norm_num) (by norm_num)
  have hcth : (screenModel (1 / 5)).θH - (screenModel (1 / 5)).c 1 (screenModel (1 / 5)).θL =
      (screenModel (1 / 5)).θL - (screenModel (1 / 5)).c 0 (screenModel (1 / 5)).θL := by
    rw [screenModel_cL, hv.c_zero]; norm_num [screenModel, crossModel]
  have h := proposition_13_D_2 hv figure_13_D_7a.1 zero_le_one hcth
  exact ⟨h.1, h.2, (lemma_13_D_1 hv figure_13_D_7a.1).1⟩

end SigModel

end MWG.AdverseSelection
