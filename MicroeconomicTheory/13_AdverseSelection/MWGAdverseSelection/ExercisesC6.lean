/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGAdverseSelection.Exercises

/-!
# Exercise 13.C.6(b): self-financing as a signal

MWG, Exercise 13.C.6(b), pp. 475-476. Projects cost `1`; a good (bad) project yields `Π` with
probability `p_G` (`p_B`) and `0` otherwise; a fraction `λ` is good; banks borrow at `r`; the
entrepreneur can contribute `x ∈ [0, 1]` of the outlay at effective cost `(1 + ρ)x`, `ρ > r`;
`p_GΠ - (1 + r) > 0 > p_BΠ - (1 + r)` (`LoanModel.Valid`). A loan of `1 - x` specifies the
repayment `R`, paid when the project succeeds.

* (i) `LoanModel.entPay`: the payoff `p_t(Π - R) - (1 + ρ)x` of type `t` going ahead
  (`0` otherwise); `exercise_13_C_6b_i` evaluates it at the zero-profit repayments.
* The game (entrepreneur offers `x`, banks offer `R`, entrepreneur accepts or not), in reduced
  form (`LoanModel.IsLoanPBE`): after `x` with belief `b` = Prob(good), Bertrand competition
  drives the banks to the zero-profit repayment `R = (1 + r)(1 - x)/(bp_G + (1 - b)p_B)`
  (`LoanModel.repay`, `exercise_13_C_6b_bank_zero_profit`); type `t` then goes ahead iff its
  payoff is nonnegative (`LoanModel.gamePay`); beliefs follow Bayes' rule on the path.
* (ii) `exercise_13_C_6b_ii_separating`: `(x_G, x_B)`, `x_G ≠ x_B`, is a separating PBE outcome
  iff `x_G ≥ x*`, `x* = p_B(p_GΠ - (1 + r))/(p_G(1 + ρ) - p_B(1 + r)) ∈ (0, 1)`. The best one
  (`exercise_13_C_6b_ii_best`) has `x_G = x*`: the bad type and the banks get `0` in every
  separating PBE, and the good type's payoff `p_GΠ - (1 + r) - (ρ - r)x_G` falls with `x_G`.
  Comparative statics of `x*` (`exercise_13_C_6b_ii_statics`): strictly increasing in `p_B`,
  `p_G` and `Π`, strictly decreasing in `r` (and in `ρ`), independent of `λ`.
* (iii) `exercise_13_C_6b_iii`: compared with the pooling equilibrium of (a) (all financed at
  `R = (1 + r)/p̄` if `p̄Π ≥ 1 + r`, none otherwise), the bad type is weakly worse off (strictly
  if loans are made in (a)); the good type is strictly better off if (a) has no lending, and
  otherwise better off iff `(ρ - r)x* < (1 + r)(p_G/p̄ - 1)`; both cases occur
  (`exercise_13_C_6b_iii_instance`).
-/

namespace MWG.AdverseSelection

/-- **Exercise 13.C.6** (MWG, p. 475). The loan market: success probabilities `p_G`, `p_B`,
fraction `λ` of good projects, profit `Π`, the banks' rate `r`, the entrepreneur's rate `ρ`. -/
structure LoanModel where
  pG : ℝ
  pB : ℝ
  lam : ℝ
  Pf : ℝ
  r : ℝ
  rho : ℝ

namespace LoanModel

/-- **Exercise 13.C.6** (MWG, p. 475). The assumptions. -/
structure Valid (L : LoanModel) : Prop where
  pB_pos : 0 < L.pB
  lt : L.pB < L.pG
  pG_le : L.pG ≤ 1
  lam_pos : 0 < L.lam
  lam_lt : L.lam < 1
  r_nonneg : 0 ≤ L.r
  rho_gt : L.r < L.rho
  good : 1 + L.r < L.pG * L.Pf
  bad : L.pB * L.Pf < 1 + L.r

/-- The success probability of type `t` (`true` = good). -/
def p (L : LoanModel) (t : Bool) : ℝ := if t then L.pG else L.pB

/-- The average success probability `bp_G + (1 - b)p_B` under the belief `b`. -/
def pbar (L : LoanModel) (b : ℝ) : ℝ := b * L.pG + (1 - b) * L.pB

/-- **Exercise 13.C.6(b)(i)** (MWG, p. 475). The payoff `p_t(Π - R) - (1 + ρ)x` of an
entrepreneur of type `t` who contributes `x` and goes ahead with repayment `R`. -/
def entPay (L : LoanModel) (t : Bool) (R x : ℝ) : ℝ := L.p t * (L.Pf - R) - (1 + L.rho) * x

/-- **Exercise 13.C.6(b)** (MWG, p. 475). The zero-profit repayment on a loan of `1 - x` under
the belief `b`. -/
noncomputable def repay (L : LoanModel) (x b : ℝ) : ℝ := (1 + L.r) * (1 - x) / L.pbar b

/-- **Exercise 13.C.6(b)** (MWG, p. 475). The entrepreneur's payoff in the game after offering
`x` when the banks hold belief `b`: she goes ahead iff that is profitable. -/
noncomputable def gamePay (L : LoanModel) (t : Bool) (x b : ℝ) : ℝ :=
  max (L.entPay t (L.repay x b) x) 0

/-- **Exercise 13.C.6(b)(ii)** (MWG, p. 475). A pure strategy PBE (reduced form): contributions
`x_t ∈ [0, 1]`, beliefs in `[0, 1]` given by Bayes' rule on the path, and each type's offer
optimal given the banks' zero-profit responses. -/
def IsLoanPBE (L : LoanModel) (xS : Bool → ℝ) (bel : ℝ → ℝ) : Prop :=
  (∀ t, 0 ≤ xS t ∧ xS t ≤ 1) ∧ (∀ x, 0 ≤ bel x ∧ bel x ≤ 1) ∧
    (∀ t x, 0 ≤ x → x ≤ 1 → L.gamePay t x (bel x) ≤ L.gamePay t (xS t) (bel (xS t))) ∧
    (xS false ≠ xS true → bel (xS true) = 1 ∧ bel (xS false) = 0) ∧
    (xS false = xS true → bel (xS true) = L.lam)

/-- **Exercise 13.C.6(b)(ii)** (MWG, p. 475). The good type's minimal separating contribution
`x* = p_B(p_GΠ - (1 + r))/(p_G(1 + ρ) - p_B(1 + r))`. -/
noncomputable def xStar (L : LoanModel) : ℝ :=
  L.pB * (L.pG * L.Pf - (1 + L.r)) / (L.pG * (1 + L.rho) - L.pB * (1 + L.r))

variable {L : LoanModel}

theorem Valid.den_pos (hL : L.Valid) : 0 < L.pG * (1 + L.rho) - L.pB * (1 + L.r) := by
  have := hL.r_nonneg
  have := hL.rho_gt
  nlinarith [hL.lt, hL.pB_pos]

theorem Valid.pbar_pos (hL : L.Valid) {b : ℝ} (hb : 0 ≤ b) : 0 < L.pbar b := by
  unfold pbar; nlinarith [hL.lt, hL.pB_pos]

/-- **Exercise 13.C.6(b)** (MWG, p. 475). At the repayment `repay x b` a bank lending `1 - x`
breaks even under the belief `b`. -/
theorem exercise_13_C_6b_bank_zero_profit (hL : L.Valid) {x b : ℝ} (hb : 0 ≤ b) :
    L.pbar b * L.repay x b - (1 + L.r) * (1 - x) = 0 := by
  rw [repay, mul_div_cancel₀ _ (hL.pbar_pos hb).ne', sub_self]

/-- **Exercise 13.C.6(b)(i)** (MWG, p. 475). The payoffs at the zero-profit repayments: a good
type identified as good gets `p_GΠ - (1 + r) - (ρ - r)x`; a bad type identified as bad gets
`p_BΠ - (1 + r) - (ρ - r)x < 0`; a bad type taken for good gets
`p_BΠ - (p_B/p_G)(1 + r)(1 - x) - (1 + ρ)x`; a good type taken for bad gets
`p_GΠ - (p_G/p_B)(1 + r)(1 - x) - (1 + ρ)x`. -/
theorem exercise_13_C_6b_i (hL : L.Valid) (x : ℝ) (hx : 0 ≤ x) :
    L.entPay true (L.repay x 1) x = L.pG * L.Pf - (1 + L.r) - (L.rho - L.r) * x ∧
      L.entPay false (L.repay x 0) x = L.pB * L.Pf - (1 + L.r) - (L.rho - L.r) * x ∧
      L.entPay false (L.repay x 0) x < 0 ∧
      L.entPay false (L.repay x 1) x =
        L.pB * L.Pf - L.pB / L.pG * ((1 + L.r) * (1 - x)) - (1 + L.rho) * x ∧
      L.entPay true (L.repay x 0) x =
        L.pG * L.Pf - L.pG / L.pB * ((1 + L.r) * (1 - x)) - (1 + L.rho) * x := by
  have hG : 0 < L.pG := hL.pB_pos.trans hL.lt
  have hB := hL.pB_pos
  have h1 : L.pbar 1 = L.pG := by simp [pbar]
  have h0 : L.pbar 0 = L.pB := by simp [pbar]
  simp only [entPay, repay, h1, h0, p, ite_true, Bool.false_eq_true, ite_false]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · field_simp; ring
  · field_simp; ring
  · field_simp
    nlinarith [hL.bad, hL.rho_gt]
  · field_simp
  · field_simp

/-- The bad type's payoff from being taken for good is `≤ 0` iff `x ≥ x*`. -/
theorem Valid.bad_mimic_iff (hL : L.Valid) (x : ℝ) :
    L.entPay false (L.repay x 1) x ≤ 0 ↔ L.xStar ≤ x := by
  have hG : 0 < L.pG := hL.pB_pos.trans hL.lt
  have hD := hL.den_pos
  have h1 : L.pbar 1 = L.pG := by simp [pbar]
  simp only [entPay, repay, h1, p, Bool.false_eq_true, ite_false, xStar]
  rw [div_le_iff₀ hD]
  have e : L.pB * (L.Pf - (1 + L.r) * (1 - x) / L.pG) - (1 + L.rho) * x =
      (L.pB * (L.pG * L.Pf - (1 + L.r)) - x * (L.pG * (1 + L.rho) - L.pB * (1 + L.r))) /
        L.pG := by
    field_simp; ring
  rw [e, div_le_iff₀ hG, zero_mul, sub_nonpos]

/-- `0 < x* < 1`. -/
theorem Valid.xStar_mem (hL : L.Valid) : 0 < L.xStar ∧ L.xStar < 1 := by
  have hD := hL.den_pos
  have hB := hL.pB_pos
  unfold xStar
  refine ⟨div_pos (mul_pos hB (by linarith [hL.good])) hD, (div_lt_one hD).2 ?_⟩
  nlinarith [hL.bad, hL.rho_gt, hL.lt]

/-- **Exercise 13.C.6(b)(ii)** (MWG, p. 475). Separating PBE: `(x_G, x_B)` with `x_G ≠ x_B` in
`[0, 1]` is the outcome of a PBE iff `x* ≤ x_G`. -/
theorem exercise_13_C_6b_ii_separating (hL : L.Valid) {xG xB : ℝ} (hG0 : 0 ≤ xG) (hG1 : xG ≤ 1)
    (hB0 : 0 ≤ xB) (hB1 : xB ≤ 1) (hne : xB ≠ xG) :
    (∃ bel, L.IsLoanPBE (fun t => if t then xG else xB) bel) ↔ L.xStar ≤ xG := by
  have hpG : 0 < L.pG := hL.pB_pos.trans hL.lt
  have hbad0 : ∀ x, 0 ≤ x → L.gamePay false x 0 = 0 := fun x hx =>
    max_eq_right ((exercise_13_C_6b_i hL x hx).2.2.1).le
  constructor
  · rintro ⟨bel, -, -, hopt, hB, -⟩
    obtain ⟨h1, h0⟩ := hB (by simpa using hne)
    have := hopt false xG hG0 hG1
    simp only [Bool.false_eq_true, ite_false] at this h0
    simp only [ite_true] at h1
    rw [h1, h0, hbad0 xB hB0, gamePay, max_le_iff] at this
    exact (hL.bad_mimic_iff xG).1 this.1
  · intro hx
    refine ⟨fun x => if x = xG then 1 else 0, fun t => ?_, fun x => ?_, fun t x hx0 hx1 => ?_,
      fun _ => ?_, fun h => absurd h (by simpa using hne)⟩
    · cases t
      · exact ⟨hB0, hB1⟩
      · exact ⟨hG0, hG1⟩
    · dsimp only
      split_ifs <;> norm_num
    · cases t
      · simp only [Bool.false_eq_true, hne, ↓reduceIte]
        rw [hbad0 xB hB0]
        by_cases hxG : x = xG
        · simp only [hxG, ↓reduceIte, gamePay]
          exact max_le ((hL.bad_mimic_iff xG).2 hx) le_rfl
        · simp only [hxG, ↓reduceIte]
          rw [hbad0 x hx0]
      · simp only [↓reduceIte]
        by_cases hxG : x = xG
        · simp [hxG]
        · simp only [hxG, ↓reduceIte, gamePay]
          rw [(exercise_13_C_6b_i hL x hx0).2.2.2.2, (exercise_13_C_6b_i hL xG hG0).1]
          have hq0 : 0 ≤ L.pG / L.pB := (div_pos hpG hL.pB_pos).le
          have hpB := hL.pB_pos.ne'
          have hk : L.pG / L.pB * ((1 + L.r) * (1 - x)) - (1 - x) * (L.pG * L.Pf) =
              (1 - x) * (L.pG / L.pB) * ((1 + L.r) - L.pB * L.Pf) := by
            field_simp
          have hk0 : 0 ≤ (1 - x) * (L.pG / L.pB) * ((1 + L.r) - L.pB * L.Pf) :=
            mul_nonneg (mul_nonneg (sub_nonneg.2 hx1) hq0) (sub_nonneg.2 hL.bad.le)
          have hVge : L.pG * L.Pf - (1 + L.rho) ≤
              L.pG * L.Pf - (1 + L.r) - (L.rho - L.r) * xG := by nlinarith [hL.rho_gt]
          refine max_le ?_ (le_max_right _ _)
          rcases le_or_gt 0 (L.pG * L.Pf - (1 + L.rho)) with h | h
          · exact le_max_of_le_left (by nlinarith)
          · exact le_max_of_le_right (by nlinarith)
    · simp only [Bool.false_eq_true, hne, ↓reduceIte, and_self]

/-- The good type's payoff when identified, `p_GΠ - (1 + r) - (ρ - r)x`, at `x*`:
`(p_GΠ - (1 + r))(1 + ρ)(p_G - p_B)/(p_G(1 + ρ) - p_B(1 + r)) > 0`. -/
theorem Valid.goodPay_xStar (hL : L.Valid) :
    L.pG * L.Pf - (1 + L.r) - (L.rho - L.r) * L.xStar =
        (L.pG * L.Pf - (1 + L.r)) * (1 + L.rho) * (L.pG - L.pB) /
          (L.pG * (1 + L.rho) - L.pB * (1 + L.r)) ∧
      0 < L.pG * L.Pf - (1 + L.r) - (L.rho - L.r) * L.xStar := by
  have hD := hL.den_pos
  have e : L.pG * L.Pf - (1 + L.r) - (L.rho - L.r) * L.xStar =
      (L.pG * L.Pf - (1 + L.r)) * (1 + L.rho) * (L.pG - L.pB) /
        (L.pG * (1 + L.rho) - L.pB * (1 + L.r)) := by
    have hxs : L.xStar * (L.pG * (1 + L.rho) - L.pB * (1 + L.r)) =
        L.pB * (L.pG * L.Pf - (1 + L.r)) := div_mul_cancel₀ _ hD.ne'
    rw [eq_div_iff hD.ne']
    linear_combination (-(L.rho - L.r)) * hxs
  refine ⟨e, ?_⟩
  rw [e]
  have := hL.r_nonneg
  have := hL.rho_gt
  exact div_pos (mul_pos (mul_pos (by linarith [hL.good]) (by linarith))
    (by linarith [hL.lt])) hD

/-- **Exercise 13.C.6(b)(ii)** (MWG, p. 475). The best separating PBE: `x_G = x*` (with
`x_B = 0`) is a separating PBE outcome; in it the good type earns
`p_GΠ - (1 + r) - (ρ - r)x* > 0`, and in every separating PBE the bad type earns `0` and the
good type at most this (the banks earn zero by `exercise_13_C_6b_bank_zero_profit`). -/
theorem exercise_13_C_6b_ii_best (hL : L.Valid) :
    (∃ bel, L.IsLoanPBE (fun t => if t then L.xStar else 0) bel) ∧
      L.gamePay true L.xStar 1 = L.pG * L.Pf - (1 + L.r) - (L.rho - L.r) * L.xStar ∧
      0 < L.gamePay true L.xStar 1 ∧
      ∀ xG xB bel, L.IsLoanPBE (fun t => if t then xG else xB) bel → xB ≠ xG →
        L.gamePay true xG (bel xG) ≤ L.gamePay true L.xStar 1 ∧
          L.gamePay false xB (bel xB) = 0 := by
  obtain ⟨hx0, hx1⟩ := hL.xStar_mem
  obtain ⟨-, hVpos⟩ := hL.goodPay_xStar
  have hV : L.gamePay true L.xStar 1 = L.pG * L.Pf - (1 + L.r) - (L.rho - L.r) * L.xStar := by
    rw [gamePay, (exercise_13_C_6b_i hL _ hx0.le).1, max_eq_left hVpos.le]
  refine ⟨(exercise_13_C_6b_ii_separating hL hx0.le hx1.le le_rfl zero_le_one hx0.ne).2 le_rfl,
    hV, hV ▸ hVpos, fun xG xB bel h hne => ?_⟩
  have hxs := h
  obtain ⟨hmem, -, -, hB, -⟩ := h
  obtain ⟨h1, h0⟩ := hB (by simpa using hne)
  simp only [ite_true, Bool.false_eq_true, ite_false] at h1 h0
  have hG := hmem true
  have hBm := hmem false
  simp only [ite_true, Bool.false_eq_true, ite_false] at hG hBm
  have hge := (exercise_13_C_6b_ii_separating hL hG.1 hG.2 hBm.1 hBm.2 hne).1 ⟨bel, hxs⟩
  refine ⟨?_, ?_⟩
  · rw [h1, hV, gamePay, (exercise_13_C_6b_i hL _ hG.1).1]
    refine max_le ?_ hVpos.le
    nlinarith [hL.rho_gt]
  · rw [h0, gamePay]
    exact max_eq_right ((exercise_13_C_6b_i hL xB hBm.1).2.2.1).le

/-- **Exercise 13.C.6(b)(ii)** (MWG, p. 475). Comparative statics of the good type's
contribution `x*` (between valid parameter values): it rises with `p_B`, `p_G` and `Π`, falls
with `r` and `ρ`, and does not depend on `λ`. -/
theorem exercise_13_C_6b_ii_statics (hL : L.Valid) :
    (∀ pB', ({ L with pB := pB' } : LoanModel).Valid → L.pB < pB' →
      L.xStar < ({ L with pB := pB' } : LoanModel).xStar) ∧
    (∀ pG', ({ L with pG := pG' } : LoanModel).Valid → L.pG < pG' →
      L.xStar < ({ L with pG := pG' } : LoanModel).xStar) ∧
    (∀ Pf', ({ L with Pf := Pf' } : LoanModel).Valid → L.Pf < Pf' →
      L.xStar < ({ L with Pf := Pf' } : LoanModel).xStar) ∧
    (∀ r', ({ L with r := r' } : LoanModel).Valid → L.r < r' →
      ({ L with r := r' } : LoanModel).xStar < L.xStar) ∧
    (∀ rho', ({ L with rho := rho' } : LoanModel).Valid → L.rho < rho' →
      ({ L with rho := rho' } : LoanModel).xStar < L.xStar) ∧
    (∀ lam', ({ L with lam := lam' } : LoanModel).xStar = L.xStar) := by
  have hD := hL.den_pos
  have hB := hL.pB_pos
  have hA : 0 < L.pG * L.Pf - (1 + L.r) := by linarith [hL.good]
  have hc : L.pB * L.Pf < 1 + L.rho := by linarith [hL.bad, hL.rho_gt]
  have hr0 := hL.r_nonneg
  refine ⟨fun pB' hV h => ?_, fun pG' hV h => ?_, fun Pf' hV h => ?_, fun r' hV h => ?_,
    fun rho' hV h => ?_, fun _ => rfl⟩
  · have hD' := hV.den_pos
    simp only [xStar] at hD' ⊢
    rw [div_lt_div_iff₀ hD hD']
    have e : pB' * (L.pG * L.Pf - (1 + L.r)) * (L.pG * (1 + L.rho) - L.pB * (1 + L.r)) -
        L.pB * (L.pG * L.Pf - (1 + L.r)) * (L.pG * (1 + L.rho) - pB' * (1 + L.r)) =
        (pB' - L.pB) * (L.pG * L.Pf - (1 + L.r)) * (L.pG * (1 + L.rho)) := by ring
    have : 0 < (pB' - L.pB) * (L.pG * L.Pf - (1 + L.r)) * (L.pG * (1 + L.rho)) :=
      mul_pos (mul_pos (by linarith) hA) (mul_pos (hB.trans hL.lt) (by linarith [hL.rho_gt]))
    linarith
  · have hD' := hV.den_pos
    simp only [xStar] at hD' ⊢
    rw [div_lt_div_iff₀ hD hD']
    have e : L.pB * (pG' * L.Pf - (1 + L.r)) * (L.pG * (1 + L.rho) - L.pB * (1 + L.r)) -
        L.pB * (L.pG * L.Pf - (1 + L.r)) * (pG' * (1 + L.rho) - L.pB * (1 + L.r)) =
        L.pB * (1 + L.r) * (pG' - L.pG) * (1 + L.rho - L.pB * L.Pf) := by ring
    have : 0 < L.pB * (1 + L.r) * (pG' - L.pG) * (1 + L.rho - L.pB * L.Pf) :=
      mul_pos (mul_pos (mul_pos hB (by linarith)) (by linarith)) (by linarith)
    linarith
  · simp only [xStar]
    exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_left
      (by nlinarith [hB.trans hL.lt]) hB) hD
  · have hD' := hV.den_pos
    simp only [xStar] at hD' ⊢
    rw [div_lt_div_iff₀ hD' hD]
    have e : L.pB * (L.pG * L.Pf - (1 + L.r)) * (L.pG * (1 + L.rho) - L.pB * (1 + r')) -
        L.pB * (L.pG * L.Pf - (1 + r')) * (L.pG * (1 + L.rho) - L.pB * (1 + L.r)) =
        L.pB * L.pG * (r' - L.r) * (1 + L.rho - L.pB * L.Pf) := by ring
    have : 0 < L.pB * L.pG * (r' - L.r) * (1 + L.rho - L.pB * L.Pf) :=
      mul_pos (mul_pos (mul_pos hB (hB.trans hL.lt)) (by linarith)) (by linarith)
    linarith
  · have hD' := hV.den_pos
    simp only [xStar] at hD' ⊢
    exact div_lt_div_of_pos_left (mul_pos hB hA) hD
      (by nlinarith [hB.trans hL.lt])

/-- **Exercise 13.C.6(a)** (MWG, p. 475), payoffs: in the pooling equilibrium of (a) all projects
are financed at `R = (1 + r)/p̄` if `p̄Π ≥ 1 + r` (`p̄ = λp_G + (1 - λ)p_B`), and type `t` earns
`p_t(Π - R)`; otherwise nothing is financed. -/
noncomputable def poolPay (L : LoanModel) (t : Bool) : ℝ :=
  if 1 + L.r ≤ L.pbar L.lam * L.Pf then L.p t * (L.Pf - (1 + L.r) / L.pbar L.lam) else 0

/-- **Exercise 13.C.6(b)(iii)** (MWG, p. 476). Compared with the equilibrium of (a): the bad type
(who earns `0` in the separating PBE) is weakly worse off, strictly when loans are made in (a);
the good type is strictly better off if (a) has no lending, and otherwise better off iff
`(ρ - r)x* < (1 + r)(p_G/p̄ - 1)`. -/
theorem exercise_13_C_6b_iii (hL : L.Valid) :
    0 ≤ L.poolPay false ∧ (1 + L.r < L.pbar L.lam * L.Pf → 0 < L.poolPay false) ∧
      (L.pbar L.lam * L.Pf < 1 + L.r → L.poolPay true < L.gamePay true L.xStar 1) ∧
      (1 + L.r ≤ L.pbar L.lam * L.Pf →
        (L.poolPay true < L.gamePay true L.xStar 1 ↔
          (L.rho - L.r) * L.xStar < (1 + L.r) * (L.pG / L.pbar L.lam - 1))) := by
  have hp := hL.pbar_pos hL.lam_pos.le
  have hB := hL.pB_pos
  obtain ⟨hx0, -⟩ := hL.xStar_mem
  obtain ⟨-, hVpos⟩ := hL.goodPay_xStar
  have hV : L.gamePay true L.xStar 1 = L.pG * L.Pf - (1 + L.r) - (L.rho - L.r) * L.xStar := by
    rw [gamePay, (exercise_13_C_6b_i hL _ hx0.le).1, max_eq_left hVpos.le]
  have hR : 1 + L.r ≤ L.pbar L.lam * L.Pf → 0 ≤ L.Pf - (1 + L.r) / L.pbar L.lam :=
    fun h => sub_nonneg.2 ((div_le_iff₀ hp).2 (by linarith))
  refine ⟨?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · unfold poolPay
    split_ifs with h
    · exact mul_nonneg hB.le (hR h)
    · exact le_rfl
  · simp only [poolPay, h.le, ↓reduceIte, p, Bool.false_eq_true]
    exact mul_pos hB (sub_pos.2 ((div_lt_iff₀ hp).2 (by linarith)))
  · simp only [poolPay, not_le.2 h, ↓reduceIte]
    rw [hV]
    exact hVpos
  · simp only [poolPay, h, ↓reduceIte, p]
    rw [hV]
    have e : L.pG * (L.Pf - (1 + L.r) / L.pbar L.lam) =
        L.pG * L.Pf - (1 + L.r) - (1 + L.r) * (L.pG / L.pbar L.lam - 1) := by
      field_simp
      ring
    rw [e]
    constructor <;> intro h' <;> linarith

/-- **Exercise 13.C.6(b)**, the instances: `p_G = 1`, `p_B = 1/2`, `Π = 3/2`, `r = 0`, `ρ = 1`, and
`λ = 1/4` or `λ = 9/10`. -/
noncomputable def loanModel (lam : ℝ) : LoanModel where
  pG := 1
  pB := 1 / 2
  lam := lam
  Pf := 3 / 2
  r := 0
  rho := 1

theorem loanModel_valid {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) : (loanModel lam).Valid where
  pB_pos := by norm_num [loanModel]
  lt := by norm_num [loanModel]
  pG_le := by norm_num [loanModel]
  lam_pos := h0
  lam_lt := h1
  r_nonneg := le_rfl
  rho_gt := by norm_num [loanModel]
  good := by norm_num [loanModel]
  bad := by norm_num [loanModel]

/-- **Exercise 13.C.6(b)(ii)-(iii)**, instances (MWG, pp. 475-476). Here `x* = 1/6` and the good
type earns `1/3` in the best separating PBE, whatever `λ`. With `λ = 1/4` nothing is financed in
(a) and the good type is better off separating; with `λ = 9/10` all projects are financed in
(a), the good type earns `17/38 > 1/3` there and the bad type `17/76 > 0`. -/
theorem exercise_13_C_6b_iii_instance :
    (loanModel (1 / 4)).xStar = 1 / 6 ∧ (loanModel (1 / 4)).gamePay true (1 / 6) 1 = 1 / 3 ∧
      (loanModel (9 / 10)).gamePay true (1 / 6) 1 = 1 / 3 ∧
      (loanModel (1 / 4)).poolPay true = 0 ∧ (loanModel (1 / 4)).poolPay false = 0 ∧
      (loanModel (9 / 10)).poolPay true = 17 / 38 ∧ (loanModel (9 / 10)).poolPay false = 17 / 76 ∧
      (loanModel (1 / 4)).poolPay true < (loanModel (1 / 4)).gamePay true (1 / 6) 1 ∧
      (loanModel (9 / 10)).gamePay true (1 / 6) 1 < (loanModel (9 / 10)).poolPay true := by
  have hg : ∀ lam : ℝ, (loanModel lam).gamePay true (1 / 6) 1 = 1 / 3 := fun lam => by
    simp only [gamePay, entPay, repay, pbar, p, loanModel, ite_true]
    norm_num
  have hpl : (loanModel (1 / 4)).poolPay true = 0 ∧ (loanModel (1 / 4)).poolPay false = 0 := by
    simp only [poolPay, pbar, loanModel]
    norm_num
  have hph : (loanModel (9 / 10)).poolPay true = 17 / 38 ∧
      (loanModel (9 / 10)).poolPay false = 17 / 76 := by
    simp only [poolPay, pbar, p, loanModel]
    norm_num
  refine ⟨by simp only [xStar, loanModel]; norm_num, hg _, hg _, hpl.1, hpl.2, hph.1, hph.2,
    ?_, ?_⟩
  · rw [hpl.1, hg]; norm_num
  · rw [hph.1, hg]; norm_num

/-- **Exercise 13.C.6(b)(ii)**, instance of `exercise_13_C_6b_ii_statics` (MWG, p. 475): the base
model `p_G = 4/5`, `p_B = 2/5`, `λ = 1/2`, `Π = 2`, `r = 0`, `ρ = 1` and each single-parameter
change used there (`p_B = 9/20`, `p_G = 9/10`, `Π = 9/4`, `r = 1/10`, `ρ = 2`) are valid. -/
theorem exercise_13_C_6b_ii_statics_instance :
    let L0 : LoanModel := ⟨4 / 5, 2 / 5, 1 / 2, 2, 0, 1⟩
    L0.Valid ∧ ({ L0 with pB := 9 / 20 } : LoanModel).Valid ∧
      ({ L0 with pG := 9 / 10 } : LoanModel).Valid ∧ ({ L0 with Pf := 9 / 4 } : LoanModel).Valid ∧
      ({ L0 with r := 1 / 10 } : LoanModel).Valid ∧ ({ L0 with rho := 2 } : LoanModel).Valid := by
  intro L0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact ⟨by norm_num [L0], by norm_num [L0], by norm_num [L0], by norm_num [L0],
      by norm_num [L0], by norm_num [L0], by norm_num [L0], by norm_num [L0], by norm_num [L0]⟩

end LoanModel

end MWG.AdverseSelection
