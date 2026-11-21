/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGAdverseSelection.ExercisesD2
import MWGAdverseSelection.Signaling

/-!
# Exercise 13.D.3: screening with observable output

MWG, Exercise 13.D.3, p. 476.

All workers perform the fixed task `T`; accepting employment has a type-independent monetary cost
`c > 0`; output is observable and contractible, so a contract is a wage schedule over output
levels, `k = (w_G, w_B)`: the wage after the good (or, in (a), the high type's) output and after
the bad (the low type's) output. A worker of type `b` obtains the good output with probability
`p_b`, and gets `p_b u(w_G - c) + (1 - p_b) u(w_B - c)` if she works, `u(0)` if she does not.

* (b) `rnGame` (risk neutral, `u(w) = w`); `exercise_13_D_3b`: in every SPNE both firms earn
  zero, a type whose expected output `ȳ_b` exceeds `c` works and gets exactly `ȳ_b - c` (she is
  paid her expected output), a type with `ȳ_b < c` does not work; `exercise_13_D_3b_exists`:
  both firms offering "pay the output" `(q_G, q_B)` is an SPNE. The full-information outcome
  obtains: output-contingent pay removes the adverse selection.
* (a) `exercise_13_D_3a`, `exercise_13_D_3a_exists`: deterministic output `θ(1 + μT)`, the case
  `p_H = 1`, `p_L = 0`: each type is paid her output `θ(1 + μT)` (if it exceeds `c`).
* (c) `labModel` (an `RSModel`: the high type is the "safe" type); `exercise_13_D_3c`: with
  strictly risk averse workers the low type receives the constant wage `p_L q_G + (1 - p_L) q_B`
  (full insurance at her expected output), the high type a wage schedule with `w_G > w_B` that
  breaks even on her and leaves the low type indifferent; instances with `u(x) = log(1 + x)`:
  `exercise_13_D_3c_exists` (`λ = 1/10`) and `exercise_13_D_3c_nonexistence` (`λ = 9/10`).

Departures: the cost enters as `u(w - c)` (a monetary cost); in (c) we assume `0 < p_L < p_H < 1`,
`q_B < q_G`, that the low type's expected output exceeds `c`, and that `u` maps onto `ℝ` from
its domain (as in Exercise 13.D.2); ties are broken in favour of the flatter wage schedule.
-/

namespace MWG.AdverseSelection

/-- The probability of the good output for type `b`. -/
def rnProb (pH pL : ℝ) (b : Bool) : ℝ := if b then pH else pL

/-- Expected output of type `b`. -/
def rnMean (pH pL qG qB : ℝ) (b : Bool) : ℝ := rnProb pH pL b * qG + (1 - rnProb pH pL b) * qB

/-- **Exercise 13.D.3(b)** (MWG, p. 476). The screening game with observable random output and
risk-neutral workers: contracts `(w_G, w_B)`, utility `E[w] - c`, profit `E[q - w]`. -/
noncomputable def rnGame (pH pL qG qB c lam : ℝ) : ScrGame where
  U b k := rnProb pH pL b * k.1 + (1 - rnProb pH pL b) * k.2 - c
  P b k := rnProb pH pL b * (qG - k.1) + (1 - rnProb pH pL b) * (qB - k.2)
  ρ _ := 0
  key k := k.1 - k.2
  lam := lam
  adm _ := True

namespace RnGame

variable {pH pL qG qB c lam : ℝ}

theorem inj (pH pL qG qB c lam : ℝ) : (rnGame pH pL qG qB c lam).Inj := by
  intro b k k' hu hk
  simp only [rnGame] at hu hk
  have h2 : k.2 = k'.2 := by
    have : rnProb pH pL b * (k.1 - k.2) = rnProb pH pL b * (k'.1 - k'.2) := by rw [hk]
    nlinarith
  exact Prod.ext (by linarith) h2

/-- Profit = expected output - cost - utility. -/
theorem P_eq (b : Bool) (k : ℝ × ℝ) :
    (rnGame pH pL qG qB c lam).P b k =
      rnMean pH pL qG qB b - c - (rnGame pH pL qG qB c lam).U b k := by
  simp only [rnGame, rnMean]; ring

theorem zero (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) {A₁ A₂ : Finset (ℝ × ℝ)}
    (h : (rnGame pH pL qG qB c lam).IsEq A₁ A₂) :
    (rnGame pH pL qG qB c lam).profit A₁ A₂ = 0 ∧
      (rnGame pH pL qG qB c lam).profit A₂ A₁ = 0 := by
  refine ScrGame.IsEq.zero (inj pH pL qG qB c lam) hl0 hl1 (fun δ k => (k.1 + δ, k.2 + δ))
    (fun _ _ _ _ => trivial) (fun δ b k => ?_) (fun δ k => ?_)
    (fun b k η hη => ⟨η / 2, half_pos hη, fun δ _ hδ => ?_⟩) h
  · simp only [rnGame]; ring
  · simp only [rnGame]; ring
  · simp only [rnGame]; ring_nf; linarith

end RnGame

/-- **Exercise 13.D.3(b)** (MWG, p. 476). With risk-neutral workers and observable output, in
every SPNE both firms earn zero, every type whose expected output exceeds `c` works and gets
utility `ȳ_b - c` (she is paid her expected output), and a type whose expected output is below
`c` does not work. -/
theorem exercise_13_D_3b {pH pL qG qB c lam : ℝ} (hl0 : 0 < lam) (hl1 : lam < 1)
    {A₁ A₂ : Finset (ℝ × ℝ)} (h : (rnGame pH pL qG qB c lam).IsEq A₁ A₂) :
    (rnGame pH pL qG qB c lam).profit A₁ A₂ = 0 ∧ (rnGame pH pL qG qB c lam).profit A₂ A₁ = 0 ∧
      (∀ b, c < rnMean pH pL qG qB b → ∃ k, (rnGame pH pL qG qB c lam).Chooses b (A₁ ∪ A₂) k ∧
        (rnGame pH pL qG qB c lam).U b k = rnMean pH pL qG qB b - c) ∧
      ∀ b, rnMean pH pL qG qB b < c → ¬ ∃ k, (rnGame pH pL qG qB c lam).Chooses b (A₁ ∪ A₂) k := by
  have hI := RnGame.inj pH pL qG qB c lam
  have hz := RnGame.zero hl0.le hl1.le h
  have hρ : ∀ b, (rnGame pH pL qG qB c lam).ρ b = 0 := fun _ => rfl
  -- "pay the output minus `ε`" attracts any type who gets less than `ȳ_b - c - ε`
  have dev : ∀ b ε, 0 < ε → 0 ≤ rnMean pH pL qG qB b - c - ε →
      (∀ k ∈ A₁ ∪ A₂, (rnGame pH pL qG qB c lam).U b k < rnMean pH pL qG qB b - c - ε) →
      False := by
    intro b ε hε h0 hlt
    have hU : ∀ b', (rnGame pH pL qG qB c lam).U b' (qG - ε, qB - ε) =
        rnMean pH pL qG qB b' - c - ε := fun b' => by simp only [rnGame, rnMean]; ring
    have hP : ∀ b', (rnGame pH pL qG qB c lam).P b' (qG - ε, qB - ε) = ε := fun b' => by
      simp only [rnGame]; ring
    cases b
    · exact ScrGame.IsEq.dev_false hI hl1 hl0.le h hz.1 (k' := (qG - ε, qB - ε)) trivial
        (by rw [hρ, hU]; exact h0)
        (fun k hk => by rw [hU]; exact hlt k (Finset.mem_union_right _ hk))
        (by rw [hP]; exact hε) (by rw [hP]; exact hε.le)
    · exact ScrGame.IsEq.dev_true_pos hI hl0 hl1.le h hz.1 (k' := (qG - ε, qB - ε)) trivial
        (by rw [hρ, hU]; exact h0)
        (fun k hk => by rw [hU]; exact hlt k (Finset.mem_union_right _ hk))
        (by rw [hP]; exact hε) (by rw [hP]; exact hε.le)
  have hA : ∀ b, c < rnMean pH pL qG qB b → ∃ k,
      (rnGame pH pL qG qB c lam).Chooses b (A₁ ∪ A₂) k ∧
        rnMean pH pL qG qB b - c ≤ (rnGame pH pL qG qB c lam).U b k := by
    intro b hb
    obtain ⟨k, hk⟩ : ∃ k, (rnGame pH pL qG qB c lam).Chooses b (A₁ ∪ A₂) k := by
      by_contra hno
      refine dev b ((rnMean pH pL qG qB b - c) / 2) (by linarith) (by linarith) fun k hk => ?_
      by_contra hle
      exact hno (ScrGame.exists_chooses b ⟨k, hk, by rw [hρ]; linarith⟩)
    refine ⟨k, hk, ?_⟩
    by_contra hlt
    rw [not_le] at hlt
    have h0 : (0 : ℝ) ≤ (rnGame pH pL qG qB c lam).U b k := hk.2.1
    refine dev b ((rnMean pH pL qG qB b - c - (rnGame pH pL qG qB c lam).U b k) / 2)
      (by linarith) (by linarith) fun k' hk' => ?_
    have := hk.2.2.1 k' hk'
    linarith
  have hB : ∀ b k, (rnGame pH pL qG qB c lam).Chooses b (A₁ ∪ A₂) k →
      (rnGame pH pL qG qB c lam).P b k ≤ 0 := by
    intro b k hk
    rw [RnGame.P_eq]
    have h0 : (0 : ℝ) ≤ (rnGame pH pL qG qB c lam).U b k := hk.2.1
    rcases lt_or_ge c (rnMean pH pL qG qB b) with hb | hb
    · obtain ⟨k', hk', hge⟩ := hA b hb
      rw [ScrGame.chooses_unique hI hk hk']
      linarith
    · linarith
  -- each type's contribution to total profit is `≤ 0`, and the total is `0`
  have htot := ScrGame.profit_add (G := rnGame pH pL qG qB c lam) A₁ A₂
  rw [hz.1, hz.2] at htot
  have hlam : (rnGame pH pL qG qB c lam).lam = lam := rfl
  rw [hlam] at htot
  have hle : ∀ b, (rnGame pH pL qG qB c lam).typeProfit b A₁ A₂ +
      (rnGame pH pL qG qB c lam).typeProfit b A₂ A₁ ≤ 0 := by
    intro b
    by_cases hex : ∃ k, (rnGame pH pL qG qB c lam).Chooses b (A₁ ∪ A₂) k
    · obtain ⟨k, hk⟩ := hex
      rw [ScrGame.typeProfit_add hI hk]; exact hB b k hk
    · rw [ScrGame.typeProfit_add_not hex]
  have hf := hle false
  have ht := hle true
  have hzero : ∀ b, (rnGame pH pL qG qB c lam).typeProfit b A₁ A₂ +
      (rnGame pH pL qG qB c lam).typeProfit b A₂ A₁ = 0 := by
    intro b; cases b <;> nlinarith
  refine ⟨hz.1, hz.2, fun b hb => ?_, fun b hb => ?_⟩
  · obtain ⟨k, hk, hge⟩ := hA b hb
    have := hzero b
    rw [ScrGame.typeProfit_add hI hk, RnGame.P_eq] at this
    exact ⟨k, hk, by linarith⟩
  · rintro ⟨k, hk⟩
    have := hzero b
    rw [ScrGame.typeProfit_add hI hk, RnGame.P_eq] at this
    have h0 : (0 : ℝ) ≤ (rnGame pH pL qG qB c lam).U b k := hk.2.1
    linarith

/-- **Exercise 13.D.3(b)** (MWG, p. 476), existence: both firms offering the contract that pays
the output, `(q_G, q_B)`, is an SPNE. -/
theorem exercise_13_D_3b_exists (pH pL qG qB c lam : ℝ) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) :
    (rnGame pH pL qG qB c lam).IsEq {(qG, qB)} {(qG, qB)} := by
  have hI := RnGame.inj pH pL qG qB c lam
  have hP0 : ∀ b, (rnGame pH pL qG qB c lam).P b (qG, qB) = 0 := fun b => by
    simp only [rnGame]; ring
  have hle : ∀ b B, (rnGame pH pL qG qB c lam).typeProfit b B {(qG, qB)} ≤ 0 := by
    intro b B
    by_cases hex : ∃ k, (rnGame pH pL qG qB c lam).Chooses b (B ∪ {(qG, qB)}) k
    · obtain ⟨k, hk⟩ := hex
      rw [ScrGame.typeProfit_of_chooses hI hk]
      have hge := hk.2.2.1 (qG, qB) (by simp)
      have hPk : (rnGame pH pL qG qB c lam).P b k ≤ 0 := by
        rw [RnGame.P_eq]
        have : (rnGame pH pL qG qB c lam).U b (qG, qB) = rnMean pH pL qG qB b - c := by
          simp only [rnGame, rnMean]
        linarith
      exact mul_nonpos_of_nonneg_of_nonpos (SigModel.share_nonneg _ _ _) hPk
    · rw [ScrGame.typeProfit_of_not hex]
  have hzero : (rnGame pH pL qG qB c lam).profit {(qG, qB)} {(qG, qB)} = 0 := by
    have : ∀ b, (rnGame pH pL qG qB c lam).typeProfit b {(qG, qB)} {(qG, qB)} = 0 := by
      intro b
      by_cases hex : ∃ k, (rnGame pH pL qG qB c lam).Chooses b ({(qG, qB)} ∪ {(qG, qB)}) k
      · obtain ⟨k, hk⟩ := hex
        rw [ScrGame.typeProfit_of_chooses hI hk]
        have : k = (qG, qB) := by
          have := hk.1; rw [Finset.union_self] at this; exact Finset.mem_singleton.1 this
        rw [this, hP0, mul_zero]
      · exact ScrGame.typeProfit_of_not hex
    simp [ScrGame.profit, this]
  have hdev : ∀ B, (rnGame pH pL qG qB c lam).Menu B →
      (rnGame pH pL qG qB c lam).profit B {(qG, qB)} ≤
        (rnGame pH pL qG qB c lam).profit {(qG, qB)} {(qG, qB)} := by
    intro B _
    rw [hzero]
    unfold ScrGame.profit
    have hlam : (rnGame pH pL qG qB c lam).lam = lam := rfl
    rw [hlam]
    nlinarith [hle false B, hle true B]
  exact ⟨fun _ _ => trivial, fun _ _ => trivial, hdev, hdev⟩

/-- **Exercise 13.D.3(a)** (MWG, p. 476). Deterministic output: type `θ` produces `θ(1 + μT)` at
the fixed task `T`; a contract pays `w_H` after output `θ_H(1 + μT)` and `w_L` after
`θ_L(1 + μT)` (the case `p_H = 1`, `p_L = 0` of `rnGame`). In every SPNE firms earn zero and each
type whose output exceeds `c` works and is paid her output; a type whose output is below `c`
does not work. -/
theorem exercise_13_D_3a {M : SigModel} (hM : M.Valid) (μ T c : ℝ) {A₁ A₂ : Finset (ℝ × ℝ)}
    (h : (rnGame 1 0 (M.θH * (1 + μ * T)) (M.θL * (1 + μ * T)) c M.lam).IsEq A₁ A₂) :
    (∀ b, c < M.θ b * (1 + μ * T) → ∃ k,
      (rnGame 1 0 (M.θH * (1 + μ * T)) (M.θL * (1 + μ * T)) c M.lam).Chooses b (A₁ ∪ A₂) k ∧
        (if b then k.1 else k.2) = M.θ b * (1 + μ * T)) ∧
      (∀ b, M.θ b * (1 + μ * T) < c → ¬ ∃ k,
        (rnGame 1 0 (M.θH * (1 + μ * T)) (M.θL * (1 + μ * T)) c M.lam).Chooses b (A₁ ∪ A₂) k) ∧
      (rnGame 1 0 (M.θH * (1 + μ * T)) (M.θL * (1 + μ * T)) c M.lam).profit A₁ A₂ = 0 ∧
      (rnGame 1 0 (M.θH * (1 + μ * T)) (M.θL * (1 + μ * T)) c M.lam).profit A₂ A₁ = 0 := by
  obtain ⟨hz1, hz2, hw, hn⟩ := exercise_13_D_3b hM.lam_pos hM.lam_lt h
  have hmean : ∀ b, rnMean 1 0 (M.θH * (1 + μ * T)) (M.θL * (1 + μ * T)) b =
      M.θ b * (1 + μ * T) := fun b => by
    cases b <;> simp [rnMean, rnProb, SigModel.θ]
  refine ⟨fun b hb => ?_, fun b hb => hn b (by rw [hmean]; exact hb), hz1, hz2⟩
  obtain ⟨k, hk, hu⟩ := hw b (by rw [hmean]; exact hb)
  refine ⟨k, hk, ?_⟩
  rw [hmean] at hu
  cases b <;> simp [rnGame, rnProb] at hu ⊢ <;> linarith

/-- **Exercise 13.D.3(a)** (MWG, p. 476), existence: paying each output level its value is an
SPNE. -/
theorem exercise_13_D_3a_exists {M : SigModel} (hM : M.Valid) (μ T c : ℝ) :
    (rnGame 1 0 (M.θH * (1 + μ * T)) (M.θL * (1 + μ * T)) c M.lam).IsEq
      {(M.θH * (1 + μ * T), M.θL * (1 + μ * T))} {(M.θH * (1 + μ * T), M.θL * (1 + μ * T))} :=
  exercise_13_D_3b_exists _ _ _ _ _ _ hM.lam_pos.le hM.lam_lt.le

namespace RSModel

/-- **Exercise 13.D.3(c)** (MWG, p. 476). Risk-averse workers: the screening model in utility
coordinates `v_s = u(w_s - c)`, with the high type (`p_H`) as the safe type, endowment
`(q_G - c, q_B - c)`, and outside option `ρ₀ = u(0)`. -/
def labModel (pH pL qG qB c lam : ℝ) (h : ℝ → ℝ) (ρ0 : ℝ) : RSModel where
  qS := pH
  qR := pL
  a₁ := qG - c
  a₂ := qB - c
  h := h
  ρS := ρ0
  ρR := ρ0
  lam := lam

/-- In the labour model with `h ρ₀ = 0` (`ρ₀ = u(0)`) and `ȳ_L > c` the outside options satisfy
the hypotheses of `rs_characterization`. -/
theorem lab_participation {pH pL qG qB c lam : ℝ} {h : ℝ → ℝ} {ρ0 vs : ℝ}
    (hM : (labModel pH pL qG qB c lam h ρ0).Valid) (hρ0 : h ρ0 = 0)
    (hv : h vs = (labModel pH pL qG qB c lam h ρ0).abar false)
    (hpos : 0 < (labModel pH pL qG qB c lam h ρ0).abar false) :
    (labModel pH pL qG qB c lam h ρ0).ρR < vs ∧
      ∃ e : ℝ × ℝ, (labModel pH pL qG qB c lam h ρ0).V true e =
        (labModel pH pL qG qB c lam h ρ0).ρS ∧
        0 ≤ (labModel pH pL qG qB c lam h ρ0).Pr true e ∧
        (labModel pH pL qG qB c lam h ρ0).V false e < vs := by
  set N := labModel pH pL qG qB c lam h ρ0
  have hhρ : N.h ρ0 = 0 := hρ0
  have hhv : N.h vs = N.abar false := hv
  have hlt : ρ0 < vs := hM.h_mono.lt_iff_lt.1 (by rw [hhρ, hhv]; exact hpos)
  have hab := abar_lt hM
  refine ⟨hlt, (ρ0, ρ0), V_diag N true ρ0, ?_, by rw [V_diag]; exact hlt⟩
  rw [Pr_diag, hhρ]; linarith

/-- **Exercise 13.D.3(c)** (MWG, p. 476). With strictly risk-averse workers, in every SPNE the
low-ability type receives the constant wage `h v* + c = p_L q_G + (1 - p_L) q_B` (her expected
output, full insurance), while the high-ability type receives a wage schedule `(w_G, w_B)`,
`w_G = h v₁ + c > w_B = h v₂ + c`, that breaks even on her and leaves the low-ability type
indifferent; both firms earn zero. -/
theorem exercise_13_D_3c {pH pL qG qB c lam : ℝ} {h : ℝ → ℝ} {ρ0 vs : ℝ}
    (hM : (labModel pH pL qG qB c lam h ρ0).Valid) (hρ0 : h ρ0 = 0)
    (hv : h vs + c = pL * qG + (1 - pL) * qB) (hpos : c < pL * qG + (1 - pL) * qB)
    {A₁ A₂ : Finset (ℝ × ℝ)} (heq : (labModel pH pL qG qB c lam h ρ0).game.IsEq A₁ A₂) :
    ∃ kS, (labModel pH pL qG qB c lam h ρ0).game.Chooses false (A₁ ∪ A₂) (vs, vs) ∧
      (labModel pH pL qG qB c lam h ρ0).game.Chooses true (A₁ ∪ A₂) kS ∧
      pH * (qG - (h kS.1 + c)) + (1 - pH) * (qB - (h kS.2 + c)) = 0 ∧
      pL * kS.1 + (1 - pL) * kS.2 = vs ∧ h kS.2 + c < h kS.1 + c ∧
      (labModel pH pL qG qB c lam h ρ0).game.profit A₁ A₂ = 0 ∧
      (labModel pH pL qG qB c lam h ρ0).game.profit A₂ A₁ = 0 := by
  have hv' : h vs = (labModel pH pL qG qB c lam h ρ0).abar false := by
    simp only [abar, q_false, labModel]; linarith
  have hpos' : 0 < (labModel pH pL qG qB c lam h ρ0).abar false := by
    simp only [abar, q_false, labModel]; linarith
  obtain ⟨hR, hS⟩ := lab_participation hM hρ0 hv' hpos'
  obtain ⟨kS, hkR, hkS, hP, hV, hlt, hz1, hz2⟩ := rs_characterization hM hv' hR hS heq
  refine ⟨kS, hkR, hkS, ?_, ?_, ?_, hz1, hz2⟩
  · simp only [Pr, q_true, labModel] at hP; linarith
  · simp only [V, q_false, labModel] at hV; linarith
  · have := hM.h_mono hlt
    change h kS.2 < h kS.1 at this
    linarith

/-- **Exercise 13.D.3(c)** (MWG, p. 476), existence: `u(x) = log(1 + x)` (`h v = e^v - 1`),
`q_G = 10`, `q_B = 2`, `c = 1`, `p_H = 2/3`, `p_L = 1/2`, `λ = 1/10`: both firms offering the
constant wage `6` and the schedule `(10, 4)` (utility levels `(log 6, log 6)`, `(log 9, log 4)`)
is an SPNE. -/
theorem exercise_13_D_3c_exists :
    (labModel (2 / 3) (1 / 2) 10 2 1 (1 / 10) (fun v => Real.exp v - 1) 0).game.IsEq
      {(Real.log 6, Real.log 6), (Real.log 9, Real.log 4)}
      {(Real.log 6, Real.log 6), (Real.log 9, Real.log 4)} := by
  have l9 : 0 < Real.log 9 := Real.log_pos (by norm_num)
  have l4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have l6 : 0 < Real.log 6 := Real.log_pos (by norm_num)
  refine log_isEq _ (κ := -1) (by norm_num [labModel]) (by norm_num [labModel])
    (by norm_num [labModel]) (by norm_num [labModel]) (by funext v; simp [labModel]; ring)
    (by norm_num [labModel]) (by norm_num [labModel]) ?_ ?_
  · simp only [labModel]; linarith
  · simp only [labModel, V, q_true]; nlinarith

/-- **Exercise 13.D.3(c)** (MWG, p. 476): an equilibrium need not exist. With the data of
`exercise_13_D_3c_exists` but `λ = 9/10`, no SPNE exists. -/
theorem exercise_13_D_3c_nonexistence :
    ¬ ∃ A₁ A₂, (labModel (2 / 3) (1 / 2) 10 2 1 (9 / 10) (fun v => Real.exp v - 1) 0).game.IsEq
      A₁ A₂ := by
  set N := labModel (2 / 3) (1 / 2) 10 2 1 (9 / 10) (fun v => Real.exp v - 1) 0
  have hN : N.Valid := log_valid N (κ := -1) (by norm_num [N, labModel])
    (by norm_num [N, labModel]) (by norm_num [N, labModel]) (by norm_num [N, labModel])
    (by funext v; simp [N, labModel]; ring) (by norm_num [N, labModel]) (by norm_num [N, labModel])
  have hv : N.h (Real.log 6) = N.abar false := by
    simp only [N, labModel, abar, q_false]; rw [Real.exp_log (by norm_num)]; norm_num
  obtain ⟨hR, hS⟩ := lab_participation (vs := Real.log 6) hN (by simp) hv
    (by simp only [labModel, abar, q_false]; norm_num)
  exact log_no_eq N (κ := -1) (by norm_num [N, labModel]) (by norm_num [N, labModel])
    (by norm_num [N, labModel]) (by norm_num [N, labModel]) (by funext v; simp [N, labModel]; ring)
    (by norm_num [N, labModel]) hR hS

end RSModel

end MWG.AdverseSelection
