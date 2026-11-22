/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGAdverseSelection.Signaling

/-!
# Separating and pooling equilibria of the signaling model

MWG, Section 13.C, pp. 453-458 and the small type on pp. 459-460.

All results are stated for home earnings `0 ≤ r < θ_H`; the main text is `r = 0`, where
`max(θ_L, r) = θ_L`, and the small type on p. 459 is `θ_L < r < θ_H`.

* `lemma_13_C_1`, `lemma_13_C_2`: in a separating PBE each type is paid her productivity and the
  low type gets no education.
* `separating_iff`: `(e*(θ_L), e*(θ_H)) = (0, e)` is a separating PBE outcome iff
  `θ_H - c(e, θ_L) ≤ max(θ_L, r) ≤ θ_H - c(e, θ_H)`; for `r = 0` this is `ẽ ≤ e ≤ e₁`
  (`separating_interval`, Figures 13.C.5-13.C.7), with the beliefs of Figure 13.C.6/13.C.7.
* `pooling_iff`: a pooling PBE at `e` exists iff `max(θ_L, r) ≤ max(E[θ], r) - c(e, θ_L)`; for
  `r = 0` this is `e ≤ e'` (Figures 13.C.9-13.C.10).
* Welfare: `separating_pareto_ranked`, `separating_vs_nosignal`, `high_type_worse_as_lam_to_one`
  (Figure 13.C.8), `pooling_dominated`.
* Refinement (pp. 457-458): `refined_separating`: with `μ(e) = 1` for `e > ẽ` the only separating
  education level of the high type is `ẽ`.
* Small type, `r ∈ (θ_L, θ_H)` with `E[θ] < r` (p. 459, Figure 13.C.12): `smalltype_pooling`,
  `smalltype_separating`, `smalltype_pareto`.
-/

namespace MWG.AdverseSelection

open Set

namespace SigModel

variable {M : SigModel}

/-- **Lemma 13.C.1** (MWG, p. 453). In any separating PBE the high type is paid `θ_H` and the
low type `θ_L` (in general, each ends up with `max(θ, r)`). -/
theorem lemma_13_C_1 (hM : M.Valid) {eS : Bool → ℝ} {μ : ℝ → ℝ} {wO : ℝ → Fin 2 → ℝ}
    (h : M.IsPBE eS μ wO) (hsep : Separating eS) :
    max (max (wO (eS true) 0) (wO (eS true) 1)) M.r = M.θH ∧
      max (max (wO (eS false) 0) (wO (eS false) 1)) M.r = max M.θL M.r := by
  obtain ⟨h0, hμ, -, hB, hNE⟩ := h
  obtain ⟨h1, h2⟩ := hB.1 hsep
  have hw : ∀ e, 0 ≤ e → max (max (wO e 0) (wO e 1)) M.r = max (M.expProd (μ e)) M.r :=
    fun e he => M.bertrand_wage (hM.θL_pos.le.trans (hM.expProd_mem (hμ e).1 (hμ e).2).1)
      _ (hNE e he)
  rw [hw _ (h0 true), hw _ (h0 false), h1, h2, expProd_one, expProd_zero,
    max_eq_left hM.r_lt.le]
  exact ⟨rfl, rfl⟩

/-- **Lemma 13.C.1** (MWG, p. 453), with `r = 0`: the wages are exactly `θ_H` and `θ_L`. -/
theorem lemma_13_C_1_r0 (hM : M.Valid) (hr : M.r = 0) {eS : Bool → ℝ} {μ : ℝ → ℝ}
    {wO : ℝ → Fin 2 → ℝ} (h : M.IsPBE eS μ wO) (hsep : Separating eS) :
    max (max (wO (eS true) 0) (wO (eS true) 1)) M.r = M.θH ∧
      max (max (wO (eS false) 0) (wO (eS false) 1)) M.r = M.θL := by
  have := lemma_13_C_1 hM h hsep
  rw [hr, max_eq_left hM.θL_pos.le] at this
  rw [hr]; exact this

/-- The low type's payoff in any PBE is at least `max(θ_L, r)` (she can choose `e = 0`). -/
theorem Valid.low_payoff (hM : M.Valid) {eS : Bool → ℝ} {μ : ℝ → ℝ} (h : M.IsPBERed eS μ) :
    max M.θL M.r ≤ M.redPay μ false (eS false) := by
  have := h.2.2.1 false 0 le_rfl
  unfold redPay at this ⊢
  rw [hM.c_zero, sub_zero] at this
  exact (max_le_max (hM.wage_mem h.2.1 0).1 le_rfl).trans this

/-- **Lemma 13.C.2** (MWG, p. 454). In any separating PBE the low type chooses `e = 0`. -/
theorem lemma_13_C_2 (hM : M.Valid) {eS : Bool → ℝ} {μ : ℝ → ℝ} (h : M.IsPBERed eS μ)
    (hsep : Separating eS) : eS false = 0 := by
  have hlow := hM.low_payoff h
  obtain ⟨-, h2⟩ := h.2.2.2.1 hsep
  unfold redPay at hlow
  rw [h2, expProd_zero] at hlow
  have hc : M.c (eS false) (M.θ false) ≤ 0 := by linarith
  by_contra hne
  have hpos := hM.c_pos false (lt_of_le_of_ne (h.1 false) (Ne.symm hne))
  linarith

/-- The separating beliefs of Figure 13.C.6/13.C.7: high ability iff `e ≥ e_H`. -/
noncomputable def sepBelief (eH : ℝ) : ℝ → ℝ := fun x => if eH ≤ x then 1 else 0

/-- The low type's no-mimicking condition forces `e > 0`, so `(0, e)` separates. -/
theorem separating_sep (hM : M.Valid) {e : ℝ} (he : 0 ≤ e)
    (hL : M.θH - M.c e M.θL ≤ max M.θL M.r) : Separating fun b : Bool => if b then e else 0 := by
  have hepos : 0 < e := by
    by_contra hle
    have he0 : e = 0 := le_antisymm (not_lt.1 hle) he
    rw [he0, hM.c_zero, sub_zero] at hL
    exact absurd hL (not_le.2 (max_lt hM.lt hM.r_lt))
  simp [Separating, hepos.ne]

/-- **Section 13.C** (MWG, pp. 454-455, Figures 13.C.6-13.C.7). Under the conditions of
`separating_iff`, the beliefs `μ(x) = 1` iff `x ≥ e` support `(0, e)` as a separating PBE. -/
theorem separating_sepBelief (hM : M.Valid) {e : ℝ} (he : 0 ≤ e)
    (hL : M.θH - M.c e M.θL ≤ max M.θL M.r) (hH : max M.θL M.r ≤ M.θH - M.c e M.θH) :
    M.IsPBERed (fun b => if b then e else 0) (sepBelief e) := by
  have hepos : 0 < e := by
    by_contra hle
    have he0 : e = 0 := le_antisymm (not_lt.1 hle) he
    rw [he0, hM.c_zero, sub_zero] at hL
    exact absurd hL (not_le.2 (max_lt hM.lt hM.r_lt))
  have hsep : Separating fun b : Bool => if b then e else 0 := by
    simp [Separating, hepos.ne]
  refine ⟨fun b => by cases b <;> simp [he], fun x => ?_, fun b x hx => ?_,
    ⟨fun _ => ?_, fun h => absurd h hsep⟩⟩
  · unfold sepBelief; split_ifs <;> norm_num
  · have hθH : max M.θH M.r = M.θH := max_eq_left hM.r_lt.le
    cases b
    · simp only [redPay, sepBelief, Bool.false_eq_true, ite_false, not_le.2 hepos, θ_false,
        hM.c_zero, sub_zero, expProd_zero]
      split_ifs with hex
      · rw [expProd_one, hθH]
        have := (hM.c_mono false).monotoneOn he hx hex
        simp only [θ_false] at this
        linarith
      · rw [expProd_zero]
        have := hM.c_nonneg false hx
        simp only [θ_false] at this
        linarith
    · simp only [redPay, sepBelief, ite_true, le_refl, expProd_one, hθH, θ_true]
      split_ifs with hex
      · rw [expProd_one, hθH]
        have := (hM.c_mono true).monotoneOn he hx hex
        simp only [θ_true] at this
        linarith
      · rw [expProd_zero]
        have := hM.c_nonneg true hx
        simp only [θ_true] at this
        linarith
  · simp [sepBelief, not_le.2 hepos]

/-- **Section 13.C** (MWG, pp. 454-455). `(0, e)` is the outcome of a separating PBE iff
`θ_H - c(e, θ_L) ≤ max(θ_L, r) ≤ θ_H - c(e, θ_H)`: the low type does not want to mimic the high
type, and the high type does not prefer to be taken for a low type. -/
theorem separating_iff (hM : M.Valid) {e : ℝ} (he : 0 ≤ e) :
    (∃ μ, M.IsPBERed (fun b => if b then e else 0) μ ∧ Separating fun b => if b then e else 0) ↔
      M.θH - M.c e M.θL ≤ max M.θL M.r ∧ max M.θL M.r ≤ M.θH - M.c e M.θH := by
  constructor
  · rintro ⟨μ, h, hsep⟩
    obtain ⟨h1, h2⟩ := h.2.2.2.1 hsep
    simp only [ite_true, Bool.false_eq_true, ite_false] at h1 h2
    have hL := h.2.2.1 false e he
    have hH := h.2.2.1 true 0 le_rfl
    simp only [redPay, h1, h2, expProd_one, expProd_zero, ite_true, Bool.false_eq_true,
      ite_false, θ_true, θ_false, hM.c_zero, sub_zero, max_eq_left hM.r_lt.le] at hL hH
    exact ⟨hL, hH⟩
  · rintro ⟨hL, hH⟩
    exact ⟨sepBelief e, separating_sepBelief hM he hL hH, separating_sep hM he hL⟩

/-- **Section 13.C** (MWG, pp. 454-455, Figures 13.C.5-13.C.7). With `r = 0`, let `ẽ` solve
`c(ẽ, θ_L) = θ_H - θ_L` and `e₁` solve `θ_H - c(e₁, θ_H) = θ_L`. Then `(0, e)` is a separating PBE
outcome iff `ẽ ≤ e ≤ e₁`. -/
theorem separating_interval (hM : M.Valid) (hr : M.r = 0) {et e1 e : ℝ} (het : 0 ≤ et)
    (he1 : 0 ≤ e1) (he : 0 ≤ e) (hcet : M.c et M.θL = M.θH - M.θL)
    (hce1 : M.θH - M.c e1 M.θH = M.θL) :
    (∃ μ, M.IsPBERed (fun b => if b then e else 0) μ ∧ Separating fun b => if b then e else 0) ↔
      et ≤ e ∧ e ≤ e1 := by
  rw [separating_iff hM he, hr, max_eq_left hM.θL_pos.le]
  have hL := (hM.c_mono false).le_iff_le het he
  have hH := (hM.c_mono true).le_iff_le he he1
  simp only [θ_false, θ_true] at hL hH
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨hL.1 (by linarith), hH.1 (by linarith)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith [hL.2 h1], by linarith [hH.2 h2]⟩

/-- The pooling beliefs: `λ` at the pooling level, low ability elsewhere (Figure 13.C.10). -/
noncomputable def poolBelief (M : SigModel) (ep : ℝ) : ℝ → ℝ :=
  fun x => if x = ep then M.lam else 0

/-- **Section 13.C** (MWG, pp. 456-457). Both types choosing `e` is a pooling PBE outcome iff the
low type prefers `(max(E[θ], r), e)` to `(max(θ_L, r), 0)`. -/
theorem pooling_iff (hM : M.Valid) {e : ℝ} (he : 0 ≤ e) :
    (∃ μ, M.IsPBERed (fun _ => e) μ) ↔ max M.θL M.r ≤ max M.Eθ M.r - M.c e M.θL := by
  constructor
  · rintro ⟨μ, h⟩
    have hlow := hM.low_payoff h
    have hB := h.2.2.2.2 rfl
    simp only [redPay, hB, expProd_lam, θ_false] at hlow
    exact hlow
  · intro hL
    refine ⟨M.poolBelief e, fun _ => he, fun x => ?_, fun b x hx => ?_,
      ⟨fun h => absurd rfl h, fun _ => by simp [poolBelief]⟩⟩
    · unfold poolBelief; split_ifs
      · exact ⟨hM.lam_pos.le, hM.lam_lt.le⟩
      · norm_num
    · have hpay : M.redPay (M.poolBelief e) b e = max M.Eθ M.r - M.c e (M.θ b) := by
        simp [redPay, poolBelief, expProd_lam]
      rw [hpay]
      by_cases hxe : x = e
      · rw [hxe, hpay]
      · simp only [redPay, poolBelief, hxe, ite_false, expProd_zero]
        have hc := hM.c_nonneg b hx
        cases b
        · simp only [θ_false] at hc ⊢; linarith
        · simp only [θ_true] at hc ⊢; linarith [hM.c_le he]

/-- **Section 13.C** (MWG, p. 457, Figure 13.C.9). With `r = 0`, if `c(e', θ_L) = E[θ] - θ_L`,
pooling at `e` is a PBE outcome iff `e ≤ e'`. -/
theorem pooling_interval (hM : M.Valid) (hr : M.r = 0) {ep e : ℝ} (hep : 0 ≤ ep) (he : 0 ≤ e)
    (hcep : M.c ep M.θL = M.Eθ - M.θL) : (∃ μ, M.IsPBERed (fun _ => e) μ) ↔ e ≤ ep := by
  rw [pooling_iff hM he, hr, max_eq_left hM.θL_pos.le,
    max_eq_left (hM.θL_pos.trans hM.Eθ_mem.1).le]
  have hL := (hM.c_mono false).le_iff_le he hep
  simp only [θ_false] at hL
  constructor
  · intro h; exact hL.1 (by linarith)
  · intro h; linarith [hL.2 h]

/-- **Section 13.C** (MWG, p. 455). Separating equilibria are Pareto ranked: firms earn zero
and the low type gets `max(θ_L, r)` in all of them, while the high type is strictly better off
with less education. -/
theorem separating_pareto_ranked (hM : M.Valid) {e e' : ℝ} (he : 0 ≤ e) (hlt : e < e') :
    M.θH - M.c e' M.θH < M.θH - M.c e M.θH := by
  have := hM.c_mono true he (he.trans hlt.le) hlt
  simp only [θ_true] at this
  linarith

/-- **Section 13.C** (MWG, p. 455). In a separating PBE the low type gets `max(θ_L, r)` and the
high type `θ_H - c(e*(θ_H), θ_H)`. -/
theorem separating_payoffs (hM : M.Valid) {eS : Bool → ℝ} {μ : ℝ → ℝ} (h : M.IsPBERed eS μ)
    (hsep : Separating eS) :
    M.redPay μ false (eS false) = max M.θL M.r ∧
      M.redPay μ true (eS true) = M.θH - M.c (eS true) M.θH := by
  obtain ⟨h1, h2⟩ := h.2.2.2.1 hsep
  have h0 := lemma_13_C_2 hM h hsep
  refine ⟨?_, ?_⟩
  · rw [h0] at h2 ⊢
    simp only [redPay, h2, expProd_zero, hM.c_zero, sub_zero]
  · simp only [redPay, h1, expProd_one, max_eq_left hM.r_lt.le, θ_true]

/-- **Section 13.C** (MWG, p. 456, Figure 13.C.8). With `r = 0`, compared with the outcome
without signaling (everybody paid `E[θ]`, no education), the low type is strictly worse off in
any separating PBE, and the high type is better off iff `θ_H - c(e*(θ_H), θ_H) ≥ E[θ]`. -/
theorem separating_vs_nosignal (hM : M.Valid) (hr : M.r = 0) :
    max M.θL M.r < M.Eθ ∧ ∀ e, (M.Eθ ≤ M.θH - M.c e M.θH ↔ M.Eθ ≤ M.θH - M.c e M.θH) := by
  rw [hr, max_eq_left hM.θL_pos.le]
  exact ⟨hM.Eθ_mem.1, fun _ => Iff.rfl⟩

/-- **Section 13.C** (MWG, p. 456, Figure 13.C.8(b)). For any positive education level `e`, if
the fraction `λ` of high-ability workers is close enough to `1`, the high type is worse off at
`(θ_H, e)` than at `(E[θ], 0)`: separating equilibria do not depend on `λ`, but `E[θ] → θ_H`. -/
theorem high_type_worse_as_lam_to_one (hM : M.Valid) {e : ℝ} (he : 0 < e) :
    ∃ l0 < 1, ∀ l, l0 < l → l < 1 → M.θH - M.c e M.θH < l * M.θH + (1 - l) * M.θL := by
  have hc : 0 < M.c e M.θH := by
    have := hM.c_pos true he; simpa only [θ_true] using this
  have hgap : 0 < M.θH - M.θL := by linarith [hM.lt]
  refine ⟨1 - M.c e M.θH / (M.θH - M.θL), by linarith [div_pos hc hgap], fun l hl _ => ?_⟩
  have : (1 - l) * (M.θH - M.θL) < M.c e M.θH := by
    have h' : 1 - l < M.c e M.θH / (M.θH - M.θL) := by linarith
    calc (1 - l) * (M.θH - M.θL) < M.c e M.θH / (M.θH - M.θL) * (M.θH - M.θL) :=
          mul_lt_mul_of_pos_right h' hgap
      _ = M.c e M.θH := div_mul_cancel₀ _ hgap.ne'
  nlinarith

/-- **Section 13.C** (MWG, p. 457). Pooling at `e = 0` gives each type `max(E[θ], r)`, exactly
the outcome without signaling, and weakly (for `e > 0` strictly) Pareto dominates pooling at
`e`. -/
theorem pooling_dominated (hM : M.Valid) (b : Bool) {e : ℝ} (he : 0 < e) :
    M.redPay (M.poolBelief e) b e < M.redPay (M.poolBelief 0) b 0 ∧
      M.redPay (M.poolBelief 0) b 0 = max M.Eθ M.r := by
  have hpay : ∀ x, M.redPay (M.poolBelief x) b x = max M.Eθ M.r - M.c x (M.θ b) := fun x => by
    simp [redPay, poolBelief, expProd_lam]
  rw [hpay, hpay, hM.c_zero, sub_zero]
  exact ⟨by linarith [hM.c_pos b he], rfl⟩

/-- **Section 13.C** (MWG, pp. 457-458). Above `ẽ` (where `θ_H - c(ẽ, θ_L) = max(θ_L, r)`) the low
type is worse off than at `e = 0` whatever the firms believe: the highest possible wage is
`θ_H`. -/
theorem low_never_above (hM : M.Valid) {et x : ℝ} (het : 0 ≤ et)
    (hcet : M.θH - M.c et M.θL = max M.θL M.r) (hx : et < x) :
    M.θH - M.c x M.θL < max M.θL M.r := by
  have := hM.c_mono false het (het.trans hx.le) hx
  simp only [θ_false] at this
  linarith

/-- **Section 13.C** (MWG, p. 458). If beliefs are reasonable in the sense that `μ(e) = 1` for
every `e > ẽ`, the only separating PBE has the high type choosing `ẽ`. -/
theorem refined_separating (hM : M.Valid) {et : ℝ} (het : 0 ≤ et)
    (hcet : M.θH - M.c et M.θL = max M.θL M.r) {eS : Bool → ℝ} {μ : ℝ → ℝ}
    (h : M.IsPBERed eS μ) (hsep : Separating eS) (hμ : ∀ x, et < x → μ x = 1) :
    eS true = et := by
  have h0 := lemma_13_C_2 hM h hsep
  have hpay := separating_payoffs hM h hsep
  obtain ⟨μ', hμ'⟩ : ∃ μ', M.IsPBERed (fun b => if b then eS true else 0) μ' ∧
      Separating fun b => if b then eS true else 0 := by
    refine ⟨μ, ?_, ?_⟩
    · have : (fun b : Bool => if b then eS true else 0) = eS := by
        funext b; cases b <;> simp [h0]
      rw [this]; exact h
    · simpa [Separating, ← h0] using hsep
  have hcond := (separating_iff hM (h.1 true)).1 ⟨μ', hμ'⟩
  have hge : et ≤ eS true := by
    have hL := (hM.c_mono false).le_iff_le het (h.1 true)
    simp only [θ_false] at hL
    exact hL.1 (by linarith [hcond.1])
  by_contra hne
  have hgt : et < eS true := lt_of_le_of_ne hge (Ne.symm hne)
  set x := (et + eS true) / 2
  have hx1 : et < x := by simp only [x]; linarith
  have hx2 : x < eS true := by simp only [x]; linarith
  have hdev := h.2.2.1 true x (het.trans hx1.le)
  rw [hpay.2] at hdev
  simp only [redPay, hμ x hx1, expProd_one, max_eq_left hM.r_lt.le, θ_true] at hdev
  have := hM.c_mono true (het.trans hx1.le) (h.1 true) hx2
  simp only [θ_true] at this
  linarith

/-- **Appendix 13.A** (MWG, p. 470). If `μ(e) = 1` for every `e > ẽ`, then in any pooling PBE the
high type gets at least `θ_H - c(ẽ, θ_H)` (she could deviate to just above `ẽ`); hence when the
high type prefers `(θ_H, ẽ)` to `(max(E[θ], r), 0)` no pooling PBE has such beliefs. -/
theorem pooling_eliminated (hM : M.Valid) {et : ℝ} (het : 0 ≤ et) {e : ℝ} {μ : ℝ → ℝ}
    (h : M.IsPBERed (fun _ => e) μ) (hμ : ∀ x, et < x → μ x = 1) :
    M.θH - M.c et M.θH ≤ M.redPay μ true e := by
  by_contra hlt
  rw [not_le] at hlt
  have hc : ContinuousWithinAt (fun x => M.c x (M.θ true)) (Ioi et) et :=
    ((hM.c_cont true) et het).mono (fun x hx => het.trans (le_of_lt hx))
  have hev : ∀ᶠ x in nhdsWithin et (Ioi et), M.c x M.θH < M.θH - M.redPay μ true e :=
    hc.eventually (gt_mem_nhds (by simp only [θ_true]; linarith))
  obtain ⟨x, hx, hxe⟩ := (hev.and self_mem_nhdsWithin).exists
  have hdev := h.2.2.1 true x (het.trans (le_of_lt hxe))
  simp only [redPay, hμ x hxe, expProd_one, max_eq_left hM.r_lt.le, θ_true] at hdev
  simp only [redPay, θ_true] at hx
  linarith

/-- **Section 13.C, small type** (MWG, p. 459). With `θ_L < r < θ_H` and `E[θ] < r`, every
pooling PBE has both types choosing `e = 0` and staying at home. -/
theorem smalltype_pooling (hM : M.Valid) (hr1 : M.θL < M.r) (hEr : M.Eθ < M.r) {e : ℝ}
    (he : 0 ≤ e) (h : ∃ μ, M.IsPBERed (fun _ => e) μ) : e = 0 ∧ M.Eθ < M.r := by
  have := (pooling_iff hM he).1 h
  rw [max_eq_right hr1.le, max_eq_right hEr.le] at this
  refine ⟨?_, hEr⟩
  by_contra hne
  have := hM.c_pos false (lt_of_le_of_ne he (Ne.symm hne))
  simp only [θ_false] at this
  linarith

/-- **Section 13.C, small type** (MWG, pp. 459-460, Figure 13.C.12). With `θ_L < r < θ_H`, `(0, e)`
is a separating PBE outcome iff `θ_H - c(e, θ_L) ≤ r ≤ θ_H - c(e, θ_H)`, i.e. `e ∈ [ẽ, e₂]`. -/
theorem smalltype_separating (hM : M.Valid) (hr1 : M.θL < M.r) {e : ℝ} (he : 0 ≤ e) :
    (∃ μ, M.IsPBERed (fun b => if b then e else 0) μ ∧ Separating fun b => if b then e else 0) ↔
      M.θH - M.c e M.θL ≤ M.r ∧ M.r ≤ M.θH - M.c e M.θH := by
  rw [separating_iff hM he, max_eq_right hr1.le]

/-- **Section 13.C, small type** (MWG, pp. 459-460). With `θ_L < r < θ_H` and `E[θ] < r`, in every
PBE each type gets at least `r`, her payoff without signaling (where nobody is employed), and the
low type gets exactly `r`; in a separating PBE with `θ_H - c(e*(θ_H), θ_H) > r` the high type is
strictly better off. -/
theorem smalltype_pareto (hM : M.Valid) (hr1 : M.θL < M.r) {eS : Bool → ℝ} {μ : ℝ → ℝ}
    (h : M.IsPBERed eS μ) :
    M.r ≤ M.redPay μ false (eS false) ∧ M.r ≤ M.redPay μ true (eS true) := by
  have hlow := hM.low_payoff h
  rw [max_eq_right hr1.le] at hlow
  refine ⟨hlow, ?_⟩
  have := h.2.2.1 true 0 le_rfl
  simp only [redPay, hM.c_zero, sub_zero] at this ⊢
  exact (le_max_right _ _).trans this

end SigModel

end MWG.AdverseSelection
