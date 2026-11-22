/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGAdverseSelection.CrossSubsidy

/-!
# Refinements in the education signaling model

MWG, Appendix A, pp. 468-471 (and p. 458).

In the education game the firms' equilibrium responses to education `e` under a belief `m` that
the worker is of high ability are the Bertrand wages `mθ_H + (1 - m)θ_L` (`bertrand_wage`), so
`S*(Θ, e) = [θ_L, θ_H]` (`education_Sstar`). We specialize the definitions of Appendix A
(`MWGAdverseSelection.Refinements`) to this game, with beliefs described by `m ∈ [0, 1]`:

* `EqDomEd`: (13.AA.3); `notEqDomEd`: `Θ**(e)`; `ViolatesICEd`: (13.AA.4).
* `education_Theta_all` (p. 469): (13.AA.1) eliminates nothing.
* `education_IC_unique` (p. 471): with `r = 0` (and `c(·, θ_L)` unbounded, so that the
  relevant indifference curves cross), every PBE that passes the intuitive criterion is the best
  separating equilibrium `(0, ẽ)`; `education_IC_exists`: the best separating equilibrium (with
  the beliefs of Figure 13.C.7) passes it. The intuitive criterion thus selects the Riley
  outcome.
-/

namespace MWG.AdverseSelection

open Set

namespace SigModel

variable {M : SigModel}

/-- **Appendix A** (MWG, p. 469). `S*(Θ, e) = [θ_L, θ_H]`: the Bertrand wage for some belief. -/
theorem education_Sstar (hM : M.Valid) : M.expProd '' Icc 0 1 = Icc M.θL M.θH := by
  ext w
  constructor
  · rintro ⟨m, hm, rfl⟩; exact hM.expProd_mem hm.1 hm.2
  · rintro ⟨h1, h2⟩
    have hgap : 0 < M.θH - M.θL := by linarith [hM.lt]
    refine ⟨(w - M.θL) / (M.θH - M.θL), ⟨div_nonneg (by linarith) hgap.le,
      (div_le_one hgap).2 (by linarith)⟩, ?_⟩
    unfold expProd; field_simp; ring

/-- **Appendix A** (MWG, p. 469). (13.AA.1) eliminates nothing in the education game: for any
type and any two education levels, a sufficiently higher wage after `e` makes `e` at least as
good as `e'`. -/
theorem education_Theta_all (M : SigModel) (b : Bool) (e e' w' : ℝ) :
    ∃ w, w' - M.c e' (M.θ b) ≤ w - M.c e (M.θ b) :=
  ⟨w' - M.c e' (M.θ b) + M.c e (M.θ b), by ring_nf; rfl⟩

/-- **(13.AA.3)** (MWG, p. 471) in the education game: `e` is equilibrium dominated for type `b`
with equilibrium payoffs `uS` if every equilibrium response gives `b` less. -/
def EqDomEd (M : SigModel) (uS : Bool → ℝ) (e : ℝ) (b : Bool) : Prop :=
  ∀ m ∈ Icc (0 : ℝ) 1, max (M.expProd m) M.r - M.c e (M.θ b) < uS b

/-- `Θ**(e)` in the education game. -/
def notEqDomEd (M : SigModel) (uS : Bool → ℝ) (e : ℝ) : Set Bool := {b | ¬ M.EqDomEd uS e b}

/-- A belief `m` (probability of `θ_H`) concentrated on `T`. -/
def AdmissibleOn (T : Set Bool) (m : ℝ) : Prop :=
  m ∈ Icc (0 : ℝ) 1 ∧ (0 < m → true ∈ T) ∧ (m < 1 → false ∈ T)

open Classical in
/-- `Θ**(e)`, or all types if it is empty. -/
noncomputable def icSetEd (M : SigModel) (uS : Bool → ℝ) (e : ℝ) : Set Bool :=
  if (M.notEqDomEd uS e).Nonempty then M.notEqDomEd uS e else univ

/-- **(13.AA.4)** (MWG, p. 471) in the education game. -/
def ViolatesICEd (M : SigModel) (uS : Bool → ℝ) : Prop :=
  ∃ b e, 0 ≤ e ∧ ∀ m, AdmissibleOn (M.icSetEd uS e) m →
    uS b < max (M.expProd m) M.r - M.c e (M.θ b)

/-- Equilibrium payoffs of a reduced-form PBE. -/
def eqPay (M : SigModel) (eS : Bool → ℝ) (μ : ℝ → ℝ) : Bool → ℝ := fun b => M.redPay μ b (eS b)

/-- If `Θ**(e) = {θ_H}` and the high type gains from being recognized, the IC is violated. -/
theorem violates_of_high (hM : M.Valid) {uS : Bool → ℝ} {e : ℝ} (he : 0 ≤ e)
    (hL : M.EqDomEd uS e false) (hH : uS true < M.θH - M.c e M.θH) : M.ViolatesICEd uS := by
  have hHnd : true ∈ M.notEqDomEd uS e := fun h =>
    absurd (h 1 ⟨zero_le_one, le_rfl⟩) (by
      rw [expProd_one, max_eq_left hM.r_lt.le, θ_true]; exact not_lt.2 hH.le)
  have hset : M.icSetEd uS e = {true} := by
    have hns : M.notEqDomEd uS e = {true} := by
      ext b; cases b
      · simp only [mem_singleton_iff, Bool.false_eq_true, iff_false]
        exact fun h => h hL
      · simp only [mem_singleton_iff, iff_true]; exact hHnd
    simp [icSetEd, hns]
  refine ⟨true, e, he, fun m hm => ?_⟩
  rw [hset] at hm
  have hm1 : m = 1 := by
    by_contra hne
    have := hm.2.2 (lt_of_le_of_ne hm.1.2 hne)
    simp at this
  rw [hm1, expProd_one, max_eq_left hM.r_lt.le, θ_true]; exact hH

/-- **Appendix A** (MWG, p. 471). With `r = 0`, every PBE that passes the intuitive criterion is
the best separating equilibrium: the low type chooses `0`, the high type `ẽ`. (We assume
`c(·, θ_L)` unbounded, so that the low type's indifference curves reach `θ_H`.) -/
theorem education_IC_unique (hM : M.Valid) (hr : M.r = 0)
    (hunb : ∀ K, ∃ e, 0 ≤ e ∧ K ≤ M.c e M.θL) {et : ℝ} (het : 0 ≤ et)
    (hcet : M.c et M.θL = M.θH - M.θL) {eS : Bool → ℝ} {μ : ℝ → ℝ} (h : M.IsPBERed eS μ)
    (hIC : ¬ M.ViolatesICEd (M.eqPay eS μ)) :
    Separating eS ∧ eS false = 0 ∧ eS true = et := by
  have hθL0 : max M.θL M.r = M.θL := by rw [hr]; exact max_eq_left hM.θL_pos.le
  have hEr : max M.Eθ M.r = M.Eθ := by rw [hr]; exact max_eq_left (hM.θL_pos.trans
    hM.Eθ_mem.1).le
  have hmax : ∀ m ∈ Icc (0 : ℝ) 1, max (M.expProd m) M.r ≤ M.θH := fun m hm =>
    max_le (hM.expProd_mem hm.1 hm.2).2 hM.r_lt.le
  by_cases hsep : Separating eS
  · have h0 := lemma_13_C_2 hM h hsep
    have hpay := separating_payoffs hM h hsep
    refine ⟨hsep, h0, ?_⟩
    obtain ⟨-, hcond⟩ : True ∧ M.θH - M.c (eS true) M.θL ≤ M.θL := by
      have hsepf : Separating fun b : Bool => if b then eS true else 0 := by
        simpa [Separating, ← h0] using hsep
      have hfun : (fun b : Bool => if b then eS true else 0) = eS := by
        funext b; cases b <;> simp [h0]
      have := ((separating_iff hM (h.1 true)).1 ⟨μ, hfun ▸ h, hsepf⟩).1
      rw [hθL0] at this
      exact ⟨trivial, this⟩
    have hge : et ≤ eS true := by
      have hL := (hM.c_mono false).le_iff_le het (h.1 true)
      simp only [θ_false] at hL
      exact hL.1 (by linarith)
    by_contra hne
    have hgt : et < eS true := lt_of_le_of_ne hge (Ne.symm hne)
    set x := (et + eS true) / 2
    have hx1 : et < x := by simp only [x]; linarith
    have hx2 : x < eS true := by simp only [x]; linarith
    refine hIC (violates_of_high hM (het.trans hx1.le) (fun m hm => ?_) ?_)
    · simp only [eqPay, hpay.1, hθL0, θ_false]
      have := low_never_above hM het (by rw [hθL0]; linarith) hx1
      rw [hθL0] at this
      linarith [hmax m hm]
    · simp only [eqPay, hpay.2]
      have := hM.c_mono true (het.trans hx1.le) (h.1 true) hx2
      simp only [θ_true] at this
      linarith
  · exfalso
    have hpool : Pooling eS := not_not.1 hsep
    obtain ⟨ep, hepd⟩ : ∃ ep, eS true = ep := ⟨_, rfl⟩
    have hμp : μ ep = M.lam := hepd ▸ h.2.2.2.2 hpool
    have hpayp : ∀ b, M.eqPay eS μ b = M.Eθ - M.c ep (M.θ b) := by
      intro b
      have hb : eS b = ep := by
        cases b with
        | false => rw [hpool, hepd]
        | true => exact hepd
      simp only [eqPay, redPay, hb, hμp, expProd_lam, hEr]
    set D := M.θH - M.Eθ
    have hD : 0 < D := by simp only [D]; linarith [hM.Eθ_mem.2]
    have hep : 0 ≤ ep := hepd ▸ h.1 true
    obtain ⟨E, hE0, hE⟩ := hunb (M.c ep M.θL + D)
    have hEep : ep < E := by
      by_contra hle
      have := (hM.c_mono false).monotoneOn hE0 hep (not_lt.1 hle)
      simp only [θ_false] at this
      linarith
    have hcontL : ContinuousOn (fun x => M.c x M.θL) (Icc ep E) :=
      (hM.c_cont false).mono fun x hx => hep.trans hx.1
    obtain ⟨eL, heL, heLv⟩ := intermediate_value_Icc hEep.le hcontL
      ⟨by linarith, hE⟩
    have heL0 : ep < eL := by
      rcases eq_or_lt_of_le heL.1 with he | he
      · rw [← he] at heLv; linarith
      · exact he
    have hsc := hM.sc ep eL hep heL0
    have hcH : ContinuousWithinAt (fun x => M.c x (M.θ true)) (Ioi eL) eL :=
      ((hM.c_cont true) eL (hep.trans heL0.le)).mono fun x hx =>
        (hep.trans heL0.le).trans (le_of_lt hx)
    have hev : ∀ᶠ x in nhdsWithin eL (Ioi eL), M.c x M.θH < M.c ep M.θH + D :=
      hcH.eventually (gt_mem_nhds (by simp only [θ_true]; linarith))
    obtain ⟨x, hx, hxe⟩ := (hev.and self_mem_nhdsWithin).exists
    have hx0 : 0 ≤ x := (hep.trans heL0.le).trans (le_of_lt hxe)
    have hLx : M.c ep M.θL + D < M.c x M.θL := by
      have := hM.c_mono false (hep.trans heL0.le) hx0 hxe
      simp only [θ_false] at this; linarith
    refine hIC (violates_of_high hM hx0 (fun m hm => ?_) ?_)
    · rw [hpayp]; simp only [θ_false, D] at hLx ⊢; linarith [hmax m hm]
    · rw [hpayp]; simp only [θ_true, D] at hx ⊢; linarith

/-- **Appendix A** (MWG, p. 471). With `r = 0`, the best separating equilibrium `(0, ẽ)` with the
beliefs of Figure 13.C.6 (`μ(e) = 1` iff `e ≥ ẽ`) is a PBE that passes the intuitive
criterion. -/
theorem education_IC_exists (hM : M.Valid) (hr : M.r = 0) {et : ℝ} (het : 0 ≤ et)
    (hcet : M.c et M.θL = M.θH - M.θL) :
    M.IsPBERed (fun b => if b then et else 0) (sepBelief et) ∧
      ¬ M.ViolatesICEd (M.eqPay (fun b => if b then et else 0) (sepBelief et)) := by
  have hθL0 : max M.θL M.r = M.θL := by rw [hr]; exact max_eq_left hM.θL_pos.le
  have hcH : M.c et M.θH ≤ M.θH - M.θL := hcet ▸ hM.c_le het
  have hcond : M.θH - M.c et M.θL ≤ max M.θL M.r ∧ max M.θL M.r ≤ M.θH - M.c et M.θH := by
    rw [hθL0]; constructor <;> linarith
  have hpbe := separating_sepBelief hM het hcond.1 hcond.2
  have hsep := separating_sep hM het hcond.1
  refine ⟨hpbe, ?_⟩
  have hpay := separating_payoffs hM hpbe hsep
  simp only [ite_true, Bool.false_eq_true, ite_false] at hpay
  have huL : M.eqPay (fun b => if b then et else 0) (sepBelief et) false = M.θL := by
    simp only [eqPay, Bool.false_eq_true, ite_false]; rw [hpay.1, hθL0]
  have huH : M.eqPay (fun b => if b then et else 0) (sepBelief et) true =
      M.θH - M.c et M.θH := by
    simp only [eqPay, ite_true]; exact hpay.2
  set uS := M.eqPay (fun b => if b then et else 0) (sepBelief et)
  have hmax : ∀ m ∈ Icc (0 : ℝ) 1, max (M.expProd m) M.r ≤ M.θH := fun m hm =>
    max_le (hM.expProd_mem hm.1 hm.2).2 hM.r_lt.le
  rintro ⟨b, e, he, hv⟩
  -- an admissible belief always exists
  have hadm : ∀ T : Set Bool, T.Nonempty → ∃ m, AdmissibleOn T m := by
    rintro T ⟨b', hb'⟩
    cases b'
    · exact ⟨0, ⟨le_rfl, zero_le_one⟩, fun h => absurd h (lt_irrefl _), fun _ => hb'⟩
    · exact ⟨1, ⟨zero_le_one, le_rfl⟩, fun _ => hb', fun h => absurd h (lt_irrefl _)⟩
  have hne : (M.icSetEd uS e).Nonempty := by
    unfold icSetEd; split_ifs with h
    exacts [h, ⟨true, trivial⟩]
  rcases le_or_gt et e with hle | hlt
  · obtain ⟨m, hm⟩ := hadm _ hne
    have := hv m hm
    have hcm := (hM.c_mono b).monotoneOn het he hle
    cases b
    · simp only [θ_false, huL] at this hcm; linarith [hmax m hm.1]
    · simp only [θ_true, huH] at this hcm; linarith [hmax m hm.1]
  · -- the low type is not equilibrium dominated below `ẽ`
    have hLnd : false ∈ M.notEqDomEd uS e := by
      intro hd
      have := hd 1 ⟨zero_le_one, le_rfl⟩
      rw [expProd_one, max_eq_left hM.r_lt.le, huL, θ_false] at this
      have hc := hM.c_mono false he het hlt
      simp only [θ_false] at hc
      linarith
    have hset : false ∈ M.icSetEd uS e := by
      simp only [icSetEd, show (M.notEqDomEd uS e).Nonempty from ⟨false, hLnd⟩, ↓reduceIte]
      exact hLnd
    have := hv 0 ⟨⟨le_rfl, zero_le_one⟩, fun h => absurd h (lt_irrefl _), fun _ => hset⟩
    rw [expProd_zero, hθL0] at this
    have hc := hM.c_nonneg b he
    cases b
    · simp only [θ_false, huL] at this hc; linarith
    · simp only [θ_true, huH] at this hc; linarith

/-- **Appendix A** (MWG, p. 471), an instance: in the model `crossModel` of Exercise 13.C.3
(`ẽ = 1`), the PBEs passing the intuitive criterion are exactly those with outcome `(0, 1)`. -/
theorem education_IC_instance :
    (crossModel.IsPBERed (fun b => if b then 1 else 0) (sepBelief 1) ∧
      ¬ crossModel.ViolatesICEd (crossModel.eqPay (fun b => if b then 1 else 0) (sepBelief 1))) ∧
    ∀ eS μ, crossModel.IsPBERed eS μ → ¬ crossModel.ViolatesICEd (crossModel.eqPay eS μ) →
      eS false = 0 ∧ eS true = 1 := by
  have hr : crossModel.r = 0 := rfl
  have hc : crossModel.c 1 crossModel.θL = crossModel.θH - crossModel.θL := by
    rw [crossModel_cL]; norm_num [crossModel]
  refine ⟨education_IC_exists crossModel_valid hr zero_le_one hc, fun eS μ h hIC => ?_⟩
  have := education_IC_unique crossModel_valid hr (fun K => ⟨max K 0, le_max_right _ _, by
    rw [crossModel_cL]; exact le_max_left _ _⟩) zero_le_one hc h hIC
  exact ⟨this.2.1, this.2.2⟩

end SigModel

end MWG.AdverseSelection
