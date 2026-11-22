/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGExternalitiesPublicGoods.Concavity
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Exercises 11.D.3-11.D.4 (MWG, p. 380)

* **Exercise 11.D.3** (learning by doing). `J > 1` identical price-taking firms with cost
  `c(qⱼ, Q)`, `Q = ∑ qⱼ`, `c_Q < 0`. With partial derivatives `c_q, c_Q` and second partials
  `c_qq, c_qQ, c_QQ`, the industry cost `C(Q) = J c(Q/J, Q)` has marginal social cost
  `MSC(Q) = c_q + J c_Q` (`exercise_11_D_3_msc`), whose derivative is
  `(1/J) c_qq + 2 c_qQ + J c_QQ`, positive by MWG's condition for `n = J`
  (`exercise_11_D_3_msc_deriv`). The symmetric equilibrium output `Q*` (price = private marginal
  cost `c_q(Q*/J, Q*)`) is below the optimal `Q°` (price = `MSC(Q°)`) (`exercise_11_D_3`); the
  per-unit subsidy `s = -J c_Q(Q°/J, Q°) > 0` makes `Q°` an equilibrium
  (`exercise_11_D_3_subsidy`); welfare `∫₀^Q P - C(Q)` is maximized at `Q°`
  (`exercise_11_D_3_optimal`). The conditions `c_q + J c_Q > 0` and the `n = 1` second-order
  condition are not needed for these conclusions.
* **Exercise 11.D.4** (nonhomogeneous externalities). Consumer utilities `φᵢ(h₁, …, h_J)`,
  concave and differentiable: `h°` is optimal iff `∑ᵢ ∂φᵢ/∂hⱼ ≤ -πⱼ'(hⱼ)`, equality if `hⱼ > 0`
  (`exercise_11_D_4_opt`); firm-specific taxes `tⱼ = -∑ᵢ ∂φᵢ/∂hⱼ(h°)` restore efficiency
  (`exercise_11_D_4_tax`); a uniform rate suffices (at an interior optimum) iff the marginal
  damages `∑ᵢ ∂φᵢ/∂hⱼ(h°)` are equal across firms (`exercise_11_D_4_uniform`), as in the
  homogeneous case of Section 11.D.
-/

namespace MWG.ExternalitiesPublicGoods

open MWG.CompetitiveMarkets

/-! ## Exercise 11.D.3 -/

/-- Evaluating `u • fst + v • snd` on `ℝ × ℝ`. -/
theorem clm2_apply (u v : ℝ) (w : ℝ × ℝ) :
    (u • ContinuousLinearMap.fst ℝ ℝ ℝ + v • ContinuousLinearMap.snd ℝ ℝ ℝ) w =
      u * w.1 + v * w.2 := by
  simp

/-- **Exercise 11.D.3**: the industry cost `C(Q) = J c(Q/J, Q)` of producing `Q` symmetrically
has derivative `c_q(Q/J, Q) + J c_Q(Q/J, Q)`, the marginal social cost. -/
theorem exercise_11_D_3_msc {c cq cQ : ℝ × ℝ → ℝ} {J : ℝ} (hJ : J ≠ 0)
    (hc : ∀ x, HasFDerivAt c (cq x • ContinuousLinearMap.fst ℝ ℝ ℝ +
      cQ x • ContinuousLinearMap.snd ℝ ℝ ℝ) x) (Q : ℝ) :
    HasDerivAt (fun Q => J * c (Q / J, Q)) (cq (Q / J, Q) + J * cQ (Q / J, Q)) Q := by
  have hpath : HasDerivAt (fun Q : ℝ => (Q / J, Q)) (1 / J, (1 : ℝ)) Q :=
    ((hasDerivAt_id Q).div_const J).prodMk (hasDerivAt_id Q)
  have h' := ((hc (Q / J, Q)).comp_hasDerivAt (f := fun Q : ℝ => (Q / J, Q)) Q hpath).const_mul J
  rw [clm2_apply] at h'
  exact (h'.congr_deriv (by field_simp) :
    HasDerivAt (fun Q => J * c (Q / J, Q)) (cq (Q / J, Q) + J * cQ (Q / J, Q)) Q)

/-- **Exercise 11.D.3**: the derivative of the marginal social cost is
`(1/J) c_qq + 2 c_qQ + J c_QQ` (with symmetric second partials). -/
theorem exercise_11_D_3_msc_deriv {cq cQ cqq cqQ cQQ : ℝ × ℝ → ℝ} {J : ℝ} (hJ : J ≠ 0)
    (hcq : ∀ x, HasFDerivAt cq (cqq x • ContinuousLinearMap.fst ℝ ℝ ℝ +
      cqQ x • ContinuousLinearMap.snd ℝ ℝ ℝ) x)
    (hcQ : ∀ x, HasFDerivAt cQ (cqQ x • ContinuousLinearMap.fst ℝ ℝ ℝ +
      cQQ x • ContinuousLinearMap.snd ℝ ℝ ℝ) x) (Q : ℝ) :
    HasDerivAt (fun Q => cq (Q / J, Q) + J * cQ (Q / J, Q))
      ((1 / J) * cqq (Q / J, Q) + 2 * cqQ (Q / J, Q) + J * cQQ (Q / J, Q)) Q := by
  have hpath : HasDerivAt (fun Q : ℝ => (Q / J, Q)) (1 / J, (1 : ℝ)) Q :=
    ((hasDerivAt_id Q).div_const J).prodMk (hasDerivAt_id Q)
  have h' := ((hcq (Q / J, Q)).comp_hasDerivAt (f := fun Q : ℝ => (Q / J, Q)) Q hpath).add
    (((hcQ (Q / J, Q)).comp_hasDerivAt (f := fun Q : ℝ => (Q / J, Q)) Q hpath).const_mul J)
  rw [clm2_apply, clm2_apply] at h'
  exact (h'.congr_deriv (by field_simp; ring) :
    HasDerivAt (fun Q => cq (Q / J, Q) + J * cQ (Q / J, Q))
      ((1 / J) * cqq (Q / J, Q) + 2 * cqQ (Q / J, Q) + J * cQQ (Q / J, Q)) Q)

/-- **Exercise 11.D.3** (MWG, p. 380), the comparison. Let `P` (inverse demand) be strictly
decreasing, `MSC = c_q + J c_Q` strictly increasing (MWG's second-order condition for `n = J`),
and `c_Q < 0`. If `Q*` is a symmetric competitive equilibrium (`P(Q*) = c_q(Q*/J, Q*)`) and `Q°`
satisfies `P(Q°) = MSC(Q°)`, then `Q* < Q°`: learning by doing is underexploited. -/
theorem exercise_11_D_3 {P : ℝ → ℝ} {cq cQ : ℝ × ℝ → ℝ} {J Qs Qo : ℝ}
    (hP : StrictAnti P) (hmsc : StrictMono fun Q => cq (Q / J, Q) + J * cQ (Q / J, Q))
    (hJ : 0 < J) (hcQ : ∀ x, cQ x < 0) (heq : P Qs = cq (Qs / J, Qs))
    (hopt : P Qo = cq (Qo / J, Qo) + J * cQ (Qo / J, Qo)) : Qs < Qo := by
  by_contra hle
  push Not at hle
  rcases eq_or_lt_of_le hle with h | h
  · rw [h] at hopt
    have := mul_neg_of_pos_of_neg hJ (hcQ (Qs / J, Qs))
    linarith
  · have h1 := hP h
    have h2 := hmsc h
    have := mul_neg_of_pos_of_neg hJ (hcQ (Qs / J, Qs))
    simp only at h2
    linarith

/-- **Exercise 11.D.3**: the per-unit subsidy `s = -J c_Q(Q°/J, Q°) > 0` restores efficiency: at
`Q°` the subsidized equilibrium condition `P(Q°) + s = c_q(Q°/J, Q°)` holds. -/
theorem exercise_11_D_3_subsidy {P : ℝ → ℝ} {cq cQ : ℝ × ℝ → ℝ} {J Qo : ℝ} (hJ : 0 < J)
    (hcQ : cQ (Qo / J, Qo) < 0) (hopt : P Qo = cq (Qo / J, Qo) + J * cQ (Qo / J, Qo)) :
    0 < -(J * cQ (Qo / J, Qo)) ∧ P Qo + -(J * cQ (Qo / J, Qo)) = cq (Qo / J, Qo) := by
  have := mul_neg_of_pos_of_neg hJ hcQ
  exact ⟨by linarith, by linarith⟩

/-- **Exercise 11.D.3**: with continuous strictly decreasing inverse demand `P` and convex
industry cost (increasing `MSC`), `Q° ≥ 0` with `P(Q°) ≤ MSC(Q°)` (equality if `Q° > 0`)
maximizes the aggregate surplus `∫₀^Q P - J c(Q/J, Q)` over `Q ≥ 0`. -/
theorem exercise_11_D_3_optimal {P : ℝ → ℝ} {c cq cQ : ℝ × ℝ → ℝ} {J Qo : ℝ} (hJ : J ≠ 0)
    (hPc : Continuous P) (hP : Antitone P)
    (hc : ∀ x, HasFDerivAt c (cq x • ContinuousLinearMap.fst ℝ ℝ ℝ +
      cQ x • ContinuousLinearMap.snd ℝ ℝ ℝ) x)
    (hmsc : Monotone fun Q => cq (Q / J, Q) + J * cQ (Q / J, Q))
    (hfoc : IsFOCSol (fun Q => P Q - (cq (Q / J, Q) + J * cQ (Q / J, Q))) 0 Qo) :
    ∀ Q, 0 ≤ Q → (∫ x in (0 : ℝ)..Q, P x) - J * c (Q / J, Q) ≤
      (∫ x in (0 : ℝ)..Qo, P x) - J * c (Qo / J, Qo) := by
  have hW : ∀ Q, HasDerivAt (fun Q => (∫ x in (0 : ℝ)..Q, P x) - J * c (Q / J, Q))
      (P Q - (cq (Q / J, Q) + J * cQ (Q / J, Q))) Q := fun Q =>
    (intervalIntegral.integral_hasDerivAt_right (hPc.intervalIntegrable _ _)
      hPc.aestronglyMeasurable.stronglyMeasurableAtFilter hPc.continuousAt).sub
      (exercise_11_D_3_msc hJ hc Q)
  have hanti : AntitoneOn (fun Q => P Q - (cq (Q / J, Q) + J * cQ (Q / J, Q))) (Set.Ici 0) :=
    fun a _ b _ hab => by
      have := hP hab; have := hmsc hab; simp only at *; linarith
  exact (kt_max_iff hW hanti hfoc.1).2 hfoc

/-! ## Exercise 11.D.4 -/

variable {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι]

/-- The aggregate surplus of Exercise 11.D.4: `∑ᵢ φᵢ(h) + ∑ⱼ πⱼ(hⱼ)`. -/
def d4Obj (φ : ι → (κ → ℝ) → ℝ) (pr : κ → ℝ → ℝ) (h : κ → ℝ) : ℝ :=
  ∑ i, φ i h + ∑ j, pr j (h j)

omit [DecidableEq κ] in
theorem d4Obj_concave (φ : ι → (κ → ℝ) → ℝ) (pr dpr : κ → ℝ → ℝ)
    (hconc : ∀ i, ConcaveOn ℝ (orthant κ) (φ i)) (hpr : ∀ j x, HasDerivAt (pr j) (dpr j x) x)
    (hdpr : ∀ j, AntitoneOn (dpr j) (Set.Ici 0)) : ConcaveOn ℝ (orthant κ) (d4Obj φ pr) := by
  refine ⟨convex_orthant κ, fun x hx y hy a b ha hb hab => ?_⟩
  simp only [d4Obj, smul_eq_mul]
  have h1 : ∀ i, a * φ i x + b * φ i y ≤ φ i (a • x + b • y) := fun i =>
    (hconc i).2 hx hy ha hb hab
  have h2 : ∀ j, a * pr j (x j) + b * pr j (y j) ≤ pr j (a * x j + b * y j) := fun j => by
    have hcj : ConcaveOn ℝ (Set.Ici 0) (pr j) := by
      refine ⟨convex_Ici 0, fun u hu v hv α β hα hβ hαβ => ?_⟩
      have t1 := foc_tangent_le (fun z _ => (hpr j z).hasDerivWithinAt) (hdpr j)
        (show 0 ≤ α * u + β * v by have := hu.out; have := hv.out; positivity) hu
      have t2 := foc_tangent_le (fun z _ => (hpr j z).hasDerivWithinAt) (hdpr j)
        (show 0 ≤ α * u + β * v by have := hu.out; have := hv.out; positivity) hv
      simp only [smul_eq_mul]
      have hb' : β = 1 - α := by linarith
      subst hb'
      nlinarith
    exact hcj.2 (Set.mem_Ici.2 (hx j)) (Set.mem_Ici.2 (hy j)) ha hb hab
  have s1 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => h1 i
  have s2 := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => h2 j
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at s1 s2
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [mul_add, mul_add]
  linarith

/-- **Exercise 11.D.4** (MWG, p. 380). With consumer utilities `φᵢ(h₁, …, h_J)` concave on the
orthant with derivatives `Dφᵢ(h)` and concave profits, `h ≥ 0` is optimal iff for every firm `j`,
`∑ᵢ ∂φᵢ/∂hⱼ(h) ≤ -πⱼ'(hⱼ)`, with equality if `hⱼ > 0`. -/
theorem exercise_11_D_4_opt (φ : ι → (κ → ℝ) → ℝ) (Dφ : ι → (κ → ℝ) →L[ℝ] ℝ)
    (pr dpr : κ → ℝ → ℝ) {h : κ → ℝ} (hφ : ∀ i, HasFDerivAt (φ i) (Dφ i) h)
    (hconc : ∀ i, ConcaveOn ℝ (orthant κ) (φ i)) (hpr : ∀ j x, HasDerivAt (pr j) (dpr j x) x)
    (hdpr : ∀ j, AntitoneOn (dpr j) (Set.Ici 0)) (hh : h ∈ orthant κ) :
    (∀ y ∈ orthant κ, d4Obj φ pr y ≤ d4Obj φ pr h) ↔
      ∀ j, ∑ i, Dφ i (Pi.single j 1) ≤ -dpr j (h j) ∧
        (0 < h j → ∑ i, Dφ i (Pi.single j 1) = -dpr j (h j)) := by
  set L : (κ → ℝ) →L[ℝ] ℝ :=
    ∑ i, Dφ i + ∑ j, dpr j (h j) • ContinuousLinearMap.proj (R := ℝ) j with hLdef
  have hL : HasFDerivAt (d4Obj φ pr) L h := by
    have h1 := HasFDerivAt.fun_sum (u := Finset.univ) fun i _ => hφ i
    have h2 := HasFDerivAt.fun_sum (u := Finset.univ) fun j (_ : j ∈ Finset.univ) =>
      ((hpr j (h j)).hasFDerivAt.comp h (hasFDerivAt_apply j h) :
        HasFDerivAt (fun g : κ → ℝ => pr j (g j)) _ h)
    have := h1.add h2
    convert this using 1
    · rfl
    · rw [hLdef]
      ext v
      simp [mul_comm]
  rw [orthant_kt_iff (d4Obj_concave φ pr dpr hconc hpr hdpr) hh hL]
  refine forall_congr' fun j => ?_
  have hLj : L (Pi.single j 1) = ∑ i, Dφ i (Pi.single j 1) + dpr j (h j) := by
    simp [L, Pi.single_apply]
  rw [hLj]
  constructor
  · rintro ⟨a, b⟩; exact ⟨by linarith, fun hp => by linarith [b hp]⟩
  · rintro ⟨a, b⟩; exact ⟨by linarith, fun hp => by linarith [b hp]⟩

omit [Fintype κ] [DecidableEq κ] [Fintype ι] in
/-- **Exercise 11.D.4**: firm `j` facing the per-unit tax `tⱼ` chooses `hⱼ` with `πⱼ'(hⱼ) ≤ tⱼ`
(equality if `hⱼ > 0`); this is the only choice when `πⱼ'` is strictly decreasing. -/
theorem firm_tax_iff {pr dpr : ℝ → ℝ} (hpr : ∀ x, HasDerivAt pr (dpr x) x)
    (hdpr : StrictAntiOn dpr (Set.Ici 0)) (t y : ℝ) :
    (0 ≤ y ∧ ∀ z, 0 ≤ z → pr z - t * z ≤ pr y - t * y) ↔ IsFOCSol dpr t y := by
  have hf : ∀ x, HasDerivAt (fun y => pr y - t * y) (dpr x - t) x := fun x => by
    have h2 : HasDerivAt (fun y => t * y) t x := by simpa using (hasDerivAt_id x).const_mul t
    exact (hpr x).sub h2
  have hanti : AntitoneOn (fun x => dpr x - t) (Set.Ici 0) := fun a ha b hb hab => by
    have := hdpr.antitoneOn ha hb hab; simp only; linarith
  rw [kt_isMax_iff hf hanti]
  simp only [IsFOCSol]
  constructor
  · rintro ⟨a, b, c⟩; exact ⟨a, by linarith, fun hp => by linarith [c hp]⟩
  · rintro ⟨a, b, c⟩; exact ⟨a, by linarith, fun hp => by linarith [c hp]⟩

/-- **Exercise 11.D.4**: the firm-specific taxes `tⱼ = -∑ᵢ ∂φᵢ/∂hⱼ(h°)` make `h°ⱼ` each firm's
(unique) choice. -/
theorem exercise_11_D_4_tax (φ : ι → (κ → ℝ) → ℝ) (Dφ : ι → (κ → ℝ) →L[ℝ] ℝ)
    (pr dpr : κ → ℝ → ℝ) {h : κ → ℝ} (hφ : ∀ i, HasFDerivAt (φ i) (Dφ i) h)
    (hconc : ∀ i, ConcaveOn ℝ (orthant κ) (φ i)) (hpr : ∀ j x, HasDerivAt (pr j) (dpr j x) x)
    (hdpr : ∀ j, StrictAntiOn (dpr j) (Set.Ici 0)) (hh : h ∈ orthant κ)
    (hopt : ∀ y ∈ orthant κ, d4Obj φ pr y ≤ d4Obj φ pr h) (j : κ) (y : ℝ) :
    (0 ≤ y ∧ ∀ z, 0 ≤ z → pr j z - (-∑ i, Dφ i (Pi.single j 1)) * z ≤
      pr j y - (-∑ i, Dφ i (Pi.single j 1)) * y) ↔ y = h j := by
  have hfoc := ((exercise_11_D_4_opt φ Dφ pr dpr hφ hconc hpr
    (fun j => (hdpr j).antitoneOn) hh).1 hopt) j
  have hj : IsFOCSol (dpr j) (-∑ i, Dφ i (Pi.single j 1)) (h j) :=
    ⟨hh j, by linarith [hfoc.1], fun hp => by linarith [hfoc.2 hp]⟩
  rw [firm_tax_iff (hpr j) (hdpr j)]
  exact ⟨fun hy => isFOCSol_unique (hdpr j) hy hj, fun hy => hy ▸ hj⟩

/-- **Exercise 11.D.4**: when should every firm face the same rate? At an optimum with all
`hⱼ° > 0`, a uniform tax `t` implements `h°` (each firm's choice is `hⱼ°`) iff the marginal
damages `-∑ᵢ ∂φᵢ/∂hⱼ(h°)` all equal `t`. -/
theorem exercise_11_D_4_uniform (φ : ι → (κ → ℝ) → ℝ) (Dφ : ι → (κ → ℝ) →L[ℝ] ℝ)
    (pr dpr : κ → ℝ → ℝ) {h : κ → ℝ} (hφ : ∀ i, HasFDerivAt (φ i) (Dφ i) h)
    (hconc : ∀ i, ConcaveOn ℝ (orthant κ) (φ i)) (hpr : ∀ j x, HasDerivAt (pr j) (dpr j x) x)
    (hdpr : ∀ j, StrictAntiOn (dpr j) (Set.Ici 0)) (hh : ∀ j, 0 < h j)
    (hopt : ∀ y ∈ orthant κ, d4Obj φ pr y ≤ d4Obj φ pr h) (t : ℝ) :
    (∀ j, IsFOCSol (dpr j) t (h j)) ↔ ∀ j, -∑ i, Dφ i (Pi.single j 1) = t := by
  have hfoc := (exercise_11_D_4_opt φ Dφ pr dpr hφ hconc hpr
    (fun j => (hdpr j).antitoneOn) (fun j => (hh j).le)).1 hopt
  constructor
  · intro ht j
    have := (ht j).2.2 (hh j)
    linarith [(hfoc j).2 (hh j)]
  · intro ht j
    exact ⟨(hh j).le, by linarith [ht j, (hfoc j).2 (hh j)], fun _ => by
      linarith [ht j, (hfoc j).2 (hh j)]⟩

end MWG.ExternalitiesPublicGoods
