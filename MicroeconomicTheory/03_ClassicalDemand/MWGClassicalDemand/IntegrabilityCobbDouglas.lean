/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.IntegrabilityPDE
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Integrability: the Cobb-Douglas demand system (Exercise 3.H.6)

MWG, Exercise 3.H.6 (p. 102): the Walrasian demand `x_l(p, w) = α_l w/p_l` with `∑ α_l = 1`.

With the utility index `u` (a log scale), `E(p, u) = exp(u + ∑ α_l (log p_l - log α_l))`, i.e.
`e(p, u) = eᵘ ∏ (p_l/α_l)^{α_l}`:

* `E(·, u)` solves (3.H.2) (`cdL_solvesPDE`), is the support function of
  `{x ≫ 0 : ∑ α_l log x_l ≥ u}` (weighted AM-GM, `cdL_expenditure_eq_supportFn`), hence concave;
  it is homogeneous of degree one and nondecreasing (from Walras' law and `x ≥ 0`);
* the integrability theorem applies: the Cobb-Douglas demand is the Walrasian demand of the
  recovered preference (`exercise_3_H_6_rationalizes`);
* the recovered utility is the (log) Cobb-Douglas utility: `U(x) = ∑ α_l log x_l` for `x ≫ 0`
  (`exercise_3_H_6_utility`).
-/

namespace MWG.ClassicalDemand

open MWG.ConsumerChoice Kreps.PreferenceProperties Filter Topology

variable {L : ℕ}

/-- **Exercise 3.H.6** (MWG, p. 102). The Cobb-Douglas demand `x_l(p, w) = α_l w/p_l`. -/
noncomputable def cdDemandL (α : Fin L → ℝ) : DemandFunction L := fun p w l => α l * w / p l

/-- **Exercise 3.H.6** (MWG, p. 102). The expenditure function of the Cobb-Douglas demand,
`E(p, u) = exp(u + ∑ α_l (log p_l - log α_l)) = eᵘ ∏ (p_l/α_l)^{α_l}`. -/
noncomputable def cdExpL (α : Fin L → ℝ) (p : Fin L → ℝ) (u : ℝ) : ℝ :=
  Real.exp (u + ∑ l, α l * (Real.log (p l) - Real.log (α l)))

/-- The Cobb-Douglas utility on a log scale, `∑ α_l log x_l`. -/
noncomputable def cdLogUtility (α : Fin L → ℝ) (x : Fin L → ℝ) : ℝ := ∑ l, α l * Real.log (x l)

/-- `E(p, u) > 0`. -/
theorem cdExpL_pos (α p : Fin L → ℝ) (u : ℝ) : 0 < cdExpL α p u := Real.exp_pos _

/-- **Exercise 3.H.6** (MWG, p. 102). `E(·, u)` solves (3.H.2) for the Cobb-Douglas demand:
`∂E/∂p_l = α_l E/p_l = x_l(p, E)`. -/
theorem cdL_solvesPDE (α : Fin L → ℝ) (u : ℝ) :
    SolvesPDE (cdDemandL α) fun p => cdExpL α p u := by
  intro q hq
  have hlog : ∀ l, HasFDerivAt (fun p : Fin L → ℝ => α l * (Real.log (p l) - Real.log (α l)))
      (α l • ((q l)⁻¹ • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin L => ℝ) l)) q := by
    intro l
    have h1 := (hasFDerivAt_apply (𝕜 := ℝ) l q).log (hq l).ne'
    exact (h1.sub_const (Real.log (α l))).const_mul (α l)
  have hS := HasFDerivAt.fun_sum (u := Finset.univ) fun l _ => hlog l
  have hE := (hS.const_add u).exp
  refine hE.congr_fderiv ?_
  ext v
  simp only [smul_apply, sum_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
    dualityDotCLM_apply, dotProduct, cdDemandL]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  have := (hq l).ne'
  simp only [cdExpL]
  field_simp

/-- The weighted AM-GM inequality in the form used for the Cobb-Douglas expenditure function:
for `q, x ≫ 0`, `∑ α_l log(q_l x_l/α_l) ≤ log(q·x)`. -/
theorem cdL_amgm {α : Fin L → ℝ} (hα : ∀ l, 0 < α l) (hsum : ∑ l, α l = 1) {q x : Fin L → ℝ}
    (hq : StrictlyPositive q) (hx : ∀ l, 0 < x l) :
    ∑ l, α l * Real.log (q l * x l / α l) ≤ Real.log (q ⬝ᵥ x) := by
  have h := (strictConcaveOn_log_Ioi.concaveOn).le_map_sum (t := Finset.univ) (w := α)
    (p := fun l => q l * x l / α l) (fun l _ => (hα l).le) hsum
    (fun l _ => Set.mem_Ioi.mpr (div_pos (mul_pos (hq l) (hx l)) (hα l)))
  simp only [smul_eq_mul] at h
  have hsum' : ∑ l, α l * (q l * x l / α l) = q ⬝ᵥ x := by
    simp only [dotProduct]
    refine Finset.sum_congr rfl fun l _ => ?_
    field_simp [(hα l).ne']
  rw [hsum'] at h
  exact h

/-- For `q, x ≫ 0` with `∑ α_l log x_l ≥ u`, `E(q, u) ≤ q·x`. -/
theorem cdL_le_dot {α : Fin L → ℝ} (hα : ∀ l, 0 < α l) (hsum : ∑ l, α l = 1)
    {q x : Fin L → ℝ} (hq : StrictlyPositive q) (hx : ∀ l, 0 < x l) {u : ℝ}
    (hu : u ≤ cdLogUtility α x) : cdExpL α q u ≤ q ⬝ᵥ x := by
  have hamgm := cdL_amgm hα hsum hq hx
  have hne : (Finset.univ : Finset (Fin L)).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.sum_empty] at hsum
    norm_num at hsum
  have hpos : 0 < q ⬝ᵥ x := Finset.sum_pos (fun l _ => mul_pos (hq l) (hx l)) hne
  have hlog : ∀ l, Real.log (q l * x l / α l) =
      Real.log (q l) - Real.log (α l) + Real.log (x l) := fun l => by
    rw [Real.log_div (mul_pos (hq l) (hx l)).ne' (hα l).ne',
      Real.log_mul (hq l).ne' (hx l).ne']
    ring
  simp only [hlog, mul_add, Finset.sum_add_distrib] at hamgm
  rw [cdExpL, ← Real.exp_log hpos]
  apply Real.exp_le_exp.mpr
  simp only [cdLogUtility] at hu
  linarith

/-- The Cobb-Douglas at-least-as-good set `{x ≫ 0 : ∑ α_l log x_l ≥ u}`. -/
def cdUpperSet (α : Fin L → ℝ) (u : ℝ) : Set (Fin L → ℝ) :=
  {x | x ∈ nonnegOrthant L ∧ (∀ l, 0 < x l) ∧ u ≤ cdLogUtility α x}

/-- **Exercise 3.H.6** (MWG, p. 102). `E(p, u)` is the expenditure function of the Cobb-Douglas
utility: for `q ≫ 0` it is the support function of `{x ≫ 0 : ∑ α_l log x_l ≥ u}`, attained at
`x_l = α_l E/q_l = x_l(q, E)`. -/
theorem cdL_expenditure_eq_supportFn {α : Fin L → ℝ} (hα : ∀ l, 0 < α l)
    (hsum : ∑ l, α l = 1) {q : Fin L → ℝ} (hq : StrictlyPositive q) (u : ℝ) :
    cdDemandL α q (cdExpL α q u) ∈ supportArgmin (cdUpperSet α u) q ∧
      supportFn (cdUpperSet α u) q = cdExpL α q u := by
  set E := cdExpL α q u with hE
  have hEpos : 0 < E := cdExpL_pos α q u
  have hxpos : ∀ l, 0 < cdDemandL α q E l := fun l =>
    div_pos (mul_pos (hα l) hEpos) (hq l)
  have hval : q ⬝ᵥ cdDemandL α q E = E := by
    simp only [dotProduct, cdDemandL]
    have : ∀ l, q l * (α l * E / q l) = α l * E := fun l => by field_simp [(hq l).ne']
    simp only [this, ← Finset.sum_mul, hsum, one_mul]
  have hlogE : Real.log E = u + ∑ l, α l * (Real.log (q l) - Real.log (α l)) := by
    rw [hE, cdExpL, Real.log_exp]
  have hmem : cdDemandL α q E ∈ cdUpperSet α u := by
    refine ⟨fun l => (hxpos l).le, hxpos, ?_⟩
    have : cdLogUtility α (cdDemandL α q E) = u := by
      simp only [cdLogUtility, cdDemandL]
      have hl : ∀ l, Real.log (α l * E / q l) =
          Real.log (α l) + Real.log E - Real.log (q l) := fun l => by
        rw [Real.log_div (mul_pos (hα l) hEpos).ne' (hq l).ne',
          Real.log_mul (hα l).ne' hEpos.ne']
      simp only [hl]
      have : ∑ l, α l * (Real.log (α l) + Real.log E - Real.log (q l)) =
          Real.log E * ∑ l, α l - ∑ l, α l * (Real.log (q l) - Real.log (α l)) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun l _ => by ring
      rw [this, hsum, mul_one, hlogE]
      ring
    rw [this]
  have hargmin : cdDemandL α q E ∈ supportArgmin (cdUpperSet α u) q :=
    ⟨hmem, fun y hy => by rw [hval]; exact cdL_le_dot hα hsum hq hy.2.1 hy.2.2⟩
  exact ⟨hargmin, (supportFn_eq_of_mem_argmin hargmin).trans hval⟩

/-- **Exercise 3.H.6** (MWG, p. 102). `E(·, u)` is concave on `p ≫ 0`. -/
theorem cdL_concave {α : Fin L → ℝ} (hα : ∀ l, 0 < α l) (hsum : ∑ l, α l = 1) (u : ℝ) :
    ConcaveOn ℝ (posPrices L) fun p => cdExpL α p u := by
  have hne : (cdUpperSet α u).Nonempty := ⟨_, (cdL_expenditure_eq_supportFn hα hsum
    (q := fun _ => 1) (fun _ => one_pos) u).1.1⟩
  have hc := (supportFn_concaveOn hne).subset (s := posPrices L) (fun p hp => ⟨0, by
    rintro _ ⟨y, hy, rfl⟩
    exact Finset.sum_nonneg fun l _ => mul_nonneg (hp l).le (hy.1 l)⟩)
    (exp_convex_strictlyPositive L)
  exact hc.congr fun p hp => (cdL_expenditure_eq_supportFn hα hsum hp u).2

/-- Walras' law for the Cobb-Douglas demand: `p·x(p, w) = w`. -/
theorem cdDemandL_walras {α : Fin L → ℝ} (hsum : ∑ l, α l = 1) {p : Fin L → ℝ}
    (hp : StrictlyPositive p) (w : ℝ) : p ⬝ᵥ cdDemandL α p w = w := by
  simp only [dotProduct, cdDemandL]
  have : ∀ l, p l * (α l * w / p l) = α l * w := fun l => by field_simp [(hp l).ne']
  simp only [this, ← Finset.sum_mul, hsum, one_mul]

/-- **Exercise 3.H.6** (MWG, p. 102). The integrability theorem applies to the Cobb-Douglas
demand: for `p ≫ 0`, `w > 0`, the Walrasian demand of the preference recovered from `E` is
exactly `{(α_l w/p_l)_l}`. -/
theorem exercise_3_H_6_rationalizes {α : Fin L → ℝ} (hα : ∀ l, 0 < α l)
    (hsum : ∑ l, α l = 1) {p : Fin L → ℝ} (hp : StrictlyPositive p) {w : ℝ} (hw : 0 < w) :
    walrasianDemandPref (recoveredPref (cdExpL α)) p w = {cdDemandL α p w} := by
  refine integrability_theorem (fun u => cdL_concave hα hsum u)
    (fun u => pde_hd1 (cdL_solvesPDE α u) fun q hq => cdDemandL_walras hsum hq _)
    (fun u => pde_monotone (cdL_solvesPDE α u) fun q hq l =>
      div_nonneg (mul_nonneg (hα l).le (cdExpL_pos α q u).le) (hq l).le)
    (fun q _ a b hab => Real.exp_lt_exp.mpr (by linarith))
    (fun q _ => by unfold cdExpL; fun_prop)
    (fun q _ w' hw' => ⟨Real.log w' - ∑ l, α l * (Real.log (q l) - Real.log (α l)), by
      simp only [cdExpL, sub_add_cancel, Real.exp_log hw']⟩)
    (fun q u hq _ => cdL_solvesPDE α u q hq) hp hw

/-- **Exercise 3.H.6** (MWG, p. 102), "what is the consumer's utility function?". For `x ≫ 0`,
`x ∈ V_u` iff `∑ α_l log x_l ≥ u`, so the recovered utility is the Cobb-Douglas utility
`U(x) = ∑ α_l log x_l` (an increasing transformation of `∏ x_l^{α_l}`). -/
theorem exercise_3_H_6_utility {α : Fin L → ℝ} (hα : ∀ l, 0 < α l) (hsum : ∑ l, α l = 1)
    {x : Fin L → ℝ} (hx : ∀ l, 0 < x l) :
    (∀ u, x ∈ (recoveredSet fun p => cdExpL α p u) ↔ u ≤ cdLogUtility α x) ∧
      recoveredUtility (cdExpL α) x = (cdLogUtility α x : EReal) := by
  have hiff : ∀ u, x ∈ (recoveredSet fun p => cdExpL α p u) ↔ u ≤ cdLogUtility α x := by
    intro u
    constructor
    · intro hV
      set q : Fin L → ℝ := fun l => α l / x l with hqdef
      have hq : StrictlyPositive q := fun l => div_pos (hα l) (hx l)
      have h : cdExpL α q u ≤ q ⬝ᵥ x := hV.2 q hq
      have hqx : q ⬝ᵥ x = 1 := by
        rw [← hsum]
        simp only [dotProduct, hqdef]
        exact Finset.sum_congr rfl fun l _ => by field_simp [(hx l).ne']
      rw [hqx, cdExpL] at h
      have h2 := Real.add_one_le_exp (u + ∑ l, α l * (Real.log (q l) - Real.log (α l)))
      have hlq : ∀ l, Real.log (q l) - Real.log (α l) = -Real.log (x l) := fun l => by
        rw [hqdef]
        simp only
        rw [Real.log_div (hα l).ne' (hx l).ne']
        ring
      simp only [hlq] at h
      have : u + ∑ l, α l * -Real.log (x l) ≤ 0 := by
        by_contra hc
        rw [not_le] at hc
        have := Real.one_lt_exp_iff.mpr hc
        linarith
      simp only [mul_neg, Finset.sum_neg_distrib] at this
      simp only [cdLogUtility]
      linarith
    · intro hu
      exact ⟨fun l => (hx l).le, fun q hq => cdL_le_dot hα hsum hq hx hu⟩
  refine ⟨hiff, ?_⟩
  have hmono : ∀ q, StrictlyPositive q → Monotone (cdExpL α q) := fun q _ a b hab =>
    Real.exp_le_exp.mpr (by linarith)
  have hcont : ∀ q, StrictlyPositive q → Continuous (cdExpL α q) := fun q _ => by
    unfold cdExpL; fun_prop
  have key : ∀ u : ℝ, (u : EReal) ≤ recoveredUtility (cdExpL α) x ↔ u ≤ cdLogUtility α x :=
    fun u => (mem_recoveredSet_iff hmono hcont (fun l => (hx l).le) u).symm.trans (hiff u)
  apply le_antisymm
  · by_contra hc
    rw [not_le] at hc
    obtain ⟨v, hv1, hv2⟩ := EReal.lt_iff_exists_real_btwn.mp hc
    have := (key v).mp hv2.le
    exact absurd (EReal.coe_lt_coe_iff.mp hv1) (not_lt.mpr this)
  · exact (key _).mpr le_rfl

end MWG.ClassicalDemand
