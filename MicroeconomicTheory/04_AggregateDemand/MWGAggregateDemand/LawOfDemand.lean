/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGAggregateDemand.Basic
import MWGClassicalDemand.RelationsBasic
import MWGClassicalDemand.UMPExercises
import MWGClassicalDemand.UtilityExercises
import MWGConsumerChoice.DemandCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Aggregate demand and the weak axiom: the uncompensated law of demand

MWG, Section 4.C, pp. 109-112, and Exercises 4.C.1 (p. 124).

* **Definition 4.C.1** (p. 109): the weak axiom for aggregate demand is MWG Chapter 2's
  `WeakAxiom` applied to `x(p, w) = ∑ᵢ xᵢ(p, αᵢ w)` (`definition_4_C_1`).
* (4.C.1)-(4.C.2) (pp. 110-111): a price-wealth change compensated for every consumer satisfies
  the compensated law of demand in the aggregate (`aggregate_compensated_law`).
* **Definition 4.C.2** (p. 111): the uncompensated law of demand `UncompensatedLawOfDemand`.
* **Exercise 4.C.1** (p. 124; claims on p. 111): ULD implies `D_p x(p, w)` negative
  semidefinite (`exercise_4_C_1_nsd`); negative definiteness for all `p` implies ULD
  (`exercise_4_C_1_nd`).
* **Proposition 4.C.1** (p. 111): ULD is preserved under addition, and ULD with homogeneity and
  Walras' law implies the weak axiom (`uld_shareDemand`, `weakAxiom_of_uld`,
  `proposition_4_C_1`). The book allows shares `αᵢ ≥ 0`; a consumer with `αᵢ = 0` has zero
  wealth, outside MWG Chapter 2's domain `w > 0`, so the shares here are positive
  (correction 2).
* **Proposition 4.C.2** (p. 112): a homothetic preference generates a demand satisfying ULD.
  The book proves the differentiable case under the extra hypothesis that the Slutsky matrix is
  negative definite off the price ray; `proposition_4_C_2` proves the statement for every
  utility homogeneous of degree one with single-valued demand, with no differentiability, by a
  revealed-preference and AM-GM argument. The book's differential argument is
  `proposition_4_C_2_differential` (`D_p x = S - (1/w) x xᵀ`).
-/

namespace MWG.AggregateDemand

open MWG.ConsumerChoice MWG.ClassicalDemand Filter Topology

variable {L I : ℕ}

/-- **Definition 4.C.1** (MWG, p. 109). The aggregate demand function `x(p, w)` satisfies the
weak axiom if `p·x(p', w') ≤ w` and `x(p, w) ≠ x(p', w')` imply `p'·x(p, w) > w'`; this is
MWG Chapter 2's `WeakAxiom` (Definition 2.F.1) for the aggregate demand function. -/
theorem definition_4_C_1 (xs : Fin I → DemandFunction L) (α : Fin I → ℝ) :
    WeakAxiom (shareDemand xs α) ↔ ∀ p w p' w', PWDomain p w → PWDomain p' w' →
      p ⬝ᵥ shareDemand xs α p' w' ≤ w → shareDemand xs α p' w' ≠ shareDemand xs α p w →
        w' < p' ⬝ᵥ shareDemand xs α p w :=
  Iff.rfl

/-- **Definition 4.C.2** (MWG, p. 111). The uncompensated law of demand (ULD):
`(p' - p)·[x(p', w) - x(p, w)] ≤ 0` for all `p, p' ≫ 0` and `w > 0`, with strict inequality
whenever `x(p', w) ≠ x(p, w)`. The definition applies to individual and to aggregate demand. -/
def UncompensatedLawOfDemand (x : DemandFunction L) : Prop :=
  ∀ p p' w, PWDomain p w → StrictlyPositive p' →
    (p' - p) ⬝ᵥ (x p' w - x p w) ≤ 0 ∧
      (x p' w ≠ x p w → (p' - p) ⬝ᵥ (x p' w - x p w) < 0)

/-- **Section 4.C** (MWG, pp. 110-111), equations (4.C.1)-(4.C.2). If every consumer's demand
satisfies Walras' law and the weak axiom, then a price-wealth change from `(p, w)` to
`(p', w')` that is compensated for every consumer, `αᵢ w' = p'·xᵢ(p, αᵢ w)`, satisfies the
compensated law of demand in the aggregate: `(p' - p)·[x(p', w') - x(p, w)] ≤ 0`, strictly if
`x(p', w') ≠ x(p, w)`. -/
theorem aggregate_compensated_law {xs : Fin I → DemandFunction L} {α : Fin I → ℝ}
    (hα : ∀ i, 0 < α i) (hW : ∀ i, WalrasLaw (xs i)) (hWA : ∀ i, WeakAxiom (xs i))
    {p p' : Fin L → ℝ} {w w' : ℝ} (hd : PWDomain p w) (hd' : PWDomain p' w')
    (hcomp : ∀ i, α i * w' = p' ⬝ᵥ xs i p (α i * w)) :
    (p' - p) ⬝ᵥ (shareDemand xs α p' w' - shareDemand xs α p w) ≤ 0 ∧
      (shareDemand xs α p' w' ≠ shareDemand xs α p w →
        (p' - p) ⬝ᵥ (shareDemand xs α p' w' - shareDemand xs α p w) < 0) := by
  have hi : ∀ i, (p' - p) ⬝ᵥ (xs i p' (α i * w') - xs i p (α i * w)) ≤ 0 ∧
      (xs i p (α i * w) ≠ xs i p' (α i * w') →
        (p' - p) ⬝ᵥ (xs i p' (α i * w') - xs i p (α i * w)) < 0) := by
    intro i
    have hdi : PWDomain p (α i * w) := ⟨hd.1, mul_pos (hα i) hd.2⟩
    have hpos : 0 < compensatedWealth (xs i) p (α i * w) p' := by
      rw [compensatedWealth, ← hcomp i]
      exact mul_pos (hα i) hd'.2
    have := proposition_2_F_1_i (hW i) (hWA i) p (α i * w) p' hdi hd'.1 hpos
    rwa [compensatedWealth, ← hcomp i] at this
  have hsum : (p' - p) ⬝ᵥ (shareDemand xs α p' w' - shareDemand xs α p w) =
      ∑ i, (p' - p) ⬝ᵥ (xs i p' (α i * w') - xs i p (α i * w)) := by
    simp only [shareDemand, ← Finset.sum_sub_distrib, dotProduct_sum]
  rw [hsum]
  refine ⟨Finset.sum_nonpos fun i _ => (hi i).1, fun hne => ?_⟩
  obtain ⟨i, hi'⟩ : ∃ i, xs i p' (α i * w') ≠ xs i p (α i * w) := by
    by_contra hall
    push Not at hall
    exact hne (Finset.sum_congr rfl fun i _ => hall i)
  have := Finset.sum_lt_sum (s := Finset.univ) (g := fun _ => (0 : ℝ)) (fun j _ => (hi j).1)
    ⟨i, Finset.mem_univ i, (hi i).2 (Ne.symm hi')⟩
  simpa using this

/-- **Proposition 4.C.1** (MWG, p. 111), first part. If every consumer's demand satisfies the
ULD, so does aggregate demand `x(p, w) = ∑ᵢ xᵢ(p, αᵢ w)` (shares `αᵢ > 0`). -/
theorem uld_shareDemand {xs : Fin I → DemandFunction L} {α : Fin I → ℝ}
    (hα : ∀ i, 0 < α i) (hU : ∀ i, UncompensatedLawOfDemand (xs i)) :
    UncompensatedLawOfDemand (shareDemand xs α) := by
  intro p p' w hd hp'
  have hi : ∀ i, (p' - p) ⬝ᵥ (xs i p' (α i * w) - xs i p (α i * w)) ≤ 0 ∧
      (xs i p' (α i * w) ≠ xs i p (α i * w) →
        (p' - p) ⬝ᵥ (xs i p' (α i * w) - xs i p (α i * w)) < 0) :=
    fun i => hU i p p' (α i * w) ⟨hd.1, mul_pos (hα i) hd.2⟩ hp'
  have hsum : (p' - p) ⬝ᵥ (shareDemand xs α p' w - shareDemand xs α p w) =
      ∑ i, (p' - p) ⬝ᵥ (xs i p' (α i * w) - xs i p (α i * w)) := by
    simp only [shareDemand, ← Finset.sum_sub_distrib, dotProduct_sum]
  rw [hsum]
  refine ⟨Finset.sum_nonpos fun i _ => (hi i).1, fun hne => ?_⟩
  obtain ⟨i, hi'⟩ : ∃ i, xs i p' (α i * w) ≠ xs i p (α i * w) := by
    by_contra hall
    push Not at hall
    exact hne (Finset.sum_congr rfl fun i _ => hall i)
  have := Finset.sum_lt_sum (s := Finset.univ) (g := fun _ => (0 : ℝ)) (fun j _ => (hi j).1)
    ⟨i, Finset.mem_univ i, (hi i).2 hi'⟩
  simpa using this

/-- **Proposition 4.C.1** (MWG, pp. 111-112), second part. A demand function that is
homogeneous of degree zero, satisfies Walras' law and the ULD satisfies the weak axiom. (The
proof rescales `p'` to `p'' = (w/w') p'`; footnote 9 explains why it is needed.) -/
theorem weakAxiom_of_uld {x : DemandFunction L} (hH : HomogeneousZero x) (hW : WalrasLaw x)
    (hU : UncompensatedLawOfDemand x) : WeakAxiom x := by
  intro p w p' w' hd hd' hle hne
  set c := w / w' with hc
  have hcpos : 0 < c := div_pos hd.2 hd'.2
  have hw'0 : w' ≠ 0 := hd'.2.ne'
  have hcw : c * w' = w := by rw [hc]; field_simp
  have hx'' : x (c • p') w = x p' w' := by
    have := hH p' w' c hd' hcpos
    rwa [hcw] at this
  have hd'' : PWDomain (c • p') w := by
    have := pwDomain_smul hd' hcpos
    rwa [hcw] at this
  have hstrict := (hU p (c • p') w hd hd''.1).2 (by rw [hx'']; exact hne)
  rw [hx''] at hstrict
  have hW'' : (c • p') ⬝ᵥ x p' w' = w := by rw [← hx'']; exact hW _ _ hd''
  have hWp : p ⬝ᵥ x p w = w := hW p w hd
  have hexp : (c • p' - p) ⬝ᵥ (x p' w' - x p w) =
      (c • p') ⬝ᵥ x p' w' - (c • p') ⬝ᵥ x p w - p ⬝ᵥ x p' w' + p ⬝ᵥ x p w := by
    simp only [sub_dotProduct, dotProduct_sub]
    ring
  rw [hexp, hW'', hWp] at hstrict
  have h1 : w < (c • p') ⬝ᵥ x p w := by linarith
  rw [smul_dotProduct, smul_eq_mul, hc] at h1
  have h2 : w' * (w / w') = w := by field_simp
  have h3 : w * w' < w * (p' ⬝ᵥ x p w) := by
    have := mul_lt_mul_of_pos_left h1 hd'.2
    rw [show w' * (w / w' * p' ⬝ᵥ x p w) = (w' * (w / w')) * p' ⬝ᵥ x p w by ring, h2] at this
    linarith
  exact lt_of_mul_lt_mul_left h3 hd.2.le

/-- **Proposition 4.C.1** (MWG, p. 111). If every consumer's Walrasian demand function is
homogeneous of degree zero, satisfies Walras' law and the ULD, then aggregate demand
`x(p, w) = ∑ᵢ xᵢ(p, αᵢ w)` (shares `αᵢ > 0`, `∑ αᵢ = 1`) satisfies the ULD and, as a
consequence, the weak axiom. -/
theorem proposition_4_C_1 {xs : Fin I → DemandFunction L} {α : Fin I → ℝ}
    (hα : ∀ i, 0 < α i) (hα1 : ∑ i, α i = 1) (hH : ∀ i, HomogeneousZero (xs i))
    (hW : ∀ i, WalrasLaw (xs i)) (hU : ∀ i, UncompensatedLawOfDemand (xs i)) :
    UncompensatedLawOfDemand (shareDemand xs α) ∧ WeakAxiom (shareDemand xs α) := by
  have hUa := uld_shareDemand hα hU
  have hpos : ∀ i (p : Fin L → ℝ) w, PWDomain p w → 0 < shareRule α i p w :=
    fun i _ _ hd => mul_pos (hα i) hd.2
  have hHa : HomogeneousZero (shareDemand xs α) :=
    ruleDemand_homogeneousZero hH hpos fun i p w a _ _ => mul_left_comm (α i) a w
  have hWa : WalrasLaw (shareDemand xs α) :=
    ruleDemand_walrasLaw hW (isWealthDistributionRule_shareRule hα1) hpos
  exact ⟨hUa, weakAxiom_of_uld hHa hWa hUa⟩

/-! ### Exercise 4.C.1: the differential version of the ULD -/

/-- A real function along a line: `t ↦ v·x(p + t v, w)` has derivative `v·D_p x v`. -/
theorem hasDerivAt_dot_line {x : DemandFunction L} {p v : Fin L → ℝ} {w t₀ : ℝ}
    {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)}
    (hD : HasFDerivAt (Function.uncurry x) D (p + t₀ • v, w)) :
    HasDerivAt (fun t : ℝ => v ⬝ᵥ x (p + t • v) w)
      (v ⬝ᵥ Matrix.mulVec (priceJacobian D) v) t₀ := by
  have h1 := hasDerivAt_line (x := x) (c := 0) (by simpa using hD)
  have h2 := (dualityDotCLM v).hasFDerivAt.comp_hasDerivAt t₀ h1
  simp only [mul_zero, add_zero] at h2
  convert h2 using 1
  · funext t
    simp [dualityDotCLM_apply]
  · rw [dualityDotCLM_apply, deriv_apply_eq_mulVec, zero_smul, add_zero]

/-- **Exercise 4.C.1** (MWG, p. 124), first part (claim on p. 111). If `x` satisfies the ULD and
is differentiable at `(p, w)`, then `D_p x(p, w)` is negative semidefinite:
`dp·D_p x(p, w) dp ≤ 0` for all `dp`. -/
theorem exercise_4_C_1_nsd {x : DemandFunction L} (hU : UncompensatedLawOfDemand x)
    {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w) {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)}
    (hD : HasFDerivAt (Function.uncurry x) D (p, w)) : NegSemidef (priceJacobian D) := by
  intro v
  have hder := hasDerivAt_dot_line (x := x) (v := v) (t₀ := 0) (by simpa using hD)
  apply hasDerivAt_nonpos_of_right_le hder
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), StrictlyPositive (p + t • v) := by
    have hc : Continuous fun t : ℝ => p + t • v := by fun_prop
    have := hc.tendsto 0
    simp only [zero_smul, add_zero] at this
    exact this.eventually (relations_eventually_strictlyPositive hd.1)
  filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with t ht htpos
  have htpos' : (0 : ℝ) < t := htpos
  have h := (hU p (p + t • v) w hd ht).1
  rw [add_sub_cancel_left, smul_dotProduct, smul_eq_mul, dotProduct_sub] at h
  simp only [zero_smul, add_zero]
  have := nonpos_of_mul_nonpos_right h htpos'
  linarith

/-- **Exercise 4.C.1** (MWG, p. 124), second part (claim on p. 111). If at wealth `w` the demand
is differentiable at every `p ≫ 0` with `D_p x(p, w)` negative definite, then `x(·, w)`
satisfies the ULD at `w`. -/
theorem exercise_4_C_1_nd {x : DemandFunction L} {w : ℝ}
    {D : (Fin L → ℝ) → ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)}
    (hD : ∀ p, StrictlyPositive p → HasFDerivAt (Function.uncurry x) (D p) (p, w))
    (hnd : ∀ p, StrictlyPositive p → NegDef (priceJacobian (D p))) {p p' : Fin L → ℝ}
    (hp : StrictlyPositive p) (hp' : StrictlyPositive p') :
    (p' - p) ⬝ᵥ (x p' w - x p w) ≤ 0 ∧
      (x p' w ≠ x p w → (p' - p) ⬝ᵥ (x p' w - x p w) < 0) := by
  by_cases hpp : p' = p
  · subst hpp
    simp
  set v := p' - p with hv
  have hv0 : v ≠ 0 := sub_ne_zero.mpr hpp
  have hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1, StrictlyPositive (p + t • v) := by
    intro t ht l
    have : (p + t • v) l = (1 - t) * p l + t * p' l := by
      simp only [hv, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      ring
    rw [this]
    rcases eq_or_lt_of_le ht.1 with h0 | h0
    · rw [← h0]; simpa using hp l
    · exact add_pos_of_nonneg_of_pos (mul_nonneg (by linarith [ht.2]) (hp l).le)
        (mul_pos h0 (hp' l))
  have hder : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (fun t : ℝ => v ⬝ᵥ x (p + t • v) w)
      (v ⬝ᵥ Matrix.mulVec (priceJacobian (D (p + t • v))) v) t :=
    fun t ht => hasDerivAt_dot_line (hD _ (hseg t ht))
  have hanti : StrictAntiOn (fun t : ℝ => v ⬝ᵥ x (p + t • v) w) (Set.Icc 0 1) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc 0 1)
    · exact fun t ht => (hder t ht).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hder t (Set.Ioo_subset_Icc_self ht)).deriv]
      exact hnd _ (hseg t (Set.Ioo_subset_Icc_self ht)) v hv0
  have hlt := hanti (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one)
    zero_lt_one
  simp only [zero_smul, add_zero, one_smul, hv, add_sub_cancel] at hlt
  have : (p' - p) ⬝ᵥ (x p' w - x p w) < 0 := by
    rw [dotProduct_sub]
    linarith
  exact ⟨this.le, fun _ => this⟩

/-! ### Proposition 4.C.2: homothetic preferences -/

/-- The strictly positive bundle `(w/∑ₗ pₗ, …, w/∑ₗ pₗ)` lies in `B_{p,w}` (`L > 0`). -/
theorem exists_pos_mem_budgetSet (hL : 0 < L) {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w) :
    ∃ y ∈ budgetSet p w, ∀ l, 0 < y l := by
  have hS : 0 < ∑ l, p l := Finset.sum_pos (fun l _ => hd.1 l) ⟨⟨0, hL⟩, Finset.mem_univ _⟩
  refine ⟨fun _ => w / ∑ l, p l, ⟨fun l => (div_pos hd.2 hS).le, ?_⟩,
    fun _ => div_pos hd.2 hS⟩
  simp only [dotProduct]
  rw [← Finset.sum_mul]
  field_simp
  exact le_rfl

/-- **Proposition 4.C.2** (MWG, p. 112). If `≿ᵢ` is homothetic, `xᵢ(p, wᵢ)` satisfies the ULD.
Here `≿ᵢ` is represented by a utility `u` homogeneous of degree one on `ℝ^L_+` (MWG Exercise
3.C.5, `exercise_3_C_5a_only_if`), positive on `ℝ^L_{++}`, with single-valued demand `xf`
satisfying Walras' law. No differentiability is assumed: if `x = x(p, w)`, `x' = x(p', w)`,
revealed preference and homogeneity give `(p·x')(p'·x) ≥ w²`, hence `p·x' + p'·x ≥ 2w`, which
is the ULD inequality; equality forces `p·x' = p'·x = w`, and uniqueness of demand then
forces `x = x'`. -/
theorem proposition_4_C_2 {u : (Fin L → ℝ) → ℝ} (hu : HomogeneousOneOn u)
    (hpos : ∀ y : Fin L → ℝ, (∀ l, 0 < y l) → 0 < u y)
    (huniq : ∀ p w, PWDomain p w → (walrasianDemand u p w).Subsingleton)
    {xf : DemandFunction L} (hxf : ∀ p w, PWDomain p w → xf p w ∈ walrasianDemand u p w)
    (hW : WalrasLaw xf) : UncompensatedLawOfDemand xf := by
  intro p p' w hd hp'
  have hd' : PWDomain p' w := ⟨hp', hd.2⟩
  set x := xf p w with hx
  set x' := xf p' w with hx'
  obtain ⟨⟨hx0, hxb⟩, hxmax⟩ := hxf p w hd
  obtain ⟨⟨hx'0, hx'b⟩, hx'max⟩ := hxf p' w hd'
  have hWx : p ⬝ᵥ x = w := hW p w hd
  have hWx' : p' ⬝ᵥ x' = w := hW p' w hd'
  have hL : 0 < L := by
    rcases Nat.eq_zero_or_pos L with h | h
    · subst h
      simp [dotProduct] at hWx
      linarith [hd.2]
    · exact h
  -- utilities at the demands are positive
  have hux : 0 < u x := by
    obtain ⟨y, hyB, hy⟩ := exists_pos_mem_budgetSet hL hd
    exact (hpos y hy).trans_le (hxmax y hyB)
  have hux' : 0 < u x' := by
    obtain ⟨y, hyB, hy⟩ := exists_pos_mem_budgetSet hL hd'
    exact (hpos y hy).trans_le (hx'max y hyB)
  have hxne : x ≠ 0 := by
    intro h
    rw [h, dotProduct_zero] at hWx
    linarith [hd.2]
  have hx'ne : x' ≠ 0 := by
    intro h
    rw [h, dotProduct_zero] at hWx'
    linarith [hd.2]
  set A := p ⬝ᵥ x' with hA
  set B := p' ⬝ᵥ x with hB
  have hApos : 0 < A := exp_dotProduct_pos hd.1 hx'0 hx'ne
  have hBpos : 0 < B := exp_dotProduct_pos hp' hx0 hxne
  -- revealed preference with rescaling
  have h1 : w * u x' ≤ A * u x := by
    have hmem : (w / A) • x' ∈ budgetSet p w := by
      refine ⟨fun l => by simpa using mul_nonneg (div_pos hd.2 hApos).le (hx'0 l), ?_⟩
      rw [dotProduct_smul, smul_eq_mul, ← hA]
      field_simp
      exact le_rfl
    have := hxmax _ hmem
    rw [hu x' hx'0 _ (div_pos hd.2 hApos)] at this
    have h' := mul_le_mul_of_nonneg_left this hApos.le
    rw [show A * (w / A * u x') = w * u x' by field_simp] at h'
    exact h'
  have h2 : w * u x ≤ B * u x' := by
    have hmem : (w / B) • x ∈ budgetSet p' w := by
      refine ⟨fun l => by simpa using mul_nonneg (div_pos hd.2 hBpos).le (hx0 l), ?_⟩
      rw [dotProduct_smul, smul_eq_mul, ← hB]
      field_simp
      exact le_rfl
    have := hx'max _ hmem
    rw [hu x hx0 _ (div_pos hd.2 hBpos)] at this
    have h' := mul_le_mul_of_nonneg_left this hBpos.le
    rw [show B * (w / B * u x) = w * u x by field_simp] at h'
    exact h'
  have hAB : w ^ 2 ≤ A * B := by
    have h3 : w * u x' * (w * u x) ≤ A * u x * (B * u x') :=
      mul_le_mul h1 h2 (mul_nonneg hd.2.le hux.le) (mul_nonneg hApos.le hux.le)
    have h4 : 0 < u x * u x' := mul_pos hux hux'
    nlinarith
  have hexp : (p' - p) ⬝ᵥ (x' - x) = 2 * w - A - B := by
    simp only [sub_dotProduct, dotProduct_sub]
    rw [hWx, hWx']
    ring
  rw [hexp]
  have hsum : 2 * w ≤ A + B := by nlinarith [sq_nonneg (A - B)]
  refine ⟨by linarith, fun hne => ?_⟩
  by_contra hge
  push Not at hge
  have hAeq : A = w := by nlinarith [sq_nonneg (A - B)]
  have hBeq : B = w := by nlinarith [sq_nonneg (A - B)]
  have hx'B : x' ∈ budgetSet p w := ⟨hx'0, by rw [← hA, hAeq]⟩
  have hxB : x ∈ budgetSet p' w := ⟨hx0, by rw [← hB, hBeq]⟩
  have hle1 : u x' ≤ u x := hxmax x' hx'B
  have hle2 : u x ≤ u x' := hx'max x hxB
  have hmem : x' ∈ walrasianDemand u p w :=
    ⟨hx'B, fun y hy => (hxmax y hy).trans hle2⟩
  exact hne (huniq p w hd hmem (hxf p w hd))

/-- **Proposition 4.C.2** (MWG, p. 112), in terms of preferences. If `≿` on `ℝ^L_+` (`L > 0`) is
rational, continuous, monotone, homothetic and strictly convex, then any Walrasian demand
function generated by `≿` satisfies the ULD. -/
theorem proposition_4_C_2_pref (hL : 0 < L) {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hr : RationalOn (nonnegOrthant L) r) (hc : PrefContinuous (nonnegOrthant L) r)
    (hm : PrefMonotone (nonnegOrthant L) r) (hh : Homothetic (nonnegOrthant L) r)
    (hsc : PrefStrictlyConvex (nonnegOrthant L) r) {xf : DemandFunction L}
    (hxf : ∀ p w, PWDomain p w → xf p w ∈ walrasianDemandPref r p w) :
    UncompensatedLawOfDemand xf := by
  obtain ⟨u, hucont, hrep, hhom⟩ := exercise_3_C_5a_only_if hL hr hc hm hh
  have hdem : ∀ p w, walrasianDemand u p w = walrasianDemandPref r p w :=
    walrasianDemand_eq_pref_of_represents hrep
  have hq := (prefStrictlyConvex_iff_strictlyQuasiconcaveOn (convex_nonnegOrthant L) hrep).mp hsc
  have hlns := exercise_3_B_1b_orthant hL hm
  have hxf' : ∀ p w, PWDomain p w → xf p w ∈ walrasianDemand u p w := by
    intro p w hd
    rw [hdem]
    exact hxf p w hd
  have hu0 : u 0 = 0 := by
    have h := hhom 0 (fun _ => le_rfl) 2 two_pos
    rw [smul_zero] at h
    linarith
  have hpos : ∀ y : Fin L → ℝ, (∀ l, 0 < y l) → 0 < u y := by
    intro y hy
    have hs := hm 0 (fun _ => le_rfl) y (fun l => (hy l).le) (fun l => by simpa using hy l)
    have := (hrep.strict_iff (x := y) (y := 0) (fun l => (hy l).le) (fun _ => le_rfl)).mp hs
    rwa [hu0] at this
  exact proposition_4_C_2 hhom hpos (fun p w _ => proposition_3_D_2_iii_unique hq p w) hxf'
    (fun p w hd => proposition_3_D_2_ii hrep hlns (hxf' p w hd))

/-- **Proposition 4.C.2** (MWG, p. 112), the book's differential argument. If demand is
homogeneous of degree one in wealth near `(p, w)` (homothetic preferences) and differentiable
there, then `D_w x(p, w) = x(p, w)/w` and `D_p x(p, w) = S(p, w) - (1/w) x(p, w) x(p, w)ᵀ`. -/
theorem proposition_4_C_2_differential {x : DemandFunction L} {p : Fin L → ℝ} {w : ℝ}
    (hw : 0 < w) (hhd : ∀ t : ℝ, 0 < t → x p (t * w) = t • x p w)
    {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)}
    (hD : HasFDerivAt (Function.uncurry x) D (p, w)) :
    wealthJacobian D = w⁻¹ • x p w ∧
      priceJacobian D = slutskyMatrix D (x p w) - w⁻¹ • Matrix.vecMulVec (x p w) (x p w) := by
  have hpath := hasDerivAt_path hD 0 1
  simp only [smul_zero, add_zero, mul_one] at hpath
  have hlin : HasDerivAt (fun t : ℝ => (1 + t / w) • x p w) (w⁻¹ • x p w) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).div_const w).const_add 1
    simpa [div_eq_inv_mul] using this.smul_const (x p w)
  have hev : (fun t : ℝ => x p (w + t)) =ᶠ[𝓝 0] fun t => (1 + t / w) • x p w := by
    have : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < 1 + t / w := by
      have hc : Continuous fun t : ℝ => 1 + t / w := by fun_prop
      have := hc.tendsto 0
      simp only [zero_div, add_zero] at this
      exact this.eventually (lt_mem_nhds one_pos)
    filter_upwards [this] with t ht
    rw [← hhd _ ht]
    congr 1
    field_simp
  have hwj : D (0, 1) = w⁻¹ • x p w := hpath.unique (hlin.congr_of_eventuallyEq hev)
  have hwj' : wealthJacobian D = w⁻¹ • x p w := by
    funext l
    simp only [wealthJacobian, wealthEffect, hwj]
  refine ⟨hwj', ?_⟩
  rw [slutskyMatrix_eq, hwj']
  ext l k
  simp [Matrix.vecMulVec]
  ring

/-- The quadratic form of an outer product: `v·(a bᵀ) v = (v·a)(b·v)`. -/
theorem dot_vecMulVec_mulVec (a b v : Fin L → ℝ) :
    v ⬝ᵥ Matrix.mulVec (Matrix.vecMulVec a b) v = (v ⬝ᵥ a) * (b ⬝ᵥ v) := by
  simp only [Matrix.mulVec, Matrix.vecMulVec, dotProduct, Matrix.of_apply]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- **Proposition 4.C.2** (MWG, p. 112), the book's conclusion from the differential identity.
If moreover the Slutsky matrix is negative semidefinite and negative off the price ray
(`v·S v < 0` for `v` not proportional to `p`), and `x(p, w)` satisfies Walras' law at `(p, w)`,
then `D_p x(p, w)` is negative definite. -/
theorem proposition_4_C_2_negDef {x : DemandFunction L} {p : Fin L → ℝ} {w : ℝ}
    (hd : PWDomain p w) (hWx : p ⬝ᵥ x p w = w) (hhd : ∀ t : ℝ, 0 < t → x p (t * w) = t • x p w)
    {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)}
    (hD : HasFDerivAt (Function.uncurry x) D (p, w))
    (hS : NegSemidef (slutskyMatrix D (x p w)))
    (hSoff : ∀ v : Fin L → ℝ, (∀ c : ℝ, v ≠ c • p) →
      v ⬝ᵥ Matrix.mulVec (slutskyMatrix D (x p w)) v < 0) :
    NegDef (priceJacobian D) := by
  intro v hv
  rw [(proposition_4_C_2_differential hd.2 hhd hD).2, Matrix.sub_mulVec, dotProduct_sub,
    Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, dot_vecMulVec_mulVec]
  have hq : 0 ≤ w⁻¹ * ((v ⬝ᵥ x p w) * (x p w ⬝ᵥ v)) := by
    rw [dotProduct_comm (x p w) v]
    exact mul_nonneg (inv_pos.mpr hd.2).le (mul_self_nonneg _)
  by_cases hprop : ∃ c : ℝ, v = c • p
  · obtain ⟨c, rfl⟩ := hprop
    have hc : c ≠ 0 := by
      rintro rfl
      exact hv (zero_smul _ _)
    have hvx : (c • p) ⬝ᵥ x p w = c * w := by rw [smul_dotProduct, hWx, smul_eq_mul]
    rw [dotProduct_comm (x p w), hvx]
    have h1 := hS (c • p)
    have h2 : 0 < w⁻¹ * (c * w * (c * w)) := by
      have : w⁻¹ * (c * w * (c * w)) = c * c * w := by field_simp
      rw [this]
      exact mul_pos (mul_self_pos.mpr hc) hd.2
    linarith
  · push Not at hprop
    have h1 := hSoff v hprop
    linarith

end MWG.AggregateDemand
