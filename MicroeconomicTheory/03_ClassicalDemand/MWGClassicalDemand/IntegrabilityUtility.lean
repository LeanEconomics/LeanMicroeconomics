/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.IntegrabilityBasic

/-!
# Integrability: the recovered utility and the integrability theorem

MWG, Section 3.H, pp. 77-80, and Exercise 3.H.1 (p. 102).

* `recoveredUtility E x = sup {u : x ∈ V_u}`, valued in `EReal` (correction D1). If `e(p, ·)` is
  nondecreasing and continuous, its upper level sets are exactly the sets `V_u`
  (`mem_recoveredSet_iff`), so it generates `e(p, u)` (Exercise 3.H.1, `exercise_3_H_1`). As
  printed (`x ≫ 0` and `Min`) the minimum need not exist (`exercise_3_H_1_min_not_attained`), and
  the real supremum can be over the empty set (`exercise_3_H_1_sup_empty`).
* The integrability theorem modulo the existence of a solution of (3.H.2)
  (`integrability_theorem`): if a family `E(p, u)` of functions with the properties of an
  expenditure function solves `∇_p E(p, u) = x(p, E(p, u))` (equation (3.H.2)) and reaches every
  wealth level, then `x(p, w)` is the Walrasian demand of the recovered preference. This is the
  conclusion of pp. 79-80, "the necessary and sufficient condition for the recovery of an
  underlying expenditure function", once a solution of (3.H.2) is given; the existence of such a
  solution (Frobenius' theorem) is the open part, see `IntegrabilityPDE` and
  `IntegrabilityTwoGoods`.
-/

namespace MWG.ClassicalDemand

open MWG.ConsumerChoice Kreps.PreferenceProperties Filter Topology

variable {L : ℕ}

/-- **Exercise 3.H.1** (MWG, p. 102). The utility recovered from a family of expenditure
functions: `U(x) = sup {u : x ∈ V_u}`, with values in `EReal` (the supremum of the empty set is
`⊥`, of an unbounded set `⊤`). -/
noncomputable def recoveredUtility (E : (Fin L → ℝ) → ℝ → ℝ) (x : Fin L → ℝ) : EReal :=
  ⨆ (u : ℝ) (_ : x ∈ recoveredSet fun p => E p u), (u : EReal)

/-- The preference relation of the recovered utility: `x ≿ y` iff `U(x) ≥ U(y)`. -/
def recoveredPref (E : (Fin L → ℝ) → ℝ → ℝ) (x y : Fin L → ℝ) : Prop :=
  recoveredUtility E y ≤ recoveredUtility E x

/-- If `x ∈ V_u` then `U(x) ≥ u`. -/
theorem le_recoveredUtility {E : (Fin L → ℝ) → ℝ → ℝ} {x : Fin L → ℝ} {u : ℝ}
    (hx : x ∈ recoveredSet fun p => E p u) : (u : EReal) ≤ recoveredUtility E x :=
  le_iSup₂ (f := fun (u : ℝ) (_ : x ∈ recoveredSet fun p => E p u) => (u : EReal)) u hx

/-- If `U(x) > u` then `x ∈ V_{u'}` for some `u' > u`. -/
theorem exists_of_lt_recoveredUtility {E : (Fin L → ℝ) → ℝ → ℝ} {x : Fin L → ℝ} {u : ℝ}
    (h : (u : EReal) < recoveredUtility E x) :
    ∃ u' : ℝ, u < u' ∧ x ∈ recoveredSet fun p => E p u' := by
  obtain ⟨u', hu'⟩ := lt_iSup_iff.mp h
  obtain ⟨hx, hlt⟩ := lt_iSup_iff.mp hu'
  exact ⟨u', EReal.coe_lt_coe_iff.mp hlt, hx⟩

/-- **Exercise 3.H.1** (MWG, p. 102), the key step. If `e(p, ·)` is nondecreasing and continuous
for every `p ≫ 0`, the upper level sets of `U` in `ℝ^L_+` are the sets `V_u`:
`x ∈ V_u ⟺ U(x) ≥ u`. -/
theorem mem_recoveredSet_iff {E : (Fin L → ℝ) → ℝ → ℝ}
    (hmono : ∀ p, StrictlyPositive p → Monotone (E p))
    (hcont : ∀ p, StrictlyPositive p → Continuous (E p)) {x : Fin L → ℝ}
    (hx : x ∈ nonnegOrthant L) (u : ℝ) :
    x ∈ (recoveredSet fun p => E p u) ↔ (u : EReal) ≤ recoveredUtility E x := by
  refine ⟨le_recoveredUtility, fun h => ⟨hx, fun p hp => ?_⟩⟩
  have hbelow : ∀ v < u, E p v ≤ p ⬝ᵥ x := by
    intro v hv
    obtain ⟨v', hvv', hxv'⟩ := exists_of_lt_recoveredUtility
      ((EReal.coe_lt_coe_iff.mpr hv).trans_le h)
    exact (hmono p hp hvv'.le).trans (hxv'.2 p hp)
  have ht : Tendsto (E p) (𝓝[<] u) (𝓝 (E p u)) :=
    ((hcont p hp).tendsto u).mono_left nhdsWithin_le_nhds
  exact le_of_tendsto ht (eventually_nhdsWithin_of_forall fun v hv => hbelow v hv)

/-- **Exercise 3.H.1** (MWG, p. 102), corrected (correction D1). Let `e(·, u)` be continuous,
concave, homogeneous of degree one and nondecreasing on `p ≫ 0` for every `u`, and `e(p, ·)`
nondecreasing and continuous for every `p ≫ 0`. Then the recovered utility
`U(x) = sup {u : x ∈ V_u}` (in `EReal`) generates `e`: for `p ≫ 0`,
`e(p, u) = min {p·x : x ∈ ℝ^L_+, U(x) ≥ u}`, the minimum being attained. -/
theorem exercise_3_H_1 {E : (Fin L → ℝ) → ℝ → ℝ}
    (hc : ∀ u, ConcaveOn ℝ (posPrices L) fun p => E p u)
    (hcp : ∀ u, ContinuousOn (fun p => E p u) (posPrices L))
    (hh : ∀ u, HD1OnPos fun p => E p u) (hm : ∀ u, MonotoneOnPos fun p => E p u)
    (hmono : ∀ p, StrictlyPositive p → Monotone (E p))
    (hcont : ∀ p, StrictlyPositive p → Continuous (E p)) {p : Fin L → ℝ}
    (hp : StrictlyPositive p) (u : ℝ) :
    (∃ x ∈ nonnegOrthant L, (u : EReal) ≤ recoveredUtility E x ∧ p ⬝ᵥ x = E p u) ∧
      ∀ x ∈ nonnegOrthant L, (u : EReal) ≤ recoveredUtility E x → E p u ≤ p ⬝ᵥ x := by
  obtain ⟨⟨x, hx⟩, hval⟩ := proposition_3_H_1_general (hc u) (hcp u) (hh u) (hm u) hp
  refine ⟨⟨x, hx.1.1, le_recoveredUtility hx.1, ?_⟩, fun y hy hU => ?_⟩
  · rw [← supportFn_eq_of_mem_argmin hx, hval]
  · exact ((mem_recoveredSet_iff hmono hcont hy u).mpr hU).2 p hp

/-- **Exercise 3.H.1** (MWG, p. 102), with the utility restricted to `x ≫ 0` as printed: the
expenditure `e(p, u)` is the infimum of `p·x` over `{x ≫ 0 : U(x) ≥ u}`. (The infimum need not
be attained: `exercise_3_H_1_min_not_attained`.) -/
theorem exercise_3_H_1_pos {E : (Fin L → ℝ) → ℝ → ℝ}
    (hc : ∀ u, ConcaveOn ℝ (posPrices L) fun p => E p u)
    (hcp : ∀ u, ContinuousOn (fun p => E p u) (posPrices L))
    (hh : ∀ u, HD1OnPos fun p => E p u) (hm : ∀ u, MonotoneOnPos fun p => E p u)
    (hmono : ∀ p, StrictlyPositive p → Monotone (E p))
    (hcont : ∀ p, StrictlyPositive p → Continuous (E p)) {p : Fin L → ℝ}
    (hp : StrictlyPositive p) (u : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ x, StrictlyPositive x ∧ (u : EReal) ≤ recoveredUtility E x ∧ p ⬝ᵥ x < E p u + ε := by
  obtain ⟨⟨x, hx, hU, hpx⟩, -⟩ := exercise_3_H_1 hc hcp hh hm hmono hcont hp u
  have hs : 0 < ∑ l, p l + 1 := by
    have := Finset.sum_nonneg fun l (_ : l ∈ Finset.univ) => (hp l).le
    linarith
  set δ := ε / (∑ l, p l + 1) with hδ
  have hδ0 : 0 < δ := div_pos hε hs
  have hxle : x ≤ x + fun _ => δ := fun l => by simp [hδ0.le]
  have hmem := (mem_recoveredSet_iff hmono hcont hx u).mpr hU
  refine ⟨x + fun _ => δ, fun l => by simp only [Pi.add_apply]; linarith [hx l], ?_, ?_⟩
  · exact (mem_recoveredSet_iff hmono hcont (fun l => (hx l).trans (hxle l)) u).mp
      (recoveredSet_upward hmem hxle)
  · have : p ⬝ᵥ (x + fun _ => δ) = p ⬝ᵥ x + δ * ∑ l, p l := by
      simp only [dotProduct, Pi.add_apply]
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun l _ => by ring
    rw [this, hpx]
    have : δ * ∑ l, p l < ε := by
      rw [hδ, div_mul_eq_mul_div, div_lt_iff₀ hs]
      nlinarith
    linarith

/-- The family `e(p, u) = exp(u) p₁` on `ℝ²` used in the counterexamples to Exercise 3.H.1. -/
noncomputable def integExpFamily (p : Fin 2 → ℝ) (u : ℝ) : ℝ := Real.exp u * p 0

/-- **Exercise 3.H.1** (MWG, p. 102), as printed with `Min` over `x ≫ 0`, is false (correction
D1). The family `e(p, u) = exp(u) p₁` on `ℝ²` is continuous, linear (hence concave and homogeneous
of degree one) and nondecreasing in `p`, and strictly increasing and continuous in `u`, but no
`x ≫ 0` with `U(x) ≥ u` attains `p·x = e(p, u)`. -/
theorem exercise_3_H_1_min_not_attained :
    (∀ u, ConcaveOn ℝ (posPrices 2) fun p => integExpFamily p u) ∧
      (∀ u, ContinuousOn (fun p => integExpFamily p u) (posPrices 2)) ∧
      (∀ u, HD1OnPos fun p => integExpFamily p u) ∧
      (∀ u, MonotoneOnPos fun p => integExpFamily p u) ∧
      (∀ p, StrictlyPositive p → StrictMono (integExpFamily p)) ∧
      (∀ p, Continuous (integExpFamily p)) ∧
      ∀ p, StrictlyPositive p → ∀ u : ℝ, ∀ x : Fin 2 → ℝ, StrictlyPositive x →
        (u : EReal) ≤ recoveredUtility integExpFamily x → integExpFamily p u < p ⬝ᵥ x := by
  refine ⟨fun u => ?_, fun u => by unfold integExpFamily; fun_prop, fun u p _ α _ => ?_,
    fun u p q _ hpq => ?_, fun p hp a b hab => ?_, fun p => by unfold integExpFamily; fun_prop,
    fun p hp u x hx hU => ?_⟩
  · refine ⟨exp_convex_strictlyPositive 2, fun a _ b _ s t _ _ _ => ?_⟩
    simp [integExpFamily, smul_eq_mul]
    ring_nf
    rfl
  · simp [integExpFamily]
    ring
  · exact mul_le_mul_of_nonneg_left (hpq 0) (Real.exp_pos u).le
  · exact mul_lt_mul_of_pos_right (Real.exp_lt_exp.mpr hab) (hp 0)
  · have hmono : ∀ q : Fin 2 → ℝ, StrictlyPositive q → Monotone (integExpFamily q) :=
      fun q hq a b hab => mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hab) (hq 0).le
    have hcont : ∀ q : Fin 2 → ℝ, StrictlyPositive q → Continuous (integExpFamily q) :=
      fun q _ => by unfold integExpFamily; fun_prop
    have hmem := (mem_recoveredSet_iff hmono hcont (fun l => (hx l).le) u).mpr hU
    have hx0 : Real.exp u ≤ x 0 := by
      apply le_of_forall_pos_lt_add
      intro ε hε
      set δ := ε / (x 1 + 1) with hδ
      have hδ0 : 0 < δ := div_pos hε (by linarith [hx 1])
      have := hmem.2 ![1, δ] (fun l => by fin_cases l <;> simp [hδ0])
      simp only [integExpFamily, Fin.isValue, Matrix.cons_val_zero, mul_one, dotProduct,
        Fin.sum_univ_two, one_mul, Matrix.cons_val_one, Matrix.cons_val_fin_one] at this
      have : δ * x 1 < ε := by
        rw [hδ, div_mul_eq_mul_div, div_lt_iff₀ (by linarith [hx 1])]
        nlinarith [hx 1]
      linarith
    simp only [integExpFamily, dotProduct, Fin.sum_univ_two]
    nlinarith [mul_le_mul_of_nonneg_left hx0 (hp 0).le, mul_pos (hp 1) (hx 1)]

/-- **Exercise 3.H.1** (MWG, p. 102): the real supremum `sup {u : x ∈ V_u}` can be over the
empty set (correction D1). For `e(p, u) = (1 + exp u) p₁` on `ℝ¹` and `x = 1/2`, no `u` has
`x ∈ V_u`, so `U(x) = ⊥` in `EReal`. -/
theorem exercise_3_H_1_sup_empty :
    recoveredUtility (fun (p : Fin 1 → ℝ) (u : ℝ) => (1 + Real.exp u) * p 0) (fun _ => 1 / 2) =
      ⊥ := by
  unfold recoveredUtility
  refine iSup₂_eq_bot.mpr fun u hu => ?_
  exfalso
  have := hu.2 (fun _ => 1) fun _ => one_pos
  simp [dotProduct] at this
  linarith [Real.exp_pos u]

/-- **Section 3.H** (MWG, pp. 77-80), the integrability theorem given a solution of (3.H.2).
Let `x(p, w)` be a demand function and `E(p, u)` a family of functions such that, for every `u`,
`E(·, u)` is concave, homogeneous of degree one and nondecreasing on `p ≫ 0`; for every `p ≫ 0`,
`E(p, ·)` is strictly increasing, continuous and reaches every `w > 0`; and `E` solves the system
of partial differential equations (3.H.2), `∇_p E(p, u) = x(p, E(p, u))` wherever
`E(p, u) > 0`. Then for all `p ≫ 0`, `w > 0`, the Walrasian demand of the recovered preference
(`U(x) = sup {u : x ∈ V_u}`) is exactly `{x(p, w)}`, and `E(·, u)` is its expenditure function
(`exercise_3_H_1`). -/
theorem integrability_theorem {x : DemandFunction L} {E : (Fin L → ℝ) → ℝ → ℝ}
    (hc : ∀ u, ConcaveOn ℝ (posPrices L) fun p => E p u)
    (hh : ∀ u, HD1OnPos fun p => E p u) (hm : ∀ u, MonotoneOnPos fun p => E p u)
    (hmono : ∀ p, StrictlyPositive p → StrictMono (E p))
    (hcont : ∀ p, StrictlyPositive p → Continuous (E p))
    (hsurj : ∀ p, StrictlyPositive p → ∀ w, 0 < w → ∃ u, E p u = w)
    (hpde : ∀ p u, StrictlyPositive p → 0 < E p u →
      HasFDerivAt (fun q => E q u) (dualityDotCLM (x p (E p u))) p)
    {p : Fin L → ℝ} (hp : StrictlyPositive p) {w : ℝ} (hw : 0 < w) :
    walrasianDemandPref (recoveredPref E) p w = {x p w} := by
  obtain ⟨u, hu⟩ := hsurj p hp w hw
  have hd := hpde p u hp (hu ▸ hw)
  rw [hu] at hd
  obtain ⟨hargmin, hval, -⟩ := proposition_3_H_1 (hc u) (hh u) (hm u) hp hd
  rw [gradientVec_dualityDotCLM] at hargmin hval
  have hmono' : ∀ q, StrictlyPositive q → Monotone (E q) := fun q hq => (hmono q hq).monotone
  have hxU : (u : EReal) ≤ recoveredUtility E (x p w) := le_recoveredUtility hargmin.1
  have hxB : x p w ∈ budgetSet p w := ⟨hargmin.1.1, by rw [← hval, hu]⟩
  -- every affordable bundle has utility at most `u`
  have hbound : ∀ y ∈ budgetSet p w, recoveredUtility E y ≤ (u : EReal) := by
    intro y hy
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨u', huu', hyu'⟩ := exists_of_lt_recoveredUtility hlt
    have h1 := hyu'.2 p hp
    have h2 := hmono p hp huu'
    rw [hu] at h2
    linarith [hy.2]
  ext y
  constructor
  · rintro ⟨hyB, hymax⟩
    have hyU : (u : EReal) ≤ recoveredUtility E y := hxU.trans (hymax (x p w) hxB)
    have hyV := (mem_recoveredSet_iff hmono' hcont hyB.1 u).mpr hyU
    -- `y` minimizes `p·y` over `V_u`; by differentiability it is the gradient `x(p, w)`
    have hmin : IsLocalMin (fun q => q ⬝ᵥ y - E q u) p := by
      filter_upwards [relations_eventually_strictlyPositive hp] with q hq
      have h1 := hyV.2 q hq
      have h2 := hyV.2 p hp
      simp only at h1 h2 ⊢
      have : p ⬝ᵥ y = E p u := le_antisymm (hu ▸ hyB.2) h2
      linarith
    have hder : HasFDerivAt (fun q => q ⬝ᵥ y - E q u)
        (dualityDotCLM y - dualityDotCLM (x p w)) p :=
      (duality_hasFDerivAt_dot_left y p).sub hd
    have h0 := hmin.hasFDerivAt_eq_zero hder
    exact dualityDotCLM_injective (sub_eq_zero.mp h0)
  · rintro rfl
    exact ⟨hxB, fun z hz => hbound z hz |>.trans hxU⟩

end MWG.ClassicalDemand
