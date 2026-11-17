import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Data.Matrix.Mul
import Mathlib.Topology.Algebra.Module.FiniteDimension
import MWGClassicalDemand.DualitySupport
import MWGClassicalDemand.RelationsBasic
import Mathlib.Data.EReal.Inv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import MWGClassicalDemand.AppendixMC
import MWGClassicalDemand.AppendixMG
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Analysis.Convex.Topology
import MWGConsumerChoice.AppendixMDNeumann
import MWGClassicalDemand.ExpCobbDouglas
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import MWGClassicalDemand.CloserCES
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Quasiconvex
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.MeanInequalities
set_option autoImplicit false

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Production sets (MWG Section 5.B)

MWG, Chapter 5, Section 5.B, pp. 128-135. Production vectors are elements of `ℝ^L`
(`Fin L → ℝ`), with outputs positive and inputs negative; the order on `ℝ^L` is the
coordinatewise one, so `0 ≤ y` is `y ∈ ℝ^L_+`.

* Properties (i)-(xii) of production sets (pp. 130-134): `NoFreeLunch`, `InactionPossible`,
  `FreeDisposal`, `Irreversible`, `NonincreasingReturns`, `NondecreasingReturns`,
  `ConstantReturns`, `Additive`, `IsConvexCone`, with the set forms of (iii) and (v), and the
  relations among them stated in the text.
* **Proposition 5.B.1** (`proposition_5_B_1`) and **Proposition 5.B.2** (`proposition_5_B_2`).
* The transformation function and the marginal rate of transformation (pp. 128-129), the
  single-output production set of a production function (p. 129), the MRTS (p. 130).
* **Example 5.B.1**, **Exercise 5.B.1**, **Exercise 5.B.2**, **Exercise 5.B.3**, and the additive
  but nonconvex technology of Figure 5.B.8.

Departure: "nonincreasing returns imply inaction is possible" (p. 132) needs `Y` nonempty,
property (i) (`inaction_of_nonincreasingReturns`, with the empty set as counterexample).
-/

namespace MWG.Production

variable {L : ℕ}

/-- **Property (iii), no free lunch** (MWG, p. 130): `y ∈ Y` and `y ≥ 0` imply `y = 0`. -/
def NoFreeLunch (Y : Set (Fin L → ℝ)) : Prop := ∀ y ∈ Y, 0 ≤ y → y = 0

/-- **Property (iv), possibility of inaction** (MWG, p. 130): `0 ∈ Y`. -/
def InactionPossible (Y : Set (Fin L → ℝ)) : Prop := (0 : Fin L → ℝ) ∈ Y

/-- **Property (v), free disposal** (MWG, p. 131): `y ∈ Y` and `y' ≤ y` imply `y' ∈ Y`. -/
def FreeDisposal (Y : Set (Fin L → ℝ)) : Prop := ∀ y ∈ Y, ∀ y', y' ≤ y → y' ∈ Y

/-- **Property (vi), irreversibility** (MWG, p. 132): `y ∈ Y` and `y ≠ 0` imply `-y ∉ Y`. -/
def Irreversible (Y : Set (Fin L → ℝ)) : Prop := ∀ y ∈ Y, y ≠ 0 → -y ∉ Y

/-- **Property (vii), nonincreasing returns to scale** (MWG, p. 132): `αy ∈ Y` for `y ∈ Y` and
`α ∈ [0, 1]`. -/
def NonincreasingReturns (Y : Set (Fin L → ℝ)) : Prop :=
  ∀ y ∈ Y, ∀ α : ℝ, 0 ≤ α → α ≤ 1 → α • y ∈ Y

/-- **Property (viii), nondecreasing returns to scale** (MWG, p. 132): `αy ∈ Y` for `y ∈ Y`
and `α ≥ 1`. -/
def NondecreasingReturns (Y : Set (Fin L → ℝ)) : Prop := ∀ y ∈ Y, ∀ α : ℝ, 1 ≤ α → α • y ∈ Y

/-- **Property (ix), constant returns to scale** (MWG, p. 132): `αy ∈ Y` for `y ∈ Y` and
`α ≥ 0`; `Y` is a cone. -/
def ConstantReturns (Y : Set (Fin L → ℝ)) : Prop := ∀ y ∈ Y, ∀ α : ℝ, 0 ≤ α → α • y ∈ Y

/-- **Property (x), additivity or free entry** (MWG, p. 133): `Y + Y ⊆ Y`. -/
def Additive (Y : Set (Fin L → ℝ)) : Prop := ∀ y ∈ Y, ∀ y' ∈ Y, y + y' ∈ Y

/-- **Property (xii), convex cone** (MWG, p. 134): `αy + βy' ∈ Y` for `y, y' ∈ Y`,
`α, β ≥ 0`. (Property (xi) is Mathlib's `Convex ℝ Y`.) -/
def IsConvexCone (Y : Set (Fin L → ℝ)) : Prop :=
  ∀ y ∈ Y, ∀ y' ∈ Y, ∀ α β : ℝ, 0 ≤ α → 0 ≤ β → α • y + β • y' ∈ Y

/-- **Property (iii)** (MWG, p. 130), geometric form: no free lunch iff `Y ∩ ℝ^L_+ ⊆ {0}`. -/
theorem noFreeLunch_iff (Y : Set (Fin L → ℝ)) :
    NoFreeLunch Y ↔ Y ∩ {y | 0 ≤ y} ⊆ {0} :=
  ⟨fun h y hy => h y hy.1 hy.2, fun h _ hy h0 => h ⟨hy, h0⟩⟩

open scoped Pointwise in
/-- **Property (v)** (MWG, p. 131), set form: free disposal iff `Y - ℝ^L_+ ⊆ Y`. -/
theorem freeDisposal_iff (Y : Set (Fin L → ℝ)) :
    FreeDisposal Y ↔ Y - {v | 0 ≤ v} ⊆ Y := by
  constructor
  · rintro h _ ⟨y, hy, v, hv, rfl⟩
    exact h y hy _ (sub_le_self y hv)
  · intro h y hy y' hy'
    have : y - (y - y') = y' := sub_sub_cancel y y'
    rw [← this]
    exact h ⟨y, hy, y - y', sub_nonneg.mpr hy', rfl⟩

/-- **Property (vii)** (MWG, p. 132): nonincreasing returns imply that inaction is possible,
for a nonempty `Y` (property (i)). -/
theorem inaction_of_nonincreasingReturns {Y : Set (Fin L → ℝ)} (hne : Y.Nonempty)
    (h : NonincreasingReturns Y) : InactionPossible Y := by
  obtain ⟨y, hy⟩ := hne
  have := h y hy 0 le_rfl zero_le_one
  rwa [zero_smul] at this

/-- The empty production set has nonincreasing returns but not inaction: the remark on p. 132
needs property (i). -/
theorem nonincreasingReturns_empty :
    NonincreasingReturns (∅ : Set (Fin L → ℝ)) ∧ ¬ InactionPossible (∅ : Set (Fin L → ℝ)) :=
  ⟨fun _ hy => absurd hy (Set.notMem_empty _), Set.notMem_empty _⟩

/-- **Property (ix)** (MWG, p. 132): constant returns is the conjunction of (vii) and (viii). -/
theorem constantReturns_iff (Y : Set (Fin L → ℝ)) :
    ConstantReturns Y ↔ NonincreasingReturns Y ∧ NondecreasingReturns Y := by
  constructor
  · intro h
    exact ⟨fun y hy α h0 _ => h y hy α h0, fun y hy α h1 => h y hy α (by linarith)⟩
  · rintro ⟨h1, h2⟩ y hy α h0
    rcases le_total α 1 with hα | hα
    · exact h1 y hy α h0 hα
    · exact h2 y hy α hα

/-- **Property (x)** (MWG, p. 133): additivity implies `ky ∈ Y` for every positive integer `k`. -/
theorem additive_nsmul {Y : Set (Fin L → ℝ)} (h : Additive Y) {y : Fin L → ℝ} (hy : y ∈ Y) :
    ∀ k : ℕ, 0 < k → (k : ℝ) • y ∈ Y := by
  intro k hk
  induction k with
  | zero => exact absurd hk (lt_irrefl 0)
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0
      simpa using hy
    · have := h _ (ih h0) y hy
      rwa [Nat.cast_succ, add_smul, one_smul]

/-- **Property (xi)** (MWG, p. 134): if `0 ∈ Y`, convexity implies nonincreasing returns. -/
theorem nonincreasingReturns_of_convex {Y : Set (Fin L → ℝ)} (hc : Convex ℝ Y)
    (h0 : InactionPossible Y) : NonincreasingReturns Y := by
  intro y hy α hα0 hα1
  have := hc hy h0 hα0 (by linarith : (0 : ℝ) ≤ 1 - α) (by ring)
  rwa [smul_zero, add_zero] at this

/-- **Property (xii)** (MWG, p. 134): a convex cone is exactly a convex set with constant
returns to scale. -/
theorem isConvexCone_iff (Y : Set (Fin L → ℝ)) :
    IsConvexCone Y ↔ Convex ℝ Y ∧ ConstantReturns Y := by
  constructor
  · intro h
    refine ⟨fun y hy y' hy' α β hα hβ _ => h y hy y' hy' α β hα hβ, fun y hy α hα => ?_⟩
    have := h y hy y hy α 0 hα le_rfl
    rwa [zero_smul, add_zero] at this
  · rintro ⟨hc, hcr⟩ y hy y' hy' α β hα hβ
    rcases (add_nonneg hα hβ).lt_or_eq with hpos | hzero
    · have hm := hc hy hy' (div_nonneg hα hpos.le) (div_nonneg hβ hpos.le)
        (by field_simp)
      have := hcr _ hm (α + β) hpos.le
      have heq : (α + β) • ((α / (α + β)) • y + (β / (α + β)) • y') = α • y + β • y' := by
        rw [smul_add, smul_smul, smul_smul, mul_div_cancel₀ _ hpos.ne',
          mul_div_cancel₀ _ hpos.ne']
      rwa [heq] at this
    · have ha : α = 0 := by linarith
      have hb : β = 0 := by linarith
      subst ha hb
      have := hcr y hy 0 le_rfl
      simpa using this

/-- **Proposition 5.B.1** (MWG, p. 134). `Y` is additive and has nonincreasing returns to scale
if and only if it is a convex cone. -/
theorem proposition_5_B_1 (Y : Set (Fin L → ℝ)) :
    Additive Y ∧ NonincreasingReturns Y ↔ IsConvexCone Y := by
  constructor
  · rintro ⟨hadd, hnir⟩
    have key : ∀ y ∈ Y, ∀ α : ℝ, 0 ≤ α → α • y ∈ Y := by
      intro y hy α hα
      obtain ⟨k, hk⟩ := exists_nat_gt α
      have hk0 : (0 : ℝ) < k := lt_of_le_of_lt hα hk
      have hkpos : 0 < k := by exact_mod_cast hk0
      have h1 := hnir _ (additive_nsmul hadd hy k hkpos) (α / k) (div_nonneg hα hk0.le)
        ((div_le_one hk0).mpr hk.le)
      rwa [smul_smul, div_mul_cancel₀ _ hk0.ne'] at h1
    intro y hy y' hy' α β hα hβ
    exact hadd _ (key y hy α hα) _ (key y' hy' β hβ)
  · intro h
    refine ⟨fun y hy y' hy' => ?_, fun y hy α hα _ => ?_⟩
    · have := h y hy y' hy' 1 1 zero_le_one zero_le_one
      simpa using this
    · have := h y hy y hy α 0 hα le_rfl
      rwa [zero_smul, add_zero] at this

/-- The vector `(y, t) ∈ ℝ^{L+1}`. -/
def extendVec (y : Fin L → ℝ) (t : ℝ) : Fin (L + 1) → ℝ := Fin.snoc y t

theorem extendVec_smul (a : ℝ) (y : Fin L → ℝ) (t : ℝ) :
    a • extendVec y t = extendVec (a • y) (a * t) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [extendVec]
  · simp [extendVec]

theorem extendVec_add (y y' : Fin L → ℝ) (t t' : ℝ) :
    extendVec y t + extendVec y' t' = extendVec (y + y') (t + t') := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [extendVec]
  · simp [extendVec]

theorem extendVec_inj {y y' : Fin L → ℝ} {t t' : ℝ} :
    extendVec y t = extendVec y' t' ↔ y = y' ∧ t = t' :=
  Fin.snoc_inj

/-- **Proposition 5.B.2** (MWG, p. 134), without the hypothesis `0 ∈ Y`, which the proof
(p. 135) does not use: for a convex `Y ⊆ ℝ^L` there is a constant returns, convex
`Y' ⊆ ℝ^{L+1}` with `Y = {y : (y, -1) ∈ Y'}`, namely `Y' = {α(y, -1) : y ∈ Y, α ≥ 0}`. -/
theorem proposition_5_B_2_general {Y : Set (Fin L → ℝ)} (hc : Convex ℝ Y) :
    ∃ Y' : Set (Fin (L + 1) → ℝ), ConstantReturns Y' ∧ Convex ℝ Y' ∧
      Y = {y | extendVec y (-1) ∈ Y'} := by
  refine ⟨{v | ∃ y ∈ Y, ∃ α : ℝ, 0 ≤ α ∧ v = α • extendVec y (-1)}, ?_, ?_, ?_⟩
  · rintro _ ⟨y, hy, α, hα, rfl⟩ β hβ
    exact ⟨y, hy, β * α, mul_nonneg hβ hα, by rw [smul_smul]⟩
  · rintro _ ⟨y, hy, α, hα, rfl⟩ _ ⟨y', hy', α', hα', rfl⟩ a b ha hb hab
    rcases (add_nonneg (mul_nonneg ha hα) (mul_nonneg hb hα')).lt_or_eq with hpos | hzero
    · set s := a * α + b * α'
      have hm := hc hy hy' (div_nonneg (mul_nonneg ha hα) hpos.le)
        (div_nonneg (mul_nonneg hb hα') hpos.le) (by rw [← add_div]; exact div_self hpos.ne')
      refine ⟨_, hm, s, hpos.le, ?_⟩
      rw [smul_smul, smul_smul, extendVec_smul, extendVec_smul, extendVec_add,
        extendVec_smul, smul_add, smul_smul, smul_smul, mul_div_cancel₀ _ hpos.ne',
        mul_div_cancel₀ _ hpos.ne']
      congr 1
      ring
    · have h1 : a * α = 0 := by linarith [mul_nonneg ha hα, mul_nonneg hb hα']
      have h2 : b * α' = 0 := by linarith [mul_nonneg ha hα, mul_nonneg hb hα']
      refine ⟨y, hy, 0, le_rfl, ?_⟩
      rw [smul_smul, smul_smul, h1, h2]
      simp only [zero_smul, add_zero]
  · ext y
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro hy
      exact ⟨y, hy, 1, zero_le_one, by rw [one_smul]⟩
    · rintro ⟨y', hy', α, _, h⟩
      rw [extendVec_smul, extendVec_inj] at h
      have hα : α = 1 := by linarith [h.2]
      rw [h.1, hα, one_smul]
      exact hy'

/-- **Proposition 5.B.2** (MWG, p. 134), as printed, with `0 ∈ Y`. -/
theorem proposition_5_B_2 {Y : Set (Fin L → ℝ)} (hc : Convex ℝ Y) (_h0 : (0 : Fin L → ℝ) ∈ Y) :
    ∃ Y' : Set (Fin (L + 1) → ℝ), ConstantReturns Y' ∧ Convex ℝ Y' ∧
      Y = {y | extendVec y (-1) ∈ Y'} :=
  proposition_5_B_2_general hc

/-- **Example 5.B.1** (MWG, p. 128). For `L = 5` and `y = (-5, 2, -6, 3, 0)`, goods 2 and 4 are
outputs (2 and 3 units), goods 1 and 3 are inputs (5 and 6 units), and good 5 is neither. -/
theorem example_5_B_1 :
    let y : Fin 5 → ℝ := ![-5, 2, -6, 3, 0]
    (0 < y 1 ∧ y 1 = 2) ∧ (0 < y 3 ∧ y 3 = 3) ∧ (y 0 < 0 ∧ -y 0 = 5) ∧
      (y 2 < 0 ∧ -y 2 = 6) ∧ y 4 = 0 := by
  norm_num

/-! ### The transformation function -/

/-- **Section 5.B** (MWG, p. 128). `F` is a transformation function for `Y`:
`Y = {y : F(y) ≤ 0}` and `F(y) = 0` exactly on the boundary of `Y`. -/
def IsTransformationFunction (F : (Fin L → ℝ) → ℝ) (Y : Set (Fin L → ℝ)) : Prop :=
  Y = {y | F y ≤ 0} ∧ ∀ y, F y = 0 ↔ y ∈ frontier Y

/-- The partial derivative `∂F(ȳ)/∂y_l`, read off the Fréchet derivative. -/
noncomputable def partialAt (F : (Fin L → ℝ) → ℝ) (y : Fin L → ℝ) (l : Fin L) : ℝ :=
  fderiv ℝ F y (Pi.single l 1)

/-- **Section 5.B** (MWG, p. 129). The marginal rate of transformation of good `l` for good `k`
at `ȳ`, `MRT_{lk}(ȳ) = (∂F(ȳ)/∂y_l)/(∂F(ȳ)/∂y_k)` (computed when `∂F(ȳ)/∂y_k ≠ 0`,
footnote 1). -/
noncomputable def MRT (F : (Fin L → ℝ) → ℝ) (y : Fin L → ℝ) (l k : Fin L) : ℝ :=
  partialAt F y l / partialAt F y k

/-- **Section 5.B** (MWG, p. 129), `∂F/∂y_k dy_k + ∂F/∂y_l dy_l = 0`. If `γ` is a curve on the
transformation frontier `F = 0` through `ȳ` that moves only goods `l ≠ k`, then
`F_k γ_k'(0) + F_l γ_l'(0) = 0`; hence `γ_k'(0) = -MRT_{lk}(ȳ) γ_l'(0)` when `F_k ≠ 0`: the slope
of the frontier is `-MRT`. -/
theorem mrt_slope {F : (Fin L → ℝ) → ℝ} {y : Fin L → ℝ} (hF : DifferentiableAt ℝ F y)
    {γ : ℝ → Fin L → ℝ} {γ' : Fin L → ℝ} (hγ : HasDerivAt γ γ' 0) (h0 : γ 0 = y)
    (hfront : ∀ t, F (γ t) = 0) {l k : Fin L} (hlk : l ≠ k)
    (hother : ∀ i, i ≠ l → i ≠ k → γ' i = 0) :
    partialAt F y k * γ' k + partialAt F y l * γ' l = 0 ∧
      (partialAt F y k ≠ 0 → γ' k = -MRT F y l k * γ' l) := by
  have hcomp : HasDerivAt (fun t => F (γ t)) (fderiv ℝ F y γ') 0 := by
    have hF' : HasFDerivAt F (fderiv ℝ F y) (γ 0) := by rw [h0]; exact hF.hasFDerivAt
    exact hF'.comp_hasDerivAt 0 hγ
  have hconst : HasDerivAt (fun t => F (γ t)) 0 0 := by
    have : (fun t => F (γ t)) = fun _ => (0 : ℝ) := funext hfront
    rw [this]
    exact hasDerivAt_const 0 0
  have hzero : fderiv ℝ F y γ' = 0 := hcomp.unique hconst
  have hdecomp : γ' = γ' k • Pi.single k 1 + γ' l • Pi.single l 1 := by
    funext i
    by_cases hik : i = k
    · subst hik
      simp [Ne.symm hlk]
    · by_cases hil : i = l
      · subst hil
        simp [hik]
      · simp [hik, hil, hother i hil hik]
  have key : partialAt F y k * γ' k + partialAt F y l * γ' l = 0 := by
    rw [hdecomp, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at hzero
    unfold partialAt
    linarith
  refine ⟨key, fun hk => ?_⟩
  unfold MRT
  field_simp
  linarith

/-- A transformation function exists for the half-plane `{y : y₁ + y₂ ≤ 0}` of `ℝ²`:
`F(y) = y₁ + y₂` (Figure 5.B.1's setting), so `IsTransformationFunction` is satisfiable. -/
theorem isTransformationFunction_halfPlane :
    IsTransformationFunction (fun y : Fin 2 → ℝ => y 0 + y 1) {y | y 0 + y 1 ≤ 0} := by
  refine ⟨rfl, fun y => ?_⟩
  have hcont : Continuous fun y : Fin 2 → ℝ => y 0 + y 1 := by fun_prop
  have hcl : IsClosed {y : Fin 2 → ℝ | y 0 + y 1 ≤ 0} := isClosed_le hcont continuous_const
  rw [frontier, hcl.closure_eq]
  constructor
  · intro hy
    refine ⟨show y 0 + y 1 ≤ 0 from hy.le, fun hint => ?_⟩
    rw [mem_interior_iff_mem_nhds] at hint
    have hg : Continuous fun t : ℝ => y + t • (1 : Fin 2 → ℝ) := by fun_prop
    have hpre := hg.continuousAt (x := 0) (by simpa using hint)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hpre
    have hmem : ε / 2 ∈ Metric.ball (0 : ℝ) ε := by
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos (by positivity)]
      linarith
    have := hball hmem
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, Pi.one_apply,
      smul_eq_mul, mul_one] at this
    linarith
  · rintro ⟨hle, hnot⟩
    by_contra hne
    have hlt : y 0 + y 1 < 0 := lt_of_le_of_ne hle hne
    apply hnot
    have hopen : IsOpen {y : Fin 2 → ℝ | y 0 + y 1 < 0} := isOpen_lt hcont continuous_const
    exact interior_maximal (t := {y : Fin 2 → ℝ | y 0 + y 1 < 0})
      (fun z (hz : z 0 + z 1 < 0) => (le_of_lt hz : z 0 + z 1 ≤ 0)) hopen
      (show y 0 + y 1 < 0 from hlt)

/-! ### Single-output technologies -/

/-- The input vector `z = (-y₁, …, -y_{L-1})` of `y ∈ ℝ^{L}` with output in the last place. -/
def inputsOf {n : ℕ} (y : Fin (n + 1) → ℝ) : Fin n → ℝ := fun i => -y (Fin.castSucc i)

/-- **Section 5.B** (MWG, p. 129). The production set of a single-output technology with
production function `f` (output good `L`, free disposal of output):
`Y = {(-z, q) : q - f(z) ≤ 0, z ≥ 0}`. -/
def singleOutputSet {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Set (Fin (n + 1) → ℝ) :=
  {y | 0 ≤ inputsOf y ∧ y (Fin.last n) - f (inputsOf y) ≤ 0}

theorem inputsOf_extendVec {n : ℕ} (z : Fin n → ℝ) (q : ℝ) : inputsOf (extendVec (-z) q) = z := by
  funext i
  simp [inputsOf, extendVec]

theorem mem_singleOutputSet {n : ℕ} {f : (Fin n → ℝ) → ℝ} {z : Fin n → ℝ} {q : ℝ} :
    extendVec (-z) q ∈ singleOutputSet f ↔ 0 ≤ z ∧ q ≤ f z := by
  change 0 ≤ inputsOf (extendVec (-z) q) ∧
      extendVec (-z) q (Fin.last n) - f (inputsOf (extendVec (-z) q)) ≤ 0 ↔ _
  rw [inputsOf_extendVec, sub_nonpos]
  simp [extendVec]

theorem extendVec_inputsOf {n : ℕ} (y : Fin (n + 1) → ℝ) :
    extendVec (-inputsOf y) (y (Fin.last n)) = y := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [extendVec]
  · simp [extendVec, inputsOf]

/-- The partial derivative `∂f(z̄)/∂z_l` of a production function. -/
noncomputable def partialF {n : ℕ} (f : (Fin n → ℝ) → ℝ) (z : Fin n → ℝ) (l : Fin n) : ℝ :=
  fderiv ℝ f z (Pi.single l 1)

/-- **Section 5.B** (MWG, p. 130). The marginal rate of technical substitution of input `l` for
input `k` at `z̄`, `MRTS_{lk}(z̄) = (∂f(z̄)/∂z_l)/(∂f(z̄)/∂z_k)`. -/
noncomputable def MRTS {n : ℕ} (f : (Fin n → ℝ) → ℝ) (z : Fin n → ℝ) (l k : Fin n) : ℝ :=
  partialF f z l / partialF f z k

/-- **Exercise 5.B.2** (MWG, p. 132). A single-output technology has constant returns to scale
if and only if its production function is homogeneous of degree one on `ℝ^{L-1}_+`. -/
theorem exercise_5_B_2 {n : ℕ} (f : (Fin n → ℝ) → ℝ) :
    ConstantReturns (singleOutputSet f) ↔
      ∀ z : Fin n → ℝ, 0 ≤ z → ∀ α : ℝ, 0 < α → f (α • z) = α * f z := by
  constructor
  · intro h z hz α hα
    have key : ∀ z : Fin n → ℝ, 0 ≤ z → ∀ α : ℝ, 0 < α → α * f z ≤ f (α • z) := by
      intro z hz α hα
      have hm : extendVec (-z) (f z) ∈ singleOutputSet f := mem_singleOutputSet.mpr ⟨hz, le_rfl⟩
      have := h _ hm α hα.le
      rw [extendVec_smul, smul_neg] at this
      exact (mem_singleOutputSet.mp this).2
    apply le_antisymm
    · have hz' : 0 ≤ α • z := smul_nonneg hα.le hz
      have := key (α • z) hz' α⁻¹ (inv_pos.mpr hα)
      rw [smul_smul, inv_mul_cancel₀ hα.ne', one_smul] at this
      have h2 := mul_le_mul_of_nonneg_left this hα.le
      rwa [← mul_assoc, mul_inv_cancel₀ hα.ne', one_mul] at h2
    · exact key z hz α hα
  · intro h y hy α hα
    have hy' := hy
    rw [← extendVec_inputsOf y] at hy' ⊢
    obtain ⟨hz, hq⟩ := mem_singleOutputSet.mp hy'
    rw [extendVec_smul, smul_neg, mem_singleOutputSet]
    refine ⟨smul_nonneg hα hz, ?_⟩
    rcases hα.lt_or_eq with hpos | hzero
    · rw [h _ hz α hpos]
      exact mul_le_mul_of_nonneg_left hq hpos.le
    · subst hzero
      have h0 := h 0 le_rfl 2 two_pos
      rw [smul_zero] at h0
      rw [zero_smul, zero_mul]
      linarith

/-- **Exercise 5.B.3** (MWG, p. 134). A single-output production set is convex if and only if
the production function is concave on `ℝ^{L-1}_+`. -/
theorem exercise_5_B_3 {n : ℕ} (f : (Fin n → ℝ) → ℝ) :
    Convex ℝ (singleOutputSet f) ↔ ConcaveOn ℝ {z : Fin n → ℝ | 0 ≤ z} f := by
  have hconv : Convex ℝ {z : Fin n → ℝ | 0 ≤ z} := fun x hx y hy a b ha hb _ =>
    show 0 ≤ a • x + b • y from add_nonneg (smul_nonneg ha hx) (smul_nonneg hb hy)
  constructor
  · intro h
    refine ⟨hconv, fun z hz z' hz' a b ha hb hab => ?_⟩
    have hm := h (mem_singleOutputSet.mpr ⟨hz, le_rfl⟩)
      (mem_singleOutputSet.mpr ⟨hz', le_rfl⟩) ha hb hab
    rw [extendVec_smul, extendVec_smul, extendVec_add, smul_neg, smul_neg, ← neg_add,
      mem_singleOutputSet] at hm
    simpa [smul_eq_mul] using hm.2
  · intro h y hy y' hy' a b ha hb hab
    rw [← extendVec_inputsOf y] at hy
    rw [← extendVec_inputsOf y'] at hy'
    obtain ⟨hz, hq⟩ := mem_singleOutputSet.mp hy
    obtain ⟨hz', hq'⟩ := mem_singleOutputSet.mp hy'
    rw [← extendVec_inputsOf y, ← extendVec_inputsOf y', extendVec_smul, extendVec_smul,
      extendVec_add, smul_neg, smul_neg, ← neg_add, mem_singleOutputSet]
    refine ⟨hconv hz hz' ha hb hab, ?_⟩
    calc a * y (Fin.last n) + b * y' (Fin.last n) ≤ a * f (inputsOf y) + b * f (inputsOf y') :=
          add_le_add (mul_le_mul_of_nonneg_left hq ha) (mul_le_mul_of_nonneg_left hq' hb)
      _ ≤ f (a • inputsOf y + b • inputsOf y') := by
          have := h.2 hz hz' ha hb hab
          simpa [smul_eq_mul] using this

/-- **Exercise 5.B.1** (MWG, p. 132), drawn as two sets in `ℝ²`. The half-plane
`{y : y₁ + y₂ ≤ 0}` violates irreversibility (it contains `(1, -1)` and `(-1, 1)`), and
`{y : y₁ ≤ 0, y₂ ≤ -y₁}` satisfies it. -/
theorem exercise_5_B_1 :
    ¬ Irreversible {y : Fin 2 → ℝ | y 0 + y 1 ≤ 0} ∧
      Irreversible {y : Fin 2 → ℝ | y 0 ≤ 0 ∧ y 1 ≤ -y 0} := by
  constructor
  · intro h
    have hy : (![1, -1] : Fin 2 → ℝ) ∈ {y : Fin 2 → ℝ | y 0 + y 1 ≤ 0} := by
      simp
    have hne : (![1, -1] : Fin 2 → ℝ) ≠ 0 := by
      intro h0
      have := congrFun h0 0
      simp at this
    apply h _ hy hne
    simp
  · rintro y ⟨h0, h1⟩ hne ⟨h0', h1'⟩
    simp only [Pi.neg_apply, neg_neg] at h0' h1'
    apply hne
    funext i
    fin_cases i <;> simp <;> linarith

/-- **Figure 5.B.8** (MWG, p. 133). The staircase technology in `ℝ²` (output in integer
amounts, each unit costing one unit of input) is additive but not convex. -/
theorem figure_5_B_8 :
    Additive {y : Fin 2 → ℝ | ∃ k : ℕ, y 1 ≤ k ∧ y 0 ≤ -k} ∧
      ¬ Convex ℝ {y : Fin 2 → ℝ | ∃ k : ℕ, y 1 ≤ k ∧ y 0 ≤ -k} := by
  constructor
  · rintro y ⟨k, hk1, hk0⟩ y' ⟨k', hk1', hk0'⟩
    refine ⟨k + k', ?_, ?_⟩ <;> simp only [Pi.add_apply, Nat.cast_add] <;> linarith
  · intro h
    have ha : (![-1, 1] : Fin 2 → ℝ) ∈ {y : Fin 2 → ℝ | ∃ k : ℕ, y 1 ≤ k ∧ y 0 ≤ -k} :=
      ⟨1, by simp, by simp⟩
    have hb : (0 : Fin 2 → ℝ) ∈ {y : Fin 2 → ℝ | ∃ k : ℕ, y 1 ≤ k ∧ y 0 ≤ -k} :=
      ⟨0, by simp, by simp⟩
    obtain ⟨k, hk1, hk0⟩ := h ha hb (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mul_zero,
      add_zero] at hk1 hk0
    norm_num at hk1 hk0
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      norm_num at hk1
    · have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      linarith

end MWG.Production

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The profit maximization problem (MWG Section 5.C, pp. 135-139)

The profit function and supply correspondence of a production set `Y ⊆ ℝ^L`:

* `profitFn Y p = sup {p·y : y ∈ Y}` with values in `[-∞, +∞]` (footnote 5), its real version
  `profit Y p` (where `p·y` is bounded above on `Y`), and `supply Y p`, the set of
  profit-maximizing plans. The bridge `profit_eq_neg_supportFn` gives `π(p) = -μ_{-Y}(p)`
  (p. 137) in terms of Chapter 3's support function.
* The constant-returns example on p. 136, **Exercise 5.C.1**, the law of supply (5.C.3).
* **Proposition 5.C.1** (i)-(vii), with **Exercise 5.C.2** (= (ii)).

Departures (see `docs/corrections.md`): (iii) is false as printed with prices `p ≫ 0`
(`proposition_5_C_1_iii_counterexample`); it holds with all `p ≥ 0`
(`proposition_5_C_1_iii_nonneg`) and with `p ≫ 0` when profits are bounded at some `p₀ ≫ 0`
(`proposition_5_C_1_iii`). Hotelling's lemma (vi) needs convexity
(`proposition_5_C_1_vi_nonconvex_counterexample`); (vii) is proved for convex `Y`, with the
semidefiniteness and `Dy(p̄)p̄ = 0` parts for every `Y`.
-/

namespace MWG.Production

open MWG.ClassicalDemand MWG.ConsumerChoice Filter Topology

variable {L : ℕ}

/-- **Section 5.C** (MWG, p. 136, footnote 5). The profit function
`π(p) = sup {p·y : y ∈ Y}`, with values in `[-∞, +∞]`. -/
noncomputable def profitFn (Y : Set (Fin L → ℝ)) (p : Fin L → ℝ) : EReal :=
  ⨆ y ∈ Y, ((p ⬝ᵥ y : ℝ) : EReal)

/-- The real profit function `sup {p·y : y ∈ Y}`, meaningful where `p·y` is bounded above on a
nonempty `Y` (there it equals `profitFn`, `profitFn_eq_coe`). -/
noncomputable def profit (Y : Set (Fin L → ℝ)) (p : Fin L → ℝ) : ℝ :=
  sSup ((fun y => p ⬝ᵥ y) '' Y)

/-- **Section 5.C** (MWG, p. 136). The supply correspondence `y(p) = {y ∈ Y : p·y = π(p)}`, the
set of profit-maximizing production plans. -/
def supply (Y : Set (Fin L → ℝ)) (p : Fin L → ℝ) : Set (Fin L → ℝ) :=
  {y | y ∈ Y ∧ ∀ y' ∈ Y, p ⬝ᵥ y' ≤ p ⬝ᵥ y}

/-- `p·y ≤ π(p)` for every `y ∈ Y`. -/
theorem le_profitFn {Y : Set (Fin L → ℝ)} {p y : Fin L → ℝ} (hy : y ∈ Y) :
    ((p ⬝ᵥ y : ℝ) : EReal) ≤ profitFn Y p :=
  le_iSup₂ (f := fun y (_ : y ∈ Y) => ((p ⬝ᵥ y : ℝ) : EReal)) y hy

/-- An upper bound for profits bounds the profit function. -/
theorem profitFn_le {Y : Set (Fin L → ℝ)} {p : Fin L → ℝ} {c : EReal}
    (h : ∀ y ∈ Y, ((p ⬝ᵥ y : ℝ) : EReal) ≤ c) : profitFn Y p ≤ c :=
  iSup₂_le h

/-- Where profits are bounded above on a nonempty `Y`, the two profit functions agree. -/
theorem profitFn_eq_coe {Y : Set (Fin L → ℝ)} (hne : Y.Nonempty) {p : Fin L → ℝ}
    (hb : BddAbove ((fun y => p ⬝ᵥ y) '' Y)) : profitFn Y p = (profit Y p : EReal) := by
  apply le_antisymm
  · exact profitFn_le fun y hy => EReal.coe_le_coe_iff.mpr (le_csSup hb ⟨y, hy, rfl⟩)
  · by_contra h
    rw [not_le] at h
    obtain ⟨r, hr1, hr2⟩ := EReal.lt_iff_exists_real_btwn.mp h
    have : profit Y p ≤ r := by
      apply csSup_le (hne.image _)
      rintro _ ⟨y, hy, rfl⟩
      exact (EReal.coe_le_coe_iff.mp ((le_profitFn hy).trans hr1.le))
    have := EReal.coe_lt_coe_iff.mp hr2
    linarith

/-- **Footnote 5** (MWG, p. 136). Where profits are unbounded, `π(p) = +∞`. -/
theorem profitFn_eq_top {Y : Set (Fin L → ℝ)} {p : Fin L → ℝ}
    (hb : ¬ BddAbove ((fun y => p ⬝ᵥ y) '' Y)) : profitFn Y p = ⊤ := by
  rw [EReal.eq_top_iff_forall_lt]
  intro r
  rw [not_bddAbove_iff] at hb
  obtain ⟨_, ⟨y, hy, rfl⟩, hlt⟩ := hb r
  exact (EReal.coe_lt_coe_iff.mpr hlt).trans_le (le_profitFn hy)

/-- `π(p) < +∞` exactly when profits are bounded above. -/
theorem profitFn_lt_top_iff {Y : Set (Fin L → ℝ)} {p : Fin L → ℝ} :
    profitFn Y p < ⊤ ↔ BddAbove ((fun y => p ⬝ᵥ y) '' Y) := by
  constructor
  · intro h
    by_contra hb
    rw [profitFn_eq_top hb] at h
    exact lt_irrefl _ h
  · rintro ⟨m, hm⟩
    exact (profitFn_le fun y hy => EReal.coe_le_coe_iff.mpr (hm ⟨y, hy, rfl⟩)).trans_lt
      (EReal.coe_lt_top m)

/-- A profit-maximizing plan gives the value of the profit function. -/
theorem profit_eq_of_mem_supply {Y : Set (Fin L → ℝ)} {p y : Fin L → ℝ} (hy : y ∈ supply Y p) :
    profit Y p = p ⬝ᵥ y :=
  IsGreatest.csSup_eq ⟨⟨y, hy.1, rfl⟩, by rintro _ ⟨y', hy', rfl⟩; exact hy.2 y' hy'⟩

/-- A profit-maximizing plan gives the value of the extended profit function. -/
theorem profitFn_eq_of_mem_supply {Y : Set (Fin L → ℝ)} {p y : Fin L → ℝ}
    (hy : y ∈ supply Y p) : profitFn Y p = ((p ⬝ᵥ y : ℝ) : EReal) :=
  le_antisymm (profitFn_le fun y' hy' => EReal.coe_le_coe_iff.mpr (hy.2 y' hy'))
    (le_profitFn hy.1)

/-- `y ∈ y(p)` iff `y ∈ Y` and `p·y = π(p)`, the book's definition (p. 136). -/
theorem mem_supply_iff {Y : Set (Fin L → ℝ)} {p y : Fin L → ℝ} :
    y ∈ supply Y p ↔ y ∈ Y ∧ ((p ⬝ᵥ y : ℝ) : EReal) = profitFn Y p := by
  constructor
  · intro hy
    exact ⟨hy.1, (profitFn_eq_of_mem_supply hy).symm⟩
  · rintro ⟨hy, h⟩
    refine ⟨hy, fun y' hy' => ?_⟩
    have := le_profitFn (p := p) hy'
    rw [← h] at this
    exact EReal.coe_le_coe_iff.mp this

open scoped Pointwise in
/-- **Section 5.C** (MWG, p. 137). `π(p) = -μ_{-Y}(p)`, where `μ_{-Y}` is Chapter 3's support
function (Definition 3.F.1) of `-Y`. -/
theorem profit_eq_neg_supportFn (Y : Set (Fin L → ℝ)) (p : Fin L → ℝ) :
    profit Y p = -supportFn (-Y) p := by
  unfold profit supportFn
  have : (fun x => p ⬝ᵥ x) '' (-Y) = -((fun y => p ⬝ᵥ y) '' Y) := by
    ext t
    simp only [Set.mem_image, Set.mem_neg]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨-x, hx, by simp [dotProduct_neg]⟩
    · rintro ⟨y, hy, h⟩
      exact ⟨-y, by rwa [neg_neg], by rw [dotProduct_neg, h, neg_neg]⟩
  rw [this, Real.sInf_neg, neg_neg]

open scoped Pointwise in
/-- **Section 5.C** (MWG, p. 137). The supply correspondence is `-` the set of minimizers of
`p·x` on `-Y`. -/
theorem supply_eq_neg_supportArgmin (Y : Set (Fin L → ℝ)) (p : Fin L → ℝ) :
    supply Y p = -supportArgmin (-Y) p := by
  ext y
  simp only [supply, supportArgmin, Set.mem_neg, Set.mem_ofPred_eq, neg_neg]
  constructor
  · rintro ⟨hy, hmax⟩
    refine ⟨hy, fun x hx => ?_⟩
    have := hmax (-x) hx
    simp only [dotProduct_neg] at this ⊢
    linarith
  · rintro ⟨hy, hmin⟩
    refine ⟨hy, fun y' hy' => ?_⟩
    have := hmin (-y') (by rwa [neg_neg])
    simp only [dotProduct_neg] at this ⊢
    linarith

open scoped Pointwise in
/-- Boundedness of profits on `Y` is boundedness below of `p·x` on `-Y`. -/
theorem bddAbove_iff_bddBelow_neg (Y : Set (Fin L → ℝ)) (p : Fin L → ℝ) :
    BddAbove ((fun y => p ⬝ᵥ y) '' Y) ↔ BddBelow ((fun x => p ⬝ᵥ x) '' (-Y)) := by
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨-m, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have := hm ⟨-x, hx, rfl⟩
    simp only [dotProduct_neg] at this
    linarith
  · rintro ⟨m, hm⟩
    refine ⟨-m, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    have := hm ⟨-y, by rwa [Set.mem_neg, neg_neg], rfl⟩
    simp only [dotProduct_neg] at this
    linarith

/-! ### The example on p. 136 and Exercise 5.C.1 -/

/-- The constant-returns technology of p. 136: one unit of good 2 per unit of good 1 used,
with free disposal: `{y ∈ ℝ² : y₁ ≤ 0, y₁ + y₂ ≤ 0}`. -/
def oneForOneTech : Set (Fin 2 → ℝ) := {y | y 0 ≤ 0 ∧ y 0 + y 1 ≤ 0}

/-- **Section 5.C** (MWG, p. 136). For the one-for-one constant-returns technology and `p ≫ 0`,
`π(p) = 0` if `p₂ ≤ p₁` and `π(p) = +∞` if `p₂ > p₁`. -/
theorem example_5_C_profit_oneForOne {p : Fin 2 → ℝ} (hp : StrictlyPositive p) :
    (p 1 ≤ p 0 → profitFn oneForOneTech p = 0) ∧
      (p 0 < p 1 → profitFn oneForOneTech p = ⊤) := by
  constructor
  · intro h
    apply le_antisymm
    · apply profitFn_le
      rintro y ⟨h0, h1⟩
      rw [EReal.coe_nonpos]
      simp only [dotProduct, Fin.sum_univ_two]
      nlinarith [hp 0, hp 1]
    · have := le_profitFn (Y := oneForOneTech) (p := p) (y := 0)
        ⟨le_rfl, by simp⟩
      simpa using this
  · intro h
    apply profitFn_eq_top
    rw [not_bddAbove_iff]
    intro r
    set t := (|r| + 1) / (p 1 - p 0) with ht
    have hpos : 0 < p 1 - p 0 := by linarith
    refine ⟨_, ⟨![-t, t], ⟨?_, ?_⟩, rfl⟩, ?_⟩
    · simp only [Matrix.cons_val_zero, neg_nonpos]
      exact div_nonneg (by positivity) hpos.le
    · simp
    · simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      have : p 0 * -t + p 1 * t = |r| + 1 := by
        rw [ht]
        field_simp
        ring
      rw [this]
      linarith [le_abs_self r]

/-- **Exercise 5.C.1** (MWG, p. 136). With nondecreasing returns to scale, either `π(p) ≤ 0` or
`π(p) = +∞`. -/
theorem exercise_5_C_1 {Y : Set (Fin L → ℝ)} (h : NondecreasingReturns Y) (p : Fin L → ℝ) :
    profitFn Y p ≤ 0 ∨ profitFn Y p = ⊤ := by
  by_cases hpos : ∃ y ∈ Y, 0 < p ⬝ᵥ y
  · right
    obtain ⟨y, hy, hpy⟩ := hpos
    apply profitFn_eq_top
    rw [not_bddAbove_iff]
    intro r
    set α := max 1 ((|r| + 1) / (p ⬝ᵥ y)) with hα
    refine ⟨_, ⟨α • y, h y hy α (le_max_left _ _), rfl⟩, ?_⟩
    change r < p ⬝ᵥ (α • y)
    rw [dotProduct_smul, smul_eq_mul]
    have h1 : (|r| + 1) / (p ⬝ᵥ y) ≤ α := le_max_right _ _
    have h2 : |r| + 1 ≤ α * (p ⬝ᵥ y) := by
      rwa [div_le_iff₀ hpy] at h1
    linarith [le_abs_self r]
  · left
    push Not at hpos
    exact profitFn_le fun y hy => EReal.coe_nonpos.mpr (hpos y hy)

/-! ### Proposition 5.C.1 -/

/-- **Proposition 5.C.1(i)** (MWG, p. 138). The profit function is homogeneous of degree one:
`π(αp) = απ(p)` for `α > 0`. -/
theorem proposition_5_C_1_i (Y : Set (Fin L → ℝ)) (p : Fin L → ℝ) {α : ℝ} (hα : 0 < α) :
    profitFn Y (α • p) = (α : EReal) * profitFn Y p := by
  have key : ∀ (β : ℝ), 0 < β → ∀ q : Fin L → ℝ,
      profitFn Y (β • q) ≤ (β : EReal) * profitFn Y q := by
    intro β hβ q
    apply profitFn_le
    intro y hy
    rw [smul_dotProduct, smul_eq_mul, EReal.coe_mul]
    exact mul_le_mul_of_nonneg_left (le_profitFn hy) (EReal.coe_nonneg.mpr hβ.le)
  apply le_antisymm (key α hα p)
  have h2 := key α⁻¹ (inv_pos.mpr hα) (α • p)
  rw [smul_smul, inv_mul_cancel₀ hα.ne', one_smul] at h2
  calc (α : EReal) * profitFn Y p ≤ (α : EReal) * ((α⁻¹ : ℝ) * profitFn Y (α • p)) :=
        mul_le_mul_of_nonneg_left h2 (EReal.coe_nonneg.mpr hα.le)
    _ = profitFn Y (α • p) := by
        rw [← mul_assoc, ← EReal.coe_mul, mul_inv_cancel₀ hα.ne', EReal.coe_one, one_mul]

/-- **Proposition 5.C.1(ii)** and **Exercise 5.C.2** (MWG, p. 138). The profit function is
convex: `π(αp + (1-α)p') ≤ απ(p) + (1-α)π(p')` for `α ∈ [0, 1]`, in `[-∞, +∞]`. -/
theorem proposition_5_C_1_ii (Y : Set (Fin L → ℝ)) (p p' : Fin L → ℝ) {α : ℝ} (h0 : 0 ≤ α)
    (h1 : α ≤ 1) :
    profitFn Y (α • p + (1 - α) • p') ≤
      (α : EReal) * profitFn Y p + ((1 - α : ℝ) : EReal) * profitFn Y p' := by
  apply profitFn_le
  intro y hy
  rw [add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul,
    EReal.coe_add, EReal.coe_mul, EReal.coe_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left (le_profitFn hy) (EReal.coe_nonneg.mpr h0))
    (mul_le_mul_of_nonneg_left (le_profitFn hy) (EReal.coe_nonneg.mpr (by linarith)))

/-- **Exercise 5.C.2** (MWG, p. 138), the hint's argument for a maximizer `y ∈ y(αp + (1-α)p')`. -/
theorem exercise_5_C_2 (Y : Set (Fin L → ℝ)) (p p' : Fin L → ℝ) {α : ℝ} (h0 : 0 ≤ α)
    (h1 : α ≤ 1) :
    profitFn Y (α • p + (1 - α) • p') ≤
      (α : EReal) * profitFn Y p + ((1 - α : ℝ) : EReal) * profitFn Y p' :=
  proposition_5_C_1_ii Y p p' h0 h1

/-- **Proposition 5.C.1(ii)** (MWG, p. 138), real form: `π` is convex on the convex set of
prices at which profits are bounded, from the concavity of Chapter 3's support function. -/
theorem proposition_5_C_1_ii_real {Y : Set (Fin L → ℝ)} (hne : Y.Nonempty) :
    ConvexOn ℝ {p : Fin L → ℝ | BddAbove ((fun y => p ⬝ᵥ y) '' Y)} (profit Y) := by
  have hne' : (-Y).Nonempty := by
    obtain ⟨y, hy⟩ := hne
    exact ⟨-y, by rwa [Set.mem_neg, neg_neg]⟩
  have hc := supportFn_concaveOn hne'
  have hdom : {p : Fin L → ℝ | BddAbove ((fun y => p ⬝ᵥ y) '' Y)} =
      {p : Fin L → ℝ | BddBelow ((fun x => p ⬝ᵥ x) '' (-Y))} := by
    ext p
    exact bddAbove_iff_bddBelow_neg Y p
  rw [hdom]
  have : profit Y = -supportFn (-Y) := funext fun p => profit_eq_neg_supportFn Y p
  rw [this]
  exact hc.neg

/-- A nonzero vector of `ℝ^L` with a negative coordinate is unbounded against free disposal:
if `Y` is nonempty with free disposal and `p·y ≤ c` on `Y`, then `p ≥ 0`. -/
theorem nonneg_of_bdd_freeDisposal {Y : Set (Fin L → ℝ)} (hne : Y.Nonempty)
    (hfd : FreeDisposal Y) {p : Fin L → ℝ} {c : ℝ} (hc : ∀ y ∈ Y, p ⬝ᵥ y ≤ c) : 0 ≤ p := by
  intro l
  by_contra hl0
  have hl : p l < 0 := not_le.mp hl0
  have hpl : p l ≠ 0 := hl.ne
  obtain ⟨y, hy⟩ := hne
  set t := (|c| + |p ⬝ᵥ y| + 1) / (-p l) with ht
  have htpos : 0 ≤ t := div_nonneg (by positivity) (by linarith)
  have hmem : y - t • Pi.single l 1 ∈ Y := by
    apply hfd y hy
    exact sub_le_self y (smul_nonneg htpos (Pi.single_nonneg.mpr zero_le_one))
  have := hc _ hmem
  rw [dotProduct_sub, dotProduct_smul, dotProduct_single, mul_one, smul_eq_mul] at this
  have h2 : t * p l = -(|c| + |p ⬝ᵥ y| + 1) := by
    rw [ht, div_mul_eq_mul_div, div_neg, mul_div_assoc, div_self hpl, mul_one]
  rw [h2] at this
  linarith [le_abs_self c, neg_abs_le (p ⬝ᵥ y)]

/-- **Proposition 5.C.1(iii)**, corrected (MWG, p. 138). If `Y` is closed, convex and has free
disposal, then `Y = {y : p·y ≤ π(p) for all p ≥ 0}`. -/
theorem proposition_5_C_1_iii_nonneg {Y : Set (Fin L → ℝ)} (hcl : IsClosed Y)
    (hc : Convex ℝ Y) (hfd : FreeDisposal Y) :
    Y = {y | ∀ p : Fin L → ℝ, 0 ≤ p → ((p ⬝ᵥ y : ℝ) : EReal) ≤ profitFn Y p} := by
  ext x
  constructor
  · intro hx p _
    exact le_profitFn hx
  · intro hx
    by_contra hxY
    rcases Y.eq_empty_or_nonempty with hY | hne
    · have := hx 0 le_rfl
      rw [hY] at this
      simp [profitFn] at this
    obtain ⟨q, c, hqx, hqY⟩ := separation_section_3_F hcl hc hxY
    have hb : ∀ y ∈ Y, (-q) ⬝ᵥ y ≤ -c := by
      intro y hy
      rw [neg_dotProduct]
      linarith [hqY y hy]
    have hp0 := nonneg_of_bdd_freeDisposal hne hfd hb
    have h1 := (hx (-q) hp0).trans (profitFn_le fun y hy => EReal.coe_le_coe_iff.mpr (hb y hy))
    have h2 := EReal.coe_le_coe_iff.mp h1
    rw [neg_dotProduct] at h2
    linarith

/-- **Proposition 5.C.1(iii)** (MWG, p. 138) with prices `p ≫ 0`, under the extra hypothesis
that profits are bounded at some `p₀ ≫ 0` (or `Y = ∅`): if `Y` is closed, convex and has free
disposal, then `Y = {y : p·y ≤ π(p) for all p ≫ 0}`. -/
theorem proposition_5_C_1_iii {Y : Set (Fin L → ℝ)} (hcl : IsClosed Y) (hc : Convex ℝ Y)
    (hfd : FreeDisposal Y) {p₀ : Fin L → ℝ} (hp₀ : StrictlyPositive p₀)
    (hb₀ : BddAbove ((fun y => p₀ ⬝ᵥ y) '' Y)) :
    Y = {y | ∀ p : Fin L → ℝ, StrictlyPositive p → ((p ⬝ᵥ y : ℝ) : EReal) ≤ profitFn Y p} := by
  ext x
  constructor
  · intro hx p _
    exact le_profitFn hx
  · intro hx
    by_contra hxY
    rcases Y.eq_empty_or_nonempty with hY | hne
    · have := hx p₀ hp₀
      rw [hY] at this
      simp [profitFn] at this
    obtain ⟨m, hm⟩ := hb₀
    obtain ⟨q, c, hqx, hqY⟩ := separation_section_3_F hcl hc hxY
    have hb : ∀ y ∈ Y, (-q) ⬝ᵥ y ≤ -c := by
      intro y hy
      rw [neg_dotProduct]
      linarith [hqY y hy]
    have hp0 := nonneg_of_bdd_freeDisposal hne hfd hb
    set δ := (-q) ⬝ᵥ x + c with hδ
    have hδpos : 0 < δ := by rw [hδ, neg_dotProduct]; linarith
    set A := |m - p₀ ⬝ᵥ x| with hA
    set ε := δ / (2 * (δ + A)) with hε
    have hδA : 0 < δ + A := by positivity
    have hεpos : 0 < ε := by positivity
    have hε1 : ε < 1 := by
      rw [hε, div_lt_one (by positivity)]
      have : 0 ≤ A := abs_nonneg _
      linarith
    set p := (1 - ε) • (-q) + ε • p₀ with hp
    have hppos : StrictlyPositive p := by
      intro l
      simp only [hp, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have := hp0 l
      have := hp₀ l
      have : 0 ≤ (1 - ε) * (-q) l := mul_nonneg (by linarith) (hp0 l)
      nlinarith
    have hbound : ∀ y ∈ Y, p ⬝ᵥ y ≤ (1 - ε) * (-c) + ε * m := by
      intro y hy
      simp only [hp, add_dotProduct, smul_dotProduct, smul_eq_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left (hb y hy) (by linarith))
        (mul_le_mul_of_nonneg_left (hm ⟨y, hy, rfl⟩) hεpos.le)
    have h1 := (hx p hppos).trans
      (profitFn_le fun y hy => EReal.coe_le_coe_iff.mpr (hbound y hy))
    have h2 := EReal.coe_le_coe_iff.mp h1
    simp only [hp, add_dotProduct, smul_dotProduct, smul_eq_mul] at h2
    have hkey : ε * (δ + A) < δ := by
      have : ε * (δ + A) = δ / 2 := by
        rw [hε]
        field_simp
      linarith
    have hAge : m - p₀ ⬝ᵥ x ≤ A := le_abs_self _
    have : (1 - ε) * ((-q) ⬝ᵥ x) + ε * (p₀ ⬝ᵥ x) - ((1 - ε) * (-c) + ε * m) =
        (1 - ε) * δ - ε * (m - p₀ ⬝ᵥ x) := by
      rw [hδ]; ring
    nlinarith

/-- **Proposition 5.C.1(iii)** is false as printed (correction): `Y = {y ∈ ℝ² : y₂ ≤ 0}` is
nonempty, closed, convex and has free disposal, `π(p) = +∞` for every `p ≫ 0`, so
`{y : p·y ≤ π(p) for all p ≫ 0} = ℝ² ≠ Y`. -/
theorem proposition_5_C_1_iii_counterexample :
    let Y : Set (Fin 2 → ℝ) := {y | y 1 ≤ 0}
    Y.Nonempty ∧ IsClosed Y ∧ Convex ℝ Y ∧ FreeDisposal Y ∧
      (∀ p : Fin 2 → ℝ, StrictlyPositive p → profitFn Y p = ⊤) ∧
      ![0, 1] ∉ Y ∧
      ∀ p : Fin 2 → ℝ, StrictlyPositive p →
        ((p ⬝ᵥ ![0, 1] : ℝ) : EReal) ≤ profitFn Y p := by
  intro Y
  have htop : ∀ p : Fin 2 → ℝ, StrictlyPositive p → profitFn Y p = ⊤ := by
    intro p hp
    apply profitFn_eq_top
    rw [not_bddAbove_iff]
    intro r
    refine ⟨_, ⟨![(|r| + 1) / p 0, 0], by simp [Y], rfl⟩, ?_⟩
    simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      mul_zero, add_zero]
    rw [mul_div_cancel₀ _ (hp 0).ne']
    linarith [le_abs_self r]
  refine ⟨⟨0, by simp [Y]⟩, isClosed_le (continuous_apply 1) continuous_const, ?_, ?_, htop,
    by simp [Y], fun p hp => by rw [htop p hp]; exact le_top⟩
  · intro y hy y' hy' a b ha hb _
    simp only [Y, Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hy hy' ⊢
    nlinarith
  · intro y hy y' hy'
    exact (hy' 1).trans hy

/-- **Proposition 5.C.1(iv)** (MWG, p. 138). The supply correspondence is homogeneous of degree
zero: `y(αp) = y(p)` for `α > 0`. -/
theorem proposition_5_C_1_iv (Y : Set (Fin L → ℝ)) (p : Fin L → ℝ) {α : ℝ} (hα : 0 < α) :
    supply Y (α • p) = supply Y p := by
  ext y
  simp only [supply, Set.mem_ofPred_eq, smul_dotProduct, smul_eq_mul]
  constructor
  · rintro ⟨hy, h⟩
    exact ⟨hy, fun y' hy' => le_of_mul_le_mul_left (h y' hy') hα⟩
  · rintro ⟨hy, h⟩
    exact ⟨hy, fun y' hy' => mul_le_mul_of_nonneg_left (h y' hy') hα.le⟩

/-- **Proposition 5.C.1(v)** (MWG, p. 138), first part. If `Y` is convex, `y(p)` is convex. -/
theorem proposition_5_C_1_v_convex {Y : Set (Fin L → ℝ)} (hc : Convex ℝ Y) (p : Fin L → ℝ) :
    Convex ℝ (supply Y p) := by
  rintro y ⟨hy, hmax⟩ y' ⟨hy', hmax'⟩ a b ha hb hab
  refine ⟨hc hy hy' ha hb hab, fun z hz => ?_⟩
  rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  have h1 := hmax z hz
  have h2 := hmax' z hz
  calc p ⬝ᵥ z = a * p ⬝ᵥ z + b * p ⬝ᵥ z := by rw [← add_mul, hab, one_mul]
    _ ≤ a * p ⬝ᵥ y + b * p ⬝ᵥ y' :=
        add_le_add (mul_le_mul_of_nonneg_left h1 ha) (mul_le_mul_of_nonneg_left h2 hb)

/-- **Proposition 5.C.1(v)** (MWG, p. 138), second part. If `Y` is strictly convex, `y(p)` has
at most one element (for `p ≠ 0`). -/
theorem proposition_5_C_1_v_strict {Y : Set (Fin L → ℝ)} (hsc : StrictConvex ℝ Y)
    {p : Fin L → ℝ} (hp : p ≠ 0) : (supply Y p).Subsingleton := by
  intro y hy y' hy'
  by_contra hne
  have hint := hsc hy.1 hy'.1 hne (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num)
  set m := (1 / 2 : ℝ) • y + (1 / 2 : ℝ) • y'
  have hnhds : Y ∈ 𝓝 m := mem_interior_iff_mem_nhds.mp hint
  have hg : Continuous fun t : ℝ => m + t • p := by fun_prop
  have hpre := hg.continuousAt (x := 0) (by simpa using hnhds)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hpre
  have hmem : ε / 2 ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith
  have hin : m + (ε / 2) • p ∈ Y := hball hmem
  have hle := hy.2 _ hin
  have hle' := hy'.2 y hy.1
  have hle'' := hy.2 y' hy'.1
  have hpp : 0 < p ⬝ᵥ p := by
    have h0 : 0 ≤ p ⬝ᵥ p := Finset.sum_nonneg fun i _ => mul_self_nonneg (p i)
    exact lt_of_le_of_ne h0 (Ne.symm fun h => hp (dotProduct_self_eq_zero.mp h))
  simp only [m, dotProduct_add, dotProduct_smul, smul_eq_mul] at hle
  nlinarith

/-- **Proposition 5.C.1(vi), Hotelling's lemma** (MWG, p. 138), for closed convex `Y`: if
`y(p̄) = {ȳ}`, then profits are finite near `p̄` and `π` is differentiable at `p̄` with
`∇π(p̄) = ȳ`. Proof: Proposition 3.F.1 (Chapter 3) applied to `-Y`. -/
theorem proposition_5_C_1_vi {Y : Set (Fin L → ℝ)} (hcl : IsClosed Y) (hc : Convex ℝ Y)
    {p y : Fin L → ℝ} (hy : supply Y p = {y}) :
    (∀ᶠ q in 𝓝 p, BddAbove ((fun y => q ⬝ᵥ y) '' Y)) ∧
      HasFDerivAt (profit Y) (dualityDotCLM y) p := by
  have hmem : -y ∈ supportArgmin (-Y) p := by
    have : y ∈ supply Y p := by rw [hy]; rfl
    rw [supply_eq_neg_supportArgmin] at this
    exact this
  have huniq : ∀ x ∈ supportArgmin (-Y) p, x = -y := by
    intro x hx
    have : -x ∈ supply Y p := by
      rw [supply_eq_neg_supportArgmin, Set.mem_neg, neg_neg]
      exact hx
    rw [hy] at this
    rw [← neg_neg x, show -x = y from this]
  have hcl' : IsClosed (-Y) := hcl.neg
  have hc' : Convex ℝ (-Y) := hc.neg
  obtain ⟨hb, hd⟩ := duality_differentiable_of_unique hcl' hc' hmem huniq
  refine ⟨?_, ?_⟩
  · filter_upwards [hb] with q hq
    exact (bddAbove_iff_bddBelow_neg Y q).mpr hq
  · have : profit Y = fun q => -supportFn (-Y) q := funext fun q => profit_eq_neg_supportFn Y q
    rw [this]
    have h2 := hd.neg
    have heq : -dualityDotCLM (-y) = dualityDotCLM (L := L) y := by
      ext q
      simp [dualityDotCLM_apply]
    rwa [heq] at h2

/-- The nonconvex production set `ℝ²_- ∪ {y : y₁ + y₂ ≤ -1}` (closed, free disposal). -/
def hotellingCounterexampleSet : Set (Fin 2 → ℝ) :=
  {y | y ≤ 0} ∪ {y | y 0 + y 1 ≤ -1}

/-- **Proposition 5.C.1(vi)** needs convexity (correction): `Y = ℝ²_- ∪ {y : y₁ + y₂ ≤ -1}` is
nonempty, closed and has free disposal, `y(1, 1) = {0}`, but `π(1 + δ, 1) = +∞` for every
`δ > 0`, so `π` is not finite near `(1, 1)`, let alone differentiable. -/
theorem proposition_5_C_1_vi_nonconvex_counterexample :
    IsClosed hotellingCounterexampleSet ∧ FreeDisposal hotellingCounterexampleSet ∧
      supply hotellingCounterexampleSet ![1, 1] = {0} ∧
      ∀ δ : ℝ, 0 < δ → profitFn hotellingCounterexampleSet ![1 + δ, 1] = ⊤ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (isClosed_le continuous_id continuous_const).union
      (isClosed_le (by fun_prop) continuous_const)
  · rintro y (hy | hy) y' hy'
    · exact Or.inl (hy'.trans hy)
    · right
      simp only [Set.mem_ofPred_eq] at hy ⊢
      linarith [hy' 0, hy' 1]
  · ext y
    simp only [supply, hotellingCounterexampleSet, Set.mem_union, Set.mem_ofPred_eq,
      Set.mem_singleton_iff, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, one_mul]
    constructor
    · rintro ⟨hy, hmax⟩
      have h0 := hmax 0 (Or.inl le_rfl)
      simp only [Pi.zero_apply, add_zero] at h0
      rcases hy with hy | hy
      · funext i
        fin_cases i
        · have h0' : y 0 ≤ 0 := hy 0
          have h1' : y 1 ≤ 0 := hy 1
          simp only [Fin.zero_eta, Fin.isValue, Pi.zero_apply]
          linarith
        · have h0' : y 0 ≤ 0 := hy 0
          have h1' : y 1 ≤ 0 := hy 1
          simp only [Fin.mk_one, Fin.isValue, Pi.zero_apply]
          linarith
      · linarith
    · rintro rfl
      refine ⟨Or.inl le_rfl, fun y' hy' => ?_⟩
      simp only [Pi.zero_apply, add_zero]
      rcases hy' with hy' | hy'
      · have h0' : y' 0 ≤ 0 := hy' 0
        have h1' : y' 1 ≤ 0 := hy' 1
        linarith
      · linarith
  · intro δ hδ
    apply profitFn_eq_top
    rw [not_bddAbove_iff]
    intro r
    set t := (|r| + 2) / δ with ht
    refine ⟨_, ⟨![t, -1 - t], Or.inr (by simp), rfl⟩, ?_⟩
    simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    have : δ * t = |r| + 2 := by rw [ht]; field_simp
    nlinarith [le_abs_self r]

/-- **Section 5.C** (MWG, p. 138), the law of supply (5.C.3): `(p - p')·(y - y') ≥ 0` for
`y ∈ y(p)` and `y' ∈ y(p')`, by the revealed preference argument. -/
theorem law_of_supply {Y : Set (Fin L → ℝ)} {p p' y y' : Fin L → ℝ} (hy : y ∈ supply Y p)
    (hy' : y' ∈ supply Y p') : 0 ≤ (p - p') ⬝ᵥ (y - y') := by
  have h1 := hy.2 y' hy'.1
  have h2 := hy'.2 y hy.1
  rw [sub_dotProduct, dotProduct_sub, dotProduct_sub]
  linarith

/-- **Proposition 5.C.1(vii)** (MWG, p. 138), semidefiniteness, for any `Y`: if `y(·)` is a
selection from the supply correspondence near `p̄` with derivative `Dy` at `p̄`, then
`Dy(p̄)` is positive semidefinite (the law of supply in differential form). -/
theorem proposition_5_C_1_vii_psd {Y : Set (Fin L → ℝ)} {ys : (Fin L → ℝ) → (Fin L → ℝ)}
    {p : Fin L → ℝ} (hys : ∀ᶠ q in 𝓝 p, ys q ∈ supply Y q)
    {D : (Fin L → ℝ) →L[ℝ] (Fin L → ℝ)} (hD : HasFDerivAt ys D p) :
    PosSemidefMWG (jacobian D) := by
  intro z
  rw [jacobian_mulVec]
  set γ : ℝ → Fin L → ℝ := fun t => p + t • z with hγ
  have hγd : HasDerivAt γ z 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const z).const_add p
    simp only [id, one_smul] at h
    exact h
  have hγ0 : γ 0 = p := by simp [γ]
  have hcomp : HasDerivAt (fun t => ys (γ t)) (D z) 0 := by
    rw [← hγ0] at hD
    exact hD.comp_hasDerivAt 0 hγd
  have hg : HasDerivAt (fun t => ∑ l, z l * ys (γ t) l) (∑ l, z l * D z l) 0 :=
    HasDerivAt.fun_sum fun l _ => (hasDerivAt_pi.mp hcomp l).const_mul (z l)
  rw [← neg_nonpos]
  apply hasDerivAt_nonpos_of_right_le hg.neg
  have hcont : Tendsto γ (𝓝[>] 0) (𝓝 p) := by
    rw [← hγ0]
    exact hγd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  filter_upwards [hcont.eventually hys, self_mem_nhdsWithin] with t ht htpos
  have hlaw := law_of_supply ht hys.self_of_nhds
  have hsub : γ t - p = t • z := by simp [γ]
  rw [hsub, smul_dotProduct, smul_eq_mul, dotProduct_sub] at hlaw
  have : 0 ≤ z ⬝ᵥ ys (γ t) - z ⬝ᵥ ys p := by
    by_contra h
    rw [not_le] at h
    have := mul_neg_of_pos_of_neg (show (0 : ℝ) < t from htpos) h
    linarith
  simp only [dotProduct] at this
  simp only [Pi.neg_apply, hγ0]
  linarith

/-- **Proposition 5.C.1(vii)** (MWG, p. 138), `Dy(p̄)p̄ = 0`, for any `Y`: if `y(q) = {ys q}` for
`q` near `p̄` and `ys` has derivative `Dy` at `p̄`, then `Dy(p̄)p̄ = 0` (from (iv)). -/
theorem proposition_5_C_1_vii_euler {Y : Set (Fin L → ℝ)} {ys : (Fin L → ℝ) → (Fin L → ℝ)}
    {p : Fin L → ℝ} (hys : ∀ᶠ q in 𝓝 p, supply Y q = {ys q})
    {D : (Fin L → ℝ) →L[ℝ] (Fin L → ℝ)} (hD : HasFDerivAt ys D p) : D p = 0 := by
  set γ : ℝ → Fin L → ℝ := fun t => p + t • p with hγ
  have hγd : HasDerivAt γ p 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const p).const_add p
    simp only [id, one_smul] at h
    exact h
  have hγ0 : γ 0 = p := by simp [γ]
  have hcomp : HasDerivAt (fun t => ys (γ t)) (D p) 0 := by
    have hD' := hD
    rw [← hγ0] at hD'
    exact hD'.comp_hasDerivAt 0 hγd
  have hcont : Tendsto γ (𝓝 0) (𝓝 p) := by
    rw [← hγ0]
    exact hγd.continuousAt.tendsto
  have hconst : (fun t => ys (γ t)) =ᶠ[𝓝 0] fun _ => ys p := by
    have : ∀ᶠ t : ℝ in 𝓝 0, -1 < t := lt_mem_nhds (by norm_num)
    filter_upwards [this, hcont.eventually hys] with t ht hst
    have hpos : 0 < 1 + t := by linarith
    have hγt : γ t = (1 + t) • p := by simp [γ, add_smul]
    have h1 := hys.self_of_nhds
    rw [hγt, proposition_5_C_1_iv Y p hpos, h1] at hst
    rw [hγt]
    have : ys ((1 + t) • p) ∈ ({ys p} : Set (Fin L → ℝ)) := by rw [hst]; rfl
    exact this
  have h0 : HasDerivAt (fun t => ys (γ t)) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (ys p)).congr_of_eventuallyEq hconst
  exact hcomp.unique h0

/-- **Proposition 5.C.1(vii)** (MWG, p. 138), `Dy(p̄) = D²π(p̄)` and symmetry, for closed convex
`Y`: if `y(q) = {ys q}` for `q` near `p̄` and `ys` has derivative `Dy` at `p̄`, then `∇π = ys`
near `p̄`, the Hessian of `π` at `p̄` is the Jacobian of `ys`, and it is symmetric. -/
theorem proposition_5_C_1_vii {Y : Set (Fin L → ℝ)} (hcl : IsClosed Y) (hc : Convex ℝ Y)
    {ys : (Fin L → ℝ) → (Fin L → ℝ)} {p : Fin L → ℝ} (hys : ∀ᶠ q in 𝓝 p, supply Y q = {ys q})
    {D : (Fin L → ℝ) →L[ℝ] (Fin L → ℝ)} (hD : HasFDerivAt ys D p) :
    hessianMatrix (profit Y) p = jacobian D ∧
      (∀ i j, jacobian D i j = jacobian D j i) ∧ PosSemidefMWG (jacobian D) ∧ D p = 0 := by
  have hgrad : ∀ᶠ q in 𝓝 p, HasFDerivAt (profit Y) (dualityDotCLM (ys q)) q := by
    filter_upwards [hys] with q hq
    exact (proposition_5_C_1_vi hcl hc hq).2
  refine ⟨?_, ?_, ?_, proposition_5_C_1_vii_euler hys hD⟩
  · have heq : (fun q => gradientVec (fderiv ℝ (profit Y) q)) =ᶠ[𝓝 p] ys := by
      filter_upwards [hgrad] with q hq
      rw [hq.fderiv, gradientVec_dualityDotCLM]
    rw [hessianMatrix, (hD.congr_of_eventuallyEq heq).fderiv]
  · have h1 : ∀ᶠ q in 𝓝 p, HasFDerivAt (profit Y) (dualityDotLin (ys q)) q := by
      filter_upwards [hgrad] with q hq
      rwa [dualityDotLin_apply]
    have h2 : HasFDerivAt (fun q => dualityDotLin (ys q)) (dualityDotLin.comp D) p :=
      dualityDotLin.hasFDerivAt.comp p hD
    intro i j
    have := second_derivative_symmetric_of_eventually h1 h2 (Pi.single j 1) (Pi.single i 1)
    simp only [ContinuousLinearMap.comp_apply, dualityDotLin_apply, dualityDotCLM_apply,
      dotProduct_single, mul_one] at this
    simpa [jacobian] using this
  · exact proposition_5_C_1_vii_psd (hys.mono fun q hq => by rw [hq]; rfl) hD

end MWG.Production

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# First-order conditions for profit maximization (MWG Section 5.C, pp. 136-137)

* (5.C.1): if `y* ∈ y(p)` for `Y = {y : F(y) ≤ 0}` with `F` differentiable at `y*` and
  `∇F(y*) ≠ 0`, then `p = λ∇F(y*)` for some `λ ≥ 0` (`foc_5_C_1`), and
  `p_l/p_k = MRT_{lk}(y*)` (`foc_5_C_1_ratio`). Sufficiency for convex `Y` (p. 137):
  `foc_5_C_1_sufficient`.
* (5.C.2): the single-output conditions `p ∂f(z*)/∂z_l ≤ w_l`, with equality if `z*_l > 0`
  (`foc_5_C_2`), `MRTS_{lk} = w_l/w_k` for interior inputs, and sufficiency for concave `f`
  (`foc_5_C_2_sufficient`).

Departure: (5.C.1) needs the constraint qualification `∇F(y*) ≠ 0`, which the book does not
state; `foc_5_C_1_needs_cq` is a transformation function `F(y) = (y₁ + y₂)³` with
`∇F(0) = 0` and `0 ∈ y(1, 1)`.
-/

namespace MWG.Production

open MWG.ClassicalDemand MWG.ConsumerChoice Filter Topology

variable {L : ℕ}

/-- A real function with negative derivative at `0` is below `g 0` just to the right of `0`. -/
theorem eventually_lt_of_hasDerivAt_neg {g : ℝ → ℝ} {d : ℝ} (hg : HasDerivAt g d 0)
    (hd : d < 0) : ∀ᶠ t in 𝓝[>] (0 : ℝ), g t < g 0 := by
  filter_upwards [hg.tendsto_slope_zero_right.eventually (eventually_lt_nhds hd),
    self_mem_nhdsWithin] with t ht htpos
  rw [zero_add, smul_eq_mul] at ht
  have htpos' : (0 : ℝ) < t := htpos
  have : g t - g 0 < 0 := by
    by_contra h
    rw [not_lt] at h
    have := mul_nonneg (inv_nonneg.mpr htpos'.le) h
    linarith
  linarith

/-- If `p` is not a nonnegative multiple of `g ≠ 0`, some direction `d` has `g·d < 0 < p·d`. -/
theorem exists_dir_of_not_nonneg_multiple {g p : Fin L → ℝ} (hg : g ≠ 0)
    (h : ¬ ∃ lam : ℝ, 0 ≤ lam ∧ p = lam • g) : ∃ d, g ⬝ᵥ d < 0 ∧ 0 < p ⬝ᵥ d := by
  have hgg : 0 < g ⬝ᵥ g := by
    have h0 : 0 ≤ g ⬝ᵥ g := Finset.sum_nonneg fun i _ => mul_self_nonneg (g i)
    exact lt_of_le_of_ne h0 (Ne.symm fun h => hg (dotProduct_self_eq_zero.mp h))
  set μ := (p ⬝ᵥ g) / (g ⬝ᵥ g) with hμ
  set r := p - μ • g with hr
  have hgr : g ⬝ᵥ r = 0 := by
    rw [hr, dotProduct_sub, dotProduct_smul, smul_eq_mul, hμ, dotProduct_comm g p]
    field_simp
    ring
  have hpr : p ⬝ᵥ r = r ⬝ᵥ r := by
    have : p = r + μ • g := by rw [hr]; abel
    conv_lhs => rw [this]
    rw [add_dotProduct, smul_dotProduct, hgr, smul_zero, add_zero]
  by_cases hr0 : r = 0
  · have hp : p = μ • g := by rw [← sub_eq_zero, ← hr, hr0]
    have hμneg : μ < 0 := by
      by_contra hμ0
      exact h ⟨μ, not_lt.mp hμ0, hp⟩
    refine ⟨-g, by rw [dotProduct_neg]; linarith, ?_⟩
    rw [hp, dotProduct_neg, smul_dotProduct, smul_eq_mul]
    nlinarith
  · have hrr : 0 < r ⬝ᵥ r := by
      have h0 : 0 ≤ r ⬝ᵥ r := Finset.sum_nonneg fun i _ => mul_self_nonneg (r i)
      exact lt_of_le_of_ne h0 (Ne.symm fun h => hr0 (dotProduct_self_eq_zero.mp h))
    set s := (r ⬝ᵥ r) / (|p ⬝ᵥ g| + 1) with hs
    have hspos : 0 < s := by positivity
    refine ⟨r - s • g, ?_, ?_⟩
    · rw [dotProduct_sub, hgr, dotProduct_smul, smul_eq_mul]
      nlinarith
    · rw [dotProduct_sub, hpr, dotProduct_smul, smul_eq_mul]
      have h1 : s * (|p ⬝ᵥ g| + 1) = r ⬝ᵥ r := by rw [hs]; field_simp
      nlinarith [le_abs_self (p ⬝ᵥ g)]

/-- **Section 5.C** (MWG, p. 136), condition (5.C.1). Let `Y = {y : F(y) ≤ 0}`, `y* ∈ y(p)`, and
`F` differentiable at `y*` with `∇F(y*) ≠ 0`. Then `p = λ∇F(y*)` for some `λ ≥ 0`. -/
theorem foc_5_C_1 {F : (Fin L → ℝ) → ℝ} {p y : Fin L → ℝ}
    (hy : y ∈ supply {y | F y ≤ 0} p) (hF : DifferentiableAt ℝ F y)
    (hcq : gradientVec (fderiv ℝ F y) ≠ 0) :
    ∃ lam : ℝ, 0 ≤ lam ∧ p = lam • gradientVec (fderiv ℝ F y) := by
  by_contra h
  obtain ⟨d, hgd, hpd⟩ := exists_dir_of_not_nonneg_multiple hcq h
  have hline := mc_line_hasDerivAt hF.hasFDerivAt d
  rw [fderiv_apply_eq_gradient_dot] at hline
  have hev := eventually_lt_of_hasDerivAt_neg hline hgd
  obtain ⟨t, ht, htpos⟩ := (hev.and self_mem_nhdsWithin).exists
  simp only [zero_smul, add_zero] at ht
  have hmem : y + t • d ∈ {y | F y ≤ 0} := le_of_lt (ht.trans_le hy.1)
  have := hy.2 _ hmem
  rw [dotProduct_add, dotProduct_smul, smul_eq_mul] at this
  have htpos' : (0 : ℝ) < t := htpos
  nlinarith

/-- **Section 5.C** (MWG, p. 137). Under (5.C.1) with `p ≫ 0` and `∂F(y*)/∂y_k ≠ 0`:
`p_l/p_k = MRT_{lk}(y*)`. -/
theorem foc_5_C_1_ratio {F : (Fin L → ℝ) → ℝ} {p y : Fin L → ℝ} (hp : StrictlyPositive p)
    (hy : y ∈ supply {y | F y ≤ 0} p) (hF : DifferentiableAt ℝ F y)
    (hcq : gradientVec (fderiv ℝ F y) ≠ 0) (l k : Fin L) :
    p l / p k = MRT F y l k := by
  obtain ⟨lam, _, hlam⟩ := foc_5_C_1 hy hF hcq
  have hl : p l = lam * partialAt F y l := by
    have := congrFun hlam l
    simpa [gradientVec, partialAt] using this
  have hk : p k = lam * partialAt F y k := by
    have := congrFun hlam k
    simpa [gradientVec, partialAt] using this
  have hlam0 : lam ≠ 0 := by
    intro h0
    have := hp k
    rw [hk, h0, zero_mul] at this
    exact lt_irrefl 0 this
  rw [hl, hk, MRT, mul_div_mul_left _ _ hlam0]

/-- **Section 5.C** (MWG, p. 137), sufficiency of (5.C.1) for convex `Y = {y : F(y) ≤ 0}`: if
`F(y*) = 0`, `F` is differentiable at `y*` and `p = λ∇F(y*)` with `λ ≥ 0`, then `y* ∈ y(p)`. -/
theorem foc_5_C_1_sufficient {F : (Fin L → ℝ) → ℝ} (hc : Convex ℝ {y | F y ≤ 0})
    {p y : Fin L → ℝ} (hy0 : F y = 0) (hF : DifferentiableAt ℝ F y) {lam : ℝ}
    (hlam : 0 ≤ lam) (hp : p = lam • gradientVec (fderiv ℝ F y)) :
    y ∈ supply {y | F y ≤ 0} p := by
  refine ⟨le_of_eq hy0, fun y' hy' => ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  rcases hlam.lt_or_eq with hpos | hzero
  · have hgd : 0 < gradientVec (fderiv ℝ F y) ⬝ᵥ (y' - y) := by
      have : 0 < p ⬝ᵥ (y' - y) := by rw [dotProduct_sub]; linarith
      rw [hp, smul_dotProduct, smul_eq_mul] at this
      exact pos_of_mul_pos_right this hpos.le
    have hline := mc_line_hasDerivAt hF.hasFDerivAt (y' - y)
    rw [fderiv_apply_eq_gradient_dot] at hline
    have hev := eventually_lt_of_hasDerivAt_neg hline.neg (neg_lt_zero.mpr hgd)
    have hev2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 := by
      filter_upwards [nhdsWithin_le_nhds (eventually_lt_nhds one_pos)] with t ht
      exact ht
    obtain ⟨t, ⟨ht, ht1⟩, htpos⟩ := ((hev.and hev2).and self_mem_nhdsWithin).exists
    have ht0 : 0 < F (y + t • (y' - y)) := by simpa [hy0] using ht
    have htpos' : (0 : ℝ) < t := htpos
    have hmem : y + t • (y' - y) ∈ {y | F y ≤ 0} := by
      have := hc (show y ∈ {y | F y ≤ 0} from le_of_eq hy0) hy' (by linarith : (0 : ℝ) ≤ 1 - t)
        htpos'.le (by ring)
      have heq : (1 - t) • y + t • y' = y + t • (y' - y) := by module
      rwa [heq] at this
    have : F (y + t • (y' - y)) ≤ 0 := hmem
    linarith
  · rw [← hzero, zero_smul] at hp
    rw [hp, zero_dotProduct, zero_dotProduct] at hlt
    exact lt_irrefl 0 hlt

/-- The transformation function `F(y) = (y₁ + y₂)³` of the half-plane `{y₁ + y₂ ≤ 0}`. -/
def cubeTransformation (y : Fin 2 → ℝ) : ℝ := (y 0 + y 1) ^ 3

/-- **(5.C.1)** needs a constraint qualification (correction): `F(y) = (y₁ + y₂)³` is a
transformation function for `Y = {y₁ + y₂ ≤ 0}`, differentiable with `∇F(0) = 0`, and
`0 ∈ y(1, 1)`, but `(1, 1) ≠ λ∇F(0)` for every `λ`. -/
theorem foc_5_C_1_needs_cq :
    IsTransformationFunction cubeTransformation {y | cubeTransformation y ≤ 0} ∧
      DifferentiableAt ℝ cubeTransformation 0 ∧
      gradientVec (fderiv ℝ cubeTransformation 0) = 0 ∧
      (0 : Fin 2 → ℝ) ∈ supply {y | cubeTransformation y ≤ 0} ![1, 1] ∧
      ¬ ∃ lam : ℝ, (![1, 1] : Fin 2 → ℝ) =
        lam • gradientVec (fderiv ℝ cubeTransformation 0) := by
  have hiff : ∀ y : Fin 2 → ℝ, cubeTransformation y ≤ 0 ↔ y 0 + y 1 ≤ 0 := fun y =>
    Odd.pow_nonpos_iff (by decide)
  have hset : {y | cubeTransformation y ≤ 0} = {y : Fin 2 → ℝ | y 0 + y 1 ≤ 0} := by
    ext y
    exact hiff y
  have a := hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) (0 : Fin 2 → ℝ)
  have b := hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) (0 : Fin 2 → ℝ)
  have h2 := (a.fun_add b).pow 3
  have hcube : cubeTransformation = fun x : Fin 2 → ℝ => (x 0 + x 1) ^ 3 := rfl
  have hgrad : gradientVec (fderiv ℝ cubeTransformation 0) = 0 := by
    rw [hcube, h2.fderiv]
    funext i
    simp [gradientVec]
  refine ⟨⟨rfl, fun y => ?_⟩, by rw [hcube]; exact h2.differentiableAt, hgrad, ?_, ?_⟩
  · rw [hset, ← isTransformationFunction_halfPlane.2 y, cubeTransformation]
    exact pow_eq_zero_iff (by norm_num)
  · refine ⟨show cubeTransformation 0 ≤ 0 by simp [cubeTransformation], fun y' hy' => ?_⟩
    have := (hiff y').mp hy'
    simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_mul,
      Pi.zero_apply, mul_zero, add_zero]
    linarith
  · rintro ⟨lam, h⟩
    rw [hgrad, smul_zero] at h
    have := congrFun h 0
    simp at this

/-! ### The single-output case (5.C.2) -/

/-- **Section 5.C** (MWG, p. 137), condition (5.C.2). If `z* ≥ 0` maximizes `p f(z) - w·z` over
`z ≥ 0` and `f` is differentiable at `z*`, then `p ∂f(z*)/∂z_l ≤ w_l` for every input, with
equality when `z*_l > 0`; in matrix form `p∇f(z*) ≤ w` and `[p∇f(z*) - w]·z* = 0`. -/
theorem foc_5_C_2 {n : ℕ} {f : (Fin n → ℝ) → ℝ} {p : ℝ} {w z : Fin n → ℝ} (hz : 0 ≤ z)
    (hopt : ∀ z', 0 ≤ z' → p * f z' - w ⬝ᵥ z' ≤ p * f z - w ⬝ᵥ z)
    (hf : DifferentiableAt ℝ f z) :
    (∀ l, p * partialF f z l ≤ w l) ∧ (∀ l, 0 < z l → p * partialF f z l = w l) ∧
      (fun l => p * partialF f z l - w l) ⬝ᵥ z = 0 := by
  have hline : ∀ l, HasDerivAt (fun t : ℝ => p * f (z + t • Pi.single l 1) -
      w ⬝ᵥ (z + t • Pi.single l 1)) (p * partialF f z l - w l) 0 := by
    intro l
    have h1 := (mc_line_hasDerivAt hf.hasFDerivAt (Pi.single l 1)).const_mul p
    have h2 : HasDerivAt (fun t : ℝ => w ⬝ᵥ (z + t • Pi.single l 1)) (w l) 0 := by
      have : (fun t : ℝ => w ⬝ᵥ (z + t • Pi.single l 1)) = fun t => w ⬝ᵥ z + t * w l := by
        funext t
        rw [dotProduct_add, dotProduct_smul, dotProduct_single, mul_one, smul_eq_mul]
      rw [this]
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (w l)).const_add (w ⬝ᵥ z)
    exact h1.sub h2
  have hle : ∀ l, p * partialF f z l ≤ w l := by
    intro l
    have := hasDerivAt_nonpos_of_right_le (hline l) ?_
    · linarith
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : (0 : ℝ) < t := ht
    simp only [zero_smul, add_zero]
    apply hopt
    exact add_nonneg hz (smul_nonneg ht'.le (Pi.single_nonneg.mpr zero_le_one))
  have heq : ∀ l, 0 < z l → p * partialF f z l = w l := by
    intro l hzl
    apply le_antisymm (hle l)
    have hl' := hline l
    rw [← neg_zero] at hl'
    have hneg := hl'.comp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))
    simp only [mul_neg, mul_one] at hneg
    have := hasDerivAt_nonpos_of_right_le hneg ?_
    · linarith
    have hI : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < z l :=
      nhdsWithin_le_nhds (eventually_lt_nhds hzl)
    filter_upwards [self_mem_nhdsWithin, hI] with t ht htz
    have ht' : (0 : ℝ) < t := ht
    simp only [Function.comp_apply, neg_zero, zero_smul, add_zero]
    apply hopt
    intro i
    by_cases hi : i = l
    · subst hi
      simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one,
        Pi.zero_apply]
      linarith
    · simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne hi, smul_eq_mul, mul_zero,
        add_zero, Pi.zero_apply]
      exact hz i
  refine ⟨hle, heq, ?_⟩
  apply Finset.sum_eq_zero
  intro l _
  change (p * partialF f z l - w l) * z l = 0
  have hzl : (0 : ℝ) ≤ z l := hz l
  rcases hzl.lt_or_eq with hpos | hzero
  · rw [heq l hpos, sub_self, zero_mul]
  · rw [← hzero, mul_zero]

/-- **Section 5.C** (MWG, p. 137). Under (5.C.2) with `p > 0`, two inputs used in positive amounts
have `MRTS_{lk}(z*) = w_l/w_k` (for `w_k ≠ 0`). -/
theorem foc_5_C_2_mrts {n : ℕ} {f : (Fin n → ℝ) → ℝ} {p : ℝ} {w z : Fin n → ℝ} (hz : 0 ≤ z)
    (hopt : ∀ z', 0 ≤ z' → p * f z' - w ⬝ᵥ z' ≤ p * f z - w ⬝ᵥ z)
    (hf : DifferentiableAt ℝ f z) (hp : 0 < p) {l k : Fin n} (hl : 0 < z l) (hk : 0 < z k) :
    MRTS f z l k = w l / w k := by
  obtain ⟨-, heq, -⟩ := foc_5_C_2 hz hopt hf
  rw [MRTS, ← heq l hl, ← heq k hk, mul_div_mul_left _ _ hp.ne']

/-- A concave function lies below its tangent plane at a point of differentiability. -/
theorem concave_le_tangent {n : ℕ} {A : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (hc : ConcaveOn ℝ A f) {x y : Fin n → ℝ} (hx : x ∈ A) (hy : y ∈ A)
    (hf : DifferentiableAt ℝ f x) : f y ≤ f x + fderiv ℝ f x (y - x) := by
  have hd := mc_line_hasDerivAt hf.hasFDerivAt (y - x)
  have key : f y - f x ≤ fderiv ℝ f x (y - x) := by
    apply mc_le_deriv_of_slope hd
    intro t ht0 ht1
    have hconc := hc.2 hy hx ht0.le (by linarith : (0 : ℝ) ≤ 1 - t) (by ring)
    have heq : t • y + (1 - t) • x = x + t • (y - x) := by module
    rw [heq, smul_eq_mul, smul_eq_mul] at hconc
    simp only [zero_smul, add_zero]
    rw [le_div_iff₀ ht0]
    linarith
  linarith

/-- **Section 5.C** (MWG, p. 137), sufficiency of (5.C.2): if `f` is concave on `ℝ^{L-1}_+`
(equivalently `Y` is convex, Exercise 5.B.3), differentiable at `z* ≥ 0`, and (5.C.2) holds,
then `z*` maximizes `p f(z) - w·z` over `z ≥ 0` (for `p ≥ 0`). -/
theorem foc_5_C_2_sufficient {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hc : ConcaveOn ℝ {z : Fin n → ℝ | 0 ≤ z} f) {p : ℝ} (hp : 0 ≤ p) {w z : Fin n → ℝ}
    (hz : 0 ≤ z) (hf : DifferentiableAt ℝ f z) (hle : ∀ l, p * partialF f z l ≤ w l)
    (hcs : (fun l => p * partialF f z l - w l) ⬝ᵥ z = 0) :
    ∀ z', 0 ≤ z' → p * f z' - w ⬝ᵥ z' ≤ p * f z - w ⬝ᵥ z := by
  intro z' hz'
  have htan := concave_le_tangent hc hz hz' hf
  have hgrad : fderiv ℝ f z (z' - z) = (fun l => partialF f z l) ⬝ᵥ (z' - z) := by
    rw [fderiv_apply_eq_gradient_dot]
    rfl
  rw [hgrad] at htan
  have h1 : (fun l => p * partialF f z l - w l) ⬝ᵥ z' ≤ 0 := by
    apply Finset.sum_nonpos
    intro l _
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith [hle l]) (hz' l)
  have h2 : p * ((fun l => partialF f z l) ⬝ᵥ (z' - z)) =
      (fun l => p * partialF f z l - w l) ⬝ᵥ z' - (fun l => p * partialF f z l - w l) ⬝ᵥ z
        + w ⬝ᵥ z' - w ⬝ᵥ z := by
    simp only [dotProduct, ← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [Pi.sub_apply]
    ring
  have h3 := mul_le_mul_of_nonneg_left htan hp
  rw [mul_add, h2, hcs] at h3
  linarith

end MWG.Production

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The cost minimization problem (MWG Section 5.C, pp. 139-142)

For a single-output technology with production function `f`, the input requirement set is
`V(q) = {z ≥ 0 : f(z) ≥ q}`; the cost function `c(w, q)` is Chapter 3's support function of
`V(q)` and the conditional factor demand `z(w, q)` is its set of minimizers (the book's remark
on p. 140 that the CMP is the EMP with `f` in place of `u`).

Most results are proved for an arbitrary input requirement set `V ⊆ ℝ^n_+` (`vcost_*`), so
that they apply to the single-output case (**Proposition 5.C.2**) and to multiple outputs
(**Exercise 5.C.4**).

* **Proposition 5.C.2** (i)-(ix); (vi), Shephard's lemma, without convexity: for closed
  `V(q)` and `w̄ ≫ 0` a unique minimizer gives differentiability (`vcost_shephard`), by a
  Danskin-type argument (`supportFn_hasFDerivAt_of_compact`).
* **Exercises 5.C.3** and **5.C.5** (quasiconcavity suffices for (iii); quasiconcavity with
  increasing returns).
-/

namespace MWG.Production

open MWG.ClassicalDemand MWG.ConsumerChoice Filter Topology

variable {n : ℕ}

/-- **Section 5.C** (MWG, p. 139). The input requirement set `V(q) = {z ≥ 0 : f(z) ≥ q}`, the
constraint set of the cost minimization problem (CMP). -/
def inputReq (f : (Fin n → ℝ) → ℝ) (q : ℝ) : Set (Fin n → ℝ) := {z | 0 ≤ z ∧ q ≤ f z}

/-- **Section 5.C** (MWG, p. 139). The cost function `c(w, q) = min {w·z : z ≥ 0, f(z) ≥ q}`,
the support function of `V(q)` (real-valued; it is the minimum when `V(q) ≠ ∅` and `w ≥ 0`). -/
noncomputable def costFn (f : (Fin n → ℝ) → ℝ) (w : Fin n → ℝ) (q : ℝ) : ℝ :=
  supportFn (inputReq f q) w

/-- The cost function with values in `[-∞, +∞]`: `+∞` when `q` cannot be produced. -/
noncomputable def costFnE (f : (Fin n → ℝ) → ℝ) (w : Fin n → ℝ) (q : ℝ) : EReal :=
  supportFnE (inputReq f q) w

/-- **Section 5.C** (MWG, p. 139). The conditional factor demand correspondence `z(w, q)`. -/
def condDemand (f : (Fin n → ℝ) → ℝ) (w : Fin n → ℝ) (q : ℝ) : Set (Fin n → ℝ) :=
  supportArgmin (inputReq f q) w

theorem inputReq_subset_nonneg (f : (Fin n → ℝ) → ℝ) (q : ℝ) :
    inputReq f q ⊆ {z | 0 ≤ z} := fun _ hz => hz.1

theorem dot_nonneg_of_nonneg {w z : Fin n → ℝ} (hw : 0 ≤ w) (hz : 0 ≤ z) : 0 ≤ w ⬝ᵥ z :=
  Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (hz i)

/-- Costs are bounded below by `0` on `V ⊆ ℝ^n_+` for `w ≥ 0`. -/
theorem bddBelow_of_subset_nonneg {V : Set (Fin n → ℝ)} (hV : V ⊆ {z | 0 ≤ z})
    {w : Fin n → ℝ} (hw : 0 ≤ w) : BddBelow ((fun z => w ⬝ᵥ z) '' V) :=
  ⟨0, by rintro _ ⟨z, hz, rfl⟩; exact dot_nonneg_of_nonneg hw (hV hz)⟩

/-! ### Results for an arbitrary input requirement set `V ⊆ ℝ^n_+` -/

/-- Homogeneity of degree one in `w`. -/
theorem vcost_smul (V : Set (Fin n → ℝ)) (w : Fin n → ℝ) {α : ℝ} (hα : 0 ≤ α) :
    supportFn V (α • w) = α * supportFn V w :=
  supportFn_smul V w hα

/-- Monotonicity in the requirement: a smaller `V` costs more. -/
theorem vcost_mono {V V' : Set (Fin n → ℝ)} (hV : V ⊆ {z | 0 ≤ z}) (hsub : V' ⊆ V)
    (hne : V'.Nonempty) {w : Fin n → ℝ} (hw : 0 ≤ w) : supportFn V w ≤ supportFn V' w :=
  csInf_le_csInf (bddBelow_of_subset_nonneg hV hw) (hne.image _) (Set.image_mono hsub)

/-- Concavity in `w` on `ℝ^n_+`. -/
theorem vcost_concaveOn {V : Set (Fin n → ℝ)} (hV : V ⊆ {z | 0 ≤ z}) (hne : V.Nonempty) :
    ConcaveOn ℝ {w : Fin n → ℝ | 0 ≤ w} (supportFn V) :=
  (supportFn_concaveOn hne).subset (fun _ hw => bddBelow_of_subset_nonneg hV hw)
    (fun x hx y hy a b ha hb _ =>
      show 0 ≤ a • x + b • y from add_nonneg (smul_nonneg ha hx) (smul_nonneg hb hy))

/-- Duality for input requirement sets: if `V ⊆ ℝ^n_+` is closed, convex and upward closed (free
disposal of inputs), then `z ∈ V` iff `w·z ≥ μ_V(w)` for every `w ≫ 0`. -/
theorem vcost_iii {V : Set (Fin n → ℝ)} (hcl : IsClosed V) (hc : Convex ℝ V)
    (hup : ∀ z ∈ V, ∀ z', z ≤ z' → z' ∈ V) (hV : V ⊆ {z | 0 ≤ z}) (z : Fin n → ℝ) :
    z ∈ V ↔ ∀ w : Fin n → ℝ, StrictlyPositive w → supportFnE V w ≤ ((w ⬝ᵥ z : ℝ) : EReal) := by
  constructor
  · intro hz w _
    exact iInf₂_le z hz
  · intro h
    by_contra hz
    rcases V.eq_empty_or_nonempty with hV0 | hne
    · have := h 1 (fun _ => one_pos)
      rw [hV0] at this
      simp [supportFnE] at this
    obtain ⟨q, c, hqz, hqV⟩ := separation_section_3_F hcl hc hz
    have hq0 : 0 ≤ q := by
      intro l
      by_contra hl0
      have hl : q l < 0 := not_le.mp hl0
      obtain ⟨v, hv⟩ := hne
      set t := (|c| + |q ⬝ᵥ v| + 1) / (-q l) with ht
      have htpos : 0 ≤ t := div_nonneg (by positivity) (by linarith)
      have hmem : v + t • Pi.single l 1 ∈ V :=
        hup v hv _ (le_add_of_nonneg_right (smul_nonneg htpos (Pi.single_nonneg.mpr zero_le_one)))
      have := hqV _ hmem
      rw [dotProduct_add, dotProduct_smul, dotProduct_single, mul_one, smul_eq_mul] at this
      have h2 : t * q l = -(|c| + |q ⬝ᵥ v| + 1) := by
        rw [ht, div_mul_eq_mul_div, div_neg, mul_div_assoc, div_self hl.ne, mul_one]
      rw [h2] at this
      linarith [neg_abs_le c, le_abs_self (q ⬝ᵥ v)]
    set s := ∑ i, |z i| with hs
    set ε := (c - q ⬝ᵥ z) / (2 * (s + 1)) with hε
    have hεpos : 0 < ε := div_pos (by linarith) (by positivity)
    set w := q + ε • (1 : Fin n → ℝ) with hw
    have hwpos : StrictlyPositive w := fun l => by
      simp only [hw, Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
      have hql : 0 ≤ q l := hq0 l
      linarith
    have hlow : (c : EReal) ≤ supportFnE V w := by
      refine le_iInf₂ fun v hv => EReal.coe_le_coe_iff.mpr ?_
      have h1 := hqV v hv
      have h2 : 0 ≤ ε • (1 : Fin n → ℝ) ⬝ᵥ v :=
        dot_nonneg_of_nonneg (smul_nonneg hεpos.le (fun _ => zero_le_one)) (hV hv)
      rw [hw, add_dotProduct]
      linarith
    have hup' := hlow.trans (h w hwpos)
    have h3 := EReal.coe_le_coe_iff.mp hup'
    rw [hw, add_dotProduct, smul_dotProduct, smul_eq_mul] at h3
    have h4 : (1 : Fin n → ℝ) ⬝ᵥ z ≤ s := by
      simp only [dotProduct, Pi.one_apply, one_mul, hs]
      exact Finset.sum_le_sum fun i _ => le_abs_self (z i)
    have hs0 : 0 ≤ s := Finset.sum_nonneg fun i _ => abs_nonneg (z i)
    have h5 : ε * (s + 1) = (c - q ⬝ᵥ z) / 2 := by
      rw [hε]
      field_simp
    nlinarith

/-- Homogeneity of degree zero of the minimizers in `w`. -/
theorem vdemand_smul (V : Set (Fin n → ℝ)) (w : Fin n → ℝ) {α : ℝ} (hα : 0 < α) :
    supportArgmin V (α • w) = supportArgmin V w := by
  ext z
  simp only [supportArgmin, Set.mem_ofPred_eq, smul_dotProduct, smul_eq_mul]
  constructor
  · rintro ⟨hz, h⟩
    exact ⟨hz, fun y hy => le_of_mul_le_mul_left (h y hy) hα⟩
  · rintro ⟨hz, h⟩
    exact ⟨hz, fun y hy => mul_le_mul_of_nonneg_left (h y hy) hα.le⟩

/-- Convexity of the set of minimizers for convex `V`. -/
theorem vdemand_convex {V : Set (Fin n → ℝ)} (hc : Convex ℝ V) (w : Fin n → ℝ) :
    Convex ℝ (supportArgmin V w) := by
  rintro y ⟨hy, hmin⟩ y' ⟨hy', hmin'⟩ a b ha hb hab
  refine ⟨hc hy hy' ha hb hab, fun z hz => ?_⟩
  rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  have h1 := hmin z hz
  have h2 := hmin' z hz
  calc a * w ⬝ᵥ y + b * w ⬝ᵥ y' ≤ a * w ⬝ᵥ z + b * w ⬝ᵥ z :=
        add_le_add (mul_le_mul_of_nonneg_left h1 ha) (mul_le_mul_of_nonneg_left h2 hb)
    _ = w ⬝ᵥ z := by rw [← add_mul, hab, one_mul]

/-- At most one minimizer for strictly convex `V` and `w ≠ 0`. -/
theorem vdemand_strict {V : Set (Fin n → ℝ)} (hsc : StrictConvex ℝ V) {w : Fin n → ℝ}
    (hw : w ≠ 0) : (supportArgmin V w).Subsingleton := by
  intro y hy y' hy'
  by_contra hne
  have hint := hsc hy.1 hy'.1 hne (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num)
  set m := (1 / 2 : ℝ) • y + (1 / 2 : ℝ) • y'
  have hnhds : V ∈ 𝓝 m := mem_interior_iff_mem_nhds.mp hint
  have hg : Continuous fun t : ℝ => m - t • w := by fun_prop
  have hpre := hg.continuousAt (x := 0) (by simpa using hnhds)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hpre
  have hmem : ε / 2 ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith
  have hin : m - (ε / 2) • w ∈ V := hball hmem
  have hle := hy.2 _ hin
  have hle' := hy'.2 y hy.1
  have hle'' := hy.2 y' hy'.1
  have hww : 0 < w ⬝ᵥ w := by
    have h0 : 0 ≤ w ⬝ᵥ w := Finset.sum_nonneg fun i _ => mul_self_nonneg (w i)
    exact lt_of_le_of_ne h0 (Ne.symm fun h => hw (dotProduct_self_eq_zero.mp h))
  simp only [m, dotProduct_sub, dotProduct_add, dotProduct_smul, smul_eq_mul] at hle
  nlinarith

/-- **Danskin's lemma** for a compact set with a unique minimizer: if `K` is compact and `x̄` is
the unique minimizer of `p̄·x` on `K`, then `μ_K` is differentiable at `p̄` with gradient `x̄`
(no convexity needed). -/
theorem supportFn_hasFDerivAt_of_compact {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    {p x : Fin n → ℝ} (hx : x ∈ supportArgmin K p) (huniq : ∀ y ∈ supportArgmin K p, y = x) :
    HasFDerivAt (supportFn K) (dualityDotCLM x) p := by
  have hbdd : ∀ q : Fin n → ℝ, BddBelow ((fun y => q ⬝ᵥ y) '' K) := fun q =>
    (hK.image (by fun_prop : Continuous fun y => q ⬝ᵥ y)).isBounded.bddBelow
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  have hRx : ‖x‖ ≤ R := hR x hx.1
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  set ε' := ε / (n + 1) with hε'
  have hε'pos : 0 < ε' := by positivity
  -- the far part of `K` is compact; its minimal excess cost is positive
  set Kf := K ∩ {y | ε' ≤ ‖y - x‖} with hKf
  have hKfc : IsCompact Kf :=
    hK.inter_right (isClosed_le continuous_const (by fun_prop))
  obtain ⟨η, hηpos, hη⟩ : ∃ η > 0, ∀ y ∈ Kf, p ⬝ᵥ x + η ≤ p ⬝ᵥ y := by
    rcases Kf.eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, fun y hy => by rw [he] at hy; exact absurd hy (Set.notMem_empty _)⟩
    obtain ⟨y0, hy0, hmin⟩ := hKfc.exists_isMinOn hne
      (by fun_prop : Continuous fun y => p ⬝ᵥ y).continuousOn
    have hlt : p ⬝ᵥ x < p ⬝ᵥ y0 := by
      rcases (hx.2 y0 hy0.1).lt_or_eq with h | h
      · exact h
      · exfalso
        have := huniq y0 ⟨hy0.1, fun z hz => h ▸ hx.2 z hz⟩
        have h3 : ε' ≤ ‖y0 - x‖ := hy0.2
        rw [this, sub_self, norm_zero] at h3
        linarith
    refine ⟨p ⬝ᵥ y0 - p ⬝ᵥ x, by linarith, fun y hy => ?_⟩
    have := hmin hy
    simp only [Set.mem_ofPred_eq] at this
    linarith
  have hball : ∀ᶠ q in 𝓝 p, ‖q - p‖ * (n * (2 * R)) ≤ η := by
    have hc : Tendsto (fun q : Fin n → ℝ => ‖q - p‖ * (n * (2 * R))) (𝓝 p) (𝓝 0) := by
      have : Tendsto (fun q : Fin n → ℝ => ‖q - p‖) (𝓝 p) (𝓝 0) := tendsto_norm_sub_self p
      simpa using this.mul_const (n * (2 * R))
    exact hc.eventually (eventually_le_nhds hηpos)
  filter_upwards [hball] with q hq
  have hup : supportFn K q ≤ q ⬝ᵥ x := supportFn_le (hbdd q) hx.1
  have hlow : supportFn K p + x ⬝ᵥ (q - p) - ε * ‖q - p‖ ≤ supportFn K q := by
    apply le_supportFn ⟨x, hx.1⟩
    intro y hy
    rw [supportFn_eq_of_mem_argmin hx]
    have hdot := duality_abs_dotProduct_le (q - p) (y - x)
    have hyx : ‖y - x‖ ≤ 2 * R := by
      calc ‖y - x‖ ≤ ‖y‖ + ‖x‖ := norm_sub_le y x
        _ ≤ 2 * R := by linarith [hR y hy]
    have hkey : q ⬝ᵥ y = p ⬝ᵥ x + x ⬝ᵥ (q - p) + (p ⬝ᵥ y - p ⬝ᵥ x) + (q - p) ⬝ᵥ (y - x) := by
      simp only [dotProduct_sub, sub_dotProduct, dotProduct_comm x q, dotProduct_comm x p]
      ring
    rw [hkey]
    have hpy := hx.2 y hy
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hqp := norm_nonneg (q - p)
    by_cases hfar : ε' ≤ ‖y - x‖
    · have h1 := hη y ⟨hy, hfar⟩
      have h2 : |(q - p) ⬝ᵥ (y - x)| ≤ η := by
        calc |(q - p) ⬝ᵥ (y - x)| ≤ n * (‖q - p‖ * ‖y - x‖) := hdot
          _ ≤ n * (‖q - p‖ * (2 * R)) := by gcongr
          _ ≤ η := by linarith
      have := neg_abs_le ((q - p) ⬝ᵥ (y - x))
      nlinarith [mul_nonneg hε.le hqp]
    · rw [not_le] at hfar
      have h2 : |(q - p) ⬝ᵥ (y - x)| ≤ ε * ‖q - p‖ := by
        calc |(q - p) ⬝ᵥ (y - x)| ≤ n * (‖q - p‖ * ‖y - x‖) := hdot
          _ ≤ n * (‖q - p‖ * ε') := by gcongr
          _ ≤ ε * ‖q - p‖ := by
            rw [hε']
            have : (n : ℝ) * (‖q - p‖ * (ε / (n + 1))) = ε * ‖q - p‖ * (n / (n + 1)) := by
              field_simp
            rw [this]
            have hfrac : (n : ℝ) / (n + 1) ≤ 1 := by
              rw [div_le_one (by positivity)]
              linarith
            calc ε * ‖q - p‖ * (n / (n + 1)) ≤ ε * ‖q - p‖ * 1 :=
                  mul_le_mul_of_nonneg_left hfrac (mul_nonneg hε.le hqp)
              _ = ε * ‖q - p‖ := mul_one _
      have := neg_abs_le ((q - p) ⬝ᵥ (y - x))
      linarith
  rw [dualityDotCLM_apply, Real.norm_eq_abs, abs_le]
  have hsp : supportFn K p = p ⬝ᵥ x := supportFn_eq_of_mem_argmin hx
  have hxq : x ⬝ᵥ (q - p) = q ⬝ᵥ x - p ⬝ᵥ x := by
    rw [dotProduct_sub, dotProduct_comm x q, dotProduct_comm x p]
  have := mul_nonneg hε.le (norm_nonneg (q - p))
  constructor <;> linarith

/-- **Shephard's lemma** for an input requirement set, without convexity: if `V ⊆ ℝ^n_+` is
closed, `w̄ ≫ 0` and `z̄` is the unique cost-minimizing input vector at `w̄`, then `μ_V` is
differentiable at `w̄` with gradient `z̄`. -/
theorem vcost_shephard {V : Set (Fin n → ℝ)} (hcl : IsClosed V) (hV : V ⊆ {z | 0 ≤ z})
    {w z : Fin n → ℝ} (hw : StrictlyPositive w) (hz : supportArgmin V w = {z}) :
    HasFDerivAt (supportFn V) (dualityDotCLM z) w := by
  have hzm : z ∈ supportArgmin V w := by rw [hz]; rfl
  set M := 4 * (w ⬝ᵥ z) + 1 with hM
  set K := V ∩ {y | w ⬝ᵥ y ≤ M} with hK
  have hwz : 0 ≤ w ⬝ᵥ z := dot_nonneg_of_nonneg (fun i => (hw i).le) (hV hzm.1)
  have hzK : z ∈ K := ⟨hzm.1, show w ⬝ᵥ z ≤ M by rw [hM]; linarith⟩
  -- `K` is compact
  have hM0 : 0 ≤ M := by rw [hM]; linarith
  have hKc : IsCompact K := by
    set R := ∑ j, M / w j with hR
    have hR0 : 0 ≤ R := Finset.sum_nonneg fun j _ => div_nonneg hM0 (hw j).le
    apply (isCompact_closedBall (0 : Fin n → ℝ) R).of_isClosed_subset
    · exact hcl.inter (isClosed_le (by fun_prop) continuous_const)
    · intro y hy
      rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hR0]
      intro i
      have hy0 : 0 ≤ y := hV hy.1
      have hyi : 0 ≤ y i := hy0 i
      have hyM : w ⬝ᵥ y ≤ M := hy.2
      rw [Real.norm_eq_abs, abs_of_nonneg hyi]
      have h1 : w i * y i ≤ w ⬝ᵥ y :=
        Finset.single_le_sum (f := fun j => w j * y j)
          (fun j _ => mul_nonneg (hw j).le (hy0 j)) (Finset.mem_univ i)
      have h2 : y i ≤ M / w i := by
        rw [le_div_iff₀ (hw i)]
        linarith
      have h3 : M / w i ≤ R :=
        Finset.single_le_sum (f := fun j => M / w j)
          (fun j _ => div_nonneg hM0 (hw j).le) (Finset.mem_univ i)
      linarith
  -- the minimizer on `K` is unique
  have hzK' : z ∈ supportArgmin K w := ⟨hzK, fun y hy => hzm.2 y hy.1⟩
  have huniqK : ∀ y ∈ supportArgmin K w, y = z := by
    intro y hy
    have : y ∈ supportArgmin V w := by
      refine ⟨hy.1.1, fun v hv => ?_⟩
      exact (hy.2 z hzK).trans (hzm.2 v hv)
    rw [hz] at this
    exact this
  have hdK := supportFn_hasFDerivAt_of_compact hKc hzK' huniqK
  -- `μ_V = μ_K` near `w`
  have hnear : ∀ᶠ q in 𝓝 w, ∀ i, w i / 2 ≤ q i ∧ q i ≤ 2 * w i := by
    rw [eventually_all]
    intro i
    have hc : Continuous fun q : Fin n → ℝ => q i := continuous_apply i
    have h1 : ∀ᶠ q in 𝓝 w, w i / 2 < q i :=
      hc.continuousAt.eventually (eventually_gt_nhds (by linarith [hw i]))
    have h2 : ∀ᶠ q in 𝓝 w, q i < 2 * w i :=
      hc.continuousAt.eventually (eventually_lt_nhds (by linarith [hw i]))
    filter_upwards [h1, h2] with q hq1 hq2
    exact ⟨hq1.le, hq2.le⟩
  have heq : supportFn V =ᶠ[𝓝 w] supportFn K := by
    filter_upwards [hnear] with q hq
    have hq0 : 0 ≤ q := fun i => show (0 : ℝ) ≤ q i by linarith [hw i, (hq i).1]
    apply le_antisymm
    · exact vcost_mono hV Set.inter_subset_left ⟨z, hzK⟩ hq0
    · apply le_csInf (Set.Nonempty.image (fun y => q ⬝ᵥ y) ⟨z, hzm.1⟩)
      rintro _ ⟨v, hv, rfl⟩
      by_cases hvK : w ⬝ᵥ v ≤ M
      · exact supportFn_le (bddBelow_of_subset_nonneg
          (fun y hy => hV hy.1) hq0) ⟨hv, hvK⟩
      · rw [not_le] at hvK
        have hv0 := hV hv
        have h1 : w ⬝ᵥ v ≤ 2 * (q ⬝ᵥ v) := by
          simp only [dotProduct, Finset.mul_sum]
          exact Finset.sum_le_sum fun i _ => by
            have hvi : 0 ≤ v i := hv0 i
            nlinarith [(hq i).1]
        have h2 : q ⬝ᵥ z ≤ 2 * (w ⬝ᵥ z) := by
          simp only [dotProduct, Finset.mul_sum]
          exact Finset.sum_le_sum fun i _ => by
            have hzi : 0 ≤ z i := hV hzm.1 i
            nlinarith [(hq i).2]
        have h3 := supportFn_le (bddBelow_of_subset_nonneg
          (fun y hy => hV hy.1) hq0) hzK
        linarith
  exact hdK.congr_of_eventuallyEq heq

/-- The law of demand for minimizers: `(w - w')·(z - z') ≤ 0`. -/
theorem vdemand_law {V : Set (Fin n → ℝ)} {w w' z z' : Fin n → ℝ}
    (hz : z ∈ supportArgmin V w) (hz' : z' ∈ supportArgmin V w') :
    (w - w') ⬝ᵥ (z - z') ≤ 0 := by
  have h1 := hz.2 z' hz'.1
  have h2 := hz'.2 z hz.1
  rw [sub_dotProduct, dotProduct_sub, dotProduct_sub]
  linarith

/-- Derivative properties of a single-valued minimizer selection: if `V ⊆ ℝ^n_+` is closed,
`w̄ ≫ 0`, `supportArgmin V w = {zs w}` for `w` near `w̄` and `zs` has derivative `D` at `w̄`,
then `D = D²μ_V(w̄)`, `D` is symmetric and negative semidefinite, and `D w̄ = 0`. -/
theorem vdemand_derivative {V : Set (Fin n → ℝ)} (hcl : IsClosed V) (hV : V ⊆ {z | 0 ≤ z})
    {zs : (Fin n → ℝ) → (Fin n → ℝ)} {w : Fin n → ℝ} (hw : StrictlyPositive w)
    (hzs : ∀ᶠ q in 𝓝 w, supportArgmin V q = {zs q})
    {D : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)} (hD : HasFDerivAt zs D w) :
    hessianMatrix (supportFn V) w = jacobian D ∧
      (∀ i j, jacobian D i j = jacobian D j i) ∧ NegSemidef (jacobian D) ∧ D w = 0 := by
  have hpos : ∀ᶠ q in 𝓝 w, StrictlyPositive q := relations_eventually_strictlyPositive hw
  have hgrad : ∀ᶠ q in 𝓝 w, HasFDerivAt (supportFn V) (dualityDotCLM (zs q)) q := by
    filter_upwards [hzs, hpos] with q hq hqpos
    exact vcost_shephard hcl hV hqpos hq
  refine ⟨?_, ?_, ?_, ?_⟩
  · have heq : (fun q => gradientVec (fderiv ℝ (supportFn V) q)) =ᶠ[𝓝 w] zs := by
      filter_upwards [hgrad] with q hq
      rw [hq.fderiv, gradientVec_dualityDotCLM]
    rw [hessianMatrix, (hD.congr_of_eventuallyEq heq).fderiv]
  · have h1 : ∀ᶠ q in 𝓝 w, HasFDerivAt (supportFn V) (dualityDotLin (zs q)) q := by
      filter_upwards [hgrad] with q hq
      rwa [dualityDotLin_apply]
    have h2 : HasFDerivAt (fun q => dualityDotLin (zs q)) (dualityDotLin.comp D) w :=
      dualityDotLin.hasFDerivAt.comp w hD
    intro i j
    have := second_derivative_symmetric_of_eventually h1 h2 (Pi.single j 1) (Pi.single i 1)
    simp only [ContinuousLinearMap.comp_apply, dualityDotLin_apply, dualityDotCLM_apply,
      dotProduct_single, mul_one] at this
    simpa [jacobian] using this
  · intro v
    rw [jacobian_mulVec]
    set γ : ℝ → Fin n → ℝ := fun t => w + t • v with hγ
    have hγd : HasDerivAt γ v 0 := by
      have h := ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add w
      simp only [id, one_smul] at h
      exact h
    have hγ0 : γ 0 = w := by simp [γ]
    have hcomp : HasDerivAt (fun t => zs (γ t)) (D v) 0 := by
      have hD' := hD
      rw [← hγ0] at hD'
      exact hD'.comp_hasDerivAt 0 hγd
    have hg : HasDerivAt (fun t => ∑ l, v l * zs (γ t) l) (∑ l, v l * D v l) 0 :=
      HasDerivAt.fun_sum fun l _ => (hasDerivAt_pi.mp hcomp l).const_mul (v l)
    apply hasDerivAt_nonpos_of_right_le hg
    have hcont : Tendsto γ (𝓝[>] 0) (𝓝 w) := by
      rw [← hγ0]
      exact hγd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    filter_upwards [hcont.eventually hzs, self_mem_nhdsWithin] with t ht htpos
    have hm1 : zs (γ t) ∈ supportArgmin V (γ t) := by rw [ht]; rfl
    have hm2 : zs w ∈ supportArgmin V w := by rw [hzs.self_of_nhds]; rfl
    have hlaw := vdemand_law hm1 hm2
    have hsub : γ t - w = t • v := by simp [γ]
    rw [hsub, smul_dotProduct, smul_eq_mul, dotProduct_sub] at hlaw
    have : v ⬝ᵥ zs (γ t) - v ⬝ᵥ zs w ≤ 0 := by
      by_contra h
      rw [not_le] at h
      have := mul_pos (show (0 : ℝ) < t from htpos) h
      linarith
    simp only [dotProduct] at this
    simp only [hγ0]
    linarith
  · set γ : ℝ → Fin n → ℝ := fun t => w + t • w with hγ
    have hγd : HasDerivAt γ w 0 := by
      have h := ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add w
      simp only [id, one_smul] at h
      exact h
    have hγ0 : γ 0 = w := by simp [γ]
    have hcomp : HasDerivAt (fun t => zs (γ t)) (D w) 0 := by
      have hD' := hD
      rw [← hγ0] at hD'
      exact hD'.comp_hasDerivAt 0 hγd
    have hcont : Tendsto γ (𝓝 0) (𝓝 w) := by
      rw [← hγ0]
      exact hγd.continuousAt.tendsto
    have hconst : (fun t => zs (γ t)) =ᶠ[𝓝 0] fun _ => zs w := by
      have : ∀ᶠ t : ℝ in 𝓝 0, -1 < t := lt_mem_nhds (by norm_num)
      filter_upwards [this, hcont.eventually hzs] with t ht hst
      have hpos : 0 < 1 + t := by linarith
      have hγt : γ t = (1 + t) • w := by simp [γ, add_smul]
      rw [hγt, vdemand_smul V w hpos, hzs.self_of_nhds] at hst
      rw [hγt]
      have : zs ((1 + t) • w) ∈ ({zs w} : Set (Fin n → ℝ)) := by rw [hst]; rfl
      exact this
    have h0 : HasDerivAt (fun t => zs (γ t)) 0 0 :=
      (hasDerivAt_const (0 : ℝ) (zs w)).congr_of_eventuallyEq hconst
    exact hcomp.unique h0

/-! ### Proposition 5.C.2 -/

/-- **Proposition 5.C.2(i)** (MWG, p. 141), first part: `c(·, q)` is homogeneous of degree one
in `w`. -/
theorem proposition_5_C_2_i_hom (f : (Fin n → ℝ) → ℝ) (w : Fin n → ℝ) (q : ℝ) {α : ℝ}
    (hα : 0 ≤ α) : costFn f (α • w) q = α * costFn f w q :=
  vcost_smul _ w hα

/-- **Proposition 5.C.2(i)** (MWG, p. 141), second part: `c(w, ·)` is nondecreasing in `q`
(where `q'` can be produced and `w ≥ 0`). -/
theorem proposition_5_C_2_i_mono (f : (Fin n → ℝ) → ℝ) {w : Fin n → ℝ} (hw : 0 ≤ w)
    {q q' : ℝ} (hqq : q ≤ q') (hne : (inputReq f q').Nonempty) :
    costFn f w q ≤ costFn f w q' :=
  vcost_mono (inputReq_subset_nonneg f q) (fun _ hz => ⟨hz.1, hqq.trans hz.2⟩) hne hw

/-- **Proposition 5.C.2(ii)** (MWG, p. 141): `c(·, q)` is concave in `w` on `ℝ^n_+`. -/
theorem proposition_5_C_2_ii (f : (Fin n → ℝ) → ℝ) {q : ℝ} (hne : (inputReq f q).Nonempty) :
    ConcaveOn ℝ {w : Fin n → ℝ | 0 ≤ w} (fun w => costFn f w q) :=
  vcost_concaveOn (inputReq_subset_nonneg f q) hne

theorem continuous_extendVec_neg (q : ℝ) :
    Continuous fun z : Fin n → ℝ => extendVec (-z) q := by
  refine continuous_pi fun i => ?_
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [extendVec, Fin.snoc_last]
    exact continuous_const
  · simp only [extendVec, Fin.snoc_castSucc, Pi.neg_apply]
    exact (continuous_apply j).neg

/-- The input requirement set is the section of the production set at output `q`. -/
theorem inputReq_eq_section (f : (Fin n → ℝ) → ℝ) (q : ℝ) :
    inputReq f q = {z | extendVec (-z) q ∈ singleOutputSet f} := by
  ext z
  exact mem_singleOutputSet.symm

theorem isClosed_inputReq {f : (Fin n → ℝ) → ℝ} (hcl : IsClosed (singleOutputSet f)) (q : ℝ) :
    IsClosed (inputReq f q) := by
  rw [inputReq_eq_section]
  exact hcl.preimage (continuous_extendVec_neg q)

theorem upward_inputReq {f : (Fin n → ℝ) → ℝ} (hfd : FreeDisposal (singleOutputSet f)) (q : ℝ) :
    ∀ z ∈ inputReq f q, ∀ z', z ≤ z' → z' ∈ inputReq f q := by
  intro z hz z' hzz
  rw [inputReq_eq_section] at hz ⊢
  apply hfd _ hz
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [extendVec]
  · simp only [extendVec, Fin.snoc_castSucc, Pi.neg_apply, neg_le_neg_iff]
    exact hzz j

/-- **Proposition 5.C.2(iii)** (MWG, p. 141). If `Y` is closed with free disposal and every
`{z ≥ 0 : f(z) ≥ q}` is convex, then `Y = {(-z, q) : w·z ≥ c(w, q) for all w ≫ 0}` (with
`c(w, q) = +∞` when `q` cannot be produced). -/
theorem proposition_5_C_2_iii {f : (Fin n → ℝ) → ℝ} (hcl : IsClosed (singleOutputSet f))
    (hfd : FreeDisposal (singleOutputSet f)) (hc : ∀ q, Convex ℝ (inputReq f q)) :
    singleOutputSet f = {y | ∀ w : Fin n → ℝ, StrictlyPositive w →
      costFnE f w (y (Fin.last n)) ≤ ((w ⬝ᵥ inputsOf y : ℝ) : EReal)} := by
  ext y
  have hy : y ∈ singleOutputSet f ↔ inputsOf y ∈ inputReq f (y (Fin.last n)) := by
    rw [inputReq_eq_section, Set.mem_ofPred_eq, extendVec_inputsOf]
  rw [hy, vcost_iii (isClosed_inputReq hcl _) (hc _) (upward_inputReq hfd _)
    (inputReq_subset_nonneg f _)]
  rfl

/-- **Proposition 5.C.2(iv)** (MWG, p. 141): `z(·, q)` is homogeneous of degree zero in `w`. -/
theorem proposition_5_C_2_iv (f : (Fin n → ℝ) → ℝ) (w : Fin n → ℝ) (q : ℝ) {α : ℝ}
    (hα : 0 < α) : condDemand f (α • w) q = condDemand f w q :=
  vdemand_smul _ w hα

/-- **Proposition 5.C.2(v)** (MWG, p. 141), first part: if `{z ≥ 0 : f(z) ≥ q}` is convex,
`z(w, q)` is convex. -/
theorem proposition_5_C_2_v_convex {f : (Fin n → ℝ) → ℝ} {q : ℝ} (hc : Convex ℝ (inputReq f q))
    (w : Fin n → ℝ) : Convex ℝ (condDemand f w q) :=
  vdemand_convex hc w

/-- **Proposition 5.C.2(v)** (MWG, p. 141), second part: if `{z ≥ 0 : f(z) ≥ q}` is strictly
convex, `z(w, q)` has at most one element (`w ≠ 0`). -/
theorem proposition_5_C_2_v_strict {f : (Fin n → ℝ) → ℝ} {q : ℝ}
    (hsc : StrictConvex ℝ (inputReq f q)) {w : Fin n → ℝ} (hw : w ≠ 0) :
    (condDemand f w q).Subsingleton :=
  vdemand_strict hsc hw

/-- **Proposition 5.C.2(vi), Shephard's lemma** (MWG, p. 141). If `Y` is closed, `w̄ ≫ 0` and
`z(w̄, q) = {z̄}`, then `c(·, q)` is differentiable at `w̄` with `∇_w c(w̄, q) = z̄`. No
convexity is needed. -/
theorem proposition_5_C_2_vi {f : (Fin n → ℝ) → ℝ} (hcl : IsClosed (singleOutputSet f))
    {w z : Fin n → ℝ} {q : ℝ} (hw : StrictlyPositive w) (hz : condDemand f w q = {z}) :
    HasFDerivAt (fun w => costFn f w q) (dualityDotCLM z) w :=
  vcost_shephard (isClosed_inputReq hcl q) (inputReq_subset_nonneg f q) hw hz

/-- **Proposition 5.C.2(vii)** (MWG, p. 141). If `Y` is closed, `w̄ ≫ 0`, `z(w, q) = {zs w}` for
`w` near `w̄` and `zs` has derivative `D` at `w̄`, then `D_w z(w̄, q) = D²_w c(w̄, q)`, symmetric
and negative semidefinite, with `D_w z(w̄, q) w̄ = 0`. -/
theorem proposition_5_C_2_vii {f : (Fin n → ℝ) → ℝ} (hcl : IsClosed (singleOutputSet f))
    {q : ℝ} {zs : (Fin n → ℝ) → (Fin n → ℝ)} {w : Fin n → ℝ} (hw : StrictlyPositive w)
    (hzs : ∀ᶠ v in 𝓝 w, condDemand f v q = {zs v})
    {D : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)} (hD : HasFDerivAt zs D w) :
    hessianMatrix (fun w => costFn f w q) w = jacobian D ∧
      (∀ i j, jacobian D i j = jacobian D j i) ∧ NegSemidef (jacobian D) ∧ D w = 0 :=
  vdemand_derivative (isClosed_inputReq hcl q) (inputReq_subset_nonneg f q) hw hzs hD

/-- If `f` is homogeneous of degree one on `ℝ^n_+`, `V(αq) = αV(q)` for `α > 0`. -/
theorem inputReq_smul {f : (Fin n → ℝ) → ℝ}
    (hf : ∀ z : Fin n → ℝ, 0 ≤ z → ∀ α : ℝ, 0 < α → f (α • z) = α * f z) {α : ℝ} (hα : 0 < α)
    (q : ℝ) : inputReq f (α * q) = (fun z => α • z) '' inputReq f q := by
  ext z
  constructor
  · rintro ⟨hz, hq⟩
    refine ⟨α⁻¹ • z, ⟨smul_nonneg (inv_nonneg.mpr hα.le) hz, ?_⟩, ?_⟩
    · rw [hf z hz α⁻¹ (inv_pos.mpr hα)]
      rw [← mul_le_mul_iff_of_pos_left hα, ← mul_assoc, mul_inv_cancel₀ hα.ne', one_mul]
      exact hq
    · simp only [smul_smul, mul_inv_cancel₀ hα.ne', one_smul]
  · rintro ⟨z', ⟨hz', hq⟩, rfl⟩
    exact ⟨smul_nonneg hα.le hz', by rw [hf z' hz' α hα]; exact mul_le_mul_of_nonneg_left hq hα.le⟩

/-- **Proposition 5.C.2(viii)** (MWG, p. 141) and **Exercise 5.C.3** (p. 161). If `f` is
homogeneous of degree one, `c(w, ·)` and `z(w, ·)` are homogeneous of degree one in `q`:
`c(w, αq) = αc(w, q)` and `z(w, αq) = αz(w, q)` for `α > 0`. -/
theorem proposition_5_C_2_viii {f : (Fin n → ℝ) → ℝ}
    (hf : ∀ z : Fin n → ℝ, 0 ≤ z → ∀ α : ℝ, 0 < α → f (α • z) = α * f z) (w : Fin n → ℝ)
    (q : ℝ) {α : ℝ} (hα : 0 < α) :
    costFn f w (α * q) = α * costFn f w q ∧
      condDemand f w (α * q) = (fun z => α • z) '' condDemand f w q := by
  have hV := inputReq_smul hf hα q
  constructor
  · unfold costFn supportFn
    rw [hV, Set.image_image]
    have : (fun z => w ⬝ᵥ (α • z)) = fun z => α * (w ⬝ᵥ z) := by
      funext z
      rw [dotProduct_smul, smul_eq_mul]
    rw [this, ← smul_eq_mul, ← Real.sInf_smul_of_nonneg hα.le]
    congr 1
    ext t
    simp [Set.mem_smul_set]
  · unfold condDemand supportArgmin
    rw [hV]
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · rintro ⟨⟨z', hz', rfl⟩, h⟩
      refine ⟨z', ⟨hz', fun y hy => ?_⟩, rfl⟩
      have := h (α • y) ⟨y, hy, rfl⟩
      simp only [dotProduct_smul, smul_eq_mul] at this
      exact le_of_mul_le_mul_left this hα
    · rintro ⟨z', ⟨hz', h⟩, rfl⟩
      refine ⟨⟨z', hz', rfl⟩, fun y hy => ?_⟩
      obtain ⟨x, hx, rfl⟩ := hy
      simp only [dotProduct_smul, smul_eq_mul]
      exact mul_le_mul_of_nonneg_left (h x hx) hα.le

/-- **Proposition 5.C.2(ix)** (MWG, p. 141) and **Exercise 5.C.3** (p. 161). If `f` is concave
on `ℝ^n_+`, then `c(w, ·)` is convex on the set of producible output levels (`w ≥ 0`); in
particular marginal costs are nondecreasing. -/
theorem proposition_5_C_2_ix {f : (Fin n → ℝ) → ℝ} (hf : ConcaveOn ℝ {z : Fin n → ℝ | 0 ≤ z} f)
    {w : Fin n → ℝ} (hw : 0 ≤ w) :
    ConvexOn ℝ {q : ℝ | (inputReq f q).Nonempty} (fun q => costFn f w q) := by
  have hconvQ : Convex ℝ {q : ℝ | (inputReq f q).Nonempty} := by
    rintro q ⟨z, hz⟩ q' ⟨z', hz'⟩ a b ha hb hab
    refine ⟨a • z + b • z', add_nonneg (smul_nonneg ha hz.1) (smul_nonneg hb hz'.1), ?_⟩
    have := hf.2 hz.1 hz'.1 ha hb hab
    simp only [smul_eq_mul] at this ⊢
    nlinarith [hz.2, hz'.2]
  refine ⟨hconvQ, fun q hq q' hq' a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  have hne : (inputReq f (a * q + b * q')).Nonempty := hconvQ hq hq' ha hb hab
  -- for any `z ∈ V(q)`, `z' ∈ V(q')`, the mixture is in `V(aq + bq')`
  have key : ∀ z ∈ inputReq f q, ∀ z' ∈ inputReq f q',
      costFn f w (a * q + b * q') ≤ a * (w ⬝ᵥ z) + b * (w ⬝ᵥ z') := by
    intro z hz z' hz'
    have hmem : a • z + b • z' ∈ inputReq f (a * q + b * q') := by
      refine ⟨add_nonneg (smul_nonneg ha hz.1) (smul_nonneg hb hz'.1), ?_⟩
      have := hf.2 hz.1 hz'.1 ha hb hab
      simp only [smul_eq_mul] at this
      nlinarith [hz.2, hz'.2]
    have := supportFn_le (bddBelow_of_subset_nonneg (inputReq_subset_nonneg f _) hw) hmem
    rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul] at this
    exact this
  -- take infima
  have hb1 := bddBelow_of_subset_nonneg (inputReq_subset_nonneg f q) hw
  have hb2 := bddBelow_of_subset_nonneg (inputReq_subset_nonneg f q') hw
  by_contra hlt
  rw [not_le] at hlt
  rcases ha.lt_or_eq with ha' | ha'
  · rcases hb.lt_or_eq with hb' | hb'
    · set d := costFn f w (a * q + b * q') - (a * costFn f w q + b * costFn f w q')
      have hd : 0 < d := by simp only [d]; linarith
      obtain ⟨_, ⟨z, hz, rfl⟩, hzlt⟩ := exists_lt_of_csInf_lt (hq.image _)
        (show costFn f w q < costFn f w q + d / (2 * a) by
          have : 0 < d / (2 * a) := by positivity
          linarith)
      obtain ⟨_, ⟨z', hz', rfl⟩, hzlt'⟩ := exists_lt_of_csInf_lt (hq'.image _)
        (show costFn f w q' < costFn f w q' + d / (2 * b) by
          have : 0 < d / (2 * b) := by positivity
          linarith)
      have h1 := key z hz z' hz'
      have e1 : a * (d / (2 * a)) = d / 2 := by field_simp
      have e2 : b * (d / (2 * b)) = d / 2 := by field_simp
      have m1 := mul_lt_mul_of_pos_left hzlt ha'
      have m2 := mul_lt_mul_of_pos_left hzlt' hb'
      simp only [mul_add] at m1 m2
      simp only [d] at e1 e2
      nlinarith
    · subst hb'
      have ha1 : a = 1 := by linarith
      subst ha1
      simp at hlt
  · subst ha'
    have hb1' : b = 1 := by linarith
    subst hb1'
    simp at hlt

/-! ### Exercise 5.C.5 -/

/-- **Exercise 5.C.5** (MWG, p. 161), first part. Property (iii) of Proposition 5.C.2 holds when
`f` is quasiconcave on `ℝ^n_+` (and `Y` is closed with free disposal): quasiconcavity is exactly
convexity of the sets `{z ≥ 0 : f(z) ≥ q}`. -/
theorem exercise_5_C_5_i {f : (Fin n → ℝ) → ℝ} (hcl : IsClosed (singleOutputSet f))
    (hfd : FreeDisposal (singleOutputSet f)) (hq : QuasiconcaveOn ℝ {z : Fin n → ℝ | 0 ≤ z} f) :
    singleOutputSet f = {y | ∀ w : Fin n → ℝ, StrictlyPositive w →
      costFnE f w (y (Fin.last n)) ≤ ((w ⬝ᵥ inputsOf y : ℝ) : EReal)} :=
  proposition_5_C_2_iii hcl hfd fun q => by
    have := hq q
    have heq : inputReq f q = {z ∈ {z : Fin n → ℝ | 0 ≤ z} | q ≤ f z} := rfl
    rw [heq]
    exact this

/-- **Exercise 5.C.5** (MWG, p. 161), second part: quasiconcavity is compatible with increasing
returns. `f(z) = (min{z₁, z₂})²` is quasiconcave on `ℝ²_+` and `f(tz) = t²f(z)`, so
`f(tz) > tf(z)` for `t > 1` whenever `f(z) > 0`. -/
theorem exercise_5_C_5_ii :
    QuasiconcaveOn ℝ {z : Fin 2 → ℝ | 0 ≤ z} (fun z => (min (z 0) (z 1)) ^ 2) ∧
      ∀ z : Fin 2 → ℝ, 0 ≤ z → ∀ t : ℝ, 1 < t → 0 < (min (z 0) (z 1)) ^ 2 →
        t * (min (z 0) (z 1)) ^ 2 < (min ((t • z) 0) ((t • z) 1)) ^ 2 := by
  constructor
  · intro r x hx y hy a b ha hb hab
    obtain ⟨hx0, hxr⟩ := hx
    obtain ⟨hy0, hyr⟩ := hy
    refine ⟨show 0 ≤ a • x + b • y from
      add_nonneg (smul_nonneg ha hx0) (smul_nonneg hb hy0), ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hmx : 0 ≤ min (x 0) (x 1) := le_min (hx0 0) (hx0 1)
    have hmy : 0 ≤ min (y 0) (y 1) := le_min (hy0 0) (hy0 1)
    have hlow : a * min (x 0) (x 1) + b * min (y 0) (y 1) ≤
        min (a * x 0 + b * y 0) (a * x 1 + b * y 1) :=
      le_min (add_le_add (mul_le_mul_of_nonneg_left (min_le_left _ _) ha)
          (mul_le_mul_of_nonneg_left (min_le_left _ _) hb))
        (add_le_add (mul_le_mul_of_nonneg_left (min_le_right _ _) ha)
          (mul_le_mul_of_nonneg_left (min_le_right _ _) hb))
    have hm := min_le_max (a := min (x 0) (x 1)) (b := min (y 0) (y 1))
    rcases le_total (min (x 0) (x 1)) (min (y 0) (y 1)) with hxy | hxy
    · have h1 : min (x 0) (x 1) ≤ a * min (x 0) (x 1) + b * min (y 0) (y 1) := by nlinarith
      calc r ≤ (min (x 0) (x 1)) ^ 2 := hxr
        _ ≤ (a * min (x 0) (x 1) + b * min (y 0) (y 1)) ^ 2 := pow_le_pow_left₀ hmx h1 2
        _ ≤ _ := pow_le_pow_left₀ (by positivity) hlow 2
    · have h1 : min (y 0) (y 1) ≤ a * min (x 0) (x 1) + b * min (y 0) (y 1) := by nlinarith
      calc r ≤ (min (y 0) (y 1)) ^ 2 := hyr
        _ ≤ (a * min (x 0) (x 1) + b * min (y 0) (y 1)) ^ 2 := pow_le_pow_left₀ hmy h1 2
        _ ≤ _ := pow_le_pow_left₀ (by positivity) hlow 2
  · intro z hz t ht hpos
    simp only [Pi.smul_apply, smul_eq_mul]
    have ht0 : 0 ≤ t := by linarith
    rw [← mul_min_of_nonneg _ _ ht0, mul_pow]
    have : t < t ^ 2 := by nlinarith
    nlinarith

end MWG.Production

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Cost minimization: first-order conditions, marginal cost, multiple outputs

MWG Section 5.C, pp. 139-141.

* Footnote 8: the first-order conditions (5.C.4) are sufficient when `f` is quasiconcave
  (`foc_5_C_4_sufficient`), with the complementary-slackness condition `λ(f(z*) - q) = 0`
  that (5.C.4) leaves implicit.
* p. 140: the multiplier `λ` is the marginal cost `∂c(w, q)/∂q` (`lambda_eq_marginal_cost`, for
  concave `f`, via the subgradient inequality `cost_lambda_subgradient`).
* Footnote 9: (5.C.4) with `λ = p` is (5.C.2) (`footnote_5_C_9`).
* (5.C.5)-(5.C.6): the output choice `max_{q ≥ 0} pq - c(w, q)` (`foc_5_C_6`), sufficient for
  convex `c(w, ·)` (`foc_5_C_6_sufficient`).
* **Exercise 5.C.4**: properties (i)-(vii) of Proposition 5.C.2 for multiple outputs.
-/

namespace MWG.Production

open MWG.ClassicalDemand MWG.ConsumerChoice Filter Topology

variable {n : ℕ}

/-- For `f` quasiconcave on `ℝ^n_+` and differentiable at `z* ≥ 0`, `f(z) ≥ f(z*)` with `z ≥ 0`
implies `∇f(z*)·(z - z*) ≥ 0`. -/
theorem quasiconcave_grad_nonneg {f : (Fin n → ℝ) → ℝ}
    (hq : QuasiconcaveOn ℝ {z : Fin n → ℝ | 0 ≤ z} f) {x z : Fin n → ℝ} (hx : 0 ≤ x)
    (hz : 0 ≤ z) (hf : DifferentiableAt ℝ f x) (hfz : f x ≤ f z) :
    0 ≤ fderiv ℝ f x (z - x) := by
  have hd := mc_line_hasDerivAt hf.hasFDerivAt (z - x)
  apply mc_le_deriv_of_slope hd
  intro t ht0 ht1
  have hmem := hq (f x) ⟨hx, le_rfl⟩ ⟨hz, hfz⟩ (by linarith : (0 : ℝ) ≤ 1 - t) ht0.le
    (by ring)
  have heq : (1 - t) • x + t • z = x + t • (z - x) := by module
  rw [heq] at hmem
  simp only [zero_smul, add_zero]
  exact div_nonneg (by linarith [hmem.2]) ht0.le

/-- **Section 5.C** (MWG, p. 140, footnote 8). Sufficiency of the first-order conditions (5.C.4)
for quasiconcave `f`: if `z* ≥ 0`, `f(z*) ≥ q`, `λ ≥ 0` with `λ(f(z*) - q) = 0`,
`w ≥ λ∇f(z*)` and `[w - λ∇f(z*)]·z* = 0`, then `z*` solves the CMP. -/
theorem foc_5_C_4_sufficient {f : (Fin n → ℝ) → ℝ}
    (hq : QuasiconcaveOn ℝ {z : Fin n → ℝ | 0 ≤ z} f) {w z : Fin n → ℝ} {q lam : ℝ}
    (hz : 0 ≤ z) (hfz : q ≤ f z) (hf : DifferentiableAt ℝ f z) (hlam : 0 ≤ lam)
    (hcs : lam * (f z - q) = 0) (hw : ∀ l, lam * partialF f z l ≤ w l)
    (hcs' : (fun l => w l - lam * partialF f z l) ⬝ᵥ z = 0) :
    z ∈ condDemand f w q := by
  refine ⟨⟨hz, hfz⟩, fun z' hz' => ?_⟩
  have hgrad : ∀ v, fderiv ℝ f z v = (fun l => partialF f z l) ⬝ᵥ v := fun v => by
    rw [fderiv_apply_eq_gradient_dot]
    rfl
  have h1 : (fun l => lam * partialF f z l) ⬝ᵥ z' ≤ w ⬝ᵥ z' := by
    apply Finset.sum_le_sum
    intro l _
    exact mul_le_mul_of_nonneg_right (hw l) (hz'.1 l)
  have h2 : w ⬝ᵥ z = (fun l => lam * partialF f z l) ⬝ᵥ z := by
    have : (fun l => w l - lam * partialF f z l) ⬝ᵥ z =
        w ⬝ᵥ z - (fun l => lam * partialF f z l) ⬝ᵥ z := by
      simp only [dotProduct, ← Finset.sum_sub_distrib, sub_mul]
    linarith
  have hsm : ∀ v, (fun l => lam * partialF f z l) ⬝ᵥ v = lam * fderiv ℝ f z v := fun v => by
    rw [hgrad]
    simp only [dotProduct, Finset.mul_sum, mul_assoc]
  rcases hlam.lt_or_eq with hpos | hzero
  · have hbind : f z = q := by
      rcases mul_eq_zero.mp hcs with h | h
      · exact absurd h hpos.ne'
      · linarith
    have h3 := quasiconcave_grad_nonneg hq hz hz'.1 hf (hbind ▸ hz'.2)
    have h4 : (fun l => lam * partialF f z l) ⬝ᵥ (z' - z) ≥ 0 := by
      rw [hsm]
      exact mul_nonneg hpos.le h3
    rw [dotProduct_sub] at h4
    linarith
  · subst hzero
    have : (fun l => (0 : ℝ) * partialF f z l) = 0 := by funext l; simp
    rw [this, zero_dotProduct] at h1 h2
    linarith

/-- **Section 5.C** (MWG, p. 140). For concave `f`, the multiplier `λ` of (5.C.4) at a binding
solution is a subgradient of `c(w, ·)` at `q̄`: `c(w, q) ≥ c(w, q̄) + λ(q - q̄)`. -/
theorem cost_lambda_subgradient {f : (Fin n → ℝ) → ℝ}
    (hc : ConcaveOn ℝ {z : Fin n → ℝ | 0 ≤ z} f) {w z : Fin n → ℝ} {qb lam : ℝ}
    (hz : z ∈ condDemand f w qb) (hbind : f z = qb) (hf : DifferentiableAt ℝ f z)
    (hlam : 0 ≤ lam) (hw : ∀ l, lam * partialF f z l ≤ w l)
    (hcs' : (fun l => w l - lam * partialF f z l) ⬝ᵥ z = 0) {q : ℝ}
    (hne : (inputReq f q).Nonempty) :
    costFn f w qb + lam * (q - qb) ≤ costFn f w q := by
  apply le_csInf (hne.image _)
  rintro _ ⟨z', hz', rfl⟩
  have hcost : costFn f w qb = w ⬝ᵥ z := supportFn_eq_of_mem_argmin hz
  rw [hcost]
  have htan := concave_le_tangent hc hz.1.1 hz'.1 hf
  have hgrad : fderiv ℝ f z (z' - z) = (fun l => partialF f z l) ⬝ᵥ (z' - z) := by
    rw [fderiv_apply_eq_gradient_dot]
    rfl
  rw [hgrad, hbind] at htan
  have h1 : (fun l => lam * partialF f z l) ⬝ᵥ z' ≤ w ⬝ᵥ z' := by
    apply Finset.sum_le_sum
    intro l _
    exact mul_le_mul_of_nonneg_right (hw l) (hz'.1 l)
  have h2 : w ⬝ᵥ z = (fun l => lam * partialF f z l) ⬝ᵥ z := by
    have : (fun l => w l - lam * partialF f z l) ⬝ᵥ z =
        w ⬝ᵥ z - (fun l => lam * partialF f z l) ⬝ᵥ z := by
      simp only [dotProduct, ← Finset.sum_sub_distrib, sub_mul]
    linarith
  have hsm : ∀ v, (fun l => lam * partialF f z l) ⬝ᵥ v =
      lam * ((fun l => partialF f z l) ⬝ᵥ v) := fun v => by
    simp only [dotProduct, Finset.mul_sum, mul_assoc]
  rw [hsm] at h1 h2
  change w ⬝ᵥ z + lam * (q - qb) ≤ w ⬝ᵥ z'
  have h3 : q - qb ≤ (fun l => partialF f z l) ⬝ᵥ (z' - z) := by linarith [hz'.2]
  rw [dotProduct_sub] at h3
  nlinarith [mul_le_mul_of_nonneg_left h3 hlam]

/-- **Section 5.C** (MWG, p. 140). "`λ` equals `∂c(w, q)/∂q`, the marginal cost of production":
for concave `f`, if `c(w, ·)` has derivative `d` at `q̄` (with nearby outputs producible), then
`d = λ`. -/
theorem lambda_eq_marginal_cost {f : (Fin n → ℝ) → ℝ}
    (hc : ConcaveOn ℝ {z : Fin n → ℝ | 0 ≤ z} f) {w z : Fin n → ℝ} {qb lam : ℝ}
    (hz : z ∈ condDemand f w qb) (hbind : f z = qb) (hf : DifferentiableAt ℝ f z)
    (hlam : 0 ≤ lam) (hw : ∀ l, lam * partialF f z l ≤ w l)
    (hcs' : (fun l => w l - lam * partialF f z l) ⬝ᵥ z = 0)
    (hnear : ∀ᶠ q in 𝓝 qb, (inputReq f q).Nonempty) {d : ℝ}
    (hd : HasDerivAt (fun q => costFn f w q) d qb) : d = lam := by
  have hmin : IsLocalMin (fun q => costFn f w q - lam * q) qb := by
    filter_upwards [hnear] with q hq
    have := cost_lambda_subgradient hc hz hbind hf hlam hw hcs' hq
    linarith
  have hd' : HasDerivAt (fun q => costFn f w q - lam * q) (d - lam) qb := by
    have h := hd.fun_sub ((hasDerivAt_id qb).const_mul lam)
    simp only [id, mul_one] at h
    exact h
  have := hmin.hasDerivAt_eq_zero hd'
  linarith

/-- **Footnote 9** (MWG, p. 141). The first-order conditions (5.C.4) of the CMP with `λ = p`
are the conditions (5.C.2) of the PMP. -/
theorem footnote_5_C_9 (f : (Fin n → ℝ) → ℝ) (w z : Fin n → ℝ) (p : ℝ) :
    ((∀ l, p * partialF f z l ≤ w l) ∧ (fun l => p * partialF f z l - w l) ⬝ᵥ z = 0) ↔
      ((∀ l, p * partialF f z l ≤ w l) ∧ (fun l => w l - p * partialF f z l) ⬝ᵥ z = 0) := by
  have : (fun l => w l - p * partialF f z l) ⬝ᵥ z =
      -((fun l => p * partialF f z l - w l) ⬝ᵥ z) := by
    simp only [dotProduct, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [this, neg_eq_zero]

/-- The tangent inequality for a convex function of one variable at a point of
differentiability. -/
theorem convex_tangent_le {S : Set ℝ} {C : ℝ → ℝ} (hC : ConvexOn ℝ S C) {x y d : ℝ}
    (hx : x ∈ S) (hy : y ∈ S) (hd : HasDerivAt C d x) : C x + d * (y - x) ≤ C y := by
  have hline : HasDerivAt (fun t : ℝ => C (x + t * (y - x)) - t * (C y - C x))
      (d * (y - x) - (C y - C x)) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => x + t * (y - x)) (y - x) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (y - x)).const_add x
    have hd' : HasDerivAt C d (x + 0 * (y - x)) := by simpa using hd
    have h2 := hd'.comp (0 : ℝ) h1
    have h3 := (hasDerivAt_id (0 : ℝ)).mul_const (C y - C x)
    have h4 := h2.fun_sub h3
    simp only [Function.comp_apply, id, one_mul] at h4
    exact h4
  have := hasDerivAt_nonpos_of_right_le hline ?_
  · linarith
  have hI : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 := nhdsWithin_le_nhds (eventually_lt_nhds one_pos)
  filter_upwards [self_mem_nhdsWithin, hI] with t ht ht1
  have ht0 : (0 : ℝ) < t := ht
  have hconv := hC.2 hx hy (by linarith : (0 : ℝ) ≤ 1 - t) ht0.le (by ring)
  simp only [smul_eq_mul] at hconv
  have heq : (1 - t) * x + t * y = x + t * (y - x) := by ring
  rw [heq] at hconv
  simp only [zero_mul, add_zero, sub_zero]
  linarith

/-- **Section 5.C** (MWG, p. 141), condition (5.C.6). If `q* ≥ 0` solves (5.C.5),
`max_{q ≥ 0} pq - C(q)`, and `C` is differentiable at `q*`, then `p - C'(q*) ≤ 0`, with equality
if `q* > 0`: at an interior optimum, price equals marginal cost. -/
theorem foc_5_C_6 {C : ℝ → ℝ} {p q d : ℝ} (hq : 0 ≤ q)
    (hopt : ∀ q', 0 ≤ q' → p * q' - C q' ≤ p * q - C q) (hd : HasDerivAt C d q) :
    p - d ≤ 0 ∧ (0 < q → p = d) := by
  have hline : HasDerivAt (fun t : ℝ => p * (q + t) - C (q + t)) (p - d) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => q + t) 1 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_add q
    have hd' : HasDerivAt C d (q + 0) := by simpa using hd
    have h2 := hd'.comp (0 : ℝ) h1
    have h3 := h1.const_mul p
    have h4 := h3.fun_sub h2
    simp only [Function.comp_apply, mul_one] at h4
    exact h4
  have hle : p - d ≤ 0 := by
    apply hasDerivAt_nonpos_of_right_le hline
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : (0 : ℝ) < t := ht
    simpa using hopt (q + t) (by linarith)
  refine ⟨hle, fun hqpos => ?_⟩
  have hl' := hline
  rw [← neg_zero] at hl'
  have hneg := hl'.comp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))
  have := hasDerivAt_nonpos_of_right_le hneg ?_
  · simp only [mul_neg, mul_one] at this
    linarith
  have hI : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < q := nhdsWithin_le_nhds (eventually_lt_nhds hqpos)
  filter_upwards [hI] with t ht
  simp only [Function.comp_apply, neg_zero, add_zero]
  have := hopt (q + -t) (by linarith)
  exact this

/-- **Section 5.C** (MWG, p. 141). If `C` is convex on `[0, ∞)`, the condition (5.C.6) is
sufficient for `q* ≥ 0` to solve (5.C.5). -/
theorem foc_5_C_6_sufficient {C : ℝ → ℝ} (hC : ConvexOn ℝ (Set.Ici 0) C) {p q d : ℝ}
    (hq : 0 ≤ q) (hd : HasDerivAt C d q) (hle : p - d ≤ 0) (heq : 0 < q → p = d) :
    ∀ q', 0 ≤ q' → p * q' - C q' ≤ p * q - C q := by
  intro q' hq'
  have htan := convex_tangent_le hC (Set.mem_Ici.mpr hq) (Set.mem_Ici.mpr hq') hd
  rcases hq.lt_or_eq with hpos | hzero
  · rw [heq hpos] at *
    linarith
  · subst hzero
    nlinarith

/-! ### Exercise 5.C.4: multiple outputs -/

/-- The input requirement set of a multiple-output technology `T` (pairs `(z, q)` of inputs and
outputs): `V(q) = {z ≥ 0 : (z, q) ∈ T}`. -/
def inputReqMulti {m : ℕ} (T : Set ((Fin n → ℝ) × (Fin m → ℝ))) (q : Fin m → ℝ) :
    Set (Fin n → ℝ) :=
  {z | 0 ≤ z ∧ (z, q) ∈ T}

/-- The cost function `c(w, q)` of a multiple-output technology. -/
noncomputable def costMulti {m : ℕ} (T : Set ((Fin n → ℝ) × (Fin m → ℝ))) (w : Fin n → ℝ)
    (q : Fin m → ℝ) : ℝ :=
  supportFn (inputReqMulti T q) w

/-- The conditional factor demand of a multiple-output technology. -/
def condDemandMulti {m : ℕ} (T : Set ((Fin n → ℝ) × (Fin m → ℝ))) (w : Fin n → ℝ)
    (q : Fin m → ℝ) : Set (Fin n → ℝ) :=
  supportArgmin (inputReqMulti T q) w

theorem inputReqMulti_subset {m : ℕ} (T : Set ((Fin n → ℝ) × (Fin m → ℝ))) (q : Fin m → ℝ) :
    inputReqMulti T q ⊆ {z | 0 ≤ z} := fun _ hz => hz.1

/-- **Exercise 5.C.4(i)** (MWG, p. 161). For multiple outputs, `c(·, q)` is homogeneous of degree
one in `w`, and nondecreasing in `q` under free disposal of outputs. -/
theorem exercise_5_C_4_i {m : ℕ} (T : Set ((Fin n → ℝ) × (Fin m → ℝ))) :
    (∀ (w : Fin n → ℝ) q (α : ℝ), 0 ≤ α → costMulti T (α • w) q = α * costMulti T w q) ∧
      ((∀ z q q', q ≤ q' → (z, q') ∈ T → (z, q) ∈ T) → ∀ (w : Fin n → ℝ), 0 ≤ w →
        ∀ q q', q ≤ q' → (inputReqMulti T q').Nonempty → costMulti T w q ≤ costMulti T w q') :=
  ⟨fun _ _ _ hα => vcost_smul _ _ hα, fun hfd _ hw q q' hqq hne =>
    vcost_mono (inputReqMulti_subset T q) (fun _ hz => ⟨hz.1, hfd _ q q' hqq hz.2⟩) hne hw⟩

/-- **Exercise 5.C.4(ii)** (MWG, p. 161): `c(·, q)` is concave in `w`. -/
theorem exercise_5_C_4_ii {m : ℕ} (T : Set ((Fin n → ℝ) × (Fin m → ℝ))) {q : Fin m → ℝ}
    (hne : (inputReqMulti T q).Nonempty) :
    ConcaveOn ℝ {w : Fin n → ℝ | 0 ≤ w} (fun w => costMulti T w q) :=
  vcost_concaveOn (inputReqMulti_subset T q) hne

/-- **Exercise 5.C.4(iii)** (MWG, p. 161): if every `V(q)` is closed, convex and has free
disposal of inputs, then `(z, q) ∈ T` with `z ≥ 0` iff `w·z ≥ c(w, q)` for all `w ≫ 0`. -/
theorem exercise_5_C_4_iii {m : ℕ} (T : Set ((Fin n → ℝ) × (Fin m → ℝ)))
    (hcl : ∀ q, IsClosed (inputReqMulti T q)) (hc : ∀ q, Convex ℝ (inputReqMulti T q))
    (hup : ∀ q, ∀ z ∈ inputReqMulti T q, ∀ z', z ≤ z' → z' ∈ inputReqMulti T q)
    (z : Fin n → ℝ) (q : Fin m → ℝ) :
    z ∈ inputReqMulti T q ↔ ∀ w : Fin n → ℝ, StrictlyPositive w →
      supportFnE (inputReqMulti T q) w ≤ ((w ⬝ᵥ z : ℝ) : EReal) :=
  vcost_iii (hcl q) (hc q) (hup q) (inputReqMulti_subset T q) z

/-- **Exercise 5.C.4(iv)** (MWG, p. 161): `z(·, q)` is homogeneous of degree zero in `w`. -/
theorem exercise_5_C_4_iv {m : ℕ} (T : Set ((Fin n → ℝ) × (Fin m → ℝ))) (w : Fin n → ℝ)
    (q : Fin m → ℝ) {α : ℝ} (hα : 0 < α) : condDemandMulti T (α • w) q = condDemandMulti T w q :=
  vdemand_smul _ w hα

/-- **Exercise 5.C.4(v)** (MWG, p. 161): convex `V(q)` gives convex `z(w, q)`; strictly convex
`V(q)` gives at most one element (`w ≠ 0`). -/
theorem exercise_5_C_4_v {m : ℕ} (T : Set ((Fin n → ℝ) × (Fin m → ℝ))) (q : Fin m → ℝ)
    (w : Fin n → ℝ) :
    (Convex ℝ (inputReqMulti T q) → Convex ℝ (condDemandMulti T w q)) ∧
      (StrictConvex ℝ (inputReqMulti T q) → w ≠ 0 → (condDemandMulti T w q).Subsingleton) :=
  ⟨fun hc => vdemand_convex hc w, fun hsc hw => vdemand_strict hsc hw⟩

/-- **Exercise 5.C.4(vi)** (MWG, p. 161), Shephard's lemma for multiple outputs. -/
theorem exercise_5_C_4_vi {m : ℕ} (T : Set ((Fin n → ℝ) × (Fin m → ℝ))) {q : Fin m → ℝ}
    (hcl : IsClosed (inputReqMulti T q)) {w z : Fin n → ℝ} (hw : StrictlyPositive w)
    (hz : condDemandMulti T w q = {z}) :
    HasFDerivAt (fun w => costMulti T w q) (dualityDotCLM z) w :=
  vcost_shephard hcl (inputReqMulti_subset T q) hw hz

/-- **Exercise 5.C.4(vii)** (MWG, p. 161): `D_w z(w̄, q) = D²_w c(w̄, q)`, symmetric and negative
semidefinite, with `D_w z(w̄, q) w̄ = 0`. -/
theorem exercise_5_C_4_vii {m : ℕ} (T : Set ((Fin n → ℝ) × (Fin m → ℝ))) {q : Fin m → ℝ}
    (hcl : IsClosed (inputReqMulti T q)) {zs : (Fin n → ℝ) → (Fin n → ℝ)} {w : Fin n → ℝ}
    (hw : StrictlyPositive w) (hzs : ∀ᶠ v in 𝓝 w, condDemandMulti T v q = {zs v})
    {D : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)} (hD : HasFDerivAt zs D w) :
    hessianMatrix (fun w => costMulti T w q) w = jacobian D ∧
      (∀ i j, jacobian D i j = jacobian D j i) ∧ NegSemidef (jacobian D) ∧ D w = 0 :=
  vdemand_derivative hcl (inputReqMulti_subset T q) hw hzs hD

end MWG.Production

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Aggregation (MWG Section 5.E, pp. 147-149)

For production sets `Y₁, …, Y_J ⊆ ℝ^L`: the aggregate production set `Y = Y₁ + ⋯ + Y_J` and the
aggregate supply correspondence `Σ_j y_j(p)`.

* **Proposition 5.E.1** (i) `π*(p) = Σ_j π_j(p)` (`proposition_5_E_1_i`, in `[-∞, +∞]` for
  nonempty `Y_j`; real form `proposition_5_E_1_i_real`) and (ii) `y*(p) = Σ_j y_j(p)`
  (`proposition_5_E_1_ii`), for every price vector and without convexity (**Exercise 5.E.2**).
* The aggregate law of supply and the symmetry and semidefiniteness of `Σ_j Dy_j(p)` (p. 147).
* **Exercise 5.E.1** (the differentiable proof of (ii)) and **Exercise 5.E.3**, which as printed
  (prices `p ≫ 0`) fails like Proposition 5.C.1(iii); corrected forms are proved.
-/

namespace MWG.Production

open MWG.ClassicalDemand MWG.ConsumerChoice Filter Topology

variable {L J : ℕ}

/-- **Section 5.E** (MWG, p. 147). The aggregate production set `Y₁ + ⋯ + Y_J`. -/
def aggSet (Ys : Fin J → Set (Fin L → ℝ)) : Set (Fin L → ℝ) :=
  {y | ∃ ys : Fin J → Fin L → ℝ, (∀ j, ys j ∈ Ys j) ∧ y = ∑ j, ys j}

/-- **Section 5.E** (MWG, p. 147). The aggregate supply correspondence `Σ_j y_j(p)`. -/
def aggSupply (Ys : Fin J → Set (Fin L → ℝ)) (p : Fin L → ℝ) : Set (Fin L → ℝ) :=
  {y | ∃ ys : Fin J → Fin L → ℝ, (∀ j, ys j ∈ supply (Ys j) p) ∧ y = ∑ j, ys j}

theorem dotProduct_finset_sum (p : Fin L → ℝ) (ys : Fin J → Fin L → ℝ) :
    p ⬝ᵥ ∑ j, ys j = ∑ j, p ⬝ᵥ ys j := by
  simp only [dotProduct, Finset.sum_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.mul_sum _ _ _

/-- **Proposition 5.E.1(ii)** (MWG, p. 148) and **Exercise 5.E.2**. For every `p`, the supply
correspondence of the aggregate production set is the sum of the individual supply
correspondences: `y*(p) = Σ_j y_j(p)`. No convexity is used. -/
theorem proposition_5_E_1_ii (Ys : Fin J → Set (Fin L → ℝ)) (p : Fin L → ℝ) :
    supply (aggSet Ys) p = aggSupply Ys p := by
  classical
  ext y
  constructor
  · rintro ⟨⟨ys, hys, rfl⟩, hmax⟩
    refine ⟨ys, fun k => ⟨hys k, fun y' hy' => ?_⟩, rfl⟩
    set ys' := Function.update ys k y' with hys'
    have hmem : ∑ j, ys' j ∈ aggSet Ys := ⟨ys', fun j => by
      by_cases hj : j = k
      · subst hj; simp [hys', hy']
      · simp [hys', hj, hys j], rfl⟩
    have h1 := hmax _ hmem
    rw [dotProduct_finset_sum, dotProduct_finset_sum] at h1
    have h2 : ∑ j, p ⬝ᵥ ys' j = ∑ j, p ⬝ᵥ ys j - p ⬝ᵥ ys k + p ⬝ᵥ y' := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k),
        ← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
      have : ∑ j ∈ Finset.univ.erase k, p ⬝ᵥ ys' j = ∑ j ∈ Finset.univ.erase k, p ⬝ᵥ ys j :=
        Finset.sum_congr rfl fun j hj => by
          rw [hys', Function.update_of_ne (Finset.ne_of_mem_erase hj)]
      rw [this, hys', Function.update_self]
      ring
    linarith
  · rintro ⟨ys, hys, rfl⟩
    refine ⟨⟨ys, fun j => (hys j).1, rfl⟩, ?_⟩
    rintro _ ⟨ys', hys', rfl⟩
    rw [dotProduct_finset_sum, dotProduct_finset_sum]
    exact Finset.sum_le_sum fun j _ => (hys j).2 _ (hys' j)

/-- **Proposition 5.E.1(i)** (MWG, p. 148), real form: if every `Y_j` is nonempty and profits are
bounded on each at `p`, the aggregate profits are bounded and `π*(p) = Σ_j π_j(p)`. -/
theorem proposition_5_E_1_i_real {Ys : Fin J → Set (Fin L → ℝ)} (hne : ∀ j, (Ys j).Nonempty)
    {p : Fin L → ℝ} (hb : ∀ j, BddAbove ((fun y => p ⬝ᵥ y) '' Ys j)) :
    BddAbove ((fun y => p ⬝ᵥ y) '' aggSet Ys) ∧ profit (aggSet Ys) p = ∑ j, profit (Ys j) p := by
  have hup : ∀ y ∈ aggSet Ys, p ⬝ᵥ y ≤ ∑ j, profit (Ys j) p := by
    rintro _ ⟨ys, hys, rfl⟩
    rw [dotProduct_finset_sum]
    exact Finset.sum_le_sum fun j _ => le_csSup (hb j) ⟨ys j, hys j, rfl⟩
  have hbdd : BddAbove ((fun y => p ⬝ᵥ y) '' aggSet Ys) :=
    ⟨_, by rintro _ ⟨y, hy, rfl⟩; exact hup y hy⟩
  refine ⟨hbdd, le_antisymm ?_ ?_⟩
  · obtain ⟨ys0, hys0⟩ : ∃ ys : Fin J → Fin L → ℝ, ∀ j, ys j ∈ Ys j :=
      ⟨fun j => (hne j).some, fun j => (hne j).some_mem⟩
    exact csSup_le ⟨_, ⟨_, ⟨ys0, hys0, rfl⟩, rfl⟩⟩ (by rintro _ ⟨y, hy, rfl⟩; exact hup y hy)
  · apply le_of_forall_pos_le_add
    intro ε hε
    have hεJ : 0 < ε / (J + 1) := by positivity
    have hex : ∀ j, ∃ y ∈ Ys j, profit (Ys j) p - ε / (J + 1) < p ⬝ᵥ y := by
      intro j
      obtain ⟨_, ⟨y, hy, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup ((hne j).image _)
        (show profit (Ys j) p - ε / (J + 1) < profit (Ys j) p by linarith)
      exact ⟨y, hy, hlt⟩
    choose ys hys hlt using hex
    have hmem : ∑ j, ys j ∈ aggSet Ys := ⟨ys, hys, rfl⟩
    have h1 : p ⬝ᵥ ∑ j, ys j ≤ profit (aggSet Ys) p := le_csSup hbdd ⟨_, hmem, rfl⟩
    rw [dotProduct_finset_sum] at h1
    have h2 : ∑ j, (profit (Ys j) p - ε / (J + 1)) ≤ ∑ j, p ⬝ᵥ ys j :=
      Finset.sum_le_sum fun j _ => (hlt j).le
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at h2
    have h3 : (J : ℝ) * (ε / (J + 1)) ≤ ε := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith
    linarith

theorem ereal_coe_sum (a : Fin J → ℝ) : ((∑ j, a j : ℝ) : EReal) = ∑ j, (a j : EReal) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, EReal.coe_add, ih]

theorem ereal_sum_ne_bot {x : Fin J → EReal} (h : ∀ j, x j ≠ ⊥) : ∑ j, x j ≠ ⊥ := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Fin.sum_univ_succ]
    exact EReal.add_ne_bot_iff.mpr ⟨h 0, ih fun j => h j.succ⟩

theorem ereal_sum_eq_top {x : Fin J → EReal} (h : ∀ j, x j ≠ ⊥) {k : Fin J} (hk : x k = ⊤) :
    ∑ j, x j = ⊤ := by
  classical
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k), hk]
  apply EReal.top_add_of_ne_bot
  induction (Finset.univ.erase k) using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact EReal.add_ne_bot_iff.mpr ⟨h a, ih⟩

theorem profitFn_ne_bot {Y : Set (Fin L → ℝ)} (hne : Y.Nonempty) (p : Fin L → ℝ) :
    profitFn Y p ≠ ⊥ := by
  obtain ⟨y, hy⟩ := hne
  exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (le_profitFn (p := p) hy)

/-- **Proposition 5.E.1(i)** (MWG, p. 148). For nonempty `Y_j` and every `p`, the aggregate
profit function is the sum of the individual ones: `π*(p) = Σ_j π_j(p)` in `(-∞, +∞]`. -/
theorem proposition_5_E_1_i {Ys : Fin J → Set (Fin L → ℝ)} (hne : ∀ j, (Ys j).Nonempty)
    (p : Fin L → ℝ) : profitFn (aggSet Ys) p = ∑ j, profitFn (Ys j) p := by
  have hneagg : (aggSet Ys).Nonempty :=
    ⟨_, ⟨fun j => (hne j).some, fun j => (hne j).some_mem, rfl⟩⟩
  by_cases hb : ∀ j, BddAbove ((fun y => p ⬝ᵥ y) '' Ys j)
  · obtain ⟨hbagg, heq⟩ := proposition_5_E_1_i_real hne hb
    rw [profitFn_eq_coe hneagg hbagg, heq, ereal_coe_sum]
    exact Finset.sum_congr rfl fun j _ => (profitFn_eq_coe (hne j) (hb j)).symm
  · push Not at hb
    obtain ⟨k, hk⟩ := hb
    have htop : profitFn (Ys k) p = ⊤ := profitFn_eq_top hk
    rw [ereal_sum_eq_top (fun j => profitFn_ne_bot (hne j) p) htop]
    apply profitFn_eq_top
    intro ⟨m, hm⟩
    apply hk
    refine ⟨m - ∑ j ∈ Finset.univ.erase k, p ⬝ᵥ (hne j).some, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    classical
    set ys := Function.update (fun j => (hne j).some) k y with hys
    have hmem : ∑ j, ys j ∈ aggSet Ys := ⟨ys, fun j => by
      by_cases hj : j = k
      · subst hj; simp [hys, hy]
      · simp [hys, hj, (hne j).some_mem], rfl⟩
    have h1 := hm ⟨_, hmem, rfl⟩
    simp only at h1
    rw [dotProduct_finset_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ k)] at h1
    have : ∑ j ∈ Finset.univ.erase k, p ⬝ᵥ ys j =
        ∑ j ∈ Finset.univ.erase k, p ⬝ᵥ (hne j).some :=
      Finset.sum_congr rfl fun j hj => by
        rw [hys, Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    rw [this, hys, Function.update_self] at h1
    simp only
    linarith

/-- **Section 5.E** (MWG, p. 147), the aggregate law of supply:
`(p - p')·[y(p) - y(p')] ≥ 0` for `y ∈ Σ_j y_j(p)` and `y' ∈ Σ_j y_j(p')`. -/
theorem aggregate_law_of_supply {Ys : Fin J → Set (Fin L → ℝ)} {p p' y y' : Fin L → ℝ}
    (hy : y ∈ aggSupply Ys p) (hy' : y' ∈ aggSupply Ys p') : 0 ≤ (p - p') ⬝ᵥ (y - y') := by
  rw [← proposition_5_E_1_ii] at hy hy'
  exact law_of_supply hy hy'

/-- **Section 5.E** (MWG, p. 147). Symmetry and positive semidefiniteness are preserved by
sums: if each `Dy_j(p)` is symmetric and positive semidefinite, so is `Σ_j Dy_j(p)`. -/
theorem sum_symm_psd (Ds : Fin J → Matrix (Fin L) (Fin L) ℝ)
    (hsym : ∀ j, ∀ a b, Ds j a b = Ds j b a) (hpsd : ∀ j, PosSemidefMWG (Ds j)) :
    (∀ a b, (∑ j, Ds j) a b = (∑ j, Ds j) b a) ∧ PosSemidefMWG (∑ j, Ds j) := by
  refine ⟨fun a b => ?_, fun z => ?_⟩
  · simp only [Matrix.sum_apply]
    exact Finset.sum_congr rfl fun j _ => hsym j a b
  · rw [Matrix.sum_mulVec, dotProduct_finset_sum]
    exact Finset.sum_nonneg fun j _ => hpsd j z

/-- If profits are finite near `p̄` and `π` has derivative `D` at `p̄`, every
profit-maximizing plan `ȳ` at `p̄` is the gradient: `D = (q ↦ ȳ·q)`. -/
theorem profit_fderiv_eq_of_mem_supply {Y : Set (Fin L → ℝ)} {p y : Fin L → ℝ}
    (hb : ∀ᶠ q in 𝓝 p, BddAbove ((fun y => q ⬝ᵥ y) '' Y))
    {D : (Fin L → ℝ) →L[ℝ] ℝ} (hD : HasFDerivAt (profit Y) D p) (hy : y ∈ supply Y p) :
    D = dualityDotCLM y := by
  have hmax : IsLocalMin (fun q => profit Y q - q ⬝ᵥ y) p := by
    filter_upwards [hb] with q hq
    rw [profit_eq_of_mem_supply hy, sub_self]
    exact sub_nonneg.mpr (le_csSup hq ⟨y, hy.1, rfl⟩)
  have hd := hD.sub (duality_hasFDerivAt_dot_left y p)
  have := hmax.hasFDerivAt_eq_zero hd
  have h2 : D = dualityDotCLM y := sub_eq_zero.mp this
  exact h2

/-- **Exercise 5.E.1** (MWG, p. 163). Assume each `π_j` is differentiable at `p̄` (finite nearby)
with gradient `g_j`, and `π* = Σ_j π_j` near `p̄`. Then every aggregate profit maximizer at `p̄`
is `Σ_j g_j`; with Hotelling's lemma `g_j = y_j(p̄)` this gives `y*(p̄) = Σ_j y_j(p̄)`. -/
theorem exercise_5_E_1 {Ys : Fin J → Set (Fin L → ℝ)} {p : Fin L → ℝ}
    {g : Fin J → Fin L → ℝ}
    (hd : ∀ j, HasFDerivAt (profit (Ys j)) (dualityDotCLM (g j)) p)
    (hsum : ∀ᶠ q in 𝓝 p, profit (aggSet Ys) q = ∑ j, profit (Ys j) q)
    (hb : ∀ᶠ q in 𝓝 p, BddAbove ((fun y => q ⬝ᵥ y) '' aggSet Ys))
    {y : Fin L → ℝ} (hy : y ∈ supply (aggSet Ys) p) : y = ∑ j, g j := by
  have hD : HasFDerivAt (profit (aggSet Ys)) (∑ j, dualityDotCLM (g j)) p := by
    have := HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ => hd j)
    exact this.congr_of_eventuallyEq hsum
  have h1 := profit_fderiv_eq_of_mem_supply hb hD hy
  have h2 : (∑ j, dualityDotCLM (g j)) = dualityDotCLM (L := L) (∑ j, g j) := by
    ext q
    simp only [FunLike.coe_sum, Finset.sum_apply, dualityDotCLM_apply]
    rw [dotProduct_comm, dotProduct_finset_sum]
    exact Finset.sum_congr rfl fun j _ => dotProduct_comm _ _
  rw [h2] at h1
  exact (dualityDotCLM_injective h1).symm

/-- Free disposal and convexity pass to the aggregate production set. -/
theorem aggSet_convex_freeDisposal {Ys : Fin J → Set (Fin L → ℝ)} (hc : ∀ j, Convex ℝ (Ys j))
    (hfd : ∀ j, FreeDisposal (Ys j)) (hJ : 0 < J) :
    Convex ℝ (aggSet Ys) ∧ FreeDisposal (aggSet Ys) := by
  classical
  constructor
  · rintro _ ⟨ys, hys, rfl⟩ _ ⟨ys', hys', rfl⟩ a b ha hb hab
    refine ⟨fun j => a • ys j + b • ys' j, fun j => hc j (hys j) (hys' j) ha hb hab, ?_⟩
    rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  · rintro _ ⟨ys, hys, rfl⟩ y' hy'
    set k : Fin J := ⟨0, hJ⟩
    refine ⟨Function.update ys k (ys k - (∑ j, ys j - y')), fun j => ?_, ?_⟩
    · by_cases hj : j = k
      · subst hj
        simp only [Function.update_self]
        exact hfd _ _ (hys _) _ (sub_le_self _ (sub_nonneg.mpr hy'))
      · simp only [Function.update_of_ne hj]
        exact hys j
    · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k), Function.update_self]
      have : ∑ j ∈ Finset.univ.erase k, Function.update ys k (ys k - (∑ j, ys j - y')) j =
          ∑ j ∈ Finset.univ.erase k, ys j :=
        Finset.sum_congr rfl fun j hj => Function.update_of_ne (Finset.ne_of_mem_erase hj) _ _
      rw [this, ← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
      abel

/-- **Exercise 5.E.3** (MWG, p. 163), corrected: if the `Y_j` are nonempty, convex, with free
disposal, and `Σ_j Y_j` is closed, then `Σ_j Y_j = {y : p·y ≤ Σ_j π_j(p) for all p ≥ 0}`. -/
theorem exercise_5_E_3 {Ys : Fin J → Set (Fin L → ℝ)} (hne : ∀ j, (Ys j).Nonempty)
    (hc : ∀ j, Convex ℝ (Ys j)) (hfd : ∀ j, FreeDisposal (Ys j)) (hJ : 0 < J)
    (hcl : IsClosed (aggSet Ys)) :
    aggSet Ys = {y | ∀ p : Fin L → ℝ, 0 ≤ p →
      ((p ⬝ᵥ y : ℝ) : EReal) ≤ ∑ j, profitFn (Ys j) p} := by
  obtain ⟨hcagg, hfdagg⟩ := aggSet_convex_freeDisposal hc hfd hJ
  rw [proposition_5_C_1_iii_nonneg hcl hcagg hfdagg]
  ext y
  simp only [Set.mem_ofPred_eq, proposition_5_E_1_i hne]

/-- **Exercise 5.E.3** (MWG, p. 163) with prices `p ≫ 0` as printed, under the extra hypothesis
that aggregate profits are bounded at some `p₀ ≫ 0`. -/
theorem exercise_5_E_3_pos {Ys : Fin J → Set (Fin L → ℝ)} (hne : ∀ j, (Ys j).Nonempty)
    (hc : ∀ j, Convex ℝ (Ys j)) (hfd : ∀ j, FreeDisposal (Ys j)) (hJ : 0 < J)
    (hcl : IsClosed (aggSet Ys)) {p₀ : Fin L → ℝ} (hp₀ : StrictlyPositive p₀)
    (hb₀ : BddAbove ((fun y => p₀ ⬝ᵥ y) '' aggSet Ys)) :
    aggSet Ys = {y | ∀ p : Fin L → ℝ, StrictlyPositive p →
      ((p ⬝ᵥ y : ℝ) : EReal) ≤ ∑ j, profitFn (Ys j) p} := by
  obtain ⟨hcagg, hfdagg⟩ := aggSet_convex_freeDisposal hc hfd hJ
  rw [proposition_5_C_1_iii hcl hcagg hfdagg hp₀ hb₀]
  ext y
  simp only [Set.mem_ofPred_eq, proposition_5_E_1_i hne]

/-- **Exercise 5.E.3** is false as printed (correction): for `J = 1` and `Y₁ = {y ∈ ℝ² : y₂ ≤ 0}`
(nonempty, convex, closed, free disposal), `(0, 1) ∉ Y₁` but `p·(0, 1) ≤ π₁(p) = +∞` for every
`p ≫ 0`. -/
theorem exercise_5_E_3_counterexample :
    let Ys : Fin 1 → Set (Fin 2 → ℝ) := fun _ => {y | y 1 ≤ 0}
    ![0, 1] ∉ aggSet Ys ∧ ∀ p : Fin 2 → ℝ, StrictlyPositive p →
      ((p ⬝ᵥ ![0, 1] : ℝ) : EReal) ≤ ∑ j, profitFn (Ys j) p := by
  intro Ys
  obtain ⟨-, -, -, -, htop, hnot, -⟩ := proposition_5_C_1_iii_counterexample
  refine ⟨?_, fun p hp => ?_⟩
  · rintro ⟨ys, hys, hsum⟩
    apply hnot
    rw [hsum, Fin.sum_univ_one]
    exact hys 0
  · rw [Fin.sum_univ_one]
    have := htop p hp
    simp only [Ys] at this ⊢
    rw [this]
    exact le_top

end MWG.Production

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Efficient production (MWG Section 5.F, pp. 149-152)

* **Definition 5.F.1** (`Efficient`) and weak efficiency (footnote 13, `WeaklyEfficient`).
* Efficient plans lie on the boundary of `Y` (`efficient_mem_frontier`), but not conversely
  (Figure 5.F.1(b), `frontier_not_efficient`).
* **Proposition 5.F.1** (first fundamental theorem, `proposition_5_F_1`); **Exercise 5.F.1**
  (`p ≥ 0, p ≠ 0` is not enough).
* **Proposition 5.F.2** (second fundamental theorem, `proposition_5_F_2`, via Chapter 3's
  separating hyperplane theorem M.G.2) and its weakly efficient form (footnote 13); the price
  vector cannot be chosen `≫ 0` (Figure 5.F.4, `figure_5_F_4`).
* The single-output illustration on p. 152 (`efficient_single_output_concave`).

Departure: Proposition 5.F.2 needs `L ≥ 1` (in `ℝ⁰` every plan is efficient and no `p ≠ 0`
exists, `proposition_5_F_2_needs_dimension`).
-/

namespace MWG.Production

open MWG.ClassicalDemand MWG.ConsumerChoice Filter Topology

variable {L : ℕ}

/-- **Definition 5.F.1** (MWG, p. 150). `y ∈ Y` is efficient if no `y' ∈ Y` has `y' ≥ y` and
`y' ≠ y`. -/
def Efficient (Y : Set (Fin L → ℝ)) (y : Fin L → ℝ) : Prop :=
  y ∈ Y ∧ ¬ ∃ y' ∈ Y, y ≤ y' ∧ y' ≠ y

/-- **Footnote 13** (MWG, p. 151). `y ∈ Y` is weakly efficient if no `y' ∈ Y` has `y' ≫ y`. -/
def WeaklyEfficient (Y : Set (Fin L → ℝ)) (y : Fin L → ℝ) : Prop :=
  y ∈ Y ∧ ¬ ∃ y' ∈ Y, ∀ i, y i < y' i

theorem Efficient.weaklyEfficient {Y : Set (Fin L → ℝ)} {y : Fin L → ℝ} (h : Efficient Y y)
    (hL : 0 < L) : WeaklyEfficient Y y := by
  refine ⟨h.1, fun ⟨y', hy', hlt⟩ => h.2 ⟨y', hy', fun i => (hlt i).le, fun he => ?_⟩⟩
  have := hlt ⟨0, hL⟩
  rw [he] at this
  exact lt_irrefl _ this

/-- **Section 5.F** (MWG, p. 150, Figure 5.F.1). Every efficient production plan is on the
boundary of `Y` (for `L ≥ 1`). -/
theorem efficient_mem_frontier {Y : Set (Fin L → ℝ)} {y : Fin L → ℝ} (h : Efficient Y y)
    (hL : 0 < L) : y ∈ frontier Y := by
  refine ⟨subset_closure h.1, fun hint => ?_⟩
  have hnhds : Y ∈ 𝓝 y := mem_interior_iff_mem_nhds.mp hint
  have hg : Continuous fun t : ℝ => y + t • (1 : Fin L → ℝ) := by fun_prop
  have hpre := hg.continuousAt (x := 0) (by simpa using hnhds)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hpre
  have hmem : ε / 2 ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith
  have hin : y + (ε / 2) • (1 : Fin L → ℝ) ∈ Y := hball hmem
  have hle : y ≤ y + (ε / 2) • (1 : Fin L → ℝ) := fun i => by
    simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
    linarith
  apply h.2 ⟨_, hin, hle, fun he => ?_⟩
  have := congrFun he ⟨0, hL⟩
  simp at this
  linarith

/-- **Figure 5.F.1(b)** (MWG, p. 150). Not every boundary point is efficient: `(-1, 0)` is on the
boundary of `ℝ²_-` but `0 ≥ (-1, 0)`. -/
theorem frontier_not_efficient :
    (![-1, 0] : Fin 2 → ℝ) ∈ frontier {y : Fin 2 → ℝ | y ≤ 0} ∧
      ¬ Efficient {y : Fin 2 → ℝ | y ≤ 0} ![-1, 0] := by
  have hcl : IsClosed {y : Fin 2 → ℝ | y ≤ 0} := isClosed_le continuous_id continuous_const
  have hmem : (![-1, 0] : Fin 2 → ℝ) ∈ {y : Fin 2 → ℝ | y ≤ 0} := by
    intro i; fin_cases i <;> simp
  refine ⟨⟨subset_closure hmem, fun hint => ?_⟩,
    fun h => h.2 ⟨0, show (0 : Fin 2 → ℝ) ≤ 0 from le_rfl, ?_, ?_⟩⟩
  · have hnhds := mem_interior_iff_mem_nhds.mp hint
    have hg : Continuous fun t : ℝ => (![-1, 0] : Fin 2 → ℝ) + t • (1 : Fin 2 → ℝ) := by
      fun_prop
    have hpre := hg.continuousAt (x := 0) (by simpa using hnhds)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hpre
    have hm : ε / 2 ∈ Metric.ball (0 : ℝ) ε := by
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos (by positivity)]
      linarith
    have := hball hm 1
    simp at this
    linarith
  · intro i; fin_cases i <;> simp
  · intro he
    have := congrFun he 0
    simp at this

/-- **Proposition 5.F.1** (MWG, p. 150). If `y ∈ Y` is profit maximizing for some `p ≫ 0`, then
`y` is efficient. Convexity is not needed (Figure 5.F.2). -/
theorem proposition_5_F_1 {Y : Set (Fin L → ℝ)} {p y : Fin L → ℝ} (hp : StrictlyPositive p)
    (hy : y ∈ supply Y p) : Efficient Y y := by
  refine ⟨hy.1, fun ⟨y', hy', hle, hne⟩ => ?_⟩
  obtain ⟨i, hi⟩ : ∃ i, y i < y' i := by
    by_contra h
    push Not at h
    exact hne (funext fun i => le_antisymm (h i) (hle i))
  have h1 : p ⬝ᵥ y < p ⬝ᵥ y' := by
    apply Finset.sum_lt_sum (fun j _ => mul_le_mul_of_nonneg_left (hle j) (hp j).le)
    exact ⟨i, Finset.mem_univ i, mul_lt_mul_of_pos_left hi (hp i)⟩
  exact absurd (hy.2 y' hy') (not_le.mpr h1)

/-- **Exercise 5.F.1** (MWG, p. 151). A plan can be profit maximizing for some `p ≥ 0`, `p ≠ 0`
and yet be inefficient: in `Y = ℝ²_-`, `y = (-1, 0)` maximizes profits at `p = (0, 1)`. -/
theorem exercise_5_F_1 :
    (0 : Fin 2 → ℝ) ≤ ![0, 1] ∧ (![0, 1] : Fin 2 → ℝ) ≠ 0 ∧
      (![-1, 0] : Fin 2 → ℝ) ∈ supply {y : Fin 2 → ℝ | y ≤ 0} ![0, 1] ∧
      ¬ Efficient {y : Fin 2 → ℝ | y ≤ 0} ![-1, 0] := by
  refine ⟨fun i => by fin_cases i <;> simp, fun h => by simpa using congrFun h 1,
    ⟨fun i => by fin_cases i <;> simp, fun y' hy' => ?_⟩, frontier_not_efficient.2⟩
  have h1 : y' 1 ≤ 0 := hy' 1
  simp [dotProduct, Fin.sum_univ_two, h1]

/-- **Proposition 5.F.2**, weakly efficient form (MWG, p. 151 and footnote 13). If `Y` is convex
and `y ∈ Y` is weakly efficient, then `y` is profit maximizing for some `p ≥ 0`, `p ≠ 0`
(`L ≥ 1`). -/
theorem proposition_5_F_2_weak (hL : 0 < L) {Y : Set (Fin L → ℝ)} (hc : Convex ℝ Y)
    {y : Fin L → ℝ} (hy : WeaklyEfficient Y y) :
    ∃ p : Fin L → ℝ, 0 ≤ p ∧ p ≠ 0 ∧ y ∈ supply Y p := by
  set P := {y' : Fin L → ℝ | ∀ i, y i < y' i} with hP
  have hPc : Convex ℝ P := by
    intro a ha b hb s t hs ht hst i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases hs.lt_or_eq with hs' | hs'
    · have h1 : y i < a i := ha i
      have h2 : y i < b i := hb i
      have h3 : s * y i + t * y i = y i := by rw [← add_mul, hst, one_mul]
      nlinarith [mul_lt_mul_of_pos_left h1 hs', mul_le_mul_of_nonneg_left h2.le ht]
    · subst hs'
      have ht1 : t = 1 := by linarith
      subst ht1
      simp only [zero_mul, one_mul, zero_add]
      exact hb i
  have hPne : P.Nonempty := ⟨y + 1, fun i => by simp⟩
  have hdisj : Disjoint P Y := Set.disjoint_left.mpr fun y' hy'P hy'Y => hy.2 ⟨y', hy'Y, hy'P⟩
  obtain ⟨p, hp0, c, hP', hY'⟩ := theorem_M_G_2_ii hL hPc hc hPne ⟨y, hy.1⟩ hdisj
  have hnonneg : 0 ≤ p := by
    intro l
    by_contra hl0
    have hl : p l < 0 := not_le.mp hl0
    set t := (|c| + |p ⬝ᵥ (y + 1)| + 1) / (-p l) with ht
    have htpos : 0 ≤ t := div_nonneg (by positivity) (by linarith)
    have hmem : y + 1 + t • Pi.single l 1 ∈ P := by
      intro i
      have : 0 ≤ (t • (Pi.single l 1 : Fin L → ℝ)) i := by
        simp only [Pi.smul_apply, smul_eq_mul]
        have hs1 : (0 : Fin L → ℝ) ≤ Pi.single l 1 := Pi.single_nonneg.mpr zero_le_one
        exact mul_nonneg htpos (hs1 i)
      simp only [Pi.add_apply, Pi.one_apply] at this ⊢
      linarith
    have := hP' _ hmem
    rw [dotProduct_add, dotProduct_smul, dotProduct_single, mul_one, smul_eq_mul] at this
    have h2 : t * p l = -(|c| + |p ⬝ᵥ (y + 1)| + 1) := by
      rw [ht, div_mul_eq_mul_div, div_neg, mul_div_assoc, div_self hl.ne, mul_one]
    rw [h2] at this
    linarith [neg_abs_le c, le_abs_self (p ⬝ᵥ (y + 1))]
  refine ⟨p, hnonneg, hp0, hy.1, fun y'' hy'' => ?_⟩
  have hc' : c ≤ p ⬝ᵥ y := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have hp1 : 0 ≤ p ⬝ᵥ (1 : Fin L → ℝ) := dot_nonneg_of_nonneg hnonneg (fun _ => zero_le_one)
    set δ := ε / (p ⬝ᵥ (1 : Fin L → ℝ) + 1) with hδ
    have hδpos : 0 < δ := by positivity
    have hmem : y + δ • (1 : Fin L → ℝ) ∈ P := fun i => by
      simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
      linarith
    have := hP' _ hmem
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul] at this
    have : δ * (p ⬝ᵥ (1 : Fin L → ℝ)) ≤ ε := by
      rw [hδ, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  exact (hY' y'' hy'').trans hc'

/-- **Proposition 5.F.2** (MWG, p. 151), second fundamental theorem for production. If `Y` is
convex, every efficient `y ∈ Y` is profit maximizing for some `p ≥ 0`, `p ≠ 0` (`L ≥ 1`). -/
theorem proposition_5_F_2 (hL : 0 < L) {Y : Set (Fin L → ℝ)} (hc : Convex ℝ Y)
    {y : Fin L → ℝ} (hy : Efficient Y y) :
    ∃ p : Fin L → ℝ, 0 ≤ p ∧ p ≠ 0 ∧ y ∈ supply Y p :=
  proposition_5_F_2_weak hL hc (hy.weaklyEfficient hL)

/-- **Proposition 5.F.2** needs `L ≥ 1` (correction): in `ℝ⁰` the plan `0` of `Y = {0}` is
efficient but there is no `p ≠ 0`. -/
theorem proposition_5_F_2_needs_dimension :
    Convex ℝ ({0} : Set (Fin 0 → ℝ)) ∧ Efficient ({0} : Set (Fin 0 → ℝ)) 0 ∧
      ∀ p : Fin 0 → ℝ, p = 0 :=
  ⟨convex_singleton 0, ⟨rfl, fun ⟨_, hy', _, hne⟩ => hne hy'⟩,
    fun _ => funext fun i => i.elim0⟩

/-- The convex technology `{y ∈ ℝ² : y₁ + (max{y₂, 0})² ≤ 0}` of Figure 5.F.4. -/
def figure5F4Set : Set (Fin 2 → ℝ) := {y | y 0 + (max (y 1) 0) ^ 2 ≤ 0}

/-- **Figure 5.F.4** (MWG, p. 152). The second part of Proposition 5.F.2 cannot be strengthened to
`p ≫ 0`: the convex set `Y = {y₁ + (max{y₂, 0})² ≤ 0}` has `0` efficient, `0` is profit maximizing
at `p = (1, 0)`, but at no `p ≫ 0`. -/
theorem figure_5_F_4 :
    Convex ℝ figure5F4Set ∧ Efficient figure5F4Set 0 ∧
      (0 : Fin 2 → ℝ) ∈ supply figure5F4Set ![1, 0] ∧
      ∀ p : Fin 2 → ℝ, StrictlyPositive p → (0 : Fin 2 → ℝ) ∉ supply figure5F4Set p := by
  refine ⟨?_, ⟨by simp [figure5F4Set], fun ⟨y', hy', hle, hne⟩ => ?_⟩, ⟨by simp [figure5F4Set],
    fun y' hy' => ?_⟩, fun p hp h0 => ?_⟩
  · intro y hy y' hy' a b ha hb hab
    simp only [figure5F4Set, Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      at hy hy' ⊢
    set u := max (y 1) 0
    set v := max (y' 1) 0
    have hu : 0 ≤ u := le_max_right _ _
    have hv : 0 ≤ v := le_max_right _ _
    have hmax : max (a * y 1 + b * y' 1) 0 ≤ a * u + b * v := by
      apply max_le
      · exact add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
          (mul_le_mul_of_nonneg_left (le_max_left _ _) hb)
      · positivity
    have h0 : 0 ≤ max (a * y 1 + b * y' 1) 0 := le_max_right _ _
    have hsq : (max (a * y 1 + b * y' 1) 0) ^ 2 ≤ (a * u + b * v) ^ 2 :=
      pow_le_pow_left₀ h0 hmax 2
    have hconv : (a * u + b * v) ^ 2 ≤ a * u ^ 2 + b * v ^ 2 := by
      have hb' : b = 1 - a := by linarith
      subst hb'
      nlinarith [mul_nonneg (mul_nonneg ha hb) (sq_nonneg (u - v))]
    nlinarith
  · have h0 : 0 ≤ y' 0 := hle 0
    have h1 : 0 ≤ y' 1 := hle 1
    have hy'0 : y' 0 + (max (y' 1) 0) ^ 2 ≤ 0 := hy'
    have hsq : 0 ≤ (max (y' 1) 0) ^ 2 := sq_nonneg _
    have hy0 : y' 0 = 0 := by linarith
    have hm : max (y' 1) 0 = 0 := by nlinarith
    have hy1 : y' 1 = 0 := by
      have := le_max_left (y' 1) 0
      linarith
    apply hne
    funext i
    fin_cases i <;> simp [hy0, hy1]
  · have hy'0 : y' 0 + (max (y' 1) 0) ^ 2 ≤ 0 := hy'
    have hsq : 0 ≤ (max (y' 1) 0) ^ 2 := sq_nonneg _
    simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_mul,
      zero_mul, add_zero, Pi.zero_apply, mul_zero]
    linarith
  · set t := p 1 / (2 * p 0) with ht
    have htpos : 0 < t := div_pos (hp 1) (by linarith [hp 0])
    have hmem : (![-(t ^ 2), t] : Fin 2 → ℝ) ∈ figure5F4Set := by
      simp only [figure5F4Set, Set.mem_ofPred_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
        max_eq_left htpos.le]
      linarith
    have := h0.2 _ hmem
    simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Pi.zero_apply, mul_zero, add_zero] at this
    have h2 : p 0 * t ^ 2 = p 1 * t / 2 := by
      rw [ht]; field_simp
    nlinarith [hp 0, hp 1]

/-- **Section 5.F** (MWG, p. 152). For a single-output technology with `f` concave on `ℝ^n_+`,
differentiable at `z̄ ≥ 0` with `∇f(z̄) ≫ 0`, the plan `(-z̄, f(z̄))` is efficient, and it is
profit maximizing at output price `1` and input prices `w = ∇f(z̄)`. -/
theorem efficient_single_output_concave {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hc : ConcaveOn ℝ {z : Fin n → ℝ | 0 ≤ z} f) {z : Fin n → ℝ} (hz : 0 ≤ z)
    (hf : DifferentiableAt ℝ f z) (hgrad : ∀ l, 0 < partialF f z l) :
    extendVec (-z) (f z) ∈ supply (singleOutputSet f) (extendVec (fun l => partialF f z l) 1) ∧
      Efficient (singleOutputSet f) (extendVec (-z) (f z)) := by
  set w : Fin n → ℝ := fun l => partialF f z l
  have hopt := foc_5_C_2_sufficient (w := w) hc zero_le_one hz hf (fun l => by simp [w])
    (by simp [w, dotProduct])
  have hprof : ∀ (z' : Fin n → ℝ) (q : ℝ),
      extendVec w 1 ⬝ᵥ extendVec (-z') q = q - w ⬝ᵥ z' := by
    intro z' q
    simp only [extendVec, dotProduct, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
      Pi.neg_apply, mul_neg, Finset.sum_neg_distrib, one_mul]
    ring
  have hmem : extendVec (-z) (f z) ∈ supply (singleOutputSet f) (extendVec w 1) := by
    refine ⟨mem_singleOutputSet.mpr ⟨hz, le_rfl⟩, fun y' hy' => ?_⟩
    rw [← extendVec_inputsOf y'] at hy' ⊢
    obtain ⟨hz', hq'⟩ := mem_singleOutputSet.mp hy'
    rw [hprof, hprof]
    have := hopt _ hz'
    linarith
  refine ⟨hmem, proposition_5_F_1 (fun i => ?_) hmem⟩
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [extendVec]
  · simp only [extendVec, Fin.snoc_castSucc]
    exact hgrad j

end MWG.Production

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Linear programming (MWG Mathematical Appendix, Section M.M, pp. 966-968)

Mathlib v4.34.0 has Farkas' lemma only for closed (proper) cones and does not prove that a
finitely generated cone is closed. Here:

* the cone `coneOf a = {Σ_i λ_i a_i : λ ≥ 0}` generated by finitely many vectors, the conic
  Carathéodory theorem (`coneOf_caratheodory`: a minimal representation uses linearly independent
  generators), and closedness (`isClosed_coneOf`);
* **Farkas' lemma** (`farkas`) from Chapter 3's separating hyperplane theorem, and the
  strictly positive separation of a cone meeting `ℝ^m_+` only at `0` (Stiemke,
  `exists_pos_of_cone_inter_nonneg`), used in Appendix 5.A;
* the primal (M.M.1) and dual (M.M.2) problems, weak duality (M.M.3) (`equation_M_M_3`), and
  **Theorem M.M.1** (`theorem_M_M_1`), with complementary slackness (M.M.4);
* footnotes 30 and 31, and the example of Figures M.M.1-M.M.2 (`example_M_M_figures`).

Correction: the proof of Theorem M.M.1 asserts `Aᵀλ̄ = f` for the multipliers; with the
constraints `x ≥ 0` only `Aᵀλ̄ ≥ f` holds (`theorem_M_M_1_proof_counterexample`).
-/

namespace MWG.Production

open MWG.ClassicalDemand MWG.ConsumerChoice Filter Topology

variable {ι : Type*} [Fintype ι] {m : ℕ}

/-- The convex cone generated by finitely many vectors `a_i ∈ ℝ^m`. -/
def coneOf (a : ι → Fin m → ℝ) : Set (Fin m → ℝ) :=
  {x | ∃ lam : ι → ℝ, 0 ≤ lam ∧ x = ∑ i, lam i • a i}

theorem zero_mem_coneOf (a : ι → Fin m → ℝ) : (0 : Fin m → ℝ) ∈ coneOf a :=
  ⟨0, le_rfl, by simp⟩

theorem generator_mem_coneOf (a : ι → Fin m → ℝ) (i : ι) : a i ∈ coneOf a := by
  classical
  exact ⟨Pi.single i 1, Pi.single_nonneg.mpr zero_le_one, by
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
    simp⟩

theorem convex_coneOf (a : ι → Fin m → ℝ) : Convex ℝ (coneOf a) := by
  rintro _ ⟨lam, hlam, rfl⟩ _ ⟨mu, hmu, rfl⟩ s t hs ht _
  refine ⟨s • lam + t • mu, add_nonneg (smul_nonneg hs hlam) (smul_nonneg ht hmu), ?_⟩
  simp only [Finset.smul_sum, smul_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul,
    Finset.sum_add_distrib]

theorem smul_mem_coneOf {a : ι → Fin m → ℝ} {x : Fin m → ℝ} (hx : x ∈ coneOf a) {t : ℝ}
    (ht : 0 ≤ t) : t • x ∈ coneOf a := by
  obtain ⟨lam, hlam, rfl⟩ := hx
  exact ⟨t • lam, smul_nonneg ht hlam, by simp [Finset.smul_sum, smul_smul]⟩

theorem add_mem_coneOf {a : ι → Fin m → ℝ} {x y : Fin m → ℝ} (hx : x ∈ coneOf a)
    (hy : y ∈ coneOf a) : x + y ∈ coneOf a := by
  obtain ⟨lam, hlam, rfl⟩ := hx
  obtain ⟨mu, hmu, rfl⟩ := hy
  exact ⟨lam + mu, add_nonneg hlam hmu, by simp [add_smul, Finset.sum_add_distrib]⟩

/-- Weights supported on `s`. -/
def SupportedOn (s : Finset ι) (lam : ι → ℝ) : Prop := ∀ i ∉ s, lam i = 0

/-- The generators indexed by `s` are linearly independent (in the form used here). -/
def IndepOn (a : ι → Fin m → ℝ) (s : Finset ι) : Prop :=
  ∀ g : ι → ℝ, SupportedOn s g → ∑ i, g i • a i = 0 → g = 0

/-- **Conic Carathéodory theorem.** Every element of `coneOf a` is a nonnegative combination of
a linearly independent subfamily of the generators. -/
theorem coneOf_caratheodory {a : ι → Fin m → ℝ} {x : Fin m → ℝ}
    (hx : x ∈ coneOf a) :
    ∃ s : Finset ι, IndepOn a s ∧ ∃ lam : ι → ℝ, 0 ≤ lam ∧ SupportedOn s lam ∧
      x = ∑ i, lam i • a i := by
  classical
  let P : Finset ι → Prop := fun s =>
    ∃ lam : ι → ℝ, 0 ≤ lam ∧ SupportedOn s lam ∧ x = ∑ i, lam i • a i
  have hex : ∃ n, ∃ s : Finset ι, s.card = n ∧ P s := by
    obtain ⟨lam, hlam, rfl⟩ := hx
    exact ⟨_, Finset.univ, rfl, lam, hlam, fun i hi => absurd (Finset.mem_univ i) hi, rfl⟩
  obtain ⟨s0, hcard, hP⟩ := Nat.find_spec hex
  refine ⟨s0, ?_, hP⟩
  obtain ⟨lam, hlam, hsupp, hxeq⟩ := hP
  -- all weights on `s0` are positive, by minimality
  have hpos : ∀ i ∈ s0, 0 < lam i := by
    intro i hi
    rcases (hlam i).lt_or_eq with h | h
    · exact h
    · exfalso
      have hlt : (s0.erase i).card < Nat.find hex := by
        rw [← hcard]
        exact Finset.card_erase_lt_of_mem hi
      apply Nat.find_min hex hlt
      refine ⟨s0.erase i, rfl, lam, hlam, fun j hj => ?_, hxeq⟩
      by_cases hji : j = i
      · subst hji; exact h.symm
      · exact hsupp j (fun hj0 => hj (Finset.mem_erase.mpr ⟨hji, hj0⟩))
  intro g hg hsum
  by_contra hg0
  -- choose a sign with a positive entry
  obtain ⟨g', hg'supp, hg'sum, i1, hi1, hg'pos⟩ : ∃ g' : ι → ℝ, SupportedOn s0 g' ∧
      ∑ i, g' i • a i = 0 ∧ ∃ i ∈ s0, 0 < g' i := by
    obtain ⟨i, hi⟩ : ∃ i, g i ≠ 0 := by
      by_contra h
      push Not at h
      exact hg0 (funext h)
    have his : i ∈ s0 := by
      by_contra hn
      exact hi (hg i hn)
    rcases lt_or_gt_of_ne hi with hneg | hposg
    · refine ⟨-g, fun j hj => by simp [hg j hj], ?_, i, his, by simp; linarith⟩
      simp only [Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, hsum, neg_zero]
    · exact ⟨g, hg, hsum, i, his, hposg⟩
  set T := s0.filter fun i => 0 < g' i with hT
  have hTne : T.Nonempty := ⟨i1, Finset.mem_filter.mpr ⟨hi1, hg'pos⟩⟩
  obtain ⟨i0, hi0T, hmin⟩ := Finset.exists_min_image T (fun i => lam i / g' i) hTne
  have hi0 := Finset.mem_filter.mp hi0T
  set θ := lam i0 / g' i0 with hθ
  have hθ0 : 0 ≤ θ := div_nonneg (hlam i0) hi0.2.le
  set lam' := lam - θ • g' with hlam'
  have hlam'nn : 0 ≤ lam' := by
    intro i
    simp only [hlam', Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    by_cases hi : i ∈ s0
    · by_cases hgi : 0 < g' i
      · have := hmin i (Finset.mem_filter.mpr ⟨hi, hgi⟩)
        rw [le_div_iff₀ hgi] at this
        linarith
      · rw [not_lt] at hgi
        have hli : 0 ≤ lam i := hlam i
        nlinarith [mul_nonneg hθ0 (neg_nonneg.mpr hgi)]
    · rw [hsupp i hi, hg'supp i hi]
      simp
  have hlam'0 : lam' i0 = 0 := by
    simp only [hlam', Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hθ]
    rw [div_mul_cancel₀ _ hi0.2.ne', sub_self]
  have hlt : (s0.erase i0).card < Nat.find hex := by
    rw [← hcard]
    exact Finset.card_erase_lt_of_mem hi0.1
  apply Nat.find_min hex hlt
  refine ⟨s0.erase i0, rfl, lam', hlam'nn, fun j hj => ?_, ?_⟩
  · by_cases hji : j = i0
    · subst hji; exact hlam'0
    · have hj0 : j ∉ s0 := fun hj0 => hj (Finset.mem_erase.mpr ⟨hji, hj0⟩)
      simp [hlam', hsupp j hj0, hg'supp j hj0]
  · simp only [hlam', Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_smul, Finset.sum_sub_distrib,
      mul_smul, ← Finset.smul_sum, hg'sum, smul_zero, sub_zero]
    exact hxeq

/-- Weights supported on `s`, as a submodule. -/
def suppSub (s : Finset ι) : Submodule ℝ (ι → ℝ) where
  carrier := {lam | SupportedOn s lam}
  add_mem' := fun ha hb i hi => by simp [ha i hi, hb i hi]
  zero_mem' := fun _ _ => rfl
  smul_mem' := fun c x hx i hi => by simp [hx i hi]

/-- The combination map restricted to weights supported on `s`. -/
noncomputable def comboOn (a : ι → Fin m → ℝ) (s : Finset ι) : suppSub s →ₗ[ℝ] (Fin m → ℝ) :=
  (Fintype.linearCombination ℝ a).comp (suppSub s).subtype

/-- **Section M.M** (MWG, p. 967; needed for Farkas' lemma). A finitely generated cone is
closed. -/
theorem isClosed_coneOf (a : ι → Fin m → ℝ) : IsClosed (coneOf a) := by
  classical
  have heq : coneOf a = ⋃ s ∈ Finset.univ.filter (fun s => IndepOn a s),
      comboOn a s '' {lam | 0 ≤ (lam : ι → ℝ)} := by
    ext x
    simp only [Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_image]
    constructor
    · intro hx
      obtain ⟨s, hind, lam, hlam, hsupp, rfl⟩ := coneOf_caratheodory hx
      exact ⟨s, hind, ⟨lam, hsupp⟩, hlam, by simp [comboOn, Fintype.linearCombination_apply]⟩
    · rintro ⟨s, -, lam, hlam, rfl⟩
      exact ⟨lam, hlam, by simp [comboOn, Fintype.linearCombination_apply]⟩
  rw [heq]
  refine isClosed_biUnion_finset fun s hs => ?_
  have hind : IndepOn a s := (Finset.mem_filter.mp hs).2
  have hker : LinearMap.ker (comboOn a s) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro lam hlam
    have := hind lam lam.2 (by simpa [comboOn, Fintype.linearCombination_apply] using hlam)
    exact Subtype.ext this
  have hemb := LinearMap.isClosedEmbedding_of_injective hker
  apply hemb.isClosedMap
  exact isClosed_le continuous_const continuous_subtype_val

/-- A cone containing `0` and closed under nonnegative scaling: a separating functional is
nonnegative on it. -/
theorem cone_sep_nonneg {C : Set (Fin m → ℝ)} (h0 : (0 : Fin m → ℝ) ∈ C)
    (hsm : ∀ x ∈ C, ∀ t : ℝ, 0 ≤ t → t • x ∈ C) {p : Fin m → ℝ} {c : ℝ}
    (hc : ∀ y ∈ C, c ≤ p ⬝ᵥ y) : c ≤ 0 ∧ ∀ y ∈ C, 0 ≤ p ⬝ᵥ y := by
  have hc0 : c ≤ 0 := by simpa using hc 0 h0
  refine ⟨hc0, fun y hy => ?_⟩
  by_contra hneg
  rw [not_le] at hneg
  set t := (|c| + 1) / (-(p ⬝ᵥ y)) with ht
  have htpos : 0 ≤ t := div_nonneg (by positivity) (by linarith)
  have := hc _ (hsm y hy t htpos)
  rw [dotProduct_smul, smul_eq_mul] at this
  have h2 : t * (p ⬝ᵥ y) = -(|c| + 1) := by
    rw [ht, div_mul_eq_mul_div, div_neg, mul_div_assoc, div_self hneg.ne, mul_one]
  rw [h2] at this
  linarith [neg_abs_le c]

/-- **Farkas' lemma** (the theorem of the alternative behind Section M.M). Exactly one holds:
`b` is a nonnegative combination of the `a_i`, or some `y` has `y·a_i ≤ 0` for all `i` and
`y·b > 0`. -/
theorem farkas (a : ι → Fin m → ℝ) (b : Fin m → ℝ) :
    (∃ lam : ι → ℝ, 0 ≤ lam ∧ b = ∑ i, lam i • a i) ↔
      ¬ ∃ y : Fin m → ℝ, (∀ i, y ⬝ᵥ a i ≤ 0) ∧ 0 < y ⬝ᵥ b := by
  constructor
  · rintro ⟨lam, hlam, rfl⟩ ⟨y, hy, hyb⟩
    rw [dotProduct_sum] at hyb
    have : ∑ i, y ⬝ᵥ (lam i • a i) ≤ 0 := Finset.sum_nonpos fun i _ => by
      rw [dotProduct_smul, smul_eq_mul]
      exact mul_nonpos_of_nonneg_of_nonpos (hlam i) (hy i)
    linarith
  · intro hno
    by_contra hb
    have hbC : b ∉ coneOf a := hb
    obtain ⟨p, c, hpb, hpC⟩ := separation_section_3_F (isClosed_coneOf a) (convex_coneOf a) hbC
    obtain ⟨hc0, hnn⟩ := cone_sep_nonneg (zero_mem_coneOf a)
      (fun x hx t ht => smul_mem_coneOf hx ht) hpC
    apply hno
    refine ⟨-p, fun i => ?_, ?_⟩
    · rw [neg_dotProduct]
      linarith [hnn _ (generator_mem_coneOf a i)]
    · rw [neg_dotProduct]
      linarith

/-- Strictly positive separation (Stiemke): if the cone generated by the `a_i` meets `ℝ^m_+`
only at `0`, there is `p ≫ 0` with `p·a_i ≤ 0` for every `i`. -/
theorem exists_pos_of_cone_inter_nonneg (a : ι → Fin m → ℝ)
    (h : ∀ x ∈ coneOf a, 0 ≤ x → x = 0) :
    ∃ p : Fin m → ℝ, StrictlyPositive p ∧ ∀ i, p ⬝ᵥ a i ≤ 0 := by
  classical
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    exact ⟨0, fun i => i.elim0, fun i => by simp⟩
  set E : Set (Fin m → ℝ) := Set.range fun j : Fin m => (Pi.single j 1 : Fin m → ℝ) with hE
  set Δ := convexHull ℝ E with hΔ
  have hΔc : IsCompact Δ := (Set.finite_range _).isCompact_convexHull ℝ
  have hΔsub : Δ ⊆ {x | 0 ≤ x ∧ ∑ j, x j = 1} := by
    apply convexHull_min
    · rintro _ ⟨j, rfl⟩
      exact ⟨Pi.single_nonneg.mpr zero_le_one, by simp⟩
    · intro x hx y hy s t hs ht hst
      refine ⟨add_nonneg (smul_nonneg hs hx.1) (smul_nonneg ht hy.1), ?_⟩
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum, hx.2, hy.2, mul_one, hst]
  have hdisj : Disjoint Δ (coneOf a) := by
    rw [Set.disjoint_left]
    intro x hxΔ hxC
    obtain ⟨hx0, hx1⟩ := hΔsub hxΔ
    have := h x hxC hx0
    rw [this] at hx1
    simp at hx1
  obtain ⟨f, u, v, hfΔ, huv, hfC⟩ := geometric_hahn_banach_compact_closed
    (convex_convexHull ℝ E) hΔc (convex_coneOf a) (isClosed_coneOf a) hdisj
  obtain ⟨q, hq⟩ := duality_exists_dot_of_clm f
  have hqC : ∀ y ∈ coneOf a, v ≤ q ⬝ᵥ y := fun y hy => by rw [← hq]; exact (hfC y hy).le
  obtain ⟨hv0, hnn⟩ := cone_sep_nonneg (zero_mem_coneOf a)
    (fun x hx t ht => smul_mem_coneOf hx ht) hqC
  refine ⟨-q, fun j => ?_, fun i => ?_⟩
  · have hj : (Pi.single j 1 : Fin m → ℝ) ∈ Δ := subset_convexHull ℝ E ⟨j, rfl⟩
    have := hfΔ _ hj
    rw [hq, dotProduct_single, mul_one] at this
    simp only [Pi.neg_apply]
    linarith
  · rw [neg_dotProduct]
    linarith [hnn _ (generator_mem_coneOf a i)]

/-! ### Linear programs -/

variable {K N : ℕ}

open Matrix in
/-- **(M.M.1)** (MWG, p. 966). The feasible set of the primal problem
`max f·x` s.t. `Ax ≤ c`, `x ≥ 0`. -/
def primalFeasible (A : Matrix (Fin K) (Fin N) ℝ) (c : Fin K → ℝ) : Set (Fin N → ℝ) :=
  {x | 0 ≤ x ∧ A *ᵥ x ≤ c}

open Matrix in
/-- **(M.M.2)** (MWG, p. 967). The feasible set of the dual problem
`min c·λ` s.t. `Aᵀλ ≥ f`, `λ ≥ 0`. -/
def dualFeasible (A : Matrix (Fin K) (Fin N) ℝ) (f : Fin N → ℝ) : Set (Fin K → ℝ) :=
  {lam | 0 ≤ lam ∧ f ≤ Aᵀ *ᵥ lam}

open Matrix in
/-- **(M.M.3)** (MWG, p. 967), weak duality: for primal-feasible `x` and dual-feasible `λ`,
`f·x ≤ (Aᵀλ)·x = λ·(Ax) ≤ λ·c`. -/
theorem equation_M_M_3 {A : Matrix (Fin K) (Fin N) ℝ} {c : Fin K → ℝ} {f : Fin N → ℝ}
    {x : Fin N → ℝ} (hx : x ∈ primalFeasible A c) {lam : Fin K → ℝ}
    (hlam : lam ∈ dualFeasible A f) : f ⬝ᵥ x ≤ c ⬝ᵥ lam := by
  have h1 : f ⬝ᵥ x ≤ (Aᵀ *ᵥ lam) ⬝ᵥ x :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hlam.2 i) (hx.1 i)
  have h2 : (Aᵀ *ᵥ lam) ⬝ᵥ x = lam ⬝ᵥ (A *ᵥ x) := by
    rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]
  have h3 : lam ⬝ᵥ (A *ᵥ x) ≤ lam ⬝ᵥ c :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hx.2 i) (hlam.1 i)
  rw [dotProduct_comm c lam]
  linarith

open Matrix in
/-- **Theorem M.M.1 (duality theorem of linear programming)** (MWG, p. 968). If the primal
problem (M.M.1) attains its maximum `v` (at `x̄`), then the dual problem (M.M.2) attains its
minimum, with the same value `v`. No constraint qualification is needed (footnote 31). -/
theorem theorem_M_M_1 {A : Matrix (Fin K) (Fin N) ℝ} {c : Fin K → ℝ} {f : Fin N → ℝ}
    {x : Fin N → ℝ} (hx : x ∈ primalFeasible A c)
    (hmax : ∀ x' ∈ primalFeasible A c, f ⬝ᵥ x' ≤ f ⬝ᵥ x) :
    ∃ lam ∈ dualFeasible A f, c ⬝ᵥ lam = f ⬝ᵥ x ∧
      ∀ lam' ∈ dualFeasible A f, c ⬝ᵥ lam ≤ c ⬝ᵥ lam' := by
  classical
  set v := f ⬝ᵥ x with hv
  -- generators in `ℝ^{N+1}`
  let a : Fin K ⊕ Fin N ⊕ Unit → Fin (N + 1) → ℝ :=
    Sum.elim (fun k => extendVec (fun n => A k n) (c k))
      (Sum.elim (fun n => extendVec (-Pi.single n 1) 0) fun _ => extendVec 0 1)
  have hcomb : ∀ (lam : Fin K → ℝ) (σ : Fin N → ℝ) (τ : ℝ),
      ∑ i, (Sum.elim lam (Sum.elim σ fun _ => τ)) i • a i =
        extendVec (Aᵀ *ᵥ lam - σ) (c ⬝ᵥ lam + τ) := by
    intro lam σ τ
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, a, extendVec_smul, Finset.univ_unique,
      Finset.sum_singleton]
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Finset.sum_apply, Pi.add_apply, extendVec, Fin.snoc_last, dotProduct]
      simp only [mul_zero, Finset.sum_const_zero, mul_one]
      have hc : ∀ k, lam k * c k = c k * lam k := fun k => mul_comm _ _
      simp only [hc]
      ring
    · simp only [Finset.sum_apply, Pi.add_apply, extendVec, Fin.snoc_castSucc, Pi.smul_apply,
        Pi.neg_apply, smul_eq_mul, Pi.zero_apply, mul_zero, add_zero, Matrix.mulVec,
        dotProduct, Matrix.transpose_apply, Pi.sub_apply]
      rw [sub_eq_add_neg]
      congr 1
      · exact Finset.sum_congr rfl fun k _ => by ring
      · rw [Finset.sum_eq_single j (fun n _ hn => by simp [Ne.symm hn])
          (by simp)]
        simp
  have hfeas : ∃ lam : Fin K ⊕ Fin N ⊕ Unit → ℝ, 0 ≤ lam ∧
      extendVec f v = ∑ i, lam i • a i := by
    rw [farkas]
    rintro ⟨y, hy, hyb⟩
    set x' : Fin N → ℝ := fun n => y (Fin.castSucc n) with hx'
    set s := y (Fin.last N) with hs
    have hyeq : y = extendVec x' s := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [extendVec, hs]
      · simp [extendVec, hx']
    have hdot : ∀ (u : Fin N → ℝ) (t : ℝ), y ⬝ᵥ extendVec u t = x' ⬝ᵥ u + s * t := by
      intro u t
      rw [hyeq]
      simp only [extendVec, dotProduct, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
    have hk : ∀ k, (A *ᵥ x') k + s * c k ≤ 0 := by
      intro k
      have := hy (Sum.inl k)
      simp only [a, Sum.elim_inl, hdot] at this
      simpa [Matrix.mulVec, dotProduct, mul_comm] using this
    have hn : 0 ≤ x' := by
      intro n
      have := hy (Sum.inr (Sum.inl n))
      simp only [a, Sum.elim_inr, Sum.elim_inl, hdot, dotProduct_neg, dotProduct_single,
        mul_one, mul_zero, add_zero] at this
      simp only [Pi.zero_apply]
      linarith
    have hs0 : s ≤ 0 := by
      have := hy (Sum.inr (Sum.inr ()))
      simp only [a, Sum.elim_inr, hdot, dotProduct_zero, mul_one, zero_add] at this
      exact this
    have hpos : 0 < f ⬝ᵥ x' + s * v := by
      rw [hdot] at hyb
      rwa [dotProduct_comm] at hyb
    rcases hs0.lt_or_eq with hsneg | hszero
    · -- `x'/(-s)` is primal feasible with a higher value
      set r := -s with hr
      have hrpos : 0 < r := by linarith
      have hfe : r⁻¹ • x' ∈ primalFeasible A c := by
        refine ⟨smul_nonneg (inv_nonneg.mpr hrpos.le) hn, fun k => ?_⟩
        rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, inv_mul_le_iff₀ hrpos]
        linarith [hk k]
      have := hmax _ hfe
      rw [dotProduct_smul, smul_eq_mul, inv_mul_le_iff₀ hrpos] at this
      nlinarith
    · -- `x + x'` is primal feasible with a higher value
      rw [hszero] at hk hpos
      have hfe : x + x' ∈ primalFeasible A c := by
        refine ⟨add_nonneg hx.1 hn, fun k => ?_⟩
        rw [Matrix.mulVec_add, Pi.add_apply]
        have := hk k
        have := hx.2 k
        simp only [zero_mul, add_zero] at *
        linarith
      have := hmax _ hfe
      rw [dotProduct_add] at this
      simp only [zero_mul, add_zero] at hpos
      linarith
  obtain ⟨μ, hμ, hμeq⟩ := hfeas
  set lam : Fin K → ℝ := fun k => μ (Sum.inl k)
  set σ : Fin N → ℝ := fun n => μ (Sum.inr (Sum.inl n))
  set τ := μ (Sum.inr (Sum.inr ()))
  have hμsplit : μ = Sum.elim lam (Sum.elim σ fun _ => τ) := by
    funext i
    rcases i with k | n | u
    · rfl
    · rfl
    · cases u; rfl
  rw [hμsplit, hcomb, extendVec_inj] at hμeq
  have hlamF : lam ∈ dualFeasible A f := by
    refine ⟨fun k => hμ (Sum.inl k), fun n => ?_⟩
    have h1 := congrFun hμeq.1 n
    have h2 : 0 ≤ σ n := hμ (Sum.inr (Sum.inl n))
    simp only [Pi.sub_apply] at h1
    linarith
  have hle : c ⬝ᵥ lam ≤ v := by
    have h2 : 0 ≤ τ := hμ (Sum.inr (Sum.inr ()))
    linarith [hμeq.2]
  have hge : v ≤ c ⬝ᵥ lam := equation_M_M_3 hx hlamF
  refine ⟨lam, hlamF, le_antisymm hle hge, fun lam' hlam' => ?_⟩
  have := equation_M_M_3 hx hlam'
  linarith

open Matrix in
/-- **(M.M.4)** (MWG, p. 968), complementary slackness: at a primal optimum `x̄` and a dual
optimum `λ̄` with equal values, `λ̄·(c - Ax̄) = 0` and `(Aᵀλ̄ - f)·x̄ = 0`. -/
theorem equation_M_M_4 {A : Matrix (Fin K) (Fin N) ℝ} {c : Fin K → ℝ} {f : Fin N → ℝ}
    {x : Fin N → ℝ} (hx : x ∈ primalFeasible A c) {lam : Fin K → ℝ}
    (hlam : lam ∈ dualFeasible A f) (heq : c ⬝ᵥ lam = f ⬝ᵥ x) :
    lam ⬝ᵥ (c - A *ᵥ x) = 0 ∧ (Aᵀ *ᵥ lam - f) ⬝ᵥ x = 0 := by
  have h1 : 0 ≤ (Aᵀ *ᵥ lam - f) ⬝ᵥ x :=
    Finset.sum_nonneg fun i _ => mul_nonneg (sub_nonneg.mpr (hlam.2 i)) (hx.1 i)
  have h2 : 0 ≤ lam ⬝ᵥ (c - A *ᵥ x) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hlam.1 i) (sub_nonneg.mpr (hx.2 i))
  have h3 : (Aᵀ *ᵥ lam) ⬝ᵥ x = lam ⬝ᵥ (A *ᵥ x) := by
    rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]
  have hsum : (Aᵀ *ᵥ lam - f) ⬝ᵥ x + lam ⬝ᵥ (c - A *ᵥ x) = 0 := by
    rw [sub_dotProduct, dotProduct_sub, h3, dotProduct_comm lam c, heq]
    ring
  constructor <;> linarith

open Matrix in
/-- **Theorem M.M.1**, the printed proof (correction): the multipliers need not satisfy
`Aᵀλ̄ = f`. For `max -x` s.t. `x ≤ 1`, `x ≥ 0` (`N = K = 1`), `x̄ = 0` is optimal, but no `λ ≥ 0`
has `Aᵀλ = f`; the dual optimum `λ̄ = 0` has `Aᵀλ̄ = 0 > -1 = f`. -/
theorem theorem_M_M_1_proof_counterexample :
    let A : Matrix (Fin 1) (Fin 1) ℝ := 1
    let c : Fin 1 → ℝ := 1
    let f : Fin 1 → ℝ := -1
    (0 : Fin 1 → ℝ) ∈ primalFeasible A c ∧
      (∀ x' ∈ primalFeasible A c, f ⬝ᵥ x' ≤ f ⬝ᵥ 0) ∧
      ¬ ∃ lam : Fin 1 → ℝ, 0 ≤ lam ∧ Aᵀ *ᵥ lam = f := by
  intro A c f
  refine ⟨⟨le_rfl, fun i => by simp [A, c]⟩, fun x' hx' => ?_, ?_⟩
  · have h0 : (0 : ℝ) ≤ x' 0 := hx'.1 0
    simp only [f, dotProduct, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
      Finset.sum_singleton, Pi.neg_apply, Pi.one_apply, neg_mul, one_mul, Pi.zero_apply,
      mul_zero, Left.neg_nonpos_iff]
    exact h0
  · rintro ⟨lam, hlam, h⟩
    have h1 := congrFun h 0
    have h2 : (0 : ℝ) ≤ lam 0 := hlam 0
    simp [A, f] at h1
    linarith

/-- **Footnote 30** (MWG, p. 966). The form (M.M.1) is general: an equality `a·x = b` is the pair
of inequalities `a·x ≤ b`, `-a·x ≤ -b`, and a variable unrestricted in sign is the difference
of two nonnegative variables. -/
theorem footnote_M_M_30 (a x : Fin N → ℝ) (b : ℝ) (t : ℝ) :
    (a ⬝ᵥ x = b ↔ a ⬝ᵥ x ≤ b ∧ (-a) ⬝ᵥ x ≤ -b) ∧
      ∃ t₁ t₂ : ℝ, 0 ≤ t₁ ∧ 0 ≤ t₂ ∧ t = t₁ - t₂ := by
  refine ⟨?_, max t 0, max (-t) 0, le_max_right _ _, le_max_right _ _, ?_⟩
  · rw [neg_dotProduct]
    constructor
    · intro h; constructor <;> linarith
    · rintro ⟨h1, h2⟩; linarith
  · rcases le_total t 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring

open Matrix in
/-- **Figures M.M.1 and M.M.2** (MWG, pp. 967-968). For `max x₁ + x₂` s.t. `2x₁ + x₂ ≤ 4`,
`x₁ + 3x₂ ≤ 7`, `x ≥ 0`, the maximizer is `x̄ = (1, 2)` with value `3`; the dual
`min 4λ₁ + 7λ₂` s.t. `2λ₁ + λ₂ ≥ 1`, `λ₁ + 3λ₂ ≥ 1`, `λ ≥ 0` has minimizer `λ̄ = (2/5, 1/5)`, value
`3`. -/
theorem example_M_M_figures :
    let A : Matrix (Fin 2) (Fin 2) ℝ := !![2, 1; 1, 3]
    let c : Fin 2 → ℝ := ![4, 7]
    let f : Fin 2 → ℝ := ![1, 1]
    ![1, 2] ∈ primalFeasible A c ∧ (∀ x ∈ primalFeasible A c, f ⬝ᵥ x ≤ f ⬝ᵥ ![1, 2]) ∧
      f ⬝ᵥ ![1, 2] = 3 ∧ ![2 / 5, 1 / 5] ∈ dualFeasible A f ∧
      (∀ lam ∈ dualFeasible A f, c ⬝ᵥ ![2 / 5, 1 / 5] ≤ c ⬝ᵥ lam) ∧ c ⬝ᵥ ![2 / 5, 1 / 5] = 3 := by
  intro A c f
  have hxF : (![1, 2] : Fin 2 → ℝ) ∈ primalFeasible A c := by
    refine ⟨fun i => by fin_cases i <;> norm_num, fun i => ?_⟩
    fin_cases i <;> simp [A, c, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num
  have hlF : (![2 / 5, 1 / 5] : Fin 2 → ℝ) ∈ dualFeasible A f := by
    refine ⟨fun i => by fin_cases i <;> norm_num, fun i => ?_⟩
    fin_cases i <;> simp [A, f, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num
  have hv1 : f ⬝ᵥ ![1, 2] = 3 := by simp [f, dotProduct, Fin.sum_univ_two]; norm_num
  have hv2 : c ⬝ᵥ ![2 / 5, 1 / 5] = 3 := by simp [c, dotProduct, Fin.sum_univ_two]; norm_num
  refine ⟨hxF, fun x hx => ?_, hv1, hlF, fun lam hlam => ?_, hv2⟩
  · rw [hv1, ← hv2]
    exact equation_M_M_3 hx hlF
  · rw [hv2, ← hv1]
    exact equation_M_M_3 hxF hlam

end MWG.Production

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The linear activity model (MWG Appendix 5.A, pp. 154-158)

A technology generated by finitely many elementary activities `a_i ∈ ℝ^L` (with or without the
disposal activities `-e_l`) is `coneOf a`, a polyhedral cone.

* Profit maximization in the linear activity model (p. 154): a profit-maximizing plan exists iff
  `p·a_i ≤ 0` for every activity (`activity_supply_nonempty_iff`); with the disposal activities
  this needs `p ≥ 0` (`disposal_supply_nonempty_iff`); activities with `p·a_i < 0` are not used,
  and `y(p)` is the cone generated by the zero-profit activities `A(p)` (`activity_supply_eq`).
* The "significant result that we shall not prove" (p. 155): in the linear activity model every
  efficient plan is profit maximizing for some `p ≫ 0` (`linear_activity_efficient_pos_price`),
  via the strictly positive separation of Section M.M.
* Leontief's input-output model (pp. 155-157): the matrix `A` and vector `b` built from the
  activities (`leontief_from_activities`), the production set (`leontiefSet`), **Proposition
  5.AA.1** and its Neumann-series proof (via Chapter 2's Theorem M.D.5(v)), the small-type
  characterization of producible final demands, and **Example 5.AA.1**.
* The linear-programming production function and its dual variables as marginal productivities
  (p. 158, `lp_dual_supergradient`, `lp_dual_marginal_products`).
-/

namespace MWG.Production

open MWG.ClassicalDemand MWG.ConsumerChoice Filter Topology

variable {ι : Type*} [Fintype ι] {L : ℕ}

/-- The disposal activities `-e_l` (p. 154) appended to the elementary activities. -/
def withDisposal {M : ℕ} (a : Fin M → Fin L → ℝ) : Fin M ⊕ Fin L → Fin L → ℝ :=
  Sum.elim a fun l => -Pi.single l 1

/-- **Appendix 5.A** (MWG, p. 154). The production set of the linear activity model is a convex
cone with constant returns to scale. -/
theorem activity_convexCone (a : ι → Fin L → ℝ) :
    Convex ℝ (coneOf a) ∧ ConstantReturns (coneOf a) ∧ IsConvexCone (coneOf a) := by
  have hcr : ConstantReturns (coneOf a) := fun y hy t ht => smul_mem_coneOf hy ht
  refine ⟨convex_coneOf a, hcr, (isConvexCone_iff _).mpr ⟨convex_coneOf a, hcr⟩⟩

/-- In the linear activity model, profits at `p` are `Σ λ_i (p·a_i)`. -/
theorem activity_profit (a : ι → Fin L → ℝ) (p : Fin L → ℝ) (lam : ι → ℝ) :
    p ⬝ᵥ ∑ i, lam i • a i = ∑ i, lam i * (p ⬝ᵥ a i) := by
  rw [dotProduct_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [dotProduct_smul, smul_eq_mul]

/-- **Appendix 5.A** (MWG, p. 154). A profit-maximizing plan exists in the linear activity model
if and only if `p·a_i ≤ 0` for every activity. -/
theorem activity_supply_nonempty_iff (a : ι → Fin L → ℝ) (p : Fin L → ℝ) :
    (supply (coneOf a) p).Nonempty ↔ ∀ i, p ⬝ᵥ a i ≤ 0 := by
  classical
  constructor
  · rintro ⟨y, hy⟩ i
    by_contra hpos
    rw [not_le] at hpos
    have := hy.2 _ (add_mem_coneOf hy.1 (generator_mem_coneOf a i))
    rw [dotProduct_add] at this
    linarith
  · intro h
    refine ⟨0, zero_mem_coneOf a, ?_⟩
    rintro _ ⟨lam, hlam, rfl⟩
    rw [activity_profit, dotProduct_zero]
    exact Finset.sum_nonpos fun i _ => mul_nonpos_of_nonneg_of_nonpos (hlam i) (h i)

/-- **Appendix 5.A** (MWG, p. 154). With the disposal activities, a profit-maximizing plan exists
iff `p ≥ 0` and `p·a_m ≤ 0` for every elementary activity. -/
theorem disposal_supply_nonempty_iff {M : ℕ} (a : Fin M → Fin L → ℝ) (p : Fin L → ℝ) :
    (supply (coneOf (withDisposal a)) p).Nonempty ↔ 0 ≤ p ∧ ∀ m, p ⬝ᵥ a m ≤ 0 := by
  rw [activity_supply_nonempty_iff]
  constructor
  · intro h
    refine ⟨fun l => ?_, fun m => h (Sum.inl m)⟩
    have := h (Sum.inr l)
    simp only [withDisposal, Sum.elim_inr, dotProduct_neg, dotProduct_single, mul_one,
      neg_nonpos] at this
    exact this
  · rintro ⟨hp, ha⟩ i
    rcases i with m | l
    · exact ha m
    · simp only [withDisposal, Sum.elim_inr, dotProduct_neg, dotProduct_single, mul_one,
        neg_nonpos]
      exact hp l

/-- **Appendix 5.A** (MWG, p. 154). If `p·a_i ≤ 0` for all activities, the maximal profit is `0`
and in any representation `y = Σ λ_i a_i` of a profit-maximizing plan, `λ_i = 0` whenever
`p·a_i < 0`. -/
theorem activity_level_zero {a : ι → Fin L → ℝ} {p : Fin L → ℝ} (h : ∀ i, p ⬝ᵥ a i ≤ 0)
    {lam : ι → ℝ} (hlam : 0 ≤ lam) (hy : ∑ i, lam i • a i ∈ supply (coneOf a) p) :
    p ⬝ᵥ ∑ i, lam i • a i = 0 ∧ ∀ i, p ⬝ᵥ a i < 0 → lam i = 0 := by
  have h0 := hy.2 0 (zero_mem_coneOf a)
  rw [dotProduct_zero] at h0
  have hle : ∑ i, lam i * (p ⬝ᵥ a i) ≤ 0 :=
    Finset.sum_nonpos fun i _ => mul_nonpos_of_nonneg_of_nonpos (hlam i) (h i)
  rw [activity_profit] at h0 ⊢
  have hsum : ∑ i, lam i * (p ⬝ᵥ a i) = 0 := le_antisymm hle h0
  refine ⟨hsum, fun i hi => ?_⟩
  have hterm := (Finset.sum_eq_zero_iff_of_nonpos fun j _ =>
    mul_nonpos_of_nonneg_of_nonpos (hlam j) (h j)).mp hsum i (Finset.mem_univ i)
  rcases mul_eq_zero.mp hterm with h1 | h1
  · exact h1
  · exact absurd h1 hi.ne

/-- **Appendix 5.A** (MWG, p. 154). If `p·a_i ≤ 0` for all activities, the supply set `y(p)` is
the cone generated by the zero-profit activities `A(p) = {a_i : p·a_i = 0}`. -/
theorem activity_supply_eq {a : ι → Fin L → ℝ} {p : Fin L → ℝ} (h : ∀ i, p ⬝ᵥ a i ≤ 0)
    (y : Fin L → ℝ) :
    y ∈ supply (coneOf a) p ↔
      ∃ lam : ι → ℝ, 0 ≤ lam ∧ (∀ i, p ⬝ᵥ a i ≠ 0 → lam i = 0) ∧ y = ∑ i, lam i • a i := by
  constructor
  · intro hy
    obtain ⟨lam, hlam, rfl⟩ := hy.1
    obtain ⟨-, hz⟩ := activity_level_zero h hlam hy
    exact ⟨lam, hlam, fun i hi => hz i (lt_of_le_of_ne (h i) hi), rfl⟩
  · rintro ⟨lam, hlam, hzero, rfl⟩
    refine ⟨⟨lam, hlam, rfl⟩, ?_⟩
    rintro _ ⟨mu, hmu, rfl⟩
    rw [activity_profit, activity_profit]
    have h1 : ∑ i, lam i * (p ⬝ᵥ a i) = 0 := Finset.sum_eq_zero fun i _ => by
      by_cases hi : p ⬝ᵥ a i = 0
      · rw [hi, mul_zero]
      · rw [hzero i hi, zero_mul]
    rw [h1]
    exact Finset.sum_nonpos fun i _ => mul_nonpos_of_nonneg_of_nonpos (hmu i) (h i)

/-- **Appendix 5.A** (MWG, p. 155), the result stated without proof: in the linear activity
model the converse of Proposition 5.F.1 holds exactly. Every efficient `y ∈ Y` is profit
maximizing for some `p ≫ 0` (strengthening Proposition 5.F.2). -/
theorem linear_activity_efficient_pos_price (a : ι → Fin L → ℝ) {y : Fin L → ℝ}
    (hy : Efficient (coneOf a) y) :
    ∃ p : Fin L → ℝ, StrictlyPositive p ∧ y ∈ supply (coneOf a) p := by
  classical
  -- the cone generated by the activities and `-y` meets `ℝ^L_+` only at `0`
  let g : ι ⊕ Unit → Fin L → ℝ := Sum.elim a fun _ => -y
  have hC : ∀ x ∈ coneOf g, 0 ≤ x → x = 0 := by
    rintro x ⟨mu, hmu, rfl⟩ hx0
    set y' := ∑ i, mu (Sum.inl i) • a i with hy'
    set t := mu (Sum.inr ())
    have hy'Y : y' ∈ coneOf a := ⟨fun i => mu (Sum.inl i), fun i => hmu (Sum.inl i), rfl⟩
    have hx : ∑ j, mu j • g j = y' - t • y := by
      rw [Fintype.sum_sum_type]
      simp [g, hy', sub_eq_add_neg]
      rfl
    rw [hx] at hx0 ⊢
    have ht : 0 ≤ t := hmu (Sum.inr ())
    rcases le_or_gt t 1 with ht1 | ht1
    · have hmem : y' + (1 - t) • y ∈ coneOf a :=
        add_mem_coneOf hy'Y (smul_mem_coneOf hy.1 (by linarith))
      have hge : y ≤ y' + (1 - t) • y := by
        intro i
        have := hx0 i
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.zero_apply] at this ⊢
        linarith
      have heq : y' + (1 - t) • y = y := by
        by_contra hne
        exact hy.2 ⟨_, hmem, hge, hne⟩
      have : y' - t • y = y' + (1 - t) • y - y := by
        rw [sub_smul, one_smul]; abel
      rw [this, heq, sub_self]
    · have htpos : 0 < t := by linarith
      have hmem : t⁻¹ • y' ∈ coneOf a := smul_mem_coneOf hy'Y (inv_nonneg.mpr htpos.le)
      have hge : y ≤ t⁻¹ • y' := by
        intro i
        have := hx0 i
        simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.zero_apply] at this ⊢
        rw [le_inv_mul_iff₀ htpos]
        linarith
      have heq : t⁻¹ • y' = y := by
        by_contra hne
        exact hy.2 ⟨_, hmem, hge, hne⟩
      have : y' = t • y := by
        rw [← heq, smul_smul, mul_inv_cancel₀ htpos.ne', one_smul]
      rw [this, sub_self]
  obtain ⟨p, hp, hpg⟩ := exists_pos_of_cone_inter_nonneg g hC
  have hpa : ∀ i, p ⬝ᵥ a i ≤ 0 := fun i => hpg (Sum.inl i)
  have hpy : 0 ≤ p ⬝ᵥ y := by
    have := hpg (Sum.inr ())
    simp only [g, Sum.elim_inr, dotProduct_neg, neg_nonpos] at this
    exact this
  refine ⟨p, hp, hy.1, ?_⟩
  rintro _ ⟨lam, hlam, rfl⟩
  rw [activity_profit]
  exact (Finset.sum_nonpos fun i _ => mul_nonpos_of_nonneg_of_nonpos (hlam i) (hpa i)).trans hpy

/-! ### Leontief's input-output model -/

variable {n : ℕ}

open Matrix in
/-- **Appendix 5.A** (MWG, p. 156). The Leontief production set (with free disposal):
`Y = {y : y ≤ [I - A; -b]α for some α ≥ 0}`, goods `1, …, L-1` produced and good `L` the
primary factor. -/
def leontiefSet (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) : Set (Fin (n + 1) → ℝ) :=
  {y | ∃ α : Fin n → ℝ, 0 ≤ α ∧ y ≤ extendVec ((1 - A) *ᵥ α) (-(b ⬝ᵥ α))}

open Matrix in
/-- **Appendix 5.A** (MWG, p. 156). `A` is productive if `(I - A)ᾱ ≫ 0` for some `ᾱ ≥ 0`. -/
def Productive (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ α : Fin n → ℝ, 0 ≤ α ∧ StrictlyPositive ((1 - A) *ᵥ α)

/-- The Leontief input-output matrix of normalized activities `a_l` (with `a_ll = 1`): entry
`(k, l)` is `-a_kl` for `k ≠ l` and `0` on the diagonal (p. 156). -/
def leontiefMatrix (acts : Fin n → Fin (n + 1) → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun k l => if k = l then 0 else -acts l (Fin.castSucc k)

/-- The vector of primary factor requirements `b = (-a_{L1}, …, -a_{L,L-1})` (p. 156). -/
def primaryReq (acts : Fin n → Fin (n + 1) → ℝ) : Fin n → ℝ := fun l => -acts l (Fin.last n)

open Matrix in
/-- **Appendix 5.A** (MWG, p. 156). For normalized activities (`a_ll = 1`), running them at levels
`α` gives net outputs `(I - A)α` of goods `1, …, L-1` and uses `b·α` of the primary factor; with
no joint production and an unproduced primary factor, `A ≥ 0` and `b ≥ 0`. -/
theorem leontief_from_activities (acts : Fin n → Fin (n + 1) → ℝ)
    (hnorm : ∀ l, acts l (Fin.castSucc l) = 1) (α : Fin n → ℝ) :
    ∑ l, α l • acts l =
      extendVec ((1 - leontiefMatrix acts) *ᵥ α) (-(primaryReq acts ⬝ᵥ α)) ∧
    ((∀ l k, k ≠ l → acts l (Fin.castSucc k) ≤ 0) → ∀ k l, 0 ≤ leontiefMatrix acts k l) ∧
    ((∀ l, acts l (Fin.last n) ≤ 0) → 0 ≤ primaryReq acts) := by
  classical
  refine ⟨?_, fun h k l => ?_, fun h l => ?_⟩
  · funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, extendVec, Fin.snoc_last,
        primaryReq, dotProduct, neg_mul, Finset.sum_neg_distrib, neg_neg]
      exact Finset.sum_congr rfl fun l _ => mul_comm _ _
    · simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, extendVec, Fin.snoc_castSucc,
        Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, Matrix.mulVec, dotProduct,
        leontiefMatrix]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j),
        ← Finset.add_sum_erase _ _ (Finset.mem_univ j), hnorm j]
      simp only [↓reduceIte, zero_mul, zero_add, mul_one]
      have : ∑ x ∈ Finset.univ.erase j, (if j = x then 0 else -acts x (Fin.castSucc j)) * α x =
          -∑ x ∈ Finset.univ.erase j, α x * acts x (Fin.castSucc j) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun x hx => by
          have hjx : j ≠ x := Ne.symm (Finset.ne_of_mem_erase hx)
          simp only [hjx, ↓reduceIte]
          ring
      rw [this]
      ring
  · simp only [leontiefMatrix]
    split_ifs with hkl
    · exact le_rfl
    · linarith [h l k hkl]
  · simp only [primaryReq, Pi.zero_apply]
    linarith [h l]

open Matrix in
/-- **Appendix 5.A** (MWG, p. 156). The Leontief set equals the cone generated by the normalized
activities and the disposal activities. -/
theorem leontiefSet_eq_coneOf (acts : Fin n → Fin (n + 1) → ℝ)
    (hnorm : ∀ l, acts l (Fin.castSucc l) = 1) :
    leontiefSet (leontiefMatrix acts) (primaryReq acts) = coneOf (withDisposal acts) := by
  classical
  ext y
  constructor
  · rintro ⟨α, hα, hy⟩
    rw [← (leontief_from_activities acts hnorm α).1] at hy
    set d := ∑ l, α l • acts l - y
    refine ⟨Sum.elim α d, fun i => ?_, ?_⟩
    · rcases i with l | k
      · exact hα l
      · exact sub_nonneg.mpr hy k
    · rw [Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, withDisposal, smul_neg, Finset.sum_neg_distrib]
      have : ∑ k, d k • (Pi.single k 1 : Fin (n + 1) → ℝ) = d := by
        funext i
        simp [Finset.sum_apply, Pi.single_apply]
      rw [this]
      simp [d]
  · rintro ⟨mu, hmu, rfl⟩
    refine ⟨fun l => mu (Sum.inl l), fun l => hmu (Sum.inl l), ?_⟩
    rw [← (leontief_from_activities acts hnorm _).1, Fintype.sum_sum_type]
    simp only [withDisposal, Sum.elim_inl, Sum.elim_inr, smul_neg, Finset.sum_neg_distrib]
    intro i
    simp only [Pi.add_apply, Pi.neg_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have : 0 ≤ ∑ k, mu (Sum.inr k) * (Pi.single k 1 : Fin (n + 1) → ℝ) i :=
      Finset.sum_nonneg fun k _ => mul_nonneg (hmu (Sum.inr k))
        ((Pi.single_nonneg.mpr zero_le_one : (0 : Fin (n + 1) → ℝ) ≤ Pi.single k 1) i)
    linarith

open Matrix in
/-- The Neumann-series facts behind Proposition 5.AA.1 (MWG, p. 157): for `A ≥ 0` productive,
`Σ_n Aⁿ` converges, `I - A` is invertible with `(I - A)⁻¹ = Σ_n Aⁿ ≥ 0`, and `Aᴺ → 0`. -/
theorem proposition_5_AA_1_neumann {A : Matrix (Fin n) (Fin n) ℝ} (hA : ∀ i j, 0 ≤ A i j)
    (hprod : Productive A) :
    Summable (fun k : ℕ => A ^ k) ∧ IsUnit (1 - A) ∧ (1 - A)⁻¹ = ∑' k : ℕ, A ^ k ∧
      (∀ i j, 0 ≤ (1 - A)⁻¹ i j) ∧ Tendsto (fun k : ℕ => A ^ k) atTop (𝓝 0) := by
  obtain ⟨α, hα, hpos⟩ := hprod
  have hAα : ∀ i, 0 ≤ (A *ᵥ α) i := fun i => by
    simp only [Matrix.mulVec, dotProduct]
    exact Finset.sum_nonneg fun j _ => mul_nonneg (hA i j) (hα j)
  have hαpos : ∀ i, 0 < α i := by
    intro i
    have h1 := hpos i
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply] at h1
    linarith [hAα i]
  have hlt : ∀ i, (A *ᵥ α) i < α i := by
    intro i
    have h1 := hpos i
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply] at h1
    linarith
  obtain ⟨hsum, hunit, hinv⟩ := theorem_M_D_5_v hA hαpos hlt
  refine ⟨hsum, hunit, hinv, fun i j => ?_, hsum.tendsto_atTop_zero⟩
  rw [hinv]
  have h1 := Pi.hasSum.mp hsum.hasSum i
  have h2 := Pi.hasSum.mp h1 j
  exact h2.nonneg fun k => pow_entry_nonneg hA k i j

open Matrix in
/-- **Proposition 5.AA.1** (MWG, p. 156). If the (nonnegative) input-output matrix `A` is
productive, every nonnegative final demand `c ∈ ℝ^{L-1}_+` is producible: `(I - A)α = c` for some
`α ≥ 0` (namely `α = (I - A)⁻¹c`). -/
theorem proposition_5_AA_1 {A : Matrix (Fin n) (Fin n) ℝ} (hA : ∀ i j, 0 ≤ A i j)
    (hprod : Productive A) {c : Fin n → ℝ} (hc : 0 ≤ c) :
    ∃ α : Fin n → ℝ, 0 ≤ α ∧ (1 - A) *ᵥ α = c := by
  obtain ⟨-, hunit, -, hnn, -⟩ := proposition_5_AA_1_neumann hA hprod
  have hdet : IsUnit (1 - A).det := (Matrix.isUnit_iff_isUnit_det _).mp hunit
  refine ⟨(1 - A)⁻¹ *ᵥ c, fun i => ?_, ?_⟩
  · simp only [Pi.zero_apply, Matrix.mulVec, dotProduct]
    exact Finset.sum_nonneg fun j _ => mul_nonneg (hnn i j) (hc j)
  · rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]

open Matrix in
/-- **Appendix 5.A** (MWG, p. 157, small type). For `A ≥ 0` and `c ≥ 0`, `c` is producible
(`(I - A)α = c` for some `α ≥ 0`) if and only if the partial sums `Σ_{k<N} Aᵏc` are bounded:
`Σ_n Aⁿc` is well defined. -/
theorem producible_iff_neumann_bounded {A : Matrix (Fin n) (Fin n) ℝ} (hA : ∀ i j, 0 ≤ A i j)
    {c : Fin n → ℝ} (hc : 0 ≤ c) :
    (∃ α : Fin n → ℝ, 0 ≤ α ∧ (1 - A) *ᵥ α = c) ↔
      ∃ B : Fin n → ℝ, ∀ N : ℕ, (∑ k ∈ Finset.range N, A ^ k) *ᵥ c ≤ B := by
  have hpowc : ∀ k (v : Fin n → ℝ), 0 ≤ v → 0 ≤ (A ^ k) *ᵥ v := fun k v hv i => by
    simp only [Pi.zero_apply, Matrix.mulVec, dotProduct]
    exact Finset.sum_nonneg fun j _ => mul_nonneg (pow_entry_nonneg hA k i j) (hv j)
  have htel' : ∀ N, (1 - A) * (∑ k ∈ Finset.range N, A ^ k) = 1 - A ^ N := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, mul_add, ih, sub_mul, one_mul, pow_succ']
      abel
  have htel : ∀ N, (∑ k ∈ Finset.range N, A ^ k) * (1 - A) = 1 - A ^ N := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, add_mul, ih, mul_sub, mul_one, pow_succ]
      abel
  constructor
  · rintro ⟨α, hα, hαc⟩
    refine ⟨α, fun N => ?_⟩
    rw [← hαc, Matrix.mulVec_mulVec, htel, Matrix.sub_mulVec, Matrix.one_mulVec]
    intro i
    have h1 : 0 ≤ ((A ^ N) *ᵥ α) i := hpowc N α hα i
    simp only [Pi.sub_apply]
    linarith
  · rintro ⟨B, hB⟩
    set S : ℕ → Fin n → ℝ := fun N => (∑ k ∈ Finset.range N, A ^ k) *ᵥ c with hS
    have hmono : Monotone S := by
      apply monotone_nat_of_le_succ
      intro N i
      have h1 : 0 ≤ ((A ^ N) *ᵥ c) i := hpowc N c hc i
      simp only [hS, Finset.sum_range_succ, Matrix.add_mulVec, Pi.add_apply]
      linarith
    have hbdd : BddAbove (Set.range S) := ⟨B, by rintro _ ⟨N, rfl⟩; exact hB N⟩
    have hlim := tendsto_atTop_ciSup hmono hbdd
    set s := ⨆ N, S N
    have hstep : Tendsto (fun N => (A ^ N) *ᵥ c) atTop (𝓝 0) := by
      have h1 : (fun N => (A ^ N) *ᵥ c) = fun N => S (N + 1) - S N := by
        funext N
        simp only [hS, Finset.sum_range_succ, Matrix.add_mulVec]
        abel
      rw [h1]
      have := (hlim.comp (tendsto_add_atTop_nat 1)).sub hlim
      simpa using this
    refine ⟨s, fun i => ?_, ?_⟩
    · have hSn : ∀ N, 0 ≤ S N i := fun N => by
        have : 0 ≤ (∑ k ∈ Finset.range N, (A ^ k) *ᵥ c) i := by
          rw [Finset.sum_apply]
          exact Finset.sum_nonneg fun k _ => hpowc k c hc i
        simp only [hS, Matrix.sum_mulVec]
        exact this
      exact ge_of_tendsto' (((continuous_apply i).tendsto s).comp hlim) hSn
    · have hcont : Continuous fun v : Fin n → ℝ => (1 - A) *ᵥ v :=
        continuous_const.matrix_mulVec continuous_id
      have h1 : Tendsto (fun N => (1 - A) *ᵥ S N) atTop (𝓝 ((1 - A) *ᵥ s)) :=
        (hcont.tendsto s).comp hlim
      have h2 : (fun N => (1 - A) *ᵥ S N) = fun N => c - (A ^ N) *ᵥ c := by
        funext N
        simp only [hS, Matrix.mulVec_mulVec]
        rw [htel', Matrix.sub_mulVec, Matrix.one_mulVec]
      rw [h2] at h1
      have h3 : Tendsto (fun N => c - (A ^ N) *ᵥ c) atTop (𝓝 (c - 0)) :=
        tendsto_const_nhds.sub hstep
      rw [sub_zero] at h3
      exact tendsto_nhds_unique h1 h3

open Matrix in
/-- **Example 5.AA.1** (MWG, p. 157). For `L = 3`, `a₁ = (1, -1, -2)` and `a₂ = (-β, 1, -4)`
with `β ≥ 0`: the input-output matrix is `A = [[0, β], [1, 0]]` with `b = (2, 4)`; activity
levels `α` give net outputs `(α₁ - βα₂, α₂ - α₁)`; `A` is productive iff `β < 1`; and then
`(I - A)⁻¹ = (1/(1 - β))[[1, β], [1, 1]]`. -/
theorem example_5_AA_1 {β : ℝ} (hβ : 0 ≤ β) :
    let acts : Fin 2 → Fin 3 → ℝ := ![![1, -1, -2], ![-β, 1, -4]]
    leontiefMatrix acts = !![0, β; 1, 0] ∧ primaryReq acts = ![2, 4] ∧
      (∀ α : Fin 2 → ℝ, (1 - leontiefMatrix acts) *ᵥ α = ![α 0 - β * α 1, α 1 - α 0]) ∧
      (Productive (leontiefMatrix acts) ↔ β < 1) ∧
      (β < 1 → (1 - leontiefMatrix acts)⁻¹ = (1 / (1 - β)) • !![1, β; 1, 1]) := by
  intro acts
  have hA : leontiefMatrix acts = !![0, β; 1, 0] := by
    ext k l
    fin_cases k <;> fin_cases l <;> simp [leontiefMatrix, acts]
  have hnet : ∀ α : Fin 2 → ℝ, (1 - leontiefMatrix acts) *ᵥ α = ![α 0 - β * α 1, α 1 - α 0] := by
    intro α
    rw [hA]
    funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring
  refine ⟨hA, ?_, hnet, ⟨?_, ?_⟩, fun hβ1 => ?_⟩
  · funext l
    fin_cases l <;> simp [primaryReq, acts]
  · rintro ⟨α, hα, hpos⟩
    rw [hnet] at hpos
    have h0 := hpos 0
    have h1 := hpos 1
    simp at h0 h1
    have hα1 : 0 ≤ α 0 := hα 0
    by_contra hge
    push Not at hge
    nlinarith
  · intro hβ1
    refine ⟨![1 + β, 2], fun i => by
      fin_cases i
      · simp only [Fin.zero_eta, Fin.isValue, Pi.zero_apply, Matrix.cons_val_zero]
        linarith
      · simp, ?_⟩
    rw [hnet]
    intro i
    fin_cases i <;> simp <;> nlinarith
  · have hne : (1 - β) ≠ 0 := by linarith
    rw [hA]
    apply Matrix.inv_eq_right_inv
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;> field_simp <;> ring

/-! ### The linear-programming production function (p. 158) -/

open Matrix in
/-- **Appendix 5.A** (MWG, p. 158). The dual variables of the linear program defining the
production function are supergradients of it: if `ᾱ` solves `max f·α` s.t. `Bα ≤ z̄`, `α ≥ 0`, there
is `λ ≥ 0` (a dual solution) with `f·α' ≤ f·ᾱ + λ·(z' - z̄)` for every `α'` feasible at any `z'`. -/
theorem lp_dual_supergradient {K N : ℕ} {B : Matrix (Fin K) (Fin N) ℝ} {f : Fin N → ℝ}
    {z : Fin K → ℝ} {α : Fin N → ℝ} (hα : α ∈ primalFeasible B z)
    (hmax : ∀ α' ∈ primalFeasible B z, f ⬝ᵥ α' ≤ f ⬝ᵥ α) :
    ∃ lam : Fin K → ℝ, 0 ≤ lam ∧ ∀ z' : Fin K → ℝ, ∀ α' ∈ primalFeasible B z',
      f ⬝ᵥ α' ≤ f ⬝ᵥ α + lam ⬝ᵥ (z' - z) := by
  obtain ⟨lam, hlamF, hval, -⟩ := theorem_M_M_1 hα hmax
  refine ⟨lam, hlamF.1, fun z' α' hα' => ?_⟩
  have := equation_M_M_3 hα' hlamF
  rw [dotProduct_sub, dotProduct_comm lam z', dotProduct_comm lam z, ← hval]
  linarith

open Matrix in
/-- **Appendix 5.A** (MWG, p. 158). The dual variable `λ_l` lies between the right and left
partial derivatives of the production function: if `F` is the LP value along the `l`-th input
direction (`F(t)` the maximum at `z̄ + t e_l`, attained for `t` near `0`), with right derivative
`d⁺` and left derivative `d⁻` at `0`, then `d⁺ ≤ λ_l ≤ d⁻`. -/
theorem lp_dual_marginal_products {K N : ℕ} {B : Matrix (Fin K) (Fin N) ℝ} {f : Fin N → ℝ}
    {z : Fin K → ℝ} {α : Fin N → ℝ} (hα : α ∈ primalFeasible B z)
    (hmax : ∀ α' ∈ primalFeasible B z, f ⬝ᵥ α' ≤ f ⬝ᵥ α) (l : Fin K) {F : ℝ → ℝ}
    (hF0 : F 0 = f ⬝ᵥ α)
    (hF : ∀ t, ∃ α' ∈ primalFeasible B (z + t • Pi.single l 1), F t = f ⬝ᵥ α')
    {dp dm : ℝ} (hdp : HasDerivWithinAt F dp (Set.Ici 0) 0)
    (hdm : HasDerivWithinAt F dm (Set.Iic 0) 0) :
    ∃ lam : Fin K → ℝ, 0 ≤ lam ∧ dp ≤ lam l ∧ lam l ≤ dm := by
  obtain ⟨lam, hlam, hsup⟩ := lp_dual_supergradient hα hmax
  have hle : ∀ t, F t ≤ F 0 + t * lam l := by
    intro t
    obtain ⟨α', hα', hFt⟩ := hF t
    have := hsup _ α' hα'
    rw [add_sub_cancel_left, dotProduct_smul, dotProduct_single, mul_one, smul_eq_mul] at this
    rw [hFt, hF0]
    linarith
  refine ⟨lam, hlam, ?_, ?_⟩
  · have hs := hasDerivWithinAt_iff_tendsto_slope.mp hdp
    rw [Set.Ici_sdiff_left] at hs
    apply le_of_tendsto hs
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : (0 : ℝ) < t := ht
    rw [slope_def_field, sub_zero, div_le_iff₀ ht']
    linarith [hle t]
  · have hs := hasDerivWithinAt_iff_tendsto_slope.mp hdm
    rw [Set.Iic_sdiff_right] at hs
    apply ge_of_tendsto hs
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : t < 0 := ht
    rw [slope_def_field, sub_zero, le_div_iff_of_neg ht']
    linarith [hle t]

end MWG.Production

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The nonsubstitution theorem (MWG Appendix 5.A, pp. 158-159)

A Leontief model with substitution: goods `1, …, L-1` are producible and good `L` is the primary
factor; each elementary activity `a_i` produces the good `prod i`, has no other positive entry
(no joint production) and does not produce the primary factor. The production set is the cone
generated by the activities and the disposal activities.

**Proposition 5.AA.2** (`proposition_5_AA_2`, Samuelson's nonsubstitution theorem): there are
`L - 1` activities `â_l`, each a nonnegative combination of the elementary activities producing
good `l`, that generate every efficient production vector with `y_{-L} ≫ 0`. The proof is the
book's: Proposition 5.F.2 strengthened to `p ≫ 0` for the linear activity model
(`linear_activity_efficient_pos_price`), Proposition 5.AA.1 and Proposition 5.F.1. The book's
hypothesis that the model is productive is not needed (without an efficient `y` with
`y_{-L} ≫ 0` the statement is vacuous).
-/

namespace MWG.Production

open MWG.ClassicalDemand MWG.ConsumerChoice Filter Topology

variable {ι : Type*} [Fintype ι] {n : ℕ}

/-- The elementary activities together with the disposal activities `-e_l`. -/
def gensWithDisposal (acts : ι → Fin (n + 1) → ℝ) : ι ⊕ Fin (n + 1) → Fin (n + 1) → ℝ :=
  Sum.elim acts fun l => -Pi.single l 1

theorem sum_gensWithDisposal (acts : ι → Fin (n + 1) → ℝ) (mu : ι ⊕ Fin (n + 1) → ℝ) :
    ∑ j, mu j • gensWithDisposal acts j =
      ∑ i, mu (Sum.inl i) • acts i - fun k => mu (Sum.inr k) := by
  rw [Fintype.sum_sum_type]
  simp only [gensWithDisposal, Sum.elim_inl, Sum.elim_inr, smul_neg, Finset.sum_neg_distrib,
    ← sub_eq_add_neg]
  congr 1
  funext k
  simp [Finset.sum_apply, Pi.single_apply]

/-- **Proposition 5.AA.2 (the nonsubstitution theorem)** (MWG, p. 159). In a Leontief model with
substitution, there are activities `â_1, …, â_{L-1}`, `â_l` a nonnegative combination of the
elementary activities producing good `l`, such that every efficient production vector `y` with
`y_{-L} ≫ 0` is generated by them. -/
theorem proposition_5_AA_2 (acts : ι → Fin (n + 1) → ℝ) (prod : ι → Fin n)
    (hprim : ∀ i, acts i (Fin.last n) ≤ 0)
    (hjoint : ∀ i k, k ≠ prod i → acts i (Fin.castSucc k) ≤ 0) :
    ∃ ah : Fin n → Fin (n + 1) → ℝ,
      (∀ l, ah l ∈ coneOf (fun i : {i // prod i = l} => acts i)) ∧
      ∀ y, Efficient (coneOf (gensWithDisposal acts)) y →
        (∀ l, 0 < y (Fin.castSucc l)) → y ∈ coneOf ah := by
  classical
  set Y := coneOf (gensWithDisposal acts) with hY
  by_cases hex : ∃ yb, Efficient Y yb ∧ ∀ l, 0 < yb (Fin.castSucc l)
  swap
  · refine ⟨0, fun l => zero_mem_coneOf _, fun y hy hpos => absurd ⟨y, hy, hpos⟩ hex⟩
  obtain ⟨yb, hyb, hybpos⟩ := hex
  obtain ⟨p, hp, hsup⟩ := linear_activity_efficient_pos_price _ hyb
  have hpg : ∀ j, p ⬝ᵥ gensWithDisposal acts j ≤ 0 :=
    (activity_supply_nonempty_iff _ p).mp ⟨yb, hsup⟩
  have hpY : ∀ y ∈ Y, p ⬝ᵥ y ≤ 0 := by
    rintro _ ⟨lam, hlam, rfl⟩
    rw [activity_profit]
    exact Finset.sum_nonpos fun j _ => mul_nonpos_of_nonneg_of_nonpos (hlam j) (hpg j)
  obtain ⟨mu, hmu, hybeq⟩ := hsup.1
  have hzero := (activity_level_zero hpg hmu (hybeq ▸ hsup)).2
  have hterm : ∀ i, mu (Sum.inl i) * (p ⬝ᵥ acts i) = 0 := by
    intro i
    by_cases h : p ⬝ᵥ acts i < 0
    · rw [hzero (Sum.inl i) h, zero_mul]
    · have : p ⬝ᵥ acts i = 0 := le_antisymm (hpg (Sum.inl i)) (not_lt.mp h)
      rw [this, mul_zero]
  -- the aggregated activities `b_l` and their gross outputs
  set bl : Fin n → Fin (n + 1) → ℝ := fun l => ∑ i : {i // prod i = l}, mu (Sum.inl i.1) • acts i
    with hbl
  have hblcone : ∀ l, bl l ∈ coneOf (fun i : {i // prod i = l} => acts i) :=
    fun l => ⟨fun i => mu (Sum.inl i.1), fun i => hmu _, rfl⟩
  have hsumbl : ∑ l, bl l = ∑ i, mu (Sum.inl i) • acts i :=
    Fintype.sum_fiberwise prod (fun i => mu (Sum.inl i) • acts i)
  have hybd : yb = ∑ l, bl l - fun k => mu (Sum.inr k) := by
    rw [hybeq, sum_gensWithDisposal, hsumbl]
  -- off-diagonal entries of `b_l` are nonpositive
  have hbloff : ∀ l k, k ≠ l → bl l (Fin.castSucc k) ≤ 0 := by
    intro l k hkl
    simp only [hbl, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_nonpos fun i _ => mul_nonpos_of_nonneg_of_nonpos (hmu _)
      (hjoint i.1 k (by rw [i.2]; exact hkl))
  have hbllast : ∀ l, bl l (Fin.last n) ≤ 0 := by
    intro l
    simp only [hbl, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_nonpos fun i _ => mul_nonpos_of_nonneg_of_nonpos (hmu _) (hprim i.1)
  have hpbl : ∀ l, p ⬝ᵥ bl l = 0 := by
    intro l
    simp only [hbl, dotProduct_sum, dotProduct_smul, smul_eq_mul]
    exact Finset.sum_eq_zero fun i _ => hterm i.1
  set g : Fin n → ℝ := fun l => bl l (Fin.castSucc l) with hg
  have hgge : ∀ l, yb (Fin.castSucc l) ≤ g l := by
    intro l
    have h1 := congrFun hybd (Fin.castSucc l)
    simp only [Pi.sub_apply, Finset.sum_apply] at h1
    rw [h1, ← Finset.add_sum_erase _ _ (Finset.mem_univ l)]
    have h2 : ∑ x ∈ Finset.univ.erase l, bl x (Fin.castSucc l) ≤ 0 :=
      Finset.sum_nonpos fun x hx => hbloff x l (Ne.symm (Finset.ne_of_mem_erase hx))
    have h3 : 0 ≤ mu (Sum.inr (Fin.castSucc l)) := hmu _
    simp only [hg]
    linarith
  have hgpos : ∀ l, 0 < g l := fun l => (hybpos l).trans_le (hgge l)
  -- the normalized activities
  set ah : Fin n → Fin (n + 1) → ℝ := fun l => (g l)⁻¹ • bl l with hah
  have hahcone : ∀ l, ah l ∈ coneOf (fun i : {i // prod i = l} => acts i) :=
    fun l => smul_mem_coneOf (hblcone l) (inv_nonneg.mpr (hgpos l).le)
  have hnorm : ∀ l, ah l (Fin.castSucc l) = 1 := by
    intro l
    simp only [hah, Pi.smul_apply, smul_eq_mul]
    exact inv_mul_cancel₀ (hgpos l).ne'
  have hpah : ∀ l, p ⬝ᵥ ah l = 0 := by
    intro l
    rw [hah, dotProduct_smul, hpbl, smul_zero]
  have hident := fun α => (leontief_from_activities ah hnorm α).1
  have hAnn := (leontief_from_activities ah hnorm 0).2.1
  have hA : ∀ k l, 0 ≤ leontiefMatrix ah k l := hAnn fun l k hkl => by
    simp only [hah, Pi.smul_apply, smul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (hgpos l).le) (hbloff l k hkl)
  -- `A` is productive, at the gross outputs `g`
  have hprod : Productive (leontiefMatrix ah) := by
    refine ⟨g, fun l => (hgpos l).le, fun l => ?_⟩
    have h1 := congrFun (hident g) (Fin.castSucc l)
    simp only [extendVec, Fin.snoc_castSucc] at h1
    rw [← h1]
    have h2 : ∑ k, g k • ah k = ∑ k, bl k := Finset.sum_congr rfl fun k _ => by
      rw [hah, smul_smul, mul_inv_cancel₀ (hgpos k).ne', one_smul]
    rw [h2]
    have h3 := congrFun hybd (Fin.castSucc l)
    simp only [Pi.sub_apply] at h3
    have h4 : 0 ≤ mu (Sum.inr (Fin.castSucc l)) := hmu _
    linarith [hybpos l]
  -- every `â_l`-combination lies in `Y`
  have hcomb : ∀ α : Fin n → ℝ, 0 ≤ α → ∑ l, α l • ah l ∈ Y := by
    intro α hα
    refine ⟨Sum.elim (fun i => α (prod i) * (g (prod i))⁻¹ * mu (Sum.inl i)) 0, fun j => ?_, ?_⟩
    · rcases j with i | k
      · exact mul_nonneg (mul_nonneg (hα _) (inv_nonneg.mpr (hgpos _).le)) (hmu _)
      · exact le_rfl
    · rw [sum_gensWithDisposal]
      simp only [Sum.elim_inl, Sum.elim_inr, Pi.zero_apply]
      have : (fun _ : Fin (n + 1) => (0 : ℝ)) = 0 := rfl
      rw [this, sub_zero, ← Fintype.sum_fiberwise prod]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [hah, hbl, smul_smul, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [i.2]
      congr 1
      ring
  refine ⟨ah, hahcone, fun y hy hypos => ?_⟩
  -- the final demand `y_{-L}` is produced by the `â_l`
  obtain ⟨α, hα, hαeq⟩ := proposition_5_AA_1 hA hprod
    (c := fun l => y (Fin.castSucc l)) (fun l => (hypos l).le)
  set y2 := ∑ l, α l • ah l with hy2
  have hy2Y : y2 ∈ Y := hcomb α hα
  have hy2c : ∀ l, y2 (Fin.castSucc l) = y (Fin.castSucc l) := by
    intro l
    rw [hy2, (hident α), extendVec, Fin.snoc_castSucc, hαeq]
  have hpy2 : p ⬝ᵥ y2 = 0 := by
    rw [hy2, dotProduct_sum]
    exact Finset.sum_eq_zero fun l _ => by rw [dotProduct_smul, hpah, smul_zero]
  have hy2sup : y2 ∈ supply Y p := ⟨hy2Y, fun y' hy' => by rw [hpy2]; exact hpY y' hy'⟩
  have hy2eff := proposition_5_F_1 hp hy2sup
  have heq : y2 = y := by
    rcases le_total (y (Fin.last n)) (y2 (Fin.last n)) with hle | hle
    · by_contra hne
      apply hy.2 ⟨y2, hy2Y, fun i => ?_, hne⟩
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact hle
      · rw [hy2c j]
    · by_contra hne
      apply hy2eff.2 ⟨y, hy.1, fun i => ?_, Ne.symm hne⟩
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact hle
      · rw [hy2c j]
  rw [← heq]
  exact ⟨α, hα, rfl⟩

end MWG.Production

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The geometry of cost and supply in the single-output case (MWG Section 5.D, pp. 143-147)

With input prices fixed, `C(q) = c(w̄, q)`, `AC(q) = C(q)/q` and the supply locus
`q(p) = argmax_{q ≥ 0} pq - C(q)`.

* (5.D.1) and its sufficiency for convex `C` are `foc_5_C_6` and `foc_5_C_6_sufficient`.
* The nonconvex case (Figure 5.D.3, p. 145): with `C(0) = 0`, `q = 0` is the unique optimum for
  `p < min AC`, the optimal set at `p = AC(q̄)` is `{0} ∪ {q > 0 : AC(q) = AC(q̄)}`, and for
  `p > AC(q̄)` every optimum is positive and earns positive profits (`supply_nonconvex`).
* **Exercise 5.D.1**: `AC(q̄) = C'(q̄)` at the efficient scale, using differentiability only at
  `q̄`; without it only `C'₋(q̄) ≤ AC(q̄) ≤ C'₊(q̄)` holds (`exercise_5_D_1_onesided`,
  `exercise_5_D_1_kink`).
* Setup costs (Figures 5.D.4-5.D.6): nonsunk fixed cost with linear variable cost, sunk costs,
  and **Exercise 5.D.2** (partially sunk).
* Short-run and long-run costs (pp. 146-147): `C(q|z̄) ≥ C(q)`, equality at the long-run input
  level, lower envelope and equality of marginal costs.

Departure: "p = C_v'(q) implies pq > C_v(q)" (p. 146) needs strict convexity; for convex `C_v`
only `pq ≥ C_v(q)` holds (`sunk_cost_covers_variable`, `sunk_cost_strict_fails`).
-/

namespace MWG.Production

open MWG.ClassicalDemand MWG.ConsumerChoice Filter Topology

/-- The optimal output set of `max_{q ≥ 0} pq - C(q)`. -/
def outputSupply (C : ℝ → ℝ) (p : ℝ) : Set ℝ :=
  {q | 0 ≤ q ∧ ∀ q', 0 ≤ q' → p * q' - C q' ≤ p * q - C q}

/-- **Section 5.D** (MWG, p. 145, Figure 5.D.3). Let `C(0) = 0` and `q̄ > 0` minimize average cost
over `q > 0` (the efficient scale). (a) If `p < AC(q̄)`, then `q = 0` is the unique optimum.
(b) If `p = AC(q̄)`, the optimal set is `{0} ∪ {q > 0 : AC(q) = AC(q̄)}`. (c) If `p > AC(q̄)`, every
optimum is positive and earns strictly positive profit, so `p > AC(q*)`. -/
theorem supply_nonconvex {C : ℝ → ℝ} (h0 : C 0 = 0) {qb : ℝ} (hqb : 0 < qb)
    (hmin : ∀ q, 0 < q → C qb / qb ≤ C q / q) (p : ℝ) :
    (p < C qb / qb → outputSupply C p = {0}) ∧
      (p = C qb / qb → outputSupply C p = {q | q = 0 ∨ (0 < q ∧ C q / q = C qb / qb)}) ∧
      (C qb / qb < p → ∀ q ∈ outputSupply C p, 0 < q ∧ 0 < p * q - C q ∧ C q / q < p) := by
  have hprof : ∀ q, 0 < q → p * q - C q = q * (p - C q / q) := fun q hq => by
    field_simp
  refine ⟨fun hp => ?_, fun hp => ?_, fun hp q hq => ?_⟩
  · ext q
    simp only [outputSupply, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hq0, hopt⟩
      by_contra hne
      have hpos : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hne)
      have := hopt 0 le_rfl
      rw [h0, hprof q hpos] at this
      have : p - C q / q < 0 := by linarith [hmin q hpos]
      nlinarith
    · rintro rfl
      refine ⟨le_rfl, fun q' hq' => ?_⟩
      rw [h0]
      rcases hq'.lt_or_eq with hpos | rfl
      · rw [hprof q' hpos]
        nlinarith [hmin q' hpos]
      · simp [h0]
  · ext q
    simp only [outputSupply, Set.mem_ofPred_eq]
    have hopt0 : ∀ q', 0 ≤ q' → p * q' - C q' ≤ 0 := by
      intro q' hq'
      rcases hq'.lt_or_eq with hpos | rfl
      · rw [hprof q' hpos, hp]
        nlinarith [hmin q' hpos]
      · simp [h0]
    constructor
    · rintro ⟨hq0, hopt⟩
      rcases hq0.lt_or_eq with hpos | rfl
      · right
        refine ⟨hpos, le_antisymm ?_ (hmin q hpos)⟩
        have h1 := hopt qb hqb.le
        have h2 : p * qb - C qb = 0 := by rw [hp]; field_simp; ring
        rw [hprof q hpos] at h1
        rw [h2] at h1
        rw [← hp]
        by_contra hlt
        rw [not_le] at hlt
        nlinarith
      · left; rfl
    · rintro (rfl | ⟨hpos, hav⟩)
      · exact ⟨le_rfl, fun q' hq' => by rw [h0]; simpa using hopt0 q' hq'⟩
      · refine ⟨hpos.le, fun q' hq' => ?_⟩
        rw [hprof q hpos, hav, ← hp, sub_self, mul_zero]
        exact hopt0 q' hq'
  · obtain ⟨hq0, hopt⟩ := hq
    have hbig : 0 < p * qb - C qb := by
      rw [hprof qb hqb]
      exact mul_pos hqb (by linarith)
    have h1 := hopt qb hqb.le
    have hposprof : 0 < p * q - C q := by linarith
    have hqpos : 0 < q := by
      rcases hq0.lt_or_eq with h | h
      · exact h
      · rw [← h, h0] at hposprof; simp at hposprof
    refine ⟨hqpos, hposprof, ?_⟩
    rw [hprof q hqpos] at hposprof
    have := (mul_pos_iff_of_pos_left hqpos).mp hposprof
    linarith

/-- **Exercise 5.D.1** (MWG, p. 144). If `q̄ > 0` minimizes `AC(q) = C(q)/q` over `q > 0` and `C` is
differentiable at `q̄`, then `AC(q̄) = C'(q̄)`. Only differentiability at `q̄` is used. -/
theorem exercise_5_D_1 {C : ℝ → ℝ} {qb d : ℝ} (hqb : 0 < qb)
    (hmin : ∀ q, 0 < q → C qb / qb ≤ C q / q) (hd : HasDerivAt C d qb) : C qb / qb = d := by
  have hAC : HasDerivAt (fun q => C q / q) ((d * qb - C qb * 1) / qb ^ 2) qb :=
    hd.div (hasDerivAt_id qb) hqb.ne'
  have hloc : IsLocalMin (fun q => C q / q) qb := by
    filter_upwards [eventually_gt_nhds hqb] with q hq
    exact hmin q hq
  have h0 := hloc.hasDerivAt_eq_zero hAC
  have h1 : d * qb - C qb = 0 := by
    rw [mul_one, div_eq_zero_iff] at h0
    rcases h0 with h | h
    · exact h
    · exact absurd h (pow_ne_zero 2 hqb.ne')
  field_simp
  linarith

/-- **Exercise 5.D.1** (MWG, p. 144), second question: without differentiability at `q̄`, only
`C'₋(q̄) ≤ AC(q̄) ≤ C'₊(q̄)` holds (one-sided derivatives). -/
theorem exercise_5_D_1_onesided {C : ℝ → ℝ} {qb dl dr : ℝ} (hqb : 0 < qb)
    (hmin : ∀ q, 0 < q → C qb / qb ≤ C q / q)
    (hdr : HasDerivWithinAt C dr (Set.Ici qb) qb) (hdl : HasDerivWithinAt C dl (Set.Iic qb) qb) :
    dl ≤ C qb / qb ∧ C qb / qb ≤ dr := by
  -- `C(q) ≥ AC(q̄) q` for `q > 0`, with equality at `q̄`
  have hge : ∀ q, 0 < q → C qb / qb * q ≤ C q := fun q hq => by
    have := hmin q hq
    rwa [le_div_iff₀ hq] at this
  have heq : C qb / qb * qb = C qb := by field_simp
  constructor
  · have hs := hasDerivWithinAt_iff_tendsto_slope.mp hdl
    rw [Set.Iic_sdiff_right] at hs
    apply le_of_tendsto hs
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (eventually_gt_nhds hqb)] with q hq hq0
    have hq' : q < qb := hq
    rw [slope_def_field, div_le_iff_of_neg (by linarith)]
    nlinarith [hge q hq0]
  · have hs := hasDerivWithinAt_iff_tendsto_slope.mp hdr
    rw [Set.Ici_sdiff_left] at hs
    apply ge_of_tendsto hs
    filter_upwards [self_mem_nhdsWithin] with q hq
    have hq' : qb < q := hq
    rw [slope_def_field, le_div_iff₀ (by linarith)]
    nlinarith [hge q (by linarith)]

/-- **Exercise 5.D.1** (MWG, p. 144): the equality can fail at a kink. For
`C(q) = max{1, q²}`, `q̄ = 1` minimizes `AC` with `AC(1) = 1`, but `C'₋(1) = 0` and `C'₊(1) = 2`. -/
theorem exercise_5_D_1_kink :
    (∀ q : ℝ, 0 < q → max 1 (1 ^ 2) / 1 ≤ max 1 (q ^ 2) / q) ∧
      HasDerivWithinAt (fun q : ℝ => max 1 (q ^ 2)) 2 (Set.Ici 1) 1 ∧
      HasDerivWithinAt (fun q : ℝ => max 1 (q ^ 2)) 0 (Set.Iic 1) 1 := by
  refine ⟨fun q hq => ?_, ?_, ?_⟩
  · rw [le_div_iff₀ hq]
    norm_num
    rcases le_total q 1 with h | h
    · exact Or.inl h
    · exact Or.inr (by nlinarith)
  · have h1 : HasDerivWithinAt (fun q : ℝ => q ^ 2) 2 (Set.Ici 1) 1 := by
      have := (hasDerivAt_pow 2 (1 : ℝ)).hasDerivWithinAt (s := Set.Ici 1)
      simpa using this
    apply h1.congr_of_mem (fun q hq => ?_) (Set.mem_Ici.mpr le_rfl)
    exact max_eq_right (by nlinarith [Set.mem_Ici.mp hq])
  · have h1 : HasDerivWithinAt (fun _ : ℝ => (1 : ℝ)) 0 (Set.Iic 1) 1 :=
      hasDerivWithinAt_const _ _ _
    apply h1.congr_of_eventuallyEq _ (by norm_num)
    filter_upwards [nhdsWithin_le_nhds (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)),
      self_mem_nhdsWithin] with q hq0 hq
    have hq1 : q ≤ 1 := hq
    exact max_eq_left (by nlinarith)

/-- **Figure 5.D.5** (MWG, p. 145). Constant returns variable cost with a nonsunk setup cost:
`C(0) = 0`, `C(q) = K + cq` for `q > 0` (`K > 0`). For `p ≤ c` the unique optimum is `q = 0`;
for `p > c` profits are unbounded and no optimum exists ("infinite supply"). -/
theorem figure_5_D_5 {K c p : ℝ} (hK : 0 < K) :
    let C : ℝ → ℝ := fun q => if q = 0 then 0 else K + c * q
    (p ≤ c → outputSupply C p = {0}) ∧ (c < p → outputSupply C p = ∅) := by
  intro C
  constructor
  · intro hp
    ext q
    simp only [outputSupply, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hq0, hopt⟩
      by_contra hne
      have := hopt 0 le_rfl
      simp only [C, hne, ↓reduceIte, mul_zero, sub_zero] at this
      nlinarith
    · rintro rfl
      refine ⟨le_rfl, fun q' hq' => ?_⟩
      by_cases h : q' = 0
      · simp [C, h]
      · simp only [C, h, ↓reduceIte, mul_zero, sub_zero]
        nlinarith
  · intro hp
    ext q
    simp only [outputSupply, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hq0 hopt
    set q' := q + (K + |p * q - C q| + 1) / (p - c) with hq'
    have hpc : 0 < p - c := by linarith
    have hq'pos : 0 < q' := by
      have : 0 < (K + |p * q - C q| + 1) / (p - c) := by positivity
      linarith
    have := hopt q' hq'pos.le
    simp only [C, hq'pos.ne', ↓reduceIte] at this
    have h2 : (p - c) * ((K + |p * q - C q| + 1) / (p - c)) = K + |p * q - C q| + 1 := by
      field_simp
    have h3 : p * q' - (K + c * q') = (p - c) * q + (K + |p * q - C q| + 1) - K := by
      rw [hq']; nlinarith
    have h4 : (p - c) * q ≥ 0 := mul_nonneg hpc.le hq0
    linarith [le_abs_self (p * q - C q)]

/-- **Section 5.D** (MWG, p. 146). With a sunk cost, `C(q) = C_v(q) + K` for all `q ≥ 0`, the
supply is the same as without `K`. -/
theorem sunk_cost_supply (Cv : ℝ → ℝ) (K p : ℝ) :
    outputSupply (fun q => Cv q + K) p = outputSupply Cv p := by
  ext q
  simp only [outputSupply, Set.mem_ofPred_eq]
  constructor <;> rintro ⟨hq, h⟩ <;> exact ⟨hq, fun q' hq' => by linarith [h q' hq']⟩

/-- **Section 5.D** (MWG, p. 146). If `C_v` is convex on `[0, ∞)` with `C_v(0) = 0` and
`p = C_v'(q)`, then `pq ≥ C_v(q)`: the firm covers its variable costs. -/
theorem sunk_cost_covers_variable {Cv : ℝ → ℝ} (hc : ConvexOn ℝ (Set.Ici 0) Cv) (h0 : Cv 0 = 0)
    {q p : ℝ} (hq : 0 ≤ q) (hd : HasDerivAt Cv p q) : Cv q ≤ p * q := by
  have := convex_tangent_le hc (Set.mem_Ici.mpr hq) (Set.mem_Ici.mpr le_rfl) hd
  rw [h0] at this
  linarith

/-- The strict inequality `pq > C_v(q)` printed on p. 146 fails for linear `C_v` (correction):
`C_v(q) = q` is convex, `C_v(0) = 0`, `C_v'(1) = 1` and `1·1 = C_v(1)`. -/
theorem sunk_cost_strict_fails :
    ConvexOn ℝ (Set.Ici 0) (fun q : ℝ => q) ∧ HasDerivAt (fun q : ℝ => q) 1 1 ∧
      ¬ ((fun q : ℝ => q) 1 < 1 * 1) :=
  ⟨convexOn_id (convex_Ici 0), hasDerivAt_id 1, by norm_num⟩

/-- **Exercise 5.D.2** (MWG, p. 146), partially sunk costs: `C(0) = K₀`, `C(q) = K + C_v(q)` for
`q > 0`, `0 < K₀ < K`. Producing some `q > 0` is optimal over shutting down iff
`pq - C_v(q) ≥ K - K₀`: only the nonsunk part `K - K₀` of the fixed cost matters. (The graph of
the supply locus is a figure.) -/
theorem exercise_5_D_2 (Cv : ℝ → ℝ) {K K₀ p q : ℝ} (hq : 0 < q) :
    let C : ℝ → ℝ := fun q => if q = 0 then K₀ else K + Cv q
    (p * 0 - C 0 ≤ p * q - C q ↔ K - K₀ ≤ p * q - Cv q) := by
  intro C
  simp only [C, hq.ne', ↓reduceIte, mul_zero, zero_sub]
  constructor <;> intro h <;> linarith

/-! ### Short-run and long-run costs -/

/-- The short-run input requirement set with input `k` fixed at `z̄`. -/
def shortRunReq {n : ℕ} (V : Set (Fin n → ℝ)) (k : Fin n) (zb : ℝ) : Set (Fin n → ℝ) :=
  {z | z ∈ V ∧ z k = zb}

/-- **Section 5.D** (MWG, p. 146). Short-run costs are at least long-run costs:
`C(q|z̄) ≥ C(q)` (`w ≥ 0`, the short-run problem feasible). -/
theorem shortRun_ge_longRun {n : ℕ} {V : Set (Fin n → ℝ)} (hV : V ⊆ {z | 0 ≤ z}) {w : Fin n → ℝ}
    (hw : 0 ≤ w) (k : Fin n) {zb : ℝ} (hne : (shortRunReq V k zb).Nonempty) :
    supportFn V w ≤ supportFn (shortRunReq V k zb) w :=
  vcost_mono hV (fun _ hz => hz.1) hne hw

/-- **Section 5.D** (MWG, pp. 146-147). If a long-run cost-minimizing input vector has `z_k = z̄`,
short-run and long-run costs coincide: `C(q|z_k(w, q)) = C(q)`. -/
theorem shortRun_eq_longRun {n : ℕ} {V : Set (Fin n → ℝ)} {w z : Fin n → ℝ} (k : Fin n)
    (hz : z ∈ supportArgmin V w) :
    supportFn (shortRunReq V k (z k)) w = supportFn V w := by
  have hz' : z ∈ supportArgmin (shortRunReq V k (z k)) w := ⟨⟨hz.1, rfl⟩, fun y hy => hz.2 y hy.1⟩
  rw [supportFn_eq_of_mem_argmin hz', supportFn_eq_of_mem_argmin hz]

/-- **Section 5.D** (MWG, p. 147). The long-run cost function is the lower envelope of the
short-run cost functions: `C(q) = min_{z̄} C(q|z̄)` (attained at `z̄ = z_k(w, q)`). -/
theorem longRun_lower_envelope {n : ℕ} {V : Set (Fin n → ℝ)} (hV : V ⊆ {z | 0 ≤ z})
    {w z : Fin n → ℝ} (hw : 0 ≤ w) (k : Fin n) (hz : z ∈ supportArgmin V w) :
    IsLeast {c | ∃ zb, (shortRunReq V k zb).Nonempty ∧ c = supportFn (shortRunReq V k zb) w}
      (supportFn V w) :=
  ⟨⟨z k, ⟨z, hz.1, rfl⟩, (shortRun_eq_longRun k hz).symm⟩,
    by rintro _ ⟨zb, hne, rfl⟩; exact shortRun_ge_longRun hV hw k hne⟩

/-- **Section 5.D** (MWG, p. 147). If the short-run cost `C(·|z̄)` with `z̄ = z_k(w, q̄)` and the
long-run cost `C(·)` are both differentiable at `q̄`, the marginal costs are equal:
`C'(q̄) = C'(q̄|z̄)` (tangency of the envelope). -/
theorem shortRun_marginal_eq {Clr Csr : ℝ → ℝ} {qb d dsr : ℝ}
    (hge : ∀ q, Clr q ≤ Csr q) (heq : Csr qb = Clr qb) (hd : HasDerivAt Clr d qb)
    (hdsr : HasDerivAt Csr dsr qb) : d = dsr := by
  have hmin : IsLocalMin (fun q => Csr q - Clr q) qb :=
    Eventually.of_forall fun q => by simp only; linarith [hge q, heq]
  have := hmin.hasDerivAt_eq_zero (hdsr.sub hd)
  linarith

end MWG.Production

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Remarks on the objectives of the firm (MWG Section 5.G, pp. 152-154)

Section 5.G has no numbered proposition; its mathematical content is the unanimity argument.

* Unanimity (pp. 152-153): with fixed prices, owner `i` (share `θ_i ≥ 0`, nonprofit wealth
  `w_i`) has budget set `{x ≥ 0 : p·x ≤ w_i + θ_i p·y}`. A plan with higher profit enlarges every
  owner's budget set (`unanimity_budget`), so every owner's maximal utility weakly increases
  (`unanimity_value`); with `θ_i > 0` and a strongly monotone utility, every bundle affordable
  before is strictly beaten (`unanimity_strict`). Hence all owners agree that the manager should
  maximize profits (`unanimity_profit_max`).
* (i) When prices depend on the firm's output, owners' objectives differ: the example on p. 153
  with `f(z) = z` and `p(q) = 2 - q` (`price_dependence_example`).
* **Exercise 5.G.1** (p. 164): (a) at a unanimously chosen interior plan consumption shares equal
  ownership shares (`exercise_5_G_1a`), (b) with equal shares unanimity forces equal consumption
  (`exercise_5_G_1b`), (c) with identical preferences and shares all owners have the same
  objective (`exercise_5_G_1c`); that common objective is not profit maximization in general
  (`exercise_5_G_1c_not_profit`, correction).
-/

namespace MWG.Production

open MWG.ClassicalDemand MWG.ConsumerChoice Filter Topology

variable {L : ℕ}

/-- **Section 5.G** (MWG, p. 152). Owner `i`'s budget set when the firm chooses `y`:
`{x ≥ 0 : p·x ≤ w_i + θ_i p·y}`. -/
def ownerBudget (p : Fin L → ℝ) (w θ : ℝ) (y : Fin L → ℝ) : Set (Fin L → ℝ) :=
  {x | 0 ≤ x ∧ p ⬝ᵥ x ≤ w + θ * (p ⬝ᵥ y)}

/-- **Section 5.G** (MWG, p. 152). Higher profit expands every owner's budget set. -/
theorem unanimity_budget (p : Fin L → ℝ) (w : ℝ) {θ : ℝ} (hθ : 0 ≤ θ) {y y' : Fin L → ℝ}
    (h : p ⬝ᵥ y ≤ p ⬝ᵥ y') : ownerBudget p w θ y ⊆ ownerBudget p w θ y' :=
  fun _ hx => ⟨hx.1, hx.2.trans (by nlinarith)⟩

/-- **Section 5.G** (MWG, pp. 152-153). Whatever her utility function, each owner's maximal
utility is at least as high under the plan with higher profit. -/
theorem unanimity_value (u : (Fin L → ℝ) → ℝ) (p : Fin L → ℝ) (w : ℝ) {θ : ℝ} (hθ : 0 ≤ θ)
    {y y' : Fin L → ℝ} (h : p ⬝ᵥ y ≤ p ⬝ᵥ y') {v v' : ℝ}
    (hv : IsGreatest (u '' ownerBudget p w θ y) v)
    (hv' : IsGreatest (u '' ownerBudget p w θ y') v') : v ≤ v' := by
  obtain ⟨⟨x, hx, rfl⟩, -⟩ := hv
  exact hv'.2 ⟨x, unanimity_budget p w hθ h hx, rfl⟩

/-- **Section 5.G** (MWG, p. 152). With `θ_i > 0`, `p ≫ 0` and a strongly monotone utility, a
plan with strictly higher profit is strictly better for owner `i`: every bundle affordable under
`y` is beaten by one affordable under `y'`. -/
theorem unanimity_strict (hL : 0 < L) (u : (Fin L → ℝ) → ℝ)
    (hu : ∀ x x', x ≤ x' → x ≠ x' → u x < u x') {p : Fin L → ℝ} (hp : StrictlyPositive p)
    (w : ℝ) {θ : ℝ} (hθ : 0 < θ) {y y' : Fin L → ℝ} (h : p ⬝ᵥ y < p ⬝ᵥ y') {x : Fin L → ℝ}
    (hx : x ∈ ownerBudget p w θ y) : ∃ x' ∈ ownerBudget p w θ y', u x < u x' := by
  set l : Fin L := ⟨0, hL⟩
  set t := θ * (p ⬝ᵥ y' - p ⬝ᵥ y) / p l with ht
  have htpos : 0 < t := div_pos (mul_pos hθ (by linarith)) (hp l)
  refine ⟨x + t • Pi.single l 1, ⟨?_, ?_⟩, hu _ _ ?_ ?_⟩
  · exact add_nonneg hx.1 (smul_nonneg htpos.le (Pi.single_nonneg.mpr zero_le_one))
  · rw [dotProduct_add, dotProduct_smul, dotProduct_single, mul_one, smul_eq_mul, ht,
      div_mul_cancel₀ _ (hp l).ne']
    have := hx.2
    nlinarith
  · exact le_add_of_nonneg_right (smul_nonneg htpos.le (Pi.single_nonneg.mpr zero_le_one))
  · intro he
    have := congrFun he l
    simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at this
    linarith

/-- **Section 5.G** (MWG, p. 153). All owners agree on profit maximization: if `y* ∈ y(p)`, then for
every feasible `y` and every owner, the budget set under `y` is contained in that under `y*`. -/
theorem unanimity_profit_max {Y : Set (Fin L → ℝ)} {p ys : Fin L → ℝ} (hys : ys ∈ supply Y p)
    {y : Fin L → ℝ} (hy : y ∈ Y) (w : ℝ) {θ : ℝ} (hθ : 0 ≤ θ) :
    ownerBudget p w θ y ⊆ ownerBudget p w θ ys :=
  unanimity_budget p w hθ (hys.2 y hy)

/-- **Section 5.G** (MWG, p. 153), remark (i). With `w_i = 0`, `f(z) = z` and the price of good 1
`p(q) = 2 - q` (good 2 the numeraire), owners who consume only good 2 maximize
`A(z) = p(f(z))f(z) - z = z - z²`, whose unique maximizer is `z = 1/2`; owners who consume only
good 1 maximize `B(z) = f(z) - z/p(f(z)) = z - z/(2 - z)`, and strictly prefer `z = 3/5` to
`z = 1/2`. The two problems have different solutions. -/
theorem price_dependence_example :
    (∀ z : ℝ, z ≠ 1 / 2 → (2 - z) * z - z < (2 - 1 / 2) * (1 / 2) - 1 / 2) ∧
      (1 / 2 : ℝ) - (1 / 2) / (2 - 1 / 2) < (3 / 5 : ℝ) - (3 / 5) / (2 - 3 / 5) := by
  refine ⟨fun z hz => ?_, by norm_num⟩
  have : 0 < (z - 1 / 2) ^ 2 := by
    have : z - 1 / 2 ≠ 0 := sub_ne_zero.mpr hz
    positivity
  nlinarith

/-- **Exercise 5.G.1(a)** (MWG, p. 164). Owners `i` have quasilinear utility in the input
(numeraire), so owner `i`'s welfare from plan `z` is `W_i(z) = v_i(p(z)) + θ_i π(z)`, with
`v_i'(p) = -x_i(p)` (envelope). If `z̄` is a local maximum of every `W_i` (unanimity),
`p'(z̄) ≠ 0`, the output market clears (`Σ_i x_i = f(z̄)`) and `Σ_i θ_i = 1`, then consumption
shares equal ownership shares: `x_i = θ_i f(z̄)`. -/
theorem exercise_5_G_1a {I : ℕ} {v : Fin I → ℝ → ℝ} {pr π : ℝ → ℝ} {θ x : Fin I → ℝ}
    {z q p' π' : ℝ} (hv : ∀ i, HasDerivAt (v i) (-x i) (pr z)) (hp : HasDerivAt pr p' z)
    (hπ : HasDerivAt π π' z) (hp' : p' ≠ 0)
    (hmax : ∀ i, IsLocalMax (fun t => v i (pr t) + θ i * π t) z)
    (hclear : ∑ i, x i = q) (hθ : ∑ i, θ i = 1) : ∀ i, x i = θ i * q := by
  have hfoc : ∀ i, -x i * p' + θ i * π' = 0 := by
    intro i
    have hd := ((hv i).comp z hp).add (hπ.const_mul (θ i))
    exact (hmax i).hasDerivAt_eq_zero hd
  have hsum : -q * p' + π' = 0 := by
    have := Finset.sum_eq_zero (s := Finset.univ) fun i (_ : i ∈ Finset.univ) => hfoc i
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, Finset.sum_neg_distrib,
      hclear, hθ, one_mul] at this
    exact this
  intro i
  have h1 := hfoc i
  have h2 : π' = q * p' := by linarith
  rw [h2] at h1
  have h3 : (θ i * q - x i) * p' = 0 := by linarith
  rcases mul_eq_zero.mp h3 with h | h
  · linarith
  · exact absurd h hp'

/-- **Exercise 5.G.1(b)** (MWG, p. 164). With identical ownership shares `θ_i = 1/I`, unanimity at
an interior plan forces all owners to consume the same amount of output; owners whose tastes lead to
different consumption at `p(z̄)` give conflicting instructions. -/
theorem exercise_5_G_1b {I : ℕ} {v : Fin I → ℝ → ℝ} {pr π : ℝ → ℝ} {x : Fin I → ℝ}
    {z q p' π' : ℝ} (hI : 0 < I) (hv : ∀ i, HasDerivAt (v i) (-x i) (pr z))
    (hp : HasDerivAt pr p' z) (hπ : HasDerivAt π π' z) (hp' : p' ≠ 0)
    (hmax : ∀ i, IsLocalMax (fun t => v i (pr t) + (1 / I : ℝ) * π t) z)
    (hclear : ∑ i, x i = q) : ∀ i j, x i = x j := by
  have hθ : ∑ _i : Fin I, (1 / I : ℝ) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have := exercise_5_G_1a (θ := fun _ => 1 / I) hv hp hπ hp' hmax hclear hθ
  intro i j
  rw [this i, this j]

/-- **Exercise 5.G.1(c)** (MWG, p. 164). With identical preferences and ownership shares, all owners
have the same objective `W(z) = v(p(z)) + θ π(z)`, so they agree on the plan. -/
theorem exercise_5_G_1c {I : ℕ} (v : ℝ → ℝ) (pr π : ℝ → ℝ) (θ : ℝ) (i j : Fin I) :
    (fun (_ : Fin I) (t : ℝ) => v (pr t) + θ * π t) i =
      (fun (_ : Fin I) (t : ℝ) => v (pr t) + θ * π t) j :=
  rfl

/-- **Exercise 5.G.1(c)** (MWG, p. 164): the common objective is not profit maximization
(correction). One owner (`θ = 1`) with utility `2√x - z` for output `x` and input `z`, `f(z) = z`:
the inverse demand is `p(q) = 1/√q`, the owner's welfare is `W(z) = 2√z - z`, maximized at
`z = 1`, while profit `π(z) = p(z)z - z = √z - z` is maximized at `z = 1/4`. -/
theorem exercise_5_G_1c_not_profit :
    (∀ z : ℝ, 0 ≤ z → 2 * Real.sqrt z - z ≤ 2 * Real.sqrt 1 - 1) ∧
      (∀ z : ℝ, 0 ≤ z → Real.sqrt z - z ≤ Real.sqrt (1 / 4) - 1 / 4) ∧
      Real.sqrt 1 - 1 < Real.sqrt (1 / 4) - 1 / 4 := by
  have h14 : Real.sqrt (1 / 4) = 1 / 2 := by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  refine ⟨fun z hz => ?_, fun z hz => ?_, ?_⟩
  · have hs := Real.sq_sqrt hz
    rw [Real.sqrt_one]
    nlinarith [sq_nonneg (Real.sqrt z - 1)]
  · have hs := Real.sq_sqrt hz
    rw [h14]
    nlinarith [sq_nonneg (Real.sqrt z - 1 / 2)]
  · rw [h14, Real.sqrt_one]
    norm_num

end MWG.Production

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The Cobb-Douglas production function (MWG Examples 5.B.2, 5.B.3, 5.C.1)

`f(z₁, z₂) = z₁^α z₂^β` (`cdProd α β`).

* **Example 5.B.2** (p. 130): `MRTS₁₂(z) = αz₂/(βz₁)`.
* **Example 5.B.3** (p. 133): `f(tz) = t^{α+β} f(z)`; constant, decreasing and increasing returns
  for `α + β = 1`, `< 1`, `> 1`.
* **Example 5.C.1** (pp. 142-143): the conditional factor demands and the cost function
  `c(w, q) = q^{1/(α+β)} θ φ(w)`, obtained from Chapter 3's Example 3.E.1 (the CMP for `f` is the
  EMP for the Cobb-Douglas utility `z₁^{α/(α+β)} z₂^{β/(α+β)}` at utility level `q^{1/(α+β)}`);
  the supply behaviour for `α + β < 1`, `= 1` and `> 1`.

Corrections: the printed output supply `q = (α+β)[p/θφ]^{(α+β)/(1-α-β)}` should read
`q = [(α+β)p/θφ]^{(α+β)/(1-α-β)}` (`example_5_C_1_supply`,
`example_5_C_1_printed_supply_counterexample`); and for `α + β > 1` doubling output multiplies
costs by `2^{1/(α+β)} < 2`, not `> 2` as printed (`example_5_C_1_doubling`).
-/

namespace MWG.Production

open MWG.ClassicalDemand MWG.ConsumerChoice Filter Topology

/-- **Example 5.B.2** (MWG, p. 130). The Cobb-Douglas production function `z₁^α z₂^β`. -/
noncomputable def cdProd (α β : ℝ) (z : Fin 2 → ℝ) : ℝ := z 0 ^ α * z 1 ^ β

theorem cdProd_differentiableAt (α β : ℝ) {z : Fin 2 → ℝ} (hz : StrictlyPositive z) :
    DifferentiableAt ℝ (cdProd α β) z :=
  ((differentiableAt_apply (𝕜 := ℝ) (0 : Fin 2) z).rpow_const (Or.inl (hz 0).ne')).mul
    ((differentiableAt_apply (𝕜 := ℝ) (1 : Fin 2) z).rpow_const (Or.inl (hz 1).ne'))

/-- The partial derivatives of the Cobb-Douglas function at `z ≫ 0`. -/
theorem cdProd_partial (α β : ℝ) {z : Fin 2 → ℝ} (hz : StrictlyPositive z) :
    partialF (cdProd α β) z 0 = α * z 0 ^ (α - 1) * z 1 ^ β ∧
      partialF (cdProd α β) z 1 = β * z 1 ^ (β - 1) * z 0 ^ α := by
  have hd := cdProd_differentiableAt α β hz
  constructor
  · have h1 := mc_line_hasDerivAt hd.hasFDerivAt (Pi.single 0 1)
    have heq : (fun t : ℝ => cdProd α β (z + t • Pi.single 0 1)) =
        fun t => (z 0 + t) ^ α * z 1 ^ β := by
      funext t
      simp [cdProd]
    rw [heq] at h1
    have h2 : HasDerivAt (fun t : ℝ => (z 0 + t) ^ α * z 1 ^ β)
        (1 * α * (z 0 + 0) ^ (α - 1) * z 1 ^ β) 0 :=
      (((hasDerivAt_id (0 : ℝ)).const_add (z 0)).rpow_const
        (Or.inl (by simp only [id_eq, add_zero]; exact (hz 0).ne'))).mul_const _
    simp only [add_zero, one_mul] at h2
    exact h1.unique h2
  · have h1 := mc_line_hasDerivAt hd.hasFDerivAt (Pi.single 1 1)
    have heq : (fun t : ℝ => cdProd α β (z + t • Pi.single 1 1)) =
        fun t => (z 1 + t) ^ β * z 0 ^ α := by
      funext t
      simp [cdProd, mul_comm]
    rw [heq] at h1
    have h2 : HasDerivAt (fun t : ℝ => (z 1 + t) ^ β * z 0 ^ α)
        (1 * β * (z 1 + 0) ^ (β - 1) * z 0 ^ α) 0 :=
      (((hasDerivAt_id (0 : ℝ)).const_add (z 1)).rpow_const
        (Or.inl (by simp only [id_eq, add_zero]; exact (hz 1).ne'))).mul_const _
    simp only [add_zero, one_mul] at h2
    exact h1.unique h2

/-- **Example 5.B.2** (MWG, p. 130). For `z ≫ 0` (and `β > 0`, so that `∂f/∂z₂ ≠ 0`),
`MRTS₁₂(z) = αz₂/(βz₁)`. -/
theorem example_5_B_2 {α β : ℝ} (hβ : 0 < β) {z : Fin 2 → ℝ} (hz : StrictlyPositive z) :
    MRTS (cdProd α β) z 0 1 = α * z 1 / (β * z 0) := by
  obtain ⟨h0, h1⟩ := cdProd_partial α β hz
  rw [MRTS, h0, h1, Real.rpow_sub_one (hz 0).ne', Real.rpow_sub_one (hz 1).ne']
  have := Real.rpow_pos_of_pos (hz 0) α
  have := Real.rpow_pos_of_pos (hz 1) β
  have := hz 0
  have := hz 1
  field_simp

/-- **Example 5.B.3** (MWG, p. 133). `f(tz) = t^{α+β} f(z)` for `t > 0`, `z ≥ 0`; in particular
`f(2z) = 2^{α+β} f(z)`. -/
theorem example_5_B_3_hom (α β : ℝ) {t : ℝ} (ht : 0 < t) {z : Fin 2 → ℝ} (hz : 0 ≤ z) :
    cdProd α β (t • z) = t ^ (α + β) * cdProd α β z := by
  simp only [cdProd, Pi.smul_apply, smul_eq_mul]
  rw [Real.mul_rpow ht.le (hz 0), Real.mul_rpow ht.le (hz 1), Real.rpow_add ht]
  ring

/-- **Example 5.B.3** (MWG, p. 133). Returns to scale of the Cobb-Douglas technology: constant
returns when `α + β = 1`; for `t > 1` and `f(z) > 0`, `f(tz) < tf(z)` when `α + β < 1` (decreasing
returns) and `f(tz) > tf(z)` when `α + β > 1` (increasing returns). -/
theorem example_5_B_3 {α β : ℝ} :
    (α + β = 1 → ConstantReturns (singleOutputSet (cdProd α β))) ∧
      (α + β < 1 → ∀ t : ℝ, 1 < t → ∀ z : Fin 2 → ℝ, 0 ≤ z → 0 < cdProd α β z →
        cdProd α β (t • z) < t * cdProd α β z) ∧
      (1 < α + β → ∀ t : ℝ, 1 < t → ∀ z : Fin 2 → ℝ, 0 ≤ z → 0 < cdProd α β z →
        t * cdProd α β z < cdProd α β (t • z)) := by
  refine ⟨fun h => ?_, fun h t ht z hz hf => ?_, fun h t ht z hz hf => ?_⟩
  · rw [exercise_5_B_2]
    intro z hz t ht
    rw [example_5_B_3_hom α β ht hz, h, Real.rpow_one]
  · rw [example_5_B_3_hom α β (by linarith) hz]
    have : t ^ (α + β) < t := by
      have := Real.rpow_lt_rpow_of_exponent_lt ht h
      rwa [Real.rpow_one] at this
    exact mul_lt_mul_of_pos_right this hf
  · rw [example_5_B_3_hom α β (by linarith) hz]
    have : t < t ^ (α + β) := by
      have := Real.rpow_lt_rpow_of_exponent_lt ht h
      rwa [Real.rpow_one] at this
    exact mul_lt_mul_of_pos_right this hf

/-! ### Example 5.C.1 -/

/-- The constant `θ = (α/β)^{β/(α+β)} + (α/β)^{-α/(α+β)}` of Example 5.C.1. -/
noncomputable def cdTheta (α β : ℝ) : ℝ :=
  (α / β) ^ (β / (α + β)) + (α / β) ^ (-(α / (α + β)))

/-- The function `φ(w) = w₁^{α/(α+β)} w₂^{β/(α+β)}` of Example 5.C.1. -/
noncomputable def cdPhi (α β : ℝ) (w : Fin 2 → ℝ) : ℝ :=
  w 0 ^ (α / (α + β)) * w 1 ^ (β / (α + β))

/-- The CMP for `z₁^α z₂^β` at output `q > 0` is the EMP for the Cobb-Douglas utility with
exponent `α/(α+β)` at utility level `q^{1/(α+β)}`. -/
theorem cd_inputReq_eq {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) {q : ℝ} (hq : 0 < q) :
    inputReq (cdProd α β) q =
      empConstraintSet (cobbDouglasUtility 1 (α / (α + β))) (q ^ (1 / (α + β))) := by
  have hs : 0 < α + β := by linarith
  ext z
  simp only [inputReq, empConstraintSet, Set.mem_ofPred_eq, cobbDouglasUtility, one_mul,
    nonnegOrthant]
  have h1a : 1 - α / (α + β) = β / (α + β) := by field_simp; ring
  rw [h1a]
  constructor
  · rintro ⟨hz, hqz⟩
    refine ⟨fun l => hz l, ?_⟩
    have hz0 : 0 ≤ z 0 := hz 0
    have hz1 : 0 ≤ z 1 := hz 1
    have hX : 0 ≤ z 0 ^ (α / (α + β)) * z 1 ^ (β / (α + β)) := by positivity
    have hpow : (z 0 ^ (α / (α + β)) * z 1 ^ (β / (α + β))) ^ (α + β) = cdProd α β z := by
      rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hz0,
        ← Real.rpow_mul hz1, div_mul_cancel₀ _ hs.ne', div_mul_cancel₀ _ hs.ne']
      rfl
    rw [← Real.rpow_le_rpow_iff (by positivity) hX hs, ← Real.rpow_mul hq.le,
      one_div_mul_cancel hs.ne', Real.rpow_one, hpow]
    exact hqz
  · rintro ⟨hz, hqz⟩
    have hz' : 0 ≤ z := fun l => hz l
    refine ⟨hz', ?_⟩
    have hz0 : 0 ≤ z 0 := hz 0
    have hz1 : 0 ≤ z 1 := hz 1
    have hpow : (z 0 ^ (α / (α + β)) * z 1 ^ (β / (α + β))) ^ (α + β) = cdProd α β z := by
      rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hz0,
        ← Real.rpow_mul hz1, div_mul_cancel₀ _ hs.ne', div_mul_cancel₀ _ hs.ne']
      rfl
    have := Real.rpow_le_rpow (by positivity) hqz hs.le
    rw [← Real.rpow_mul hq.le, one_div_mul_cancel hs.ne', Real.rpow_one, hpow] at this
    exact this

/-- `α^{-α}(1-α)^{α-1}` with `α = a/(a+b)` equals the book's `θ`. -/
theorem cdTheta_eq {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    (α / (α + β)) ^ (-(α / (α + β))) * (1 - α / (α + β)) ^ (α / (α + β) - 1) = cdTheta α β := by
  have hs : 0 < α + β := by linarith
  have h1a : 1 - α / (α + β) = β / (α + β) := by field_simp; ring
  have h2 : α / (α + β) - 1 = -(β / (α + β)) := by field_simp; ring
  have hA := Real.rpow_pos_of_pos hα (α / (α + β))
  have hB := Real.rpow_pos_of_pos hβ (β / (α + β))
  have hsplit : (α + β) ^ (α / (α + β)) * (α + β) ^ (β / (α + β)) = α + β := by
    rw [← Real.rpow_add hs, ← add_div, div_self hs.ne', Real.rpow_one]
  have hαs : α ^ (β / (α + β)) = α / α ^ (α / (α + β)) := by
    rw [eq_div_iff hA.ne', ← Real.rpow_add hα, ← add_div, add_comm, div_self hs.ne',
      Real.rpow_one]
  have hβs : β ^ (α / (α + β)) = β / β ^ (β / (α + β)) := by
    rw [eq_div_iff hB.ne', ← Real.rpow_add hβ, ← add_div, div_self hs.ne', Real.rpow_one]
  have e1 : (α / (α + β)) ^ (-(α / (α + β))) = (α + β) ^ (α / (α + β)) / α ^ (α / (α + β)) := by
    rw [Real.rpow_neg (div_pos hα hs).le, Real.div_rpow hα.le hs.le, inv_div]
  have e2 : (β / (α + β)) ^ (-(β / (α + β))) = (α + β) ^ (β / (α + β)) / β ^ (β / (α + β)) := by
    rw [Real.rpow_neg (div_pos hβ hs).le, Real.div_rpow hβ.le hs.le, inv_div]
  have e3 : (α / β) ^ (β / (α + β)) = α / α ^ (α / (α + β)) / β ^ (β / (α + β)) := by
    rw [Real.div_rpow hα.le hβ.le, hαs]
  have e4 : (α / β) ^ (-(α / (α + β))) = β / β ^ (β / (α + β)) / α ^ (α / (α + β)) := by
    rw [Real.rpow_neg (div_pos hα hβ).le, Real.div_rpow hα.le hβ.le, inv_div, hβs]
  rw [h1a, h2, cdTheta, e1, e2, e3, e4, div_mul_div_comm, hsplit]
  field_simp

/-- **Example 5.C.1** (MWG, p. 142). For `f(z) = z₁^α z₂^β` (`α, β > 0`), `w ≫ 0` and `q > 0`:
the conditional factor demands are
`z₁(w, q) = q^{1/(α+β)}(αw₂/(βw₁))^{β/(α+β)}`, `z₂(w, q) = q^{1/(α+β)}(βw₁/(αw₂))^{α/(α+β)}`,
and the cost function is `c(w, q) = q^{1/(α+β)} θ φ(w)`. -/
theorem example_5_C_1_cost {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) {w : Fin 2 → ℝ}
    (hw : StrictlyPositive w) {q : ℝ} (hq : 0 < q) :
    costFn (cdProd α β) w q = q ^ (1 / (α + β)) * cdTheta α β * cdPhi α β w ∧
      condDemand (cdProd α β) w q =
        {![q ^ (1 / (α + β)) * (α * w 1 / (β * w 0)) ^ (β / (α + β)),
          q ^ (1 / (α + β)) * (β * w 0 / (α * w 1)) ^ (α / (α + β))]} := by
  have hs : 0 < α + β := by linarith
  have ha0 : 0 < α / (α + β) := div_pos hα hs
  have ha1 : α / (α + β) < 1 := by rw [div_lt_one hs]; linarith
  have hub : 0 < q ^ (1 / (α + β)) := Real.rpow_pos_of_pos hq _
  obtain ⟨hexp, hhick⟩ := example_3_E_1 ha0 ha1 hw hub
  have h1a : 1 - α / (α + β) = β / (α + β) := by field_simp; ring
  have hratio : α / (α + β) / (1 - α / (α + β)) = α / β := by rw [h1a]; field_simp
  constructor
  · unfold costFn
    rw [cd_inputReq_eq hα hβ hq, ← expenditure_eq_supportFn, hexp,
      cdExpenditure_eq_book ha0 ha1 hw, ← cdTheta_eq hα hβ, cdPhi, h1a]
    ring
  · unfold condDemand
    rw [cd_inputReq_eq hα hβ hq]
    change hicksianDemand _ _ _ = _
    rw [hhick]
    congr 1
    obtain ⟨e0, e1⟩ := cdHicksian_eq_book ha0 ha1 hw (q ^ (1 / (α + β)))
    funext l
    fin_cases l
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      rw [e0, h1a]
      have : α / (α + β) * w 1 / (β / (α + β) * w 0) = α * w 1 / (β * w 0) := by
        field_simp
      rw [this, mul_comm]
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [e1, h1a]
      have : β / (α + β) * w 0 / (α / (α + β) * w 1) = β * w 0 / (α * w 1) := by
        field_simp
      rw [this, mul_comm]

/-- **Example 5.C.1** (MWG, p. 142), `α + β < 1`, corrected: with `c(q) = Kq^{1/s}`
(`K = θφ(w) > 0`, `s = α + β ∈ (0, 1)`) and `p > 0`, the unique solution of the first-order
condition (5.C.7), `q* = (sp/K)^{s/(1-s)}`, maximizes profits (5.C.5) (sufficient because `c` is
convex in `q`). -/
theorem example_5_C_1_supply {s K p : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hK : 0 < K) (hp : 0 < p) :
    let qs := (s * p / K) ^ (s / (1 - s))
    HasDerivAt (fun q => K * q ^ (1 / s)) p qs ∧
      ∀ q, 0 ≤ q → p * q - K * q ^ (1 / s) ≤ p * qs - K * qs ^ (1 / s) := by
  intro qs
  have hspK : 0 < s * p / K := by positivity
  have hqs : 0 < qs := Real.rpow_pos_of_pos hspK _
  have hr : 1 ≤ 1 / s := by rw [le_div_iff₀ hs0]; linarith
  have hpow : qs ^ (1 / s - 1) = s * p / K := by
    rw [← Real.rpow_mul hspK.le]
    have h1s : (1 - s) ≠ 0 := by linarith
    have : s / (1 - s) * (1 / s - 1) = 1 := by field_simp
    rw [this, Real.rpow_one]
  have hd : HasDerivAt (fun q => K * q ^ (1 / s)) p qs := by
    have := (Real.hasDerivAt_rpow_const (p := 1 / s) (Or.inl hqs.ne')).const_mul K
    convert this using 1
    rw [hpow]
    field_simp
  refine ⟨hd, ?_⟩
  have hconv : ConvexOn ℝ (Set.Ici 0) (fun q : ℝ => K * q ^ (1 / s)) :=
    (convexOn_rpow hr).smul hK.le
  exact foc_5_C_6_sufficient hconv hqs.le hd (by linarith) (fun _ => rfl)

/-- The printed supply `q = (α+β)[p/θφ]^{(α+β)/(1-α-β)}` (MWG, p. 142) is wrong (correction): for
`s = α + β = 1/3`, `K = θφ = 1`, `p = 1` it gives `q = 1/3`, at which (5.C.7) fails
(`K(1/s)q^{1/s - 1} = 1/3 ≠ p`) and profits `q - q³` are lower than at `q = 1/2`. -/
theorem example_5_C_1_printed_supply_counterexample :
    let s : ℝ := 1 / 3
    let qbook : ℝ := s * (1 / 1) ^ (s / (1 - s))
    qbook = 1 / 3 ∧ 1 * (1 / s) * qbook ^ ((1 / s) - 1) ≠ 1 ∧
      1 * qbook - 1 * qbook ^ (1 / s) < 1 * (1 / 2) - 1 * (1 / 2 : ℝ) ^ (1 / s) := by
  intro s qbook
  have hs : (1 / s : ℝ) = 3 := by norm_num [s]
  have hq : qbook = 1 / 3 := by simp [qbook, s]
  refine ⟨hq, ?_, ?_⟩
  · rw [hs, hq, show (3 : ℝ) - 1 = (2 : ℕ) by norm_num, Real.rpow_natCast]
    norm_num
  · rw [hs, hq, show (3 : ℝ) = (3 : ℕ) by norm_num, Real.rpow_natCast, Real.rpow_natCast]
    norm_num

/-- **Example 5.C.1** (MWG, p. 142), `α + β = 1`: with `c(q) = Kq`, `q = 0` is the unique optimum
if `K > p`, no solution exists if `K < p`, and every `q ≥ 0` is optimal (with zero profit) if
`K = p`. -/
theorem example_5_C_1_crs {K p : ℝ} :
    (p < K → outputSupply (fun q => K * q) p = {0}) ∧
      (K < p → outputSupply (fun q => K * q) p = ∅) ∧
      (K = p → outputSupply (fun q => K * q) p = Set.Ici 0) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · ext q
    simp only [outputSupply, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hq, hopt⟩
      have := hopt 0 le_rfl
      nlinarith
    · rintro rfl
      exact ⟨le_rfl, fun q' hq' => by nlinarith⟩
  · ext q
    simp only [outputSupply, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hq hopt
    have := hopt (q + 1) (by linarith)
    nlinarith
  · ext q
    simp only [outputSupply, Set.mem_ofPred_eq, Set.mem_Ici]
    subst h
    constructor
    · exact fun h => h.1
    · exact fun hq => ⟨hq, fun q' _ => by ring_nf; exact le_rfl⟩

/-- **Example 5.C.1** (MWG, p. 143), `α + β > 1`: with `c(q) = Kq^{1/s}`, `s > 1`, and `p > 0`,
profits are unbounded, so the PMP has no solution. -/
theorem example_5_C_1_irs {s K p : ℝ} (hs : 1 < s) (hK : 0 < K) (hp : 0 < p) (M : ℝ) :
    ∃ q, 0 ≤ q ∧ M < p * q - K * q ^ (1 / s) := by
  have hr0 : 0 < 1 / s := by positivity
  have hr1 : 1 / s < 1 := by rw [div_lt_one (by linarith)]; exact hs
  set q := max ((2 * K / p) ^ (1 / (1 - 1 / s))) (2 * (|M| + 1) / p) with hq
  have hq1 : 0 < q := lt_max_of_lt_right (by positivity)
  refine ⟨q, hq1.le, ?_⟩
  -- `K q^{1/s} ≤ pq/2` because `q^{1 - 1/s} ≥ 2K/p`
  have hA : 2 * K / p ≤ q ^ (1 - 1 / s) := by
    have h1 : (2 * K / p) ^ (1 / (1 - 1 / s)) ≤ q := le_max_left _ _
    have h2 := Real.rpow_le_rpow (by positivity) h1 (by linarith : (0 : ℝ) ≤ 1 - 1 / s)
    rwa [← Real.rpow_mul (by positivity), one_div_mul_cancel (by linarith), Real.rpow_one]
      at h2
  have hsplit : q = q ^ (1 / s) * q ^ (1 - 1 / s) := by
    rw [← Real.rpow_add hq1, add_sub_cancel, Real.rpow_one]
  have hB : K * q ^ (1 / s) ≤ p * q / 2 := by
    have hqs := Real.rpow_pos_of_pos hq1 (1 / s)
    calc K * q ^ (1 / s) = (p / 2) * (2 * K / p) * q ^ (1 / s) := by field_simp
      _ ≤ (p / 2) * q ^ (1 - 1 / s) * q ^ (1 / s) := by gcongr
      _ = (p / 2) * (q ^ (1 / s) * q ^ (1 - 1 / s)) := by ring
      _ = p * q / 2 := by rw [← hsplit]; ring
  have hC : 2 * (|M| + 1) / p ≤ q := le_max_right _ _
  rw [div_le_iff₀ hp] at hC
  linarith [le_abs_self M]

/-- **Example 5.C.1** (MWG, p. 143), correction of "a factor of `2^{1/(α+β)} > 2`": with increasing
returns (`α + β > 1`), doubling output multiplies costs by `2^{1/(α+β)}`, which is `< 2`. -/
theorem example_5_C_1_doubling {s K q : ℝ} (hs : 1 < s) (hq : 0 ≤ q) :
    K * (2 * q) ^ (1 / s) = (2 : ℝ) ^ (1 / s) * (K * q ^ (1 / s)) ∧ (2 : ℝ) ^ (1 / s) < 2 := by
  refine ⟨by rw [Real.mul_rpow (by norm_num) hq]; ring, ?_⟩
  have h := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2)
    (show 1 / s < 1 by rw [div_lt_one (by linarith)]; exact hs)
  rwa [Real.rpow_one] at h

end MWG.Production

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercises 5.B.4-5.B.6 (MWG, pp. 160-161)

* **Exercise 5.B.4**: the additive closure `Y⁺` (the smallest additive set containing `Y`), and
  the decreasing-returns technology `{y₁ ≤ 0, y₂ ≤ √(-y₁)}` whose additive closure is not closed
  (it contains `(-ε, 1)` for every `ε > 0` but not `(0, 1)`).
* **Exercise 5.B.5**: closed, convex and `-ℝ^L_+ ⊆ Y` imply free disposal.
* **Exercise 5.B.6**: two techniques with input requirement functions `φ₁, φ₂`; (b) subadditive
  `φ_i` give additivity; (c) first-order conditions and their sufficiency for convex `φ_i`;
  (d) with strictly concave `φ_i` a cost-minimizing plan never uses both techniques.
-/

namespace MWG.Production

open MWG.ClassicalDemand MWG.ConsumerChoice Filter Topology

variable {L : ℕ}

/-- **Exercise 5.B.4** (MWG, p. 160). The additive closure `Y⁺`: all finite sums of elements of
`Y` (at least one). -/
def addClosure (Y : Set (Fin L → ℝ)) : Set (Fin L → ℝ) :=
  {y | ∃ (k : ℕ) (ys : ℕ → Fin L → ℝ), (∀ i ≤ k, ys i ∈ Y) ∧ y = ∑ i ∈ Finset.range (k + 1), ys i}

/-- **Exercise 5.B.4** (MWG, p. 160). `Y⁺` contains `Y`, is additive, and is contained in every
additive set containing `Y`: it is the smallest additive production set containing `Y`. -/
theorem exercise_5_B_4_closure (Y : Set (Fin L → ℝ)) :
    Y ⊆ addClosure Y ∧ Additive (addClosure Y) ∧
      ∀ Z : Set (Fin L → ℝ), Y ⊆ Z → Additive Z → addClosure Y ⊆ Z := by
  refine ⟨fun y hy => ⟨0, fun _ => y, fun _ _ => hy, by simp⟩, ?_, ?_⟩
  · rintro _ ⟨k, ys, hys, rfl⟩ _ ⟨k', ys', hys', rfl⟩
    refine ⟨k + k' + 1, fun i => if i < k + 1 then ys i else ys' (i - (k + 1)), fun i hi => ?_, ?_⟩
    · dsimp only
      split_ifs with h
      · exact hys i (by omega)
      · exact hys' _ (by omega)
    · have e : k + k' + 1 + 1 = (k + 1) + (k' + 1) := by omega
      rw [e, Finset.sum_range_add (fun i => if i < k + 1 then ys i else ys' (i - (k + 1)))
        (k + 1) (k' + 1)]
      congr 1
      · exact Finset.sum_congr rfl fun i hi => by
          simp [Finset.mem_range.mp hi]
      · exact Finset.sum_congr rfl fun i _ => by
          simp only [show ¬ (k + 1 + i < k + 1) by omega, ↓reduceIte, Nat.add_sub_cancel_left]
  · intro Z hYZ hadd
    rintro _ ⟨k, ys, hys, rfl⟩
    induction k with
    | zero => simpa using hYZ (hys 0 le_rfl)
    | succ k ih =>
      rw [Finset.sum_range_succ]
      exact hadd _ (ih fun i hi => hys i (by omega)) _ (hYZ (hys _ le_rfl))

/-- The decreasing-returns technology of Figure 5.B.5(a): `{y : y₁ ≤ 0, y₂ ≤ √(-y₁)}`. -/
def sqrtTech : Set (Fin 2 → ℝ) := {y | y 0 ≤ 0 ∧ y 1 ≤ Real.sqrt (-y 0)}

/-- **Exercise 5.B.4** (MWG, p. 160). For the decreasing-returns technology `{y₁ ≤ 0,
y₂ ≤ √(-y₁)}` (closed, with free disposal), the additive closure violates closedness:
`(-ε, 1) ∈ Y⁺` for every `ε > 0`, but `(0, 1) ∉ Y⁺`. -/
theorem exercise_5_B_4_not_closed :
    IsClosed sqrtTech ∧ FreeDisposal sqrtTech ∧
      (∀ ε : ℝ, 0 < ε → (![-ε, 1] : Fin 2 → ℝ) ∈ addClosure sqrtTech) ∧
      (![0, 1] : Fin 2 → ℝ) ∉ addClosure sqrtTech ∧ ¬ IsClosed (addClosure sqrtTech) := by
  have hmem : ∀ ε : ℝ, 0 < ε → (![-ε, 1] : Fin 2 → ℝ) ∈ addClosure sqrtTech := by
    intro ε hε
    obtain ⟨k, hk⟩ := exists_nat_gt (1 / ε)
    set m : ℝ := k + 1 with hm
    have hm0 : 0 < m := by positivity
    set r := Real.sqrt (ε / m) with hr
    have hr0 : 0 ≤ r := Real.sqrt_nonneg _
    have hrr : r ^ 2 = ε / m := Real.sq_sqrt (by positivity)
    have hkε : 1 < m * ε := by
      have h1 : 1 < (k : ℝ) * ε := by rwa [div_lt_iff₀ hε] at hk
      rw [hm]
      nlinarith
    have hmr : 1 ≤ m * r := by
      have h1 : (m * r) ^ 2 = m * ε := by rw [mul_pow, hrr]; field_simp
      have h2 : 0 ≤ m * r := by positivity
      nlinarith
    have hneg : -(-ε / m) = ε / m := by ring
    have hε0 : -ε / m ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hm0.le
    refine ⟨k, fun i => if i = 0 then ![-ε / m, 1 - k * r] else ![-ε / m, r],
      fun i _ => ?_, ?_⟩
    · dsimp only
      split_ifs with hi
      · refine ⟨hε0, ?_⟩
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hneg]
        rw [← hr]
        nlinarith
      · exact ⟨hε0, by simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hneg, hr, le_refl]⟩
    · funext l
      rw [Finset.sum_apply, Finset.sum_range_succ']
      simp only [Nat.add_one_ne_zero, ↓reduceIte, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul]
      fin_cases l
      · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
        rw [hm]
        field_simp
        ring
      · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
        ring
  have hnot : (![0, 1] : Fin 2 → ℝ) ∉ addClosure sqrtTech := by
    rintro ⟨k, ys, hys, hsum⟩
    have h0 := congrFun hsum 0
    have h1 := congrFun hsum 1
    simp only [Finset.sum_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    have hle : ∀ j ∈ Finset.range (k + 1), ys j 0 ≤ 0 := fun j hj =>
      (hys j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))).1
    have hall : ∀ i ∈ Finset.range (k + 1), ys i 0 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonpos hle).mp h0.symm
    have hle1 : ∀ i ∈ Finset.range (k + 1), ys i 1 ≤ 0 := fun i hi => by
      have := (hys i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))).2
      rw [hall i hi, neg_zero, Real.sqrt_zero] at this
      exact this
    have := Finset.sum_nonpos hle1
    linarith
  refine ⟨?_, ?_, hmem, hnot, fun hcl => hnot ?_⟩
  · exact (isClosed_le (continuous_apply 0) continuous_const).inter
      (isClosed_le (continuous_apply 1) ((continuous_apply 0).neg.sqrt))
  · rintro y ⟨h0, h1⟩ y' hy'
    have a0 : y' 0 ≤ y 0 := hy' 0
    have a1 : y' 1 ≤ y 1 := hy' 1
    exact ⟨by linarith, a1.trans (h1.trans (Real.sqrt_le_sqrt (by linarith)))⟩
  · have hlim : Tendsto (fun n : ℕ => (![-(1 / (n + 1 : ℝ)), 1] : Fin 2 → ℝ)) atTop
        (𝓝 ![0, 1]) := by
      rw [tendsto_pi_nhds]
      intro l
      fin_cases l
      · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
        have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).neg
        rw [neg_zero] at this
        exact this
      · simp
    exact hcl.mem_of_tendsto hlim (Eventually.of_forall fun n => hmem _ (by positivity))

/-- **Exercise 5.B.5** (MWG, p. 160). If `Y` is closed and convex and `-ℝ^L_+ ⊆ Y`, then `Y` has
free disposal. -/
theorem exercise_5_B_5 {Y : Set (Fin L → ℝ)} (hcl : IsClosed Y) (hc : Convex ℝ Y)
    (hneg : ∀ v : Fin L → ℝ, 0 ≤ v → -v ∈ Y) : FreeDisposal Y := by
  intro y hy y' hy'
  set v := y - y' with hv
  have hv0 : 0 ≤ v := sub_nonneg.mpr hy'
  -- `(1 - t)y + t(-v/t) = (1 - t)y - v ∈ Y`, and `→ y - v = y'` as `t → 0⁺`
  have hmem : ∀ t : ℝ, 0 < t → t < 1 → (1 - t) • y - v ∈ Y := by
    intro t ht0 ht1
    have := hc hy (hneg (t⁻¹ • v) (smul_nonneg (inv_nonneg.mpr ht0.le) hv0))
      (by linarith : (0 : ℝ) ≤ 1 - t) ht0.le (by ring)
    rwa [smul_neg, smul_smul, mul_inv_cancel₀ ht0.ne', one_smul, ← sub_eq_add_neg] at this
  have hlim : Tendsto (fun t : ℝ => (1 - t) • y - v) (𝓝[>] 0) (𝓝 y') := by
    have hcont : Continuous fun t : ℝ => (1 - t) • y - v := by fun_prop
    have := hcont.tendsto 0
    simp only [sub_zero, one_smul] at this
    rw [hv, sub_sub_cancel] at this
    exact this.mono_left nhdsWithin_le_nhds
  apply hcl.mem_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (eventually_lt_nhds one_pos)]
    with t ht ht1
  exact hmem t ht ht1

/-! ### Exercise 5.B.6 -/

/-- **Exercise 5.B.6(a)** (MWG, p. 161). The three-good production set of two techniques with
minimal input requirements `φ₁(q₁)` (input 1 only) and `φ₂(q₂)` (input 2 only), with free
disposal: `(-z₁, -z₂, q)` with `q ≤ q₁ + q₂`, `φ₁(q₁) ≤ z₁`, `φ₂(q₂) ≤ z₂`, `q₁, q₂ ≥ 0`. -/
def twoTechSet (φ₁ φ₂ : ℝ → ℝ) : Set (Fin 3 → ℝ) :=
  {y | ∃ q₁ q₂ : ℝ, 0 ≤ q₁ ∧ 0 ≤ q₂ ∧ y 2 ≤ q₁ + q₂ ∧ φ₁ q₁ ≤ -y 0 ∧ φ₂ q₂ ≤ -y 1}

/-- **Exercise 5.B.6(b)** (MWG, p. 161). If `φ₁` and `φ₂` are subadditive
(`φ(a + b) ≤ φ(a) + φ(b)`, e.g. concave with `φ(0) = 0`, or linear), the production set is
additive. -/
theorem exercise_5_B_6b {φ₁ φ₂ : ℝ → ℝ}
    (h₁ : ∀ a b, 0 ≤ a → 0 ≤ b → φ₁ (a + b) ≤ φ₁ a + φ₁ b)
    (h₂ : ∀ a b, 0 ≤ a → 0 ≤ b → φ₂ (a + b) ≤ φ₂ a + φ₂ b) : Additive (twoTechSet φ₁ φ₂) := by
  rintro y ⟨q₁, q₂, hq₁, hq₂, hy2, hy0, hy1⟩ y' ⟨q₁', q₂', hq₁', hq₂', hy2', hy0', hy1'⟩
  refine ⟨q₁ + q₁', q₂ + q₂', by positivity, by positivity, ?_, ?_, ?_⟩ <;>
    simp only [Pi.add_apply]
  · linarith
  · linarith [h₁ q₁ q₁' hq₁ hq₁']
  · linarith [h₂ q₂ q₂' hq₂ hq₂']

/-- **Exercise 5.B.6(c)** (MWG, p. 161). With output price `p` and input prices `w₁, w₂`, profit
maximization separates by technique: if `q_i* ≥ 0` maximizes `pq_i - w_iφ_i(q_i)` and `φ_i` is
differentiable there, then `p ≤ w_iφ_i'(q_i*)` with equality if `q_i* > 0` (marginal cost of each
technique equals the price); these conditions are sufficient when `φ_i` is convex. -/
theorem exercise_5_B_6c {φ : ℝ → ℝ} {w p q d : ℝ} (hq : 0 ≤ q) (hd : HasDerivAt φ d q) :
    ((∀ q', 0 ≤ q' → p * q' - w * φ q' ≤ p * q - w * φ q) → p - w * d ≤ 0 ∧ (0 < q → p = w * d))
      ∧ (0 ≤ w → ConvexOn ℝ (Set.Ici 0) φ → p - w * d ≤ 0 → (0 < q → p = w * d) →
        ∀ q', 0 ≤ q' → p * q' - w * φ q' ≤ p * q - w * φ q) := by
  have hd' : HasDerivAt (fun x => w * φ x) (w * d) q := hd.const_mul w
  exact ⟨fun hopt => foc_5_C_6 hq hopt hd', fun hw hc hle heq =>
    foc_5_C_6_sufficient (hc.smul hw) hq hd' hle heq⟩

/-- **Exercise 5.B.6(d)** (MWG, p. 161). If `φ₁` and `φ₂` are strictly concave on `[0, ∞)` and
`w₁, w₂ > 0`, a cost-minimizing way to produce `q > 0` never uses both techniques: the cost
`g(q₁) = w₁φ₁(q₁) + w₂φ₂(q - q₁)` of any split with `0 < q₁ < q` exceeds that of producing with
one technique only. -/
theorem exercise_5_B_6d_aux {φ₁ φ₂ : ℝ → ℝ} (h₁ : StrictConcaveOn ℝ (Set.Ici 0) φ₁)
    (h₂ : StrictConcaveOn ℝ (Set.Ici 0) φ₂) {w₁ w₂ q q₁ : ℝ} (hw₁ : 0 < w₁) (hw₂ : 0 < w₂)
    (hq₁ : 0 < q₁) (hq₁q : q₁ < q) :
    min (w₁ * φ₁ 0 + w₂ * φ₂ q) (w₁ * φ₁ q + w₂ * φ₂ 0) < w₁ * φ₁ q₁ + w₂ * φ₂ (q - q₁) := by
  have hq : 0 < q := by linarith
  set t := q₁ / q with ht
  have ht0 : 0 < t := div_pos hq₁ hq
  have ht1 : t < 1 := by rw [div_lt_one hq]; exact hq₁q
  have e1 : q₁ = (1 - t) * 0 + t * q := by rw [ht]; field_simp; ring
  have e2 : q - q₁ = (1 - t) * q + t * 0 := by rw [ht]; field_simp; ring
  have a1 := h₁.2 (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hq.le) (ne_of_lt hq)
    (by linarith : 0 < 1 - t) ht0 (by ring)
  have a2 := h₂.2 (Set.mem_Ici.mpr hq.le) (Set.mem_Ici.mpr le_rfl) (ne_of_gt hq)
    (by linarith : 0 < 1 - t) ht0 (by ring)
  simp only [smul_eq_mul] at a1 a2
  rw [← e1] at a1
  rw [← e2] at a2
  have hcomb : (1 - t) * (w₁ * φ₁ 0 + w₂ * φ₂ q) + t * (w₁ * φ₁ q + w₂ * φ₂ 0) <
      w₁ * φ₁ q₁ + w₂ * φ₂ (q - q₁) := by nlinarith
  rcases le_total (w₁ * φ₁ 0 + w₂ * φ₂ q) (w₁ * φ₁ q + w₂ * φ₂ 0) with h | h
  · rw [min_eq_left h]; nlinarith
  · rw [min_eq_right h]; nlinarith

/-- **Exercise 5.B.6(d)** (MWG, p. 161), as stated: a cost-minimizing split `(q₁, q - q₁)` of `q`
between strictly concave techniques uses only one of them (`q₁ = 0` or `q₁ = q`). -/
theorem exercise_5_B_6d {φ₁ φ₂ : ℝ → ℝ} (h₁ : StrictConcaveOn ℝ (Set.Ici 0) φ₁)
    (h₂ : StrictConcaveOn ℝ (Set.Ici 0) φ₂) {w₁ w₂ q q₁ : ℝ} (hw₁ : 0 < w₁) (hw₂ : 0 < w₂)
    (hq₁ : 0 ≤ q₁) (hq₁q : q₁ ≤ q)
    (hmin : ∀ q₁', 0 ≤ q₁' → q₁' ≤ q →
      w₁ * φ₁ q₁ + w₂ * φ₂ (q - q₁) ≤ w₁ * φ₁ q₁' + w₂ * φ₂ (q - q₁')) :
    q₁ = 0 ∨ q₁ = q := by
  by_contra h
  push Not at h
  have hlt := exercise_5_B_6d_aux h₁ h₂ hw₁ hw₂ (lt_of_le_of_ne hq₁ (Ne.symm h.1))
    (lt_of_le_of_ne hq₁q h.2)
  have m1 := hmin 0 le_rfl (by linarith)
  have m2 := hmin q (by linarith) le_rfl
  simp only [sub_zero, sub_self] at m1 m2
  rcases le_total (w₁ * φ₁ 0 + w₂ * φ₂ q) (w₁ * φ₁ q + w₂ * φ₂ 0) with hh | hh
  · rw [min_eq_left hh] at hlt; linarith
  · rw [min_eq_right hh] at hlt; linarith

end MWG.Production

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercises 5.C.6-5.C.13 and the necessity of (5.C.4) (MWG, pp. 140, 161-162)

* (5.C.4) necessity (p. 140): with a constraint qualification, a cost-minimizing `z*` satisfies
  `w ≥ λ∇f(z*)`, `[w - λ∇f(z*)]·z* = 0` for some `λ ≥ 0` (`foc_5_C_4`, via Farkas' lemma); the
  qualification is needed (`foc_5_C_4_needs_cq`).
* **Exercise 5.C.6** (a)-(c), from the first-order conditions differentiated along price changes
  (the implicit function theorem supplies the differentiable demand).
* **Exercise 5.C.7**: false as printed with `∂²f/∂z_ℓ∂z_k < 0`; true (two inputs) with `> 0`.
* **Exercise 5.C.8**: the two observations violate profit maximization (weak axiom of profit
  maximization).
* **Exercise 5.C.9(a)-(b)** and **5.C.10(a)-(c)**: profit and cost functions; (c) via Chapter 3's
  CES expenditure function (Exercise 3.E.6).
* **Exercise 5.C.11**: `∂z_ℓ/∂q = ∂(∂c/∂q)/∂w_ℓ` (symmetry of the second derivative).
* **Exercise 5.C.12**: profit maximization in `Y` and in its constant-returns extension `Y'`.
* **Exercise 5.C.13**: `z₁ = αC/w₁`.
-/

namespace MWG.Production

open MWG.ClassicalDemand MWG.ConsumerChoice Filter Topology

variable {n : ℕ}

/-! ### Necessity of (5.C.4) -/

/-- **Section 5.C** (MWG, p. 140), condition (5.C.4), with a constraint qualification: let `z*`
solve the CMP with `f(z*) = q`, `f` differentiable at `z*`, and suppose some direction `d` with
`d_ℓ ≥ 0` whenever `z*_ℓ = 0` has `∇f(z*)·d > 0`. Then `w ≥ λ∇f(z*)` and
`[w - λ∇f(z*)]·z* = 0` for some `λ ≥ 0`. -/
theorem foc_5_C_4 {f : (Fin n → ℝ) → ℝ} {w z : Fin n → ℝ} {q : ℝ}
    (hz : z ∈ condDemand f w q) (hbind : f z = q) (hf : DifferentiableAt ℝ f z)
    (hcq : ∃ d : Fin n → ℝ, (∀ l, z l = 0 → 0 ≤ d l) ∧ 0 < (fun l => partialF f z l) ⬝ᵥ d) :
    ∃ lam : ℝ, 0 ≤ lam ∧ (∀ l, lam * partialF f z l ≤ w l) ∧
      (fun l => w l - lam * partialF f z l) ⬝ᵥ z = 0 := by
  classical
  set g : Fin n → ℝ := fun l => partialF f z l with hg
  have hgrad : ∀ v, fderiv ℝ f z v = g ⬝ᵥ v := fun v => by
    rw [fderiv_apply_eq_gradient_dot]; rfl
  -- generators: `g` and the unit vectors of the binding nonnegativity constraints
  let gen : Unit ⊕ {l // z l = 0} → Fin n → ℝ := Sum.elim (fun _ => g) fun l => Pi.single l.1 1
  have hcone : ∃ μ : Unit ⊕ {l // z l = 0} → ℝ, 0 ≤ μ ∧ w = ∑ i, μ i • gen i := by
    rw [farkas]
    rintro ⟨y, hy, hyw⟩
    obtain ⟨d0, hd0, hgd0⟩ := hcq
    set d := -y with hd
    have hgd : 0 ≤ g ⬝ᵥ d := by
      have := hy (Sum.inl ())
      simp only [gen, Sum.elim_inl] at this
      rw [hd, dotProduct_neg, dotProduct_comm]; linarith
    have hdl : ∀ l, z l = 0 → 0 ≤ d l := by
      intro l hl
      have := hy (Sum.inr ⟨l, hl⟩)
      simp only [gen, Sum.elim_inr, dotProduct_single, mul_one] at this
      simp only [hd, Pi.neg_apply]; linarith
    have hwd : w ⬝ᵥ d < 0 := by rw [hd, dotProduct_neg, dotProduct_comm]; linarith
    -- perturb by the qualification direction
    set ε := -(w ⬝ᵥ d) / (2 * (|w ⬝ᵥ d0| + 1)) with hε
    have hεpos : 0 < ε := div_pos (by linarith) (by positivity)
    set e := d + ε • d0 with he
    have hge : 0 < g ⬝ᵥ e := by
      rw [he, dotProduct_add, dotProduct_smul, smul_eq_mul]; nlinarith
    have hwe : w ⬝ᵥ e < 0 := by
      rw [he, dotProduct_add, dotProduct_smul, smul_eq_mul]
      have h1 : ε * (w ⬝ᵥ d0) ≤ ε * |w ⬝ᵥ d0| := mul_le_mul_of_nonneg_left (le_abs_self _)
        hεpos.le
      have h2 : ε * (|w ⬝ᵥ d0| + 1) = -(w ⬝ᵥ d) / 2 := by rw [hε]; field_simp
      nlinarith
    have hel : ∀ l, z l = 0 → 0 ≤ e l := fun l hl => by
      simp only [he, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact add_nonneg (hdl l hl) (mul_nonneg hεpos.le (hd0 l hl))
    -- feasibility along `z + t e` for small `t > 0`
    have hline := mc_line_hasDerivAt hf.hasFDerivAt e
    rw [hgrad] at hline
    have hfup := eventually_lt_of_hasDerivAt_neg hline.neg (neg_lt_zero.mpr hge)
    have hpos : ∀ l, ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 ≤ z l + t * e l := by
      intro l
      by_cases hl : z l = 0
      · filter_upwards [self_mem_nhdsWithin] with t ht
        rw [hl, zero_add]; exact mul_nonneg (le_of_lt ht) (hel l hl)
      · have hzl : 0 < z l := lt_of_le_of_ne (hz.1.1 l) (Ne.symm hl)
        have hc : Continuous fun t : ℝ => z l + t * e l := by fun_prop
        have := hc.continuousAt (x := 0) |>.eventually (eventually_gt_nhds (by simpa using hzl))
        exact (Filter.Eventually.filter_mono nhdsWithin_le_nhds this).mono fun t ht => ht.le
    obtain ⟨t, ⟨htf, htpos⟩, ht⟩ := ((hfup.and (eventually_all.mpr hpos)).and
      self_mem_nhdsWithin).exists
    simp only [Pi.neg_apply, zero_smul, add_zero, neg_lt_neg_iff] at htf
    have htz : (0 : ℝ) < t := ht
    have hmem : z + t • e ∈ inputReq f q := by
      refine ⟨fun l => ?_, by rw [← hbind]; exact htf.le⟩
      simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using htpos l
    have := hz.2 _ hmem
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul] at this
    nlinarith
  obtain ⟨μ, hμ, hwμ⟩ := hcone
  set lam := μ (Sum.inl ())
  have hwsplit : ∀ l, w l = lam * partialF f z l + ∑ i : {l // z l = 0}, μ (Sum.inr i) *
      (Pi.single i.1 1 : Fin n → ℝ) l := by
    intro l
    have := congrFun hwμ l
    rw [Fintype.sum_sum_type] at this
    simpa [gen, Finset.sum_apply, lam] using this
  refine ⟨lam, hμ _, fun l => ?_, ?_⟩
  · rw [hwsplit l]
    have : 0 ≤ ∑ i : {l // z l = 0}, μ (Sum.inr i) * (Pi.single i.1 1 : Fin n → ℝ) l :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hμ _)
        ((Pi.single_nonneg.mpr zero_le_one : (0 : Fin n → ℝ) ≤ Pi.single i.1 1) l)
    linarith
  · apply Finset.sum_eq_zero
    intro l _
    change (w l - lam * partialF f z l) * z l = 0
    rw [hwsplit l, add_sub_cancel_left, Finset.sum_mul]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hil : i.1 = l
    · rw [← hil, i.2, mul_zero]
    · simp [Ne.symm hil]

/-- **(5.C.4)** needs a constraint qualification (correction): for `f(z) = (z - 1)³ + 1` (one
input, increasing), `w = 1` and `q = 1`, the CMP is solved by `z* = 1`, where `f'(1) = 0`, and no
`λ` satisfies `w ≥ λf'(z*)` with `[w - λf'(z*)]z* = 0`. -/
theorem foc_5_C_4_needs_cq :
    let f : (Fin 1 → ℝ) → ℝ := fun z => (z 0 - 1) ^ 3 + 1
    (1 : Fin 1 → ℝ) ∈ condDemand f 1 1 ∧ partialF f 1 0 = 0 ∧
      ¬ ∃ lam : ℝ, (fun l => (1 : Fin 1 → ℝ) l - lam * partialF f 1 l) ⬝ᵥ 1 = 0 := by
  intro f
  have hpart : partialF f 1 0 = 0 := by
    have hd : DifferentiableAt ℝ f 1 := by fun_prop
    have h1 := mc_line_hasDerivAt hd.hasFDerivAt (Pi.single 0 1)
    have heq : (fun t : ℝ => f (1 + t • Pi.single 0 1)) = fun t => t ^ 3 + 1 := by
      funext t; simp [f]
    rw [heq] at h1
    have h2 : HasDerivAt (fun t : ℝ => t ^ 3 + 1) (↑3 * (0 : ℝ) ^ 2) 0 :=
      (hasDerivAt_pow 3 (0 : ℝ)).add_const 1
    have := h1.unique h2
    simpa [partialF] using this
  refine ⟨⟨⟨fun _ => zero_le_one, by simp [f]⟩, fun z hz => ?_⟩, hpart, ?_⟩
  · have h1 : (1 : ℝ) ≤ (z 0 - 1) ^ 3 + 1 := hz.2
    have h2 : 0 ≤ (z 0 - 1) ^ 3 := by linarith
    have h3 : 1 ≤ z 0 := by
      by_contra h
      have : (z 0 - 1) ^ 3 < 0 := Odd.pow_neg (by decide) (by linarith)
      linarith
    simp [dotProduct]; linarith
  · rintro ⟨lam, h⟩
    simp [dotProduct, hpart] at h

/-! ### Exercise 5.C.6 -/

/-- **Exercise 5.C.6(a)-(b)** (MWG, p. 161). Let `z(p)` be the profit-maximizing input vector as a
differentiable function of the output price near `p̄ > 0` (the implicit function theorem gives
it when `D²f(z̄)` is invertible), satisfying the first-order conditions `p∇f(z(p)) = w̄`, with
`∇f` differentiable at `z̄ = z(p̄)` with negative definite Hessian `H`, and `w̄ ≫ 0`. Then
(a) output rises with the price, `dq/dp = ∇f(z̄)·z'(p̄) > 0`, and (b) some input demand rises. -/
theorem exercise_5_C_6_ab (hn : 0 < n) {G : (Fin n → ℝ) → (Fin n → ℝ)}
    {H : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)} {zf : ℝ → Fin n → ℝ} {zp w : Fin n → ℝ} {p : ℝ}
    (hp : 0 < p) (hw : StrictlyPositive w) (hfoc : ∀ᶠ t in 𝓝 p, t • G (zf t) = w)
    (hzd : HasDerivAt zf zp p) (hG : HasFDerivAt G H (zf p)) (hneg : NegDef (jacobian H)) :
    0 < G (zf p) ⬝ᵥ zp ∧ ∃ l, 0 < zp l := by
  have hcomp : HasDerivAt (fun t => G (zf t)) (H zp) p := hG.comp_hasDerivAt p hzd
  have hprod : HasDerivAt (fun t => t • G (zf t)) (p • H zp + (1 : ℝ) • G (zf p)) p :=
    (hasDerivAt_id p).smul hcomp
  have hconst : HasDerivAt (fun t => t • G (zf t)) 0 p :=
    (hasDerivAt_const p w).congr_of_eventuallyEq hfoc
  have hid : p • H zp + G (zf p) = 0 := by
    have := hprod.unique hconst
    rwa [one_smul] at this
  have hgpos : ∀ l, 0 < G (zf p) l := by
    intro l
    have h1 := congrFun hfoc.self_of_nhds l
    simp only [Pi.smul_apply, smul_eq_mul] at h1
    have := hw l
    rw [← h1] at this
    exact pos_of_mul_pos_right this hp.le
  have hzp0 : zp ≠ 0 := by
    intro h0
    rw [h0, map_zero, smul_zero, zero_add] at hid
    have := hgpos ⟨0, hn⟩
    rw [hid] at this
    exact lt_irrefl 0 this
  have hq := hneg zp hzp0
  rw [jacobian_mulVec] at hq
  have hG' : G (zf p) = -(p • H zp) := by
    rw [add_comm] at hid
    exact eq_neg_of_add_eq_zero_left hid
  have hdot : G (zf p) ⬝ᵥ zp = -p * (zp ⬝ᵥ H zp) := by
    rw [hG', neg_dotProduct, smul_dotProduct, smul_eq_mul, dotProduct_comm]; ring
  have ha : 0 < G (zf p) ⬝ᵥ zp := by rw [hdot]; nlinarith
  refine ⟨ha, ?_⟩
  by_contra hall
  push Not at hall
  have : G (zf p) ⬝ᵥ zp ≤ 0 :=
    Finset.sum_nonpos fun l _ => mul_nonpos_of_nonneg_of_nonpos (hgpos l).le (hall l)
  linarith

/-- **Exercise 5.C.6(c)** (MWG, p. 161). Under the same hypotheses, with `z(w_ℓ)` the
profit-maximizing input vector as a differentiable function of the `ℓ`-th input price
(`p̄∇f(z) = w̄ + t e_ℓ`), the demand for input `ℓ` falls: `∂z_ℓ/∂w_ℓ < 0`. -/
theorem exercise_5_C_6_c {G : (Fin n → ℝ) → (Fin n → ℝ)} {H : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    {zf : ℝ → Fin n → ℝ} {zl w : Fin n → ℝ} {p : ℝ} (hp : 0 < p) (l : Fin n)
    (hfoc : ∀ᶠ t in 𝓝 0, p • G (zf t) = w + t • Pi.single l 1) (hzd : HasDerivAt zf zl 0)
    (hG : HasFDerivAt G H (zf 0)) (hneg : NegDef (jacobian H)) :
    p • H zl = Pi.single l 1 ∧ zl l < 0 := by
  have hcomp : HasDerivAt (fun t => p • G (zf t)) (p • H zl) 0 :=
    (hG.comp_hasDerivAt 0 hzd).const_smul p
  have hrhs : HasDerivAt (fun t : ℝ => w + t • (Pi.single l 1 : Fin n → ℝ)) (Pi.single l 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single l 1 : Fin n → ℝ)).const_add w
  have hid : p • H zl = Pi.single l 1 := hcomp.unique (hrhs.congr_of_eventuallyEq hfoc)
  refine ⟨hid, ?_⟩
  have hzl0 : zl ≠ 0 := by
    intro h0
    rw [h0, map_zero, smul_zero] at hid
    have := congrFun hid l
    simp at this
  have hq := hneg zl hzl0
  rw [jacobian_mulVec] at hq
  have hH : H zl = p⁻¹ • Pi.single l 1 := by
    rw [← hid, smul_smul, inv_mul_cancel₀ hp.ne', one_smul]
  rw [hH, dotProduct_smul, dotProduct_single, mul_one, smul_eq_mul] at hq
  have := mul_neg_iff.mp hq
  rcases this with ⟨h1, h2⟩ | ⟨h1, _⟩
  · exact h2
  · exact absurd h1 (not_lt.mpr (inv_nonneg.mpr hp.le))

/-! ### Exercise 5.C.7 -/

open Matrix in
/-- **Exercise 5.C.7** (MWG, p. 161), corrected (two inputs): if the Hessian `H` is negative
definite with positive cross partials (`∂²f/∂z₁∂z₂ > 0`, complementary inputs), then the solution
`v` of `pHv = e_k` (the derivative of the input demands in `w_k`) has `v_ℓ < 0` for `ℓ ≠ k`, and the
solution of `pHv = -∇f` (the derivative in `p`) is `≫ 0` when `∇f ≫ 0`. -/
theorem exercise_5_C_7_corrected {H : Matrix (Fin 2) (Fin 2) ℝ} (hneg : NegDef H)
    (h01 : 0 < H 0 1) (h10 : 0 < H 1 0) {p : ℝ} (hp : 0 < p) :
    (∀ v : Fin 2 → ℝ, p • H *ᵥ v = Pi.single 1 1 → v 0 < 0) ∧
      (∀ v : Fin 2 → ℝ, p • H *ᵥ v = Pi.single 0 1 → v 1 < 0) ∧
      (∀ g v : Fin 2 → ℝ, StrictlyPositive g → p • H *ᵥ v = -g → 0 < v 0 ∧ 0 < v 1) := by
  have ha : H 0 0 < 0 := by
    have := hneg ![1, 0] (by intro h; simpa using congrFun h 0)
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have hd : H 1 1 < 0 := by
    have := hneg ![0, 1] (by intro h; simpa using congrFun h 1)
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have hdet : 0 < H 0 0 * H 1 1 - H 0 1 * H 1 0 := by
    have := hneg ![H 1 1 - H 1 0, H 0 0 - H 0 1] ?_
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at this
      nlinarith
    · intro h
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      simp at h0 h1
      linarith
  have hsolve : ∀ v r : Fin 2 → ℝ, p • H *ᵥ v = r →
      p * (H 0 0 * v 0 + H 0 1 * v 1) = r 0 ∧ p * (H 1 0 * v 0 + H 1 1 * v 1) = r 1 := by
    intro v r h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
    constructor <;> linarith
  have hdp := mul_pos hdet hp
  refine ⟨fun v hv => ?_, fun v hv => ?_, fun g v hg hv => ?_⟩
  · obtain ⟨e0, e1⟩ := hsolve v _ hv
    simp only [Fin.isValue, ne_eq, zero_ne_one, not_false_eq_true, Pi.single_eq_of_ne,
      Pi.single_eq_same] at e0 e1
    have key : (H 0 0 * H 1 1 - H 0 1 * H 1 0) * p * v 0 = -H 0 1 := by
      linear_combination H 1 1 * e0 - H 0 1 * e1
    by_contra hv0
    push Not at hv0
    nlinarith
  · obtain ⟨e0, e1⟩ := hsolve v _ hv
    simp only [Fin.isValue, ne_eq, one_ne_zero, not_false_eq_true, Pi.single_eq_of_ne,
      Pi.single_eq_same] at e0 e1
    have key : (H 0 0 * H 1 1 - H 0 1 * H 1 0) * p * v 1 = -H 1 0 := by
      linear_combination H 0 0 * e1 - H 1 0 * e0
    by_contra hv1
    push Not at hv1
    nlinarith
  · obtain ⟨e0, e1⟩ := hsolve v _ hv
    have g0 := hg 0
    have g1 := hg 1
    simp only [Pi.neg_apply] at e0 e1
    have key0 : (H 0 0 * H 1 1 - H 0 1 * H 1 0) * p * v 0 = -H 1 1 * g 0 + H 0 1 * g 1 := by
      linear_combination H 1 1 * e0 - H 0 1 * e1
    have key1 : (H 0 0 * H 1 1 - H 0 1 * H 1 0) * p * v 1 = -H 0 0 * g 1 + H 1 0 * g 0 := by
      linear_combination H 0 0 * e1 - H 1 0 * e0
    constructor
    · by_contra h; push Not at h; nlinarith
    · by_contra h; push Not at h; nlinarith

open Matrix in
/-- **Exercise 5.C.7** (MWG, p. 161) is false as printed (correction): with negative cross
partials the cross-price effects are positive. For the negative definite Hessian
`H = [[-3/4, -1/4], [-1/4, -3/4]]` (that of `f(z) = -e^{-z₁} - e^{-z₂} - e^{-z₁-z₂}` at
`z₁ = z₂ = ln 2`, an increasing, strictly concave `f` with `∂²f/∂z₁∂z₂ < 0`) and `p = 1`, any
differentiable input demand satisfying the first-order conditions has `∂z₁/∂w₂ = 1/2 > 0`. -/
theorem exercise_5_C_7_counterexample :
    let H : Matrix (Fin 2) (Fin 2) ℝ := !![-3 / 4, -1 / 4; -1 / 4, -3 / 4]
    NegDef H ∧ H 0 1 < 0 ∧ ∀ v : Fin 2 → ℝ, (1 : ℝ) • H *ᵥ v = Pi.single 1 1 → v 0 = 1 / 2 := by
  intro H
  refine ⟨fun z hz => ?_, by simp [H]; norm_num, fun v hv => ?_⟩
  · have : z 0 ≠ 0 ∨ z 1 ≠ 0 := by
      by_contra h
      push Not at h
      exact hz (funext fun i => by fin_cases i <;> simp [h.1, h.2])
    have hform : z ⬝ᵥ H *ᵥ z = -(3 / 4) * z 0 ^ 2 - (1 / 2) * z 0 * z 1 - (3 / 4) * z 1 ^ 2 := by
      simp [H, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      ring
    rw [hform]
    rcases this with h | h
    · have := sq_pos_of_ne_zero h; nlinarith [sq_nonneg (z 0 + z 1), sq_nonneg (z 1)]
    · have := sq_pos_of_ne_zero h; nlinarith [sq_nonneg (z 0 + z 1), sq_nonneg (z 0)]
  · have h0 := congrFun hv 0
    have h1 := congrFun hv 1
    simp [H, dotProduct, Fin.sum_univ_two] at h0 h1
    linarith

/-! ### Exercise 5.C.8 -/

/-- **Exercise 5.C.8** (MWG, p. 161). The observations of months 3 and 95 (both producing
`q = 60` at output price `4`; month 3 inputs `(40, 50)` at prices `(3, 1)`, month 95 inputs
`(55, 40)` at prices `(2, 2)`) cannot both be profit maximizing for any fixed technology: at
month-95 prices the month-3 plan is more profitable (`60 > 50`); the month-95 inputs are not
cost minimizing. -/
theorem exercise_5_C_8 (Y : Set (Fin 3 → ℝ)) :
    ¬ ((![-40, -50, 60] : Fin 3 → ℝ) ∈ supply Y ![3, 1, 4] ∧
      (![-55, -40, 60] : Fin 3 → ℝ) ∈ supply Y ![2, 2, 4]) := by
  rintro ⟨h3, h95⟩
  have := h95.2 _ h3.1
  simp [dotProduct, Fin.sum_univ_three] at this
  norm_num at this

/-! ### Exercises 5.C.9 and 5.C.10 -/

/-- **Exercise 5.C.10(a)** (MWG, p. 162). For `f(z) = z₁ + z₂` (perfect substitutes), `w ≫ 0` and
`q ≥ 0`: `c(w, q) = q min{w₁, w₂}`. -/
theorem exercise_5_C_10a {w : Fin 2 → ℝ} (hw : StrictlyPositive w) {q : ℝ} (hq : 0 ≤ q) :
    costFn (fun z => z 0 + z 1) w q = q * min (w 0) (w 1) := by
  apply le_antisymm
  · rcases le_total (w 0) (w 1) with h | h
    · rw [min_eq_left h]
      have hm : (![q, 0] : Fin 2 → ℝ) ∈ inputReq (fun z => z 0 + z 1) q :=
        ⟨fun i => by fin_cases i <;> simp [hq], by simp⟩
      calc costFn (fun z => z 0 + z 1) w q ≤ w ⬝ᵥ ![q, 0] :=
            supportFn_le (bddBelow_of_subset_nonneg (inputReq_subset_nonneg _ q)
              (fun i => (hw i).le)) hm
        _ = q * w 0 := by simp [dotProduct, Fin.sum_univ_two]; ring
    · rw [min_eq_right h]
      have hm : (![0, q] : Fin 2 → ℝ) ∈ inputReq (fun z => z 0 + z 1) q :=
        ⟨fun i => by fin_cases i <;> simp [hq], by simp⟩
      calc costFn (fun z => z 0 + z 1) w q ≤ w ⬝ᵥ ![0, q] :=
            supportFn_le (bddBelow_of_subset_nonneg (inputReq_subset_nonneg _ q)
              (fun i => (hw i).le)) hm
        _ = q * w 1 := by simp [dotProduct, Fin.sum_univ_two]; ring
  · have hne : (inputReq (fun z : Fin 2 → ℝ => z 0 + z 1) q).Nonempty :=
      ⟨![q, 0], fun i => by fin_cases i <;> simp [hq], by simp⟩
    apply le_supportFn hne
    intro z hz
    have h0 : 0 ≤ z 0 := hz.1 0
    have h1 : 0 ≤ z 1 := hz.1 1
    have hq' : q ≤ z 0 + z 1 := hz.2
    simp only [dotProduct, Fin.sum_univ_two]
    have m0 := min_le_left (w 0) (w 1)
    have m1 := min_le_right (w 0) (w 1)
    have hmin : 0 ≤ min (w 0) (w 1) := le_min (hw 0).le (hw 1).le
    nlinarith

/-- **Exercise 5.C.10(b)** (MWG, p. 162). For the Leontief technology `f(z) = min{z₁, z₂}`,
`w ≫ 0` and `q ≥ 0`: `c(w, q) = q(w₁ + w₂)` and `z(w, q) = {(q, q)}`. -/
theorem exercise_5_C_10b {w : Fin 2 → ℝ} (hw : StrictlyPositive w) {q : ℝ} (hq : 0 ≤ q) :
    condDemand (fun z => min (z 0) (z 1)) w q = {![q, q]} ∧
      costFn (fun z => min (z 0) (z 1)) w q = q * (w 0 + w 1) := by
  have hmem : (![q, q] : Fin 2 → ℝ) ∈ inputReq (fun z => min (z 0) (z 1)) q :=
    ⟨fun i => by fin_cases i <;> simp [hq], by simp⟩
  have hdem : condDemand (fun z => min (z 0) (z 1)) w q = {![q, q]} := by
    ext z
    simp only [Set.mem_singleton_iff]
    constructor
    · rintro ⟨hz, hmin⟩
      have h1 := hmin _ hmem
      have a0 : q ≤ z 0 := (le_min_iff.mp hz.2).1
      have a1 : q ≤ z 1 := (le_min_iff.mp hz.2).2
      simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h1
      have e0 : z 0 = q := by nlinarith [hw 0, hw 1]
      have e1 : z 1 = q := by nlinarith [hw 0, hw 1]
      funext i; fin_cases i <;> simp [e0, e1]
    · rintro rfl
      refine ⟨hmem, fun z hz => ?_⟩
      have a0 : q ≤ z 0 := (le_min_iff.mp hz.2).1
      have a1 : q ≤ z 1 := (le_min_iff.mp hz.2).2
      simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      nlinarith [hw 0, hw 1]
  refine ⟨hdem, ?_⟩
  have hx : (![q, q] : Fin 2 → ℝ) ∈ condDemand (fun z => min (z 0) (z 1)) w q := by
    rw [hdem]; rfl
  rw [costFn, supportFn_eq_of_mem_argmin hx]
  simp [dotProduct, Fin.sum_univ_two]; ring

/-- **Exercise 5.C.10(c)** (MWG, p. 162). For the CES technology `f(z) = (z₁^ρ + z₂^ρ)^{1/ρ}`
(`ρ < 1`, `ρ ≠ 0`), the CMP is the EMP of Exercise 3.E.6: `c(w, q) = q(w₁^r + w₂^r)^{1/r}` with
`r = ρ/(ρ-1)`, and `z(w, q)` is the CES Hicksian demand. (`ρ = 1` is part (a).) -/
theorem exercise_5_C_10c {ρ : ℝ} (hρ1 : ρ < 1) (hρ0 : ρ ≠ 0) {w : Fin 2 → ℝ}
    (hw : StrictlyPositive w) {q : ℝ} (hq : 0 ≤ q) :
    costFn (cesUtility ρ) w q = q * cesSum ρ w ^ (1 / cesR ρ) ∧
      condDemand (cesUtility ρ) w q = {cesHicks ρ w q} := by
  have hV : inputReq (cesUtility ρ) q = empConstraintSet (cesUtility ρ) q := by
    ext z; exact ⟨fun h => ⟨fun l => h.1 l, h.2⟩, fun h => ⟨fun l => h.1 l, h.2⟩⟩
  constructor
  · rw [costFn, hV, ← expenditure_eq_supportFn, exercise_3_E_6_expenditure hρ1 hρ0 hw hq]
    rfl
  · rw [condDemand, hV]
    exact exercise_3_E_6_hicksian hρ1 hρ0 hw hq

/-- **Exercise 5.C.9(a)** (MWG, p. 161). For `f(z) = √(z₁ + z₂)`, `w ≫ 0`, `p > 0`, with
`m = min{w₁, w₂}`: profits satisfy `pf(z) - w·z ≤ p²/(4m)` for every `z ≥ 0`, with equality at
`q = p/(2m)` using only the cheaper input; so `π(p, w) = p²/(4m)`. -/
theorem exercise_5_C_9a {w : Fin 2 → ℝ} (hw : StrictlyPositive w) {p : ℝ} (hp : 0 < p) :
    (∀ z : Fin 2 → ℝ, 0 ≤ z →
      p * Real.sqrt (z 0 + z 1) - w ⬝ᵥ z ≤ p ^ 2 / (4 * min (w 0) (w 1))) ∧
    ∃ z : Fin 2 → ℝ, 0 ≤ z ∧
      p * Real.sqrt (z 0 + z 1) - w ⬝ᵥ z = p ^ 2 / (4 * min (w 0) (w 1)) := by
  set m := min (w 0) (w 1) with hm
  have hm0 : 0 < m := lt_min (hw 0) (hw 1)
  constructor
  · intro z hz
    have h0 : 0 ≤ z 0 := hz 0
    have h1 : 0 ≤ z 1 := hz 1
    set s := Real.sqrt (z 0 + z 1)
    have hs : s ^ 2 = z 0 + z 1 := Real.sq_sqrt (by linarith)
    have hwz : m * (z 0 + z 1) ≤ w ⬝ᵥ z := by
      simp only [dotProduct, Fin.sum_univ_two]
      nlinarith [min_le_left (w 0) (w 1), min_le_right (w 0) (w 1)]
    rw [le_div_iff₀ (by positivity)]
    have h4 := mul_le_mul_of_nonneg_left hwz (by positivity : (0 : ℝ) ≤ 4 * m)
    have h5 : 4 * m * (m * s ^ 2) ≤ 4 * m * (w ⬝ᵥ z) := by rw [hs]; exact h4
    nlinarith [sq_nonneg (2 * m * s - p), h5]
  · set q := p / (2 * m)
    have hq : 0 ≤ q := by positivity
    rcases le_total (w 0) (w 1) with h | h
    · refine ⟨![q ^ 2, 0], fun i => by fin_cases i <;> simp [sq_nonneg], ?_⟩
      have hmw : m = w 0 := min_eq_left h
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, add_zero, Real.sqrt_sq hq,
        dotProduct, Fin.sum_univ_two, mul_zero]
      simp only [q, hmw]
      have := hw 0
      field_simp
      ring
    · refine ⟨![0, q ^ 2], fun i => by fin_cases i <;> simp [sq_nonneg], ?_⟩
      have hmw : m = w 1 := min_eq_right h
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zero_add, Real.sqrt_sq hq,
        dotProduct, Fin.sum_univ_two, mul_zero]
      simp only [q, hmw]
      have := hw 1
      field_simp
      ring

/-- **Exercise 5.C.9(b)** (MWG, p. 162). For `f(z) = √(min{z₁, z₂})`, `w ≫ 0`, `p > 0`: profits
are at most `p²/(4(w₁ + w₂))`, attained at `z₁ = z₂ = (p/(2(w₁ + w₂)))²`. -/
theorem exercise_5_C_9b {w : Fin 2 → ℝ} (hw : StrictlyPositive w) {p : ℝ} (hp : 0 < p) :
    (∀ z : Fin 2 → ℝ, 0 ≤ z →
      p * Real.sqrt (min (z 0) (z 1)) - w ⬝ᵥ z ≤ p ^ 2 / (4 * (w 0 + w 1))) ∧
    p * Real.sqrt (min ((p / (2 * (w 0 + w 1))) ^ 2) ((p / (2 * (w 0 + w 1))) ^ 2)) -
      w ⬝ᵥ ![(p / (2 * (w 0 + w 1))) ^ 2, (p / (2 * (w 0 + w 1))) ^ 2] =
        p ^ 2 / (4 * (w 0 + w 1)) := by
  have hW : 0 < w 0 + w 1 := add_pos (hw 0) (hw 1)
  constructor
  · intro z hz
    have h0 : 0 ≤ z 0 := hz 0
    have h1 : 0 ≤ z 1 := hz 1
    set mz := min (z 0) (z 1)
    have hmz : 0 ≤ mz := le_min h0 h1
    set s := Real.sqrt mz
    have hs : s ^ 2 = mz := Real.sq_sqrt hmz
    have hwz : (w 0 + w 1) * mz ≤ w ⬝ᵥ z := by
      simp only [dotProduct, Fin.sum_univ_two]
      nlinarith [min_le_left (z 0) (z 1), min_le_right (z 0) (z 1), hw 0, hw 1]
    rw [le_div_iff₀ (by positivity)]
    have h4 := mul_le_mul_of_nonneg_left hwz (by positivity : (0 : ℝ) ≤ 4 * (w 0 + w 1))
    have h5 : 4 * (w 0 + w 1) * ((w 0 + w 1) * s ^ 2) ≤ 4 * (w 0 + w 1) * (w ⬝ᵥ z) := by
      rw [hs]; exact h4
    nlinarith [sq_nonneg (2 * (w 0 + w 1) * s - p), h5]
  · rw [min_self, Real.sqrt_sq (by positivity)]
    simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp
    ring

/-! ### Exercises 5.C.11-5.C.13 -/

/-- **Exercise 5.C.11** (MWG, p. 162). If `c` is twice differentiable near `(w̄, q̄)` (with
derivative `c'` and second derivative `c''`), then by Shephard's lemma `z_ℓ = ∂c/∂w_ℓ`, and
`∂z_ℓ/∂q = ∂(∂c/∂q)/∂w_ℓ` (symmetry of the second derivative); hence `∂z_ℓ/∂q > 0` iff marginal cost
is increasing in `w_ℓ`. -/
theorem exercise_5_C_11 {c : (Fin n → ℝ) × ℝ → ℝ} {c' : (Fin n → ℝ) × ℝ → (Fin n → ℝ) × ℝ →L[ℝ] ℝ}
    {c'' : (Fin n → ℝ) × ℝ →L[ℝ] (Fin n → ℝ) × ℝ →L[ℝ] ℝ} {x : (Fin n → ℝ) × ℝ}
    (hc : ∀ᶠ y in 𝓝 x, HasFDerivAt c (c' y) y) (hc' : HasFDerivAt c' c'' x) (l : Fin n) :
    c'' (0, 1) (Pi.single l 1, 0) = c'' (Pi.single l 1, 0) (0, 1) ∧
      (0 < c'' (0, 1) (Pi.single l 1, 0) ↔ 0 < c'' (Pi.single l 1, 0) (0, 1)) := by
  have := second_derivative_symmetric_of_eventually hc hc' (0, 1) (Pi.single l 1, 0)
  exact ⟨this, by rw [this]⟩

/-- **Exercise 5.C.12** (MWG, p. 162). Let `Y' = {α(y, -1) : y ∈ Y, α ≥ 0}` (Proposition 5.B.2).
If `y ∈ y(p)`, then `(y, -1)` maximizes profits on `Y'` at prices `(p, π(p))`; conversely, if
`(y, -1)` maximizes profits on `Y'` at `(p, p_{L+1})`, then `y ∈ y(p)` and `π(p) = p_{L+1}`. -/
theorem exercise_5_C_12 {L : ℕ} (Y : Set (Fin L → ℝ)) (p y : Fin L → ℝ) (pL : ℝ) :
    let Y' : Set (Fin (L + 1) → ℝ) := {v | ∃ y ∈ Y, ∃ α : ℝ, 0 ≤ α ∧ v = α • extendVec y (-1)}
    (y ∈ supply Y p → extendVec y (-1) ∈ supply Y' (extendVec p (p ⬝ᵥ y))) ∧
      (y ∈ Y → extendVec y (-1) ∈ supply Y' (extendVec p pL) → y ∈ supply Y p ∧ p ⬝ᵥ y = pL) := by
  intro Y'
  have hdot : ∀ (u : Fin L → ℝ) (a b : ℝ) (v : Fin L → ℝ),
      extendVec u a ⬝ᵥ extendVec v b = u ⬝ᵥ v + a * b := by
    intro u a b v
    simp only [extendVec, dotProduct, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
  constructor
  · intro hy
    refine ⟨⟨y, hy.1, 1, zero_le_one, by rw [one_smul]⟩, ?_⟩
    rintro _ ⟨y', hy', α, hα, rfl⟩
    rw [dotProduct_smul, hdot, hdot, smul_eq_mul]
    have := hy.2 y' hy'
    nlinarith
  · intro hyY hy
    have h0 : (0 : Fin (L + 1) → ℝ) ∈ Y' := ⟨y, hyY, 0, le_rfl, by rw [zero_smul]⟩
    have hmax0 := hy.2 0 h0
    rw [dotProduct_zero, hdot] at hmax0
    have hle : ∀ y' ∈ Y, p ⬝ᵥ y' - pL ≤ p ⬝ᵥ y - pL := by
      intro y' hy'
      have := hy.2 _ ⟨y', hy', 1, zero_le_one, rfl⟩
      rw [one_smul, hdot, hdot] at this
      linarith
    have hge : 0 ≤ p ⬝ᵥ y - pL := by linarith
    have hle0 : p ⬝ᵥ y - pL ≤ 0 := by
      have := hy.2 (2 • extendVec y (-1)) ⟨y, hyY, 2, by norm_num, rfl⟩
      rw [dotProduct_smul, hdot, smul_eq_mul] at this
      linarith
    exact ⟨⟨hyY, fun y' hy' => by linarith [hle y' hy']⟩, by linarith⟩

/-- **Exercise 5.C.13** (MWG, p. 162). A revenue-maximizing firm with cash constraint `w·z ≤ C`
and maximal output `f*(w, C)` with `pf*(w, C) = R(p, w, C) = p[γ + ln C - α ln w₁ - (1-α) ln w₂]`:
at its choice `z ≫ 0` (on the budget line, `f(z) = f*(w̄, C̄)`) the use of input 1 is
`z₁ = αC̄/w̄₁` (Roy's identity: `z` remains affordable when prices move along `C = w·z`, so
`w ↦ f*(w, w·z)` is minimized at `w̄`). -/
theorem exercise_5_C_13 {γ α : ℝ} {f : (Fin 2 → ℝ) → ℝ} {w z : Fin 2 → ℝ} {C : ℝ}
    (hw : StrictlyPositive w) (hC : 0 < C) (hz : StrictlyPositive z) (hbud : w ⬝ᵥ z = C)
    (hval : f z = γ + Real.log C - α * Real.log (w 0) - (1 - α) * Real.log (w 1))
    (hbound : ∀ (w' : Fin 2 → ℝ) (C' : ℝ), StrictlyPositive w' → 0 < C' → w' ⬝ᵥ z ≤ C' →
      f z ≤ γ + Real.log C' - α * Real.log (w' 0) - (1 - α) * Real.log (w' 1)) :
    z 0 = α * C / w 0 := by
  -- `g(t) = value at prices (w₁ + t, w₂) and budget (w₁ + t)z₁ + w₂z₂` is minimized at `t = 0`
  set g : ℝ → ℝ := fun t => γ + Real.log ((w 0 + t) * z 0 + w 1 * z 1) - α * Real.log (w 0 + t)
    - (1 - α) * Real.log (w 1)
  have hCe : w 0 * z 0 + w 1 * z 1 = C := by rw [← hbud]; simp [dotProduct, Fin.sum_univ_two]
  have hmin : IsLocalMin g 0 := by
    have hev : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < w 0 + t :=
      (continuous_const.add continuous_id).continuousAt.eventually
        (eventually_gt_nhds (by simpa using hw 0))
    filter_upwards [hev] with t ht
    have hw' : StrictlyPositive ![w 0 + t, w 1] := fun i => by fin_cases i <;> simp [ht, hw 1]
    have hC' : 0 < (w 0 + t) * z 0 + w 1 * z 1 := by nlinarith [hz 0, hz 1, hw 1]
    have := hbound ![w 0 + t, w 1] _ hw' hC' (by simp [dotProduct, Fin.sum_univ_two])
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
    simp only [g, add_zero, hCe]
    linarith
  have hd : HasDerivAt g (z 0 / C - α / w 0) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => (w 0 + t) * z 0 + w 1 * z 1) (z 0) 0 := by
      simpa using (((hasDerivAt_id (0 : ℝ)).const_add (w 0)).mul_const (z 0)).add_const
        (w 1 * z 1)
    have h2 := h1.log (by simp [hCe, hC.ne'])
    have h3 : HasDerivAt (fun t : ℝ => w 0 + t) 1 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_add (w 0)
    have h4 := (h3.log (by simp [(hw 0).ne'])).const_mul α
    have h5 := ((h2.const_add γ).sub h4).sub_const ((1 - α) * Real.log (w 1))
    simp only [add_zero, hCe] at h5
    convert h5 using 1
    ring
  have := hmin.hasDerivAt_eq_zero hd
  have hw0 := (hw 0).ne'
  field_simp at this ⊢
  linarith

end MWG.Production

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercises 5.AA.2-5.AA.5 (MWG, pp. 164-166)

* **Exercise 5.AA.2**: (a) in a productive Leontief model with `b ≫ 0` every plan `[I - A; -b]α` is
  efficient; (b) with `α ≫ 0` the supporting prices (wage `1`) are unique, `p = b(I - A)⁻¹`;
  (c) `p = Σ_k bAᵏ`, labour embodied directly and indirectly; (d) prices supporting the whole
  technology are componentwise below those of any other productive selection of techniques.
* **Exercise 5.AA.3**: (a) the production possibility set `4c₁ + 6c₂ ≤ 10`, (b) prices `(4, 6)`,
  (c) labour embodied, (e) the switch of techniques at `β = 4`.
* **Exercise 5.AA.4**: membership of `y₁, …, y₅`, efficiency of `(0, -5, 5, 0)`, inefficiency of
  `a₁`.
* **Exercise 5.AA.5**: (a)-(c) convexity, no free lunch, no free disposal; (d)-(e) inefficient
  activities (correction: `a₃` and `a₈` are both efficient); (f) the efficient set
  `cone(a₃, a₈) ∪ cone(a₇, a₈)`; (g)-(h) the linear program and its solution `412.5`.
-/

namespace MWG.Production

open MWG.ClassicalDemand MWG.ConsumerChoice Filter Topology

variable {n : ℕ}

open Matrix in
/-- For `A ≥ 0` productive, `T = (I - A)⁻¹` satisfies `T(I - A) = I`, `T ≥ 0` and `T_jj ≥ 1`. -/
theorem leontief_inverse_facts {A : Matrix (Fin n) (Fin n) ℝ} (hA : ∀ i j, 0 ≤ A i j)
    (hprod : Productive A) :
    (1 - A)⁻¹ * (1 - A) = 1 ∧ (1 - A) * (1 - A)⁻¹ = 1 ∧ (∀ i j, 0 ≤ (1 - A)⁻¹ i j) ∧
      ∀ j, 1 ≤ (1 - A)⁻¹ j j := by
  obtain ⟨-, hunit, -, hnn, -⟩ := proposition_5_AA_1_neumann hA hprod
  have hdet : IsUnit (1 - A).det := (Matrix.isUnit_iff_isUnit_det _).mp hunit
  have hl := Matrix.nonsing_inv_mul _ hdet
  have hr := Matrix.mul_nonsing_inv _ hdet
  refine ⟨hl, hr, hnn, fun j => ?_⟩
  have hT : (1 - A)⁻¹ = 1 + (1 - A)⁻¹ * A := by
    have := hl
    rw [Matrix.mul_sub, Matrix.mul_one] at this
    exact sub_eq_iff_eq_add.mp this
  have := congrFun (congrFun hT j) j
  rw [this, Matrix.add_apply, Matrix.one_apply_eq, Matrix.mul_apply]
  have : 0 ≤ ∑ k, (1 - A)⁻¹ j k * A k j :=
    Finset.sum_nonneg fun k _ => mul_nonneg (hnn j k) (hA k j)
  linarith

open Matrix in
/-- **Exercise 5.AA.2(a)** (MWG, p. 164). In a Leontief model with no substitution, `A ≥ 0`
productive and `b ≫ 0`, every plan `y = [I - A; -b]α` with `α ≥ 0` is efficient: it maximizes
profits (zero) at the prices `(b(I - A)⁻¹, 1) ≫ 0`. -/
theorem exercise_5_AA_2a {A : Matrix (Fin n) (Fin n) ℝ} (hA : ∀ i j, 0 ≤ A i j)
    (hprod : Productive A) {b : Fin n → ℝ} (hb : StrictlyPositive b) {α : Fin n → ℝ}
    (hα : 0 ≤ α) :
    extendVec ((1 - A) *ᵥ α) (-(b ⬝ᵥ α)) ∈
        supply (leontiefSet A b) (extendVec (b ᵥ* (1 - A)⁻¹) 1) ∧
      Efficient (leontiefSet A b) (extendVec ((1 - A) *ᵥ α) (-(b ⬝ᵥ α))) := by
  obtain ⟨hl, -, hnn, hdiag⟩ := leontief_inverse_facts hA hprod
  set pr := b ᵥ* (1 - A)⁻¹ with hpr
  have hdot : ∀ (u : Fin n → ℝ) (t : ℝ), extendVec pr 1 ⬝ᵥ extendVec u t = pr ⬝ᵥ u + t := by
    intro u t
    simp [extendVec, dotProduct, Fin.sum_univ_castSucc]
  have hzero : ∀ α' : Fin n → ℝ, pr ⬝ᵥ ((1 - A) *ᵥ α') = b ⬝ᵥ α' := by
    intro α'
    rw [Matrix.dotProduct_mulVec, hpr, Matrix.vecMul_vecMul, hl, Matrix.vecMul_one]
  have hprpos : StrictlyPositive pr := by
    intro j
    have : b j * 1 ≤ pr j := by
      simp only [hpr, Matrix.vecMul, dotProduct]
      calc b j * 1 ≤ b j * (1 - A)⁻¹ j j := mul_le_mul_of_nonneg_left (hdiag j) (hb j).le
        _ ≤ ∑ i, b i * (1 - A)⁻¹ i j := Finset.single_le_sum (f := fun i => b i * (1 - A)⁻¹ i j)
            (fun i _ => mul_nonneg (hb i).le (hnn i j)) (Finset.mem_univ j)
    linarith [hb j]
  have hsup : extendVec ((1 - A) *ᵥ α) (-(b ⬝ᵥ α)) ∈
      supply (leontiefSet A b) (extendVec pr 1) := by
    refine ⟨⟨α, hα, le_rfl⟩, ?_⟩
    rintro y' ⟨α', hα', hle⟩
    rw [← extendVec_inputsOf y'] at hle ⊢
    rw [hdot, hdot, hzero]
    have h1 : extendVec pr 1 ⬝ᵥ extendVec (-inputsOf y') (y' (Fin.last n)) ≤
        extendVec pr 1 ⬝ᵥ extendVec ((1 - A) *ᵥ α') (-(b ⬝ᵥ α')) :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hle i) (by
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp [extendVec]
        · simp only [extendVec, Fin.snoc_castSucc]; exact (hprpos j).le)
    rw [hdot, hdot, hzero] at h1
    linarith
  refine ⟨hsup, proposition_5_F_1 (fun i => ?_) hsup⟩
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [extendVec]
  · simp only [extendVec, Fin.snoc_castSucc]; exact hprpos j

open Matrix in
/-- **Exercise 5.AA.2(b)** (MWG, p. 164). If `α ≫ 0` and `[I - A; -b]α` maximizes profits at the
prices `(p, 1)` (primary factor price normalized to `1`), then `p = b(I - A)⁻¹`: the supporting
prices are unique. -/
theorem exercise_5_AA_2b {A : Matrix (Fin n) (Fin n) ℝ} (hA : ∀ i j, 0 ≤ A i j)
    (hprod : Productive A) {b α p : Fin n → ℝ} (hα : StrictlyPositive α)
    (hsup : extendVec ((1 - A) *ᵥ α) (-(b ⬝ᵥ α)) ∈ supply (leontiefSet A b) (extendVec p 1)) :
    p = b ᵥ* (1 - A)⁻¹ := by
  obtain ⟨-, hr, -, -⟩ := leontief_inverse_facts hA hprod
  have hdot : ∀ (u : Fin n → ℝ) (t : ℝ), extendVec p 1 ⬝ᵥ extendVec u t = p ⬝ᵥ u + t := by
    intro u t
    simp [extendVec, dotProduct, Fin.sum_univ_castSucc]
  -- profits `p(I - A)α' - bα'` are maximized at the interior point `α`
  have hcoef : ∀ j, (p ᵥ* (1 - A)) j = b j := by
    intro j
    have hprof : ∀ t : ℝ, -α j < t →
        (p ᵥ* (1 - A) - b) ⬝ᵥ (α + t • Pi.single j 1) ≤ (p ᵥ* (1 - A) - b) ⬝ᵥ α := by
      intro t ht
      have hmem : extendVec ((1 - A) *ᵥ (α + t • Pi.single j 1))
          (-(b ⬝ᵥ (α + t • Pi.single j 1))) ∈ leontiefSet A b := by
        refine ⟨α + t • Pi.single j 1, fun i => ?_, le_rfl⟩
        by_cases hij : i = j
        · subst hij; simp; linarith
        · simp [hij, (hα i).le]
      have := hsup.2 _ hmem
      rw [hdot, hdot, Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec] at this
      simp only [sub_dotProduct]
      linarith
    have h1 := hprof 1 (by linarith [hα j])
    have h2 := hprof (-(α j / 2)) (by linarith [hα j])
    simp only [dotProduct_add, dotProduct_smul, dotProduct_single, mul_one, smul_eq_mul,
      Pi.sub_apply] at h1 h2
    have := hα j
    nlinarith
  have hpv : p ᵥ* (1 - A) = b := funext hcoef
  rw [← hpv, Matrix.vecMul_vecMul, hr, Matrix.vecMul_one]

open Matrix in
/-- **Exercise 5.AA.2(c)** (MWG, p. 164). The prices `p = b(I - A)⁻¹ = Σ_k bAᵏ` are the amounts of
primary factor used directly (`b`) and indirectly (`bA + bA² + ⋯`) per unit of each good. -/
theorem exercise_5_AA_2c {A : Matrix (Fin n) (Fin n) ℝ} (hA : ∀ i j, 0 ≤ A i j)
    (hprod : Productive A) (b : Fin n → ℝ) :
    HasSum (fun k : ℕ => b ᵥ* (A ^ k)) (b ᵥ* (1 - A)⁻¹) := by
  obtain ⟨hsum, -, hinv, -, -⟩ := proposition_5_AA_1_neumann hA hprod
  rw [hinv]
  let g : Matrix (Fin n) (Fin n) ℝ →+ (Fin n → ℝ) :=
    { toFun := fun M => b ᵥ* M, map_zero' := Matrix.vecMul_zero b,
      map_add' := fun M N => Matrix.vecMul_add M N b }
  exact hsum.hasSum.map g (continuous_const.matrix_vecMul continuous_id)

open Matrix in
/-- **Exercise 5.AA.2(d)** (MWG, p. 164). Let `p` (with wage `1`) support the whole technology, so
every activity of another productive selection `(A', b')` earns at most zero profit,
`p(I - A') ≤ b'`. Then `p ≤ b'(I - A')⁻¹` componentwise: the prices of the technique selected by
the nonsubstitution theorem (`p = b(I - A)⁻¹`) are minimal. -/
theorem exercise_5_AA_2d {A' : Matrix (Fin n) (Fin n) ℝ} (hA' : ∀ i j, 0 ≤ A' i j)
    (hprod' : Productive A') {b' p : Fin n → ℝ} (hle : p ᵥ* (1 - A') ≤ b') :
    p ≤ b' ᵥ* (1 - A')⁻¹ := by
  obtain ⟨-, hr, hnn, -⟩ := leontief_inverse_facts hA' hprod'
  intro j
  have : p = (p ᵥ* (1 - A')) ᵥ* (1 - A')⁻¹ := by
    rw [Matrix.vecMul_vecMul, hr, Matrix.vecMul_one]
  rw [this]
  simp only [Matrix.vecMul, dotProduct]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hle i) (hnn i j)

/-! ### Exercise 5.AA.3 -/

/-- **Exercise 5.AA.3(a)-(c)** (MWG, p. 165). For `A = [[0, 1], [1/2, 0]]` (`a_{ℓk}` the amount
of good `ℓ` per unit of good `k`) and `b = (1, 2)`: (b) the zero-profit prices with wage `1`,
`p_k = Σ_ℓ p_ℓ a_{ℓk} + b_k`, are `p = (4, 6)`; (c) `4` is the labour embodied in one net unit of
good `1`; (a) with `10` units of labour, `c ≥ 0` is producible iff `4c₁ + 6c₂ ≤ 10`. -/
theorem exercise_5_AA_3 :
    let A : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1 / 2, 0]
    let b : Fin 2 → ℝ := ![1, 2]
    (∀ p : Fin 2 → ℝ, (p 0 = p 0 * A 0 0 + p 1 * A 1 0 + b 0 ∧
      p 1 = p 0 * A 0 1 + p 1 * A 1 1 + b 1) ↔ p = ![4, 6]) ∧
    b ⬝ᵥ ![2, 1] = 4 ∧ (1 - A).mulVec ![2, 1] = ![1, 0] ∧
    ∀ c : Fin 2 → ℝ, 0 ≤ c →
      ((∃ x : Fin 2 → ℝ, 0 ≤ x ∧ c ≤ (1 - A).mulVec x ∧ b ⬝ᵥ x ≤ 10) ↔ 4 * c 0 + 6 * c 1 ≤ 10) := by
  intro A b
  refine ⟨fun p => ?_, by simp [b, dotProduct]; norm_num, ?_, fun c hc => ?_⟩
  · simp only [A, b, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    constructor
    · rintro ⟨h0, h1⟩
      funext i; fin_cases i <;> simp <;> linarith
    · rintro rfl
      norm_num
  · funext i
    fin_cases i <;> norm_num [A, Matrix.mulVec, dotProduct]
  · constructor
    · rintro ⟨x, hx, hcx, hbx⟩
      have h0 := hcx 0
      have h1 := hcx 1
      have x0 : 0 ≤ x 0 := hx 0
      have x1 : 0 ≤ x 1 := hx 1
      simp [A, Matrix.mulVec, dotProduct] at h0 h1
      simp [b, dotProduct] at hbx
      linarith
    · intro h
      have c0 : 0 ≤ c 0 := hc 0
      have c1 : 0 ≤ c 1 := hc 1
      refine ⟨![2 * c 0 + 2 * c 1, c 0 + 2 * c 1], fun i => ?_, fun i => ?_, ?_⟩
      · fin_cases i <;> simp <;> linarith
      · fin_cases i <;> simp [A, Matrix.mulVec, dotProduct] <;> linarith
      · simp [b, dotProduct]; linarith

/-- **Exercise 5.AA.3(e)** (MWG, p. 165). With the second technique for good 2 (`a'₁₂ = 1/2`,
`b'₂ = β`), the zero-profit prices are `p₂ = (2 + 4β)/3` (against `p₂ = 6` with the original
technique); the techniques switch at `β = 4`, the new one being cheaper iff `β < 4`. -/
theorem exercise_5_AA_3e (β : ℝ) :
    (∀ p₁ p₂ : ℝ, (p₁ = p₂ / 2 + 1 ∧ p₂ = p₁ / 2 + β) ↔ (p₂ = (2 + 4 * β) / 3 ∧
      p₁ = (4 + 2 * β) / 3)) ∧ ((2 + 4 * β) / 3 < 6 ↔ β < 4) ∧ ((2 + 4 * β) / 3 = 6 ↔ β = 4) := by
  refine ⟨fun p₁ p₂ => ⟨fun ⟨h1, h2⟩ => ⟨by linarith, by linarith⟩,
    fun ⟨h1, h2⟩ => ⟨by linarith, by linarith⟩⟩, ⟨fun h => by linarith, fun h => by linarith⟩,
    ⟨fun h => by linarith, fun h => by subst h; norm_num⟩⟩

/-! ### Exercise 5.AA.4 -/

/-- The four activities of Exercise 5.AA.4. -/
def aa4 : Fin 4 → Fin 4 → ℝ := ![![1, -1, 0, 0], ![0, -1, 1, 0], ![0, 0, -1, 1], ![2, 0, 0, -1]]

theorem aa4_coords (lam : Fin 4 ⊕ Fin 4 → ℝ) :
    ∑ j, lam j • withDisposal aa4 j =
      ![lam (Sum.inl 0) + 2 * lam (Sum.inl 3) - lam (Sum.inr 0),
        -lam (Sum.inl 0) - lam (Sum.inl 1) - lam (Sum.inr 1),
        lam (Sum.inl 1) - lam (Sum.inl 2) - lam (Sum.inr 2),
        lam (Sum.inl 2) - lam (Sum.inl 3) - lam (Sum.inr 3)] := by
  rw [Fintype.sum_sum_type]
  funext i
  fin_cases i <;> simp [withDisposal, aa4, Fin.sum_univ_four] <;> ring

/-- **Exercise 5.AA.4(a)** (MWG, p. 165). With the disposal activities, `y₂ = 3a₁ + a₄`,
`y₃ = 3(a₂ + a₃ + a₄)` and `y₄ = 4(a₂ + a₃)` belong to `Y`, while `y₁ = (6, 0, 0, -2)` and
`y₅ = (0, -3, 4, 0)` do not. -/
theorem exercise_5_AA_4a :
    (![6, 0, 0, -2] : Fin 4 → ℝ) ∉ coneOf (withDisposal aa4) ∧
      (![5, -3, 0, -1] : Fin 4 → ℝ) ∈ coneOf (withDisposal aa4) ∧
      (![6, -3, 0, 0] : Fin 4 → ℝ) ∈ coneOf (withDisposal aa4) ∧
      (![0, -4, 0, 4] : Fin 4 → ℝ) ∈ coneOf (withDisposal aa4) ∧
      (![0, -3, 4, 0] : Fin 4 → ℝ) ∉ coneOf (withDisposal aa4) := by
  have hmem : ∀ (l : Fin 4 → ℝ), 0 ≤ l → ∑ j, (Sum.elim l 0 : Fin 4 ⊕ Fin 4 → ℝ) j •
      withDisposal aa4 j ∈ coneOf (withDisposal aa4) := fun l hl =>
    ⟨Sum.elim l 0, fun j => by rcases j with j | j; exacts [hl j, le_rfl], rfl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨lam, hlam, h⟩
    rw [aa4_coords] at h
    have h0 := congrFun h 0; have h1 := congrFun h 1
    have h2 := congrFun h 2; have h3 := congrFun h 3
    simp at h0 h1 h2 h3
    have := hlam (Sum.inl 0); have := hlam (Sum.inl 1); have := hlam (Sum.inl 2)
    have := hlam (Sum.inl 3); have := hlam (Sum.inr 0); have := hlam (Sum.inr 1)
    have := hlam (Sum.inr 2); have := hlam (Sum.inr 3)
    simp only [Pi.zero_apply] at *
    linarith
  · have := hmem ![3, 0, 0, 1] (fun i => by fin_cases i <;> simp)
    rw [aa4_coords] at this
    convert this using 1
    funext i; fin_cases i <;> norm_num
  · have := hmem ![0, 3, 3, 3] (fun i => by fin_cases i <;> simp)
    rw [aa4_coords] at this
    convert this using 1
    funext i; fin_cases i <;> norm_num
  · have := hmem ![0, 4, 4, 0] (fun i => by fin_cases i <;> simp)
    rw [aa4_coords] at this
    convert this using 1
    funext i; fin_cases i <;> simp
  · rintro ⟨lam, hlam, h⟩
    rw [aa4_coords] at h
    have h1 := congrFun h 1; have h2 := congrFun h 2
    simp at h1 h2
    have := hlam (Sum.inl 0); have := hlam (Sum.inl 1); have := hlam (Sum.inl 2)
    have := hlam (Sum.inr 1); have := hlam (Sum.inr 2)
    simp only [Pi.zero_apply] at *
    linarith

/-- **Exercise 5.AA.4(b)-(c)** (MWG, p. 165). `y = (0, -5, 5, 0) = 5a₂` is efficient: it maximizes
profits at `p = (1, 2, 2, 2) ≫ 0`. `a₁ = (1, -1, 0, 0)` is feasible but not efficient:
`a₂ + a₃ + a₄ = (2, -1, 0, 0) ≥ a₁`. -/
theorem exercise_5_AA_4bc :
    (![0, -5, 5, 0] : Fin 4 → ℝ) ∈ supply (coneOf (withDisposal aa4)) ![1, 2, 2, 2] ∧
      Efficient (coneOf (withDisposal aa4)) ![0, -5, 5, 0] ∧
      ¬ Efficient (coneOf (withDisposal aa4)) ![1, -1, 0, 0] := by
  have hpg : ∀ j, (![1, 2, 2, 2] : Fin 4 → ℝ) ⬝ᵥ withDisposal aa4 j ≤ 0 := by
    intro j
    rcases j with j | j <;> fin_cases j <;>
      simp [withDisposal, aa4, dotProduct, Fin.sum_univ_four, Pi.single_apply]
  have hsup : (![0, -5, 5, 0] : Fin 4 → ℝ) ∈ supply (coneOf (withDisposal aa4)) ![1, 2, 2, 2] := by
    rw [activity_supply_eq hpg]
    refine ⟨Sum.elim ![0, 5, 0, 0] 0, fun j => ?_, fun j hj => ?_, ?_⟩
    · rcases j with j | j <;> fin_cases j <;> simp
    · rcases j with j | j <;> fin_cases j <;>
        simp [withDisposal, aa4, dotProduct, Fin.sum_univ_four, Pi.single_apply] at hj ⊢
    · rw [aa4_coords]; funext i; fin_cases i <;> simp
  refine ⟨hsup, proposition_5_F_1 (fun i => by fin_cases i <;> simp) hsup, fun h => ?_⟩
  apply h.2 ⟨![2, -1, 0, 0], ⟨Sum.elim ![0, 1, 1, 1] 0, fun j => by
    rcases j with j | j <;> fin_cases j <;> simp, by rw [aa4_coords]; funext i; fin_cases i <;>
      simp⟩, fun i => by fin_cases i <;> simp, fun he => by
    have := congrFun he 0; simp at this⟩

end MWG.Production

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercise 5.AA.5 (MWG, pp. 165-166)

Eight elementary activities in `ℝ⁴`, `Y = {Σ_m α_m a_m : α ≥ 0}` (no disposal activities).

* (a) `Y` is a convex cone; (b) no free lunch, via `p = (2, 2, 2, 1)`; (c) no free disposal, and
  adding the disposal activities restores it (`freeDisposal_withDisposal`).
* (d) by direct comparison `a₄ ≤ a₂`, `a₅ ≤ 3a₁`, `a₆ ≤ a₇/2` are inefficient; correction: the
  comparison of `a₃` with `a₈` shows nothing, both are efficient (`exercise_5_AA_5d_correction`).
* (e) `a₁ ≤ (4/3)a₃ + (2/15)a₇` and `a₂ ≤ a₃ + (3/10)a₇`.
* (f) the efficient set is `cone(a₃, a₈) ∪ cone(a₇, a₈)` (`exercise_5_AA_5f`).
* (g)-(h) maximizing net output of good 3 with resources `(480, 300, 0, 0)` is a linear program
  with value `412.5`, attained at `75a₃ + 37.5a₈` (`exercise_5_AA_5gh`).
-/

namespace MWG.Production

open MWG.ClassicalDemand MWG.ConsumerChoice Filter Topology

/-- The eight activities of Exercise 5.AA.5. -/
def aa5 : Fin 8 → Fin 4 → ℝ :=
  ![![-3, -6, 4, 0], ![-7, -9, 3, 2], ![-1, -2, 3, -1], ![-8, -13, 3, 1],
    ![-11, -19, 12, 0], ![-4, -3, -2, 5], ![-8, -5, 0, 10], ![-2, -4, 5, 2]]

/-- Adding the disposal activities gives free disposal. -/
theorem freeDisposal_withDisposal {L M : ℕ} (a : Fin M → Fin L → ℝ) :
    FreeDisposal (coneOf (withDisposal a)) := by
  rintro _ ⟨lam, hlam, rfl⟩ y' hy'
  set d := ∑ j, lam j • withDisposal a j - y' with hd
  set E : Fin M ⊕ Fin L → ℝ := Sum.elim (0 : Fin M → ℝ) d with hE
  refine ⟨lam + E, add_nonneg hlam (fun j => ?_), ?_⟩
  · rcases j with j | j
    · exact le_rfl
    · exact sub_nonneg.mpr hy' j
  · have hEs : ∑ j, E j • withDisposal a j = -d := by
      rw [Fintype.sum_sum_type]
      funext i
      simp [hE, withDisposal, Finset.sum_apply, Pi.single_apply]
    have hsplit : ∑ j, (lam + E) j • withDisposal a j =
        ∑ j, lam j • withDisposal a j + ∑ j, E j • withDisposal a j := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by rw [Pi.add_apply, add_smul]
    rw [hsplit, hEs, hd]
    abel

theorem aa5_dot (p : Fin 4 → ℝ) (m : Fin 8) :
    p ⬝ᵥ aa5 m = p 0 * aa5 m 0 + p 1 * aa5 m 1 + p 2 * aa5 m 2 + p 3 * aa5 m 3 := by
  simp [dotProduct, Fin.sum_univ_four]

/-- **Exercise 5.AA.5(a)-(c)** (MWG, p. 166). `Y` is convex (a convex cone); it has no free lunch
(`p = (2, 2, 2, 1) ≫ 0` makes every activity unprofitable); it does not have free disposal
(`(-1, 0, 0, 0) ∉ Y`, since every activity uses good 2); with the four disposal activities added
it does. -/
theorem exercise_5_AA_5abc :
    Convex ℝ (coneOf aa5) ∧ NoFreeLunch (coneOf aa5) ∧ ¬ FreeDisposal (coneOf aa5) ∧
      FreeDisposal (coneOf (withDisposal aa5)) := by
  have hp : ∀ m, (![2, 2, 2, 1] : Fin 4 → ℝ) ⬝ᵥ aa5 m ≤ 0 := by
    intro m; rw [aa5_dot]; fin_cases m <;> simp [aa5] <;> norm_num
  refine ⟨convex_coneOf aa5, ?_, ?_, freeDisposal_withDisposal aa5⟩
  · rintro _ ⟨lam, hlam, rfl⟩ h0
    have hle : (![2, 2, 2, 1] : Fin 4 → ℝ) ⬝ᵥ ∑ m, lam m • aa5 m ≤ 0 := by
      rw [activity_profit]
      exact Finset.sum_nonpos fun m _ => mul_nonpos_of_nonneg_of_nonpos (hlam m) (hp m)
    set y := ∑ m, lam m • aa5 m
    have hy0 : 0 ≤ y 0 := h0 0
    have hy1 : 0 ≤ y 1 := h0 1
    have hy2 : 0 ≤ y 2 := h0 2
    have hy3 : 0 ≤ y 3 := h0 3
    simp [dotProduct, Fin.sum_univ_four] at hle
    have e0 : y 0 = 0 := by linarith
    have e1 : y 1 = 0 := by linarith
    have e2 : y 2 = 0 := by linarith
    have e3 : y 3 = 0 := by linarith
    funext i
    fin_cases i
    exacts [e0, e1, e2, e3]
  · intro h
    obtain ⟨lam, hlam, hy⟩ := h 0 (zero_mem_coneOf aa5) ![-1, 0, 0, 0]
      (fun i => by fin_cases i <;> simp)
    have h0 := congrFun hy 0
    have h1 := congrFun hy 1
    simp [Finset.sum_apply, Fin.sum_univ_eight, aa5] at h0 h1
    have := hlam 0; have := hlam 1; have := hlam 2; have := hlam 3
    have := hlam 4; have := hlam 5; have := hlam 6; have := hlam 7
    simp only [Pi.zero_apply] at *
    linarith

/-- **Exercise 5.AA.5(d)** (MWG, p. 166). By direct comparison `a₄ ≤ a₂`, `a₅ ≤ 3a₁` and
`a₆ ≤ (1/2)a₇` (with strict inequalities somewhere), so `a₄`, `a₅`, `a₆` are not efficient. -/
theorem exercise_5_AA_5d :
    ¬ Efficient (coneOf aa5) (aa5 3) ∧ ¬ Efficient (coneOf aa5) (aa5 4) ∧
      ¬ Efficient (coneOf aa5) (aa5 5) := by
  have hg : ∀ m, aa5 m ∈ coneOf aa5 := generator_mem_coneOf aa5
  refine ⟨fun h => h.2 ⟨aa5 1, hg 1, fun i => ?_, fun he => ?_⟩,
    fun h => h.2 ⟨(3 : ℝ) • aa5 0, smul_mem_coneOf (hg 0) (by norm_num), fun i => ?_, fun he => ?_⟩,
    fun h => h.2 ⟨(1 / 2 : ℝ) • aa5 6, smul_mem_coneOf (hg 6) (by norm_num), fun i => ?_,
      fun he => ?_⟩⟩
  all_goals first
    | (fin_cases i <;> simp [aa5] <;> norm_num)
    | (have := congrFun he 1; norm_num [aa5] at this)

/-- **Exercise 5.AA.5(d)**, correction (MWG, p. 166): the "direct comparison of `a₃` with `a₈`"
proves nothing; both are efficient, being profit maximizing at `p = (30, 30, 31, 3) ≫ 0` and
`p = (2, 2, 2, 1) ≫ 0` respectively. -/
theorem exercise_5_AA_5d_correction :
    Efficient (coneOf aa5) (aa5 2) ∧ Efficient (coneOf aa5) (aa5 7) := by
  constructor
  · have hp : ∀ m, (![30, 30, 31, 3] : Fin 4 → ℝ) ⬝ᵥ aa5 m ≤ 0 := by
      intro m; rw [aa5_dot]; fin_cases m <;> simp [aa5] <;> norm_num
    refine proposition_5_F_1 (p := ![30, 30, 31, 3]) (fun i => by fin_cases i <;> simp) ?_
    rw [activity_supply_eq hp]
    refine ⟨Pi.single 2 1, Pi.single_nonneg.mpr zero_le_one, fun m hm => ?_, ?_⟩
    · by_contra h
      have : m = 2 := by by_contra hm2; simp [hm2] at h
      subst this; rw [aa5_dot] at hm; simp [aa5] at hm; norm_num at hm
    · rw [Finset.sum_eq_single 2 (fun j _ hj => by simp [hj]) (by simp)]; simp
  · have hp : ∀ m, (![2, 2, 2, 1] : Fin 4 → ℝ) ⬝ᵥ aa5 m ≤ 0 := by
      intro m; rw [aa5_dot]; fin_cases m <;> simp [aa5] <;> norm_num
    refine proposition_5_F_1 (p := ![2, 2, 2, 1]) (fun i => by fin_cases i <;> simp) ?_
    rw [activity_supply_eq hp]
    refine ⟨Pi.single 7 1, Pi.single_nonneg.mpr zero_le_one, fun m hm => ?_, ?_⟩
    · by_contra h
      have : m = 7 := by by_contra hm2; simp [hm2] at h
      subst this; rw [aa5_dot] at hm; simp [aa5] at hm; norm_num at hm
    · rw [Finset.sum_eq_single 7 (fun j _ hj => by simp [hj]) (by simp)]; simp

/-- **Exercise 5.AA.5(e)** (MWG, p. 166). `a₁ ≤ (4/3)a₃ + (2/15)a₇` and `a₂ ≤ a₃ + (3/10)a₇`, with
strict inequality somewhere: `a₁` and `a₂` are not efficient. -/
theorem exercise_5_AA_5e :
    ¬ Efficient (coneOf aa5) (aa5 0) ∧ ¬ Efficient (coneOf aa5) (aa5 1) := by
  have hg : ∀ m, aa5 m ∈ coneOf aa5 := generator_mem_coneOf aa5
  constructor
  · intro h
    apply h.2 ⟨(4 / 3 : ℝ) • aa5 2 + (2 / 15 : ℝ) • aa5 6,
      add_mem_coneOf (smul_mem_coneOf (hg 2) (by norm_num)) (smul_mem_coneOf (hg 6) (by norm_num)),
      fun i => ?_, fun he => ?_⟩
    · fin_cases i <;> simp [aa5] <;> norm_num
    · have := congrFun he 0; simp [aa5] at this; norm_num at this
  · intro h
    apply h.2 ⟨aa5 2 + (3 / 10 : ℝ) • aa5 6,
      add_mem_coneOf (hg 2) (smul_mem_coneOf (hg 6) (by norm_num)), fun i => ?_, fun he => ?_⟩
    · fin_cases i <;> simp [aa5] <;> norm_num
    · have := congrFun he 0; simp [aa5] at this; norm_num at this

theorem aa5_mem_supply_of_price {p y : Fin 4 → ℝ} (hp : ∀ m, p ⬝ᵥ aa5 m ≤ 0)
    (hy : y ∈ coneOf aa5) (hpy : p ⬝ᵥ y = 0) : y ∈ supply (coneOf aa5) p := by
  refine ⟨hy, ?_⟩
  rintro _ ⟨lam, hlam, rfl⟩
  rw [activity_profit, hpy]
  exact Finset.sum_nonpos fun m _ => mul_nonpos_of_nonneg_of_nonpos (hlam m) (hp m)

theorem aa5_two_mem {i j : Fin 8} {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    s • aa5 i + t • aa5 j ∈ coneOf aa5 :=
  add_mem_coneOf (smul_mem_coneOf (generator_mem_coneOf aa5 i) hs)
    (smul_mem_coneOf (generator_mem_coneOf aa5 j) ht)

/-- **Exercise 5.AA.5(f)** (MWG, p. 166). The efficient production vectors are exactly the
nonnegative combinations of `a₃` and `a₈` or of `a₇` and `a₈`:
`cone(a₃, a₈) ∪ cone(a₇, a₈)`. -/
theorem exercise_5_AA_5f (y : Fin 4 → ℝ) :
    Efficient (coneOf aa5) y ↔
      (∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ y = s • aa5 2 + t • aa5 7) ∨
        (∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ y = s • aa5 6 + t • aa5 7) := by
  constructor
  · intro hy
    obtain ⟨p, hp, hsup⟩ := linear_activity_efficient_pos_price aa5 hy
    have hpa := (activity_supply_nonempty_iff aa5 p).mp ⟨y, hsup⟩
    obtain ⟨lam, hlam, hz, rfl⟩ := (activity_supply_eq hpa y).mp hsup
    have p0 := hp 0; have p1 := hp 1; have p2 := hp 2; have p3 := hp 3
    have hd : ∀ m, p ⬝ᵥ aa5 m = p 0 * aa5 m 0 + p 1 * aa5 m 1 + p 2 * aa5 m 2 + p 3 * aa5 m 3 :=
      aa5_dot p
    have q : ∀ m, p ⬝ᵥ aa5 m ≤ 0 := hpa
    have e : ∀ m, m ≠ 2 → m ≠ 6 → m ≠ 7 → lam m = 0 := by
      intro m h2 h6 h7
      apply hz m
      have q0 := q 0; have q1 := q 1; have q2 := q 2; have q6 := q 6
      rw [hd] at q0 q1 q2 q6 ⊢
      fin_cases m <;> simp [aa5] at h2 h6 h7 q0 q1 q2 q6 ⊢ <;> linarith
    have hnot : ¬ (p ⬝ᵥ aa5 2 = 0 ∧ p ⬝ᵥ aa5 6 = 0) := by
      rintro ⟨h2, h6⟩
      have q7 := q 7
      rw [hd] at h2 h6 q7
      simp [aa5] at h2 h6 q7
      linarith
    have hsum : ∑ m, lam m • aa5 m = lam 2 • aa5 2 + lam 6 • aa5 6 + lam 7 • aa5 7 := by
      rw [Fin.sum_univ_eight, e 0 (by decide) (by decide) (by decide),
        e 1 (by decide) (by decide) (by decide), e 3 (by decide) (by decide) (by decide),
        e 4 (by decide) (by decide) (by decide), e 5 (by decide) (by decide) (by decide)]
      simp only [zero_smul, zero_add, add_zero]
    rw [hsum]
    by_cases h2 : p ⬝ᵥ aa5 2 = 0
    · have h6 : lam 6 = 0 := hz 6 fun h => hnot ⟨h2, h⟩
      exact Or.inl ⟨lam 2, lam 7, hlam 2, hlam 7, by rw [h6, zero_smul, add_zero]⟩
    · have h2' : lam 2 = 0 := hz 2 h2
      exact Or.inr ⟨lam 6, lam 7, hlam 6, hlam 7, by rw [h2', zero_smul, zero_add]⟩
  · rintro (⟨s, t, hs, ht, rfl⟩ | ⟨s, t, hs, ht, rfl⟩)
    · have hp : ∀ m, (![1, 5, 4, 1] : Fin 4 → ℝ) ⬝ᵥ aa5 m ≤ 0 := by
        intro m; rw [aa5_dot]; fin_cases m <;> simp [aa5] <;> norm_num
      refine proposition_5_F_1 (p := ![1, 5, 4, 1]) (fun i => by fin_cases i <;> simp)
        (aa5_mem_supply_of_price hp (aa5_two_mem hs ht) ?_)
      rw [dotProduct_add, dotProduct_smul, dotProduct_smul, aa5_dot, aa5_dot]
      simp [aa5]; norm_num
    · have hp : ∀ m, (![25, 60, 38, 50] : Fin 4 → ℝ) ⬝ᵥ aa5 m ≤ 0 := by
        intro m; rw [aa5_dot]; fin_cases m <;> simp [aa5] <;> norm_num
      refine proposition_5_F_1 (p := ![25, 60, 38, 50]) (fun i => by fin_cases i <;> simp)
        (aa5_mem_supply_of_price hp (aa5_two_mem hs ht) ?_)
      rw [dotProduct_add, dotProduct_smul, dotProduct_smul, aa5_dot, aa5_dot]
      simp [aa5]; norm_num

open Matrix in
/-- **Exercise 5.AA.5(g)-(h)** (MWG, p. 166). With resources `s = (480, 300, 0, 0)`, maximizing the
net production of good 3 is the linear program `max Σ_m α_m a_{3m}` s.t. `-Σ_m α_m a_{ℓm} ≤ s_ℓ`,
`α ≥ 0`. Its value is `412.5`, attained by `75a₃ + 37.5a₈`; the dual solution
`λ = (0, 11/8, 0, 1/4)` (shadow prices of the resources) certifies optimality. -/
theorem exercise_5_AA_5gh :
    let B : Matrix (Fin 4) (Fin 8) ℝ := fun l m => -aa5 m l
    let f : Fin 8 → ℝ := fun m => aa5 m 2
    let s : Fin 4 → ℝ := ![480, 300, 0, 0]
    let α : Fin 8 → ℝ := ![0, 0, 75, 0, 0, 0, 0, 75 / 2]
    α ∈ primalFeasible B s ∧ f ⬝ᵥ α = 825 / 2 ∧
      ![0, 11 / 8, 0, 1 / 4] ∈ dualFeasible B f ∧ s ⬝ᵥ ![0, 11 / 8, 0, 1 / 4] = 825 / 2 ∧
      ∀ α' ∈ primalFeasible B s, f ⬝ᵥ α' ≤ f ⬝ᵥ α := by
  intro B f s α
  have hα : α ∈ primalFeasible B s := by
    refine ⟨fun m => by fin_cases m <;> norm_num [α], fun l => ?_⟩
    fin_cases l <;> simp [B, s, α, aa5, Matrix.mulVec, dotProduct, Fin.sum_univ_eight] <;>
      norm_num
  have hval : f ⬝ᵥ α = 825 / 2 := by
    simp [f, α, aa5, dotProduct, Fin.sum_univ_eight]; norm_num
  have hlam : (![0, 11 / 8, 0, 1 / 4] : Fin 4 → ℝ) ∈ dualFeasible B f := by
    refine ⟨fun l => by fin_cases l <;> norm_num, fun m => ?_⟩
    have hcomp : (Bᵀ *ᵥ (![0, 11 / 8, 0, 1 / 4] : Fin 4 → ℝ)) m =
        -(11 / 8) * aa5 m 1 - (1 / 4) * aa5 m 3 := by
      have hT : ∀ i j, Bᵀ i j = -aa5 i j := fun i j => rfl
      simp only [Matrix.mulVec, dotProduct, hT, Fin.sum_univ_four]
      simp
      ring
    rw [hcomp]
    fin_cases m <;> simp [f, aa5] <;> norm_num
  have hdual : s ⬝ᵥ ![0, 11 / 8, 0, 1 / 4] = 825 / 2 := by
    simp [s, dotProduct, Fin.sum_univ_four]; norm_num
  refine ⟨hα, hval, hlam, hdual, fun α' hα' => ?_⟩
  rw [hval, ← hdual]
  exact equation_M_M_3 hα' hlam

end MWG.Production

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercises 5.D.4, 5.D.5 and 5.E.5 (MWG, pp. 163-164)

* **Exercise 5.D.4(a)**: with one output, decreasing average cost implies subadditivity.
* **Exercise 5.D.5(b)-(c)**: with a representative consumer `u(q) - z`, an interior optimum has
  `u'(q̄) = 1/f'(z̄)` (marginal utility equals marginal cost), and this condition is not
  sufficient under increasing returns.
* **Exercise 5.E.5** (Weitzman): with `AC_j(q_j) = α + β_j q_j`, (a) if all `β_j > 0` output is
  allocated in proportion to `1/β_j`; (b) if all `β_j < 0` it is concentrated in the plant with
  the most negative `β_j`; (c) in general a cost-minimizing allocation uses at most one plant with
  `β_j < 0`.
-/

namespace MWG.Production

open MWG.ClassicalDemand MWG.ConsumerChoice Filter Topology

/-- **Exercise 5.D.4(a)** (MWG, p. 163). With one output, if average cost `C(q)/q` is nonincreasing
on `q > 0` and `C(0) ≥ 0`, then `C` is subadditive: splitting `q = Σ_j q_j` among `J` firms never
lowers total cost. -/
theorem exercise_5_D_4a {J : ℕ} (hJ : 0 < J) {C : ℝ → ℝ} (h0 : 0 ≤ C 0)
    (hdec : ∀ q q', 0 < q → q ≤ q' → C q' / q' ≤ C q / q) (qs : Fin J → ℝ) (hqs : 0 ≤ qs) :
    C (∑ j, qs j) ≤ ∑ j, C (qs j) := by
  set Q := ∑ j, qs j with hQ
  rcases (Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => hqs j).lt_or_eq with hpos | hzero
  · have hQ0 : 0 < Q := hpos
    have hle : ∀ j, C Q / Q * qs j ≤ C (qs j) := by
      intro j
      rcases (hqs j).lt_or_eq with hj | hj
      · have hjQ : qs j ≤ Q := Finset.single_le_sum (fun i _ => hqs i) (Finset.mem_univ j)
        have := hdec (qs j) Q hj hjQ
        rw [div_le_div_iff₀ hQ0 hj] at this
        rw [div_mul_eq_mul_div, div_le_iff₀ hQ0]
        linarith
      · have hj' : qs j = 0 := hj.symm
        rw [hj', mul_zero]; exact h0
    calc C Q = C Q / Q * Q := by rw [div_mul_cancel₀ _ hQ0.ne']
      _ = ∑ j, C Q / Q * qs j := by rw [hQ, Finset.mul_sum]
      _ ≤ ∑ j, C (qs j) := Finset.sum_le_sum fun j _ => hle j
  · have hall : ∀ j, qs j = 0 := fun j =>
      (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hqs i).mp hzero.symm j (Finset.mem_univ j)
    have hQz : Q = 0 := hzero.symm
    rw [hQz]
    have : ∑ j, C (qs j) = J * C 0 := by simp [hall]
    rw [this]
    have : (1 : ℝ) ≤ J := by exact_mod_cast hJ
    nlinarith

/-- **Exercise 5.D.5(b)** (MWG, p. 163). With a representative consumer `u(q) - z` and
`q = f(z)`, an interior maximizer `z̄` of `u(f(z)) - z` satisfies `u'(f(z̄)) f'(z̄) = 1`: marginal
utility equals marginal cost `1/f'(z̄)` (the inverse function `C = f⁻¹` has `C'(q̄) = 1/f'(z̄)`). -/
theorem exercise_5_D_5b {u f : ℝ → ℝ} {z mu mf : ℝ} (hu : HasDerivAt u mu (f z))
    (hf : HasDerivAt f mf z) (hmax : IsLocalMax (fun t => u (f t) - t) z) :
    mu * mf = 1 ∧ (mf ≠ 0 → mu = 1 / mf) := by
  have hd : HasDerivAt (fun t => u (f t) - t) (mu * mf - 1) z :=
    (hu.comp z hf).sub (hasDerivAt_id z)
  have h := hmax.hasDerivAt_eq_zero hd
  refine ⟨by linarith, fun hne => ?_⟩
  field_simp
  linarith

/-- **Exercise 5.D.5(c)** (MWG, p. 163). "MU = MC is sufficient" is wrong under increasing returns:
for `f(z) = z²` and `u(q) = q/2`, at `z̄ = 1` marginal utility `1/2` equals marginal cost
`(√q)' = 1/2`, but `u(f(z)) - z = z²/2 - z` is larger at `z = 4` (it is unbounded). -/
theorem exercise_5_D_5c :
    HasDerivAt (fun q : ℝ => q / 2) (1 / 2) 1 ∧ HasDerivAt Real.sqrt (1 / 2) 1 ∧
      (fun z : ℝ => z ^ 2 / 2 - z) 1 < (fun z : ℝ => z ^ 2 / 2 - z) 4 := by
  refine ⟨?_, ?_, by norm_num⟩
  · simpa using (hasDerivAt_id (1 : ℝ)).div_const 2
  · have := Real.hasDerivAt_sqrt (x := 1) one_ne_zero
    simpa using this

/-- **Exercise 5.E.5(a)** (MWG, p. 164). With `C_j(q_j) = αq_j + β_jq_j²` and all `β_j > 0`, the
allocation `q_j = (q/β_j)/Σ_k(1/β_k)` (equal marginal costs) minimizes total cost among all
allocations of `q` with `q_j ≥ 0`. -/
theorem exercise_5_E_5a {J : ℕ} {α q : ℝ} {β : Fin J → ℝ} (hβ : ∀ j, 0 < β j)
    (hJ : 0 < J) (qs : Fin J → ℝ) (hsum : ∑ j, qs j = q) :
    let B := ∑ k, 1 / β k
    ∑ j, (α * (q / β j / B) + β j * (q / β j / B) ^ 2) ≤ ∑ j, (α * qs j + β j * qs j ^ 2) := by
  intro B
  have hB : 0 < B := Finset.sum_pos (fun k _ => by have := hβ k; positivity)
    ⟨⟨0, hJ⟩, Finset.mem_univ _⟩
  -- tangent inequality with the common marginal cost `μ = α + 2q/B`
  have key : ∀ j, α * (q / β j / B) + β j * (q / β j / B) ^ 2 + (α + 2 * q / B) *
      (qs j - q / β j / B) ≤ α * qs j + β j * qs j ^ 2 := by
    intro j
    have hb := hβ j
    have hsq : β j * (qs j - q / β j / B) ^ 2 ≥ 0 := by positivity
    have e : β j * (q / β j / B) = q / B := by field_simp
    have e2 : 2 * q / B = 2 * (β j * (q / β j / B)) := by rw [e]; ring
    have : α * (q / β j / B) + β j * (q / β j / B) ^ 2 + (α + 2 * q / B) * (qs j - q / β j / B) =
        α * qs j + β j * qs j ^ 2 - β j * (qs j - q / β j / B) ^ 2 := by rw [e2]; ring
    linarith
  have hsum2 : ∑ j, (qs j - q / β j / B) = 0 := by
    rw [Finset.sum_sub_distrib, hsum]
    have : ∑ j, q / β j / B = q / B * B := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [this, div_mul_cancel₀ _ hB.ne', sub_self]
  calc ∑ j, (α * (q / β j / B) + β j * (q / β j / B) ^ 2)
      = ∑ j, (α * (q / β j / B) + β j * (q / β j / B) ^ 2 + (α + 2 * q / B) *
          (qs j - q / β j / B)) := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hsum2, mul_zero, add_zero]
    _ ≤ _ := Finset.sum_le_sum fun j _ => key j

/-- **Exercise 5.E.5(b)** (MWG, p. 164). With all `β_j < 0` (concave costs), producing all of
`q ≥ 0` in a plant `j*` with the most negative `β_{j*}` minimizes total cost. -/
theorem exercise_5_E_5b {J : ℕ} {α q : ℝ} {β : Fin J → ℝ} (hβ : ∀ j, β j < 0) {js : Fin J}
    (hmin : ∀ j, β js ≤ β j) (qs : Fin J → ℝ) (hqs : 0 ≤ qs) (hsum : ∑ j, qs j = q) :
    α * q + β js * q ^ 2 ≤ ∑ j, (α * qs j + β j * qs j ^ 2) := by
  have h1 : ∑ j, β js * qs j ^ 2 ≤ ∑ j, β j * qs j ^ 2 :=
    Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hmin j) (sq_nonneg _)
  have h2 : ∑ j, qs j ^ 2 ≤ q ^ 2 := by
    rw [← hsum, sq, Finset.sum_mul]
    exact Finset.sum_le_sum fun j _ => by
      rw [sq]
      exact mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun i _ => hqs i)
        (Finset.mem_univ j)) (hqs j)
  have h3 : β js * q ^ 2 ≤ β js * ∑ j, qs j ^ 2 :=
    mul_le_mul_of_nonpos_left h2 (hβ js).le
  rw [← Finset.mul_sum] at h1
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsum]
  linarith

/-- **Exercise 5.E.5(c)** (MWG, p. 164). In general, a cost-minimizing allocation never uses two
plants with `β_i, β_k < 0`: moving both outputs to the plant with the smaller `β` strictly lowers
cost. -/
theorem exercise_5_E_5c {α βi βk qi qk : ℝ} (hi : βi < 0) (hle : βi ≤ βk)
    (hqi : 0 < qi) (hqk : 0 < qk) :
    α * (qi + qk) + βi * (qi + qk) ^ 2 < (α * qi + βi * qi ^ 2) + (α * qk + βk * qk ^ 2) := by
  have : βi * qk ^ 2 ≤ βk * qk ^ 2 := mul_le_mul_of_nonneg_right hle (sq_nonneg _)
  nlinarith [mul_pos hqi hqk]

end MWG.Production

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Proposition 5.C.1(vii) without convexity (MWG, p. 138)

`Profit` proves Proposition 5.C.1(vii) for closed convex `Y` (via Hotelling's lemma, which
needs convexity, correction 4). Here the symmetry of `Dy(p̄)` is proved for an arbitrary
production set `Y`, under the book's hypothesis that `y(·)` is a function (indeed any selection
from the supply correspondence near `p̄`) differentiable at `p̄`.

The proof does not go through `π`. A selection `y(·)` from the supply correspondence is
*cyclically monotone*: around any closed cycle of prices `p⁰, …, p^N = p⁰`,
`Σ (p^{i+1} - p^i)·y(p^i) ≤ 0` (`supply_cyclic`). Rescaling a cycle around `p̄` and letting the
scale tend to zero, the derivative `D = Dy(p̄)` inherits cyclic monotonicity
(`deriv_cyclic`). Along a long thin rectangle (`n` steps along `a`, one step along `b`) this
gives `b·Da - a·Db ≤ a·Da/n + b·Db`, and rescaling `a`, `b` and letting `n → ∞` gives
`b·Da = a·Db` (`cyclic_symm`).

`Dy(p̄) = D²π(p̄)` also holds: Hotelling's lemma holds at every price where the selection is
continuous (`hotelling_of_continuousAt`, no convexity), so `∇π(p̄) = y(p̄)`; when `y(·)` is
continuous near `p̄` the Hessian of `π` at `p̄` is `Dy(p̄)` (`proposition_5_C_1_vii_general`).
-/

namespace MWG.Production

open MWG.ClassicalDemand MWG.ConsumerChoice Filter Topology

variable {L : ℕ}

/-- A selection from the supply correspondence is cyclically monotone: for prices
`P 0, …, P N` with `P N = P 0`, `Σ_{i<N} (P(i+1) - P i)·y(P i) ≤ 0`. -/
theorem supply_cyclic {Y : Set (Fin L → ℝ)} {ys : (Fin L → ℝ) → (Fin L → ℝ)} {N : ℕ}
    (P : ℕ → Fin L → ℝ) (hP : ∀ i ≤ N, ys (P i) ∈ supply Y (P i)) (hcyc : P N = P 0) :
    ∑ i ∈ Finset.range N, (P (i + 1) - P i) ⬝ᵥ ys (P i) ≤ 0 := by
  have key : ∀ i < N, (P (i + 1) - P i) ⬝ᵥ ys (P i) ≤
      P (i + 1) ⬝ᵥ ys (P (i + 1)) - P i ⬝ᵥ ys (P i) := by
    intro i hi
    have := (hP (i + 1) hi).2 _ (hP i hi.le).1
    rw [sub_dotProduct]
    linarith
  calc _ ≤ ∑ i ∈ Finset.range N, (P (i + 1) ⬝ᵥ ys (P (i + 1)) - P i ⬝ᵥ ys (P i)) :=
        Finset.sum_le_sum fun i hi => key i (Finset.mem_range.mp hi)
    _ = P N ⬝ᵥ ys (P N) - P 0 ⬝ᵥ ys (P 0) :=
        Finset.sum_range_sub (fun i => P i ⬝ᵥ ys (P i)) N
    _ = 0 := by rw [hcyc, sub_self]

/-- The derivative of a supply selection at `p̄` is cyclically monotone: for any cycle
`Q 0, …, Q N = Q 0`, `Σ_{i<N} (Q(i+1) - Q i)·D(Q i) ≤ 0`. -/
theorem deriv_cyclic {Y : Set (Fin L → ℝ)} {ys : (Fin L → ℝ) → (Fin L → ℝ)} {p : Fin L → ℝ}
    (hys : ∀ᶠ q in 𝓝 p, ys q ∈ supply Y q) {D : (Fin L → ℝ) →L[ℝ] (Fin L → ℝ)}
    (hD : HasFDerivAt ys D p) (N : ℕ) (Q : ℕ → Fin L → ℝ) (hcyc : Q N = Q 0) :
    ∑ i ∈ Finset.range N, (Q (i + 1) - Q i) ⬝ᵥ D (Q i) ≤ 0 := by
  have hline : ∀ v : Fin L → ℝ, HasDerivAt (fun t : ℝ => p + t • v) v 0 := by
    intro v
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add p
    simp only [id, one_smul] at h
    exact h
  have hlim : ∀ i, Tendsto (fun t : ℝ => t⁻¹ • (ys (p + t • Q i) - ys p)) (𝓝[>] 0)
      (𝓝 (D (Q i))) := by
    intro i
    have hD' := hD
    rw [← show p + (0 : ℝ) • Q i = p by simp] at hD'
    have hc := (hD'.comp_hasDerivAt (0 : ℝ) (hline (Q i))).tendsto_slope_zero_right
    simpa only [zero_add, zero_smul, add_zero, Function.comp_def] using hc
  have hsum : Tendsto (fun t : ℝ => ∑ i ∈ Finset.range N,
      (Q (i + 1) - Q i) ⬝ᵥ (t⁻¹ • (ys (p + t • Q i) - ys p))) (𝓝[>] 0)
      (𝓝 (∑ i ∈ Finset.range N, (Q (i + 1) - Q i) ⬝ᵥ D (Q i))) :=
    tendsto_finsetSum _ fun i _ =>
      ((continuous_const.dotProduct continuous_id).tendsto _).comp (hlim i)
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i ∈ Finset.range (N + 1),
      ys (p + t • Q i) ∈ supply Y (p + t • Q i) := by
    rw [Finset.eventually_all]
    intro i _
    have hc : Tendsto (fun t : ℝ => p + t • Q i) (𝓝[>] 0) (𝓝 p) := by
      have := (hline (Q i)).continuousAt.tendsto
      simp only [zero_smul, add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    exact hc.eventually hys
  refine le_of_tendsto hsum ?_
  filter_upwards [hev, self_mem_nhdsWithin] with t ht htpos
  have htpos' : (0 : ℝ) < t := htpos
  have hcyc' := supply_cyclic (Y := Y) (ys := ys) (N := N) (fun i => p + t • Q i)
    (fun i hi => ht i (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))) (by simp [hcyc])
  have hzero : ∑ i ∈ Finset.range N, (Q (i + 1) - Q i) ⬝ᵥ ys p = 0 := by
    simp only [sub_dotProduct]
    rw [Finset.sum_range_sub (fun i => Q i ⬝ᵥ ys p) N, hcyc, sub_self]
  have hterm : ∀ i ∈ Finset.range N, (Q (i + 1) - Q i) ⬝ᵥ (t⁻¹ • (ys (p + t • Q i) - ys p)) =
      t⁻¹ * t⁻¹ * ((p + t • Q (i + 1) - (p + t • Q i)) ⬝ᵥ ys (p + t • Q i)) -
        t⁻¹ * ((Q (i + 1) - Q i) ⬝ᵥ ys p) := by
    intro i _
    have e : p + t • Q (i + 1) - (p + t • Q i) = t • (Q (i + 1) - Q i) := by
      rw [smul_sub]; abel
    rw [e, dotProduct_smul, smul_dotProduct, dotProduct_sub, smul_eq_mul, smul_eq_mul]
    field_simp
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    hzero, mul_zero, sub_zero]
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hcyc'

/-- `Σ_{i<n} i = n(n-1)/2` in `ℝ`. -/
theorem sum_range_cast_id (n : ℕ) : ∑ i ∈ Finset.range n, (i : ℝ) = n * (n - 1) / 2 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- The thin-rectangle cycle: `n` steps from `0` to `a`, one step to `a + b`, `n` steps back to
`b`, one step back to `0`. -/
noncomputable def thinCycle (n : ℕ) (a b : Fin L → ℝ) (i : ℕ) : Fin L → ℝ :=
  if i ≤ n then ((i : ℝ) / n) • a
  else if i ≤ 2 * n + 1 then (1 - ((i : ℝ) - n - 1) / n) • a + b else 0

/-- Along the thin rectangle, a cyclically monotone linear map satisfies
`b·Da - a·Db ≤ a·Da/n + b·Db`. -/
theorem thinCycle_bound (D : (Fin L → ℝ) →L[ℝ] (Fin L → ℝ))
    (hD : ∀ (N : ℕ) (Q : ℕ → Fin L → ℝ), Q N = Q 0 →
      ∑ i ∈ Finset.range N, (Q (i + 1) - Q i) ⬝ᵥ D (Q i) ≤ 0)
    (a b : Fin L → ℝ) {n : ℕ} (hn : 1 ≤ n) :
    b ⬝ᵥ D a - a ⬝ᵥ D b ≤ a ⬝ᵥ D a / n + b ⬝ᵥ D b := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  set Q := thinCycle n a b with hQdef
  have hQ0 : Q 0 = 0 := by simp [hQdef, thinCycle]
  have hQN : Q (2 * n + 2) = 0 := by
    simp only [hQdef, thinCycle]
    simp only [show ¬ (2 * n + 2 ≤ n) by omega, show ¬ (2 * n + 2 ≤ 2 * n + 1) by omega,
      ↓reduceIte]
  have h := hD (2 * n + 2) Q (by rw [hQN, hQ0])
  set f := fun i => (Q (i + 1) - Q i) ⬝ᵥ D (Q i) with hf
  -- the four pieces of the cycle
  have h1 : ∀ i ∈ Finset.range n, f i = (i : ℝ) * (a ⬝ᵥ D a / (n * n)) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    simp only [hf, hQdef, thinCycle]
    simp only [show i + 1 ≤ n by omega, show i ≤ n by omega, ↓reduceIte]
    rw [← sub_smul, map_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    push_cast
    field_simp
    ring
  have h2 : f n = b ⬝ᵥ D a := by
    simp only [hf, hQdef, thinCycle]
    simp only [le_refl, show ¬ (n + 1 ≤ n) by omega, show n + 1 ≤ 2 * n + 1 by omega,
      ↓reduceIte]
    rw [div_self hn0, one_smul]
    push_cast
    simp
  have h3 : ∀ j ∈ Finset.range n, f (n + 1 + j) =
      -(1 / n) * ((1 - (j : ℝ) / n) * (a ⬝ᵥ D a) + a ⬝ᵥ D b) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    simp only [hf, hQdef, thinCycle]
    simp only [show ¬ (n + 1 + j + 1 ≤ n) by omega, show n + 1 + j + 1 ≤ 2 * n + 1 by omega,
      show ¬ (n + 1 + j ≤ n) by omega, show n + 1 + j ≤ 2 * n + 1 by omega, ↓reduceIte]
    have e : (1 - ((↑(n + 1 + j + 1) : ℝ) - n - 1) / n) • a + b -
        ((1 - ((↑(n + 1 + j) : ℝ) - n - 1) / n) • a + b) = (-(1 / n) : ℝ) • a := by
      rw [add_sub_add_right_eq_sub, ← sub_smul]
      congr 1
      push_cast
      field_simp
      ring
    rw [e, map_add, map_smul, smul_dotProduct, dotProduct_add, dotProduct_smul, smul_eq_mul,
      smul_eq_mul]
    have e2 : (1 - ((↑(n + 1 + j) : ℝ) - n - 1) / n) = 1 - (j : ℝ) / n := by
      push_cast; ring
    rw [e2]
  have h4 : f (2 * n + 1) = -(b ⬝ᵥ D b) := by
    simp only [hf, hQdef, thinCycle]
    simp only [show ¬ (2 * n + 1 + 1 ≤ n) by omega, show ¬ (2 * n + 1 + 1 ≤ 2 * n + 1) by omega,
      show ¬ (2 * n + 1 ≤ n) by omega, le_refl, ↓reduceIte]
    have e2 : (1 - ((↑(2 * n + 1) : ℝ) - n - 1) / n) = 0 := by
      push_cast
      field_simp
      ring
    rw [e2, zero_smul, zero_add, zero_sub, neg_dotProduct]
  have hsplit : ∑ i ∈ Finset.range (2 * n + 2), f i =
      (∑ i ∈ Finset.range n, f i) + f n + (∑ j ∈ Finset.range n, f (n + 1 + j)) +
        f (2 * n + 1) := by
    rw [show 2 * n + 2 = (n + 1 + n) + 1 by omega, Finset.sum_range_succ,
      Finset.sum_range_add, Finset.sum_range_succ]
    congr 2
    omega
  have hs1 : ∑ i ∈ Finset.range n, f i = (n * (n - 1) / 2) * (a ⬝ᵥ D a / (n * n)) := by
    rw [Finset.sum_congr rfl h1, ← Finset.sum_mul, sum_range_cast_id]
  have hs3 : ∑ j ∈ Finset.range n, f (n + 1 + j) =
      -(1 / n) * ((n - n * (n - 1) / (2 * n)) * (a ⬝ᵥ D a) + n * (a ⬝ᵥ D b)) := by
    rw [Finset.sum_congr rfl h3, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_mul,
      Finset.sum_sub_distrib, ← Finset.sum_div, sum_range_cast_id]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    field_simp
  have htot : ∑ i ∈ Finset.range (2 * n + 2), f i =
      -(a ⬝ᵥ D a) / n + b ⬝ᵥ D a - a ⬝ᵥ D b - b ⬝ᵥ D b := by
    rw [hsplit, hs1, h2, hs3, h4]
    field_simp
    ring
  have h' : ∑ i ∈ Finset.range (2 * n + 2), f i ≤ 0 := h
  rw [htot] at h'
  have : a ⬝ᵥ D a / n = (a ⬝ᵥ D a) / n := rfl
  rw [neg_div] at h'
  linarith

/-- A cyclically monotone linear map is symmetric: `b·Da = a·Db`. -/
theorem cyclic_symm (D : (Fin L → ℝ) →L[ℝ] (Fin L → ℝ))
    (hD : ∀ (N : ℕ) (Q : ℕ → Fin L → ℝ), Q N = Q 0 →
      ∑ i ∈ Finset.range N, (Q (i + 1) - Q i) ⬝ᵥ D (Q i) ≤ 0)
    (a b : Fin L → ℝ) : b ⬝ᵥ D a = a ⬝ᵥ D b := by
  have half : ∀ a b : Fin L → ℝ, b ⬝ᵥ D a - a ⬝ᵥ D b ≤ 0 := by
    intro a b
    set X := b ⬝ᵥ D a - a ⬝ᵥ D b
    set A := a ⬝ᵥ D a
    set B := b ⬝ᵥ D b
    -- rescaled bound: `X ≤ s A / n + B / s` for `s > 0`, `n ≥ 1`
    have hres : ∀ s : ℝ, 0 < s → ∀ n : ℕ, 1 ≤ n → X ≤ s * A / n + B / s := by
      intro s hs n hn
      set μ := Real.sqrt s
      have hμ : 0 < μ := Real.sqrt_pos.mpr hs
      have hμ2 : μ * μ = s := Real.mul_self_sqrt hs.le
      have h := thinCycle_bound D hD (μ • a) (μ⁻¹ • b) hn
      simp only [map_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul] at h
      have e1 : μ * (μ⁻¹ * (b ⬝ᵥ D a)) = b ⬝ᵥ D a := by field_simp
      have e2 : μ⁻¹ * (μ * (a ⬝ᵥ D b)) = a ⬝ᵥ D b := by field_simp
      have e3 : μ * (μ * A) = s * A := by rw [← hμ2]; ring
      have e4 : μ⁻¹ * (μ⁻¹ * B) = B / s := by rw [← hμ2]; field_simp
      rw [e1, e2, e3, e4] at h
      exact h
    by_contra hX
    push Not at hX
    set s := 2 * (|B| + 1) / X with hs
    have hs0 : 0 < s := by positivity
    obtain ⟨n, hn⟩ := exists_nat_gt (2 * s * |A| / X + 1)
    have hn1 : 1 ≤ n := by
      have : (1 : ℝ) < n := by
        have : 0 ≤ 2 * s * |A| / X := by positivity
        linarith
      exact_mod_cast this.le
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have h := hres s hs0 n hn1
    have hB : B / s < X / 2 := by
      rw [div_lt_iff₀ hs0, hs]
      field_simp
      nlinarith [le_abs_self B, abs_nonneg B]
    have hA : s * A / n < X / 2 := by
      rw [div_lt_iff₀ hnpos]
      have h1 : s * A ≤ s * |A| := mul_le_mul_of_nonneg_left (le_abs_self A) hs0.le
      have h2 : 2 * s * |A| < X * n := by
        have h3 : 2 * s * |A| / X < n := by linarith
        rw [div_lt_iff₀ hX] at h3; linarith
      nlinarith
    linarith
  have h1 := half a b
  have h2 := half b a
  linarith

/-- **Proposition 5.C.1(vii)** (MWG, p. 138), symmetry, for an arbitrary production set `Y`: if
`y(·)` is a selection from the supply correspondence near `p̄` (in particular if `y(·)` is a
function) and is differentiable at `p̄`, then `Dy(p̄)` is symmetric. No closedness, free
disposal or convexity is needed. -/
theorem proposition_5_C_1_vii_symm {Y : Set (Fin L → ℝ)} {ys : (Fin L → ℝ) → (Fin L → ℝ)}
    {p : Fin L → ℝ} (hys : ∀ᶠ q in 𝓝 p, ys q ∈ supply Y q)
    {D : (Fin L → ℝ) →L[ℝ] (Fin L → ℝ)} (hD : HasFDerivAt ys D p) :
    ∀ i j, jacobian D i j = jacobian D j i := by
  intro i j
  have h := cyclic_symm D (deriv_cyclic hys hD) (Pi.single j 1) (Pi.single i 1)
  simpa [jacobian] using h

/-- `|h·v| ≤ L‖h‖‖v‖` for the sup norm. -/
theorem abs_dotProduct_le_norm (h v : Fin L → ℝ) : |h ⬝ᵥ v| ≤ L * (‖h‖ * ‖v‖) := by
  calc |h ⬝ᵥ v| ≤ ∑ l, |h l * v l| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _l : Fin L, ‖h‖ * ‖v‖ := Finset.sum_le_sum fun l _ => by
        rw [abs_mul]
        exact mul_le_mul (norm_le_pi_norm h l) (norm_le_pi_norm v l) (abs_nonneg _)
          (norm_nonneg _)
    _ = L * (‖h‖ * ‖v‖) := by simp

/-- **Hotelling's lemma** (Proposition 5.C.1(vi), MWG, p. 138) without convexity, at a price
where a supply selection is continuous: if `y(q) ∈ y(q)` for `q` near `p̄` and `y(·)` is
continuous at `p̄`, then `π` is differentiable at `p̄` with `∇π(p̄) = y(p̄)`. -/
theorem hotelling_of_continuousAt {Y : Set (Fin L → ℝ)} {ys : (Fin L → ℝ) → (Fin L → ℝ)}
    {p : Fin L → ℝ} (hys : ∀ᶠ q in 𝓝 p, ys q ∈ supply Y q) (hc : ContinuousAt ys p) :
    HasFDerivAt (profit Y) (dualityDotCLM (ys p)) p := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc0
  have hp := hys.self_of_nhds
  have hshift : Tendsto (fun h : Fin L → ℝ => p + h) (𝓝 0) (𝓝 p) := by
    have := (tendsto_const_nhds (x := p)).add (tendsto_id (x := 𝓝 (0 : Fin L → ℝ)))
    simpa using this
  have hcl : ∀ᶠ h in 𝓝 (0 : Fin L → ℝ), ‖ys (p + h) - ys p‖ ≤ c / (L + 1) := by
    have := (hc.tendsto.comp hshift)
    have hball := Metric.tendsto_nhds.mp this (c / (L + 1)) (by positivity)
    filter_upwards [hball] with h hh
    rw [dist_eq_norm] at hh
    exact hh.le
  filter_upwards [hshift.eventually hys, hcl] with h hh hcl'
  rw [profit_eq_of_mem_supply hh, profit_eq_of_mem_supply hp, dualityDotCLM_apply]
  have hup := hh.2 _ hp.1
  have hlow := hp.2 _ hh.1
  have hb := abs_dotProduct_le_norm h (ys (p + h) - ys p)
  rw [Real.norm_eq_abs, abs_le]
  have hL : (L : ℝ) * (‖h‖ * ‖ys (p + h) - ys p‖) ≤ c * ‖h‖ := by
    have h1 : ‖h‖ * ‖ys (p + h) - ys p‖ ≤ ‖h‖ * (c / (L + 1)) :=
      mul_le_mul_of_nonneg_left hcl' (norm_nonneg h)
    have h2 : (L : ℝ) * (‖h‖ * (c / (L + 1))) ≤ c * ‖h‖ := by
      rw [show (L : ℝ) * (‖h‖ * (c / (L + 1))) = (L / (L + 1)) * (c * ‖h‖) by ring]
      have : (L : ℝ) / (L + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith
      exact mul_le_of_le_one_left (by positivity) this
    calc _ ≤ (L : ℝ) * (‖h‖ * (c / (L + 1))) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ _ := h2
  rw [abs_le] at hb
  simp only [add_dotProduct, dotProduct_sub, dotProduct_comm (ys p) h] at hup hlow hb ⊢
  constructor <;> nlinarith [norm_nonneg h]

/-- If `Y` is closed and the supply correspondence is single-valued, `y(q) = {ys q}`, for `q`
near `p̄`, then `ys` is continuous near `p̄`. Proof: `π` is convex and finite near `p̄`, hence
locally Lipschitz (Mathlib), which bounds `ys` locally; a limit point of `ys(q_n)` along
`q_n → q` lies in `Y` (closed) and maximizes profit at `q`, so it is `ys q`. -/
theorem supply_continuousAt_of_single {Y : Set (Fin L → ℝ)} (hcl : IsClosed Y)
    {ys : (Fin L → ℝ) → (Fin L → ℝ)} {p : Fin L → ℝ}
    (hys : ∀ᶠ q in 𝓝 p, supply Y q = {ys q}) : ∀ᶠ q in 𝓝 p, ContinuousAt ys q := by
  obtain ⟨U, hU, hUo, hpU⟩ := eventually_nhds_iff.mp hys
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hUo p hpU
  set C := Metric.ball p r with hC
  have hmem : ∀ q ∈ C, ys q ∈ supply Y q := fun q hq => by rw [hU q (hball hq)]; rfl
  have hprof : ∀ q ∈ C, profit Y q = q ⬝ᵥ ys q := fun q hq => profit_eq_of_mem_supply (hmem q hq)
  have hconv : ConvexOn ℝ C (profit Y) := by
    refine ⟨convex_ball p r, fun x hx y hy a b ha hb hab => ?_⟩
    have hz : a • x + b • y ∈ C := convex_ball p r hx hy ha hb hab
    rw [hprof _ hz, hprof x hx, hprof y hy, add_dotProduct, smul_dotProduct, smul_dotProduct,
      smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
    have h1 := (hmem x hx).2 _ (hmem _ hz).1
    have h2 := (hmem y hy).2 _ (hmem _ hz).1
    nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]
  have hlip := hconv.locallyLipschitzOn Metric.isOpen_ball
  filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr)] with q hq
  -- local bound on `ys`
  obtain ⟨K, t, ht, hK⟩ := hlip hq
  rw [nhdsWithin_eq_nhds.mpr (Metric.isOpen_ball.mem_nhds hq)] at ht
  obtain ⟨δ, hδ, hδt⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem ht
    (Metric.isOpen_ball.mem_nhds hq))
  have hbound : ∀ q' ∈ Metric.ball q (δ / 2), ‖ys q'‖ ≤ K := by
    intro q' hq'
    have hq'C : q' ∈ C := (hδt (Metric.ball_subset_ball (by linarith) hq')).2
    refine (pi_norm_le_iff_of_nonneg K.coe_nonneg).mpr fun i => ?_
    have hdir : ∀ c : ℝ, |c| ≤ δ / 4 → c * ys q' i ≤ K * |c| := by
      intro c hc
      set h : Fin L → ℝ := Pi.single i c with hh
      have hnh : ‖h‖ = |c| := by rw [hh, Pi.norm_single, Real.norm_eq_abs]
      have hin : q' + h ∈ Metric.ball q δ := by
        rw [Metric.mem_ball, dist_eq_norm] at hq' ⊢
        calc ‖q' + h - q‖ ≤ ‖q' - q‖ + ‖h‖ := by
              rw [show q' + h - q = (q' - q) + h by abel]; exact norm_add_le _ _
          _ < δ := by rw [hnh]; linarith
      have hin' := hδt hin
      have hq'in := hδt (Metric.ball_subset_ball (by linarith) hq')
      have hle := (hmem _ hin'.2).2 _ (hmem q' hq'C).1
      have hl := hK.dist_le_mul _ hin'.1 _ hq'in.1
      rw [hprof _ hin'.2, hprof _ hq'C, Real.dist_eq, dist_eq_norm,
        show q' + h - q' = h by abel, hnh] at hl
      have : (q' + h) ⬝ᵥ ys q' = q' ⬝ᵥ ys q' + c * ys q' i := by
        rw [add_dotProduct, hh, single_dotProduct]
      rw [abs_le] at hl
      linarith [hl.2]
    have hpos := hdir (δ / 4) (by rw [abs_of_pos (by positivity)])
    have hneg := hdir (-(δ / 4)) (by rw [abs_neg, abs_of_pos (by positivity)])
    rw [abs_of_pos (by positivity)] at hpos
    rw [abs_neg, abs_of_pos (by positivity)] at hneg
    have hδ4 : 0 < δ / 4 := by positivity
    have u1 : ys q' i ≤ K := (mul_le_mul_iff_of_pos_left hδ4).mp (by linarith)
    have u2 : -ys q' i ≤ K := (mul_le_mul_iff_of_pos_left hδ4).mp (by linarith)
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  -- sequential continuity
  rw [ContinuousAt, tendsto_nhds_iff_seq_tendsto]
  intro u hu
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  set v := u ∘ ns with hv
  have hvt : Tendsto v atTop (𝓝 q) := hu.comp hns
  have hevC : ∀ᶠ n in atTop, v n ∈ Metric.ball q (δ / 2) ∧ v n ∈ C :=
    hvt.eventually_mem (Filter.inter_mem (Metric.ball_mem_nhds q (by linarith : (0 : ℝ) < δ / 2))
      (Metric.isOpen_ball.mem_nhds hq))
  have hfreq : ∃ᶠ n in atTop, ys (v n) ∈ Metric.closedBall (0 : Fin L → ℝ) K :=
    (hevC.mono fun n hn => by
      rw [mem_closedBall_zero_iff]; exact hbound _ hn.1).frequently
  obtain ⟨a, -, φ, hφ, hlim⟩ := tendsto_subseq_of_frequently_bounded
    Metric.isBounded_closedBall hfreq
  have hvφ : Tendsto (v ∘ φ) atTop (𝓝 q) := hvt.comp hφ.tendsto_atTop
  have hevφ : ∀ᶠ n in atTop, v (φ n) ∈ C := (hφ.tendsto_atTop.eventually hevC).mono
    fun n hn => hn.2
  have haY : a ∈ Y := hcl.mem_of_tendsto hlim (hevφ.mono fun n hn => (hmem _ hn).1)
  have hdotlim : ∀ (x : ℕ → Fin L → ℝ) (y : ℕ → Fin L → ℝ) (x₀ y₀ : Fin L → ℝ),
      Tendsto x atTop (𝓝 x₀) → Tendsto y atTop (𝓝 y₀) →
      Tendsto (fun n => x n ⬝ᵥ y n) atTop (𝓝 (x₀ ⬝ᵥ y₀)) := by
    intro x y x₀ y₀ hx hy
    exact ((continuous_fst.dotProduct continuous_snd).tendsto (x₀, y₀)).comp (hx.prodMk_nhds hy)
  have hsup : a ∈ supply Y q := by
    refine ⟨haY, fun y hy => ?_⟩
    refine le_of_tendsto_of_tendsto (hdotlim _ _ _ _ hvφ tendsto_const_nhds)
      (hdotlim _ _ _ _ hvφ hlim) ?_
    filter_upwards [hevφ] with n hn
    exact (hmem _ hn).2 y hy
  have hqU : supply Y q = {ys q} := hU q (hball hq)
  rw [hqU, Set.mem_singleton_iff] at hsup
  rw [← hsup]
  exact ⟨φ, hlim⟩

/-- **Proposition 5.C.1(vii)** (MWG, p. 138) for a closed, not necessarily convex, production set
`Y`: if `y(·)` is a function near `p̄` (`y(q) = {ys q}`) differentiable at `p̄`, then `∇π = ys`
near `p̄` (`ys` is continuous there, `supply_continuousAt_of_single`, and Hotelling's lemma holds,
`hotelling_of_continuousAt`), `D²π(p̄) = Dy(p̄)`, and this matrix is symmetric and positive
semidefinite with `Dy(p̄)p̄ = 0`. Free disposal is not needed; symmetry and semidefiniteness need
neither closedness nor single-valuedness (`proposition_5_C_1_vii_symm`,
`proposition_5_C_1_vii_psd`). -/
theorem proposition_5_C_1_vii_general {Y : Set (Fin L → ℝ)} (hcl : IsClosed Y)
    {ys : (Fin L → ℝ) → (Fin L → ℝ)} {p : Fin L → ℝ} (hys : ∀ᶠ q in 𝓝 p, supply Y q = {ys q})
    {D : (Fin L → ℝ) →L[ℝ] (Fin L → ℝ)} (hD : HasFDerivAt ys D p) :
    (∀ᶠ q in 𝓝 p, HasFDerivAt (profit Y) (dualityDotCLM (ys q)) q) ∧
      hessianMatrix (profit Y) p = jacobian D ∧
      (∀ i j, jacobian D i j = jacobian D j i) ∧ PosSemidefMWG (jacobian D) ∧ D p = 0 := by
  have hcont := supply_continuousAt_of_single hcl hys
  have hsel : ∀ᶠ q in 𝓝 p, ys q ∈ supply Y q := hys.mono fun q hq => by rw [hq]; rfl
  have hgrad : ∀ᶠ q in 𝓝 p, HasFDerivAt (profit Y) (dualityDotCLM (ys q)) q := by
    filter_upwards [hsel.eventually_nhds, hcont] with q hq hcq
    exact hotelling_of_continuousAt hq hcq
  refine ⟨hgrad, ?_, proposition_5_C_1_vii_symm hsel hD, proposition_5_C_1_vii_psd hsel hD,
    proposition_5_C_1_vii_euler hys hD⟩
  have heq : (fun q => gradientVec (fderiv ℝ (profit Y) q)) =ᶠ[𝓝 p] ys := by
    filter_upwards [hgrad] with q hq
    rw [hq.fderiv, gradientVec_dualityDotCLM]
  rw [hessianMatrix, (hD.congr_of_eventuallyEq heq).fderiv]

/-- A nonconvex production set: the decreasing-returns technology `{y₁ ≤ 0, y₂ ≤ √(-y₁)}`
together with the isolated plan `(-4, 5/2)`. -/
def ssY : Set (Fin 2 → ℝ) :=
  {y | y 0 ≤ 0 ∧ y 1 ≤ Real.sqrt (-y 0)} ∪ {![-4, 5 / 2]}

/-- The supply function `y(p) = (-(p₂/2p₁)², p₂/2p₁)` of `ssY` near `p̄ = (1, 1)`. -/
noncomputable def ssSupply (p : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![-(p 1 / (2 * p 0)) ^ 2, p 1 / (2 * p 0)]

/-- For `0 < q₂ < 2q₁`, `ssSupply q` maximizes profit on `ssY` at `q`. -/
theorem ssSupply_mem_supply {q : Fin 2 → ℝ} (h0 : 0 < q 0) (h1 : 0 < q 1) (h2 : q 1 < 2 * q 0) :
    ssSupply q ∈ supply ssY q := by
  have hdot : ∀ y : Fin 2 → ℝ, q ⬝ᵥ y = q 0 * y 0 + q 1 * y 1 := fun y => by
    simp [dotProduct, Fin.sum_univ_two]
  have hval : q ⬝ᵥ ssSupply q = q 1 ^ 2 / (4 * q 0) := by
    rw [hdot]
    simp only [ssSupply, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp
    ring
  refine ⟨Or.inl ⟨?_, ?_⟩, fun y hy => ?_⟩
  · simp only [ssSupply, Matrix.cons_val_zero]
    nlinarith [sq_nonneg (q 1 / (2 * q 0))]
  · simp only [ssSupply, Matrix.cons_val_zero, Matrix.cons_val_one, neg_neg]
    rw [Real.sqrt_sq (by positivity)]
  · rw [hval, hdot]
    rcases hy with ⟨hy0, hy1⟩ | hy
    · set x := Real.sqrt (-y 0) with hx
      have hx2 : x ^ 2 = -y 0 := Real.sq_sqrt (by linarith)
      have hx0 : 0 ≤ x := Real.sqrt_nonneg _
      rw [le_div_iff₀ (by positivity)]
      have h3 : q 1 * y 1 ≤ q 1 * x := mul_le_mul_of_nonneg_left hy1 h1.le
      have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 4 * q 0)
      have hy0' : y 0 = -x ^ 2 := by linarith
      rw [hy0']
      nlinarith [sq_nonneg (2 * q 0 * x - q 1)]
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [le_div_iff₀ (by positivity)]
      nlinarith [mul_pos (by linarith : (0 : ℝ) < 2 * q 0 - q 1)
        (by linarith : (0 : ℝ) < 8 * q 0 - q 1)]

/-- **Proposition 5.C.1(vii)** (MWG, p. 138): the hypotheses of `proposition_5_C_1_vii_symm`
hold for the nonconvex production set `ssY`: `ssY` is not convex, `y(p) = ssSupply p` is
profit maximizing for `p` near `(1, 1)` and is differentiable at `(1, 1)`; so `Dy(1, 1)` is
symmetric. -/
theorem proposition_5_C_1_vii_symm_instance :
    ¬ Convex ℝ ssY ∧ (∀ᶠ q in 𝓝 (![1, 1] : Fin 2 → ℝ), ssSupply q ∈ supply ssY q) ∧
      DifferentiableAt ℝ ssSupply ![1, 1] ∧
      ∀ i j, jacobian (fderiv ℝ ssSupply ![1, 1]) i j =
        jacobian (fderiv ℝ ssSupply ![1, 1]) j i := by
  have hsel : ∀ᶠ q in 𝓝 (![1, 1] : Fin 2 → ℝ), ssSupply q ∈ supply ssY q := by
    have hopen : IsOpen {q : Fin 2 → ℝ | 0 < q 0 ∧ 0 < q 1 ∧ q 1 < 2 * q 0} :=
      (isOpen_lt continuous_const (continuous_apply 0)).inter
        ((isOpen_lt continuous_const (continuous_apply 1)).inter
          (isOpen_lt (continuous_apply 1) (continuous_const.mul (continuous_apply 0))))
    filter_upwards [hopen.mem_nhds (by simp)] with q hq
    exact ssSupply_mem_supply hq.1 hq.2.1 hq.2.2
  have hdiff : DifferentiableAt ℝ ssSupply ![1, 1] := by
    rw [differentiableAt_pi]
    intro i
    fin_cases i
    · change DifferentiableAt ℝ (fun p : Fin 2 → ℝ => -(p 1 / (2 * p 0)) ^ 2) _
      fun_prop (disch := simp)
    · change DifferentiableAt ℝ (fun p : Fin 2 → ℝ => p 1 / (2 * p 0)) _
      fun_prop (disch := simp)
  refine ⟨fun hc => ?_, hsel, hdiff,
    proposition_5_C_1_vii_symm hsel hdiff.hasFDerivAt⟩
  have ha : (![-4, 5 / 2] : Fin 2 → ℝ) ∈ ssY := Or.inr rfl
  have hb : (![-25 / 4, 5 / 2] : Fin 2 → ℝ) ∈ ssY := by
    refine Or.inl ⟨by simp; norm_num, ?_⟩
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [show -(-25 / 4 : ℝ) = (5 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hmid := hc ha hb (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)
  rcases hmid with ⟨_, h⟩ | h
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
      Matrix.cons_val_one] at h
    have hlt : Real.sqrt (-(1 / 2 * -4 + 1 / 2 * (-25 / 4))) < 5 / 2 := by
      rw [Real.sqrt_lt' (by norm_num)]; norm_num
    linarith
  · have := congrFun (Set.mem_singleton_iff.mp h) 0
    simp at this
    norm_num at this

/-- For `0 < q₂ < 2q₁` the supply of `ssY` is single-valued: `y(q) = {ssSupply q}`. -/
theorem ss_supply_eq {q : Fin 2 → ℝ} (h0 : 0 < q 0) (h1 : 0 < q 1) (h2 : q 1 < 2 * q 0) :
    supply ssY q = {ssSupply q} := by
  have hm := ssSupply_mem_supply h0 h1 h2
  ext y
  refine ⟨fun hy => ?_, fun hy => by rw [Set.mem_singleton_iff.mp hy]; exact hm⟩
  have hge := hy.2 _ hm.1
  have hdot : ∀ y : Fin 2 → ℝ, q ⬝ᵥ y = q 0 * y 0 + q 1 * y 1 := fun y => by
    simp [dotProduct, Fin.sum_univ_two]
  have hval : q ⬝ᵥ ssSupply q = q 1 ^ 2 / (4 * q 0) := by
    rw [hdot]
    simp only [ssSupply, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp
    ring
  rw [hval, hdot, div_le_iff₀ (by positivity)] at hge
  rw [Set.mem_singleton_iff]
  rcases hy.1 with ⟨hy0, hy1⟩ | hpt
  · set x := Real.sqrt (-y 0) with hx
    have hx2 : x ^ 2 = -y 0 := Real.sq_sqrt (by linarith)
    have hx0 : 0 ≤ x := Real.sqrt_nonneg _
    have h3 : q 1 * y 1 ≤ q 1 * x := mul_le_mul_of_nonneg_left hy1 h1.le
    have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 4 * q 0)
    have hy0' : y 0 = -x ^ 2 := by linarith
    rw [hy0'] at hge
    have hA : (2 * q 0 * x - q 1) ^ 2 = 0 := by
      nlinarith [sq_nonneg (2 * q 0 * x - q 1)]
    have hxr : x = q 1 / (2 * q 0) := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hA
      field_simp
      linarith
    have hB : 4 * q 0 * (q 1 * y 1) = 4 * q 0 * (q 1 * x) := by
      nlinarith [sq_nonneg (2 * q 0 * x - q 1)]
    have hy1x : y 1 = x := by
      have h40 : (4 * q 0 * q 1) ≠ 0 := by positivity
      have : 4 * q 0 * q 1 * y 1 = 4 * q 0 * q 1 * x := by linarith
      exact mul_left_cancel₀ h40 this
    funext i
    fin_cases i
    · simp only [ssSupply, Fin.zero_eta, Matrix.cons_val_zero]
      rw [hy0', hxr]
    · simp only [ssSupply, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [hy1x, hxr]
  · rw [Set.mem_singleton_iff] at hpt
    subst hpt
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hge
    nlinarith [mul_pos (by linarith : (0 : ℝ) < 2 * q 0 - q 1)
      (by linarith : (0 : ℝ) < 8 * q 0 - q 1)]

/-- **Proposition 5.C.1(vii)** (MWG, p. 138): the hypotheses of `proposition_5_C_1_vii_general`
hold for the closed nonconvex production set `ssY` at `p̄ = (1, 1)`, so `D²π(1, 1) = Dy(1, 1)`,
symmetric. -/
theorem proposition_5_C_1_vii_general_instance :
    IsClosed ssY ∧ (∀ᶠ q in 𝓝 (![1, 1] : Fin 2 → ℝ), supply ssY q = {ssSupply q}) ∧
      hessianMatrix (profit ssY) ![1, 1] = jacobian (fderiv ℝ ssSupply ![1, 1]) ∧
      ∀ i j, jacobian (fderiv ℝ ssSupply ![1, 1]) i j =
        jacobian (fderiv ℝ ssSupply ![1, 1]) j i := by
  have hcl : IsClosed ssY := by
    refine IsClosed.union ?_ isClosed_singleton
    exact (isClosed_le (continuous_apply 0) continuous_const).inter
      (isClosed_le (continuous_apply 1) (Real.continuous_sqrt.comp (continuous_apply 0).neg))
  have hopen : IsOpen {q : Fin 2 → ℝ | 0 < q 0 ∧ 0 < q 1 ∧ q 1 < 2 * q 0} :=
    (isOpen_lt continuous_const (continuous_apply 0)).inter
      ((isOpen_lt continuous_const (continuous_apply 1)).inter
        (isOpen_lt (continuous_apply 1) (continuous_const.mul (continuous_apply 0))))
  have hys : ∀ᶠ q in 𝓝 (![1, 1] : Fin 2 → ℝ), supply ssY q = {ssSupply q} := by
    filter_upwards [hopen.mem_nhds (by simp)] with q hq
    exact ss_supply_eq hq.1 hq.2.1 hq.2.2
  have hdiff := proposition_5_C_1_vii_symm_instance.2.2.1
  have h := proposition_5_C_1_vii_general hcl hys hdiff.hasFDerivAt
  exact ⟨hcl, hys, h.2.1, h.2.2.1⟩

end MWG.Production

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercise 5.B.4: the closed case (MWG, p. 160)

`ExercisesB` shows that the additive closure `Y⁺` of the decreasing-returns technology of
Figure 5.B.5(a) is not closed. The reason is that arbitrarily small plants have positive output
at a high average product. In the technology of Figure 5.B.5(b) returns are increasing at small
scale, so two small plants can be merged into one without loss.

`exercise_5_B_4_closed` makes this precise for one input (good 1) and one output (good 2): let
`Y` be closed, use good 1 as an input (`y₁ ≤ 0`), have bounded output for bounded input, and
let two plans with input below some `δ > 0` be replaceable by their sum
(`y, y' ∈ Y`, `y₁, y'₁ > -δ` imply `y + y' ∈ Y`, increasing returns at small scale). Then `Y⁺`
is closed. The proof puts each element of `Y⁺` in a normal form with at most one plan using
less than `δ` of the input (`b4_normal_form`), so an element of `Y⁺` with input at most `B`
is a sum of at most `B/δ + 1` plans from a compact set, and `Y⁺` is locally a finite union of
compact sets.

`exercise_5_B_4_closed_instance`: the S-shaped technology `{y₁ ≤ 0, y₂ ≤ min(y₁², 1)}`
(increasing then decreasing returns, nonincreasing returns violated, as in Figure 5.B.5(b))
satisfies the hypotheses, so its additive closure is closed.
-/

namespace MWG.Production

open MWG.ClassicalDemand MWG.ConsumerChoice Filter Topology

/-- A finite sum `Σ_{i ≤ m} y_i` of elements of `Y` lies in `Y⁺`. -/
theorem b4_sum_mem_addClosure {L : ℕ} {Y : Set (Fin L → ℝ)} :
    ∀ (m : ℕ) (ys : Fin (m + 1) → Fin L → ℝ), (∀ i, ys i ∈ Y) → ∑ i, ys i ∈ addClosure Y := by
  have hc := exercise_5_B_4_closure Y
  intro m
  induction m with
  | zero => intro ys hys; simpa using hc.1 (hys 0)
  | succ m ih =>
    intro ys hys
    rw [Fin.sum_univ_succ]
    exact hc.2.1 _ (hc.1 (hys 0)) _ (ih (fun i => ys i.succ) fun i => hys _)

/-- Normal form: if two plans using less than `δ` of the input can be merged, every element of
`Y⁺` is a sum `Σ_{i ≤ m} y_i` of plans of `Y` in which all but `y₀` use at least `δ`. -/
theorem b4_normal_form {Y : Set (Fin 2 → ℝ)} {δ : ℝ}
    (hmerge : ∀ y ∈ Y, ∀ y' ∈ Y, -δ < y 0 → -δ < y' 0 → y + y' ∈ Y) {x : Fin 2 → ℝ}
    (hx : x ∈ addClosure Y) :
    ∃ (m : ℕ) (ys : Fin (m + 1) → Fin 2 → ℝ), (∀ i, ys i ∈ Y) ∧
      (∀ i : Fin m, ys i.succ 0 ≤ -δ) ∧ x = ∑ i, ys i := by
  obtain ⟨k, zs, hzs, rfl⟩ := hx
  induction k with
  | zero => exact ⟨0, fun _ => zs 0, fun _ => hzs 0 le_rfl, fun i => i.elim0, by simp⟩
  | succ k ih =>
    obtain ⟨m, ys, hys, hbig, hsum⟩ := ih fun i hi => hzs i (by omega)
    set y := zs (k + 1) with hy
    have hyY : y ∈ Y := hzs (k + 1) le_rfl
    rw [Finset.sum_range_succ, hsum]
    by_cases h1 : y 0 ≤ -δ
    · refine ⟨m + 1, Fin.cons (ys 0) (Fin.cons y (Fin.tail ys)), ?_, ?_, ?_⟩
      · intro i
        refine Fin.cases (hys 0) (fun j => ?_) i
        refine Fin.cases hyY (fun l => ?_) j
        exact hys l.succ
      · intro i
        refine Fin.cases h1 (fun l => ?_) i
        exact hbig l
      · simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.tail, hy]
        abel
    · push Not at h1
      by_cases h2 : ys 0 0 ≤ -δ
      · refine ⟨m + 1, Fin.cons y ys, ?_, ?_, ?_⟩
        · intro i
          refine Fin.cases hyY (fun l => ?_) i
          exact hys l
        · intro i
          refine Fin.cases h2 (fun l => ?_) i
          exact hbig l
        · simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, hy]
          abel
      · push Not at h2
        refine ⟨m, Fin.cons (ys 0 + y) (Fin.tail ys), ?_, ?_, ?_⟩
        · intro i
          refine Fin.cases (hmerge _ (hys 0) _ hyY h2 h1) (fun l => ?_) i
          exact hys l.succ
        · intro i
          exact hbig i
        · simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.tail, hy]
          abel

/-- **Exercise 5.B.4** (MWG, p. 160), the closed case of Figure 5.B.5(b). Let `Y ⊆ ℝ²` be closed,
with good 1 an input (`y₁ ≤ 0`), output bounded for bounded input, and increasing returns at
small scale: two plans each using less than `δ > 0` of the input can be merged
(`y + y' ∈ Y`). Then the additive closure `Y⁺` is closed. -/
theorem exercise_5_B_4_closed {Y : Set (Fin 2 → ℝ)} (hcl : IsClosed Y)
    (hin : ∀ y ∈ Y, y 0 ≤ 0) (hbdd : ∀ B : ℝ, ∃ U : ℝ, ∀ y ∈ Y, -B ≤ y 0 → y 1 ≤ U)
    {δ : ℝ} (hδ : 0 < δ) (hmerge : ∀ y ∈ Y, ∀ y' ∈ Y, -δ < y 0 → -δ < y' 0 → y + y' ∈ Y) :
    IsClosed (addClosure Y) := by
  -- closedness on each box `R_B = {x₁ ≥ -B, x₂ ≥ -B}`
  have hbox : ∀ B : ℝ, IsClosed (addClosure Y ∩ {x | -B ≤ x 0 ∧ -B ≤ x 1}) := by
    intro B
    obtain ⟨U, hU⟩ := hbdd B
    set U' := max U 0 with hU'
    set K : ℕ := ⌊B / δ⌋₊ with hK
    set lo : ℝ := -B - K * U' with hlo
    set box : Set (Fin 2 → ℝ) := Set.univ.pi fun l => Set.Icc (![-B, lo] l) (![0, U'] l)
      with hboxdef
    have hboxc : IsCompact box := isCompact_univ_pi fun l => isCompact_Icc
    have hboxmem : ∀ v : Fin 2 → ℝ, v ∈ box ↔ (-B ≤ v 0 ∧ v 0 ≤ 0) ∧ (lo ≤ v 1 ∧ v 1 ≤ U') := by
      intro v
      simp only [hboxdef, Set.mem_univ_pi, Set.mem_Icc, Fin.forall_fin_two]
      simp
    -- the compact sets of tuples
    set T : ℕ → Set (Fin 2 → ℝ) := fun m =>
      (fun ys : Fin (m + 1) → Fin 2 → ℝ => ∑ i, ys i) ''
        {ys | ∀ i, ys i ∈ Y ∧ ys i ∈ box} with hT
    have hTc : ∀ m, IsClosed (T m) := by
      intro m
      have hcpt : IsCompact {ys : Fin (m + 1) → Fin 2 → ℝ | ∀ i, ys i ∈ Y ∧ ys i ∈ box} := by
        refine (isCompact_univ_pi fun _ => hboxc).of_isClosed_subset ?_ ?_
        · have : {ys : Fin (m + 1) → Fin 2 → ℝ | ∀ i, ys i ∈ Y ∧ ys i ∈ box} =
              ⋂ i, (fun ys : Fin (m + 1) → Fin 2 → ℝ => ys i) ⁻¹' (Y ∩ box) := by
            ext ys; simp [Set.mem_iInter]
          rw [this]
          exact isClosed_iInter fun i => (hcl.inter hboxc.isClosed).preimage (continuous_apply i)
        · intro ys hys
          simp only [Set.mem_univ_pi]
          exact fun i => (hys i).2
      exact (hcpt.image (continuous_finsetSum _ fun i _ => continuous_apply i)).isClosed
    have hRc : IsClosed {x : Fin 2 → ℝ | -B ≤ x 0 ∧ -B ≤ x 1} :=
      (isClosed_le continuous_const (continuous_apply 0)).inter
        (isClosed_le continuous_const (continuous_apply 1))
    have heq : addClosure Y ∩ {x | -B ≤ x 0 ∧ -B ≤ x 1} =
        (⋃ m ∈ Finset.range (K + 1), T m) ∩ {x | -B ≤ x 0 ∧ -B ≤ x 1} := by
      ext x
      constructor
      · rintro ⟨hx, hxB⟩
        refine ⟨?_, hxB⟩
        obtain ⟨m, ys, hys, hbig, rfl⟩ := b4_normal_form hmerge hx
        have hsum0 : (∑ i, ys i) 0 = ∑ i, ys i 0 := Finset.sum_apply _ _ _
        have hsum1 : (∑ i, ys i) 1 = ∑ i, ys i 1 := Finset.sum_apply _ _ _
        have hneg : ∀ i, ys i 0 ≤ 0 := fun i => hin _ (hys i)
        -- each plan uses at most the total input
        have hge : ∀ i, (∑ j, ys j) 0 ≤ ys i 0 := by
          intro i
          rw [hsum0]
          calc ∑ j, ys j 0 ≤ ∑ j ∈ {i}, ys j 0 :=
                Finset.sum_le_sum_of_subset_of_nonpos (by simp) fun j _ _ => hneg j
            _ = ys i 0 := by simp
        have hm : (m : ℝ) * δ ≤ B := by
          have h1 : ∑ i : Fin m, ys i.succ 0 ≤ ∑ _i : Fin m, -δ :=
            Finset.sum_le_sum fun i _ => hbig i
          have h2 : (∑ j, ys j) 0 = ys 0 0 + ∑ i : Fin m, ys i.succ 0 := by
            rw [hsum0, Fin.sum_univ_succ]
          have h3 := hneg 0
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
          linarith [hxB.1]
        have hmK : m ≤ K := by
          rw [hK]
          apply Nat.le_floor
          rw [le_div_iff₀ hδ]
          exact hm
        have hmK' : (m : ℝ) ≤ K := by exact_mod_cast hmK
        have hup : ∀ i, ys i 1 ≤ U' := fun i =>
          (hU _ (hys i) (le_trans hxB.1 (hge i))).trans (le_max_left _ _)
        have hU0 : 0 ≤ U' := le_max_right _ _
        refine Set.mem_biUnion (x := m) (Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega))) ?_
        refine ⟨ys, fun i => ⟨hys i, (hboxmem _).mpr ⟨⟨le_trans hxB.1 (hge i), hneg i⟩,
          ?_, hup i⟩⟩, rfl⟩
        -- lower bound on the output of each plan
        have hrest : ∑ j ∈ Finset.univ.erase i, ys j 1 ≤ m * U' := by
          calc ∑ j ∈ Finset.univ.erase i, ys j 1 ≤ ∑ _j ∈ Finset.univ.erase i, U' :=
                Finset.sum_le_sum fun j _ => hup j
            _ = m * U' := by
                rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i)]
                simp
        have hsplit : ∑ j, ys j 1 = ys i 1 + ∑ j ∈ Finset.univ.erase i, ys j 1 :=
          (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
        have h1 := hxB.2
        rw [hsum1, hsplit] at h1
        have : (m : ℝ) * U' ≤ K * U' := mul_le_mul_of_nonneg_right hmK' hU0
        rw [hlo]
        linarith
      · rintro ⟨hx, hxB⟩
        refine ⟨?_, hxB⟩
        obtain ⟨m, -, hm⟩ := Set.mem_iUnion₂.mp hx
        obtain ⟨ys, hys, rfl⟩ := hm
        exact b4_sum_mem_addClosure m ys fun i => (hys i).1
    rw [heq]
    refine IsClosed.inter ?_ hRc
    exact isClosed_biUnion_finset fun m _ => hTc m
  -- closedness from the boxes
  refine isClosed_of_closure_subset fun x hx => ?_
  set B := max (-x 0) (-x 1) + 1 with hB
  set O : Set (Fin 2 → ℝ) := {v | -B < v 0 ∧ -B < v 1} with hO
  have hOo : IsOpen O :=
    (isOpen_lt continuous_const (continuous_apply 0)).inter
      (isOpen_lt continuous_const (continuous_apply 1))
  have hxO : x ∈ O := ⟨by rw [hB]; linarith [le_max_left (-x 0) (-x 1)],
    by rw [hB]; linarith [le_max_right (-x 0) (-x 1)]⟩
  have h1 := hOo.inter_closure ⟨hxO, hx⟩
  have h2 : closure (O ∩ addClosure Y) ⊆ addClosure Y ∩ {x | -B ≤ x 0 ∧ -B ≤ x 1} := by
    refine (hbox B).closure_subset_iff.mpr ?_
    rintro v ⟨hvO, hv⟩
    exact ⟨hv, hvO.1.le, hvO.2.le⟩
  exact (h2 h1).1

/-- The S-shaped technology `{y : y₁ ≤ 0, y₂ ≤ min(y₁², 1)}` of Figure 5.B.5(b). -/
def sTech : Set (Fin 2 → ℝ) := {y | y 0 ≤ 0 ∧ y 1 ≤ min (y 0 ^ 2) 1}

/-- **Exercise 5.B.4** (MWG, p. 160), Figure 5.B.5(b): the S-shaped technology
`{y₁ ≤ 0, y₂ ≤ min(y₁², 1)}` is closed, allows inaction, violates nonincreasing returns
(`(-1, 1) ∈ Y` but `(-1/2, 1/2) ∉ Y`), satisfies the hypotheses of `exercise_5_B_4_closed`
(with `δ = 1/2`), and its additive closure `Y⁺` is closed. -/
theorem exercise_5_B_4_closed_instance :
    IsClosed sTech ∧ InactionPossible sTech ∧ ¬ NonincreasingReturns sTech ∧
      (∀ y ∈ sTech, y 0 ≤ 0) ∧ (∀ B : ℝ, ∃ U : ℝ, ∀ y ∈ sTech, -B ≤ y 0 → y 1 ≤ U) ∧
      (∀ y ∈ sTech, ∀ y' ∈ sTech, -(1 / 2) < y 0 → -(1 / 2) < y' 0 → y + y' ∈ sTech) ∧
      IsClosed (addClosure sTech) := by
  have hcl : IsClosed sTech :=
    (isClosed_le (continuous_apply 0) continuous_const).inter
      (isClosed_le (continuous_apply 1) (((continuous_apply 0).pow 2).min continuous_const))
  have hin : ∀ y ∈ sTech, y 0 ≤ 0 := fun y hy => hy.1
  have hbdd : ∀ B : ℝ, ∃ U : ℝ, ∀ y ∈ sTech, -B ≤ y 0 → y 1 ≤ U :=
    fun _ => ⟨1, fun y hy _ => hy.2.trans (min_le_right _ _)⟩
  have hmerge : ∀ y ∈ sTech, ∀ y' ∈ sTech, -(1 / 2) < y 0 → -(1 / 2) < y' 0 →
      y + y' ∈ sTech := by
    intro y hy y' hy' h h'
    refine ⟨by simp only [Pi.add_apply]; linarith [hy.1, hy'.1], ?_⟩
    simp only [Pi.add_apply]
    have a := hy.2.trans (min_le_left _ _)
    have b := hy'.2.trans (min_le_left _ _)
    have hprod : 0 ≤ y 0 * y' 0 := mul_nonneg_of_nonpos_of_nonpos hy.1 hy'.1
    refine le_min (by nlinarith) ?_
    have : (y 0 + y' 0) ^ 2 < 1 := by nlinarith [hy.1, hy'.1]
    nlinarith
  refine ⟨hcl, ⟨le_rfl, by simp⟩, fun hnirs => ?_, hin, hbdd, hmerge,
    exercise_5_B_4_closed hcl hin hbdd (by norm_num) hmerge⟩
  have hmem : (![-1, 1] : Fin 2 → ℝ) ∈ sTech := ⟨by simp, by simp⟩
  have := hnirs _ hmem (1 / 2) (by norm_num) (by norm_num)
  have h2 := this.2
  simp at h2
  norm_num at h2

end MWG.Production

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercise 5.C.7: the explicit counterexample and the `n`-input correction (MWG, p. 161)

`ExercisesC` refutes Exercise 5.C.7 at the level of the first-order conditions. Here:

* **The counterexample realized.** For `f(z) = -e^{-z₁} - e^{-z₂} - e^{-z₁-z₂}` (increasing,
  strictly concave, `∂²f/∂z₁∂z₂ = -e^{-z₁-z₂} < 0`; `c7f_technology`) the profit-maximizing input
  demand has the closed form `z_ℓ(p, w) = -ln u_ℓ`, where, with `r = w/p` and `d = r₁ - r₂`,
  `u₁ = (d - 1 + √((1-d)² + 4r₁))/2` and `u₂ = u₁ - d` (`c7demand`). It is the unique
  maximizer of `p f(z) - w·z` for every `p > 0`, `w ≫ 0` (`exercise_5_C_7_demand`); at `p = 1`,
  `w = (3/4, 3/4)` it is `(ln 2, ln 2)` and `∂z₁/∂w₂ = 1/2 > 0`
  (`exercise_5_C_7_explicit_counterexample`), against the printed claim `∂z₁/∂w₂ < 0`.
* **The corrected statement for `n` inputs** (`exercise_5_C_7_corrected_n`): if `D²f(z)` is
  negative definite with all cross partials `∂²f/∂z_ℓ∂z_k > 0` (complementary inputs), then
  every input demand falls with every input price (`∂z_ℓ/∂w_k < 0`, all `ℓ, k`) and rises with
  the output price when `∇f ≥ 0`, `∇f ≠ 0`. The key fact (`negDef_offdiag_pos_solution_pos`) is
  that `-D²f` is a nonsingular M-matrix with a strictly positive inverse.
-/

namespace MWG.Production

open MWG.ClassicalDemand MWG.ConsumerChoice Filter Topology

/-! ### The `n`-input corrected statement -/

/-- If `H` is negative definite with positive off-diagonal entries and `p > 0`, the solution of
`pHx = -b` with `b ≥ 0`, `b ≠ 0` is strictly positive (`-pH` is a nonsingular M-matrix). -/
theorem negDef_offdiag_pos_solution_pos {n : ℕ} {H : Matrix (Fin n) (Fin n) ℝ}
    (hneg : NegDef H) (hoff : ∀ i j, i ≠ j → 0 < H i j) {p : ℝ} (hp : 0 < p)
    {x b : Fin n → ℝ} (hx : Matrix.mulVec (p • H) x = -b) (hb : 0 ≤ b) (hb0 : b ≠ 0) :
    ∀ i, 0 < x i := by
  have hrow : ∀ i, p * ∑ j, H i j * x j = -b i := by
    intro i
    have := congrFun hx i
    simpa [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc] using this
  have hrow' : ∀ i, ∑ j, H i j * x j ≤ 0 := by
    intro i
    have h := hrow i
    have := hb i
    by_contra hc
    push Not at hc
    have : 0 < p * ∑ j, H i j * x j := mul_pos hp hc
    simp only [Pi.zero_apply] at *
    linarith
  -- step 1: `x ≥ 0`
  set m : Fin n → ℝ := fun i => max (-x i) 0 with hm
  set xp : Fin n → ℝ := fun i => max (x i) 0 with hxp
  have hx_eq : ∀ j, x j = xp j - m j := by
    intro j
    simp only [hm, hxp]
    rcases le_total 0 (x j) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  have hm0 : ∀ j, 0 ≤ m j := fun j => le_max_right _ _
  have hxp0 : ∀ j, 0 ≤ xp j := fun j => le_max_right _ _
  have hmxp : ∀ j, m j * xp j = 0 := by
    intro j
    simp only [hm, hxp]
    rcases le_total 0 (x j) with h | h
    · rw [max_eq_right (by linarith)]; ring
    · rw [max_eq_right h]; ring
  have hcross : 0 ≤ ∑ i, m i * ∑ j, H i j * xp j := by
    refine Finset.sum_nonneg fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_nonneg fun j _ => ?_
    by_cases hij : i = j
    · subst hij
      rw [show m i * (H i i * xp i) = H i i * (m i * xp i) by ring, hmxp, mul_zero]
    · exact mul_nonneg (hm0 i) (mul_nonneg (hoff i j hij).le (hxp0 j))
  have hmx : ∑ i, m i * ∑ j, H i j * x j ≤ 0 :=
    Finset.sum_nonpos fun i _ => mul_nonpos_of_nonneg_of_nonpos (hm0 i) (hrow' i)
  have hsplit : ∑ i, m i * ∑ j, H i j * x j =
      ∑ i, m i * ∑ j, H i j * xp j - ∑ i, m i * ∑ j, H i j * m j := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hx_eq j]; ring
  have hmm : 0 ≤ m ⬝ᵥ H.mulVec m := by
    have : m ⬝ᵥ H.mulVec m = ∑ i, m i * ∑ j, H i j * m j := by
      simp [dotProduct, Matrix.mulVec]
    rw [this]
    linarith
  have hmz : m = 0 := by
    by_contra hne
    have := hneg m hne
    linarith
  have hxnn : ∀ j, 0 ≤ x j := by
    intro j
    have := congrFun hmz j
    simp only [hm, Pi.zero_apply] at this
    have h2 : -x j ≤ 0 := by rw [← this]; exact le_max_left _ _
    linarith
  -- step 2: strict positivity
  intro i
  rcases (hxnn i).lt_or_eq with h | h
  · exact h
  · exfalso
    have hterms : ∀ j ∈ Finset.univ, 0 ≤ H i j * x j := by
      intro j _
      by_cases hij : i = j
      · subst hij; rw [← h, mul_zero]
      · exact mul_nonneg (hoff i j hij).le (hxnn j)
    have hsum0 : ∑ j, H i j * x j = 0 :=
      le_antisymm (hrow' i) (Finset.sum_nonneg hterms)
    have hall := (Finset.sum_eq_zero_iff_of_nonneg hterms).mp hsum0
    have hx0 : x = 0 := by
      funext j
      by_cases hij : i = j
      · subst hij; exact h.symm
      · have := hall j (Finset.mem_univ j)
        rcases mul_eq_zero.mp this with h1 | h1
        · exact absurd h1 (hoff i j hij).ne'
        · exact h1
    apply hb0
    funext k
    have := hrow k
    simp only [hx0, Pi.zero_apply, mul_zero, Finset.sum_const_zero] at this
    simp only [Pi.zero_apply]
    linarith

/-- **Exercise 5.C.7** (MWG, p. 161), corrected, for `n` inputs. Let `H = D²f(z)` be negative
definite with all cross partials positive (`∂²f/∂z_ℓ∂z_k > 0`, complementary inputs) and
`p > 0`. Differentiating the first-order conditions `p∇f(z(p, w)) = w`, the derivative `v` of the
demands in `w_k` solves `pHv = e_k` and is strictly negative in every component
(`∂z_ℓ/∂w_k < 0` for all `ℓ`, `k`); the derivative in `p` solves `pHv = -∇f` and is strictly
positive when `∇f ≥ 0`, `∇f ≠ 0`. -/
theorem exercise_5_C_7_corrected_n {n : ℕ} {H : Matrix (Fin n) (Fin n) ℝ} (hneg : NegDef H)
    (hoff : ∀ i j, i ≠ j → 0 < H i j) {p : ℝ} (hp : 0 < p) :
    (∀ (k : Fin n) (v : Fin n → ℝ), Matrix.mulVec (p • H) v = Pi.single k 1 → ∀ l, v l < 0) ∧
      (∀ g v : Fin n → ℝ, 0 ≤ g → g ≠ 0 → Matrix.mulVec (p • H) v = -g → ∀ l, 0 < v l) := by
  refine ⟨fun k v hv l => ?_, fun g v hg hg0 hv l =>
    negDef_offdiag_pos_solution_pos hneg hoff hp hv hg hg0 l⟩
  have hv' : Matrix.mulVec (p • H) (-v) = -Pi.single k 1 := by
    rw [Matrix.mulVec_neg, hv]
  have hs : (0 : Fin n → ℝ) ≤ Pi.single k 1 := Pi.single_nonneg.mpr zero_le_one
  have hs0 : (Pi.single k 1 : Fin n → ℝ) ≠ 0 := by
    intro h
    have := congrFun h k
    simp at this
  have := negDef_offdiag_pos_solution_pos hneg hoff hp hv' hs hs0 l
  simp only [Pi.neg_apply] at this
  linarith

/-- The matrix `[[-3, 1, 1], [1, -3, 1], [1, 1, -3]]`, the Hessian of the concave quadratic
`f(z) = c·z - (3/2)Σz_ℓ² + Σ_{ℓ<k} z_ℓ z_k`. -/
def c7H3 : Matrix (Fin 3) (Fin 3) ℝ := !![-3, 1, 1; 1, -3, 1; 1, 1, -3]

/-- The matrix `c7H3` satisfies the hypotheses of `exercise_5_C_7_corrected_n`. -/
theorem exercise_5_C_7_corrected_n_instance :
    NegDef c7H3 ∧ ∀ i j : Fin 3, i ≠ j → 0 < c7H3 i j := by
  refine ⟨fun z hz => ?_, fun i j hij => ?_⟩
  · have hform : z ⬝ᵥ Matrix.mulVec c7H3 z =
        -(z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2) - ((z 0 - z 1) ^ 2 + (z 0 - z 2) ^ 2 + (z 1 - z 2) ^ 2) := by
      simp [c7H3, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      ring
    rw [hform]
    have : z 0 ≠ 0 ∨ z 1 ≠ 0 ∨ z 2 ≠ 0 := by
      by_contra h
      push Not at h
      exact hz (funext fun i => by fin_cases i <;> simp [h.1, h.2.1, h.2.2])
    rcases this with h | h | h
    · have := sq_pos_of_ne_zero h
      nlinarith [sq_nonneg (z 1), sq_nonneg (z 2), sq_nonneg (z 0 - z 1), sq_nonneg (z 0 - z 2),
        sq_nonneg (z 1 - z 2)]
    · have := sq_pos_of_ne_zero h
      nlinarith [sq_nonneg (z 0), sq_nonneg (z 2), sq_nonneg (z 0 - z 1), sq_nonneg (z 0 - z 2),
        sq_nonneg (z 1 - z 2)]
    · have := sq_pos_of_ne_zero h
      nlinarith [sq_nonneg (z 0), sq_nonneg (z 1), sq_nonneg (z 0 - z 1), sq_nonneg (z 0 - z 2),
        sq_nonneg (z 1 - z 2)]
  · fin_cases i <;> fin_cases j <;> simp_all [c7H3]

/-! ### The counterexample with an explicit demand function -/

/-- The technology `f(z) = -e^{-z₁} - e^{-z₂} - e^{-z₁-z₂}`. -/
noncomputable def c7f (z : Fin 2 → ℝ) : ℝ :=
  -(Real.exp (-z 0) + Real.exp (-z 1) + Real.exp (-z 0 - z 1))

/-- `u₁ = e^{-z₁}` at the optimum, as a function of the real input prices `r = w/p`. -/
noncomputable def c7u (r₀ r₁ : ℝ) : ℝ :=
  (r₀ - r₁ - 1 + Real.sqrt ((1 - r₀ + r₁) ^ 2 + 4 * r₀)) / 2

/-- `u₂ = e^{-z₂} = u₁ - (r₁ - r₂)` at the optimum. -/
noncomputable def c7v (r₀ r₁ : ℝ) : ℝ := c7u r₀ r₁ - (r₀ - r₁)

/-- The closed-form input demand `z(p, w) = (-ln u₁, -ln u₂)` for `f = c7f`. -/
noncomputable def c7demand (p : ℝ) (w : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![-Real.log (c7u (w 0 / p) (w 1 / p)), -Real.log (c7v (w 0 / p) (w 1 / p))]

/-- **Exercise 5.C.7** (MWG, p. 161): `c7f` meets the exercise's hypotheses. It is strictly
increasing in each input (`∂f/∂z₁ = e^{-z₁} + e^{-z₁-z₂} > 0`), strictly concave, and its cross
partial is `∂²f/∂z₂∂z₁ = -e^{-z₁-z₂} < 0`. -/
theorem c7f_technology (s t : ℝ) :
    HasDerivAt (fun x => c7f ![x, t]) (Real.exp (-s) + Real.exp (-s - t)) s ∧
      0 < Real.exp (-s) + Real.exp (-s - t) ∧
      HasDerivAt (fun y => Real.exp (-s) + Real.exp (-s - y)) (-Real.exp (-s - t)) t ∧
      -Real.exp (-s - t) < 0 ∧ StrictConcaveOn ℝ Set.univ c7f := by
  refine ⟨?_, by positivity, ?_, by simp [Real.exp_pos], ?_⟩
  · have h1 := ((hasDerivAt_id s).neg).exp
    have h2 := ((hasDerivAt_id s).neg.sub_const t).exp
    have h := ((h1.add_const (Real.exp (-t))).add h2).neg
    convert h using 1
    · funext x; simp [c7f]
    · simp; ring
  · have h := (((hasDerivAt_id t).const_sub (-s)).exp).const_add (Real.exp (-s))
    convert h using 1
    · funext y; simp [sub_eq_add_neg]
    · simp
  · refine ⟨convex_univ, fun x _ y _ hxy a b ha hb hab => ?_⟩
    have hcv : ∀ u v : ℝ, Real.exp (a * u + b * v) ≤ a * Real.exp u + b * Real.exp v :=
      fun u v => by
        simpa [smul_eq_mul] using convexOn_exp.2 (Set.mem_univ u) (Set.mem_univ v) ha.le hb.le hab
    have hst : ∀ u v : ℝ, u ≠ v → Real.exp (a * u + b * v) < a * Real.exp u + b * Real.exp v :=
      fun u v huv => by
        simpa [smul_eq_mul] using
          strictConvexOn_exp.2 (Set.mem_univ u) (Set.mem_univ v) huv ha hb hab
    have hc0 : (a • x + b • y) 0 = a * x 0 + b * y 0 := by simp
    have hc1 : (a • x + b • y) 1 = a * x 1 + b * y 1 := by simp
    change a * c7f x + b * c7f y < c7f (a • x + b • y)
    have e0 : -(a * x 0 + b * y 0) = a * -x 0 + b * -y 0 := by ring
    have e1 : -(a * x 1 + b * y 1) = a * -x 1 + b * -y 1 := by ring
    have e2 : -(a * x 0 + b * y 0) - (a * x 1 + b * y 1) =
        a * (-x 0 - x 1) + b * (-y 0 - y 1) := by ring
    have hmid : c7f (a • x + b • y) = -(Real.exp (a * -x 0 + b * -y 0) +
        Real.exp (a * -x 1 + b * -y 1) + Real.exp (a * (-x 0 - x 1) + b * (-y 0 - y 1))) := by
      unfold c7f; rw [hc0, hc1, e2, e0, e1]
    rw [hmid]
    unfold c7f
    have : x 0 ≠ y 0 ∨ x 1 ≠ y 1 := by
      by_contra h
      push Not at h
      exact hxy (funext fun i => by fin_cases i <;> simp [h.1, h.2])
    rcases this with h | h
    · have := hst (-x 0) (-y 0) (by intro e; exact h (by linarith))
      have := hcv (-x 1) (-y 1)
      have := hcv (-x 0 - x 1) (-y 0 - y 1)
      nlinarith
    · have := hcv (-x 0) (-y 0)
      have := hst (-x 1) (-y 1) (by intro e; exact h (by linarith))
      have := hcv (-x 0 - x 1) (-y 0 - y 1)
      nlinarith

/-- The optimality conditions solved by `c7u`, `c7v`: for `r ≫ 0`, `u₁, u₂ > 0`,
`u₁ + u₁u₂ = r₁` and `u₂ + u₁u₂ = r₂`. -/
theorem c7_foc {r₀ r₁ : ℝ} (h₀ : 0 < r₀) (h₁ : 0 < r₁) :
    0 < c7u r₀ r₁ ∧ 0 < c7v r₀ r₁ ∧ c7u r₀ r₁ + c7u r₀ r₁ * c7v r₀ r₁ = r₀ ∧
      c7v r₀ r₁ + c7u r₀ r₁ * c7v r₀ r₁ = r₁ := by
  set S := Real.sqrt ((1 - r₀ + r₁) ^ 2 + 4 * r₀) with hS
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hS2 : S ^ 2 = (1 - r₀ + r₁) ^ 2 + 4 * r₀ := Real.sq_sqrt (by positivity)
  have hu : c7u r₀ r₁ = (r₀ - r₁ - 1 + S) / 2 := rfl
  have hv : c7v r₀ r₁ = (r₀ - r₁ - 1 + S) / 2 - (r₀ - r₁) := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hu]
    have : 1 - r₀ + r₁ < S := by
      rcases lt_or_ge (1 - r₀ + r₁) 0 with h | h
      · linarith
      · rw [hS, Real.lt_sqrt h]; linarith
    linarith
  · rw [hv]
    have : 1 + r₀ - r₁ < S := by
      rcases lt_or_ge (1 + r₀ - r₁) 0 with h | h
      · linarith
      · rw [hS, Real.lt_sqrt h]; nlinarith
    linarith
  · rw [hu, hv]; linear_combination hS2 / 4
  · rw [hu, hv]; linear_combination hS2 / 4

/-- **Exercise 5.C.7** (MWG, p. 161), the counterexample realized: for `f = c7f`, every `p > 0`
and `w ≫ 0`, the closed-form `c7demand p w` is the unique maximizer of `p f(z) - w·z` over
`z ∈ ℝ²` (hence the profit-maximizing input demand). -/
theorem exercise_5_C_7_demand {p : ℝ} (hp : 0 < p) {w : Fin 2 → ℝ} (hw : StrictlyPositive w)
    (z : Fin 2 → ℝ) :
    p * c7f z - w ⬝ᵥ z ≤ p * c7f (c7demand p w) - w ⬝ᵥ c7demand p w ∧
      (z ≠ c7demand p w → p * c7f z - w ⬝ᵥ z < p * c7f (c7demand p w) - w ⬝ᵥ c7demand p w) := by
  obtain ⟨hu, hv, hf0, hf1⟩ := c7_foc (div_pos (hw 0) hp) (div_pos (hw 1) hp)
  set u := c7u (w 0 / p) (w 1 / p)
  set v := c7v (w 0 / p) (w 1 / p)
  set zs := c7demand p w with hzs
  have hz0 : zs 0 = -Real.log u := rfl
  have hz1 : zs 1 = -Real.log v := rfl
  have heu : Real.exp (-zs 0) = u := by rw [hz0, neg_neg, Real.exp_log hu]
  have hev : Real.exp (-zs 1) = v := by rw [hz1, neg_neg, Real.exp_log hv]
  have heuv : Real.exp (-zs 0 - zs 1) = u * v := by
    rw [sub_eq_add_neg, Real.exp_add, heu, hev]
  have hw0 : w 0 = p * (u + u * v) := by rw [hf0]; field_simp
  have hw1 : w 1 = p * (v + u * v) := by rw [hf1]; field_simp
  -- tangent inequalities `e^x ≥ e^{x₀}(1 + x - x₀)`
  have tang : ∀ x x₀ : ℝ, Real.exp x₀ * (1 + (x - x₀)) ≤ Real.exp x := by
    intro x x₀
    have := Real.add_one_le_exp (x - x₀)
    have e : Real.exp x = Real.exp x₀ * Real.exp (x - x₀) := by
      rw [← Real.exp_add]; ring_nf
    rw [e]
    nlinarith [Real.exp_pos x₀]
  have tang' : ∀ x x₀ : ℝ, x ≠ x₀ → Real.exp x₀ * (1 + (x - x₀)) < Real.exp x := by
    intro x x₀ hne
    have := Real.add_one_lt_exp (sub_ne_zero.mpr hne)
    have e : Real.exp x = Real.exp x₀ * Real.exp (x - x₀) := by
      rw [← Real.exp_add]; ring_nf
    rw [e]
    nlinarith [Real.exp_pos x₀]
  have t0 := tang (-z 0) (-zs 0)
  have t1 := tang (-z 1) (-zs 1)
  have t2 := tang (-z 0 - z 1) (-zs 0 - zs 1)
  rw [heu] at t0
  rw [hev] at t1
  rw [heuv] at t2
  have hdot : ∀ x : Fin 2 → ℝ, w ⬝ᵥ x = w 0 * x 0 + w 1 * x 1 := fun x => by
    simp [dotProduct, Fin.sum_univ_two]
  simp only [c7f, hdot, heu, hev, heuv]
  rw [hw0, hw1]
  refine ⟨by nlinarith, fun hne => ?_⟩
  have : z 0 ≠ zs 0 ∨ z 1 ≠ zs 1 := by
    by_contra h
    push Not at h
    exact hne (funext fun i => by fin_cases i <;> simp [h.1, h.2])
  rcases this with h | h
  · have s0 := tang' (-z 0) (-zs 0) (by intro e; exact h (by linarith))
    rw [heu] at s0
    nlinarith
  · have s1 := tang' (-z 1) (-zs 1) (by intro e; exact h (by linarith))
    rw [hev] at s1
    nlinarith

/-- **Exercise 5.C.7** (MWG, p. 161) is false, with an explicit demand function: for
`f = c7f` (increasing, strictly concave, `∂²f/∂z₁∂z₂ < 0`, `c7f_technology`), at `p = 1` and
`w = (3/4, 3/4)` the profit-maximizing demand is `(ln 2, ln 2)`, and
`∂z₁/∂w₂ = 1/2 > 0`, contradicting `∂z_ℓ/∂w_k < 0`. -/
theorem exercise_5_C_7_explicit_counterexample :
    c7demand 1 ![3 / 4, 3 / 4] = ![Real.log 2, Real.log 2] ∧
      HasDerivAt (fun t => c7demand 1 ![3 / 4, t] 0) (1 / 2) (3 / 4) ∧ (0 : ℝ) < 1 / 2 := by
  have hsq : Real.sqrt ((1 - 3 / 4 + 3 / 4 : ℝ) ^ 2 + 4 * (3 / 4)) = 2 := by
    rw [show ((1 - 3 / 4 + 3 / 4 : ℝ) ^ 2 + 4 * (3 / 4)) = 2 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have hu : c7u (3 / 4) (3 / 4) = 1 / 2 := by
    rw [c7u, hsq]; norm_num
  have hv : c7v (3 / 4) (3 / 4) = 1 / 2 := by
    rw [c7v, hu]; norm_num
  refine ⟨?_, ?_, by norm_num⟩
  · funext i
    fin_cases i
    · simp [c7demand, hu, Real.log_inv]
    · simp [c7demand, hv, Real.log_inv]
  · -- `t ↦ -ln((3/4 - t - 1 + √((1 - 3/4 + t)² + 3))/2)`
    have hg : HasDerivAt (fun t : ℝ => (1 - 3 / 4 + t) ^ 2 + 4 * (3 / 4)) 2 (3 / 4) := by
      have h := (((hasDerivAt_id (3 / 4 : ℝ)).const_add (1 - 3 / 4)).pow 2).add_const
        (4 * (3 / 4 : ℝ))
      convert h using 1 <;> norm_num [id]
    have hgpos : ((1 - 3 / 4 + 3 / 4 : ℝ) ^ 2 + 4 * (3 / 4)) ≠ 0 := by norm_num
    have hsqrt := hg.sqrt hgpos
    rw [hsq] at hsqrt
    have hu' : HasDerivAt (fun t : ℝ => c7u (3 / 4) t) (-1 / 4) (3 / 4) := by
      have h := ((((hasDerivAt_id (3 / 4 : ℝ)).const_sub (3 / 4 - 1)).add hsqrt).div_const 2)
      convert h using 1
      · funext t; simp only [c7u, id, Pi.add_apply]; ring
      · norm_num
    have hlog := hu'.log (by rw [hu]; norm_num)
    rw [hu] at hlog
    have h := hlog.neg
    convert h using 1
    · funext t
      simp [c7demand]
    · norm_num

end MWG.Production

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercises 5.D.3, 5.D.4(b)-(c) and 5.D.5(a) (MWG, pp. 162-163)

* **Exercise 5.D.3** (Le Chatelier): with long-run cost `c(q)` and short-run cost `c_s(q)`
  (input 1 fixed at its long-run optimal level for `q̄`), `c_s ≥ c` with equality at `q̄`. Then
  the long-run supply response `dq/dp` is at least the short-run one (`exercise_5_D_3`). The
  proof compares the long-run and short-run profit functions: their difference is minimized at
  `p̄`, its derivative is `q(p) - q_s(p)` by Hotelling's lemma (`hotelling_1d`), and a
  second-order necessary condition (`second_order_nonneg`) gives `q'(p̄) - q_s'(p̄) ≥ 0`. The
  inequality is weak in general (`exercise_5_D_3_equal`); `exercise_5_D_3_instance` is a strict
  example.
* **Exercise 5.D.4(b)**: decreasing ray average cost does not imply subadditivity:
  `C(q) = √q₁ + √q₂ + √(√q₁√q₂)` (`exercise_5_D_4b`).
* **Exercise 5.D.4(c)**: decreasing ray average cost and quasiconvexity (with `C` nondecreasing,
  `C(0) = 0`) imply subadditivity (`exercise_5_D_4c`; continuity is not needed); instance
  `C(q) = √(q₁ + q₂)` (`exercise_5_D_4c_instance`).
* **Exercise 5.D.5(a)**: increasing returns imply a nondecreasing average product
  (`exercise_5_D_5a_average`), but not a nondecreasing marginal product: `f(z) = z(1 - e^{-z})`
  (`exercise_5_D_5a_marginal`).
-/

namespace MWG.Production

open MWG.ClassicalDemand MWG.ConsumerChoice Filter Topology

/-! ### Exercise 5.D.3 -/

/-- Hotelling's lemma in one dimension: if `q(p')` maximizes `p'q - c(q)` over `q ≥ 0` for `p'`
near `p` and `q(·)` is continuous at `p`, then the profit `π(p') = p'q(p') - c(q(p'))` has
derivative `q(p)` at `p`. -/
theorem hotelling_1d {c qs : ℝ → ℝ} {p : ℝ}
    (hopt : ∀ᶠ p' in 𝓝 p, 0 ≤ qs p' ∧ ∀ q, 0 ≤ q → p' * q - c q ≤ p' * qs p' - c (qs p'))
    (hc : ContinuousAt qs p) :
    HasDerivAt (fun p' => p' * qs p' - c (qs p')) (qs p) p := by
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  have hp := hopt.self_of_nhds
  have hcl : ∀ᶠ p' in 𝓝 p, |qs p' - qs p| ≤ ε := by
    have := Metric.tendsto_nhds.mp hc.tendsto ε hε
    filter_upwards [this] with p' hp'
    rw [Real.dist_eq] at hp'
    exact hp'.le
  filter_upwards [hopt, hcl] with p' hp' hcl'
  have h1 := hp'.2 (qs p) hp.1
  have h2 := hp.2 (qs p') hp'.1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, smul_eq_mul, abs_le]
  have hab : |(p' - p) * (qs p' - qs p)| ≤ ε * |p' - p| := by
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right hcl' (abs_nonneg _)
  rw [abs_le] at hab
  constructor <;> nlinarith [abs_nonneg (p' - p)]

/-- A second-order necessary condition: if `g` has a local minimum at `x₀`, has derivative
`g'(x)` near `x₀`, `g'(x₀) = 0` and `g'` has derivative `d` at `x₀`, then `d ≥ 0`. -/
theorem second_order_nonneg {g g' : ℝ → ℝ} {x₀ d : ℝ} (hmin : ∀ᶠ x in 𝓝 x₀, g x₀ ≤ g x)
    (hg : ∀ᶠ x in 𝓝 x₀, HasDerivAt g (g' x) x) (hg0 : g' x₀ = 0) (hd : HasDerivAt g' d x₀) :
    0 ≤ d := by
  by_contra hneg
  push Not at hneg
  have hsl := hd.tendsto_slope_zero_right
  have hshift : Tendsto (fun t : ℝ => x₀ + t) (𝓝[>] 0) (𝓝 x₀) := by
    have : Tendsto (fun t : ℝ => x₀ + t) (𝓝 0) (𝓝 (x₀ + 0)) :=
      tendsto_const_nhds.add tendsto_id
    rw [add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), t⁻¹ • (g' (x₀ + t) - g' x₀) < 0 ∧
      HasDerivAt g (g' (x₀ + t)) (x₀ + t) ∧ g x₀ ≤ g (x₀ + t) :=
    (hsl.eventually (gt_mem_nhds hneg)).and ((hshift.eventually hg).and (hshift.eventually hmin))
  obtain ⟨ε, hε, hall⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.mp hev
  set b := ε / 2 with hb
  have hb0 : 0 < b := by positivity
  have hbε : b ∈ Set.Ioo 0 ε := ⟨hb0, by linarith⟩
  have hcont : ContinuousOn g (Set.Icc x₀ (x₀ + b)) := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with h | h
    · rw [← h]; exact hg.self_of_nhds.continuousAt.continuousWithinAt
    · have ht : x - x₀ ∈ Set.Ioo 0 ε := ⟨by linarith, by linarith [hx.2]⟩
      have := (hall ht).2.1
      rw [add_sub_cancel] at this
      exact this.continuousAt.continuousWithinAt
  have hderiv : ∀ x ∈ Set.Ioo x₀ (x₀ + b), HasDerivAt g (g' x) x := by
    intro x hx
    have ht : x - x₀ ∈ Set.Ioo 0 ε := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have := (hall ht).2.1
    rwa [add_sub_cancel] at this
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope g g' (by linarith) hcont hderiv
  have hξt : ξ - x₀ ∈ Set.Ioo 0 ε := ⟨by linarith [hξ.1], by linarith [hξ.2]⟩
  have hneg' := (hall hξt).1
  rw [add_sub_cancel, hg0, sub_zero, smul_eq_mul] at hneg'
  have hgξ : g' ξ < 0 := by
    have hpos : 0 < (ξ - x₀)⁻¹ := inv_pos.mpr hξt.1
    by_contra h
    push Not at h
    have := mul_nonneg hpos.le h
    linarith
  have hgb := (hall hbε).2.2
  rw [hξeq, add_sub_cancel_left] at hgξ
  have : g (x₀ + b) - g x₀ < 0 := by
    rw [div_neg_iff] at hgξ
    rcases hgξ with h | h
    · linarith [h.2]
    · linarith [h.1]
  linarith

/-- **Exercise 5.D.3** (MWG, p. 162), Le Chatelier. Let `c(q)` be the long-run cost and `c_s(q)`
the short-run cost with input 1 fixed at its long-run level for `q̄ = q(p̄)`, so that
`c_s ≥ c` on `q ≥ 0` with equality at `q̄` (`shortRun_ge_longRun`, `shortRun_eq_longRun`). If
the long-run and short-run supplies `q(p)`, `q_s(p)` maximize profits near `p̄`, coincide at
`p̄`, are continuous near `p̄` and differentiable at `p̄`, then `q_s'(p̄) ≤ q'(p̄)`: output
responds at least as much in the long run as in the short run. -/
theorem exercise_5_D_3 {c cs qL qS : ℝ → ℝ} {p dL dS : ℝ}
    (hle : ∀ q, 0 ≤ q → c q ≤ cs q) (heq : cs (qL p) = c (qL p)) (hsame : qS p = qL p)
    (hL : ∀ᶠ p' in 𝓝 p, 0 ≤ qL p' ∧ ∀ q, 0 ≤ q → p' * q - c q ≤ p' * qL p' - c (qL p'))
    (hS : ∀ᶠ p' in 𝓝 p, 0 ≤ qS p' ∧ ∀ q, 0 ≤ q → p' * q - cs q ≤ p' * qS p' - cs (qS p'))
    (hcL : ∀ᶠ p' in 𝓝 p, ContinuousAt qL p') (hcS : ∀ᶠ p' in 𝓝 p, ContinuousAt qS p')
    (hdL : HasDerivAt qL dL p) (hdS : HasDerivAt qS dS p) : dS ≤ dL := by
  set φ : ℝ → ℝ := fun p' => (p' * qL p' - c (qL p')) - (p' * qS p' - cs (qS p')) with hφ
  have hmin : ∀ᶠ x in 𝓝 p, φ p ≤ φ x := by
    filter_upwards [hL, hS] with x hx hx'
    have hφp : φ p = 0 := by simp only [hφ, hsame, heq]; ring
    rw [hφp]
    have h1 := hx.2 (qS x) hx'.1
    have h2 := hle (qS x) hx'.1
    simp only [hφ]
    linarith
  have hgrad : ∀ᶠ x in 𝓝 p, HasDerivAt φ (qL x - qS x) x := by
    filter_upwards [hL.eventually_nhds, hS.eventually_nhds, hcL, hcS] with x hx hx' hcx hcx'
    exact (hotelling_1d hx hcx).sub (hotelling_1d hx' hcx')
  have := second_order_nonneg hmin hgrad (by rw [hsame, sub_self]) (hdL.sub hdS)
  linarith

/-- **Exercise 5.D.3** (MWG, p. 162): a strict instance. With `c(q) = q²` and
`c_s(q) = q² + (q - 1)²` (`c_s ≥ c`, equal at `q̄ = 1`), at `p̄ = 2` the supplies are
`q(p) = p/2` and `q_s(p) = (p + 2)/4`, and `q_s' = 1/4 < 1/2 = q'`. -/
theorem exercise_5_D_3_instance :
    (∀ q : ℝ, 0 ≤ q → q ^ 2 ≤ q ^ 2 + (q - 1) ^ 2) ∧
      (∀ᶠ p' in 𝓝 (2 : ℝ), 0 ≤ p' / 2 ∧
        ∀ q : ℝ, 0 ≤ q → p' * q - q ^ 2 ≤ p' * (p' / 2) - (p' / 2) ^ 2) ∧
      (∀ᶠ p' in 𝓝 (2 : ℝ), 0 ≤ (p' + 2) / 4 ∧ ∀ q : ℝ, 0 ≤ q →
        p' * q - (q ^ 2 + (q - 1) ^ 2) ≤
          p' * ((p' + 2) / 4) - (((p' + 2) / 4) ^ 2 + ((p' + 2) / 4 - 1) ^ 2)) ∧
      HasDerivAt (fun p' : ℝ => p' / 2) (1 / 2) 2 ∧
      HasDerivAt (fun p' : ℝ => (p' + 2) / 4) (1 / 4) 2 ∧ (1 / 4 : ℝ) < 1 / 2 := by
  have hpos : ∀ᶠ p' in 𝓝 (2 : ℝ), 0 < p' := lt_mem_nhds (by norm_num)
  refine ⟨fun q _ => by nlinarith [sq_nonneg (q - 1)], ?_, ?_, ?_, ?_, by norm_num⟩
  · filter_upwards [hpos] with p' hp'
    exact ⟨by positivity, fun q _ => by nlinarith [sq_nonneg (q - p' / 2)]⟩
  · filter_upwards [hpos] with p' hp'
    exact ⟨by positivity, fun q _ => by nlinarith [sq_nonneg (q - (p' + 2) / 4)]⟩
  · simpa using (hasDerivAt_id (2 : ℝ)).div_const 2
  · simpa using ((hasDerivAt_id (2 : ℝ)).add_const 2).div_const 4

/-- **Exercise 5.D.3** (MWG, p. 162): the response is only weakly larger in general. If fixing
input 1 does not raise costs (`c_s = c`, e.g. when input 1 is not used), the short-run and
long-run supplies coincide: for `c(q) = q²`, both are `p/2`, with equal derivatives. -/
theorem exercise_5_D_3_equal :
    (∀ᶠ p' in 𝓝 (2 : ℝ), 0 ≤ p' / 2 ∧
        ∀ q : ℝ, 0 ≤ q → p' * q - q ^ 2 ≤ p' * (p' / 2) - (p' / 2) ^ 2) ∧
      HasDerivAt (fun p' : ℝ => p' / 2) (1 / 2) 2 := by
  have hpos : ∀ᶠ p' in 𝓝 (2 : ℝ), 0 < p' := lt_mem_nhds (by norm_num)
  refine ⟨?_, by simpa using (hasDerivAt_id (2 : ℝ)).div_const 2⟩
  filter_upwards [hpos] with p' hp'
  exact ⟨by positivity, fun q _ => by nlinarith [sq_nonneg (q - p' / 2)]⟩

/-! ### Exercise 5.D.4(b)-(c) -/

variable {M : ℕ}

/-- **Exercise 5.D.4** (MWG, p. 163). `C` is subadditive: no split of `q = Σ_j q_j` among
`J ≥ 1` firms has `Σ_j C(q_j) < C(q)`. -/
def Subadditive (C : (Fin M → ℝ) → ℝ) : Prop :=
  ∀ (J : ℕ), 0 < J → ∀ qs : Fin J → Fin M → ℝ, (∀ j, 0 ≤ qs j) → C (∑ j, qs j) ≤ ∑ j, C (qs j)

/-- **Exercise 5.D.4(b)** (MWG, p. 163). Decreasing ray average cost: `C(q) > C(kq)/k` for all
`k > 1` and `q ∈ ℝ^M_+`, `q ≠ 0` (at `q = 0` the condition would need `C(0) > 0`, against
`C(0) = 0` in (c)). -/
def DecreasingRayAC (C : (Fin M → ℝ) → ℝ) : Prop :=
  ∀ q : Fin M → ℝ, 0 ≤ q → q ≠ 0 → ∀ k : ℝ, 1 < k → C (k • q) / k < C q

/-- The cost function `C(q) = √q₁ + √q₂ + √(√q₁ √q₂)` of Exercise 5.D.4(b). -/
noncomputable def cost4b (q : Fin 2 → ℝ) : ℝ :=
  Real.sqrt (q 0) + Real.sqrt (q 1) + Real.sqrt (Real.sqrt (q 0) * Real.sqrt (q 1))

/-- **Exercise 5.D.4(b)** (MWG, p. 163). `C(q) = √q₁ + √q₂ + √(√q₁√q₂)` is continuous,
nondecreasing, has `C(0) = 0` and decreasing ray average cost (it is homogeneous of degree
`1/2`), but is not subadditive: producing `(1, 0)` and `(0, 1)` in separate firms costs
`2 < 3 = C(1, 1)`. -/
theorem exercise_5_D_4b :
    Continuous cost4b ∧ (∀ x y : Fin 2 → ℝ, x ≤ y → cost4b x ≤ cost4b y) ∧ cost4b 0 = 0 ∧
      DecreasingRayAC cost4b ∧ ¬ Subadditive cost4b := by
  refine ⟨by unfold cost4b; fun_prop, fun x y hxy => ?_, by simp [cost4b], ?_, ?_⟩
  · have h0 := Real.sqrt_le_sqrt (hxy 0)
    have h1 := Real.sqrt_le_sqrt (hxy 1)
    have h2 : Real.sqrt (x 0) * Real.sqrt (x 1) ≤ Real.sqrt (y 0) * Real.sqrt (y 1) :=
      mul_le_mul h0 h1 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    unfold cost4b
    linarith [Real.sqrt_le_sqrt h2]
  · intro q hq hq0 k hk
    have hk0 : 0 < k := by linarith
    have hsk : Real.sqrt (k * q 0) = Real.sqrt k * Real.sqrt (q 0) := Real.sqrt_mul hk0.le _
    have hsk1 : Real.sqrt (k * q 1) = Real.sqrt k * Real.sqrt (q 1) := Real.sqrt_mul hk0.le _
    have hkk : Real.sqrt k * Real.sqrt k = k := Real.mul_self_sqrt hk0.le
    have hs3 : Real.sqrt (Real.sqrt k * Real.sqrt (q 0) * (Real.sqrt k * Real.sqrt (q 1))) =
        Real.sqrt k * Real.sqrt (Real.sqrt (q 0) * Real.sqrt (q 1)) := by
      rw [show Real.sqrt k * Real.sqrt (q 0) * (Real.sqrt k * Real.sqrt (q 1)) =
        k * (Real.sqrt (q 0) * Real.sqrt (q 1)) by
          linear_combination (Real.sqrt (q 0) * Real.sqrt (q 1)) * hkk]
      exact Real.sqrt_mul hk0.le _
    have hC : cost4b (k • q) = Real.sqrt k * cost4b q := by
      simp only [cost4b, Pi.smul_apply, smul_eq_mul, hsk, hsk1, hs3]
      ring
    have hpos : 0 < cost4b q := by
      have : q 0 ≠ 0 ∨ q 1 ≠ 0 := by
        by_contra h
        push Not at h
        exact hq0 (funext fun i => by fin_cases i <;> simp [h.1, h.2])
      have n0 := Real.sqrt_nonneg (q 0)
      have n1 := Real.sqrt_nonneg (q 1)
      have n2 := Real.sqrt_nonneg (Real.sqrt (q 0) * Real.sqrt (q 1))
      unfold cost4b
      rcases this with h | h
      · have := Real.sqrt_pos.mpr (lt_of_le_of_ne (hq 0) (Ne.symm h)); linarith
      · have := Real.sqrt_pos.mpr (lt_of_le_of_ne (hq 1) (Ne.symm h)); linarith
    have hsk1' : 1 < Real.sqrt k := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_lt_sqrt zero_le_one hk
    rw [hC, div_lt_iff₀ hk0]
    have : 0 < Real.sqrt k := by linarith
    have h1 := mul_lt_mul_of_pos_left hsk1' (mul_pos this hpos)
    have h2 : Real.sqrt k * cost4b q * Real.sqrt k = cost4b q * k := by
      linear_combination cost4b q * hkk
    linarith
  · intro hsub
    have h := hsub 2 (by norm_num) ![![1, 0], ![0, 1]] (fun j => by
      fin_cases j <;> intro i <;> fin_cases i <;> simp)
    have hsum : (∑ j, (![![1, 0], ![0, 1]] : Fin 2 → Fin 2 → ℝ) j) = ![1, 1] := by
      funext i; fin_cases i <;> simp [Fin.sum_univ_two]
    rw [hsum, Fin.sum_univ_two] at h
    simp [cost4b] at h
    norm_num at h

/-- **Exercise 5.D.4(c)** (MWG, p. 163). If `C` is nondecreasing on `ℝ^M_+`, `C(0) = 0`, and `C`
has decreasing ray average cost and is quasiconvex on `ℝ^M_+`, then `C` is subadditive. (The
book's continuity hypothesis is not needed.) Proof: with `S = Σ_j C(q_j)`,
`q = Σ_j (C(q_j)/S)·(S/C(q_j)) q_j` is a convex combination of points of the sublevel set
`{C ≤ S}` (by decreasing ray average cost), which is convex. -/
theorem exercise_5_D_4c {C : (Fin M → ℝ) → ℝ}
    (hmono : ∀ x y : Fin M → ℝ, 0 ≤ x → x ≤ y → C x ≤ C y) (h0 : C 0 = 0)
    (hqc : QuasiconvexOn ℝ {x : Fin M → ℝ | 0 ≤ x} C) (hdrac : DecreasingRayAC C) :
    Subadditive C := by
  intro J hJ qs hqs
  have hCnn : ∀ x : Fin M → ℝ, 0 ≤ x → 0 ≤ C x := fun x hx => h0 ▸ hmono 0 x le_rfl hx
  have hCpos : ∀ x : Fin M → ℝ, 0 ≤ x → x ≠ 0 → 0 < C x := by
    intro x hx hx0
    have h2 := hdrac x hx hx0 2 one_lt_two
    have : 0 ≤ C ((2 : ℝ) • x) / 2 := div_nonneg (hCnn _ (smul_nonneg zero_le_two hx))
      zero_le_two
    linarith
  set S := ∑ j, C (qs j) with hS
  have hSnn : 0 ≤ S := Finset.sum_nonneg fun j _ => hCnn _ (hqs j)
  have hqnn : 0 ≤ ∑ j, qs j := Finset.sum_nonneg fun j _ => hqs j
  rcases hSnn.lt_or_eq with hSpos | hS0
  · -- the convex combination
    set lam : Fin J → ℝ := fun j => C (qs j) / S with hlam
    set x : Fin J → Fin M → ℝ := fun j => (S / C (qs j)) • qs j with hx
    have hlam0 : ∀ j ∈ Finset.univ, 0 ≤ lam j := fun j _ => div_nonneg (hCnn _ (hqs j)) hSpos.le
    have hlam1 : ∑ j ∈ Finset.univ, lam j = 1 := by
      rw [hlam, ← Finset.sum_div, ← hS, div_self hSpos.ne']
    have hcomb : ∑ j ∈ Finset.univ, lam j • x j = ∑ j, qs j := by
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : qs j = 0
      · simp [hlam, hx, hj]
      · have hc := hCpos _ (hqs j) hj
        simp only [hlam, hx, smul_smul]
        rw [show C (qs j) / S * (S / C (qs j)) = 1 by field_simp, one_smul]
    have hmem : ∀ j ∈ Finset.univ, x j ∈ {y | y ∈ {x : Fin M → ℝ | 0 ≤ x} ∧ C y ≤ S} := by
      intro j _
      by_cases hj : qs j = 0
      · refine ⟨by simp [hx, hj], ?_⟩
        simp only [hx, hj, smul_zero, h0]
        exact hSnn
      · have hc := hCpos _ (hqs j) hj
        have hle : C (qs j) ≤ S :=
          Finset.single_le_sum (fun i _ => hCnn _ (hqs i)) (Finset.mem_univ j)
        have hk : 1 ≤ S / C (qs j) := by rw [le_div_iff₀ hc]; linarith
        refine ⟨smul_nonneg (by linarith) (hqs j), ?_⟩
        rcases hk.lt_or_eq with hk1 | hk1
        · have := hdrac (qs j) (hqs j) hj _ hk1
          rw [div_lt_iff₀ (by linarith)] at this
          have e : C (qs j) * (S / C (qs j)) = S := by field_simp
          simp only [hx]
          linarith
        · simp only [hx, ← hk1, one_smul]
          exact hle
    have := (hqc S).sum_mem hlam0 hlam1 hmem
    rw [hcomb] at this
    exact this.2
  · -- all costs zero: then all `q_j = 0`
    have hall : ∀ j, qs j = 0 := by
      intro j
      by_contra hj
      have hc := hCpos _ (hqs j) hj
      have hle : C (qs j) ≤ S :=
        Finset.single_le_sum (fun i _ => hCnn _ (hqs i)) (Finset.mem_univ j)
      linarith
    have : ∑ j, qs j = 0 := Finset.sum_eq_zero fun j _ => hall j
    rw [this, h0]
    exact hSnn

/-- **Exercise 5.D.4(c)** (MWG, p. 163): the hypotheses are met by `C(q) = √(q₁ + q₂)`. -/
theorem exercise_5_D_4c_instance :
    let C : (Fin 2 → ℝ) → ℝ := fun q => Real.sqrt (q 0 + q 1)
    (∀ x y : Fin 2 → ℝ, 0 ≤ x → x ≤ y → C x ≤ C y) ∧ C 0 = 0 ∧
      QuasiconvexOn ℝ {x : Fin 2 → ℝ | 0 ≤ x} C ∧ DecreasingRayAC C ∧ Subadditive C := by
  intro C
  have hmono : ∀ x y : Fin 2 → ℝ, 0 ≤ x → x ≤ y → C x ≤ C y :=
    fun x y _ hxy => Real.sqrt_le_sqrt (add_le_add (hxy 0) (hxy 1))
  have h0 : C 0 = 0 := by simp [C]
  have hqc : QuasiconvexOn ℝ {x : Fin 2 → ℝ | 0 ≤ x} C := by
    intro r
    rintro x ⟨hx, hxr⟩ y ⟨hy, hyr⟩ a b ha hb hab
    refine ⟨fun i => ?_, ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      exact add_nonneg (mul_nonneg ha (hx i)) (mul_nonneg hb (hy i))
    · simp only [C, Real.sqrt_le_iff] at hxr hyr ⊢
      refine ⟨hxr.1, ?_⟩
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith [hxr.2, hyr.2]
  have hdrac : DecreasingRayAC C := by
    intro q hq hq0 k hk
    have hk0 : 0 < k := by linarith
    have q0 : 0 ≤ q 0 := hq 0
    have q1 : 0 ≤ q 1 := hq 1
    have hs : 0 < q 0 + q 1 := by
      rcases (add_nonneg q0 q1).lt_or_eq with h | h
      · exact h
      · exfalso
        have a0 : q 0 = 0 := by linarith
        have a1 : q 1 = 0 := by linarith
        exact hq0 (funext fun i => by fin_cases i <;> simp [a0, a1])
    have e : C (k • q) = Real.sqrt k * C q := by
      simp only [C, Pi.smul_apply, smul_eq_mul, ← mul_add]
      exact Real.sqrt_mul hk0.le _
    have hkk : Real.sqrt k * Real.sqrt k = k := Real.mul_self_sqrt hk0.le
    have hsk1 : 1 < Real.sqrt k := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_lt_sqrt zero_le_one hk
    have hC : 0 < C q := Real.sqrt_pos.mpr hs
    rw [e, div_lt_iff₀ hk0]
    have h1 := mul_lt_mul_of_pos_left hsk1 (mul_pos (by linarith : 0 < Real.sqrt k) hC)
    have h2 : Real.sqrt k * C q * Real.sqrt k = C q * k := by
      linear_combination C q * hkk
    linarith
  exact ⟨hmono, h0, hqc, hdrac, exercise_5_D_4c hmono h0 hqc hdrac⟩

/-! ### Exercise 5.D.5(a) -/

/-- **Exercise 5.D.5(a)** (MWG, p. 163), average product. If `f` has increasing returns to
scale (`f(αz) ≥ αf(z)` for `α ≥ 1`, `z ≥ 0`), the average product `f(z)/z` is nondecreasing on
`z > 0`. (Differentiability is not needed.) -/
theorem exercise_5_D_5a_average {f : ℝ → ℝ}
    (hirs : ∀ z, 0 ≤ z → ∀ α : ℝ, 1 ≤ α → α * f z ≤ f (α * z)) {z z' : ℝ} (hz : 0 < z)
    (hzz : z ≤ z') : f z / z ≤ f z' / z' := by
  have hz' : 0 < z' := lt_of_lt_of_le hz hzz
  have h := hirs z hz.le (z' / z) (by rw [le_div_iff₀ hz]; linarith)
  rw [div_mul_cancel₀ _ hz.ne'] at h
  rw [div_le_div_iff₀ hz hz']
  have : z' / z * f z * z = z' * f z := by field_simp
  nlinarith

/-- The production function `f(z) = z(1 - e^{-z})` of Exercise 5.D.5(a). -/
noncomputable def prod5a (z : ℝ) : ℝ := z * (1 - Real.exp (-z))

/-- **Exercise 5.D.5(a)** (MWG, p. 163), marginal product. `f(z) = z(1 - e^{-z})` is
differentiable with `f'(z) = 1 - e^{-z} + ze^{-z}` and has (strictly) increasing returns to
scale, but its marginal product falls between `z = 2` and `z = 3`:
`f'(3) = 1 + 2e^{-3} < 1 + e^{-2} = f'(2)`. -/
theorem exercise_5_D_5a_marginal :
    (∀ z : ℝ, HasDerivAt prod5a (1 - Real.exp (-z) + z * Real.exp (-z)) z) ∧
      (∀ z, 0 ≤ z → ∀ α : ℝ, 1 ≤ α → α * prod5a z ≤ prod5a (α * z)) ∧
      (∀ z, 0 < z → ∀ α : ℝ, 1 < α → α * prod5a z < prod5a (α * z)) ∧
      1 - Real.exp (-3) + 3 * Real.exp (-3) < 1 - Real.exp (-2) + 2 * Real.exp (-2) := by
  refine ⟨fun z => ?_, fun z hz α hα => ?_, fun z hz α hα => ?_, ?_⟩
  · have h := (hasDerivAt_id z).mul (((hasDerivAt_id z).neg.exp).const_sub 1)
    convert h using 1
    · funext x; simp [prod5a]
    · simp
  · have : Real.exp (-(α * z)) ≤ Real.exp (-z) :=
      Real.exp_le_exp.mpr (by nlinarith)
    unfold prod5a
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ α) hz]
  · have : Real.exp (-(α * z)) < Real.exp (-z) :=
      Real.exp_lt_exp.mpr (by nlinarith)
    unfold prod5a
    nlinarith [mul_pos (by linarith : (0 : ℝ) < α) hz]
  · have he : 2 < Real.exp 1 := by
      have := Real.add_one_lt_exp (one_ne_zero : (1 : ℝ) ≠ 0)
      linarith
    have h2 : Real.exp (-2) = Real.exp 1 * Real.exp (-3) := by
      rw [← Real.exp_add]; norm_num
    have h3 := Real.exp_pos (-3)
    rw [h2]
    nlinarith

end MWG.Production

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercise 5.E.4: a uniform population of Leontief technologies (MWG, pp. 163-164)

Each technology `z = (z₁, z₂) ∈ [0, 10]²` produces up to one unit of output with fixed input
requirements `z₁, z₂` per unit; the technologies are uniformly distributed on `[0, 10]²`
(density `1/100`). The integrals over the square are written as iterated interval integrals.

* (a) At input prices `w` and output price `1`, technology `z` produces `1` if `w·z < 1`, `0`
  if `w·z > 1` (anything in `[0, 1]` if `w·z = 1`) and earns `max(0, 1 - w·z)`
  (`exercise_5_E_4a`).
* (b) For `w₁, w₂ ≥ 1/10` the aggregate profit is `π(w₁, w₂, 1) = 1/(600 w₁ w₂)`
  (`exercise_5_E_4b`).
* (c) The aggregate input demands, computed directly, are `z₁(w) = 1/(600 w₁² w₂)` and
  `z₂(w) = 1/(600 w₁ w₂²)`, and they equal `-∂π/∂w_ℓ` (`exercise_5_E_4c`).
* (d) If `π(w) = 1/(600 w₁ w₂)` held for all `w ≫ 0`, it would be the profit function of the
  Cobb-Douglas production function `f(z) = (9 z₁ z₂/200)^{1/3}` (decreasing returns, degree
  `2/3`), with the same input demands (`exercise_5_E_4d`).
-/

namespace MWG.Production

open MWG.ClassicalDemand MWG.ConsumerChoice Filter Topology MeasureTheory

/-! ### (a) One technology -/

/-- **Exercise 5.E.4(a)** (MWG, p. 163). The technology `z` choosing output `q ∈ [0, 1]` at
input prices `w` (output price `1`) earns `q(1 - w·z) ≤ max(0, 1 - w·z)`; if `w·z < 1` the
unique optimum is `q = 1`, if `w·z > 1` it is `q = 0`, and if `w·z = 1` every `q` is optimal. -/
theorem exercise_5_E_4a (w z : Fin 2 → ℝ) :
    (∀ q ∈ Set.Icc (0 : ℝ) 1, q * (1 - w ⬝ᵥ z) ≤ max 0 (1 - w ⬝ᵥ z)) ∧
      (w ⬝ᵥ z < 1 → ∀ q ∈ Set.Icc (0 : ℝ) 1,
        (q * (1 - w ⬝ᵥ z) = max 0 (1 - w ⬝ᵥ z) ↔ q = 1)) ∧
      (1 < w ⬝ᵥ z → ∀ q ∈ Set.Icc (0 : ℝ) 1,
        (q * (1 - w ⬝ᵥ z) = max 0 (1 - w ⬝ᵥ z) ↔ q = 0)) ∧
      (w ⬝ᵥ z = 1 → ∀ q ∈ Set.Icc (0 : ℝ) 1, q * (1 - w ⬝ᵥ z) = max 0 (1 - w ⬝ᵥ z)) := by
  refine ⟨fun q hq => ?_, fun h q hq => ?_, fun h q hq => ?_, fun h q _ => ?_⟩
  · rcases le_total 0 (1 - w ⬝ᵥ z) with h | h
    · rw [max_eq_right h]; nlinarith [hq.1, hq.2]
    · rw [max_eq_left h]; nlinarith [hq.1, hq.2]
  · rw [max_eq_right (by linarith)]
    constructor
    · intro he
      have : (q - 1) * (1 - w ⬝ᵥ z) = 0 := by linarith
      rcases mul_eq_zero.mp this with h' | h'
      · linarith
      · linarith
    · rintro rfl; ring
  · rw [max_eq_left (by linarith)]
    constructor
    · intro he
      rcases mul_eq_zero.mp he with h' | h'
      · exact h'
      · linarith
    · rintro rfl; ring
  · rw [h]; simp

/-! ### Integrals -/

/-- `∫₀ᵇ max(0, c - at)^{k+1} dt = max(0, c)^{k+2}/((k+2)a)` for `a > 0`, `c ≤ ab`. -/
theorem e4_pow_integral {a c b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hcb : c ≤ a * b) (k : ℕ) :
    ∫ t in (0 : ℝ)..b, (max 0 (c - a * t)) ^ (k + 1) = (max 0 c) ^ (k + 2) / ((k + 2) * a) := by
  have hcont : Continuous fun t : ℝ => (max 0 (c - a * t)) ^ (k + 1) :=
    (continuous_const.max (continuous_const.sub (continuous_const.mul continuous_id))).pow _
  rcases le_or_gt c 0 with hc | hc
  · have h0 : Set.EqOn (fun t : ℝ => (max 0 (c - a * t)) ^ (k + 1)) (fun _ => 0)
        (Set.uIcc 0 b) := by
      intro t ht
      rw [Set.uIcc_of_le hb] at ht
      have : c - a * t ≤ 0 := by nlinarith [ht.1]
      simp [max_eq_left this]
    rw [intervalIntegral.integral_congr h0, intervalIntegral.integral_zero, max_eq_left hc]
    simp
  · set t0 := c / a with ht0
    have ht00 : 0 ≤ t0 := div_nonneg hc.le ha.le
    have ht0b : t0 ≤ b := by rw [ht0, div_le_iff₀ ha]; linarith
    have hat0 : a * t0 = c := by rw [ht0]; field_simp
    rw [← intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable 0 t0)
      (hcont.intervalIntegrable t0 b)]
    have h1 : Set.EqOn (fun t : ℝ => (max 0 (c - a * t)) ^ (k + 1))
        (fun t => (c - a * t) ^ (k + 1)) (Set.uIcc 0 t0) := by
      intro t ht
      rw [Set.uIcc_of_le ht00] at ht
      have : 0 ≤ c - a * t := by nlinarith [ht.2]
      simp only [max_eq_right this]
    have h2 : Set.EqOn (fun t : ℝ => (max 0 (c - a * t)) ^ (k + 1)) (fun _ => 0)
        (Set.uIcc t0 b) := by
      intro t ht
      rw [Set.uIcc_of_le ht0b] at ht
      have : c - a * t ≤ 0 := by nlinarith [ht.1]
      simp [max_eq_left this]
    rw [intervalIntegral.integral_congr h1, intervalIntegral.integral_congr h2,
      intervalIntegral.integral_zero, add_zero, max_eq_right hc.le]
    have hk : (0 : ℝ) < k + 2 := by positivity
    have hF : ∀ t ∈ Set.uIcc 0 t0, HasDerivAt
        (fun t : ℝ => -(c - a * t) ^ (k + 2) / ((k + 2) * a)) ((c - a * t) ^ (k + 1)) t := by
      intro t _
      have h := ((((hasDerivAt_id t).const_mul a).const_sub c).pow (k + 2)).neg.div_const
        ((k + 2) * a)
      convert h using 1
      · funext x; simp
      · rw [show k + 2 - 1 = k + 1 by omega]
        simp only [id, mul_one]
        push_cast
        field_simp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
      ((by fun_prop : Continuous fun x : ℝ => (c - a * x) ^ (k + 1)).intervalIntegrable 0 t0)]
    rw [hat0]
    simp only [sub_self, mul_zero, sub_zero]
    rw [zero_pow (by omega)]
    ring

/-- `∫₀ᵇ 1[at < c] dt = max(0, c)/a` for `a > 0`, `c ≤ ab`. -/
theorem e4_step_integral {a c b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hcb : c ≤ a * b) :
    ∫ t in (0 : ℝ)..b, (if a * t < c then (1 : ℝ) else 0) = max 0 c / a := by
  rcases le_or_gt c 0 with hc | hc
  · have h0 : Set.EqOn (fun t : ℝ => if a * t < c then (1 : ℝ) else 0) (fun _ => 0)
        (Set.uIcc 0 b) := by
      intro t ht
      rw [Set.uIcc_of_le hb] at ht
      have : ¬ a * t < c := by push Not; nlinarith [ht.1]
      simp only [this, ↓reduceIte]
    rw [intervalIntegral.integral_congr h0, intervalIntegral.integral_zero, max_eq_left hc,
      zero_div]
  · set t0 := c / a with ht0
    have ht00 : 0 ≤ t0 := div_nonneg hc.le ha.le
    have ht0b : t0 ≤ b := by rw [ht0, div_le_iff₀ ha]; linarith
    have hat0 : a * t0 = c := by rw [ht0]; field_simp
    have hanti : Antitone fun t : ℝ => if a * t < c then (1 : ℝ) else 0 := by
      intro x y hxy
      have : a * x ≤ a * y := mul_le_mul_of_nonneg_left hxy ha.le
      by_cases hy : a * y < c
      · have hx : a * x < c := lt_of_le_of_lt this hy
        simp only [hx, hy, ↓reduceIte, le_refl]
      · simp only [hy, ↓reduceIte]
        split_ifs <;> norm_num
    have i1 : IntervalIntegrable (fun t : ℝ => if a * t < c then (1 : ℝ) else 0) volume 0 t0 :=
      hanti.intervalIntegrable
    have i2 : IntervalIntegrable (fun t : ℝ => if a * t < c then (1 : ℝ) else 0) volume t0 b :=
      hanti.intervalIntegrable
    rw [← intervalIntegral.integral_add_adjacent_intervals i1 i2]
    have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ t0 := by
      rw [ae_iff]
      simp
    have h1 : ∫ t in (0 : ℝ)..t0, (if a * t < c then (1 : ℝ) else 0) =
        ∫ _t in (0 : ℝ)..t0, (1 : ℝ) := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [hae] with x hx hmem
      rw [Set.uIoc_of_le ht00] at hmem
      have hlt : x < t0 := lt_of_le_of_ne hmem.2 hx
      have : a * x < c := by rw [← hat0]; exact mul_lt_mul_of_pos_left hlt ha
      simp only [this, ↓reduceIte]
    have h2 : Set.EqOn (fun t : ℝ => if a * t < c then (1 : ℝ) else 0) (fun _ => 0)
        (Set.uIcc t0 b) := by
      intro t ht
      rw [Set.uIcc_of_le ht0b] at ht
      have : ¬ a * t < c := by
        push Not
        rw [← hat0]
        exact mul_le_mul_of_nonneg_left ht.1 ha.le
      simp only [this, ↓reduceIte]
    rw [h1, intervalIntegral.integral_congr h2, intervalIntegral.integral_zero, add_zero,
      intervalIntegral.integral_const, max_eq_right hc.le, ht0]
    simp

/-! ### (b) Aggregate profit -/

/-- **Exercise 5.E.4(b)** (MWG, p. 164). The aggregate profit
`π(w, 1) = (1/100) ∫₀¹⁰∫₀¹⁰ max(0, 1 - w₁z₁ - w₂z₂) dz₂ dz₁` of the population. -/
noncomputable def e4AggProfit (w : Fin 2 → ℝ) : ℝ :=
  (1 / 100) * ∫ s in (0 : ℝ)..10, ∫ t in (0 : ℝ)..10, max 0 (1 - w 0 * s - w 1 * t)

/-- **Exercise 5.E.4(b)** (MWG, p. 164): for `w₁, w₂ ≥ 1/10`, `π(w₁, w₂, 1) = 1/(600 w₁ w₂)`. -/
theorem exercise_5_E_4b {w : Fin 2 → ℝ} (h0 : 1 / 10 ≤ w 0) (h1 : 1 / 10 ≤ w 1) :
    e4AggProfit w = 1 / (600 * w 0 * w 1) := by
  have hw0 : 0 < w 0 := by linarith
  have hw1 : 0 < w 1 := by linarith
  have hinner : Set.EqOn (fun s => ∫ t in (0 : ℝ)..10, max 0 (1 - w 0 * s - w 1 * t))
      (fun s => (max 0 (1 - w 0 * s)) ^ 2 / (2 * w 1)) (Set.uIcc 0 10) := by
    intro s hs
    rw [Set.uIcc_of_le (by norm_num)] at hs
    have h := e4_pow_integral hw1 (by norm_num : (0 : ℝ) ≤ 10)
      (show 1 - w 0 * s ≤ w 1 * 10 by nlinarith [hs.1]) 0
    simp only [zero_add, pow_one, Nat.cast_zero] at h
    simpa only [sub_sub] using h
  unfold e4AggProfit
  rw [intervalIntegral.integral_congr hinner, intervalIntegral.integral_div]
  have h := e4_pow_integral hw0 (by norm_num : (0 : ℝ) ≤ 10)
    (show (1 : ℝ) ≤ w 0 * 10 by linarith) 1
  simp only [show (1 : ℕ) + 1 = 2 from rfl, max_eq_right (zero_le_one' ℝ), one_pow] at h
  rw [h]
  push_cast
  field_simp
  ring

/-! ### (c) Aggregate input demand -/

/-- **Exercise 5.E.4(c)** (MWG, p. 164). The aggregate demand for an input with price `a`,
the other input having price `b`: `(1/100) ∫₀¹⁰∫₀¹⁰ s·q(s, t) dt ds`, where technology `(s, t)`
(`s` the requirement of this input) produces `q = 1` iff `as + bt < 1` (the boundary
`as + bt = 1` has measure zero). The demand for `z₁` is `e4AggDemand w₁ w₂`, for `z₂`
`e4AggDemand w₂ w₁`. -/
noncomputable def e4AggDemand (a b : ℝ) : ℝ :=
  (1 / 100) * ∫ s in (0 : ℝ)..10, ∫ t in (0 : ℝ)..10,
    s * (if a * s + b * t < 1 then (1 : ℝ) else 0)

/-- The aggregate demand computed directly: `1/(600 a² b)` for `a, b ≥ 1/10`. -/
theorem e4AggDemand_eq {a b : ℝ} (ha : 1 / 10 ≤ a) (hb : 1 / 10 ≤ b) :
    e4AggDemand a b = 1 / (600 * a ^ 2 * b) := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hinner : Set.EqOn (fun s => ∫ t in (0 : ℝ)..10,
      s * (if a * s + b * t < 1 then (1 : ℝ) else 0))
      (fun s => s * (max 0 (1 - a * s) / b)) (Set.uIcc 0 10) := by
    intro s hs
    rw [Set.uIcc_of_le (by norm_num)] at hs
    have e : (fun t => s * (if a * s + b * t < 1 then (1 : ℝ) else 0)) =
        fun t => s * (if b * t < 1 - a * s then (1 : ℝ) else 0) := by
      funext t
      congr 1
      exact if_congr ⟨fun h => by linarith, fun h => by linarith⟩ rfl rfl
    change ∫ t in (0 : ℝ)..10, s * (if a * s + b * t < 1 then (1 : ℝ) else 0) =
      s * (max 0 (1 - a * s) / b)
    rw [e, intervalIntegral.integral_const_mul, e4_step_integral hb0 (by norm_num)
      (by nlinarith [hs.1])]
  unfold e4AggDemand
  rw [intervalIntegral.integral_congr hinner]
  set s0 := 1 / a with hs0
  have hs00 : 0 ≤ s0 := by positivity
  have hs010 : s0 ≤ 10 := by rw [hs0, div_le_iff₀ ha0]; linarith
  have has0 : a * s0 = 1 := by rw [hs0]; field_simp
  have hcont : Continuous fun s : ℝ => s * (max 0 (1 - a * s) / b) :=
    continuous_id.mul ((continuous_const.max
      (continuous_const.sub (continuous_const.mul continuous_id))).div_const _)
  rw [← intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable 0 s0)
    (hcont.intervalIntegrable s0 10)]
  have h1 : Set.EqOn (fun s : ℝ => s * (max 0 (1 - a * s) / b))
      (fun s => s * (1 - a * s) / b) (Set.uIcc 0 s0) := by
    intro s hs
    rw [Set.uIcc_of_le hs00] at hs
    have : 0 ≤ 1 - a * s := by nlinarith [hs.2]
    simp only [max_eq_right this]
    ring
  have h2 : Set.EqOn (fun s : ℝ => s * (max 0 (1 - a * s) / b)) (fun _ => 0)
      (Set.uIcc s0 10) := by
    intro s hs
    rw [Set.uIcc_of_le hs010] at hs
    have : 1 - a * s ≤ 0 := by nlinarith [hs.1]
    simp [max_eq_left this]
  rw [intervalIntegral.integral_congr h1, intervalIntegral.integral_congr h2,
    intervalIntegral.integral_zero, add_zero]
  have hF : ∀ s ∈ Set.uIcc 0 s0, HasDerivAt (fun s : ℝ => (s ^ 2 / 2 - a * s ^ 3 / 3) / b)
      (s * (1 - a * s) / b) s := by
    intro s _
    have h := ((((hasDerivAt_id s).pow 2).div_const 2).sub
      (((hasDerivAt_id s).pow 3).const_mul a |>.div_const 3)).div_const b
    convert h using 1
    · funext x; simp
    · simp only [id]
      push_cast
      ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    ((by fun_prop : Continuous fun x : ℝ => x * (1 - a * x) / b).intervalIntegrable 0 s0), hs0]
  field_simp
  ring

/-- **Exercise 5.E.4(c)** (MWG, p. 164). For `w₁, w₂ ≥ 1/10` the aggregate input demands are
`z₁(w) = 1/(600 w₁² w₂)` and `z₂(w) = 1/(600 w₁ w₂²)` (computed directly), and they agree with
`-∂π/∂w₁`, `-∂π/∂w₂` from (b) (Hotelling's lemma), which verifies (b). -/
theorem exercise_5_E_4c {w : Fin 2 → ℝ} (h0 : 1 / 10 ≤ w 0) (h1 : 1 / 10 ≤ w 1) :
    e4AggDemand (w 0) (w 1) = 1 / (600 * w 0 ^ 2 * w 1) ∧
      e4AggDemand (w 1) (w 0) = 1 / (600 * w 0 * w 1 ^ 2) ∧
      HasDerivAt (fun x => 1 / (600 * x * w 1)) (-e4AggDemand (w 0) (w 1)) (w 0) ∧
      HasDerivAt (fun x => 1 / (600 * w 0 * x)) (-e4AggDemand (w 1) (w 0)) (w 1) := by
  have hw0 : 0 < w 0 := by linarith
  have hw1 : 0 < w 1 := by linarith
  have d1 := e4AggDemand_eq h0 h1
  have d2 := e4AggDemand_eq h1 h0
  refine ⟨d1, by rw [d2]; ring, ?_, ?_⟩
  · rw [d1]
    have h := (hasDerivAt_inv hw0.ne').const_mul (1 / (600 * w 1))
    convert h using 1
    · funext x; ring
    · ring
  · rw [d2]
    have h := (hasDerivAt_inv hw1.ne').const_mul (1 / (600 * w 0))
    convert h using 1
    · funext x; ring
    · ring

/-! ### (d) The aggregate production function -/

/-- The Cobb-Douglas production function `f(z) = (9 z₁ z₂/200)^{1/3}`. -/
noncomputable def e4Prod (z : Fin 2 → ℝ) : ℝ := (9 / 200 * (z 0 * z 1)) ^ ((3 : ℕ)⁻¹ : ℝ)

/-- **Exercise 5.E.4(d)** (MWG, p. 164). If the profit function `1/(600 w₁ w₂)` of (b) held for
all `w ≫ 0`, the underlying aggregate production function would be
`f(z) = (9 z₁ z₂/200)^{1/3}`: for every `w ≫ 0`, `max_{z ≥ 0} f(z) - w·z = 1/(600 w₁ w₂)`,
attained at the input demands `(1/(600 w₁² w₂), 1/(600 w₁ w₂²))` of (c). -/
theorem exercise_5_E_4d {w : Fin 2 → ℝ} (hw : StrictlyPositive w) :
    (∀ z : Fin 2 → ℝ, 0 ≤ z → e4Prod z - w ⬝ᵥ z ≤ 1 / (600 * w 0 * w 1)) ∧
      e4Prod ![1 / (600 * w 0 ^ 2 * w 1), 1 / (600 * w 0 * w 1 ^ 2)] -
        w ⬝ᵥ ![1 / (600 * w 0 ^ 2 * w 1), 1 / (600 * w 0 * w 1 ^ 2)] = 1 / (600 * w 0 * w 1) := by
  have hw0 := hw 0
  have hw1 := hw 1
  set K := 1 / (600 * w 0 * w 1) with hK
  have hK0 : 0 < K := by positivity
  have hdot : ∀ z : Fin 2 → ℝ, w ⬝ᵥ z = w 0 * z 0 + w 1 * z 1 := fun z => by
    simp [dotProduct, Fin.sum_univ_two]
  -- `f(z) = 3 (K · w₁z₁ · w₂z₂)^{1/3}`
  have hcube : ((27 : ℝ)) ^ ((3 : ℕ)⁻¹ : ℝ) = 3 := by
    rw [show (27 : ℝ) = 3 ^ 3 by norm_num]
    exact Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)
  have hf : ∀ z : Fin 2 → ℝ, 0 ≤ z →
      e4Prod z = 3 * (K * (w 0 * z 0) * (w 1 * z 1)) ^ ((3 : ℕ)⁻¹ : ℝ) := by
    intro z hz
    have hz0 : 0 ≤ z 0 := hz 0
    have hz1 : 0 ≤ z 1 := hz 1
    have e : 9 / 200 * (z 0 * z 1) = 27 * (K * (w 0 * z 0) * (w 1 * z 1)) := by
      rw [hK]; field_simp; ring
    rw [e4Prod, e, Real.mul_rpow (by norm_num) (by positivity), hcube]
  refine ⟨fun z hz => ?_, ?_⟩
  · have hz0 : 0 ≤ z 0 := hz 0
    have hz1 : 0 ≤ z 1 := hz 1
    have hamgm := Real.geom_mean_le_arith_mean3_weighted (w₁ := (3 : ℕ)⁻¹) (w₂ := (3 : ℕ)⁻¹)
      (w₃ := (3 : ℕ)⁻¹) (p₁ := K) (p₂ := w 0 * z 0) (p₃ := w 1 * z 1) (by norm_num)
      (by norm_num) (by norm_num) hK0.le (by positivity) (by positivity) (by norm_num)
    rw [← Real.mul_rpow hK0.le (by positivity), ← Real.mul_rpow (by positivity)
      (by positivity)] at hamgm
    rw [hf z hz, hdot]
    push_cast at hamgm
    linarith
  · have hz : (0 : Fin 2 → ℝ) ≤ ![1 / (600 * w 0 ^ 2 * w 1), 1 / (600 * w 0 * w 1 ^ 2)] := by
      intro i
      fin_cases i
      · change 0 ≤ 1 / (600 * w 0 ^ 2 * w 1); positivity
      · change 0 ≤ 1 / (600 * w 0 * w 1 ^ 2); positivity
    rw [hf _ hz, hdot]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    have e1 : w 0 * (1 / (600 * w 0 ^ 2 * w 1)) = K := by rw [hK]; field_simp
    have e2 : w 1 * (1 / (600 * w 0 * w 1 ^ 2)) = K := by rw [hK]; field_simp
    rw [e1, e2, show K * K * K = K ^ 3 by ring,
      Real.pow_rpow_inv_natCast hK0.le (by norm_num)]
    ring

end MWG.Production

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercise 5.AA.1: the cost function of Figure 5.AA.4 (MWG, pp. 159, 164)

Figure 5.AA.4 (p. 159) shows the unit isoquant of good 1 produced from goods 2 and 3 with the
elementary activities `a₁ = (1, -2, -1)`, `a₂ = (1, -1, -2)` and the disposal activities
`d₁, d₂, d₃`. The input requirement set for one unit of good 1 is
`V = {z ∈ ℝ² : (1, -z₂, -z₃) ∈ Y}`, `Y` the cone generated by the five activities
(`aa1Req`), equivalently `{z : z ≥ α(2, 1) + β(1, 2), α, β ≥ 0, α + β ≥ 1}` (`mem_aa1Req_iff`).

**Exercise 5.AA.1**: for `w ≥ 0`, `c(w, 1) = min(2w₂ + w₃, w₂ + 2w₃)` (`exercise_5_AA_1_cost`);
for `w ≫ 0`, `z(w, 1) = {(2, 1)}` if `w₂ < w₃`, `{(1, 2)}` if `w₂ > w₃`, and the segment
between them if `w₂ = w₃` (`exercise_5_AA_1_demand`). Where the demand is single-valued,
`∇_w c(w, 1) = z(w, 1)`, both by direct computation and by Shephard's lemma
(`exercise_5_AA_1_gradient`).
-/

namespace MWG.Production

open MWG.ClassicalDemand MWG.ConsumerChoice Filter Topology

/-- The elementary activities `a₁ = (1, -2, -1)` and `a₂ = (1, -1, -2)` of Figure 5.AA.4. -/
def aa1Acts : Fin 2 → Fin 3 → ℝ := ![![1, -2, -1], ![1, -1, -2]]

/-- **Figure 5.AA.4** (MWG, p. 159). The input requirement set for one unit of good 1:
`{z : (1, -z₂, -z₃) ∈ Y}`, with `Y` generated by `a₁, a₂` and the disposal activities. -/
def aa1Req : Set (Fin 2 → ℝ) := {z | ![1, -z 0, -z 1] ∈ coneOf (withDisposal aa1Acts)}

/-- The input requirement set of Figure 5.AA.4: `z ∈ V` iff `z ≥ α(2, 1) + β(1, 2)` for some
`α, β ≥ 0` with `α + β ≥ 1`. -/
theorem mem_aa1Req_iff (z : Fin 2 → ℝ) :
    z ∈ aa1Req ↔ ∃ α β : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 1 ≤ α + β ∧ 2 * α + β ≤ z 0 ∧ α + 2 * β ≤ z 1 := by
  constructor
  · rintro ⟨lam, hlam, heq⟩
    have h0 := congrFun heq 0
    have h1 := congrFun heq 1
    have h2 := congrFun heq 2
    simp [withDisposal, aa1Acts, Fintype.sum_sum_type, Fin.sum_univ_two,
      Pi.single_apply] at h0 h1 h2
    have l0 : 0 ≤ lam (Sum.inl 0) := hlam _
    have l1 : 0 ≤ lam (Sum.inl 1) := hlam _
    have l2 : 0 ≤ lam (Sum.inr 0) := hlam _
    have l3 : 0 ≤ lam (Sum.inr 1) := hlam _
    have l4 : 0 ≤ lam (Sum.inr 2) := hlam _
    exact ⟨lam (Sum.inl 0), lam (Sum.inl 1), l0, l1, by linarith, by linarith, by linarith⟩
  · rintro ⟨α, β, hα, hβ, h1, h2, h3⟩
    refine ⟨Sum.elim ![α, β] ![α + β - 1, z 0 - 2 * α - β, z 1 - α - 2 * β], ?_, ?_⟩
    · intro i
      rcases i with i | i <;> fin_cases i <;> simp <;> linarith
    · funext l
      fin_cases l <;>
        simp [withDisposal, aa1Acts, Fintype.sum_sum_type, Fin.sum_univ_two,
          Pi.single_apply] <;> ring

theorem aa1Req_nonneg : aa1Req ⊆ {z | 0 ≤ z} := by
  intro z hz
  obtain ⟨α, β, hα, hβ, _, h2, h3⟩ := (mem_aa1Req_iff z).mp hz
  intro i
  fin_cases i
  · change 0 ≤ z 0; linarith
  · change 0 ≤ z 1; linarith

theorem isClosed_aa1Req : IsClosed aa1Req := by
  have hc : Continuous fun z : Fin 2 → ℝ => (![1, -z 0, -z 1] : Fin 3 → ℝ) := by
    refine continuous_pi fun i => ?_
    fin_cases i
    · exact continuous_const
    · exact (continuous_apply 0).neg
    · exact (continuous_apply 1).neg
  exact (isClosed_coneOf _).preimage hc

theorem aa1_mem_21 : (![2, 1] : Fin 2 → ℝ) ∈ aa1Req :=
  (mem_aa1Req_iff _).mpr ⟨1, 0, by norm_num, le_rfl, by norm_num, by simp, by simp⟩

theorem aa1_mem_12 : (![1, 2] : Fin 2 → ℝ) ∈ aa1Req :=
  (mem_aa1Req_iff _).mpr ⟨0, 1, le_rfl, by norm_num, by norm_num, by simp, by simp⟩

theorem aa1_dot (w z : Fin 2 → ℝ) : w ⬝ᵥ z = w 0 * z 0 + w 1 * z 1 := by
  simp [dotProduct, Fin.sum_univ_two]

/-- For `w ≥ 0` and `z ∈ V`, `w·z ≥ min(2w₂ + w₃, w₂ + 2w₃)`. -/
theorem aa1_lower {w z : Fin 2 → ℝ} (hw : 0 ≤ w) (hz : z ∈ aa1Req) :
    min (2 * w 0 + w 1) (w 0 + 2 * w 1) ≤ w ⬝ᵥ z := by
  obtain ⟨α, β, hα, hβ, h1, h2, h3⟩ := (mem_aa1Req_iff z).mp hz
  have hw0 : 0 ≤ w 0 := hw 0
  have hw1 : 0 ≤ w 1 := hw 1
  have hm1 := min_le_left (2 * w 0 + w 1) (w 0 + 2 * w 1)
  have hm2 := min_le_right (2 * w 0 + w 1) (w 0 + 2 * w 1)
  have hm0 : 0 ≤ min (2 * w 0 + w 1) (w 0 + 2 * w 1) := le_min (by linarith) (by linarith)
  rw [aa1_dot]
  nlinarith [mul_le_mul_of_nonneg_left h2 hw0, mul_le_mul_of_nonneg_left h3 hw1,
    mul_le_mul_of_nonneg_left hm1 hα, mul_le_mul_of_nonneg_left hm2 hβ,
    mul_le_mul_of_nonneg_right h1 hm0]

/-- **Exercise 5.AA.1** (MWG, p. 164), the cost function: for `w ≥ 0`,
`c(w, 1) = min(2w₂ + w₃, w₂ + 2w₃)`. -/
theorem exercise_5_AA_1_cost {w : Fin 2 → ℝ} (hw : 0 ≤ w) :
    supportFn aa1Req w = min (2 * w 0 + w 1) (w 0 + 2 * w 1) := by
  apply IsLeast.csInf_eq
  refine ⟨?_, by rintro _ ⟨z, hz, rfl⟩; exact aa1_lower hw hz⟩
  rcases le_total (2 * w 0 + w 1) (w 0 + 2 * w 1) with h | h
  · exact ⟨![2, 1], aa1_mem_21, by change w ⬝ᵥ _ = _; rw [aa1_dot, min_eq_left h]; simp; ring⟩
  · exact ⟨![1, 2], aa1_mem_12, by change w ⬝ᵥ _ = _; rw [aa1_dot, min_eq_right h]; simp; ring⟩

/-- **Exercise 5.AA.1** (MWG, p. 164), the input demand: for `w ≫ 0`, `z(w, 1) = {(2, 1)}` if
`w₂ < w₃` (only `a₁` is used), `{(1, 2)}` if `w₂ > w₃` (only `a₂`), and the segment
`{z : z₂ + z₃ = 3, 1 ≤ z₂ ≤ 2}` (any mix of `a₁` and `a₂`) if `w₂ = w₃`. -/
theorem exercise_5_AA_1_demand {w : Fin 2 → ℝ} (hw : StrictlyPositive w) :
    (w 0 < w 1 → supportArgmin aa1Req w = {![2, 1]}) ∧
      (w 1 < w 0 → supportArgmin aa1Req w = {![1, 2]}) ∧
      (w 0 = w 1 → supportArgmin aa1Req w = {z | z 0 + z 1 = 3 ∧ 1 ≤ z 0 ∧ z 0 ≤ 2}) := by
  have hw0 := hw 0
  have hw1 := hw 1
  have hwn : 0 ≤ w := fun i => (hw i).le
  -- membership in the argmin: in `V` and cost at most the minimum
  have hmem : ∀ z, z ∈ supportArgmin aa1Req w ↔
      z ∈ aa1Req ∧ w ⬝ᵥ z ≤ min (2 * w 0 + w 1) (w 0 + 2 * w 1) := by
    intro z
    constructor
    · rintro ⟨hz, hle⟩
      refine ⟨hz, ?_⟩
      rcases le_total (2 * w 0 + w 1) (w 0 + 2 * w 1) with h | h
      · have := hle _ aa1_mem_21
        rw [min_eq_left h]; rw [aa1_dot, aa1_dot] at this; rw [aa1_dot]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this; linarith
      · have := hle _ aa1_mem_12
        rw [min_eq_right h]; rw [aa1_dot, aa1_dot] at this; rw [aa1_dot]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this; linarith
    · rintro ⟨hz, hle⟩
      exact ⟨hz, fun y hy => hle.trans (aa1_lower hwn hy)⟩
  refine ⟨fun hlt => ?_, fun hlt => ?_, fun heq => ?_⟩
  · ext z
    rw [hmem, Set.mem_singleton_iff, min_eq_left (by linarith)]
    constructor
    · rintro ⟨hz, hle⟩
      obtain ⟨α, β, hα, hβ, h1, h2, h3⟩ := (mem_aa1Req_iff z).mp hz
      rw [aa1_dot] at hle
      have t1 : 0 ≤ (α + β - 1) * (2 * w 0 + w 1) := mul_nonneg (by linarith) (by linarith)
      have t2 : 0 ≤ β * (w 1 - w 0) := mul_nonneg hβ (by linarith)
      have t3 : 0 ≤ w 0 * (z 0 - 2 * α - β) := mul_nonneg hw0.le (by linarith)
      have t4 : 0 ≤ w 1 * (z 1 - α - 2 * β) := mul_nonneg hw1.le (by linarith)
      have hsum : (α + β - 1) * (2 * w 0 + w 1) + β * (w 1 - w 0) + w 0 * (z 0 - 2 * α - β) +
          w 1 * (z 1 - α - 2 * β) ≤ 0 := by nlinarith
      have e2 : β * (w 1 - w 0) = 0 := by linarith
      have hb0 : β = 0 := by
        rcases mul_eq_zero.mp e2 with h | h
        · exact h
        · exact absurd h (by linarith)
      have e1 : (α + β - 1) * (2 * w 0 + w 1) = 0 := by linarith
      have ha1 : α = 1 := by
        rcases mul_eq_zero.mp e1 with h | h
        · linarith
        · exact absurd h (by linarith)
      have e3 : w 0 * (z 0 - 2 * α - β) = 0 := by linarith
      have e4 : w 1 * (z 1 - α - 2 * β) = 0 := by linarith
      have hz0 : z 0 = 2 := by
        rcases mul_eq_zero.mp e3 with h | h
        · exact absurd h hw0.ne'
        · rw [ha1, hb0] at h; linarith
      have hz1 : z 1 = 1 := by
        rcases mul_eq_zero.mp e4 with h | h
        · exact absurd h hw1.ne'
        · rw [ha1, hb0] at h; linarith
      funext i
      fin_cases i <;> simp [hz0, hz1]
    · rintro rfl
      exact ⟨aa1_mem_21, by rw [aa1_dot]; simp; linarith⟩
  · ext z
    rw [hmem, Set.mem_singleton_iff, min_eq_right (by linarith)]
    constructor
    · rintro ⟨hz, hle⟩
      obtain ⟨α, β, hα, hβ, h1, h2, h3⟩ := (mem_aa1Req_iff z).mp hz
      rw [aa1_dot] at hle
      have t1 : 0 ≤ (α + β - 1) * (w 0 + 2 * w 1) := mul_nonneg (by linarith) (by linarith)
      have t2 : 0 ≤ α * (w 0 - w 1) := mul_nonneg hα (by linarith)
      have t3 : 0 ≤ w 0 * (z 0 - 2 * α - β) := mul_nonneg hw0.le (by linarith)
      have t4 : 0 ≤ w 1 * (z 1 - α - 2 * β) := mul_nonneg hw1.le (by linarith)
      have hsum : (α + β - 1) * (w 0 + 2 * w 1) + α * (w 0 - w 1) + w 0 * (z 0 - 2 * α - β) +
          w 1 * (z 1 - α - 2 * β) ≤ 0 := by nlinarith
      have e2 : α * (w 0 - w 1) = 0 := by linarith
      have ha0 : α = 0 := by
        rcases mul_eq_zero.mp e2 with h | h
        · exact h
        · exact absurd h (by linarith)
      have e1 : (α + β - 1) * (w 0 + 2 * w 1) = 0 := by linarith
      have hb1 : β = 1 := by
        rcases mul_eq_zero.mp e1 with h | h
        · linarith
        · exact absurd h (by linarith)
      have e3 : w 0 * (z 0 - 2 * α - β) = 0 := by linarith
      have e4 : w 1 * (z 1 - α - 2 * β) = 0 := by linarith
      have hz0 : z 0 = 1 := by
        rcases mul_eq_zero.mp e3 with h | h
        · exact absurd h hw0.ne'
        · rw [ha0, hb1] at h; linarith
      have hz1 : z 1 = 2 := by
        rcases mul_eq_zero.mp e4 with h | h
        · exact absurd h hw1.ne'
        · rw [ha0, hb1] at h; linarith
      funext i
      fin_cases i <;> simp [hz0, hz1]
    · rintro rfl
      exact ⟨aa1_mem_12, by rw [aa1_dot]; simp; linarith⟩
  · ext z
    rw [hmem, min_eq_left (by linarith)]
    constructor
    · rintro ⟨hz, hle⟩
      obtain ⟨α, β, hα, hβ, h1, h2, h3⟩ := (mem_aa1Req_iff z).mp hz
      rw [aa1_dot, ← heq] at hle
      have hs : z 0 + z 1 ≤ 3 := by nlinarith
      refine ⟨by linarith, by linarith, by linarith⟩
    · rintro ⟨hs, h1, h2⟩
      refine ⟨(mem_aa1Req_iff z).mpr ⟨z 0 - 1, 2 - z 0, by linarith, by linarith, by linarith,
        by linarith, by linarith⟩, ?_⟩
      rw [aa1_dot, ← heq]
      nlinarith

/-- **Exercise 5.AA.1** (MWG, p. 164), `z(w, 1) = ∇_w c(w, 1)` wherever `z(w, 1)` is
single-valued (`w ≫ 0`, `w₂ ≠ w₃`). With `zs = (2, 1)` for `w₂ < w₃` and `(1, 2)` for
`w₂ > w₃`, `c(·, 1)` coincides near `w` with the linear function `w' ↦ w'·zs`, so it is
differentiable at `w` with gradient `zs` (direct verification); Shephard's lemma
(`vcost_shephard`) gives the same derivative. -/
theorem exercise_5_AA_1_gradient {w : Fin 2 → ℝ} (hw : StrictlyPositive w) (hne : w 0 ≠ w 1) :
    ∃ zs : Fin 2 → ℝ, supportArgmin aa1Req w = {zs} ∧
      HasFDerivAt (supportFn aa1Req) (dualityDotCLM zs) w ∧
      (∀ᶠ w' in 𝓝 w, supportFn aa1Req w' = zs ⬝ᵥ w') := by
  have hw0 := hw 0
  have hw1 := hw 1
  have hopen : ∀ (r : (Fin 2 → ℝ) → Prop), IsOpen {w' | r w'} → r w → ∀ᶠ w' in 𝓝 w, r w' :=
    fun r ho hr => ho.mem_nhds hr
  have hc0 : Continuous fun w' : Fin 2 → ℝ => w' 0 := continuous_apply 0
  have hc1 : Continuous fun w' : Fin 2 → ℝ => w' 1 := continuous_apply 1
  have hpos : ∀ᶠ w' in 𝓝 w, 0 < w' 0 ∧ 0 < w' 1 :=
    hopen _ ((isOpen_lt continuous_const hc0).inter (isOpen_lt continuous_const hc1)) ⟨hw0, hw1⟩
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · refine ⟨![2, 1], (exercise_5_AA_1_demand hw).1 hlt, ?_, ?_⟩
    · exact vcost_shephard isClosed_aa1Req aa1Req_nonneg hw ((exercise_5_AA_1_demand hw).1 hlt)
    · filter_upwards [hpos, hopen _ (isOpen_lt hc0 hc1) hlt] with w' hp hl
      have hw' : 0 ≤ w' := fun i => by fin_cases i <;> simp [hp.1.le, hp.2.le]
      rw [exercise_5_AA_1_cost hw', min_eq_left (by linarith), dotProduct_comm, aa1_dot]
      simp; ring
  · refine ⟨![1, 2], (exercise_5_AA_1_demand hw).2.1 hgt, ?_, ?_⟩
    · exact vcost_shephard isClosed_aa1Req aa1Req_nonneg hw
        ((exercise_5_AA_1_demand hw).2.1 hgt)
    · filter_upwards [hpos, hopen _ (isOpen_lt hc1 hc0) hgt] with w' hp hl
      have hw' : 0 ≤ w' := fun i => by fin_cases i <;> simp [hp.1.le, hp.2.le]
      rw [exercise_5_AA_1_cost hw', min_eq_right (by linarith), dotProduct_comm, aa1_dot]
      simp; ring

end MWG.Production

set_option linter.style.longLine false
#print axioms MWG.Production.NoFreeLunch
#print axioms MWG.Production.InactionPossible
#print axioms MWG.Production.FreeDisposal
#print axioms MWG.Production.Irreversible
#print axioms MWG.Production.NonincreasingReturns
#print axioms MWG.Production.NondecreasingReturns
#print axioms MWG.Production.ConstantReturns
#print axioms MWG.Production.Additive
#print axioms MWG.Production.IsConvexCone
#print axioms MWG.Production.noFreeLunch_iff
#print axioms MWG.Production.freeDisposal_iff
#print axioms MWG.Production.inaction_of_nonincreasingReturns
#print axioms MWG.Production.nonincreasingReturns_empty
#print axioms MWG.Production.constantReturns_iff
#print axioms MWG.Production.additive_nsmul
#print axioms MWG.Production.nonincreasingReturns_of_convex
#print axioms MWG.Production.isConvexCone_iff
#print axioms MWG.Production.proposition_5_B_1
#print axioms MWG.Production.extendVec
#print axioms MWG.Production.extendVec_smul
#print axioms MWG.Production.extendVec_add
#print axioms MWG.Production.extendVec_inj
#print axioms MWG.Production.proposition_5_B_2_general
#print axioms MWG.Production.proposition_5_B_2
#print axioms MWG.Production.example_5_B_1
#print axioms MWG.Production.IsTransformationFunction
#print axioms MWG.Production.partialAt
#print axioms MWG.Production.MRT
#print axioms MWG.Production.mrt_slope
#print axioms MWG.Production.isTransformationFunction_halfPlane
#print axioms MWG.Production.inputsOf
#print axioms MWG.Production.singleOutputSet
#print axioms MWG.Production.inputsOf_extendVec
#print axioms MWG.Production.mem_singleOutputSet
#print axioms MWG.Production.extendVec_inputsOf
#print axioms MWG.Production.partialF
#print axioms MWG.Production.MRTS
#print axioms MWG.Production.exercise_5_B_2
#print axioms MWG.Production.exercise_5_B_3
#print axioms MWG.Production.exercise_5_B_1
#print axioms MWG.Production.figure_5_B_8
#print axioms MWG.Production.profitFn
#print axioms MWG.Production.profit
#print axioms MWG.Production.supply
#print axioms MWG.Production.le_profitFn
#print axioms MWG.Production.profitFn_le
#print axioms MWG.Production.profitFn_eq_coe
#print axioms MWG.Production.profitFn_eq_top
#print axioms MWG.Production.profitFn_lt_top_iff
#print axioms MWG.Production.profit_eq_of_mem_supply
#print axioms MWG.Production.profitFn_eq_of_mem_supply
#print axioms MWG.Production.mem_supply_iff
#print axioms MWG.Production.profit_eq_neg_supportFn
#print axioms MWG.Production.supply_eq_neg_supportArgmin
#print axioms MWG.Production.bddAbove_iff_bddBelow_neg
#print axioms MWG.Production.oneForOneTech
#print axioms MWG.Production.example_5_C_profit_oneForOne
#print axioms MWG.Production.exercise_5_C_1
#print axioms MWG.Production.proposition_5_C_1_i
#print axioms MWG.Production.proposition_5_C_1_ii
#print axioms MWG.Production.exercise_5_C_2
#print axioms MWG.Production.proposition_5_C_1_ii_real
#print axioms MWG.Production.nonneg_of_bdd_freeDisposal
#print axioms MWG.Production.proposition_5_C_1_iii_nonneg
#print axioms MWG.Production.proposition_5_C_1_iii
#print axioms MWG.Production.proposition_5_C_1_iii_counterexample
#print axioms MWG.Production.proposition_5_C_1_iv
#print axioms MWG.Production.proposition_5_C_1_v_convex
#print axioms MWG.Production.proposition_5_C_1_v_strict
#print axioms MWG.Production.proposition_5_C_1_vi
#print axioms MWG.Production.hotellingCounterexampleSet
#print axioms MWG.Production.proposition_5_C_1_vi_nonconvex_counterexample
#print axioms MWG.Production.law_of_supply
#print axioms MWG.Production.proposition_5_C_1_vii_psd
#print axioms MWG.Production.proposition_5_C_1_vii_euler
#print axioms MWG.Production.proposition_5_C_1_vii
#print axioms MWG.Production.eventually_lt_of_hasDerivAt_neg
#print axioms MWG.Production.exists_dir_of_not_nonneg_multiple
#print axioms MWG.Production.foc_5_C_1
#print axioms MWG.Production.foc_5_C_1_ratio
#print axioms MWG.Production.foc_5_C_1_sufficient
#print axioms MWG.Production.cubeTransformation
#print axioms MWG.Production.foc_5_C_1_needs_cq
#print axioms MWG.Production.foc_5_C_2
#print axioms MWG.Production.foc_5_C_2_mrts
#print axioms MWG.Production.concave_le_tangent
#print axioms MWG.Production.foc_5_C_2_sufficient
#print axioms MWG.Production.inputReq
#print axioms MWG.Production.costFn
#print axioms MWG.Production.costFnE
#print axioms MWG.Production.condDemand
#print axioms MWG.Production.inputReq_subset_nonneg
#print axioms MWG.Production.dot_nonneg_of_nonneg
#print axioms MWG.Production.bddBelow_of_subset_nonneg
#print axioms MWG.Production.vcost_smul
#print axioms MWG.Production.vcost_mono
#print axioms MWG.Production.vcost_concaveOn
#print axioms MWG.Production.vcost_iii
#print axioms MWG.Production.vdemand_smul
#print axioms MWG.Production.vdemand_convex
#print axioms MWG.Production.vdemand_strict
#print axioms MWG.Production.supportFn_hasFDerivAt_of_compact
#print axioms MWG.Production.vcost_shephard
#print axioms MWG.Production.vdemand_law
#print axioms MWG.Production.vdemand_derivative
#print axioms MWG.Production.proposition_5_C_2_i_hom
#print axioms MWG.Production.proposition_5_C_2_i_mono
#print axioms MWG.Production.proposition_5_C_2_ii
#print axioms MWG.Production.continuous_extendVec_neg
#print axioms MWG.Production.inputReq_eq_section
#print axioms MWG.Production.isClosed_inputReq
#print axioms MWG.Production.upward_inputReq
#print axioms MWG.Production.proposition_5_C_2_iii
#print axioms MWG.Production.proposition_5_C_2_iv
#print axioms MWG.Production.proposition_5_C_2_v_convex
#print axioms MWG.Production.proposition_5_C_2_v_strict
#print axioms MWG.Production.proposition_5_C_2_vi
#print axioms MWG.Production.proposition_5_C_2_vii
#print axioms MWG.Production.inputReq_smul
#print axioms MWG.Production.proposition_5_C_2_viii
#print axioms MWG.Production.proposition_5_C_2_ix
#print axioms MWG.Production.exercise_5_C_5_i
#print axioms MWG.Production.exercise_5_C_5_ii
#print axioms MWG.Production.quasiconcave_grad_nonneg
#print axioms MWG.Production.foc_5_C_4_sufficient
#print axioms MWG.Production.cost_lambda_subgradient
#print axioms MWG.Production.lambda_eq_marginal_cost
#print axioms MWG.Production.footnote_5_C_9
#print axioms MWG.Production.convex_tangent_le
#print axioms MWG.Production.foc_5_C_6
#print axioms MWG.Production.foc_5_C_6_sufficient
#print axioms MWG.Production.inputReqMulti
#print axioms MWG.Production.costMulti
#print axioms MWG.Production.condDemandMulti
#print axioms MWG.Production.inputReqMulti_subset
#print axioms MWG.Production.exercise_5_C_4_i
#print axioms MWG.Production.exercise_5_C_4_ii
#print axioms MWG.Production.exercise_5_C_4_iii
#print axioms MWG.Production.exercise_5_C_4_iv
#print axioms MWG.Production.exercise_5_C_4_v
#print axioms MWG.Production.exercise_5_C_4_vi
#print axioms MWG.Production.exercise_5_C_4_vii
#print axioms MWG.Production.aggSet
#print axioms MWG.Production.aggSupply
#print axioms MWG.Production.dotProduct_finset_sum
#print axioms MWG.Production.proposition_5_E_1_ii
#print axioms MWG.Production.proposition_5_E_1_i_real
#print axioms MWG.Production.ereal_coe_sum
#print axioms MWG.Production.ereal_sum_ne_bot
#print axioms MWG.Production.ereal_sum_eq_top
#print axioms MWG.Production.profitFn_ne_bot
#print axioms MWG.Production.proposition_5_E_1_i
#print axioms MWG.Production.aggregate_law_of_supply
#print axioms MWG.Production.sum_symm_psd
#print axioms MWG.Production.profit_fderiv_eq_of_mem_supply
#print axioms MWG.Production.exercise_5_E_1
#print axioms MWG.Production.aggSet_convex_freeDisposal
#print axioms MWG.Production.exercise_5_E_3
#print axioms MWG.Production.exercise_5_E_3_pos
#print axioms MWG.Production.exercise_5_E_3_counterexample
#print axioms MWG.Production.Efficient
#print axioms MWG.Production.WeaklyEfficient
#print axioms MWG.Production.Efficient.weaklyEfficient
#print axioms MWG.Production.efficient_mem_frontier
#print axioms MWG.Production.frontier_not_efficient
#print axioms MWG.Production.proposition_5_F_1
#print axioms MWG.Production.exercise_5_F_1
#print axioms MWG.Production.proposition_5_F_2_weak
#print axioms MWG.Production.proposition_5_F_2
#print axioms MWG.Production.proposition_5_F_2_needs_dimension
#print axioms MWG.Production.figure5F4Set
#print axioms MWG.Production.figure_5_F_4
#print axioms MWG.Production.efficient_single_output_concave
#print axioms MWG.Production.coneOf
#print axioms MWG.Production.zero_mem_coneOf
#print axioms MWG.Production.generator_mem_coneOf
#print axioms MWG.Production.convex_coneOf
#print axioms MWG.Production.smul_mem_coneOf
#print axioms MWG.Production.add_mem_coneOf
#print axioms MWG.Production.SupportedOn
#print axioms MWG.Production.IndepOn
#print axioms MWG.Production.coneOf_caratheodory
#print axioms MWG.Production.suppSub
#print axioms MWG.Production.comboOn
#print axioms MWG.Production.isClosed_coneOf
#print axioms MWG.Production.cone_sep_nonneg
#print axioms MWG.Production.farkas
#print axioms MWG.Production.exists_pos_of_cone_inter_nonneg
#print axioms MWG.Production.primalFeasible
#print axioms MWG.Production.dualFeasible
#print axioms MWG.Production.equation_M_M_3
#print axioms MWG.Production.theorem_M_M_1
#print axioms MWG.Production.equation_M_M_4
#print axioms MWG.Production.theorem_M_M_1_proof_counterexample
#print axioms MWG.Production.footnote_M_M_30
#print axioms MWG.Production.example_M_M_figures
#print axioms MWG.Production.withDisposal
#print axioms MWG.Production.activity_convexCone
#print axioms MWG.Production.activity_profit
#print axioms MWG.Production.activity_supply_nonempty_iff
#print axioms MWG.Production.disposal_supply_nonempty_iff
#print axioms MWG.Production.activity_level_zero
#print axioms MWG.Production.activity_supply_eq
#print axioms MWG.Production.linear_activity_efficient_pos_price
#print axioms MWG.Production.leontiefSet
#print axioms MWG.Production.Productive
#print axioms MWG.Production.leontiefMatrix
#print axioms MWG.Production.primaryReq
#print axioms MWG.Production.leontief_from_activities
#print axioms MWG.Production.leontiefSet_eq_coneOf
#print axioms MWG.Production.proposition_5_AA_1_neumann
#print axioms MWG.Production.proposition_5_AA_1
#print axioms MWG.Production.producible_iff_neumann_bounded
#print axioms MWG.Production.example_5_AA_1
#print axioms MWG.Production.lp_dual_supergradient
#print axioms MWG.Production.lp_dual_marginal_products
#print axioms MWG.Production.gensWithDisposal
#print axioms MWG.Production.sum_gensWithDisposal
#print axioms MWG.Production.proposition_5_AA_2
#print axioms MWG.Production.outputSupply
#print axioms MWG.Production.supply_nonconvex
#print axioms MWG.Production.exercise_5_D_1
#print axioms MWG.Production.exercise_5_D_1_onesided
#print axioms MWG.Production.exercise_5_D_1_kink
#print axioms MWG.Production.figure_5_D_5
#print axioms MWG.Production.sunk_cost_supply
#print axioms MWG.Production.sunk_cost_covers_variable
#print axioms MWG.Production.sunk_cost_strict_fails
#print axioms MWG.Production.exercise_5_D_2
#print axioms MWG.Production.shortRunReq
#print axioms MWG.Production.shortRun_ge_longRun
#print axioms MWG.Production.shortRun_eq_longRun
#print axioms MWG.Production.longRun_lower_envelope
#print axioms MWG.Production.shortRun_marginal_eq
#print axioms MWG.Production.ownerBudget
#print axioms MWG.Production.unanimity_budget
#print axioms MWG.Production.unanimity_value
#print axioms MWG.Production.unanimity_strict
#print axioms MWG.Production.unanimity_profit_max
#print axioms MWG.Production.price_dependence_example
#print axioms MWG.Production.exercise_5_G_1a
#print axioms MWG.Production.exercise_5_G_1b
#print axioms MWG.Production.exercise_5_G_1c
#print axioms MWG.Production.exercise_5_G_1c_not_profit
#print axioms MWG.Production.cdProd
#print axioms MWG.Production.cdProd_differentiableAt
#print axioms MWG.Production.cdProd_partial
#print axioms MWG.Production.example_5_B_2
#print axioms MWG.Production.example_5_B_3_hom
#print axioms MWG.Production.example_5_B_3
#print axioms MWG.Production.cdTheta
#print axioms MWG.Production.cdPhi
#print axioms MWG.Production.cd_inputReq_eq
#print axioms MWG.Production.cdTheta_eq
#print axioms MWG.Production.example_5_C_1_cost
#print axioms MWG.Production.example_5_C_1_supply
#print axioms MWG.Production.example_5_C_1_printed_supply_counterexample
#print axioms MWG.Production.example_5_C_1_crs
#print axioms MWG.Production.example_5_C_1_irs
#print axioms MWG.Production.example_5_C_1_doubling
#print axioms MWG.Production.addClosure
#print axioms MWG.Production.exercise_5_B_4_closure
#print axioms MWG.Production.sqrtTech
#print axioms MWG.Production.exercise_5_B_4_not_closed
#print axioms MWG.Production.exercise_5_B_5
#print axioms MWG.Production.twoTechSet
#print axioms MWG.Production.exercise_5_B_6b
#print axioms MWG.Production.exercise_5_B_6c
#print axioms MWG.Production.exercise_5_B_6d_aux
#print axioms MWG.Production.exercise_5_B_6d
#print axioms MWG.Production.foc_5_C_4
#print axioms MWG.Production.foc_5_C_4_needs_cq
#print axioms MWG.Production.exercise_5_C_6_ab
#print axioms MWG.Production.exercise_5_C_6_c
#print axioms MWG.Production.exercise_5_C_7_corrected
#print axioms MWG.Production.exercise_5_C_7_counterexample
#print axioms MWG.Production.exercise_5_C_8
#print axioms MWG.Production.exercise_5_C_10a
#print axioms MWG.Production.exercise_5_C_10b
#print axioms MWG.Production.exercise_5_C_10c
#print axioms MWG.Production.exercise_5_C_9a
#print axioms MWG.Production.exercise_5_C_9b
#print axioms MWG.Production.exercise_5_C_11
#print axioms MWG.Production.exercise_5_C_12
#print axioms MWG.Production.exercise_5_C_13
#print axioms MWG.Production.leontief_inverse_facts
#print axioms MWG.Production.exercise_5_AA_2a
#print axioms MWG.Production.exercise_5_AA_2b
#print axioms MWG.Production.exercise_5_AA_2c
#print axioms MWG.Production.exercise_5_AA_2d
#print axioms MWG.Production.exercise_5_AA_3
#print axioms MWG.Production.exercise_5_AA_3e
#print axioms MWG.Production.aa4
#print axioms MWG.Production.aa4_coords
#print axioms MWG.Production.exercise_5_AA_4a
#print axioms MWG.Production.exercise_5_AA_4bc
#print axioms MWG.Production.aa5
#print axioms MWG.Production.freeDisposal_withDisposal
#print axioms MWG.Production.aa5_dot
#print axioms MWG.Production.exercise_5_AA_5abc
#print axioms MWG.Production.exercise_5_AA_5d
#print axioms MWG.Production.exercise_5_AA_5d_correction
#print axioms MWG.Production.exercise_5_AA_5e
#print axioms MWG.Production.aa5_mem_supply_of_price
#print axioms MWG.Production.aa5_two_mem
#print axioms MWG.Production.exercise_5_AA_5f
#print axioms MWG.Production.exercise_5_AA_5gh
#print axioms MWG.Production.exercise_5_D_4a
#print axioms MWG.Production.exercise_5_D_5b
#print axioms MWG.Production.exercise_5_D_5c
#print axioms MWG.Production.exercise_5_E_5a
#print axioms MWG.Production.exercise_5_E_5b
#print axioms MWG.Production.exercise_5_E_5c
#print axioms MWG.Production.supply_cyclic
#print axioms MWG.Production.deriv_cyclic
#print axioms MWG.Production.sum_range_cast_id
#print axioms MWG.Production.thinCycle
#print axioms MWG.Production.thinCycle_bound
#print axioms MWG.Production.cyclic_symm
#print axioms MWG.Production.proposition_5_C_1_vii_symm
#print axioms MWG.Production.abs_dotProduct_le_norm
#print axioms MWG.Production.hotelling_of_continuousAt
#print axioms MWG.Production.supply_continuousAt_of_single
#print axioms MWG.Production.proposition_5_C_1_vii_general
#print axioms MWG.Production.ssY
#print axioms MWG.Production.ssSupply
#print axioms MWG.Production.ssSupply_mem_supply
#print axioms MWG.Production.proposition_5_C_1_vii_symm_instance
#print axioms MWG.Production.ss_supply_eq
#print axioms MWG.Production.proposition_5_C_1_vii_general_instance
#print axioms MWG.Production.b4_sum_mem_addClosure
#print axioms MWG.Production.b4_normal_form
#print axioms MWG.Production.exercise_5_B_4_closed
#print axioms MWG.Production.sTech
#print axioms MWG.Production.exercise_5_B_4_closed_instance
#print axioms MWG.Production.negDef_offdiag_pos_solution_pos
#print axioms MWG.Production.exercise_5_C_7_corrected_n
#print axioms MWG.Production.c7H3
#print axioms MWG.Production.exercise_5_C_7_corrected_n_instance
#print axioms MWG.Production.c7f
#print axioms MWG.Production.c7u
#print axioms MWG.Production.c7v
#print axioms MWG.Production.c7demand
#print axioms MWG.Production.c7f_technology
#print axioms MWG.Production.c7_foc
#print axioms MWG.Production.exercise_5_C_7_demand
#print axioms MWG.Production.exercise_5_C_7_explicit_counterexample
#print axioms MWG.Production.hotelling_1d
#print axioms MWG.Production.second_order_nonneg
#print axioms MWG.Production.exercise_5_D_3
#print axioms MWG.Production.exercise_5_D_3_instance
#print axioms MWG.Production.exercise_5_D_3_equal
#print axioms MWG.Production.Subadditive
#print axioms MWG.Production.DecreasingRayAC
#print axioms MWG.Production.cost4b
#print axioms MWG.Production.exercise_5_D_4b
#print axioms MWG.Production.exercise_5_D_4c
#print axioms MWG.Production.exercise_5_D_4c_instance
#print axioms MWG.Production.exercise_5_D_5a_average
#print axioms MWG.Production.prod5a
#print axioms MWG.Production.exercise_5_D_5a_marginal
#print axioms MWG.Production.exercise_5_E_4a
#print axioms MWG.Production.e4_pow_integral
#print axioms MWG.Production.e4_step_integral
#print axioms MWG.Production.e4AggProfit
#print axioms MWG.Production.exercise_5_E_4b
#print axioms MWG.Production.e4AggDemand
#print axioms MWG.Production.e4AggDemand_eq
#print axioms MWG.Production.exercise_5_E_4c
#print axioms MWG.Production.e4Prod
#print axioms MWG.Production.exercise_5_E_4d
#print axioms MWG.Production.aa1Acts
#print axioms MWG.Production.aa1Req
#print axioms MWG.Production.mem_aa1Req_iff
#print axioms MWG.Production.aa1Req_nonneg
#print axioms MWG.Production.isClosed_aa1Req
#print axioms MWG.Production.aa1_mem_21
#print axioms MWG.Production.aa1_mem_12
#print axioms MWG.Production.aa1_dot
#print axioms MWG.Production.aa1_lower
#print axioms MWG.Production.exercise_5_AA_1_cost
#print axioms MWG.Production.exercise_5_AA_1_demand
#print axioms MWG.Production.exercise_5_AA_1_gradient
