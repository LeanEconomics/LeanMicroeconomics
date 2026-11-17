/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Data.Matrix.Mul
import Mathlib.Topology.Algebra.Module.FiniteDimension

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
