/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGGeneralEquilibriumExamples.Tools
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Function

/-!
# Factor markets with fixed output prices (MWG Section 15.D, pp. 529-532)

Firms `j : κ` produce good `j` from `L` primary factors with production functions `fⱼ` on `ℝ^L₊`;
output prices `p` are fixed (a small open economy) and the factor endowment is `z̄`.

* p. 530: profit maximization `max pⱼ fⱼ(zⱼ) - w·zⱼ` (`IsOptimalInput`) and the factor market
  equilibrium (`IsFactorEqm`: `w ≫ 0`, optimal inputs, `∑ⱼ zⱼ = z̄`).
* (15.D.1)-(15.D.2): with concave production functions, differentiable at an interior allocation,
  an allocation with `w ≫ 0` is an equilibrium if and only if `pⱼ ∂fⱼ/∂z_{ℓj} = w_ℓ` and the factor
  markets clear (`factorEqm_iff_foc`).
* (15.D.5)-(15.D.6), p. 531: the equilibrium allocation maximizes the economy's revenue
  `∑ pⱼ fⱼ(zⱼ)` subject to `∑ zⱼ = z̄` (`factorEqm_revenue_max`).
* p. 532: the equilibrium factor prices are a supergradient of the aggregate revenue function
  (`factorEqm_supergradient`); hence an increase in the endowment of one factor cannot raise its
  equilibrium price (`factor_price_endowment_opposite`).
* **Exercise 15.D.2** (in general form): with concave production functions the production
  possibility set is convex (`exercise_15_D_2`).
-/

namespace MWG.GeneralEquilibriumExamples

open MWG.ConsumerChoice Filter Topology

variable {κ : Type*} [Fintype κ] {L : ℕ}

/-- **Section 15.D** (MWG, p. 530). Firm `j`'s profit maximization at output prices `p` and factor
prices `w`: `zⱼ ∈ ℝ^L₊` maximizes `pⱼ fⱼ(z) - w·z`. -/
def IsOptimalInput (f : κ → (Fin L → ℝ) → ℝ) (p : κ → ℝ) (w : Fin L → ℝ) (j : κ)
    (z : Fin L → ℝ) : Prop :=
  z ∈ nonnegOrthant L ∧ ∀ z' ∈ nonnegOrthant L, p j * f j z' - w ⬝ᵥ z' ≤ p j * f j z - w ⬝ᵥ z

/-- **Section 15.D** (MWG, p. 530). An equilibrium of the factor markets given output prices `p`:
factor prices `w ≫ 0` and an allocation `(z₁, …, z_J)` with every `zⱼ` profit maximizing and
`∑ⱼ zⱼ = z̄`. -/
def IsFactorEqm (f : κ → (Fin L → ℝ) → ℝ) (p : κ → ℝ) (zbar : Fin L → ℝ) (w : Fin L → ℝ)
    (z : κ → Fin L → ℝ) : Prop :=
  StrictlyPositive w ∧ (∀ j, IsOptimalInput f p w j (z j)) ∧ ∑ j, z j = zbar

/-- The tangent hyperplane of a concave function lies above it: if `f` is concave on the convex set
`S` and has derivative `f'` at `x ∈ S`, then `f y ≤ f x + f'(y - x)` for `y ∈ S`. -/
theorem concave_le_fderiv {S : Set (Fin L → ℝ)} {f : (Fin L → ℝ) → ℝ}
    {f' : (Fin L → ℝ) →L[ℝ] ℝ} {x y : Fin L → ℝ} (hfc : ConcaveOn ℝ S f) (hx : x ∈ S)
    (hy : y ∈ S) (hf : HasFDerivAt f f' x) : f y ≤ f x + f' (y - x) := by
  set g : ℝ → ℝ := fun t => f (x + t • (y - x)) with hg
  have hgc : ConcaveOn ℝ (Set.Icc 0 1) g := by
    have h := hfc.comp_affineMap (AffineMap.lineMap x y)
    refine h.subset (fun t ht => ?_) (convex_Icc 0 1) |>.congr fun t _ => ?_
    · simp only [Set.mem_preimage, AffineMap.lineMap_apply_module']
      have := hfc.1 hy hx ht.1 (by linarith [ht.2] : (0 : ℝ) ≤ 1 - t) (by ring)
      convert this using 1
      module
    · simp only [Function.comp_apply, AffineMap.lineMap_apply_module', hg]
      congr 1
      module
  have hline : HasDerivAt (fun t : ℝ => x + t • (y - x)) (y - x) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (y - x)).const_add x
  have hgd : HasDerivAt g (f' (y - x)) 0 := by
    have := HasFDerivAt.comp_hasDerivAt (0 : ℝ) (by simpa using hf) hline
    simpa [Function.comp_def, hg] using this
  have := concave_le_tangent hgc (Set.left_mem_Icc.2 zero_le_one)
    (Set.right_mem_Icc.2 zero_le_one) hgd
  simpa [hg] using this

/-- **(15.D.1)-(15.D.2)** (MWG, p. 530). Let the production functions be concave on `ℝ^L₊`, the
output prices nonnegative, `w ≫ 0`, and the allocation interior (`zⱼ ≫ 0`) with `fⱼ` differentiable
at `zⱼ`. Then `(w, z)` is a factor market equilibrium if and only if
`pⱼ ∂fⱼ(zⱼ)/∂z_{ℓj} = w_ℓ` for all `j, ℓ` (15.D.1) and `∑ⱼ zⱼ = z̄` (15.D.2): first-order
conditions are necessary and sufficient. -/
theorem factorEqm_iff_foc {f : κ → (Fin L → ℝ) → ℝ} {p : κ → ℝ} {zbar w : Fin L → ℝ}
    {z : κ → Fin L → ℝ} (hfc : ∀ j, ConcaveOn ℝ (nonnegOrthant L) (f j)) (hp : ∀ j, 0 ≤ p j)
    (hw : StrictlyPositive w) (hint : ∀ j l, 0 < z j l) {f' : κ → (Fin L → ℝ) →L[ℝ] ℝ}
    (hf : ∀ j, HasFDerivAt (f j) (f' j) (z j)) :
    IsFactorEqm f p zbar w z ↔
      (∀ j l, p j * f' j (Pi.single l 1) = w l) ∧ ∑ j, z j = zbar := by
  have hzm : ∀ j, z j ∈ nonnegOrthant L := fun j l => (hint j l).le
  -- the derivative of profit along a coordinate direction
  have hprof : ∀ j l, HasDerivAt (fun t : ℝ => p j * f j (z j + t • Pi.single l 1) -
      w ⬝ᵥ (z j + t • Pi.single l 1)) (p j * f' j (Pi.single l 1) - w l) 0 := by
    intro j l
    have hline : HasDerivAt (fun t : ℝ => z j + t • Pi.single l (1 : ℝ)) (Pi.single l 1) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single l (1 : ℝ))).const_add (z j)
    have h1 := (HasFDerivAt.comp_hasDerivAt (0 : ℝ) (by simpa using hf j) hline).const_mul (p j)
    have h2 : HasDerivAt (fun t : ℝ => w ⬝ᵥ (z j + t • Pi.single l 1)) (w l) 0 := by
      have : (fun t : ℝ => w ⬝ᵥ (z j + t • Pi.single l 1)) =
          fun t => w ⬝ᵥ z j + t * w l := by
        funext t
        simp [dotProduct_add, dotProduct_smul]
      rw [this]
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (w l)).const_add (w ⬝ᵥ z j)
    exact h1.sub h2
  constructor
  · rintro ⟨-, hopt, hsum⟩
    refine ⟨fun j l => ?_, hsum⟩
    -- an interior maximum: the derivative of profit vanishes
    have hmax : IsLocalMax (fun t : ℝ => p j * f j (z j + t • Pi.single l 1) -
        w ⬝ᵥ (z j + t • Pi.single l 1)) 0 := by
      have hev : ∀ᶠ t in 𝓝 (0 : ℝ), z j + t • Pi.single l 1 ∈ nonnegOrthant L := by
        have hc : Continuous fun t : ℝ => z j + t • Pi.single l (1 : ℝ) := by fun_prop
        have hopen : IsOpen (⋂ k, {v : Fin L → ℝ | 0 < v k}) :=
          isOpen_iInter_of_finite fun k => isOpen_lt continuous_const (continuous_apply k)
        have hmem : z j + (0 : ℝ) • Pi.single l (1 : ℝ) ∈ ⋂ k, {v : Fin L → ℝ | 0 < v k} := by
          rw [zero_smul, add_zero, Set.mem_iInter]
          exact hint j
        have := hc.continuousAt.eventually (hopen.mem_nhds hmem)
        filter_upwards [this] with t ht k
        exact (Set.mem_iInter.1 ht k).le
      filter_upwards [hev] with t ht
      have := (hopt j).2 _ ht
      simpa using this
    have := hmax.hasDerivAt_eq_zero (hprof j l)
    linarith
  · rintro ⟨hfoc, hsum⟩
    refine ⟨hw, fun j => ⟨hzm j, fun z' hz' => ?_⟩, hsum⟩
    have htan := concave_le_fderiv (hfc j) (hzm j) hz' (hf j)
    -- `pⱼ f'ⱼ(v) = w·v` for every direction `v`
    have hlin : ∀ v, p j * f' j v = w ⬝ᵥ v := by
      intro v
      have := LinearMap.pi_apply_eq_sum_univ (f' j).toLinearMap v
      simp only [ContinuousLinearMap.coe_coe, smul_eq_mul] at this
      rw [this, Finset.mul_sum, dotProduct]
      refine Finset.sum_congr rfl fun l _ => ?_
      have he : (fun k => if l = k then (1 : ℝ) else 0) = Pi.single l 1 := by
        funext k
        simp [Pi.single_apply, eq_comm]
      rw [he, ← hfoc j l]
      ring
    have h1 := mul_le_mul_of_nonneg_left htan (hp j)
    rw [mul_add, hlin, dotProduct_sub] at h1
    linarith

/-- **(15.D.5)-(15.D.6)** (MWG, p. 531). The equilibrium factor allocation solves the revenue
maximizing planner's problem: `∑ⱼ pⱼ fⱼ(z'ⱼ) ≤ ∑ⱼ pⱼ fⱼ(zⱼ)` for every allocation `z'` of `z̄`
(the first welfare theorem in this model). -/
theorem factorEqm_revenue_max {f : κ → (Fin L → ℝ) → ℝ} {p : κ → ℝ} {zbar w : Fin L → ℝ}
    {z : κ → Fin L → ℝ} (h : IsFactorEqm f p zbar w z) {z' : κ → Fin L → ℝ}
    (hz' : ∀ j, z' j ∈ nonnegOrthant L) (hsum : ∑ j, z' j = zbar) :
    ∑ j, p j * f j (z' j) ≤ ∑ j, p j * f j (z j) := by
  have hle : ∑ j, (p j * f j (z' j) - w ⬝ᵥ z' j) ≤ ∑ j, (p j * f j (z j) - w ⬝ᵥ z j) :=
    Finset.sum_le_sum fun j _ => (h.2.1 j).2 _ (hz' j)
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← dotProduct_sum, ← dotProduct_sum, hsum,
    h.2.2] at hle
  linarith

/-- **Section 15.D** (MWG, p. 532). The equilibrium factor prices are a supergradient of the
aggregate revenue function: for every endowment `z̃` and every allocation `z'` of `z̃`,
`∑ⱼ pⱼ fⱼ(z'ⱼ) - w·z̃ ≤ ∑ⱼ pⱼ fⱼ(zⱼ) - w·z̄` (the aggregate profit maximization (15.D.6)). -/
theorem factorEqm_supergradient {f : κ → (Fin L → ℝ) → ℝ} {p : κ → ℝ} {zbar w : Fin L → ℝ}
    {z : κ → Fin L → ℝ} (h : IsFactorEqm f p zbar w z) {z' : κ → Fin L → ℝ}
    (hz' : ∀ j, z' j ∈ nonnegOrthant L) :
    ∑ j, p j * f j (z' j) - w ⬝ᵥ ∑ j, z' j ≤ ∑ j, p j * f j (z j) - w ⬝ᵥ zbar := by
  have hle : ∑ j, (p j * f j (z' j) - w ⬝ᵥ z' j) ≤ ∑ j, (p j * f j (z j) - w ⬝ᵥ z j) :=
    Finset.sum_le_sum fun j _ => (h.2.1 j).2 _ (hz' j)
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← dotProduct_sum, ← dotProduct_sum,
    h.2.2] at hle
  exact hle

/-- **Section 15.D** (MWG, p. 532). Comparing two equilibria at the same output prices with
endowments `z̄` and `z̄'`, `(w' - w)·(z̄' - z̄) ≤ 0`. In particular
(`factor_price_endowment_opposite`) an increase in the endowment of a single factor cannot raise
its equilibrium price. -/
theorem factorEqm_monotone {f : κ → (Fin L → ℝ) → ℝ} {p : κ → ℝ} {zbar zbar' w w' : Fin L → ℝ}
    {z z' : κ → Fin L → ℝ} (h : IsFactorEqm f p zbar w z) (h' : IsFactorEqm f p zbar' w' z') :
    (w' - w) ⬝ᵥ (zbar' - zbar) ≤ 0 := by
  have h1 := factorEqm_supergradient h (fun j => (h'.2.1 j).1)
  have h2 := factorEqm_supergradient h' (fun j => (h.2.1 j).1)
  rw [h'.2.2] at h1
  rw [h.2.2] at h2
  simp only [sub_dotProduct, dotProduct_sub] at h1 h2 ⊢
  linarith

/-- **Section 15.D** (MWG, p. 532). An increase `δ > 0` in the endowment of factor `ℓ` alone
changes its equilibrium price in the opposite direction (weakly): `w'_ℓ ≤ w_ℓ`. -/
theorem factor_price_endowment_opposite {f : κ → (Fin L → ℝ) → ℝ} {p : κ → ℝ}
    {zbar w w' : Fin L → ℝ} {z z' : κ → Fin L → ℝ} {l : Fin L} {δ : ℝ} (hδ : 0 < δ)
    (h : IsFactorEqm f p zbar w z) (h' : IsFactorEqm f p (zbar + δ • Pi.single l 1) w' z') :
    w' l ≤ w l := by
  have := factorEqm_monotone h h'
  simp only [add_sub_cancel_left, dotProduct_smul, smul_eq_mul, sub_dotProduct] at this
  simp only [dotProduct_single, mul_one] at this
  nlinarith

/-- **Exercise 15.D.2** (MWG, p. 542), general form: the production possibility set
`{q ≥ 0 : ∃ zⱼ ≥ 0, ∑ zⱼ ≤ z̄, qⱼ ≤ fⱼ(zⱼ)}` (with free disposal) is convex when every production
function is concave on `ℝ^L₊`. -/
def productionPossibilitySet (f : κ → (Fin L → ℝ) → ℝ) (zbar : Fin L → ℝ) : Set (κ → ℝ) :=
  {q | (∀ j, 0 ≤ q j) ∧ ∃ z : κ → Fin L → ℝ, (∀ j, z j ∈ nonnegOrthant L) ∧
    (∀ l, ∑ j, z j l ≤ zbar l) ∧ ∀ j, q j ≤ f j (z j)}

/-- **Exercise 15.D.2** (MWG, p. 542). With concave production functions the production
possibility set is convex. -/
theorem exercise_15_D_2 {f : κ → (Fin L → ℝ) → ℝ}
    (hfc : ∀ j, ConcaveOn ℝ (nonnegOrthant L) (f j)) (zbar : Fin L → ℝ) :
    Convex ℝ (productionPossibilitySet f zbar) := by
  rintro q ⟨hq0, z, hz, hzs, hqz⟩ q' ⟨hq0', z', hz', hzs', hqz'⟩ a b ha hb hab
  refine ⟨fun j => ?_, fun j => a • z j + b • z' j, fun j => ?_, fun l => ?_, fun j => ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hq0 j)) (mul_nonneg hb (hq0' j))
  · exact (hfc j).1 (hz j) (hz' j) ha hb hab
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    have h1 := mul_le_mul_of_nonneg_left (hzs l) ha
    have h2 := mul_le_mul_of_nonneg_left (hzs' l) hb
    have h3 : a * zbar l + b * zbar l = zbar l := by rw [← add_mul, hab, one_mul]
    linarith
  · have := (hfc j).2 (hz j) (hz' j) ha hb hab
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    nlinarith [hqz j, hqz' j]

end MWG.GeneralEquilibriumExamples
