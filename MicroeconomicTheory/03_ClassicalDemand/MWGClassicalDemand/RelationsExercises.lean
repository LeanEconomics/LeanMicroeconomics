/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.RelationsBasic
import MWGClassicalDemand.UMPExercises
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Exercises for Section 3.G

MWG, Exercises 3.G.4, 3.G.6-3.G.8, 3.G.11, 3.G.13, 3.G.14, 3.G.17 (pp. 99-102).

* 3.G.7: indirect demand `g(x) = ∇u(x)/(x·∇u(x))` at an interior optimum with `w = 1`, and
  `x(p) = ∇v(p)/(p·∇v(p))` from Roy's identity and Exercise 3.D.8.
* 3.G.8: logarithmically homogeneous `v` gives `x(p, 1) = -∇_p v(p, 1)`.
* 3.G.11 and 3.G.13: from Roy's identity, Gorman-form indirect utility gives affine wealth
  expansion paths, and an indirect utility polynomial of degree `n` in `w` gives expansion paths
  in a subspace of dimension at most `n + 1`.
* 3.G.14: the substitution matrix completed by symmetry and `S p = 0`, which is negative
  semidefinite.
* 3.G.4(a) (a nonlinear transformation destroys additive separability) and 3.G.4(b).
* 3.G.6(a)-(b): demand for good 3 from Walras' law; homogeneity of degree zero.
* 3.G.17(a)-(c): Hausman's local indirect utility: Roy's identity, the inverse expenditure
  function and the Hicksian demand as `∂e/∂p₁`.
-/

namespace MWG.ClassicalDemand

open MWG.ConsumerChoice Kreps.PreferenceProperties Filter Topology

variable {L : ℕ}

/-- **Exercise 3.G.7** (MWG, p. 100), first part. At an interior solution `x ≫ 0` of the UMP
with `w = 1`, if `u` is differentiable at `x` and `x·∇u(x) ≠ 0`, the price vector is
`g(x) = ∇u(x)/(x·∇u(x))`. -/
theorem exercise_3_G_7_indirect_demand {u : (Fin L → ℝ) → ℝ}
    {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop} (hrep : RepresentsOn (nonnegOrthant L) u r)
    (hlns : LocallyNonsatiated (nonnegOrthant L) r) {u' : (Fin L → ℝ) →L[ℝ] ℝ}
    {p x : Fin L → ℝ} (hp : StrictlyPositive p) (hx : x ∈ walrasianDemand u p 1)
    (hd : HasFDerivAt u u' x) (hint : ∀ l, 0 < x l) (hne : x ⬝ᵥ gradientVec u' ≠ 0) :
    p = (1 / (x ⬝ᵥ gradientVec u')) • gradientVec u' := by
  obtain ⟨lam, -, hfoc⟩ := equation_3_D_4 hp hx hd hint
  have hw : p ⬝ᵥ x = 1 := proposition_3_D_2_ii hrep hlns hx
  have hlam : x ⬝ᵥ gradientVec u' = lam := by
    rw [hfoc, dotProduct_smul, smul_eq_mul, dotProduct_comm, hw, mul_one]
  rw [hlam] at hne ⊢
  rw [hfoc, smul_smul, one_div, inv_mul_cancel₀ hne, one_smul]

/-- **Exercise 3.G.7** (MWG, p. 100), second part. From Roy's identity and Exercise 3.D.8: if
`v` is differentiable at `(p, 1)` with `p·∇_p v(p, 1) ≠ 0`, then
`x(p) = ∇_p v(p)/(p·∇_p v(p))`. -/
theorem exercise_3_G_7_demand {u : (Fin L → ℝ) → ℝ} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hrep : RepresentsOn (nonnegOrthant L) u r) (hu : ContinuousOn u (nonnegOrthant L))
    (hlns : LocallyNonsatiated (nonnegOrthant L) r) (hsc : PrefStrictlyConvex (nonnegOrthant L) r)
    {p : Fin L → ℝ} (hp : StrictlyPositive p) {Dv : ((Fin L → ℝ) × ℝ) →L[ℝ] ℝ}
    (hD : HasFDerivAt (fun q : (Fin L → ℝ) × ℝ => indirectUtility u q.1 q.2) Dv (p, 1))
    {x : Fin L → ℝ} (hx : x ∈ walrasianDemand u p 1)
    (hne : ∑ l, p l * Dv (Pi.single l 1, 0) ≠ 0) :
    ∀ l, x l = Dv (Pi.single l 1, 0) / ∑ k, p k * Dv (Pi.single k 1, 0) := by
  have hroy := (proposition_3_G_4 hrep hu hlns hsc ⟨hp, one_pos⟩ hD hx).1
  have heuler := exercise_3_D_8 u hD
  rw [one_mul] at heuler
  intro l
  have := hroy l
  rw [heuler] at this
  field_simp
  linarith

/-- **Exercise 3.G.8** (MWG, p. 100). If `v` is logarithmically homogeneous at `p`,
`v(p, αw) = v(p, w) + ln α` (here used at `w = 1`), and differentiable at `(p, 1)`, then
`∂v/∂w(p, 1) = 1` and Roy's identity gives `x(p, 1) = -∇_p v(p, 1)`. -/
theorem exercise_3_G_8 {u : (Fin L → ℝ) → ℝ} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hrep : RepresentsOn (nonnegOrthant L) u r) (hu : ContinuousOn u (nonnegOrthant L))
    (hlns : LocallyNonsatiated (nonnegOrthant L) r) (hsc : PrefStrictlyConvex (nonnegOrthant L) r)
    {p : Fin L → ℝ} (hp : StrictlyPositive p) {Dv : ((Fin L → ℝ) × ℝ) →L[ℝ] ℝ}
    (hD : HasFDerivAt (fun q : (Fin L → ℝ) × ℝ => indirectUtility u q.1 q.2) Dv (p, 1))
    (hlog : ∀ α : ℝ, 0 < α → indirectUtility u p α = indirectUtility u p 1 + Real.log α)
    {x : Fin L → ℝ} (hx : x ∈ walrasianDemand u p 1) :
    Dv (0, 1) = 1 ∧ ∀ l, x l = -Dv (Pi.single l 1, 0) := by
  have hpath : HasDerivAt (fun w : ℝ => ((p, w) : (Fin L → ℝ) × ℝ)) ((0 : Fin L → ℝ), 1) 1 :=
    (hasDerivAt_const 1 p).prodMk (hasDerivAt_id 1)
  have h1 : HasDerivAt (fun w : ℝ => indirectUtility u p w) (Dv (0, 1)) 1 :=
    HasFDerivAt.comp_hasDerivAt (f := fun w : ℝ => ((p, w) : (Fin L → ℝ) × ℝ)) 1 hD hpath
  have h2 : HasDerivAt (fun w : ℝ => indirectUtility u p w) 1 1 := by
    have hlogd : HasDerivAt (fun w : ℝ => indirectUtility u p 1 + Real.log w) 1 1 := by
      simpa using (Real.hasDerivAt_log one_ne_zero).const_add (indirectUtility u p 1)
    apply hlogd.congr_of_eventuallyEq
    filter_upwards [lt_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with w hw
    exact hlog w hw
  have hw1 : Dv (0, 1) = 1 := h1.unique h2
  refine ⟨hw1, fun l => ?_⟩
  have := (proposition_3_G_4 hrep hu hlns hsc ⟨hp, one_pos⟩ hD hx).1 l
  rw [hw1, one_mul] at this
  linarith

/-- The partial derivative in prices of a function of `(p, w)`, read off its derivative. -/
theorem relations_partial_price_eq {V : (Fin L → ℝ) × ℝ → ℝ} {p : Fin L → ℝ} {w : ℝ}
    {Dv : ((Fin L → ℝ) × ℝ) →L[ℝ] ℝ} (hD : HasFDerivAt V Dv (p, w))
    {g : (Fin L → ℝ) →L[ℝ] ℝ} (hg : HasFDerivAt (fun q => V (q, w)) g p) (l : Fin L) :
    Dv (Pi.single l 1, 0) = g (Pi.single l 1) := by
  have h1 : HasFDerivAt (fun q => V (q, w)) (Dv.comp ((ContinuousLinearMap.id ℝ _).prod 0)) p :=
    HasFDerivAt.comp (f := fun q => ((q, w) : (Fin L → ℝ) × ℝ)) p hD
      ((hasFDerivAt_id p).prodMk (hasFDerivAt_const w p))
  rw [← h1.unique hg]
  rfl

/-- **Exercise 3.G.11** (MWG, p. 101). Gorman form `v(p, w) = a(p) + b(p) w` with `b(p) ≠ 0`:
Roy's identity, `∂v/∂p_l + (∂v/∂w) x_l = 0` at every `(p, w)`, `w ∈ W`, forces
`x(p, w) = -(∇a(p) + w ∇b(p))/b(p)`, so the wealth expansion path is a straight line. -/
theorem exercise_3_G_11 {a b : (Fin L → ℝ) → ℝ} {p : Fin L → ℝ} {a' b' : (Fin L → ℝ) →L[ℝ] ℝ}
    (ha : HasFDerivAt a a' p) (hb : HasFDerivAt b b' p) (hb0 : b p ≠ 0)
    {x : ℝ → Fin L → ℝ} {W : Set ℝ}
    (hroy : ∀ w ∈ W, ∀ Dv : ((Fin L → ℝ) × ℝ) →L[ℝ] ℝ,
      HasFDerivAt (fun q : (Fin L → ℝ) × ℝ => a q.1 + b q.1 * q.2) Dv (p, w) →
        ∀ l, Dv (Pi.single l 1, 0) + Dv (0, 1) * x w l = 0) :
    ∀ w ∈ W, x w = -(1 / b p) • (gradientVec a' + w • gradientVec b') := by
  intro w hw
  have hD : HasFDerivAt (fun q : (Fin L → ℝ) × ℝ => a q.1 + b q.1 * q.2)
      (a'.comp (ContinuousLinearMap.fst ℝ _ ℝ) +
        (w • b'.comp (ContinuousLinearMap.fst ℝ _ ℝ) +
          b p • ContinuousLinearMap.snd ℝ _ ℝ)) (p, w) := by
    have h1 := HasFDerivAt.comp (f := Prod.fst) (p, w) ha hasFDerivAt_fst
    have h2 := (HasFDerivAt.comp (f := Prod.fst) (p, w) hb hasFDerivAt_fst).mul hasFDerivAt_snd
    refine HasFDerivAt.congr_fderiv
      (f := fun q : (Fin L → ℝ) × ℝ => a q.1 + b q.1 * q.2) (h1.add h2) ?_
    ext v <;> simp
  funext l
  have := hroy w hw _ hD l
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_apply,
    smul_eq_mul, map_zero, mul_zero, add_zero, zero_add, mul_one] at this
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, gradientVec]
  field_simp
  linarith

/-- **Exercise 3.G.13** (MWG, p. 101). If `v(p, w) = ∑_{k ≤ n} c_k(p) w^k` and Roy's identity
holds at `(p, w)` with `∂v/∂w ≠ 0`, then `x(p, w)` lies in the span of the `n + 1` vectors
`∇c_k(p)`: the wealth expansion path lies in a subspace of dimension at most `n + 1`. -/
theorem exercise_3_G_13 {n : ℕ} {c : Fin (n + 1) → (Fin L → ℝ) → ℝ} {p : Fin L → ℝ}
    {c' : Fin (n + 1) → (Fin L → ℝ) →L[ℝ] ℝ} (hc : ∀ k, HasFDerivAt (c k) (c' k) p) {w : ℝ}
    {Dv : ((Fin L → ℝ) × ℝ) →L[ℝ] ℝ}
    (hD : HasFDerivAt (fun q : (Fin L → ℝ) × ℝ => ∑ k, c k q.1 * q.2 ^ (k : ℕ)) Dv (p, w))
    (hw : Dv (0, 1) ≠ 0) {x : Fin L → ℝ}
    (hroy : ∀ l, Dv (Pi.single l 1, 0) + Dv (0, 1) * x l = 0) :
    x ∈ Submodule.span ℝ (Set.range fun k => gradientVec (c' k)) ∧
      Module.finrank ℝ (Submodule.span ℝ (Set.range fun k => gradientVec (c' k))) ≤ n + 1 := by
  have hg : HasFDerivAt (fun q => ∑ k, c k q * w ^ (k : ℕ))
      (∑ k : Fin (n + 1), w ^ (k : ℕ) • c' k) p := by
    have := HasFDerivAt.fun_sum (u := Finset.univ) fun k _ => (hc k).mul_const (w ^ (k : ℕ))
    convert this using 1
  have hpart := fun l => relations_partial_price_eq hD hg l
  have hx : x = ∑ k : Fin (n + 1), (-(w ^ (k : ℕ)) / Dv (0, 1)) • gradientVec (c' k) := by
    funext l
    have h1 := hroy l
    rw [hpart l] at h1
    simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
      Pi.smul_apply, smul_eq_mul] at h1
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, gradientVec]
    have hsum : ∑ k : Fin (n + 1), -(w ^ (k : ℕ)) / Dv (0, 1) * c' k (Pi.single l 1) =
        -(∑ k : Fin (n + 1), w ^ (k : ℕ) * c' k (Pi.single l 1)) / Dv (0, 1) := by
      rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hsum]
    field_simp
    linarith
  refine ⟨?_, ?_⟩
  · rw [hx]
    exact Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · have := finrank_range_le_card (R := ℝ) (b := fun k => gradientVec (c' k))
    rw [Fintype.card_fin] at this
    exact this

/-- **Exercise 3.G.14** (MWG, p. 101). The substitution matrix at prices `(1, 2, 6)`, completed
by symmetry and `S p = 0`. -/
noncomputable def exercise_3_G_14_matrix : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-10, -4, 3; -4, -4, 2; 3, 2, -7 / 6]

/-- **Exercise 3.G.14** (MWG, p. 101). A symmetric matrix with `s₁₁ = -10`, `s₂₂ = -4`,
`s₃₁ = 3` and `S p = 0` at `p = (1, 2, 6)` is uniquely determined; the completed matrix is
negative semidefinite, so it has all the properties of a substitution matrix. -/
theorem exercise_3_G_14 :
    (∀ S : Matrix (Fin 3) (Fin 3) ℝ, S 0 0 = -10 → S 1 1 = -4 → S 2 0 = 3 →
        (∀ i j, S i j = S j i) → S.mulVec ![1, 2, 6] = 0 → S = exercise_3_G_14_matrix) ∧
      (∀ i j, exercise_3_G_14_matrix i j = exercise_3_G_14_matrix j i) ∧
      exercise_3_G_14_matrix.mulVec ![1, 2, 6] = 0 ∧ NegSemidef exercise_3_G_14_matrix := by
  refine ⟨fun S h00 h11 h20 hsym hp => ?_, ?_, ?_, ?_⟩
  · have r0 := congrFun hp 0
    have r1 := congrFun hp 1
    have r2 := congrFun hp 2
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at r0 r1 r2
    have h01 := hsym 0 1
    have h02 := hsym 0 2
    have h12 := hsym 1 2
    ext i j
    fin_cases i <;> fin_cases j <;> simp [exercise_3_G_14_matrix] <;> linarith
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [exercise_3_G_14_matrix]
  · ext i
    fin_cases i <;> simp [exercise_3_G_14_matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      <;> norm_num
  · intro z
    simp [exercise_3_G_14_matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    nlinarith [sq_nonneg (z 0 + 2 / 5 * z 1 - 3 / 10 * z 2), sq_nonneg (z 1 - z 2 / 3)]

/-- **Exercise 3.G.4(b)** (MWG, p. 99). For an additively separable `u(x) = ∑ u_l(x_l)`, the
ordering of bundles that differ only on a group `G` of commodities does not depend on the fixed
values `c` of the other commodities. -/
theorem exercise_3_G_4b (v : Fin L → ℝ → ℝ) (G : Finset (Fin L)) (x y c c' : Fin L → ℝ) :
    let u : (Fin L → ℝ) → ℝ := fun z => ∑ l, v l (z l)
    let merge : (Fin L → ℝ) → (Fin L → ℝ) → Fin L → ℝ :=
      fun a b l => if l ∈ G then a l else b l
    (u (merge y c) ≤ u (merge x c) ↔ u (merge y c') ≤ u (merge x c')) := by
  intro u merge
  have key : ∀ d : Fin L → ℝ, u (merge x d) - u (merge y d) =
      ∑ l ∈ G, (v l (x l) - v l (y l)) := by
    intro d
    simp only [u, merge, ← Finset.sum_sub_distrib]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ G)]
    have h2 : ∑ l ∈ Finset.univ.filter (· ∉ G),
        (v l (if l ∈ G then x l else d l) - v l (if l ∈ G then y l else d l)) = 0 := by
      refine Finset.sum_eq_zero fun l hl => ?_
      rw [Finset.mem_filter] at hl
      simp [hl.2]
    rw [h2, add_zero, Finset.filter_mem_eq_inter, Finset.univ_inter]
    refine Finset.sum_congr rfl fun l hl => ?_
    simp [hl]
  constructor
  · intro h
    have := key c
    have := key c'
    linarith
  · intro h
    have := key c
    have := key c'
    linarith

/-- **Exercise 3.G.4(a)** (MWG, p. 99), the "only" part illustrated: additive separability is
not preserved by the increasing transformation `exp`. `u = x₁ + x₂` is additively separable,
but `exp(x₁ + x₂)` is not `v₁(x₁) + v₂(x₂)` for any `v₁, v₂`. -/
theorem exercise_3_G_4a_not_ordinal :
    ¬ ∃ v₁ v₂ : ℝ → ℝ, ∀ x₁ x₂ : ℝ, Real.exp (x₁ + x₂) = v₁ x₁ + v₂ x₂ := by
  rintro ⟨v₁, v₂, h⟩
  have h11 := h 1 1
  have h10 := h 1 0
  have h01 := h 0 1
  have h00 := h 0 0
  have hmix : Real.exp 2 - 2 * Real.exp 1 + 1 = 0 := by
    have e2 : Real.exp 2 = Real.exp (1 + 1) := by norm_num
    rw [e2]
    simp only [add_zero, zero_add] at h10 h01 h00
    rw [Real.exp_zero] at h00
    linarith
  have : Real.exp 2 = Real.exp 1 ^ 2 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [this] at hmix
  have hne : Real.exp 1 ≠ 1 := by
    intro h1
    have := Real.add_one_lt_exp one_ne_zero
    linarith
  have hsq : (Real.exp 1 - 1) ^ 2 = 0 := by linarith
  have h0 : Real.exp 1 - 1 = 0 := (pow_eq_zero_iff two_ne_zero).mp hsq
  exact hne (by linarith)

/-- **Exercise 3.G.4(a)** (MWG, p. 99), the "preserved" part: positive affine transformations
`a u + b` of an additively separable `u` are additively separable. -/
theorem exercise_3_G_4a_affine (v : Fin L → ℝ → ℝ) (a b : ℝ) (hL : 0 < L) :
    ∃ w : Fin L → ℝ → ℝ, ∀ x : Fin L → ℝ, a * ∑ l, v l (x l) + b = ∑ l, w l (x l) := by
  refine ⟨fun l t => a * v l t + if l = ⟨0, hL⟩ then b else 0, fun x => ?_⟩
  rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_ite_eq']
  simp

/-- The demand functions of Exercise 3.G.6 (Fisher). -/
noncomputable def exercise_3_G_6_x1 (β δ : ℝ) (p : Fin 3 → ℝ) (w : ℝ) : ℝ :=
  100 - 5 * (p 0 / p 2) + β * (p 1 / p 2) + δ * (w / p 2)

/-- The demand for good 2 in Exercise 3.G.6. -/
noncomputable def exercise_3_G_6_x2 (α β γ δ : ℝ) (p : Fin 3 → ℝ) (w : ℝ) : ℝ :=
  α + β * (p 0 / p 2) + γ * (p 1 / p 2) + δ * (w / p 2)

/-- **Exercise 3.G.6(b)** (MWG, p. 100). The demand functions for goods 1 and 2 are homogeneous
of degree zero in `(p, w)`. -/
theorem exercise_3_G_6b (α β γ δ : ℝ) {p : Fin 3 → ℝ} (hp : p 2 ≠ 0) (w : ℝ) {t : ℝ}
    (ht : t ≠ 0) :
    exercise_3_G_6_x1 β δ (t • p) (t * w) = exercise_3_G_6_x1 β δ p w ∧
      exercise_3_G_6_x2 α β γ δ (t • p) (t * w) = exercise_3_G_6_x2 α β γ δ p w := by
  simp only [exercise_3_G_6_x1, exercise_3_G_6_x2, Pi.smul_apply, smul_eq_mul]
  constructor <;> field_simp

/-- **Exercise 3.G.6(a)** (MWG, p. 100). With Walras' law the demand for good 3 is
`x₃ = (w - p₁x₁ - p₂x₂)/p₃`. -/
theorem exercise_3_G_6a {x : Fin 3 → ℝ} {p : Fin 3 → ℝ} {w : ℝ} (hp : p 2 ≠ 0)
    (hW : p ⬝ᵥ x = w) : x 2 = (w - p 0 * x 0 - p 1 * x 1) / p 2 := by
  rw [← hW]
  simp [dotProduct, Fin.sum_univ_three]
  field_simp
  ring

/-- The local indirect utility of Exercise 3.G.17 (Hausman). -/
noncomputable def exercise_3_G_17_v (a b c p₁ p₂ w : ℝ) : ℝ :=
  -Real.exp (-(b * p₁ / p₂)) * (w / p₂ + 1 / b * (a * p₁ / p₂ + a / b + c))

/-- The local expenditure function of Exercise 3.G.17. -/
noncomputable def exercise_3_G_17_e (a b c p₁ p₂ u : ℝ) : ℝ :=
  -p₂ * u * Real.exp (b * p₁ / p₂) - 1 / b * (a * p₁ + a / b * p₂ + c * p₂)

/-- **Exercise 3.G.17(a)** (MWG, pp. 101-102). The partial derivatives of the local indirect
utility in `p₁` and `w`, and Roy's identity: `-(∂v/∂p₁)/(∂v/∂w) = a p₁/p₂ + b w/p₂ + c`. -/
theorem exercise_3_G_17a {a b c p₁ p₂ w : ℝ} (hb : b ≠ 0) (hp : p₂ ≠ 0) :
    HasDerivAt (fun w' => exercise_3_G_17_v a b c p₁ p₂ w') (-Real.exp (-(b * p₁ / p₂)) / p₂) w ∧
      HasDerivAt (fun q => exercise_3_G_17_v a b c q p₂ w)
        (b / p₂ * Real.exp (-(b * p₁ / p₂)) * (w / p₂ + 1 / b * (a * p₁ / p₂ + a / b + c)) -
          Real.exp (-(b * p₁ / p₂)) * (a / (b * p₂))) p₁ ∧
      -((b / p₂ * Real.exp (-(b * p₁ / p₂)) * (w / p₂ + 1 / b * (a * p₁ / p₂ + a / b + c)) -
          Real.exp (-(b * p₁ / p₂)) * (a / (b * p₂))) / (-Real.exp (-(b * p₁ / p₂)) / p₂)) =
        a * p₁ / p₂ + b * w / p₂ + c := by
  refine ⟨?_, ?_, ?_⟩
  · have h1 : HasDerivAt (fun w' : ℝ => w' / p₂ + 1 / b * (a * p₁ / p₂ + a / b + c))
        (1 / p₂) w := ((hasDerivAt_id' w).div_const p₂).add_const _
    exact (h1.const_mul (-Real.exp (-(b * p₁ / p₂)))).congr_deriv (by field_simp)
  · have hlin : HasDerivAt (fun q : ℝ => -(b * q / p₂)) (-(b / p₂)) p₁ :=
      (((hasDerivAt_id' p₁).const_mul b).div_const p₂).neg.congr_deriv (by ring)
    have hin : HasDerivAt (fun q : ℝ => w / p₂ + 1 / b * (a * q / p₂ + a / b + c))
        (1 / b * (a * 1 / p₂)) p₁ :=
      (((((hasDerivAt_id' p₁).const_mul a).div_const p₂).add_const (a / b)).add_const
        c).const_mul (1 / b) |>.const_add (w / p₂)
    exact (hlin.exp.neg.mul hin).congr_deriv (by simp only [Pi.neg_apply]; field_simp; ring)
  · have hE := Real.exp_pos (-(b * p₁ / p₂))
    field_simp
    ring

/-- **Exercise 3.G.17(b)** (MWG, p. 101). The local expenditure function inverts the local
indirect utility: `v(p, e(p, u)) = u`. -/
theorem exercise_3_G_17b {a b c p₁ p₂ u : ℝ} (hb : b ≠ 0) (hp : p₂ ≠ 0) :
    exercise_3_G_17_v a b c p₁ p₂ (exercise_3_G_17_e a b c p₁ p₂ u) = u := by
  unfold exercise_3_G_17_v exercise_3_G_17_e
  have h : Real.exp (-(b * p₁ / p₂)) * Real.exp (b * p₁ / p₂) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  field_simp
  linear_combination (b ^ 2 * p₂ * u) * h

/-- **Exercise 3.G.17(c)** (MWG, p. 102). The local Hicksian demand for good 1 is
`∂e/∂p₁ = -u b exp(b p₁/p₂) - a/b`. -/
theorem exercise_3_G_17c {a b c p₁ p₂ u : ℝ} (hb : b ≠ 0) (hp : p₂ ≠ 0) :
    HasDerivAt (fun q => exercise_3_G_17_e a b c q p₂ u)
      (-u * b * Real.exp (b * p₁ / p₂) - a / b) p₁ := by
  have hlin : HasDerivAt (fun q : ℝ => b * q / p₂) (b * 1 / p₂) p₁ :=
    ((hasDerivAt_id' p₁).const_mul b).div_const p₂
  have h2 : HasDerivAt (fun q : ℝ => 1 / b * (a * q + a / b * p₂ + c * p₂)) (1 / b * (a * 1))
      p₁ := ((((hasDerivAt_id' p₁).const_mul a).add_const (a / b * p₂)).add_const
        (c * p₂)).const_mul (1 / b)
  exact ((hlin.exp.const_mul (-p₂ * u)).sub h2).congr_deriv (by field_simp)

end MWG.ClassicalDemand
