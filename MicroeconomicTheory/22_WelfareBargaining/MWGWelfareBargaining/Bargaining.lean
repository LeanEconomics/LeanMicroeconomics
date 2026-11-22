/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Compact
import Mathlib.Algebra.Order.Pi

/-!
# Bargaining problems and the axioms of Section 22.E

MWG, Section 22.E, pp. 838-841: the bargaining problem `(U, u*)`, Definitions 22.E.1-22.E.7.

A `BargainingProblem ι` is a set `U ⊆ ℝ^I` that is convex, closed and has free disposal
(`U - ℝ^I₊ ⊆ U`), together with a threat point `d = u*` interior to `U` such that
`{u ∈ U : u ≥ d}` is bounded (p. 839). We record boundedness by an upper bound `B` for the
coordinates of `{u ∈ U : u ≥ d}`; `BargainingProblem.isBounded` gives the bridge to metric
boundedness. A bargaining solution (Definition 22.E.1) is a map `f` with `f P ∈ P.U`.

The properties of Definitions 22.E.2-22.E.7 are `IUO`, `IUU`, `ParetoBS`, `SymmetricBS`,
`IndivRational` and `IIA`. Definition 22.E.3 is stated after the normalisation `u* = 0` in the
book; we state it for all problems by scaling the threat point too, which is equivalent in the
presence of `IUO` (`f(U, u*) = f(U - {u*}, 0) + u*`, p. 839, `normalize_eq`).

Constructions used throughout: translation `P.translate a` (`U + a`, `d + a`), rescaling
`P.scale β` (`{(βᵢuᵢ)ᵢ}`, `βd`), and the half-space problems `halfSpace c r`
`{u : ∑ cᵢuᵢ ≤ r}` with threat point `0`.
-/

namespace MWG.WelfareBargaining

open Set

variable {ι : Type*}

/-- **Section 22.E** (MWG, p. 839). A bargaining problem `(U, u*)`: `U ⊆ ℝ^I` convex, closed,
with free disposal; the threat point `d = u*` is interior to `U`, and `{u ∈ U : u ≥ d}` is
bounded. -/
@[ext]
structure BargainingProblem (ι : Type*) where
  /-- The utility possibility set. -/
  U : Set (ι → ℝ)
  /-- The threat (status-quo) point `u*`. -/
  d : ι → ℝ
  convex : Convex ℝ U
  closed : IsClosed U
  comprehensive : ∀ u ∈ U, ∀ v : ι → ℝ, v ≤ u → v ∈ U
  interior_d : d ∈ interior U
  bdd : ∃ B : ℝ, ∀ u ∈ U, d ≤ u → ∀ i, u i ≤ B

namespace BargainingProblem

theorem d_mem (P : BargainingProblem ι) : P.d ∈ P.U := interior_subset P.interior_d

/-- The bounded part is bounded in the metric sense (MWG, p. 839). -/
theorem isBounded [Finite ι] (P : BargainingProblem ι) :
    Bornology.IsBounded {u ∈ P.U | P.d ≤ u} := by
  cases nonempty_fintype ι
  obtain ⟨B, hB⟩ := P.bdd
  refine (Metric.isBounded_Icc P.d (fun _ => B)).subset fun u hu => ⟨hu.2, fun i => hB u hu.1
    hu.2 i⟩

/-- Some point strictly above the threat point lies in `U`. -/
theorem exists_gt [Finite ι] [Nonempty ι] (P : BargainingProblem ι) :
    ∃ ε > 0, (fun i => P.d i + ε) ∈ P.U := by
  cases nonempty_fintype ι
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 P.interior_d)
  refine ⟨ε / 2, by positivity, hball ?_⟩
  rw [Metric.mem_ball, dist_pi_lt_iff hε]
  intro i
  rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos (by positivity)]
  linarith

/-- Translation of a problem by `a`: `U' = U + a` and `u*' = u* + a` (Definition 22.E.2). -/
def translate [Fintype ι] (P : BargainingProblem ι) (a : ι → ℝ) : BargainingProblem ι where
  U := {v | v - a ∈ P.U}
  d := P.d + a
  convex := by
    have : {v : ι → ℝ | v - a ∈ P.U} = (fun x => -a + x) ⁻¹' P.U := by
      ext v; simp [sub_eq_neg_add]
    rw [this]
    exact P.convex.translate_preimage_right (-a)
  closed := P.closed.preimage (continuous_id.sub continuous_const)
  comprehensive := fun u hu v hv => P.comprehensive _ hu _ fun i => by
    simpa using sub_le_sub_right (hv i) (a i)
  interior_d := by
    have h := preimage_interior_subset_interior_preimage
      (f := fun v : ι → ℝ => v - a) (t := P.U) (continuous_id.sub continuous_const)
    apply h
    simp only [mem_preimage, add_sub_cancel_right]
    exact P.interior_d
  bdd := by
    obtain ⟨B, hB⟩ := P.bdd
    refine ⟨B + ∑ i, |a i|, fun u hu hdu i => ?_⟩
    have := hB _ hu (fun j => by have := hdu j; simp at this ⊢; linarith) i
    simp only [Pi.sub_apply] at this
    have h1 : a i ≤ |a i| := le_abs_self _
    have h2 : |a i| ≤ ∑ j, |a j| :=
      Finset.single_le_sum (f := fun j => |a j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    linarith

@[simp] theorem translate_U [Fintype ι] (P : BargainingProblem ι) (a : ι → ℝ) (v : ι → ℝ) :
    v ∈ (P.translate a).U ↔ v - a ∈ P.U := Iff.rfl

@[simp] theorem translate_d [Fintype ι] (P : BargainingProblem ι) (a : ι → ℝ) :
    (P.translate a).d = P.d + a := rfl

/-- Translating back and forth returns the problem. -/
theorem translate_translate [Fintype ι] (P : BargainingProblem ι) (a b : ι → ℝ) :
    (P.translate a).translate b = P.translate (a + b) := by
  ext v
  · simp [sub_sub, add_comm]
  · simp [add_assoc]

theorem translate_zero [Fintype ι] (P : BargainingProblem ι) : P.translate 0 = P := by
  ext v <;> simp

/-- The normalised problem `(U - {u*}, 0)`. -/
def normalize [Fintype ι] (P : BargainingProblem ι) : BargainingProblem ι := P.translate (-P.d)

theorem normalize_d [Fintype ι] (P : BargainingProblem ι) : P.normalize.d = 0 := by
  simp [normalize]

theorem normalize_translate [Fintype ι] (P : BargainingProblem ι) :
    P.normalize.translate P.d = P := by
  rw [normalize, translate_translate, neg_add_cancel, translate_zero]

/-- Rescaling of a problem by `β ≫ 0`: `U' = {(βᵢuᵢ)ᵢ : u ∈ U}` and `u*' = (βᵢu*ᵢ)ᵢ`
(Definition 22.E.3). -/
def scale [Fintype ι] (P : BargainingProblem ι) (β : ι → ℝ) (hβ : ∀ i, 0 < β i) :
    BargainingProblem ι where
  U := {v | (fun i => v i / β i) ∈ P.U}
  d := fun i => β i * P.d i
  convex := by
    intro x hx y hy a b ha hb hab
    simp only [mem_ofPred_eq] at hx hy ⊢
    have := P.convex hx hy ha hb hab
    convert this using 1
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  closed := P.closed.preimage (continuous_pi fun i => (continuous_apply i).div_const _)
  comprehensive := fun u hu v hv => P.comprehensive _ hu _ fun i =>
    div_le_div_of_nonneg_right (hv i) (hβ i).le
  interior_d := by
    have h := preimage_interior_subset_interior_preimage
      (f := fun v : ι → ℝ => fun i => v i / β i) (t := P.U)
      (continuous_pi fun i => (continuous_apply i).div_const _)
    apply h
    have : (fun i => β i * P.d i / β i) = P.d := funext fun i => by field_simp [(hβ i).ne']
    simp only [mem_preimage, this]
    exact P.interior_d
  bdd := by
    obtain ⟨B, hB⟩ := P.bdd
    refine ⟨(∑ j, β j) * |B|, fun u hu hdu i => ?_⟩
    have hle := hB _ hu (fun j => by
      rw [le_div_iff₀ (hβ j), mul_comm]; exact hdu j) i
    have h1 : u i ≤ β i * |B| := by
      rw [div_le_iff₀ (hβ i)] at hle
      nlinarith [le_abs_self B, hβ i]
    have h2 : β i ≤ ∑ j, β j :=
      Finset.single_le_sum (f := β) (fun j _ => (hβ j).le) (Finset.mem_univ i)
    nlinarith [abs_nonneg B]

theorem scale_U [Fintype ι] (P : BargainingProblem ι) (β : ι → ℝ) (hβ : ∀ i, 0 < β i)
    (v : ι → ℝ) : v ∈ (P.scale β hβ).U ↔ (fun i => v i / β i) ∈ P.U := Iff.rfl

theorem scale_d [Fintype ι] (P : BargainingProblem ι) (β : ι → ℝ) (hβ : ∀ i, 0 < β i) :
    (P.scale β hβ).d = fun i => β i * P.d i := rfl

/-- `v` is the image of `u ∈ U` under the rescaling. -/
theorem mem_scale [Fintype ι] (P : BargainingProblem ι) (β : ι → ℝ) (hβ : ∀ i, 0 < β i)
    {u : ι → ℝ} (hu : u ∈ P.U) : (fun i => β i * u i) ∈ (P.scale β hβ).U := by
  rw [scale_U]
  convert hu using 1
  funext i
  field_simp [(hβ i).ne']

end BargainingProblem

/-- A set is symmetric if it is invariant under permutations of the coordinates (MWG,
footnote 25, p. 840). -/
def IsSymmetricSet (U : Set (ι → ℝ)) : Prop := ∀ σ : Equiv.Perm ι, ∀ u ∈ U, u ∘ σ ∈ U

/-- **Section 22.E** (MWG, pp. 843-844). The half-space problem `{u : ∑ᵢ cᵢuᵢ ≤ r}` with threat
point `0`, for `c ≫ 0` and `r > 0`. -/
def halfSpace [Fintype ι] (c : ι → ℝ) (hc : ∀ i, 0 < c i) (r : ℝ) (hr : 0 < r) :
    BargainingProblem ι where
  U := {u | ∑ i, c i * u i ≤ r}
  d := 0
  convex := by
    intro x hx y hy a b ha hb hab
    simp only [mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hx hy ⊢
    have : ∑ i, c i * (a * x i + b * y i) = a * ∑ i, c i * x i + b * ∑ i, c i * y i := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this]
    nlinarith
  closed := isClosed_le (continuous_finsetSum _ fun i _ => continuous_const.mul
    (continuous_apply i)) continuous_const
  comprehensive := fun u hu v hv => le_trans (Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_left (hv i) (hc i).le) hu
  interior_d := by
    have hopen : IsOpen {u : ι → ℝ | ∑ i, c i * u i < r} := isOpen_lt
      (continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_apply i))
      continuous_const
    refine mem_interior.2 ⟨{u : ι → ℝ | ∑ i, c i * u i < r}, fun u (hu : _ < r) => hu.le,
      hopen, ?_⟩
    simp [hr]
  bdd := by
    refine ⟨∑ j, r / c j, fun u hu hdu i => ?_⟩
    have hdu' : ∀ j, 0 ≤ u j := fun j => by simpa using hdu j
    have h1 : c i * u i ≤ r := le_trans (Finset.single_le_sum (f := fun j => c j * u j)
      (fun j _ => mul_nonneg (hc j).le (hdu' j)) (Finset.mem_univ i)) hu
    have h2 : u i ≤ r / c i := by rw [le_div_iff₀ (hc i)]; linarith
    exact h2.trans (Finset.single_le_sum (f := fun j => r / c j)
      (fun j _ => (div_pos hr (hc j)).le) (Finset.mem_univ i))

theorem halfSpace_U [Fintype ι] (c : ι → ℝ) (hc : ∀ i, 0 < c i) (r : ℝ) (hr : 0 < r)
    (u : ι → ℝ) : u ∈ (halfSpace c hc r hr).U ↔ ∑ i, c i * u i ≤ r := Iff.rfl

/-- The half-space problem with equal coefficients is symmetric. -/
theorem halfSpace_symmetric [Fintype ι] (k : ℝ) (hk : 0 < k) (r : ℝ) (hr : 0 < r) :
    IsSymmetricSet (halfSpace (fun _ : ι => k) (fun _ => hk) r hr).U := by
  intro σ u hu
  simp only [halfSpace_U, Function.comp] at hu ⊢
  rwa [Equiv.sum_comp σ (fun i => k * u i)]

/-- **Definition 22.E.1** (MWG, p. 839). A bargaining solution assigns to every problem a point
of its utility possibility set. -/
def IsBargainingSolution (f : BargainingProblem ι → ι → ℝ) : Prop :=
  ∀ P, f P ∈ P.U

/-- **Definition 22.E.2** (MWG, p. 839). Independence of utility origins:
`f(U + a, u* + a) = f(U, u*) + a`. -/
def IUO [Fintype ι] (f : BargainingProblem ι → ι → ℝ) : Prop :=
  ∀ P a, f (P.translate a) = f P + a

/-- **Definition 22.E.3** (MWG, p. 840). Independence of utility units:
`f(βU, βu*) = β f(U, u*)` for `β ≫ 0`. -/
def IUU [Fintype ι] (f : BargainingProblem ι → ι → ℝ) : Prop :=
  ∀ P β (hβ : ∀ i, 0 < β i), f (P.scale β hβ) = fun i => β i * f P i

/-- **Definition 22.E.4** (MWG, p. 840). The (weak) Pareto property: no `v ∈ U` with
`vᵢ > fᵢ(U)` for every `i`. -/
def ParetoBS (f : BargainingProblem ι → ι → ℝ) : Prop :=
  ∀ P, ¬∃ v ∈ P.U, ∀ i, f P i < v i

/-- **Definition 22.E.5** (MWG, p. 840). Symmetry: for a symmetric problem (symmetric `U`,
threat point with equal entries) all entries of `f(U)` are equal. -/
def SymmetricBS (f : BargainingProblem ι → ι → ℝ) : Prop :=
  ∀ P : BargainingProblem ι, IsSymmetricSet P.U → (∀ i j, P.d i = P.d j) → ∀ i j, f P i = f P j

/-- **Definition 22.E.6** (MWG, p. 840). Individual rationality: `f(U) ≥ u*`. -/
def IndivRational (f : BargainingProblem ι → ι → ℝ) : Prop :=
  ∀ P, P.d ≤ f P

/-- **Definition 22.E.7** (MWG, p. 841). Independence of irrelevant alternatives: if
`U' ⊆ U` (same threat point) and `f(U) ∈ U'` then `f(U') = f(U)`. -/
def IIA (f : BargainingProblem ι → ι → ℝ) : Prop :=
  ∀ P P' : BargainingProblem ι, P'.U ⊆ P.U → P'.d = P.d → f P ∈ P'.U → f P' = f P

/-- **Section 22.E** (MWG, p. 839). Under `IUO`, `f(U, u*) = f(U - {u*}, 0) + u*`: problems may
be normalised to `u* = 0`. -/
theorem normalize_eq [Fintype ι] {f : BargainingProblem ι → ι → ℝ} (hf : IUO f)
    (P : BargainingProblem ι) :
    f P = f P.normalize + P.d := by
  conv_lhs => rw [← P.normalize_translate]
  exact hf _ _

end MWG.WelfareBargaining
