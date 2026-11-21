/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.AppendixMH
import LeanEconomics.FixedPoint.Brouwer
import LeanEconomics.FixedPoint.Kakutani
import Mathlib.Order.FixedPoints
import Mathlib.Order.CompleteLatticeIntervals
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Data.Fin.VecNotation

/-!
# Fixed point theorems

MWG, Mathematical Appendix, Section M.I, pp. 952-953.

* **Theorem M.I.1** (Brouwer, `theorem_M_I_1`): from LeanEconomics' `brouwer` (any
  finite-dimensional real normed space), stated for `A ⊆ ℝ^N`. The case `N = 1`, `A = [0, 1]`,
  by the intermediate value theorem as in the text (`brouwer_unitInterval_ivt`); continuity is
  indispensable (`figure_M_I_1b`); convexity is indispensable: a 90-degree clockwise rotation of
  the circle `‖x‖ = 1` in `ℝ²` is continuous with no fixed point (`circle_rotation_no_fixedPoint`,
  `circle_not_convex`).
* **Theorem M.I.2** (Kakutani, `theorem_M_I_2`): with MWG's upper hemicontinuity
  (Definition M.H.3, `UpperHemicontinuousMWG` from Chapter 3), derived from LeanEconomics'
  `kakutani` (closed-graph form, any real normed space; `kakutani_mwg`). Convex values are
  indispensable (`figure_M_I_2b`).
* **Theorem M.I.3** (Tarski, `theorem_M_I_3`): a nondecreasing self-map of `[0, 1]^N` has a fixed
  point; proved by the Knaster-Tarski theorem on the complete lattice `[0, 1]^N`. Continuity is
  not needed (`figure_M_I_3`).

Each theorem has a concrete instance of its hypotheses (`theorem_M_I_1_instance`,
`theorem_M_I_2_instance`, and `figure_M_I_3` for Theorem M.I.3).
-/

namespace MWG.SimultaneousMoveGames

open MWG.ClassicalDemand Filter Topology

/-- **Theorem M.I.1** (Brouwer's fixed point theorem; MWG, p. 952). If `A ⊆ ℝ^N` is nonempty,
compact and convex and `f : A → A` is continuous, then `f` has a fixed point `x = f(x)`. -/
theorem theorem_M_I_1 {N : ℕ} {A : Set (Fin N → ℝ)} (hne : A.Nonempty) (hA : IsCompact A)
    (hconv : Convex ℝ A) {f : (Fin N → ℝ) → (Fin N → ℝ)} (hf : ContinuousOn f A)
    (hmaps : Set.MapsTo f A A) : ∃ x ∈ A, x = f x := by
  obtain ⟨x, hx, hfx⟩ := LeanEconomics.FixedPoint.brouwer hA hconv hne hf hmaps
  exact ⟨x, hx, hfx.symm⟩

/-- The hypotheses of Theorem M.I.1 are satisfiable: halving maps the cube `[0, 1]^N` into
itself. -/
theorem theorem_M_I_1_instance (N : ℕ) :
    let A : Set (Fin N → ℝ) := Set.pi Set.univ fun _ => Set.Icc 0 1
    A.Nonempty ∧ IsCompact A ∧ Convex ℝ A ∧ ContinuousOn (fun x => (1 / 2 : ℝ) • x) A ∧
      Set.MapsTo (fun x : Fin N → ℝ => (1 / 2 : ℝ) • x) A A := by
  intro A
  refine ⟨⟨0, fun k _ => by simp⟩, isCompact_univ_pi fun _ => isCompact_Icc,
    convex_pi fun _ _ => convex_Icc 0 1, (continuous_const_smul _).continuousOn,
    fun x hx k _ => ?_⟩
  have := hx k (Set.mem_univ k)
  simp only [Pi.smul_apply, smul_eq_mul, Set.mem_Icc] at this ⊢
  constructor <;> linarith [this.1, this.2]

/-- **Section M.I** (MWG, pp. 952-953). For `N = 1` and `A = [0, 1]` Brouwer's theorem is a
consequence of the intermediate value theorem applied to `φ(x) = f(x) - x`, which has
`φ(0) ≥ 0` and `φ(1) ≤ 0`. -/
theorem brouwer_unitInterval_ivt {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc 0 1))
    (hmaps : Set.MapsTo f (Set.Icc 0 1) (Set.Icc 0 1)) : ∃ x ∈ Set.Icc (0 : ℝ) 1, f x = x := by
  have hφ : ContinuousOn (fun x => f x - x) (Set.Icc 0 1) := hf.sub continuousOn_id
  have h0 := hmaps (Set.left_mem_Icc.2 zero_le_one)
  have h1 := hmaps (Set.right_mem_Icc.2 zero_le_one)
  have hmem : (0 : ℝ) ∈ Set.Icc (f 1 - 1) (f 0 - 0) := ⟨by linarith [h1.2], by linarith [h0.1]⟩
  obtain ⟨x, hx, hx0⟩ := intermediate_value_Icc' zero_le_one hφ hmem
  exact ⟨x, hx, by linarith [hx0]⟩

/-- **Figure M.I.1(b)** (MWG, p. 952). Continuity is indispensable: the function equal to `1`
on `[0, 1/2]` and to `0` on `(1/2, 1]` maps `[0, 1]` into itself and has no fixed point. -/
theorem figure_M_I_1b :
    let f : ℝ → ℝ := fun x => if x ≤ 1 / 2 then 1 else 0
    Set.MapsTo f (Set.Icc 0 1) (Set.Icc 0 1) ∧ ∀ x ∈ Set.Icc (0 : ℝ) 1, f x ≠ x := by
  intro f
  refine ⟨fun x _ => ?_, fun x _ => ?_⟩
  · simp only [f]
    split_ifs <;> norm_num
  · simp only [f]
    split_ifs with h
    · intro h1; linarith
    · intro h0; rw [← h0] at h; norm_num at h

/-- The unit circle `S = {x ∈ ℝ² : ‖x‖ = 1}` (Euclidean norm, written out). -/
def unitCircle : Set (Fin 2 → ℝ) := {x | x 0 ^ 2 + x 1 ^ 2 = 1}

/-- The 90-degree clockwise rotation `(x₁, x₂) ↦ (x₂, -x₁)`. -/
def rotateClockwise (x : Fin 2 → ℝ) : Fin 2 → ℝ := ![x 1, -x 0]

/-- **Section M.I** (MWG, p. 953). The 90-degree clockwise rotation is continuous, maps the
circle `S` into itself and has no fixed point on it. -/
theorem circle_rotation_no_fixedPoint :
    Continuous rotateClockwise ∧ Set.MapsTo rotateClockwise unitCircle unitCircle ∧
      ∀ x ∈ unitCircle, rotateClockwise x ≠ x := by
  refine ⟨?_, fun x hx => ?_, fun x hx hfx => ?_⟩
  · refine continuous_pi fun k => ?_
    fin_cases k
    · exact continuous_apply 1
    · exact (continuous_apply 0).neg
  · simp only [unitCircle, Set.mem_ofPred_eq, rotateClockwise, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one] at hx ⊢
    nlinarith [hx]
  · have h0 := congrFun hfx 0
    have h1 := congrFun hfx 1
    simp only [rotateClockwise, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] at h0 h1
    simp only [unitCircle, Set.mem_ofPred_eq] at hx
    have : x 0 = 0 := by linarith
    have : x 1 = 0 := by linarith
    simp_all

/-- **Section M.I** (MWG, p. 953). The circle is not convex (the midpoint of `(1, 0)` and
`(-1, 0)` is not on it), which is why the rotation escapes Brouwer's theorem. -/
theorem circle_not_convex : ¬ Convex ℝ unitCircle := by
  intro h
  have hp : (![1, 0] : Fin 2 → ℝ) ∈ unitCircle := by simp [unitCircle]
  have hq : (![-1, 0] : Fin 2 → ℝ) ∈ unitCircle := by simp [unitCircle]
  have hm := h hp hq (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)
  simp [unitCircle] at hm

/-- **Theorem M.I.2 in a real normed space**: MWG's Kakutani theorem, with upper
hemicontinuity in the sense of Definition M.H.3, derived from LeanEconomics' closed-graph
`kakutani`. -/
theorem kakutani_mwg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {A : Set E}
    (hne : A.Nonempty) (hA : IsCompact A) (hconv : Convex ℝ A) {f : E → Set E}
    (huhc : UpperHemicontinuousMWG A f) (hfA : CorrMapsInto A A f)
    (hfne : ∀ x ∈ A, (f x).Nonempty) (hfconv : ∀ x ∈ A, Convex ℝ (f x)) :
    ∃ x ∈ A, x ∈ f x := by
  refine LeanEconomics.FixedPoint.kakutani hA hconv hne hfne hfconv hfA ?_
  refine IsSeqClosed.isClosed fun p q hp hq => ?_
  have hx : Tendsto (fun n => (p n).1) atTop (𝓝 q.1) := (continuous_fst.tendsto _).comp hq
  have hy : Tendsto (fun n => (p n).2) atTop (𝓝 q.2) := (continuous_snd.tendsto _).comp hq
  have hqA : q.1 ∈ A := hA.isClosed.mem_of_tendsto hx (Eventually.of_forall fun n => (hp n).1)
  exact ⟨hqA, huhc.1 (fun n => (p n).1) (fun n => (p n).2) q.1 q.2 (fun n => (hp n).1) hqA
    (fun n => (hp n).2) hx hy⟩

/-- **Theorem M.I.2** (Kakutani's fixed point theorem; MWG, p. 953). If `A ⊆ ℝ^N` is nonempty,
compact and convex and `f : A → A` is an upper hemicontinuous correspondence with `f(x) ⊆ A`
nonempty and convex for every `x ∈ A`, then `f` has a fixed point `x ∈ f(x)`. -/
theorem theorem_M_I_2 {N : ℕ} {A : Set (Fin N → ℝ)} (hne : A.Nonempty) (hA : IsCompact A)
    (hconv : Convex ℝ A) {f : (Fin N → ℝ) → Set (Fin N → ℝ)}
    (huhc : UpperHemicontinuousMWG A f) (hfA : CorrMapsInto A A f)
    (hfne : ∀ x ∈ A, (f x).Nonempty) (hfconv : ∀ x ∈ A, Convex ℝ (f x)) :
    ∃ x ∈ A, x ∈ f x :=
  kakutani_mwg hne hA hconv huhc hfA hfne hfconv

/-- The hypotheses of Theorem M.I.2 are satisfiable: the constant correspondence `f(x) = A` on the
cube `A = [0, 1]^N`. -/
theorem theorem_M_I_2_instance (N : ℕ) :
    let A : Set (Fin N → ℝ) := Set.pi Set.univ fun _ => Set.Icc 0 1
    A.Nonempty ∧ IsCompact A ∧ Convex ℝ A ∧ UpperHemicontinuousMWG A (fun _ => A) ∧
      CorrMapsInto A A (fun _ => A) ∧ (∀ x ∈ A, ((fun _ => A) x).Nonempty) ∧
      ∀ x ∈ A, Convex ℝ ((fun _ => A) x) := by
  intro A
  have hAc : IsCompact A := isCompact_univ_pi fun _ => isCompact_Icc
  have hne : A.Nonempty := ⟨0, fun k _ => by simp⟩
  have hconv : Convex ℝ A := convex_pi fun _ _ => convex_Icc 0 1
  refine ⟨hne, hAc, hconv, ?_, fun _ _ => le_rfl, fun _ _ => hne, fun _ _ => hconv⟩
  refine (uhc_iff_hasClosedGraph_of_isCompact hAc (fun _ _ => le_rfl)).2 ?_
  intro xs ys x y _ _ hys _ hy
  exact hAc.isClosed.mem_of_tendsto hy (Eventually.of_forall hys)

/-- The correspondence of Figure M.I.2(b): `{1}` on `[0, 1/2)`, `{0, 1}` at `1/2`, `{0}` on
`(1/2, 1]`. -/
noncomputable def figM12b (x : ℝ) : Set ℝ :=
  if x < 1 / 2 then {1} else if x = 1 / 2 then {0, 1} else {0}

/-- **Figure M.I.2(b)** (MWG, p. 953). Convex values are indispensable: the correspondence
`figM12b` on `[0, 1]` is upper hemicontinuous with nonempty values in `[0, 1]`, its value at
`1/2` is not convex, and it has no fixed point. -/
theorem figure_M_I_2b :
    UpperHemicontinuousMWG (Set.Icc (0 : ℝ) 1) figM12b ∧
      CorrMapsInto (Set.Icc (0 : ℝ) 1) (Set.Icc 0 1) figM12b ∧
      (∀ x ∈ Set.Icc (0 : ℝ) 1, (figM12b x).Nonempty) ∧ ¬ Convex ℝ (figM12b (1 / 2)) ∧
      ∀ x ∈ Set.Icc (0 : ℝ) 1, x ∉ figM12b x := by
  have hY : CorrMapsInto (Set.Icc (0 : ℝ) 1) (Set.Icc 0 1) figM12b := by
    intro x _ y hy
    unfold figM12b at hy
    split_ifs at hy
    · simp only [Set.mem_singleton_iff] at hy; subst hy; norm_num
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl <;> norm_num
    · simp only [Set.mem_singleton_iff] at hy; subst hy; norm_num
  refine ⟨(uhc_iff_hasClosedGraph_of_isCompact isCompact_Icc hY).2 ?_, hY, ?_, ?_, ?_⟩
  · refine hasClosedGraph_of_isClosed (C := (Set.Iic (1 / 2) ×ˢ {1}) ∪ (Set.Ici (1 / 2) ×ˢ {0}))
      ((isClosed_Iic.prod isClosed_singleton).union (isClosed_Ici.prod isClosed_singleton))
      fun x _ y => ?_
    unfold figM12b
    split_ifs with h1 h2
    · simp only [Set.mem_singleton_iff, Set.mem_union, Set.mem_prod, Set.mem_Iic, Set.mem_Ici]
      constructor
      · intro hy; exact Or.inl ⟨h1.le, hy⟩
      · rintro (⟨_, hy⟩ | ⟨hx, _⟩)
        · exact hy
        · linarith
    · subst h2
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union, Set.mem_prod,
        Set.mem_Iic, Set.mem_Ici, le_refl, true_and]
      tauto
    · simp only [Set.mem_singleton_iff, Set.mem_union, Set.mem_prod, Set.mem_Iic, Set.mem_Ici]
      constructor
      · intro hy; exact Or.inr ⟨by push Not at h1; exact h1, hy⟩
      · rintro (⟨hx, _⟩ | ⟨_, hy⟩)
        · exact absurd (le_antisymm hx (not_lt.1 h1)) h2
        · exact hy
  · intro x _
    unfold figM12b
    split_ifs <;> simp
  · intro h
    have h0 : (0 : ℝ) ∈ figM12b (1 / 2) := by simp [figM12b]
    have h1 : (1 : ℝ) ∈ figM12b (1 / 2) := by simp [figM12b]
    have := h h0 h1 (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    simp [figM12b] at this
  · intro x hx hfx
    unfold figM12b at hfx
    split_ifs at hfx with h1 h2
    · simp only [Set.mem_singleton_iff] at hfx; linarith
    · subst h2; norm_num at hfx
    · simp only [Set.mem_singleton_iff] at hfx; subst hfx; norm_num at h1

/-- **Theorem M.I.3** (Tarski's fixed point theorem; MWG, p. 953). If `f : [0, 1]^N → [0, 1]^N`
is nondecreasing (`f(x') ≥ f(x)` whenever `x' ≥ x`), then `f` has a fixed point. Continuity is
not assumed. -/
theorem theorem_M_I_3 {N : ℕ} {f : (Fin N → ℝ) → (Fin N → ℝ)}
    (hmaps : Set.MapsTo f (Set.pi Set.univ fun _ => Set.Icc 0 1)
      (Set.pi Set.univ fun _ => Set.Icc 0 1))
    (hmono : MonotoneOn f (Set.pi Set.univ fun _ => Set.Icc 0 1)) :
    ∃ x ∈ Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1), x = f x := by
  have hfact : Fact ((0 : ℝ) ≤ 1) := ⟨zero_le_one⟩
  set C : Set (Fin N → ℝ) := Set.pi Set.univ fun _ => Set.Icc 0 1 with hC
  have hval : ∀ y : Fin N → Set.Icc (0 : ℝ) 1, (fun k => (y k : ℝ)) ∈ C :=
    fun y k _ => (y k).2
  let g : (Fin N → Set.Icc (0 : ℝ) 1) →o (Fin N → Set.Icc (0 : ℝ) 1) :=
    { toFun := fun y k => ⟨f (fun k => (y k : ℝ)) k, hmaps (hval y) k (Set.mem_univ k)⟩
      monotone' := fun y y' hyy' k => by
        have : (fun k => (y k : ℝ)) ≤ fun k => (y' k : ℝ) := fun k => hyy' k
        exact hmono (hval y) (hval y') this k }
  refine ⟨fun k => (OrderHom.lfp g k : ℝ), hval _, ?_⟩
  funext k
  have h := congrFun (OrderHom.map_lfp g) k
  exact (congrArg Subtype.val h).symm

/-- **Figure M.I.3** (MWG, p. 953). A nondecreasing, discontinuous self-map of `[0, 1]` (`1/4`
below `1/2`, `3/4` from `1/2` on) satisfies the hypotheses of Theorem M.I.3 and has fixed
points, although it is not continuous. -/
theorem figure_M_I_3 :
    let f : (Fin 1 → ℝ) → (Fin 1 → ℝ) := fun x _ => if x 0 < 1 / 2 then 1 / 4 else 3 / 4
    Set.MapsTo f (Set.pi Set.univ fun _ => Set.Icc 0 1) (Set.pi Set.univ fun _ => Set.Icc 0 1) ∧
      MonotoneOn f (Set.pi Set.univ fun _ => Set.Icc 0 1) ∧ ¬ Continuous f ∧
      f (fun _ => 1 / 4) = (fun _ => 1 / 4) := by
  intro f
  refine ⟨fun x _ k _ => ?_, fun x _ y _ hxy k => ?_, fun hc => ?_, ?_⟩
  · simp only [f]
    split_ifs <;> norm_num
  · simp only [f]
    have := hxy 0
    split_ifs with h1 h2 <;> norm_num
    linarith
  · have hc0 : Continuous fun t : ℝ => f (fun _ => t) 0 :=
      (continuous_apply 0).comp (hc.comp (continuous_pi fun _ => continuous_id))
    have hlim : Tendsto (fun t : ℝ => f (fun _ => t) 0) (𝓝[<] (1 / 2)) (𝓝 (1 / 4)) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [f]
      rw [Set.mem_Iio] at ht
      simp only [ht, ↓reduceIte]
    have hval := hc0.continuousAt (x := 1 / 2)
    have h2 := tendsto_nhds_unique (hval.tendsto.mono_left nhdsWithin_le_nhds) hlim
    simp only [f, lt_irrefl, ↓reduceIte] at h2
    norm_num at h2
  · funext k
    simp only [f]
    norm_num

end MWG.SimultaneousMoveGames
