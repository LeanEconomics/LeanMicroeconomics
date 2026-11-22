/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.Perm
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Coalitional bargaining: the Shapley value

MWG, Section 22.F, pp. 846-848: games in characteristic form, Definitions 22.F.1-22.F.6, the
claim `∑ᵢ g_{v,π}(i) = v(I)` (p. 848), and Exercises 22.F.2, 22.F.3(a), 22.F.4(a).

A game in characteristic form on the agents `Fin n` is `v : Finset (Fin n) → ℝ` with
`v(∅) = 0`. An ordering of the agents is a permutation `π`; agent `i`'s marginal contribution is
`g_{v,π}(i) = v({h : π(h) ≤ π(i)}) - v({h : π(h) < π(i)})` (`margContrib`), and the Shapley value
is the average over the `n!` orderings (Definition 22.F.6). We prove that marginal contributions
add up to `v(I)` along every ordering, and that the Shapley value is Paretian, independent of
utility origins and of common changes of units, symmetric, satisfies the dummy axiom
(Exercise 22.F.2) and is linear (Exercise 22.F.3(a)); and that every cooperative solution with
the properties of Exercise 22.F.4(a) gives the unanimity game `u_T` the values `v(I)/|T|` on `T`
and `0` off `T`.
-/

namespace MWG.WelfareBargaining

open Finset

variable {n : ℕ}

/-- A game in characteristic form (MWG, p. 846): the worth `v(S)` of every coalition. -/
abbrev Game (n : ℕ) := Finset (Fin n) → ℝ

/-- The predecessors of `i` in the ordering `π`: `{h : π(h) < π(i)}`. -/
def preds (π' : Equiv.Perm (Fin n)) (i : Fin n) : Finset (Fin n) :=
  univ.filter fun h => π' h < π' i

/-- **Section 22.F** (MWG, p. 847). Agent `i`'s marginal contribution in the ordering `π`:
`g_{v,π}(i) = v({h : π(h) ≤ π(i)}) - v({h : π(h) < π(i)})`. -/
def margContrib (v : Game n) (π' : Equiv.Perm (Fin n)) (i : Fin n) : ℝ :=
  v (insert i (preds π' i)) - v (preds π' i)

/-- **Definition 22.F.6** (MWG, p. 848). The Shapley value
`f_{s,i}(v) = (1/I!) ∑_π g_{v,π}(i)`. -/
noncomputable def shapley (v : Game n) (i : Fin n) : ℝ :=
  (1 / (Nat.factorial n : ℝ)) * ∑ π' : Equiv.Perm (Fin n), margContrib v π' i

/-- The first `m` agents of the ordering `π`. -/
def initSeg (π' : Equiv.Perm (Fin n)) (m : ℕ) : Finset (Fin n) :=
  univ.filter fun h => (π' h : ℕ) < m

theorem preds_eq_initSeg (π' : Equiv.Perm (Fin n)) (i : Fin n) :
    preds π' i = initSeg π' (π' i) := by
  ext h; simp only [preds, initSeg, mem_filter, mem_univ, true_and]; exact Fin.lt_def

theorem insert_preds_eq_initSeg (π' : Equiv.Perm (Fin n)) (i : Fin n) :
    insert i (preds π' i) = initSeg π' (π' i + 1) := by
  ext h
  simp only [mem_insert, preds, initSeg, mem_filter, mem_univ, true_and, Fin.lt_def]
  constructor
  · rintro (rfl | h); · omega
    · omega
  · intro hh
    rcases Nat.lt_succ_iff_lt_or_eq.1 hh with h' | h'
    · exact Or.inr h'
    · exact Or.inl (π'.injective (Fin.ext h'))

theorem initSeg_zero (π' : Equiv.Perm (Fin n)) : initSeg π' 0 = ∅ := by
  ext h; simp [initSeg]

theorem initSeg_n (π' : Equiv.Perm (Fin n)) : initSeg π' n = univ := by
  ext h; simp [initSeg]

/-- **Section 22.F** (MWG, p. 848). Along every ordering the marginal contributions add up to
`v(I)`: `∑ᵢ g_{v,π}(i) = v(I)` (with `v(∅) = 0`). -/
theorem sum_margContrib (v : Game n) (hv : v ∅ = 0) (π' : Equiv.Perm (Fin n)) :
    ∑ i, margContrib v π' i = v univ := by
  have : ∑ i, margContrib v π' i = ∑ k : Fin n, (v (initSeg π' (k + 1)) - v (initSeg π' k)) := by
    rw [← Equiv.sum_comp π'.symm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [margContrib, insert_preds_eq_initSeg, preds_eq_initSeg, Equiv.apply_symm_apply]
  rw [this, Fin.sum_univ_eq_sum_range (fun k => v (initSeg π' (k + 1)) - v (initSeg π' k)),
    Finset.sum_range_sub (fun k => v (initSeg π' k)), initSeg_n, initSeg_zero, hv, sub_zero]

/-- **Definition 22.F.1** (MWG, p. 847). A cooperative solution is feasible: `∑ fᵢ(v) ≤ v(I)`. -/
def IsCoopSolution (f : Game n → Fin n → ℝ) : Prop := ∀ v, v ∅ = 0 → ∑ i, f v i ≤ v univ

/-- **Definition 22.F.2** (MWG, p. 847). Independence of utility origins and of common changes of
utility units: `v(S) = βv'(S) + ∑_{i∈S} αᵢ` implies `f(v) = βf(v') + α`. -/
def CoopIUO (f : Game n → Fin n → ℝ) : Prop :=
  ∀ v v' : Game n, ∀ (β : ℝ) (α : Fin n → ℝ), 0 < β → v' ∅ = 0 →
    (∀ S, v S = β * v' S + ∑ i ∈ S, α i) → ∀ i, f v i = β * f v' i + α i

/-- **Definition 22.F.3** (MWG, p. 847). Pareto: `∑ fᵢ(v) = v(I)`. -/
def CoopPareto (f : Game n → Fin n → ℝ) : Prop := ∀ v, v ∅ = 0 → ∑ i, f v i = v univ

/-- **Definition 22.F.4** (MWG, p. 847). Symmetry: if `v'(S) = v(σ(S))` for all `S` then
`fᵢ(v') = f_{σ(i)}(v)`. -/
def CoopSymmetric (f : Game n → Fin n → ℝ) : Prop :=
  ∀ (v : Game n) (σ : Equiv.Perm (Fin n)), v ∅ = 0 → ∀ i,
    f (fun S => v (S.map σ.toEmbedding)) i = f v (σ i)

/-- **Definition 22.F.5** (MWG, p. 847). The dummy axiom: if `v(S ∪ {i}) = v(S)` for every `S`
then `fᵢ(v) = 0`. -/
def CoopDummy (f : Game n → Fin n → ℝ) : Prop :=
  ∀ (v : Game n) (i : Fin n), v ∅ = 0 → (∀ S, v (insert i S) = v S) → f v i = 0

/-- Linearity (Exercise 22.F.3): `f(v + v') = f(v) + f(v')`. -/
def CoopLinear (f : Game n → Fin n → ℝ) : Prop :=
  ∀ v v' : Game n, v ∅ = 0 → v' ∅ = 0 → f (v + v') = f v + f v'

theorem shapley_pareto (v : Game n) (hv : v ∅ = 0) : ∑ i, shapley v i = v univ := by
  simp only [shapley, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [sum_margContrib v hv, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- **Exercise 22.F.3(a)** (MWG, p. 855). The Shapley value is linear in the game. -/
theorem exercise_22_F_3a (v v' : Game n) : shapley (v + v') = shapley v + shapley v' := by
  funext i
  simp only [shapley, Pi.add_apply, margContrib, ← mul_add, ← Finset.sum_add_distrib]
  congr 1; exact Finset.sum_congr rfl fun π' _ => by ring

theorem shapley_smul (c : ℝ) (v : Game n) : shapley (c • v) = c • shapley v := by
  funext i
  simp only [shapley, Pi.smul_apply, smul_eq_mul, margContrib, Finset.mul_sum]
  exact Finset.sum_congr rfl fun π' _ => by ring

/-- The Shapley value of an additive game `a(S) = ∑_{i∈S} αᵢ` is `α`. -/
theorem shapley_additive (α : Fin n → ℝ) : shapley (fun S => ∑ i ∈ S, α i) = α := by
  funext i
  have hm : ∀ π' : Equiv.Perm (Fin n), margContrib (fun S => ∑ j ∈ S, α j) π' i = α i := by
    intro π'
    simp only [margContrib]
    rw [Finset.sum_insert (by simp [preds])]
    ring
  simp only [shapley, hm, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul]
  field_simp

/-- **Exercise 22.F.2** (MWG, p. 855), dummy axiom. -/
theorem shapley_dummy : CoopDummy (shapley (n := n)) := by
  intro v i _ hd
  have : ∀ π', margContrib v π' i = 0 := fun π' => by simp [margContrib, hd]
  simp [shapley, this]

/-- **Exercise 22.F.2** (MWG, p. 855), independence of utility origins and of common changes of
units. -/
theorem shapley_IUO : CoopIUO (shapley (n := n)) := by
  intro v v' β α _ _ hrel i
  have hv : v = β • v' + fun S => ∑ j ∈ S, α j := funext fun S => by
    simp [hrel S, smul_eq_mul]
  rw [hv, exercise_22_F_3a, shapley_smul, shapley_additive]
  simp

theorem map_insert_perm (σ : Equiv.Perm (Fin n)) (i : Fin n) (S : Finset (Fin n)) :
    (insert i S).map σ.toEmbedding = insert (σ i) (S.map σ.toEmbedding) := by
  simp [Finset.map_insert]

theorem preds_map (π' σ : Equiv.Perm (Fin n)) (i : Fin n) :
    (preds π' i).map σ.toEmbedding = preds (σ.symm.trans π') (σ i) := by
  ext g
  simp only [preds, mem_map_equiv, mem_filter, mem_univ, true_and, Equiv.trans_apply,
    Equiv.symm_apply_apply]

/-- **Exercise 22.F.2** (MWG, p. 855), symmetry. -/
theorem shapley_symmetric : CoopSymmetric (shapley (n := n)) := by
  intro v σ _ i
  simp only [shapley]
  congr 1
  have key : ∀ π' : Equiv.Perm (Fin n), margContrib (fun S => v (S.map σ.toEmbedding)) π' i =
      margContrib v (π' * σ.symm) (σ i) := by
    intro π'
    simp only [margContrib, map_insert_perm, preds_map]
    rfl
  simp only [key]
  exact Equiv.sum_comp (Equiv.mulRight σ.symm) (fun ρ => margContrib v ρ (σ i))

/-- **Exercise 22.F.2** (MWG, p. 855). The Shapley value satisfies invariance to independent
changes of origins and common changes of units, Pareto, symmetry and the dummy axiom; it is
feasible, hence a cooperative solution. -/
theorem exercise_22_F_2 :
    IsCoopSolution (shapley (n := n)) ∧ CoopIUO (shapley (n := n)) ∧
      CoopPareto (shapley (n := n)) ∧ CoopSymmetric (shapley (n := n)) ∧
      CoopDummy (shapley (n := n)) :=
  ⟨fun v hv => (shapley_pareto v hv).le, shapley_IUO, shapley_pareto, shapley_symmetric,
    shapley_dummy⟩

/-- **Exercise 22.F.4** (MWG, p. 855). The unanimity game of `T` with worth `c`:
`u(S) = c` if `T ⊆ S` and `0` otherwise. -/
noncomputable def unanimity (T : Finset (Fin n)) (c : ℝ) : Game n := by
  classical
  exact fun S => if T ⊆ S then c else 0

/-- **Exercise 22.F.4(a)** (MWG, p. 855). For a nonempty `T`, a Paretian, symmetric cooperative
solution satisfying the dummy axiom assigns `c/|T|` to the members of `T` and `0` to the others
in the unanimity game `u_T`. -/
theorem exercise_22_F_4a {f : Game n → Fin n → ℝ} (hP : CoopPareto f) (hS : CoopSymmetric f)
    (hD : CoopDummy f) (T : Finset (Fin n)) (hT : T.Nonempty) (c : ℝ) (i : Fin n) :
    f (unanimity T c) i = if i ∈ T then c / T.card else 0 := by
  classical
  have h0 : unanimity T c ∅ = 0 := by
    simp [unanimity, Finset.subset_empty, hT.ne_empty]
  -- non-members are dummies
  have hdummy : ∀ j ∉ T, f (unanimity T c) j = 0 := by
    intro j hj
    refine hD _ j h0 fun S => ?_
    simp only [unanimity]
    congr 1
    exact propext ⟨fun h => fun x hx => (Finset.mem_insert.1 (h hx)).resolve_left
      (fun e => hj (e ▸ hx)), fun h => h.trans (Finset.subset_insert _ _)⟩
  -- members are treated equally
  have hequal : ∀ j ∈ T, ∀ k ∈ T, f (unanimity T c) j = f (unanimity T c) k := by
    intro j hj k hk
    have hinv : (fun S => unanimity T c (S.map (Equiv.swap j k).toEmbedding)) =
        unanimity T c := by
      funext S
      simp only [unanimity]
      congr 1
      refine propext ⟨fun h x hx => ?_, fun h x hx => ?_⟩
      · have := h (show Equiv.swap j k x ∈ T from by
          rcases eq_or_ne x j with rfl | hxj
          · simpa using hk
          rcases eq_or_ne x k with rfl | hxk
          · simpa using hj
          · rwa [Equiv.swap_apply_of_ne_of_ne hxj hxk])
        simpa using this
      · simp only [mem_map_equiv, Equiv.symm_swap]
        apply h
        rcases eq_or_ne x j with rfl | hxj
        · simpa using hk
        rcases eq_or_ne x k with rfl | hxk
        · simpa using hj
        · rwa [Equiv.swap_apply_of_ne_of_ne hxj hxk]
    have := hS (unanimity T c) (Equiv.swap j k) h0 j
    rw [hinv, Equiv.swap_apply_left] at this
    exact this
  have hsum := hP _ h0
  have hval : unanimity T c univ = c := by simp [unanimity]
  obtain ⟨t, ht⟩ := hT
  have hsplit : ∑ j, f (unanimity T c) j = T.card * f (unanimity T c) t := by
    rw [← Finset.sum_subset (Finset.subset_univ T) fun j _ hj => hdummy j hj]
    rw [Finset.sum_congr rfl fun j hj => hequal j hj t ht]
    simp
  have hcard : (0 : ℝ) < T.card := Nat.cast_pos.2 (Finset.card_pos.2 ⟨t, ht⟩)
  split_ifs with hi
  · rw [hequal i hi t ht]
    rw [hsplit, hval] at hsum
    field_simp
    linarith
  · exact hdummy i hi

/-- The Harsanyi dividend `d_T(v) = ∑_{R ⊆ T} (-1)^{|T|-|R|} v(R)`: the coefficient of the
unanimity game `u_T` in `v` (Exercise 22.F.4). -/
noncomputable def dividend (v : Game n) (T : Finset (Fin n)) : ℝ :=
  ∑ R ∈ T.powerset, (-1 : ℝ) ^ (T.card - R.card) * v R

theorem alt_sum_between (R S : Finset (Fin n)) (hRS : R ⊆ S) :
    ∑ T ∈ S.powerset.filter (fun T => R ⊆ T), (-1 : ℝ) ^ (T.card - R.card) =
      if S = R then 1 else 0 := by
  classical
  have hbij : ∑ U ∈ (S \ R).powerset, (-1 : ℝ) ^ U.card =
      ∑ T ∈ S.powerset.filter (fun T => R ⊆ T), (-1 : ℝ) ^ (T.card - R.card) := by
    refine Finset.sum_nbij' (fun U => U ∪ R) (fun T => T \ R) ?_ ?_ ?_ ?_ ?_
    · intro U hU
      simp only [mem_powerset] at hU
      simp only [mem_filter, mem_powerset]
      exact ⟨union_subset (hU.trans sdiff_subset) hRS, subset_union_right⟩
    · intro T hT
      simp only [mem_filter, mem_powerset] at hT
      simp only [mem_powerset]
      exact sdiff_subset_sdiff hT.1 le_rfl
    · intro U hU
      simp only [mem_powerset] at hU
      exact union_sdiff_cancel_right (disjoint_of_subset_left hU disjoint_sdiff_self_left)
    · intro T hT
      simp only [mem_filter, mem_powerset] at hT
      exact sdiff_union_of_subset hT.2
    · intro U hU
      simp only [mem_powerset] at hU
      rw [card_union_of_disjoint (disjoint_of_subset_left hU disjoint_sdiff_self_left),
        Nat.add_sub_cancel]
  rw [← hbij]
  have hz : ∑ U ∈ (S \ R).powerset, (-1 : ℝ) ^ U.card =
      ((∑ U ∈ (S \ R).powerset, (-1 : ℤ) ^ U.card : ℤ) : ℝ) := by push_cast; rfl
  rw [hz, sum_powerset_neg_one_pow_card]
  have : S \ R = ∅ ↔ S = R :=
    ⟨fun h => le_antisymm (sdiff_eq_empty_iff_subset.1 h) hRS, fun h => by simp [h]⟩
  by_cases h : S = R
  · simp [h]
  · simp [show ¬S \ R = ∅ from fun h' => h (this.1 h'), h]

/-- **Exercise 22.F.4** (MWG, p. 855). Möbius inversion: every game is the sum of unanimity
games weighted by its dividends, `v(S) = ∑_{T ⊆ S} d_T(v)`. -/
theorem sum_dividend (v : Game n) (S : Finset (Fin n)) :
    ∑ T ∈ S.powerset, dividend v T = v S := by
  classical
  simp only [dividend]
  rw [Finset.sum_comm' (t' := S.powerset) (s' := fun R => S.powerset.filter (fun T => R ⊆ T))
    (fun T R => by
      simp only [mem_powerset, mem_filter]
      exact ⟨fun h => ⟨⟨h.1, h.2⟩, h.2.trans h.1⟩, fun h => ⟨h.1.1, h.1.2⟩⟩)]
  have : ∀ R ∈ S.powerset, ∑ T ∈ S.powerset.filter (fun T => R ⊆ T),
      (-1 : ℝ) ^ (T.card - R.card) * v R = if S = R then v R else 0 := by
    intro R hR
    rw [← Finset.sum_mul, alt_sum_between R S (mem_powerset.1 hR)]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq]
  simp

/-- The sum of the unanimity games `u_T(d_T(v))` over nonempty `T` is `v` (if `v(∅) = 0`). -/
theorem eq_sum_unanimity (v : Game n) (hv : v ∅ = 0) :
    v = fun S => ∑ T ∈ (univ.powerset.filter fun T : Finset (Fin n) => T.Nonempty),
      unanimity T (dividend v T) S := by
  classical
  funext S
  rw [← sum_dividend v S]
  simp only [unanimity]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.filter_filter]
  have hd0 : dividend v ∅ = 0 := by simp [dividend, hv]
  rw [← Finset.sum_filter_add_sum_filter_not S.powerset (fun T => T.Nonempty)]
  have hempty : ∑ T ∈ S.powerset.filter (fun T => ¬T.Nonempty), dividend v T = 0 := by
    refine Finset.sum_eq_zero fun T hT => ?_
    simp only [mem_filter, not_nonempty_iff_eq_empty] at hT
    rw [hT.2, hd0]
  rw [hempty, add_zero]
  apply Finset.sum_congr
  · ext T; simp [and_comm]
  · intro _ _; rfl

/-- The value determined by the dividends: `∑_{T ∋ i} d_T(v)/|T|`. -/
noncomputable def dividendValue (v : Game n) (i : Fin n) : ℝ :=
  ∑ T ∈ (univ.powerset.filter fun T : Finset (Fin n) => T.Nonempty),
    if i ∈ T then dividend v T / T.card else 0

theorem unanimity_empty {T : Finset (Fin n)} (hT : T.Nonempty) (c : ℝ) :
    unanimity T c ∅ = 0 := by
  classical
  simp [unanimity, Finset.subset_empty, hT.ne_empty]

theorem dividend_add (v w : Game n) (T : Finset (Fin n)) :
    dividend (v + w) T = dividend v T + dividend w T := by
  simp only [dividend, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- A Paretian, symmetric, linear cooperative solution with the dummy axiom is given by the
dividend formula. -/
theorem value_eq_dividendValue {f : Game n → Fin n → ℝ} (hP : CoopPareto f)
    (hS : CoopSymmetric f) (hD : CoopDummy f) (hL : CoopLinear f) (v : Game n) (hv : v ∅ = 0) :
    f v = dividendValue v := by
  classical
  have hzero : f 0 = 0 := by
    have := hL 0 0 rfl rfl
    simp only [add_zero] at this
    have h2 : f 0 + f 0 = f 0 + 0 := by rw [← this, add_zero]
    exact add_left_cancel h2
  have key : ∀ A ⊆ (univ.powerset.filter fun T : Finset (Fin n) => T.Nonempty),
      f (fun S => ∑ T ∈ A, unanimity T (dividend v T) S) =
        ∑ T ∈ A, f (unanimity T (dividend v T)) := by
    intro A
    induction A using Finset.induction_on with
    | empty => intro _; simp only [Finset.sum_empty]; exact hzero
    | insert T A hTA ih =>
      intro hsub
      have hT : T.Nonempty := (mem_filter.1 (hsub (mem_insert_self T A))).2
      have hA : A ⊆ _ := (subset_insert T A).trans hsub
      have hsplit : (fun S => ∑ T' ∈ insert T A, unanimity T' (dividend v T') S) =
          unanimity T (dividend v T) + fun S => ∑ T' ∈ A, unanimity T' (dividend v T') S := by
        funext S; simp [Finset.sum_insert hTA]
      have h0 : (fun S => ∑ T' ∈ A, unanimity T' (dividend v T') S) ∅ = 0 :=
        Finset.sum_eq_zero fun T' hT' =>
          unanimity_empty (mem_filter.1 (hA hT')).2 _
      rw [hsplit, hL _ _ (unanimity_empty hT _) h0, ih hA, Finset.sum_insert hTA]
  conv_lhs => rw [eq_sum_unanimity v hv]
  rw [key _ subset_rfl]
  funext i
  simp only [Finset.sum_apply, dividendValue]
  refine Finset.sum_congr rfl fun T hT => ?_
  exact exercise_22_F_4a hP hS hD T (mem_filter.1 hT).2 _ i

/-- **Exercise 22.F.4(c)** (MWG, p. 855). The Shapley value is the only cooperative solution
that is independent of utility origins and common units, Paretian, symmetric, satisfies the
dummy axiom and is linear: any such `f` agrees with the Shapley value on every game. -/
theorem exercise_22_F_4c {f : Game n → Fin n → ℝ} (hP : CoopPareto f) (hS : CoopSymmetric f)
    (hD : CoopDummy f) (hL : CoopLinear f) (v : Game n) (hv : v ∅ = 0) : f v = shapley v := by
  rw [value_eq_dividendValue hP hS hD hL v hv,
    value_eq_dividendValue shapley_pareto shapley_symmetric shapley_dummy
      (fun v w _ _ => exercise_22_F_3a v w) v hv]

/-- Weak linearity (Exercise 22.F.4(b)): adding `α u_T` adds `α/|T|` to the members of `T`. -/
def CoopWeaklyLinear (f : Game n → Fin n → ℝ) : Prop :=
  ∀ (v : Game n) (T : Finset (Fin n)), v ∅ = 0 → T.Nonempty → ∀ α : ℝ,
    f (v + unanimity T α) = f v + fun i => if i ∈ T then α / T.card else 0

/-- **Exercise 22.F.4(b)** (MWG, p. 855). With the properties of (a), weak linearity implies
linearity: the solution is then given by the dividend formula, which is additive. -/
theorem exercise_22_F_4b {f : Game n → Fin n → ℝ} (hP : CoopPareto f) (hS : CoopSymmetric f)
    (hD : CoopDummy f) (hW : CoopWeaklyLinear f) : CoopLinear f := by
  classical
  have hzero : f 0 = 0 := by
    funext i
    have h := exercise_22_F_4a hP hS hD univ ⟨i, mem_univ i⟩ 0 i
    have e : unanimity (univ : Finset (Fin n)) 0 = 0 := by funext S; simp [unanimity]
    rw [e] at h; simpa using h
  have hval : ∀ v : Game n, v ∅ = 0 → f v = dividendValue v := by
    intro v hv
    have key : ∀ A ⊆ (univ.powerset.filter fun T : Finset (Fin n) => T.Nonempty),
        f (fun S => ∑ T ∈ A, unanimity T (dividend v T) S) =
          fun i => ∑ T ∈ A, if i ∈ T then dividend v T / T.card else 0 := by
      intro A
      induction A using Finset.induction_on with
      | empty => intro _; simp only [Finset.sum_empty]; exact hzero
      | insert T A hTA ih =>
        intro hsub
        have hT : T.Nonempty := (mem_filter.1 (hsub (mem_insert_self T A))).2
        have hA : A ⊆ _ := (subset_insert T A).trans hsub
        have hsplit : (fun S => ∑ T' ∈ insert T A, unanimity T' (dividend v T') S) =
            (fun S => ∑ T' ∈ A, unanimity T' (dividend v T') S) + unanimity T (dividend v T) := by
          funext S; simp [Finset.sum_insert hTA, add_comm]
        have h0 : (fun S => ∑ T' ∈ A, unanimity T' (dividend v T') S) ∅ = 0 :=
          Finset.sum_eq_zero fun T' hT' => unanimity_empty (mem_filter.1 (hA hT')).2 _
        rw [hsplit, hW _ T h0 hT, ih hA]
        funext i
        simp [Finset.sum_insert hTA, add_comm]
    conv_lhs => rw [eq_sum_unanimity v hv]
    rw [key _ subset_rfl]
    rfl
  intro v w hv hw
  have hvw : (v + w) ∅ = 0 := by simp [hv, hw]
  rw [hval _ hvw, hval _ hv, hval _ hw]
  funext i
  simp only [dividendValue, Pi.add_apply, ← Finset.sum_add_distrib, dividend_add]
  refine Finset.sum_congr rfl fun T _ => ?_
  split_ifs <;> ring

end MWG.WelfareBargaining
