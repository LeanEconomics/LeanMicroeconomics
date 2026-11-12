/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.BigOperators.Ring.Finset
import ChoicePreferenceUtility.Basic

/-!
# Stochastic choice rationalized by random preferences

MWG, Exercise 1.D.5, p. 16.

`X = {x, y, z}` is `Fin 3` (`x = 0`, `y = 1`, `z = 2`) and `𝓑 = {{x,y}, {y,z}, {z,x}}`. The six
strict preference relations on `X` are encoded by the permutations `σ` of `Fin 3`, read as
rank assignments: `a ≻_σ b` iff `σ a < σ b`. Each such relation is irreflexive, transitive and
total on distinct alternatives (`rankPrefers_strictTotal`), and distinct permutations give
distinct relations (`rankPrefers_injective`). A stochastic choice function on the pairs is
`c a b = C_a({a, b})`. It is rationalized by preferences if a probability distribution `Pr` on
the six relations gives `c a b = Pr{≻ : a ≻ b}` for every pair of distinct alternatives.

For the cyclic function `C({x,y}) = C({y,z}) = C({z,x}) = (α, 1 - α)` we prove: it is
rationalizable iff `1/3 ≤ α ≤ 2/3` (`cyclicChoice_rationalizable_iff`). Hence (a) `α = 1/2` is
rationalizable, (b) `α = 1/4` is not, and (c) on `0 < α < 1` the function switches between
rationalizable and nonrationalizable exactly at `α = 1/3` and `α = 2/3`. The key fact is that
every strict ordering ranks exactly one or two of the three cyclic pairs `x ≻ y`, `y ≻ z`,
`z ≻ x` the "cyclic" way, so `3α = E[count] ∈ [1, 2]`.
-/

namespace MWG.PreferenceChoice

/-- The strict preference relation encoded by a ranking `σ`: `a ≻ b` iff `a` has the smaller
rank. -/
abbrev rankPrefers (σ : Equiv.Perm (Fin 3)) (a b : Fin 3) : Prop := σ a < σ b

/-- Each ranking gives a strict preference relation: irreflexive, transitive, and total on
distinct alternatives. -/
theorem rankPrefers_strictTotal (σ : Equiv.Perm (Fin 3)) :
    (∀ a, ¬rankPrefers σ a a) ∧
      (∀ a b c, rankPrefers σ a b → rankPrefers σ b c → rankPrefers σ a c) ∧
      (∀ a b, a ≠ b → rankPrefers σ a b ∨ rankPrefers σ b a) := by
  refine ⟨fun a => lt_irrefl _, fun a b c => lt_trans, fun a b hab => ?_⟩
  exact lt_or_gt_of_ne (fun h => hab (σ.injective h))

/-- Distinct rankings give distinct strict preference relations, so the six permutations are
the six strict preference relations of the exercise. -/
theorem rankPrefers_injective : Function.Injective rankPrefers := by
  have key : ∀ σ τ : Equiv.Perm (Fin 3), (∀ a b, σ a < σ b ↔ τ a < τ b) → σ = τ := by decide
  intro σ τ h
  exact key σ τ fun a b => by
    have := congrFun (congrFun h a) b
    exact Iff.of_eq this

/-- A stochastic choice function `c a b = C_a({a, b})` on the three pairs is rationalized by
preferences if some probability distribution on the six strict relations gives
`c a b = Pr{≻ : a ≻ b}` for all distinct `a, b`. -/
def StochasticRationalizable (c : Fin 3 → Fin 3 → ℝ) : Prop :=
  ∃ Pr : Equiv.Perm (Fin 3) → ℝ, (∀ σ, 0 ≤ Pr σ) ∧ ∑ σ, Pr σ = 1 ∧
    ∀ a b, a ≠ b → c a b = ∑ σ ∈ Finset.univ.filter (fun σ => rankPrefers σ a b), Pr σ

/-- The cyclic stochastic choice function `C({x,y}) = C({y,z}) = C({z,x}) = (α, 1 - α)`:
`C_a({a, a + 1}) = α` and `C_{a+1}({a, a + 1}) = 1 - α` (indices mod 3). -/
def cyclicChoice (α : ℝ) (a b : Fin 3) : ℝ := if b = a + 1 then α else 1 - α

/-- The cyclic function is a stochastic choice function on `𝓑` when `0 ≤ α ≤ 1`: frequencies
are nonnegative and sum to one on each pair. -/
theorem cyclicChoice_valid {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) (a b : Fin 3) (hab : a ≠ b) :
    0 ≤ cyclicChoice α a b ∧ cyclicChoice α a b + cyclicChoice α b a = 1 := by
  have key : ∀ a b : Fin 3, a ≠ b → (b = a + 1 ∧ ¬a = b + 1) ∨ (¬b = a + 1 ∧ a = b + 1) := by
    decide
  rcases key a b hab with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
  · simp only [cyclicChoice, eq_true h1', eq_false h2', ite_true, ite_false]
    constructor <;> linarith
  · simp only [cyclicChoice, eq_true h2', eq_false h1', ite_true, ite_false]
    constructor <;> linarith

/-- How many of the cyclic pairs `x ≻ y`, `y ≻ z`, `z ≻ x` the ranking `σ` has. -/
def cyclicCount (σ : Equiv.Perm (Fin 3)) : ℕ :=
  (if σ 0 < σ 1 then 1 else 0) + (if σ 1 < σ 2 then 1 else 0) + (if σ 2 < σ 0 then 1 else 0)

/-- Every strict ordering of `{x, y, z}` has one or two of the cyclic pairs. -/
theorem cyclicCount_bounds (σ : Equiv.Perm (Fin 3)) : 1 ≤ cyclicCount σ ∧ cyclicCount σ ≤ 2 := by
  revert σ
  unfold cyclicCount
  decide

/-- **Exercise 1.D.5** (MWG, p. 16), necessity. If the cyclic function is rationalizable then
`1/3 ≤ α ≤ 2/3`. -/
theorem cyclicChoice_bounds_of_rationalizable {α : ℝ}
    (h : StochasticRationalizable (cyclicChoice α)) : 1 / 3 ≤ α ∧ α ≤ 2 / 3 := by
  obtain ⟨Pr, hnn, hsum, hc⟩ := h
  have h01 := hc 0 1 (by decide)
  have h12 := hc 1 2 (by decide)
  have h20 := hc 2 0 (by decide)
  have c : ∀ a b : Fin 3, b = a + 1 → cyclicChoice α a b = α := fun a b h => by
    simp only [cyclicChoice, eq_true h, ite_true]
  rw [c 0 1 (by decide)] at h01
  rw [c 1 2 (by decide)] at h12
  rw [c 2 0 (by decide)] at h20
  rw [Finset.sum_filter] at h01 h12 h20
  have h3 : 3 * α = ∑ σ, Pr σ * (cyclicCount σ : ℝ) := by
    have e : ∀ σ : Equiv.Perm (Fin 3), Pr σ * (cyclicCount σ : ℝ) =
        (if rankPrefers σ 0 1 then Pr σ else 0) + (if rankPrefers σ 1 2 then Pr σ else 0) +
          (if rankPrefers σ 2 0 then Pr σ else 0) := by
      intro σ
      simp only [cyclicCount, rankPrefers]
      push_cast
      split_ifs <;> ring
    simp only [e, Finset.sum_add_distrib]
    rw [← h01, ← h12, ← h20]
    ring
  have hlo : ∑ σ, Pr σ * 1 ≤ ∑ σ, Pr σ * (cyclicCount σ : ℝ) :=
    Finset.sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left
      (by exact_mod_cast (cyclicCount_bounds σ).1) (hnn σ)
  have hhi : ∑ σ, Pr σ * (cyclicCount σ : ℝ) ≤ ∑ σ, Pr σ * 2 :=
    Finset.sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left
      (by exact_mod_cast (cyclicCount_bounds σ).2) (hnn σ)
  rw [← Finset.sum_mul, hsum] at hlo hhi
  constructor <;> linarith

/-- The number of rankings with `a ≻ b` is three for distinct `a, b`. -/
theorem rankPrefers_card (a b : Fin 3) (hab : a ≠ b) :
    (Finset.univ.filter fun σ : Equiv.Perm (Fin 3) => rankPrefers σ a b).card = 3 := by
  revert a b
  unfold rankPrefers
  decide

/-- The total cyclic count over the rankings with `a ≻ b`: five for a cyclic pair `b = a + 1`,
four otherwise. -/
theorem rankPrefers_cyclicCount_sum (a b : Fin 3) (hab : a ≠ b) :
    ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin 3) => rankPrefers σ a b), cyclicCount σ =
      if b = a + 1 then 5 else 4 := by
  revert a b
  unfold rankPrefers cyclicCount
  decide

/-- The explicit distribution used for sufficiency: probability `1/6 + (α - 1/2)` on the three
rankings with two cyclic pairs and `1/6 - (α - 1/2)` on the other three. -/
noncomputable def cyclicDistribution (α : ℝ) (σ : Equiv.Perm (Fin 3)) : ℝ :=
  1 / 6 + (α - 1 / 2) * (2 * (cyclicCount σ : ℝ) - 3)

/-- **Exercise 1.D.5** (MWG, p. 16), sufficiency. If `1/3 ≤ α ≤ 2/3`, the cyclic function is
rationalized by `cyclicDistribution α`. -/
theorem cyclicChoice_rationalizable_of_bounds {α : ℝ} (h1 : 1 / 3 ≤ α) (h2 : α ≤ 2 / 3) :
    StochasticRationalizable (cyclicChoice α) := by
  have hsumFilter : ∀ s : Finset (Equiv.Perm (Fin 3)), ∑ σ ∈ s, cyclicDistribution α σ =
      s.card / 6 + (α - 1 / 2) * (2 * ((∑ σ ∈ s, cyclicCount σ : ℕ) : ℝ) - 3 * s.card) := by
    intro s
    simp only [cyclicDistribution, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
      ← Finset.mul_sum, Finset.sum_sub_distrib, Nat.cast_sum]
    ring
  refine ⟨cyclicDistribution α, fun σ => ?_, ?_, fun a b hab => ?_⟩
  · unfold cyclicDistribution
    rcases cyclicCount_bounds σ with ⟨hl, hu⟩
    have : cyclicCount σ = 1 ∨ cyclicCount σ = 2 := by omega
    rcases this with h | h <;> rw [h] <;> push_cast <;> linarith
  · rw [hsumFilter]
    have hc : (Finset.univ : Finset (Equiv.Perm (Fin 3))).card = 6 := by decide
    have hs : ∑ σ : Equiv.Perm (Fin 3), cyclicCount σ = 9 := by
      unfold cyclicCount
      decide
    rw [hc, hs]
    push_cast
    ring
  · rw [hsumFilter, rankPrefers_card a b hab, rankPrefers_cyclicCount_sum a b hab]
    unfold cyclicChoice
    split_ifs <;> push_cast <;> ring

/-- **Exercise 1.D.5** (MWG, p. 16). The cyclic stochastic choice function is rationalizable by
preferences iff `1/3 ≤ α ≤ 2/3`. -/
theorem cyclicChoice_rationalizable_iff (α : ℝ) :
    StochasticRationalizable (cyclicChoice α) ↔ 1 / 3 ≤ α ∧ α ≤ 2 / 3 :=
  ⟨cyclicChoice_bounds_of_rationalizable, fun h => cyclicChoice_rationalizable_of_bounds h.1 h.2⟩

/-- **Exercise 1.D.5(a)** (MWG, p. 16). `C({x,y}) = C({y,z}) = C({z,x}) = (1/2, 1/2)` can be
rationalized by preferences. -/
theorem exercise_1_D_5a : StochasticRationalizable (cyclicChoice (1 / 2)) :=
  (cyclicChoice_rationalizable_iff _).mpr ⟨by norm_num, by norm_num⟩

/-- **Exercise 1.D.5(b)** (MWG, p. 16). `C({x,y}) = C({y,z}) = C({z,x}) = (1/4, 3/4)` is not
rationalizable by preferences. -/
theorem exercise_1_D_5b : ¬StochasticRationalizable (cyclicChoice (1 / 4)) := fun h => by
  have := ((cyclicChoice_rationalizable_iff _).mp h).1
  norm_num at this

/-- **Exercise 1.D.5(c)** (MWG, p. 16). For `0 < α < 1`, the cyclic function is rationalizable
exactly on `[1/3, 2/3]`: it switches from rationalizable to nonrationalizable at `α = 1/3`
(below) and at `α = 2/3` (above). -/
theorem exercise_1_D_5c :
    (∀ α : ℝ, 0 < α → α < 1 → (StochasticRationalizable (cyclicChoice α) ↔
      α ∈ Set.Icc (1 / 3 : ℝ) (2 / 3))) ∧
      (∀ α : ℝ, 0 < α → α < 1 / 3 → ¬StochasticRationalizable (cyclicChoice α)) ∧
      (∀ α : ℝ, 2 / 3 < α → α < 1 → ¬StochasticRationalizable (cyclicChoice α)) := by
  refine ⟨fun α _ _ => cyclicChoice_rationalizable_iff α, fun α _ h h' => ?_,
    fun α h _ h' => ?_⟩
  · have := ((cyclicChoice_rationalizable_iff α).mp h').1
    linarith
  · have := ((cyclicChoice_rationalizable_iff α).mp h').2
    linarith

end MWG.PreferenceChoice
