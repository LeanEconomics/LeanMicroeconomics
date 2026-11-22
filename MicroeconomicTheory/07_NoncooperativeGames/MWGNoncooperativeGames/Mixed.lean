/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGNoncooperativeGames.Strategies
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# Randomized choices: mixed and behaviour strategies

MWG, Section 7.E, pp. 231-233.

* `IsMixedStrategy` is Definition 7.E.1 and `mixedExtension S` is the simplex `Δ(S_i)`;
  `pureMixed` is a pure strategy viewed as a degenerate mixed strategy.
* `NormalForm.mixedPayoff` is player `i`'s von Neumann-Morgenstern utility
  `u_i(σ) = ∑_{s ∈ S} σ₁(s₁) ⋯ σ_I(s_I) u_i(s)` from a mixed profile with independent
  randomizations, and `NormalForm.mixedExtensionGame` is `Γ_N = [I, {Δ(S_i)}, {u_i(·)}]`.
* `ExtensiveForm.IsBehaviorStrategy` is Definition 7.E.2.
* `ExtensiveForm.weight G j f x` is the product, along the path to `x`, of the move
  probabilities `f` at the nodes where `j` moves (`j = none` is nature).
  `reach_assemble_factor` factorises reach probabilities across the players, and
  `mixedOutcome_factor` does so for mixed profiles: the probability of a terminal node under a
  mixed profile is nature's weight times the product of the players' `mixedWeight`s. This is
  the factorisation behind Kuhn's theorem (module `MWGNoncooperativeGames.Kuhn`).
* `mixedPayoff_toNormalForm`: the payoff of a mixed profile in the induced normal form is the
  expected utility of the induced distribution over terminal nodes.
-/

namespace MWG.NoncooperativeGames

/-- **Definition 7.E.1** (MWG, p. 232). A mixed strategy over a finite pure strategy set `S`:
`σ(s) ≥ 0` for every `s` and `∑_s σ(s) = 1`. -/
def IsMixedStrategy {S : Type*} [Fintype S] (σ : S → ℝ) : Prop :=
  (∀ s, 0 ≤ σ s) ∧ ∑ s, σ s = 1

/-- **Section 7.E** (MWG, p. 232). The mixed extension `Δ(S_i)`, the simplex of probability
vectors on `S_i`. -/
def mixedExtension (S : Type*) [Fintype S] : Set (S → ℝ) := {σ | IsMixedStrategy σ}

/-- **Section 7.E** (MWG, p. 232). With `S_i = {s_{1i}, …, s_{Mi}}` the mixed extension is
`{(σ₁, …, σ_M) ∈ ℝ^M : σ_m ≥ 0, ∑_m σ_m = 1}`. -/
theorem mixedExtension_fin (M : ℕ) :
    mixedExtension (Fin M) = {σ : Fin M → ℝ | (∀ m, 0 ≤ σ m) ∧ ∑ m, σ m = 1} := rfl

/-- A pure strategy as the degenerate mixed strategy putting probability one on it. -/
def pureMixed {S : Type*} [DecidableEq S] (s : S) : S → ℝ := fun t => if t = s then 1 else 0

/-- **Section 7.E** (MWG, p. 232). A pure strategy is a (degenerate) mixed strategy. -/
theorem isMixedStrategy_pureMixed {S : Type*} [Fintype S] [DecidableEq S] (s : S) :
    IsMixedStrategy (pureMixed s) := by
  refine ⟨fun t => ?_, ?_⟩
  · unfold pureMixed
    split_ifs <;> norm_num
  · simp [pureMixed]

namespace NormalForm

variable {I : Type*} {S : I → Type*} [Fintype I] [DecidableEq I] [∀ i, Fintype (S i)]

/-- **Section 7.E** (MWG, p. 232). Player `i`'s von Neumann-Morgenstern utility from the mixed
profile `σ`: `u_i(σ) = ∑_{s ∈ S} [σ₁(s₁) σ₂(s₂) ⋯ σ_I(s_I)] u_i(s)`. -/
def mixedPayoff (N : NormalForm I S) (σ : (i : I) → S i → ℝ) (i : I) : ℝ :=
  ∑ s : (i : I) → S i, (∏ j, σ j (s j)) * N.payoff i s

/-- **Section 7.E** (MWG, p. 232). Independent randomizations induce a probability
distribution on pure strategy profiles: `∑_s σ₁(s₁) ⋯ σ_I(s_I) = 1`. -/
theorem sum_prod_mixed {σ : (i : I) → S i → ℝ} (hσ : ∀ i, IsMixedStrategy (σ i)) :
    (∀ s : (i : I) → S i, 0 ≤ ∏ j, σ j (s j)) ∧ ∑ s : (i : I) → S i, ∏ j, σ j (s j) = 1 := by
  refine ⟨fun s => Finset.prod_nonneg fun j _ => (hσ j).1 _, ?_⟩
  rw [← Fintype.prod_sum]
  exact Finset.prod_eq_one fun j _ => (hσ j).2

variable [∀ i, DecidableEq (S i)]

/-- **Section 7.E** (MWG, p. 232). On degenerate mixed strategies the mixed payoff is the pure
payoff: pure strategies are a special case of mixed strategies. -/
theorem mixedPayoff_pure (N : NormalForm I S) (s : (i : I) → S i) (i : I) :
    N.mixedPayoff (fun j => pureMixed (s j)) i = N.payoff i s := by
  unfold mixedPayoff pureMixed
  simp_rw [Fintype.prod_boole]
  have : ∀ t : (i : I) → S i, (∀ j, t j = s j) ↔ t = s := fun t => funext_iff.symm
  simp_rw [this]
  simp

/-- **Section 7.E** (MWG, p. 232). The mixed extension `Γ_N = [I, {Δ(S_i)}, {u_i(·)}]` of a
normal form game. -/
def mixedExtensionGame (N : NormalForm I S) :
    NormalForm I (fun i => {σ : S i → ℝ // IsMixedStrategy σ}) where
  payoff i σ := N.mixedPayoff (fun j => (σ j).1) i

/-- The mixed extension agrees with the original game on degenerate mixed strategies. -/
theorem mixedExtensionGame_pure (N : NormalForm I S) (s : (i : I) → S i) (i : I) :
    N.mixedExtensionGame.payoff i (fun j => ⟨pureMixed (s j), isMixedStrategy_pureMixed _⟩) =
      N.payoff i s :=
  N.mixedPayoff_pure s i

end NormalForm

namespace ExtensiveForm

variable {I A H : Type*} (G : ExtensiveForm I A H) [DecidableEq I]

omit [DecidableEq I] in
/-- **Definition 7.E.2** (MWG, p. 233). A behaviour strategy for player `i`: at every one of
her information sets `k ∈ ℋ_i`, a probability `λ_i(a, k) ≥ 0` on each `a ∈ C(k)` with
`∑_{a ∈ C(k)} λ_i(a, k) = 1` (and, by convention, zero off `C(k)`). -/
def IsBehaviorStrategy (i : I) (β : H → A → ℝ) : Prop :=
  ∀ k, G.player k = some i →
    (∀ a, 0 ≤ β k a) ∧ (∀ a, a ∉ G.avail k → β k a = 0) ∧ ∑ a ∈ G.avail k, β k a = 1

/-- The product of the move probabilities `f` at the nodes on the path to `x` where `j` moves
(`j = none`: nature). -/
def weight (j : Option I) (f : H → A → ℝ) : List A → ℝ
  | [] => 1
  | a :: x => weight j f x * if G.player (G.info x) = j then f (G.info x) a else 1

@[simp] theorem weight_nil (j : Option I) (f : H → A → ℝ) : G.weight j f [] = 1 := rfl

theorem weight_cons (j : Option I) (f : H → A → ℝ) (a : A) (x : List A) :
    G.weight j f (a :: x) =
      G.weight j f x * if G.player (G.info x) = j then f (G.info x) a else 1 := rfl

/-- The weight of `j` depends only on `f` at `j`'s information sets. -/
theorem weight_congr (j : Option I) {f f' : H → A → ℝ}
    (h : ∀ k, G.player k = j → f k = f' k) (x : List A) :
    G.weight j f x = G.weight j f' x := by
  induction x with
  | nil => rfl
  | cons a x ih =>
    rw [weight_cons, weight_cons, ih]
    split_ifs with hk
    · rw [h _ hk]
    · rfl

/-- **Section 7.E** (MWG, pp. 232-233). Reach probabilities factorise across nature and the
players: `P(x) = w_nature(x) · ∏_j w_j(x)`. -/
theorem reach_assemble_factor [Fintype I] (F : I → H → A → ℝ) (x : List A) :
    G.reach (G.assemble F) x = G.weight none G.natureProb x * ∏ j, G.weight (some j) (F j) x := by
  classical
  induction x with
  | nil => simp
  | cons a x ih =>
    rw [reach_cons, ih, weight_cons]
    simp_rw [weight_cons]
    rw [Finset.prod_mul_distrib]
    cases hk : G.player (G.info x) with
    | none =>
      rw [G.assemble_of_none _ hk]
      simp
      ring
    | some j₀ =>
      rw [G.assemble_of_some _ hk]
      simp only [Option.some.injEq, reduceCtorEq, ite_false, mul_one]
      rw [Finset.prod_ite_eq]
      simp only [Finset.mem_univ, ite_true]
      ring

variable [DecidableEq A]

/-- The pure strategy `s` of player `i` takes, at each of `i`'s nodes on the path to `x`, the
action that the path takes there. -/
def Consistent {i : I} (s : G.PureStrategy i) (x : List A) : Prop :=
  ∀ y a (hy : G.player (G.info y) = some i), a :: y <:+ x → (s ⟨G.info y, hy⟩).1 = a

/-- The weight of a pure strategy is `1` if it is consistent with the path to `x`. -/
theorem weight_pureBeh_of_consistent {i : I} (s : G.PureStrategy i) {x : List A}
    (h : G.Consistent s x) : G.weight (some i) (G.pureBeh s) x = 1 := by
  induction x with
  | nil => rfl
  | cons a x ih =>
    rw [weight_cons, ih (fun y b hy hb => h y b hy (hb.trans (List.suffix_cons a x)))]
    split_ifs with hk
    · simp [G.pureBeh_of_mem s hk, h x a hk (List.suffix_refl _)]
    · norm_num

/-- The weight of a pure strategy is `0` if it is not consistent with the path to `x`. -/
theorem weight_pureBeh_of_not_consistent {i : I} (s : G.PureStrategy i) {x : List A}
    (h : ¬ G.Consistent s x) : G.weight (some i) (G.pureBeh s) x = 0 := by
  induction x with
  | nil =>
    exfalso
    refine h fun y a _ hya => ?_
    have := hya.length_le
    simp at this
  | cons a x ih =>
    rw [weight_cons]
    by_cases hx : G.Consistent s x
    · have hk : ∃ hk : G.player (G.info x) = some i, (s ⟨G.info x, hk⟩).1 ≠ a := by
        by_contra hno
        refine h fun y b hy hb => ?_
        rcases List.suffix_cons_iff.1 hb with he | hb'
        · simp only [List.cons.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          by_contra hne
          exact hno ⟨hy, hne⟩
        · exact hx y b hy hb'
      obtain ⟨hk, hne⟩ := hk
      simp [hk, G.pureBeh_of_mem s hk, hne]
    · rw [ih hx, zero_mul]

/-- A pure strategy is a behaviour strategy. -/
theorem isBehaviorStrategy_pureBeh {i : I} (s : G.PureStrategy i) :
    G.IsBehaviorStrategy i (G.pureBeh s) := by
  intro k hk
  refine ⟨fun a => ?_, fun a ha => ?_, G.sum_pureBeh s hk⟩
  · rw [G.pureBeh_of_mem s hk]
    split_ifs <;> norm_num
  · have hne : (s ⟨k, hk⟩).1 ≠ a := by
      rintro rfl
      exact ha (s ⟨k, hk⟩).2
    simp [G.pureBeh_of_mem s hk, hne]

variable [Fintype A] [Fintype H] [DecidableEq H]

/-- Player `i`'s realization weight of node `x` under the mixed strategy `σ`: the probability
that `σ` selects a pure strategy taking the path's actions at `i`'s nodes before `x`. -/
def mixedWeight {i : I} (σ : G.PureStrategy i → ℝ) (x : List A) : ℝ :=
  ∑ s, σ s * G.weight (some i) (G.pureBeh s) x

variable [Fintype I]

/-- The probability of a terminal node under a mixed strategy profile `σ = (σ₁, …, σ_I)` with
independent randomizations: `∑_s σ₁(s₁) ⋯ σ_I(s_I) P_s(z)`. -/
def mixedOutcome (σ : (i : I) → G.PureStrategy i → ℝ) (z : List A) : ℝ :=
  ∑ s : (i : I) → G.PureStrategy i, (∏ j, σ j (s j)) * G.reach (G.pureProfile s) z

omit [Fintype A] in
/-- **Section 7.E** (MWG, pp. 232-233). The outcome probability of a mixed profile factorises:
`P_σ(x) = w_nature(x) · ∏_j mixedWeight σ_j x`. -/
theorem mixedOutcome_factor (σ : (i : I) → G.PureStrategy i → ℝ) (x : List A) :
    G.mixedOutcome σ x = G.weight none G.natureProb x * ∏ j, G.mixedWeight (σ j) x := by
  unfold mixedOutcome mixedWeight pureProfile
  simp_rw [reach_assemble_factor]
  rw [Fintype.prod_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.prod_mul_distrib]
  ring

/-- **Section 7.E** (MWG, p. 232). A mixed strategy profile induces a probability distribution
over the terminal nodes. -/
theorem mixedOutcome_distribution {σ : (i : I) → G.PureStrategy i → ℝ}
    (hσ : ∀ i, IsMixedStrategy (σ i)) :
    (∀ z, 0 ≤ G.mixedOutcome σ z) ∧ ∑ z ∈ G.terminals, G.mixedOutcome σ z = 1 := by
  obtain ⟨hnn, hsum⟩ := NormalForm.sum_prod_mixed hσ
  refine ⟨fun z => Finset.sum_nonneg fun s _ =>
    mul_nonneg (hnn s) (G.reach_nonneg (G.pureProfile_nonneg s) z), ?_⟩
  unfold mixedOutcome
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, G.sum_reach_terminals (G.sum_pureProfile _), mul_one]
  exact hsum

/-- **Section 7.E** (MWG, p. 232). In the normal form induced by an extensive form, the payoff
of a mixed profile is the expected utility of the induced distribution over terminal nodes:
`u_i(σ) = E_σ[u_i(s)] = ∑_z P_σ(z) u_i(z)`. -/
theorem mixedPayoff_toNormalForm (σ : (i : I) → G.PureStrategy i → ℝ) (i : I) :
    G.toNormalForm.mixedPayoff σ i =
      ∑ z ∈ G.terminals, G.mixedOutcome σ z * G.payoff i z := by
  unfold NormalForm.mixedPayoff toNormalForm mixedOutcome
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun s _ => ?_
  ring

end ExtensiveForm

end MWG.NoncooperativeGames
