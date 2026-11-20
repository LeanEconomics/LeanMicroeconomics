/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGNoncooperativeGames.ExtensiveForm
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith

/-!
# Strategies and the normal form representation of a game

MWG, Section 7.D, pp. 228-231.

* `ExtensiveForm.PureStrategy G i` is Definition 7.D.1: a function `s_i : ℋ_i → 𝒜` with
  `s_i(H) ∈ C(H)`, encoded as a dependent function on player `i`'s information sets.
  `card_pureStrategy` and `exercise_7_D_1` count them (Exercise 7.D.1).
* `ExtensiveForm.reach G f x` is the probability that node `x` is reached when moves are
  drawn from the move probabilities `f : H → A → ℝ` (one distribution per information set,
  nature included). `assemble` combines the players' (behaviour) plans with nature's
  probabilities, and `pureProfile s` is the profile of pure strategies `s`.
* `sum_reach_terminals`: whenever the move probabilities at every information set sum to one,
  the reach probabilities of the terminal nodes sum to one. So every strategy profile induces
  a probability distribution over terminal nodes (MWG, p. 229); without moves of nature
  this distribution is degenerate (`pureProfile_outcome_degenerate`).
* `NormalForm I S` is Definition 7.D.2, `Γ_N = [I, {S_i}, {u_i(·)}]`, and
  `ExtensiveForm.toNormalForm` is the induced normal form, with expected-utility payoffs.
-/

namespace MWG.NoncooperativeGames

/-- **Definition 7.D.2** (MWG, p. 230). A game in normal form `Γ_N = [I, {S_i}, {u_i(·)}]`:
players `I`, strategy sets `S i`, and von Neumann-Morgenstern payoffs `u_i(s₁, …, s_I)`. -/
structure NormalForm (I : Type*) (S : I → Type*) where
  /-- The payoff `u_i(s)` of player `i` at strategy profile `s`. -/
  payoff : I → ((i : I) → S i) → ℝ

namespace ExtensiveForm

variable {I A H : Type*} (G : ExtensiveForm I A H)

/-- Player `i`'s collection of information sets `ℋ_i = {H ∈ ℋ : ι(H) = i}` (MWG, p. 227). -/
abbrev InfoSetOf (i : I) := {k : H // G.player k = some i}

/-- **Definition 7.D.1** (MWG, p. 228). A pure strategy of player `i`: a choice
`s_i(H) ∈ C(H)` at each of her information sets `H ∈ ℋ_i`. -/
abbrev PureStrategy (i : I) := (k : G.InfoSetOf i) → {a : A // a ∈ G.avail k.1}

/-- A pure strategy given by a plain function `f : H → A` with `f k ∈ C(k)` on `ℋ_i`. -/
def pureOfFun (i : I) (f : H → A) (hf : ∀ k, G.player k = some i → f k ∈ G.avail k) :
    G.PureStrategy i := fun k => ⟨f k.1, hf k.1 k.2⟩

@[simp] theorem pureOfFun_apply (i : I) (f : H → A)
    (hf : ∀ k, G.player k = some i → f k ∈ G.avail k) (k : G.InfoSetOf i) :
    (G.pureOfFun i f hf k).1 = f k.1 := rfl

/-- The probability of reaching node `x` when the move at a decision node `y` is drawn from
`f (H(y))`: the product of the move probabilities along the path to `x`. -/
def reach (f : H → A → ℝ) : List A → ℝ
  | [] => 1
  | a :: x => reach f x * f (G.info x) a

@[simp] theorem reach_nil (f : H → A → ℝ) : G.reach f [] = 1 := rfl

@[simp] theorem reach_cons (f : H → A → ℝ) (a : A) (x : List A) :
    G.reach f (a :: x) = G.reach f x * f (G.info x) a := rfl

/-- Combine plans `F j` of the players with nature's probabilities: at an information set of
player `j` use `F j`, at one of nature use `ρ`. -/
def assemble (F : I → H → A → ℝ) : H → A → ℝ := fun k =>
  match G.player k with
  | none => G.natureProb k
  | some j => F j k

theorem assemble_of_none (F : I → H → A → ℝ) {k : H} (hk : G.player k = none) :
    G.assemble F k = G.natureProb k := by
  simp [assemble, hk]

theorem assemble_of_some (F : I → H → A → ℝ) {k : H} {j : I} (hk : G.player k = some j) :
    G.assemble F k = F j k := by
  simp [assemble, hk]

/-- A reach probability is nonnegative when all move probabilities are. -/
theorem reach_nonneg {f : H → A → ℝ} (hf : ∀ k a, 0 ≤ f k a) (x : List A) :
    0 ≤ G.reach f x := by
  induction x with
  | nil => simp
  | cons a x ih => exact mul_nonneg ih (hf _ _)

variable [DecidableEq A] [DecidableEq I]

/-- A pure strategy as degenerate move probabilities: probability one on `s_i(H)` at each of
player `i`'s information sets `H` (zero elsewhere; values off `ℋ_i` are never used). -/
def pureBeh {i : I} (s : G.PureStrategy i) : H → A → ℝ := fun k a =>
  if hk : G.player k = some i then (if (s ⟨k, hk⟩).1 = a then 1 else 0) else 0

theorem pureBeh_of_mem {i : I} (s : G.PureStrategy i) {k : H} (hk : G.player k = some i)
    (a : A) : G.pureBeh s k a = if (s ⟨k, hk⟩).1 = a then 1 else 0 := by
  simp [pureBeh, hk]

/-- The move probabilities of a pure strategy profile `s = (s₁, …, s_I)`. -/
def pureProfile (s : (i : I) → G.PureStrategy i) : H → A → ℝ :=
  G.assemble fun j => G.pureBeh (s j)

/-- A pure strategy puts total probability one on the available actions. -/
theorem sum_pureBeh {i : I} (s : G.PureStrategy i) {k : H} (hk : G.player k = some i) :
    ∑ a ∈ G.avail k, G.pureBeh s k a = 1 := by
  simp only [G.pureBeh_of_mem s hk]
  rw [Finset.sum_ite_eq]
  simp [(s ⟨k, hk⟩).2]

/-- The move probabilities of a pure strategy profile sum to one at every information set. -/
theorem sum_pureProfile (s : (i : I) → G.PureStrategy i) (k : H) :
    ∑ a ∈ G.avail k, G.pureProfile s k a = 1 := by
  cases hk : G.player k with
  | none => rw [pureProfile, G.assemble_of_none _ hk]; exact G.nature_sum k hk
  | some j => rw [pureProfile, G.assemble_of_some _ hk]; exact G.sum_pureBeh (s j) hk

/-- The move probabilities of a pure strategy profile are nonnegative. -/
theorem pureProfile_nonneg (s : (i : I) → G.PureStrategy i) (k : H) (a : A) :
    0 ≤ G.pureProfile s k a := by
  cases hk : G.player k with
  | none => rw [pureProfile, G.assemble_of_none _ hk]; exact G.nature_nonneg k hk a
  | some j =>
    rw [pureProfile, G.assemble_of_some _ hk, pureBeh]
    split_ifs <;> norm_num

variable [Fintype A]

omit [DecidableEq A] [DecidableEq I] [Fintype A] in
/-- A terminal node has no strict successor among the terminal nodes. -/
theorem eq_of_terminal_suffix {x z : List A} (hx : G.IsTerminal x) (hz : z ∈ G.nodes)
    (hxz : x <:+ z) : z = x := by
  by_contra hne
  obtain ⟨b, hb⟩ := exists_cons_suffix hxz (Ne.symm hne)
  exact hx.2 b (G.mem_of_suffix hb hz)

omit [DecidableEq I] in
/-- Splitting the terminal nodes below a decision node `x` by the action taken at `x`. -/
theorem sum_terminals_below_decision {x : List A} (hx : G.IsDecision x) (r : List A → ℝ) :
    ∑ z ∈ G.terminals with x <:+ z, r z =
      ∑ a ∈ G.avail (G.info x), ∑ z ∈ G.terminals with a :: x <:+ z, r z := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z hz => ?_
  rw [mem_terminals] at hz
  by_cases hxz : x <:+ z
  · have hne : x ≠ z := by
      rintro rfl
      exact ((G.isDecision_or_isTerminal hx.1).2 ⟨hx, hz⟩).elim
    obtain ⟨b, hb⟩ := exists_cons_suffix hxz hne
    have hbav : b ∈ G.avail (G.info x) := G.mem_avail_of_cons_mem (G.mem_of_suffix hb hz.1)
    have key : ∀ a, (a :: x <:+ z) ↔ a = b := by
      intro a
      constructor
      · intro ha
        have := suffix_unique ha hb (by simp)
        simpa using this
      · rintro rfl
        exact hb
    simp only [key, hxz, ite_true]
    rw [Finset.sum_ite_eq']
    simp [hbav]
  · have : ∀ a, ¬ (a :: x <:+ z) := fun a ha => hxz ((List.suffix_cons a x).trans ha)
    simp [this, hxz]

omit [DecidableEq A] [DecidableEq I] [Fintype A] in
/-- The length of a node is at most the largest length of a node. -/
theorem length_le_sup {x : List A} (hx : x ∈ G.nodes) :
    x.length ≤ G.nodes.sup List.length :=
  Finset.le_sup (f := List.length) hx

omit [DecidableEq I] in
/-- **Section 7.D** (MWG, p. 229). Reach probabilities split over the terminal nodes: for
every node `x`, the reach probabilities of the terminal nodes following `x` sum to the reach
probability of `x`, whenever the move probabilities sum to one at every information set. -/
theorem sum_reach_terminals_below {f : H → A → ℝ}
    (hf : ∀ k, ∑ a ∈ G.avail k, f k a = 1) {x : List A} (hx : x ∈ G.nodes) :
    ∑ z ∈ G.terminals with x <:+ z, G.reach f z = G.reach f x := by
  suffices h : ∀ n, ∀ x ∈ G.nodes, G.nodes.sup List.length - x.length ≤ n →
      ∑ z ∈ G.terminals with x <:+ z, G.reach f z = G.reach f x from h _ x hx le_rfl
  intro n
  induction n with
  | zero =>
    intro x hx hn
    have hterm : G.IsTerminal x := by
      refine ⟨hx, fun b hb => ?_⟩
      have := G.length_le_sup hb
      simp only [List.length_cons] at this
      omega
    have : (G.terminals.filter fun z => x <:+ z) = {x} := by
      ext z
      simp only [Finset.mem_filter, mem_terminals, Finset.mem_singleton]
      constructor
      · rintro ⟨hz, hxz⟩
        exact G.eq_of_terminal_suffix hterm hz.1 hxz
      · rintro rfl
        exact ⟨hterm, List.suffix_refl _⟩
    rw [this, Finset.sum_singleton]
  | succ n ih =>
    intro x hx hn
    rcases (G.isDecision_or_isTerminal hx).1 with hdec | hterm
    · rw [G.sum_terminals_below_decision hdec]
      have hchild : ∀ a ∈ G.avail (G.info x),
          ∑ z ∈ G.terminals with a :: x <:+ z, G.reach f z = G.reach f x * f (G.info x) a := by
        intro a ha
        have hmem := G.cons_mem_of_mem_avail hdec ha
        have hl := G.length_le_sup hmem
        simp only [List.length_cons] at hl
        rw [ih (a :: x) hmem (by simp only [List.length_cons]; omega), reach_cons]
      rw [Finset.sum_congr rfl hchild, ← Finset.mul_sum, hf, mul_one]
    · have : (G.terminals.filter fun z => x <:+ z) = {x} := by
        ext z
        simp only [Finset.mem_filter, mem_terminals, Finset.mem_singleton]
        constructor
        · rintro ⟨hz, hxz⟩
          exact G.eq_of_terminal_suffix hterm hz.1 hxz
        · rintro rfl
          exact ⟨hterm, List.suffix_refl _⟩
      rw [this, Finset.sum_singleton]

omit [DecidableEq I] in
/-- **Section 7.D** (MWG, p. 229). Move probabilities summing to one at every information set
induce a probability distribution over the terminal nodes. -/
theorem sum_reach_terminals {f : H → A → ℝ} (hf : ∀ k, ∑ a ∈ G.avail k, f k a = 1) :
    ∑ z ∈ G.terminals, G.reach f z = 1 := by
  have h := G.sum_reach_terminals_below hf G.nil_mem
  simpa using h

/-- **Section 7.D** (MWG, p. 229). Every profile of pure strategies induces a probability
distribution over the terminal nodes of the game. -/
theorem pureProfile_outcome_distribution (s : (i : I) → G.PureStrategy i) :
    (∀ z, 0 ≤ G.reach (G.pureProfile s) z) ∧
      ∑ z ∈ G.terminals, G.reach (G.pureProfile s) z = 1 :=
  ⟨G.reach_nonneg (G.pureProfile_nonneg s), G.sum_reach_terminals (G.sum_pureProfile s)⟩

omit [Fintype A] in
/-- Without moves of nature, every reach probability of a pure profile is `0` or `1`. -/
theorem reach_pureProfile_zero_or_one (hN : ∀ k, G.player k ≠ none)
    (s : (i : I) → G.PureStrategy i) (x : List A) :
    G.reach (G.pureProfile s) x = 0 ∨ G.reach (G.pureProfile s) x = 1 := by
  induction x with
  | nil => simp
  | cons a x ih =>
    rw [reach_cons]
    obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.1 (hN (G.info x))
    have hstep : G.pureProfile s (G.info x) a =
        if (s j ⟨G.info x, hj⟩).1 = a then 1 else 0 := by
      rw [pureProfile, G.assemble_of_some _ hj, G.pureBeh_of_mem _ hj]
    rw [hstep]
    rcases ih with h | h <;> split_ifs <;> simp [h]

/-- **Section 7.D** (MWG, p. 229). Without moves of nature, a pure strategy profile induces a
single sequence of moves: exactly one terminal node is reached, with probability one. -/
theorem pureProfile_outcome_degenerate (hN : ∀ k, G.player k ≠ none)
    (s : (i : I) → G.PureStrategy i) :
    ∃! z, z ∈ G.terminals ∧ G.reach (G.pureProfile s) z = 1 := by
  have hsum := G.sum_reach_terminals (G.sum_pureProfile s)
  have hex : ∃ z ∈ G.terminals, G.reach (G.pureProfile s) z = 1 := by
    by_contra hno
    push Not at hno
    have : ∑ z ∈ G.terminals, G.reach (G.pureProfile s) z = 0 := by
      refine Finset.sum_eq_zero fun z hz => ?_
      exact (G.reach_pureProfile_zero_or_one hN s z).resolve_right (hno z hz)
    linarith
  obtain ⟨z, hz, h1⟩ := hex
  refine ⟨z, ⟨hz, h1⟩, fun z' ⟨hz', h1'⟩ => ?_⟩
  by_contra hne
  have hle : G.reach (G.pureProfile s) z + G.reach (G.pureProfile s) z' ≤
      ∑ z ∈ G.terminals, G.reach (G.pureProfile s) z := by
    rw [← Finset.sum_pair (Ne.symm hne)]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun y _ _ =>
      G.reach_nonneg (G.pureProfile_nonneg s) y
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl <;> assumption
  linarith

omit [Fintype A] in
/-- The move probabilities of a pure profile at an information set of player `j`. -/
theorem pureProfile_apply (s : (i : I) → G.PureStrategy i) {k : H} {j : I}
    (hk : G.player k = some j) (a : A) :
    G.pureProfile s k a = if (s j ⟨k, hk⟩).1 = a then 1 else 0 := by
  rw [pureProfile, G.assemble_of_some _ hk, G.pureBeh_of_mem _ hk]

/-- **Section 7.D** (MWG, p. 229). Without moves of nature, the normal form payoff of a pure
profile is the payoff at the terminal node it reaches. -/
theorem toNormalForm_payoff_eq_of_reach (hN : ∀ k, G.player k ≠ none)
    (s : (i : I) → G.PureStrategy i) {z : List A} (hz : z ∈ G.terminals)
    (h1 : G.reach (G.pureProfile s) z = 1) (i : I) :
    ∑ y ∈ G.terminals, G.reach (G.pureProfile s) y * G.payoff i y = G.payoff i z := by
  rw [Finset.sum_eq_single z, h1, one_mul]
  · intro y hy hyz
    have h0 : G.reach (G.pureProfile s) y = 0 := by
      refine (G.reach_pureProfile_zero_or_one hN s y).resolve_right fun hy1 => hyz ?_
      obtain ⟨w, -, hw⟩ := G.pureProfile_outcome_degenerate hN s
      rw [hw y ⟨hy, hy1⟩, hw z ⟨hz, h1⟩]
    rw [h0, zero_mul]
  · intro h
    exact absurd hz h

variable [Fintype H] [DecidableEq H]

omit [DecidableEq A] [Fintype A] in
/-- **Section 7.D, Exercise 7.D.1** (MWG, pp. 229 and 233). The number of pure strategies of
player `i` is the product, over her information sets, of the number of available actions. -/
theorem card_pureStrategy (i : I) :
    Fintype.card (G.PureStrategy i) = ∏ k : G.InfoSetOf i, (G.avail k.1).card := by
  rw [Fintype.card_pi]
  simp

omit [DecidableEq A] [Fintype A] in
/-- **Exercise 7.D.1** (MWG, p. 233). If player `i`'s information sets are indexed
`n = 1, …, N` and `M_n` actions are possible at information set `n`, then player `i` has
`M₁ ⋯ M_N` pure strategies. -/
theorem exercise_7_D_1 (i : I) (N : ℕ) (e : Fin N ≃ G.InfoSetOf i) (M : Fin N → ℕ)
    (hM : ∀ n, (G.avail (e n).1).card = M n) :
    Fintype.card (G.PureStrategy i) = ∏ n, M n := by
  rw [card_pureStrategy, ← Fintype.prod_equiv e (fun n => M n)]
  intro n
  exact (hM n).symm

/-- **Section 7.D** (MWG, pp. 229-230). The normal form induced by an extensive form: the
strategy sets are the pure strategy sets, and `u_i(s)` is the expected utility of the
terminal-node distribution induced by `s`. -/
def toNormalForm : NormalForm I G.PureStrategy where
  payoff i s := ∑ z ∈ G.terminals, G.reach (G.pureProfile s) z * G.payoff i z

omit [Fintype H] [DecidableEq H] in
/-- **Section 7.D** (MWG, p. 229). Without moves of nature, `u_i(s)` is player `i`'s payoff at
the terminal node reached by `s`. -/
theorem toNormalForm_payoff_of_reach (hN : ∀ k, G.player k ≠ none)
    (s : (i : I) → G.PureStrategy i) {z : List A} (hz : z ∈ G.terminals)
    (h1 : G.reach (G.pureProfile s) z = 1) (i : I) :
    G.toNormalForm.payoff i s = G.payoff i z :=
  G.toNormalForm_payoff_eq_of_reach hN s hz h1 i

end ExtensiveForm

end MWG.NoncooperativeGames
