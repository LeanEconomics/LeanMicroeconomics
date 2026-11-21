import MWGNoncooperativeGames.Kuhn
import MWGSimultaneousMoveGames.Dominance
import Mathlib.Tactic.FinCases
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Data.ENat.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.SpecificLimits.Normed
import MWGSimultaneousMoveGames.TremblingHand
import Mathlib.Topology.Sequences
import Mathlib.Topology.Order.Compact
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.LinearCombination
import MWGNoncooperativeGames.MatchingPennies
import Mathlib.Data.Fintype.Pi
import MWGSimultaneousMoveGames.TwoPlayerConverse
import MWGSimultaneousMoveGames.Bimatrix
import MWGSimultaneousMoveGames.MixedStrategies
import MWGSimultaneousMoveGames.Examples8B
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.ConditionalProbability
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Algebra.BigOperators.Field
set_option autoImplicit false

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Continuation payoffs, behaviour profiles, subgames and subgame perfection

MWG, Section 9.B, pp. 268-276: the objects that the chapter's solution concepts are built on.
Games are Chapter 7's `ExtensiveForm I A H` (nodes are histories, most recent action first).

* `reachFrom G f x z` is the probability of moving from node `x` to node `z` when moves are
  drawn from `f : H → A → ℝ`; `cont G f x i` is player `i`'s **continuation payoff** from `x`,
  `∑_{z terminal after x} P(z | x) u_i(z)`. It satisfies the backward-induction recursion
  (`cont_decision`, `cont_terminal`), equals the normal-form payoff at the initial node
  (`cont_nil`, `toNormalForm_payoff_eq_cont`), and depends only on the moves at the information
  sets of the nodes after `x` (`cont_congr`).
* A **behaviour profile** `F : I → H → A → ℝ` gives a behaviour strategy `F i` to every player
  (Definition 7.E.2); the moves are `G.assemble F` (nature moves by `ρ`). `IsNashB` is Nash
  equilibrium (Definition 8.D.2) of the extensive form in behaviour strategies, with
  deviations to arbitrary behaviour strategies. For pure profiles it implies the Nash property
  in the induced normal form (`IsNashB.isNashEquilibrium_pure`).
* `IsSubgameRoot` is **Definition 9.B.1** (a subgame is identified with its initial node) and
  `IsSPNE` is **Definition 9.B.2**. `isNashB_of_isSPNE`: an SPNE is a Nash equilibrium;
  `exercise_9_B_2a`, `exercise_9_B_2b`.
* `cont_sub_eq_sum_entry`: if two move functions differ only on a set `D` of information sets,
  the difference of continuation payoffs from `y` is the reach-weighted sum of the differences
  at the **entry nodes** (the first nodes after `y` lying in `D`). This decomposition drives
  the proofs of Propositions 9.C.1 and 9.C.2.

Departure: MWG states the solution concepts for mixed strategies `σ`; we use behaviour
strategies throughout (equivalent under perfect recall by Kuhn's theorem, Chapter 7).
-/

namespace MWG.DynamicGames

open MWG.NoncooperativeGames MWG.NoncooperativeGames.ExtensiveForm

variable {I A H : Type*} (G : ExtensiveForm I A H) [DecidableEq A]

/-- The probability of moving from node `x` to node `z` (for `x` a predecessor of `z`) when
the move at each decision node `y` is drawn from `f (H(y))`. -/
def reachFrom (f : H → A → ℝ) (x : List A) : List A → ℝ
  | [] => if x = [] then 1 else 0
  | a :: y => if a :: y = x then 1 else reachFrom f x y * f (G.info y) a

/-- The probability of moving from a node to itself is one. -/
theorem reachFrom_self (f : H → A → ℝ) (x : List A) : reachFrom G f x x = 1 := by
  cases x with
  | nil => simp [reachFrom]
  | cons a y => simp [reachFrom]

/-- One more step after `y`. -/
theorem reachFrom_cons (f : H → A → ℝ) {x y : List A} (h : x <:+ y) (a : A) :
    reachFrom G f x (a :: y) = reachFrom G f x y * f (G.info y) a := by
  have hne : a :: y ≠ x := by
    intro he
    have := h.length_le
    rw [← he] at this
    simp at this
  simp [reachFrom, hne]

/-- The probability of moving to the immediate successor `a :: x` is `f (H(x)) a`. -/
theorem reachFrom_cons_self (f : H → A → ℝ) (x : List A) (a : A) :
    reachFrom G f x (a :: x) = f (G.info x) a := by
  rw [reachFrom_cons G f (List.suffix_refl x), reachFrom_self, one_mul]

/-- From the initial node, `reachFrom` is Chapter 7's reach probability. -/
theorem reachFrom_nil (f : H → A → ℝ) (z : List A) : reachFrom G f [] z = G.reach f z := by
  induction z with
  | nil => simp [reachFrom]
  | cons a y ih => simp [reachFrom, ih]

/-- Reach probabilities multiply along a path: `P(z | x) = P(y | x) P(z | y)`. -/
theorem reachFrom_trans (f : H → A → ℝ) {x y z : List A} (hxy : x <:+ y) (hyz : y <:+ z) :
    reachFrom G f x z = reachFrom G f x y * reachFrom G f y z := by
  induction z with
  | nil =>
    have hy : y = [] := List.eq_nil_of_suffix_nil hyz
    subst hy
    rw [reachFrom_self, mul_one]
  | cons a z ih =>
    rcases List.suffix_cons_iff.1 hyz with h | h
    · subst h
      rw [reachFrom_self, mul_one]
    · rw [reachFrom_cons G f (hxy.trans h), reachFrom_cons G f h, ih h]
      ring

/-- `P(z) = P(x) P(z | x)`. -/
theorem reach_eq_mul_reachFrom (f : H → A → ℝ) {x z : List A} (h : x <:+ z) :
    G.reach f z = G.reach f x * reachFrom G f x z := by
  rw [← reachFrom_nil, ← reachFrom_nil, reachFrom_trans G f List.nil_suffix h]

/-- Reach probabilities are nonnegative when move probabilities are. -/
theorem reachFrom_nonneg {f : H → A → ℝ} (hf : ∀ k a, 0 ≤ f k a) (x z : List A) :
    0 ≤ reachFrom G f x z := by
  induction z with
  | nil => simp only [reachFrom]; split_ifs <;> norm_num
  | cons a y ih =>
    simp only [reachFrom]
    split_ifs
    · norm_num
    · exact mul_nonneg ih (hf _ _)

/-- `reachFrom` from `x` to `z` depends only on the moves at the decision nodes on the path
from `x` to `z`. -/
theorem reachFrom_congr {f f' : H → A → ℝ} {x z : List A} (hxz : x <:+ z)
    (h : ∀ y, x <:+ y → ∀ b, b :: y <:+ z → f (G.info y) b = f' (G.info y) b) :
    reachFrom G f x z = reachFrom G f' x z := by
  induction z with
  | nil =>
    have hx : x = [] := List.eq_nil_of_suffix_nil hxz
    subst hx
    simp [reachFrom]
  | cons a z ih =>
    rcases List.suffix_cons_iff.1 hxz with he | he
    · subst he
      rw [reachFrom_self, reachFrom_self]
    · rw [reachFrom_cons G f he, reachFrom_cons G f' he,
        ih he fun y hy b hb => h y hy b (hb.trans (List.suffix_cons a z)),
        h z he a (List.suffix_refl _)]

variable [Fintype A]

/-- **Section 9.B** (MWG, pp. 270-272). Player `i`'s continuation payoff from node `x` when
moves are drawn from `f`: `∑_{z ∈ T, x ≤ z} P(z | x) u_i(z)`. -/
def cont (f : H → A → ℝ) (x : List A) (i : I) : ℝ :=
  ∑ z ∈ G.terminals with x <:+ z, reachFrom G f x z * G.payoff i z

/-- At a terminal node the continuation payoff is the payoff there. -/
theorem cont_terminal (f : H → A → ℝ) {x : List A} (hx : G.IsTerminal x) (i : I) :
    cont G f x i = G.payoff i x := by
  have : (G.terminals.filter fun z => x <:+ z) = {x} := by
    ext z
    simp only [Finset.mem_filter, mem_terminals, Finset.mem_singleton]
    constructor
    · rintro ⟨hz, hxz⟩
      exact G.eq_of_terminal_suffix hx hz.1 hxz
    · rintro rfl
      exact ⟨hx, List.suffix_refl _⟩
  rw [cont, this, Finset.sum_singleton, reachFrom_self, one_mul]

/-- **Section 9.B** (MWG, pp. 270-271). The backward-induction recursion: at a decision node
the continuation payoff is the expected continuation payoff of the successors. -/
theorem cont_decision (f : H → A → ℝ) {x : List A} (hx : G.IsDecision x) (i : I) :
    cont G f x i = ∑ a ∈ G.avail (G.info x), f (G.info x) a * cont G f (a :: x) i := by
  unfold cont
  rw [G.sum_terminals_below_decision hx]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun z hz => ?_
  rw [Finset.mem_filter] at hz
  rw [reachFrom_trans G f (List.suffix_cons a x) hz.2, reachFrom_cons_self]
  ring

/-- The backward-induction recursion in one formula, for evaluating continuation payoffs in
concrete games. -/
theorem cont_eq (f : H → A → ℝ) {x : List A} (hx : x ∈ G.nodes) (i : I) :
    cont G f x i = if ∃ b, b :: x ∈ G.nodes then
      ∑ a ∈ G.avail (G.info x), f (G.info x) a * cont G f (a :: x) i else G.payoff i x := by
  split_ifs with h
  · exact cont_decision G f ⟨hx, h⟩ i
  · exact cont_terminal G f ⟨hx, fun b hb => h ⟨b, hb⟩⟩ i

/-- The backward-induction recursion without side conditions (continuation payoffs vanish off
the tree), for evaluating continuation payoffs in concrete games by rewriting. -/
theorem cont_unfold (f : H → A → ℝ) (x : List A) (i : I) :
    cont G f x i = if x ∈ G.nodes then (if ∃ b, b :: x ∈ G.nodes then
      ∑ a ∈ G.avail (G.info x), f (G.info x) a * cont G f (a :: x) i else G.payoff i x)
      else 0 := by
  split_ifs with hx hb
  · rw [cont_eq G f hx]
    simp only [hb, ↓reduceIte]
  · rw [cont_eq G f hx]
    simp only [hb, ↓reduceIte]
  · unfold cont
    refine Finset.sum_eq_zero fun z hz => ?_
    rw [Finset.mem_filter, mem_terminals] at hz
    exact absurd (G.mem_of_suffix hz.2 hz.1.1) hx

/-- At the initial node the continuation payoff is the expected payoff
`∑_{z ∈ T} P(z) u_i(z)`. -/
theorem cont_nil (f : H → A → ℝ) (i : I) :
    cont G f [] i = ∑ z ∈ G.terminals, G.reach f z * G.payoff i z := by
  unfold cont
  simp [reachFrom_nil]

/-- `P(x) · cont(x) = ∑_{z ≥ x} P(z) u_i(z)`. -/
theorem reach_mul_cont (f : H → A → ℝ) (x : List A) (i : I) :
    G.reach f x * cont G f x i =
      ∑ z ∈ G.terminals with x <:+ z, G.reach f z * G.payoff i z := by
  unfold cont
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun z hz => ?_
  rw [Finset.mem_filter] at hz
  rw [reach_eq_mul_reachFrom G f hz.2]
  ring

/-- The continuation payoff from `x` depends only on the moves at the information sets of the
decision nodes following (or equal to) `x`. -/
theorem cont_congr {f f' : H → A → ℝ} {x : List A}
    (h : ∀ y, G.IsDecision y → x <:+ y → f (G.info y) = f' (G.info y)) (i : I) :
    cont G f x i = cont G f' x i := by
  unfold cont
  refine Finset.sum_congr rfl fun z hz => ?_
  rw [Finset.mem_filter, mem_terminals] at hz
  rw [reachFrom_congr G hz.2 fun y hy b hb => by
    rw [h y (G.isDecision_of_cons_mem (G.mem_of_suffix hb hz.1.1)) hy]]

/-- Probabilities of moving from `x` to the terminal nodes after it sum to one. -/
theorem sum_reachFrom_terminals {f : H → A → ℝ} (hf1 : ∀ k, ∑ a ∈ G.avail k, f k a = 1)
    {x : List A} (hx : x ∈ G.nodes) :
    ∑ z ∈ G.terminals with x <:+ z, reachFrom G f x z = 1 := by
  suffices h : ∀ n, ∀ x ∈ G.nodes, G.nodes.sup List.length - x.length ≤ n →
      ∑ z ∈ G.terminals with x <:+ z, reachFrom G f x z = 1 from h _ x hx le_rfl
  intro n
  induction n with
  | zero =>
    intro y hy hn
    have hterm : G.IsTerminal y := by
      refine ⟨hy, fun b hb => ?_⟩
      have := G.length_le_sup hb
      simp only [List.length_cons] at this
      omega
    have hs : (G.terminals.filter fun z => y <:+ z) = {y} := by
      ext z
      simp only [Finset.mem_filter, mem_terminals, Finset.mem_singleton]
      constructor
      · rintro ⟨hz, hyz⟩
        exact G.eq_of_terminal_suffix hterm hz.1 hyz
      · rintro rfl
        exact ⟨hterm, List.suffix_refl _⟩
    rw [hs, Finset.sum_singleton, reachFrom_self]
  | succ n ih =>
    intro y hy hn
    rcases (G.isDecision_or_isTerminal hy).1 with hdec | hterm
    · rw [G.sum_terminals_below_decision hdec]
      have hc : ∀ a ∈ G.avail (G.info y), ∑ z ∈ G.terminals with a :: y <:+ z,
          reachFrom G f y z = f (G.info y) a := by
        intro a ha
        have hmem := G.cons_mem_of_mem_avail hdec ha
        have hl := G.length_le_sup hmem
        simp only [List.length_cons] at hl
        have := ih (a :: y) hmem (by simp only [List.length_cons]; omega)
        rw [← mul_one (f (G.info y) a), ← this, Finset.mul_sum]
        refine Finset.sum_congr rfl fun z hz => ?_
        rw [Finset.mem_filter] at hz
        rw [reachFrom_trans G f (List.suffix_cons a y) hz.2, reachFrom_cons_self]
      rw [Finset.sum_congr rfl hc, hf1]
    · have hs : (G.terminals.filter fun z => y <:+ z) = {y} := by
        ext z
        simp only [Finset.mem_filter, mem_terminals, Finset.mem_singleton]
        constructor
        · rintro ⟨hz, hyz⟩
          exact G.eq_of_terminal_suffix hterm hz.1 hyz
        · rintro rfl
          exact ⟨hterm, List.suffix_refl _⟩
      rw [hs, Finset.sum_singleton, reachFrom_self]

/-- Continuation payoffs are bounded below by the smallest terminal payoff. -/
theorem le_cont {f : H → A → ℝ} (hf0 : ∀ k a, 0 ≤ f k a)
    (hf1 : ∀ k, ∑ a ∈ G.avail k, f k a = 1)
    {x : List A} (hx : x ∈ G.nodes) (i : I) (m : ℝ) (hm : ∀ z ∈ G.terminals, m ≤ G.payoff i z) :
    m ≤ cont G f x i := by
  have key := sum_reachFrom_terminals G hf1 hx
  calc m = ∑ z ∈ G.terminals with x <:+ z, reachFrom G f x z * m := by
        rw [← Finset.sum_mul, key, one_mul]
    _ ≤ cont G f x i := by
        unfold cont
        refine Finset.sum_le_sum fun z hz => ?_
        rw [Finset.mem_filter] at hz
        exact mul_le_mul_of_nonneg_left (hm z hz.1) (reachFrom_nonneg G hf0 x z)

omit [Fintype A] in
/-- Splitting a sum over the nodes of a set `S` following a node `y ∉ S` by the
action taken at `y`. -/
theorem sum_suffix_split {S : Finset (List A)} (hS : ∀ x ∈ S, x ∈ G.nodes) {y : List A}
    (hyS : y ∉ S) (g : List A → ℝ) :
    ∑ x ∈ S with y <:+ x, g x = ∑ a ∈ G.avail (G.info y), ∑ x ∈ S with a :: y <:+ x, g x := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z hz => ?_
  by_cases hyz : y <:+ z
  · have hne : y ≠ z := by
      rintro rfl
      exact hyS hz
    obtain ⟨b, hb⟩ := exists_cons_suffix hyz hne
    have hbav : b ∈ G.avail (G.info y) := G.mem_avail_of_cons_mem (G.mem_of_suffix hb (hS z hz))
    have key : ∀ a, (a :: y <:+ z) ↔ a = b := by
      intro a
      constructor
      · intro ha
        have := suffix_unique ha hb (by simp)
        simpa using this
      · rintro rfl
        exact hb
    simp only [key, hyz, ite_true]
    rw [Finset.sum_ite_eq']
    simp [hbav]
  · have : ∀ a, ¬ (a :: y <:+ z) := fun a ha => hyz ((List.suffix_cons a y).trans ha)
    simp [this, hyz]

/-- The **entry nodes** of a set `D` of information sets after node `y`: decision nodes `x`
following `y` with `H(x) ∈ D` such that no decision node between `y` (inclusive) and `x`
(exclusive) has its information set in `D`. -/
def entryNodes (D : H → Prop) [DecidablePred D] (y : List A) : Finset (List A) :=
  G.decisionNodes.filter fun x => y <:+ x ∧ D (G.info x) ∧
    ∀ w ∈ G.decisionNodes, y <:+ w → w <:+ x → w ≠ x → ¬ D (G.info w)

/-- Membership in `entryNodes`. -/
theorem mem_entryNodes {D : H → Prop} [DecidablePred D] {y x : List A} :
    x ∈ entryNodes G D y ↔ G.IsDecision x ∧ y <:+ x ∧ D (G.info x) ∧
      ∀ w, G.IsDecision w → y <:+ w → w <:+ x → w ≠ x → ¬ D (G.info w) := by
  simp only [entryNodes, Finset.mem_filter, mem_decisionNodes]

/-- **Section 9.B/9.C decomposition.** If `f` and `f'` agree outside a set `D` of information
sets, then the difference of continuation payoffs from a node `y` is the sum over the entry
nodes `x` of `D` after `y` of `P(x | y) (cont f x − cont f' x)`. -/
theorem cont_sub_eq_sum_entry (D : H → Prop) [DecidablePred D] {f f' : H → A → ℝ}
    (hff : ∀ k, ¬ D k → f k = f' k) {y : List A} (hy : y ∈ G.nodes) (i : I) :
    cont G f y i - cont G f' y i =
      ∑ x ∈ entryNodes G D y, reachFrom G f y x * (cont G f x i - cont G f' x i) := by
  suffices h : ∀ n, ∀ y ∈ G.nodes, G.nodes.sup List.length - y.length ≤ n →
      cont G f y i - cont G f' y i =
        ∑ x ∈ entryNodes G D y, reachFrom G f y x * (cont G f x i - cont G f' x i) from
    h _ y hy le_rfl
  intro n
  induction n with
  | zero =>
    intro y hy hn
    have hterm : G.IsTerminal y := by
      refine ⟨hy, fun b hb => ?_⟩
      have := G.length_le_sup hb
      simp only [List.length_cons] at this
      omega
    have hE : entryNodes G D y = ∅ := by
      ext x
      simp only [mem_entryNodes, Finset.notMem_empty, iff_false]
      rintro ⟨hx, hyx, -⟩
      have := G.eq_of_terminal_suffix hterm hx.1 hyx
      subst this
      exact ((G.isDecision_or_isTerminal hy).2 ⟨hx, hterm⟩)
    rw [hE, Finset.sum_empty, cont_terminal G f hterm, cont_terminal G f' hterm, sub_self]
  | succ n ih =>
    intro y hy hn
    rcases (G.isDecision_or_isTerminal hy).1 with hdec | hterm
    · by_cases hD : D (G.info y)
      · have hE : entryNodes G D y = {y} := by
          ext x
          simp only [mem_entryNodes, Finset.mem_singleton]
          constructor
          · rintro ⟨-, hyx, -, hmin⟩
            by_contra hne
            exact hmin y hdec (List.suffix_refl _) hyx (Ne.symm hne) hD
          · rintro rfl
            refine ⟨hdec, List.suffix_refl _, hD, fun w _ hyw hwy hne => ?_⟩
            exact absurd (List.IsSuffix.eq_of_length hwy
              (le_antisymm hwy.length_le hyw.length_le)) hne
        rw [hE, Finset.sum_singleton, reachFrom_self, one_mul]
      · have hfy : f (G.info y) = f' (G.info y) := hff _ hD
        have hchild : ∀ a ∈ G.avail (G.info y),
            cont G f (a :: y) i - cont G f' (a :: y) i =
              ∑ x ∈ entryNodes G D (a :: y),
                reachFrom G f (a :: y) x * (cont G f x i - cont G f' x i) := by
          intro a ha
          have hmem := G.cons_mem_of_mem_avail hdec ha
          have hl := G.length_le_sup hmem
          simp only [List.length_cons] at hl
          exact ih (a :: y) hmem (by simp only [List.length_cons]; omega)
        rw [cont_decision G f hdec, cont_decision G f' hdec, hfy, ← Finset.sum_sub_distrib]
        simp_rw [← mul_sub]
        rw [Finset.sum_congr rfl fun a ha => by rw [hchild a ha]]
        have hyE : y ∉ entryNodes G D y := fun h => hD ((mem_entryNodes G).1 h).2.2.1
        have hsplit := sum_suffix_split G (S := entryNodes G D y)
          (fun x hx => ((mem_entryNodes G).1 hx).1.1) hyE
          (fun x => reachFrom G f y x * (cont G f x i - cont G f' x i))
        have hall : (entryNodes G D y).filter (fun x => y <:+ x) = entryNodes G D y :=
          Finset.filter_true_of_mem fun x hx => ((mem_entryNodes G).1 hx).2.1
        rw [hall] at hsplit
        rw [hsplit]
        refine Finset.sum_congr rfl fun a _ => ?_
        have hfil : (entryNodes G D y).filter (fun x => a :: y <:+ x) =
            entryNodes G D (a :: y) := by
          ext x
          simp only [Finset.mem_filter, mem_entryNodes]
          constructor
          · rintro ⟨⟨hx, -, hDx, hmin⟩, hay⟩
            exact ⟨hx, hay, hDx, fun w hw haw hwx hne =>
              hmin w hw ((List.suffix_cons a y).trans haw) hwx hne⟩
          · rintro ⟨hx, hay, hDx, hmin⟩
            refine ⟨⟨hx, (List.suffix_cons a y).trans hay, hDx, fun w hw hyw hwx hne => ?_⟩,
              hay⟩
            by_cases hwy : w = y
            · subst hwy
              exact hD
            · obtain ⟨b, hb⟩ := exists_cons_suffix hyw (Ne.symm hwy)
              have hbx : b :: y <:+ x := hb.trans hwx
              have hab : b :: y = a :: y := suffix_unique hbx hay (by simp)
              rw [hab] at hb
              exact hmin w hw hb hwx hne
        rw [hfil, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x hx => ?_
        have hay := ((mem_entryNodes G).1 hx).2.1
        rw [reachFrom_trans G f (List.suffix_cons a y) hay, reachFrom_cons_self, hfy]
        ring
    · have hE : entryNodes G D y = ∅ := by
        ext x
        simp only [mem_entryNodes, Finset.notMem_empty, iff_false]
        rintro ⟨hx, hyx, -⟩
        have := G.eq_of_terminal_suffix hterm hx.1 hyx
        subst this
        exact ((G.isDecision_or_isTerminal hy).2 ⟨hx, hterm⟩)
      rw [hE, Finset.sum_empty, cont_terminal G f hterm, cont_terminal G f' hterm, sub_self]

/-- Before the entry nodes of `D`, two move functions that agree outside `D` give the same
probability of reaching an entry node. -/
theorem reachFrom_entry_congr (D : H → Prop) [DecidablePred D] {f f' : H → A → ℝ}
    (hff : ∀ k, ¬ D k → f k = f' k) {y x : List A} (hx : x ∈ entryNodes G D y) :
    reachFrom G f y x = reachFrom G f' y x := by
  rw [mem_entryNodes] at hx
  obtain ⟨hdx, hyx, -, hmin⟩ := hx
  refine reachFrom_congr G hyx fun w hyw b hbw => ?_
  have hw : G.IsDecision w := G.isDecision_of_cons_mem (G.mem_of_suffix hbw hdx.1)
  have hwx : w <:+ x := (List.suffix_cons b w).trans hbw
  have hne : w ≠ x := by
    rintro rfl
    have := hbw.length_le
    simp at this
  rw [hff _ (hmin w hw hyw hwx hne)]

variable [DecidableEq I]

/-- A behaviour strategy profile: every player `i` uses a behaviour strategy `F i`
(Definition 7.E.2). Values of `F i` off player `i`'s information sets are irrelevant. -/
def IsBehaviorProfile (F : I → H → A → ℝ) : Prop := ∀ i, G.IsBehaviorStrategy i (F i)

omit [DecidableEq A] [Fintype A] [DecidableEq I] in
/-- The moves of a behaviour profile are nonnegative probabilities. -/
theorem assemble_nonneg {F : I → H → A → ℝ} (hF : IsBehaviorProfile G F) (k : H) (a : A) :
    0 ≤ G.assemble F k a := by
  cases hk : G.player k with
  | none => rw [G.assemble_of_none _ hk]; exact G.nature_nonneg k hk a
  | some j => rw [G.assemble_of_some _ hk]; exact ((hF j) k hk).1 a

omit [DecidableEq A] [Fintype A] [DecidableEq I] in
/-- The moves of a behaviour profile sum to one at every information set. -/
theorem assemble_sum {F : I → H → A → ℝ} (hF : IsBehaviorProfile G F) (k : H) :
    ∑ a ∈ G.avail k, G.assemble F k a = 1 := by
  cases hk : G.player k with
  | none => rw [G.assemble_of_none _ hk]; exact G.nature_sum k hk
  | some j => rw [G.assemble_of_some _ hk]; exact ((hF j) k hk).2.2

omit [DecidableEq A] [Fintype A] in
/-- Replacing one player's behaviour strategy by another behaviour strategy gives a behaviour
profile. -/
theorem isBehaviorProfile_update {F : I → H → A → ℝ} (hF : IsBehaviorProfile G F) {i : I}
    {g : H → A → ℝ} (hg : G.IsBehaviorStrategy i g) :
    IsBehaviorProfile G (Function.update F i g) := by
  intro j
  by_cases hj : j = i
  · subst hj
    simpa using hg
  · simpa [hj] using hF j

/-- **Definition 8.D.2 for an extensive form** (MWG, pp. 246 and 268). A behaviour profile
`F` is a Nash equilibrium of `Γ_E` if no player can raise her expected payoff by switching to
another behaviour strategy, the others' strategies held fixed. -/
def IsNashB (F : I → H → A → ℝ) : Prop :=
  IsBehaviorProfile G F ∧ ∀ i g, G.IsBehaviorStrategy i g →
    cont G (G.assemble (Function.update F i g)) [] i ≤ cont G (G.assemble F) [] i

/-- **Section 7.D** (MWG, p. 230). The normal-form payoff of a pure profile is the
continuation payoff at the initial node. -/
theorem toNormalForm_payoff_eq_cont (s : (i : I) → G.PureStrategy i)
    (i : I) : G.toNormalForm.payoff i s = cont G (G.pureProfile s) [] i := by
  rw [cont_nil]
  rfl

/-- A pure strategy profile as a behaviour profile. -/
def pureB (s : (i : I) → G.PureStrategy i) : I → H → A → ℝ := fun j => G.pureBeh (s j)

omit [Fintype A] in
/-- The moves of `pureB s` are those of the pure profile `s`. -/
theorem assemble_pureB (s : (i : I) → G.PureStrategy i) :
    G.assemble (pureB G s) = G.pureProfile s := rfl

omit [Fintype A] in
/-- A pure strategy profile is a behaviour profile. -/
theorem isBehaviorProfile_pureB (s : (i : I) → G.PureStrategy i) :
    IsBehaviorProfile G (pureB G s) := fun j => G.isBehaviorStrategy_pureBeh (s j)

omit [Fintype A] in
/-- Updating one player's pure strategy commutes with `pureB`. -/
theorem pureB_update (s : (i : I) → G.PureStrategy i) (i : I) (t : G.PureStrategy i) :
    pureB G (Function.update s i t) = Function.update (pureB G s) i (G.pureBeh t) := by
  funext j
  exact Function.apply_update (fun j => G.pureBeh (i := j)) s i t j

/-- **Section 9.B** (MWG, p. 269). A pure profile that is a Nash equilibrium of `Γ_E` in
behaviour strategies is a (pure strategy) Nash equilibrium of the induced normal form. -/
theorem IsNashB.isNashEquilibrium_pure
    {s : (i : I) → G.PureStrategy i} (h : IsNashB G (pureB G s)) :
    MWG.SimultaneousMoveGames.IsNashEquilibrium G.toNormalForm s := by
  intro i t
  rw [toNormalForm_payoff_eq_cont, toNormalForm_payoff_eq_cont, ← assemble_pureB,
    ← assemble_pureB, pureB_update]
  exact h.2 i _ (G.isBehaviorStrategy_pureBeh t)

/-- **Definition 9.B.1** (MWG, p. 274). The decision node `x` is the initial node of a
subgame: (i) its information set contains `x` alone (the subgame contains `x` and all its
successors, and only these), and (ii) no information set is broken: if a decision node `y`
follows `x`, then every node of `H(y)` follows `x`. -/
def IsSubgameRoot (x : List A) : Prop :=
  G.IsDecision x ∧ (∀ y, G.IsDecision y → G.info y = G.info x → y = x) ∧
    ∀ y, G.IsDecision y → x <:+ y → ∀ y', G.IsDecision y' → G.info y' = G.info y → x <:+ y'

/-- **Section 9.B** (MWG, p. 275). The profile `F` induces a Nash equilibrium in the subgame
starting at `x`: no player can raise her continuation payoff from `x` by changing her
behaviour strategy (only her moves inside the subgame matter, `cont_congr`). -/
def InducesNashAt (F : I → H → A → ℝ) (x : List A) : Prop :=
  ∀ i g, G.IsBehaviorStrategy i g →
    cont G (G.assemble (Function.update F i g)) x i ≤ cont G (G.assemble F) x i

/-- **Definition 9.B.2** (MWG, p. 275). A subgame perfect Nash equilibrium: a behaviour
profile inducing a Nash equilibrium in every subgame. -/
def IsSPNE (F : I → H → A → ℝ) : Prop :=
  IsBehaviorProfile G F ∧ ∀ x, IsSubgameRoot G x → InducesNashAt G F x

omit [DecidableEq A] [Fintype A] [DecidableEq I] in
/-- **Section 9.B** (MWG, p. 274). Without absent-mindedness, the game as a whole is a
subgame when its initial node is a decision node. -/
theorem isSubgameRoot_nil (hNA : G.NoAbsentMindedness) (h : G.IsDecision []) :
    IsSubgameRoot G [] := by
  refine ⟨h, fun y hy he => ?_, fun y _ _ y' _ _ => List.nil_suffix⟩
  by_contra hne
  exact hNA [] h.1 y hy.1 h.2 hy.2 he.symm ⟨List.nil_suffix, Ne.symm hne⟩

/-- **Section 9.B** (MWG, p. 275). Any SPNE is a Nash equilibrium (the game as a whole is a
subgame). -/
theorem isNashB_of_isSPNE (hNA : G.NoAbsentMindedness) {F : I → H → A → ℝ}
    (h : IsSPNE G F) : IsNashB G F := by
  refine ⟨h.1, fun i g hg => ?_⟩
  by_cases hd : G.IsDecision []
  · exact h.2 [] (isSubgameRoot_nil G hNA hd) i g hg
  · have ht : G.IsTerminal [] := ⟨G.nil_mem, fun b hb => hd ⟨G.nil_mem, b, hb⟩⟩
    rw [cont_terminal _ _ ht, cont_terminal _ _ ht]

/-- **Exercise 9.B.2(a)** (MWG, p. 275). If the only subgame is the game as a whole, every
Nash equilibrium is subgame perfect. -/
theorem exercise_9_B_2a {F : I → H → A → ℝ} (honly : ∀ x, IsSubgameRoot G x → x = [])
    (h : IsNashB G F) : IsSPNE G F := by
  refine ⟨h.1, fun x hx => ?_⟩
  obtain rfl := honly x hx
  exact h.2

/-- A subgame of the subgame starting at `x`: a decision node `y` after `x` whose
information set within the subgame is `{y}` and whose successors' information sets are not
broken within the subgame (Definition 9.B.1 applied to the subgame). -/
def IsSubgameRootWithin (x y : List A) : Prop :=
  G.IsDecision y ∧ x <:+ y ∧ (∀ y', G.IsDecision y' → x <:+ y' → G.info y' = G.info y → y' = y) ∧
    ∀ w, G.IsDecision w → y <:+ w → ∀ w', G.IsDecision w' → x <:+ w' → G.info w' = G.info w →
      y <:+ w'

omit [DecidableEq A] [Fintype A] [DecidableEq I] in
/-- The subgames of the subgame starting at `x` are exactly the subgames of `Γ_E` starting
after `x`. -/
theorem isSubgameRootWithin_iff {x y : List A} (hx : IsSubgameRoot G x) (hxy : x <:+ y) :
    IsSubgameRootWithin G x y ↔ IsSubgameRoot G y := by
  constructor
  · rintro ⟨hy, -, hsing, hbr⟩
    refine ⟨hy, fun y' hy' he => hsing y' hy' (hx.2.2 y hy hxy y' hy' he) he,
      fun w hw hyw w' hw' he => hbr w hw hyw w' hw' (hx.2.2 w hw (hxy.trans hyw) w' hw' he) he⟩
  · rintro ⟨hy, hsing, hbr⟩
    exact ⟨hy, hxy, fun y' hy' _ he => hsing y' hy' he,
      fun w hw hyw w' hw' _ he => hbr w hw hyw w' hw' he⟩

/-- **Exercise 9.B.2(b)** (MWG, p. 275). An SPNE induces a subgame perfect Nash equilibrium in
every subgame: it induces a Nash equilibrium in every subgame of every subgame. -/
theorem exercise_9_B_2b {F : I → H → A → ℝ} (h : IsSPNE G F) {x : List A}
    (hx : IsSubgameRoot G x) :
    InducesNashAt G F x ∧ ∀ y, IsSubgameRootWithin G x y → InducesNashAt G F y :=
  ⟨h.2 x hx, fun y hy => h.2 y ((isSubgameRootWithin_iff G hx hy.2.1).1 hy)⟩

end MWG.DynamicGames

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Backward induction and Zermelo's theorem

MWG, Section 9.B, pp. 270-276: backward induction in finite games of perfect information,
Proposition 9.B.1 (Zermelo's theorem) and Proposition 9.B.2.

* `OneShotOptimalAt G F x`: at decision node `x` the mover's continuation payoff is at least
  that of every immediate successor, i.e. her move at `x` is optimal given the continuation
  play (the backward-induction requirement).
* `oneShot_deviation_principle` (the **one-shot deviation principle** for finite trees): if
  the moves are one-shot optimal at every decision node, then no player can gain from any
  change of her behaviour strategy, from any node on. In a game of perfect information the
  converse holds (`oneShotOptimal_of_isSPNE`), so SPNE = backward induction
  (`isSPNE_iff_oneShotOptimal`).
* `exists_backwardInduction`: in a finite game of perfect information a pure profile derived
  by backward induction exists (the procedure is well defined).
* `proposition_9_B_1` (Zermelo): a pure Nash equilibrium derived by backward induction exists;
  every such profile is a Nash equilibrium of `Γ_E` and of its normal form; with no moves of
  nature and no player having equal payoffs at two terminal nodes it is unique.
* `proposition_9_B_2`: a pure SPNE exists; with the same proviso it is unique (as a behaviour
  profile).
* Correction: with moves of nature the uniqueness clause fails (`natureTie`,
  `zermelo_uniqueness_fails_with_nature`): ties arise between lotteries over terminal nodes.
* `exercise_9_B_4`: in a finite two-player zero-sum game of perfect information all subgame
  perfect Nash equilibria have the same payoffs.
-/

namespace MWG.DynamicGames

open MWG.NoncooperativeGames MWG.NoncooperativeGames.ExtensiveForm

variable {I A H : Type*} (G : ExtensiveForm I A H) [DecidableEq A] [Fintype A] [DecidableEq I]
  [DecidableEq H]

/-- **Section 9.B** (MWG, p. 270). The move at decision node `x` is optimal for its mover given
the continuation play: no immediate successor gives the mover a higher continuation payoff. -/
def OneShotOptimalAt (F : I → H → A → ℝ) (x : List A) : Prop :=
  ∀ j, G.player (G.info x) = some j → ∀ a ∈ G.avail (G.info x),
    cont G (G.assemble F) (a :: x) j ≤ cont G (G.assemble F) x j

omit [DecidableEq A] [Fintype A] [DecidableEq H] in
/-- The moves of `update F i g` at an information set of nature. -/
theorem assemble_update_of_none (F : I → H → A → ℝ) (i : I) (g : H → A → ℝ) {k : H}
    (hk : G.player k = none) : G.assemble (Function.update F i g) k = G.assemble F k := by
  rw [G.assemble_of_none _ hk, G.assemble_of_none _ hk]

omit [DecidableEq A] [Fintype A] [DecidableEq H] in
/-- The moves of `update F i g` at an information set of a player `j ≠ i`. -/
theorem assemble_update_of_ne (F : I → H → A → ℝ) {i j : I} (g : H → A → ℝ) {k : H}
    (hk : G.player k = some j) (hji : j ≠ i) :
    G.assemble (Function.update F i g) k = G.assemble F k := by
  rw [G.assemble_of_some _ hk, G.assemble_of_some _ hk, Function.update_of_ne hji]

omit [DecidableEq A] [Fintype A] [DecidableEq H] in
/-- The moves of `update F i g` at an information set of player `i`. -/
theorem assemble_update_self (F : I → H → A → ℝ) {i : I} (g : H → A → ℝ) {k : H}
    (hk : G.player k = some i) : G.assemble (Function.update F i g) k = g k := by
  rw [G.assemble_of_some _ hk, Function.update_self]

omit [DecidableEq H] in
/-- **One-shot deviation principle** (finite trees; MWG, proof of Proposition 9.B.1,
pp. 272-273). If a behaviour profile's moves are one-shot optimal at every decision node, then
from every node no player gains by switching to any other behaviour strategy. -/
theorem oneShot_deviation_principle {F : I → H → A → ℝ} (hF : IsBehaviorProfile G F)
    (hopt : ∀ x, G.IsDecision x → OneShotOptimalAt G F x) {x : List A} (hx : x ∈ G.nodes)
    (i : I) {g : H → A → ℝ} (hg : G.IsBehaviorStrategy i g) :
    cont G (G.assemble (Function.update F i g)) x i ≤ cont G (G.assemble F) x i := by
  suffices h : ∀ n, ∀ x ∈ G.nodes, G.nodes.sup List.length - x.length ≤ n →
      cont G (G.assemble (Function.update F i g)) x i ≤ cont G (G.assemble F) x i from
    h _ x hx le_rfl
  intro n
  induction n with
  | zero =>
    intro y hy hn
    have hterm : G.IsTerminal y := by
      refine ⟨hy, fun b hb => ?_⟩
      have := G.length_le_sup hb
      simp only [List.length_cons] at this
      omega
    rw [cont_terminal _ _ hterm, cont_terminal _ _ hterm]
  | succ n ih =>
    intro y hy hn
    rcases (G.isDecision_or_isTerminal hy).1 with hdec | hterm
    · have hchild : ∀ a ∈ G.avail (G.info y),
          cont G (G.assemble (Function.update F i g)) (a :: y) i ≤
            cont G (G.assemble F) (a :: y) i := by
        intro a ha
        have hmem := G.cons_mem_of_mem_avail hdec ha
        have hl := G.length_le_sup hmem
        simp only [List.length_cons] at hl
        exact ih (a :: y) hmem (by simp only [List.length_cons]; omega)
      rw [cont_decision _ _ hdec, cont_decision _ (G.assemble F) hdec]
      cases hk : G.player (G.info y) with
      | none =>
        rw [assemble_update_of_none G F i g hk]
        exact Finset.sum_le_sum fun a ha =>
          mul_le_mul_of_nonneg_left (hchild a ha) (assemble_nonneg G hF _ _)
      | some j =>
        by_cases hji : j = i
        · subst hji
          rw [assemble_update_self G F g hk]
          have hsum : ∑ a ∈ G.avail (G.info y), G.assemble F (G.info y) a *
              cont G (G.assemble F) (a :: y) j = cont G (G.assemble F) y j := by
            rw [cont_decision _ _ hdec]
          calc ∑ a ∈ G.avail (G.info y), g (G.info y) a *
                cont G (G.assemble (Function.update F j g)) (a :: y) j
              ≤ ∑ a ∈ G.avail (G.info y), g (G.info y) a * cont G (G.assemble F) y j :=
                Finset.sum_le_sum fun a ha => mul_le_mul_of_nonneg_left
                  ((hchild a ha).trans (hopt y hdec j hk a ha)) ((hg _ hk).1 a)
            _ = cont G (G.assemble F) y j := by rw [← Finset.sum_mul, (hg _ hk).2.2, one_mul]
            _ = _ := hsum.symm
        · rw [assemble_update_of_ne G F g hk hji]
          exact Finset.sum_le_sum fun a ha =>
            mul_le_mul_of_nonneg_left (hchild a ha) (assemble_nonneg G hF _ _)
    · rw [cont_terminal _ _ hterm, cont_terminal _ _ hterm]

omit [DecidableEq H] in
/-- **One-shot deviation principle, consequence.** A behaviour profile whose moves are one-shot
optimal at every decision node is a subgame perfect Nash equilibrium (in every game). -/
theorem isSPNE_of_oneShotOptimal {F : I → H → A → ℝ} (hF : IsBehaviorProfile G F)
    (hopt : ∀ x, G.IsDecision x → OneShotOptimalAt G F x) : IsSPNE G F :=
  ⟨hF, fun _ hx i _ hg => oneShot_deviation_principle G hF hopt hx.1.1 i hg⟩

omit [DecidableEq A] [Fintype A] [DecidableEq I] [DecidableEq H] in
/-- **Section 9.B** (MWG, p. 275; Exercise 9.B.1). In a game of perfect information every
decision node initiates a subgame. -/
theorem isSubgameRoot_of_perfectInformation (hPI : G.PerfectInformation) {x : List A}
    (hx : G.IsDecision x) : IsSubgameRoot G x := by
  refine ⟨hx, fun y hy he => hPI y hy.1 x hx.1 hy.2 hx.2 he, fun y hy hxy y' hy' he => ?_⟩
  rw [hPI y' hy'.1 y hy.1 hy'.2 hy.2 he]
  exact hxy

omit [DecidableEq A] [Fintype A] [DecidableEq I] [DecidableEq H] in
/-- In a game of perfect information, the information set of a decision node does not recur
after it. -/
theorem info_ne_of_perfectInformation (hPI : G.PerfectInformation) {x y : List A}
    (hx : G.IsDecision x) (hy : G.IsDecision y) {a : A} (hxy : a :: x <:+ y) :
    G.info y ≠ G.info x := by
  intro he
  have := hPI y hy.1 x hx.1 hy.2 hx.2 he
  subst this
  have := hxy.length_le
  simp at this

/-- The move function putting probability one on `a`. -/
def dirac (a : A) : A → ℝ := fun b => if b = a then 1 else 0

omit [DecidableEq I] in
/-- With the move at `x` replaced by a sure move `a`, the continuation from `x` is the
continuation from `a :: x` (perfect information). -/
theorem cont_dirac_update (hPI : G.PerfectInformation) (f : H → A → ℝ) {x : List A}
    (hx : G.IsDecision x) {a : A} (ha : a ∈ G.avail (G.info x)) (i : I) :
    cont G (Function.update f (G.info x) (dirac a)) x i = cont G f (a :: x) i := by
  rw [cont_decision _ _ hx, Function.update_self]
  simp only [dirac, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq' (G.avail (G.info x))]
  simp only [ha, ↓reduceIte]
  refine cont_congr G (fun y hy hay => ?_) i
  rw [Function.update_of_ne (info_ne_of_perfectInformation G hPI hx hy hay)]

omit [DecidableEq H] in
/-- **Section 9.B** (MWG, p. 275). In a game of perfect information an SPNE is one-shot
optimal at every decision node: each decision node starts a subgame, and a sure move is a
behaviour deviation. -/
theorem oneShotOptimal_of_isSPNE (hPI : G.PerfectInformation) {F : I → H → A → ℝ}
    (h : IsSPNE G F) {x : List A} (hx : G.IsDecision x) : OneShotOptimalAt G F x := by
  classical
  intro j hj a ha
  set g : H → A → ℝ := Function.update (F j) (G.info x) (dirac a) with hg_def
  have hg : G.IsBehaviorStrategy j g := by
    intro k hk
    by_cases hkx : k = G.info x
    · subst hkx
      simp only [hg_def, Function.update_self]
      refine ⟨fun b => by unfold dirac; split_ifs <;> norm_num, fun b hb => ?_, ?_⟩
      · have hba : b ≠ a := fun h => hb (h ▸ ha)
        simp [dirac, hba]
      · simp only [dirac]
        rw [Finset.sum_ite_eq' (G.avail (G.info x))]
        simp [ha]
    · simp only [hg_def, Function.update_of_ne hkx]
      exact h.1 j k hk
  have hdev := h.2 x (isSubgameRoot_of_perfectInformation G hPI hx) j g hg
  have heq : G.assemble (Function.update F j g) =
      Function.update (G.assemble F) (G.info x) (dirac a) := by
    funext k
    by_cases hkx : k = G.info x
    · subst hkx
      rw [assemble_update_self G F g hj, Function.update_self, hg_def, Function.update_self]
    · rw [Function.update_of_ne hkx]
      cases hk : G.player k with
      | none => rw [assemble_update_of_none G F j g hk]
      | some l =>
        by_cases hlj : l = j
        · subst hlj
          rw [assemble_update_self G F g hk, hg_def, Function.update_of_ne hkx,
            G.assemble_of_some _ hk]
        · rw [assemble_update_of_ne G F g hk hlj]
  rw [heq, cont_dirac_update G hPI _ hx ha] at hdev
  exact hdev

omit [DecidableEq H] in
/-- **Section 9.B** (MWG, pp. 275-276). In a finite game of perfect information the subgame
perfect Nash equilibria are exactly the behaviour profiles whose moves are optimal at every
decision node given the continuation play (backward induction). -/
theorem isSPNE_iff_oneShotOptimal (hPI : G.PerfectInformation) {F : I → H → A → ℝ}
    (hF : IsBehaviorProfile G F) :
    IsSPNE G F ↔ ∀ x, G.IsDecision x → OneShotOptimalAt G F x := by
  classical
  exact
    ⟨fun h _ hx => oneShotOptimal_of_isSPNE G hPI h hx, isSPNE_of_oneShotOptimal G hF⟩

/-- **Section 9.B** (MWG, p. 270). A pure strategy profile derived through backward induction:
its moves are optimal at every decision node given the continuation play. -/
def IsBackwardInduction (s : (i : I) → G.PureStrategy i) : Prop :=
  ∀ x, G.IsDecision x → OneShotOptimalAt G (pureB G s) x

/-- The pure strategy profile in which every player plays `c k` at each of her information
sets. -/
def pureOfChoice (c : H → A) (hc : ∀ k, c k ∈ G.avail k) : (i : I) → G.PureStrategy i :=
  fun i => G.pureOfFun i c fun k _ => hc k

omit [DecidableEq H] in
/-- At a player's decision node the continuation payoff of a pure profile is that of the
chosen successor. -/
theorem cont_pureOfChoice (c : H → A) (hc : ∀ k, c k ∈ G.avail k) {x : List A}
    (hx : G.IsDecision x) {j : I} (hj : G.player (G.info x) = some j) (i : I) :
    cont G (G.assemble (pureB G (pureOfChoice G c hc))) x i =
      cont G (G.assemble (pureB G (pureOfChoice G c hc))) (c (G.info x) :: x) i := by
  rw [cont_decision _ _ hx, assemble_pureB, Finset.sum_eq_single (c (G.info x))]
  · simp [G.pureProfile_apply _ hj, pureOfChoice]
  · intro b _ hb
    simp [G.pureProfile_apply _ hj, pureOfChoice, Ne.symm hb]
  · intro h
    exact absurd (hc _) h

omit [DecidableEq H] in
/-- **Section 9.B** (MWG, pp. 270-272). In a finite game of perfect information the backward
induction procedure is well defined: there is a pure strategy profile whose moves are optimal
at every decision node given the continuation play. -/
theorem exists_backwardInduction (hPI : G.PerfectInformation) :
    ∃ s : (i : I) → G.PureStrategy i, IsBackwardInduction G s := by
  classical
  set D := G.nodes.sup List.length
  -- downward induction on the length of the decision nodes
  suffices h : ∀ n, ∃ c : H → A, ∃ hc : ∀ k, c k ∈ G.avail k, ∀ x, G.IsDecision x →
      D ≤ x.length + n → OneShotOptimalAt G (pureB G (pureOfChoice G c hc)) x by
    obtain ⟨c, hc, h⟩ := h D
    exact ⟨pureOfChoice G c hc, fun x hx => h x hx (by omega)⟩
  intro n
  induction n with
  | zero =>
    refine ⟨fun k => (G.avail_nonempty k).choose, fun k => (G.avail_nonempty k).choose_spec,
      fun x hx hl => ?_⟩
    obtain ⟨b, hb⟩ := hx.2
    have := G.length_le_sup hb
    simp only [List.length_cons] at this
    omega
  | succ n ih =>
    obtain ⟨c, hc, hopt⟩ := ih
    set F := pureB G (pureOfChoice G c hc)
    -- the new choice at the information sets of decision nodes of length `D - (n+1)`
    let best : H → A := fun k =>
      match G.player k with
      | none => c k
      | some j =>
        if (G.rep k).length + (n + 1) = D then
          ((G.avail k).exists_max_image (fun a => cont G (G.assemble F) (a :: G.rep k) j)
            (G.avail_nonempty k)).choose
        else c k
    have hbest : ∀ k, best k ∈ G.avail k := by
      intro k
      simp only [best]
      split
      · exact hc k
      · split_ifs
        · exact (Exists.choose_spec ((G.avail k).exists_max_image _ (G.avail_nonempty k))).1
        · exact hc k
    refine ⟨best, hbest, ?_⟩
    set F' := pureB G (pureOfChoice G best hbest)
    -- nodes of length at least `D - n` see no change
    have hrep : ∀ y, G.IsDecision y → G.rep (G.info y) = y := fun y hy =>
      hPI _ (G.rep_isDecision _).1 y hy.1 (G.rep_isDecision _).2 hy.2 (G.info_rep _)
    have hsame : ∀ y, G.IsDecision y → D ≤ y.length + n →
        G.assemble F' (G.info y) = G.assemble F (G.info y) := by
      intro y hy hl
      cases hk : G.player (G.info y) with
      | none => rw [G.assemble_of_none _ hk, G.assemble_of_none _ hk]
      | some j =>
        have hbk : best (G.info y) = c (G.info y) := by
          have hne : ¬ (y.length + (n + 1) = D) := by omega
          simp only [best, hk, hrep y hy, hne, ite_false]
        funext a
        simp only [F', F, assemble_pureB, G.pureProfile_apply _ hk, pureOfChoice,
          pureOfFun_apply, hbk]
        split_ifs with h1 <;> simp [h1]
    have hcont : ∀ y, y ∈ G.nodes → D ≤ y.length + n → ∀ i,
        cont G (G.assemble F') y i = cont G (G.assemble F) y i := by
      intro y _ hl i
      exact cont_congr G (fun w hw hyw => hsame w hw (by have := hyw.length_le; omega)) i
    intro x hx hl
    by_cases hlx : D ≤ x.length + n
    · intro j hj a ha
      have hax : a :: x ∈ G.nodes := G.cons_mem_of_mem_avail hx ha
      rw [hcont x hx.1 hlx, hcont (a :: x) hax (by simp; omega)]
      exact hopt x hx hlx j hj a ha
    · have hxl : x.length + (n + 1) = D := by omega
      intro j hj a ha
      have hk : best (G.info x) = ((G.avail (G.info x)).exists_max_image
          (fun a => cont G (G.assemble F) (a :: G.rep (G.info x)) j)
          (G.avail_nonempty _)).choose := by
        simp only [best, hj, hrep x hx, hxl, ite_true]
      have hmax := (Exists.choose_spec ((G.avail (G.info x)).exists_max_image
          (fun a => cont G (G.assemble F) (a :: G.rep (G.info x)) j) (G.avail_nonempty _)))
      rw [← hk, hrep x hx] at hmax
      have hax : a :: x ∈ G.nodes := G.cons_mem_of_mem_avail hx ha
      have hbx : best (G.info x) :: x ∈ G.nodes := G.cons_mem_of_mem_avail hx (hbest _)
      rw [cont_pureOfChoice G best hbest hx hj, hcont _ hbx (by simp; omega),
        hcont _ hax (by simp; omega)]
      exact hmax.2 a ha

omit [DecidableEq I] [DecidableEq H] in
/-- Uniqueness core: with no moves of nature and no player having equal payoffs at two
terminal nodes, two profiles that are one-shot optimal everywhere have the same moves at every
information set after `x`, and both lead from `x` to the same terminal node. -/
theorem oneShotOptimal_unique (hN : ∀ k, G.player k ≠ none)
    (hinj : ∀ i, ∀ z ∈ G.terminals, ∀ z' ∈ G.terminals, G.payoff i z = G.payoff i z' → z = z')
    {F F' : I → H → A → ℝ} (hF : IsBehaviorProfile G F) (hF' : IsBehaviorProfile G F')
    (hopt : ∀ x, G.IsDecision x → OneShotOptimalAt G F x)
    (hopt' : ∀ x, G.IsDecision x → OneShotOptimalAt G F' x) {x : List A} (hx : x ∈ G.nodes) :
    (∃ z ∈ G.terminals, x <:+ z ∧ ∀ i, cont G (G.assemble F) x i = G.payoff i z ∧
        cont G (G.assemble F') x i = G.payoff i z) ∧
      ∀ y, G.IsDecision y → x <:+ y → G.assemble F (G.info y) = G.assemble F' (G.info y) := by
  suffices h : ∀ n, ∀ x ∈ G.nodes, G.nodes.sup List.length - x.length ≤ n →
      (∃ z ∈ G.terminals, x <:+ z ∧ ∀ i, cont G (G.assemble F) x i = G.payoff i z ∧
        cont G (G.assemble F') x i = G.payoff i z) ∧
      ∀ y, G.IsDecision y → x <:+ y → G.assemble F (G.info y) = G.assemble F' (G.info y) from
    h _ x hx le_rfl
  intro n
  induction n with
  | zero =>
    intro y hy hn
    have hterm : G.IsTerminal y := by
      refine ⟨hy, fun b hb => ?_⟩
      have := G.length_le_sup hb
      simp only [List.length_cons] at this
      omega
    refine ⟨⟨y, (mem_terminals G).2 hterm, List.suffix_refl _, fun i =>
      ⟨cont_terminal _ _ hterm i, cont_terminal _ _ hterm i⟩⟩, fun w hw hyw => ?_⟩
    have := G.eq_of_terminal_suffix hterm hw.1 hyw
    subst this
    exact absurd ⟨hw, hterm⟩ (G.isDecision_or_isTerminal hy).2
  | succ n ih =>
    intro y hy hn
    rcases (G.isDecision_or_isTerminal hy).1 with hdec | hterm
    · set k := G.info y with hkdef
      have hchild : ∀ a ∈ G.avail (G.info y),
          (∃ z ∈ G.terminals, a :: y <:+ z ∧ ∀ i, cont G (G.assemble F) (a :: y) i =
            G.payoff i z ∧ cont G (G.assemble F') (a :: y) i = G.payoff i z) ∧
          ∀ w, G.IsDecision w → a :: y <:+ w →
            G.assemble F (G.info w) = G.assemble F' (G.info w) := fun a ha => by
        have hmem := G.cons_mem_of_mem_avail hdec ha
        have hl := G.length_le_sup hmem
        simp only [List.length_cons] at hl
        exact ih (a :: y) hmem (by simp only [List.length_cons]; omega)
      have hex : ∀ a (ha : a ∈ G.avail (G.info y)), ∃ z, z ∈ G.terminals ∧ a :: y <:+ z ∧
          ∀ i, cont G (G.assemble F) (a :: y) i = G.payoff i z ∧
            cont G (G.assemble F') (a :: y) i = G.payoff i z := fun a ha => by
        obtain ⟨z, hz, h1, h2⟩ := (hchild a ha).1
        exact ⟨z, hz, h1, h2⟩
      choose zf hzf hyz hval using hex
      have hagree := fun a ha => (hchild a ha).2
      obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.1 (hN (G.info y))
      -- the mover's values at the successors are distinct
      have hdist : ∀ a (ha : a ∈ G.avail k) b (hb : b ∈ G.avail k), a ≠ b →
          G.payoff j (zf a ha) ≠ G.payoff j (zf b hb) := by
        intro a ha b hb hab he
        have := hinj j _ (hzf a ha) _ (hzf b hb) he
        have h1 := hyz a ha
        rw [this] at h1
        exact hab (by simpa using suffix_unique h1 (hyz b hb) (by simp))
      obtain ⟨a₀, ha₀, hmax⟩ := (G.avail k).exists_max_image
        (fun a => if h : a ∈ G.avail k then G.payoff j (zf a h) else 0) (G.avail_nonempty k)
      simp only [ha₀, ↓reduceDIte] at hmax
      -- any one-shot optimal behaviour puts all mass on `a₀`
      have hdirac : ∀ (P : I → H → A → ℝ), IsBehaviorProfile G P →
          OneShotOptimalAt G P y →
          (∀ a (ha : a ∈ G.avail k), cont G (G.assemble P) (a :: y) j = G.payoff j (zf a ha)) →
          G.assemble P k = dirac a₀ := by
        intro P hP hoP hPv
        have hsum := cont_decision G (G.assemble P) hdec j
        have hge := hoP j hj a₀ ha₀
        rw [hPv a₀ ha₀] at hge
        have hzero : ∀ a ∈ G.avail k, G.assemble P k a *
            (G.payoff j (zf a₀ ha₀) - cont G (G.assemble P) (a :: y) j) = 0 := by
          have hnn : ∀ a ∈ G.avail k, 0 ≤ G.assemble P k a *
              (G.payoff j (zf a₀ ha₀) - cont G (G.assemble P) (a :: y) j) := by
            intro a ha
            refine mul_nonneg (assemble_nonneg G hP _ _) ?_
            rw [hPv a ha]
            have := hmax a ha
            simp only [ha, ↓reduceDIte] at this
            linarith
          refine (Finset.sum_eq_zero_iff_of_nonneg hnn).1 ?_
          refine le_antisymm ?_ (Finset.sum_nonneg hnn)
          simp_rw [mul_sub]
          rw [Finset.sum_sub_distrib, ← Finset.sum_mul, assemble_sum G hP, one_mul, ← hsum]
          linarith
        have hoff : ∀ a ∈ G.avail k, a ≠ a₀ → G.assemble P k a = 0 := by
          intro a ha hne
          have := hzero a ha
          rw [hPv a ha] at this
          have hlt : G.payoff j (zf a ha) < G.payoff j (zf a₀ ha₀) := by
            have h1 := hmax a ha
            simp only [ha, ↓reduceDIte] at h1
            exact lt_of_le_of_ne h1 (hdist a ha a₀ ha₀ hne)
          rcases mul_eq_zero.1 this with h | h
          · exact h
          · linarith
        have hon : G.assemble P k a₀ = 1 := by
          have := assemble_sum G hP k
          rw [← Finset.add_sum_erase _ _ ha₀, Finset.sum_eq_zero fun a ha =>
            hoff a (Finset.mem_of_mem_erase ha) (Finset.ne_of_mem_erase ha), add_zero] at this
          exact this
        funext a
        simp only [dirac]
        split_ifs with h
        · subst h
          exact hon
        · by_cases ha : a ∈ G.avail k
          · exact hoff a ha h
          · rw [G.assemble_of_some _ hj]
            exact (hP j k hj).2.1 a ha
      have hFd := hdirac F hF (hopt y hdec) fun a ha => (hval a ha j).1
      have hF'd := hdirac F' hF' (hopt' y hdec) fun a ha => (hval a ha j).2
      refine ⟨⟨zf a₀ ha₀, hzf a₀ ha₀, (List.suffix_cons a₀ y).trans (hyz a₀ ha₀), fun i => ?_⟩,
        fun w hw hyw => ?_⟩
      · rw [cont_decision _ _ hdec, cont_decision _ (G.assemble F') hdec, hFd, hF'd]
        simp only [dirac, ite_mul, one_mul, zero_mul]
        rw [Finset.sum_ite_eq' (G.avail k), Finset.sum_ite_eq' (G.avail k)]
        simp only [ha₀, ↓reduceIte]
        exact hval a₀ ha₀ i
      · by_cases hwy : w = y
        · subst hwy
          rw [hFd, hF'd]
        · obtain ⟨b, hb⟩ := exists_cons_suffix hyw (Ne.symm hwy)
          have hbav : b ∈ G.avail k := G.mem_avail_of_cons_mem (G.mem_of_suffix hb hw.1)
          exact hagree b hbav w hw hb
    · refine ⟨⟨y, (mem_terminals G).2 hterm, List.suffix_refl _, fun i =>
        ⟨cont_terminal _ _ hterm i, cont_terminal _ _ hterm i⟩⟩, fun w hw hyw => ?_⟩
      have := G.eq_of_terminal_suffix hterm hw.1 hyw
      subst this
      exact absurd ⟨hw, hterm⟩ (G.isDecision_or_isTerminal hy).2

omit [Fintype A] [DecidableEq H] in
/-- Moves that agree at every information set give equal pure strategy profiles. -/
theorem pure_eq_of_assemble_eq {s s' : (i : I) → G.PureStrategy i}
    (h : ∀ k, G.assemble (pureB G s) k = G.assemble (pureB G s') k) : s = s' := by
  funext i
  funext k
  have := congrFun (h k.1) (s i k).1
  rw [assemble_pureB, assemble_pureB, G.pureProfile_apply _ k.2,
    G.pureProfile_apply _ k.2] at this
  simp only [ite_true] at this
  split_ifs at this with he
  · exact Subtype.ext he.symm
  · norm_num at this

omit [DecidableEq H] in
/-- **Proposition 9.B.1 (Zermelo's theorem)** (MWG, p. 272). Every finite game of perfect
information has a pure strategy profile derived through backward induction, and every such
profile is a Nash equilibrium of `Γ_E` (in behaviour strategies, hence also of its normal
form). Moreover, if there are no moves of nature and no player has the same payoffs at two
terminal nodes, there is a unique profile derived in this manner. -/
theorem proposition_9_B_1 (hPI : G.PerfectInformation) :
    (∃ s : (i : I) → G.PureStrategy i, IsBackwardInduction G s) ∧
    (∀ s, IsBackwardInduction G s → IsNashB G (pureB G s) ∧
      MWG.SimultaneousMoveGames.IsNashEquilibrium G.toNormalForm s) ∧
    ((∀ k, G.player k ≠ none) →
      (∀ i, ∀ z ∈ G.terminals, ∀ z' ∈ G.terminals, G.payoff i z = G.payoff i z' → z = z') →
      ∃! s : (i : I) → G.PureStrategy i, IsBackwardInduction G s) := by
  classical
  have hNA := G.noAbsentMindedness_of_perfectInformation hPI
  refine ⟨exists_backwardInduction G hPI, fun s hs => ?_, fun hN hinj => ?_⟩
  · have hN : IsNashB G (pureB G s) :=
      isNashB_of_isSPNE G hNA (isSPNE_of_oneShotOptimal G (isBehaviorProfile_pureB G s) hs)
    exact ⟨hN, hN.isNashEquilibrium_pure⟩
  · obtain ⟨s, hs⟩ := exists_backwardInduction G hPI
    refine ⟨s, hs, fun s' hs' => pure_eq_of_assemble_eq G fun k => ?_⟩
    obtain ⟨x, hx, hb, rfl⟩ := G.info_surj k
    exact ((oneShotOptimal_unique G hN hinj (isBehaviorProfile_pureB G s')
      (isBehaviorProfile_pureB G s) hs' hs G.nil_mem).2 x ⟨hx, hb⟩ List.nil_suffix)

omit [DecidableEq H] in
/-- **Section 9.B** (MWG, p. 273). Every finite game of perfect information has a pure strategy
Nash equilibrium. -/
theorem exists_pure_nash_of_perfectInformation
    (hPI : G.PerfectInformation) :
    ∃ s : (i : I) → G.PureStrategy i,
      MWG.SimultaneousMoveGames.IsNashEquilibrium G.toNormalForm s := by
  classical
  obtain ⟨s, hs⟩ := exists_backwardInduction G hPI
  exact ⟨s, ((proposition_9_B_1 G hPI).2.1 s hs).2⟩

omit [DecidableEq H] in
/-- **Proposition 9.B.2** (MWG, p. 276). Every finite game of perfect information has a pure
strategy subgame perfect Nash equilibrium. Moreover, if there are no moves of nature and no
player has the same payoffs at any two terminal nodes, the SPNE is unique: any two SPNE (in
behaviour strategies) prescribe the same moves at every information set. -/
theorem proposition_9_B_2 (hPI : G.PerfectInformation) :
    (∃ s : (i : I) → G.PureStrategy i, IsSPNE G (pureB G s)) ∧
    ((∀ k, G.player k ≠ none) →
      (∀ i, ∀ z ∈ G.terminals, ∀ z' ∈ G.terminals, G.payoff i z = G.payoff i z' → z = z') →
      ∀ F F', IsSPNE G F → IsSPNE G F' → ∀ k, G.assemble F k = G.assemble F' k) := by
  classical
  refine ⟨?_, fun hN hinj F F' hF hF' k => ?_⟩
  · obtain ⟨s, hs⟩ := exists_backwardInduction G hPI
    exact ⟨s, isSPNE_of_oneShotOptimal G (isBehaviorProfile_pureB G s) hs⟩
  · obtain ⟨x, hx, hb, rfl⟩ := G.info_surj k
    exact (oneShotOptimal_unique G hN hinj hF.1 hF'.1
      (fun y hy => oneShotOptimal_of_isSPNE G hPI hF hy)
      (fun y hy => oneShotOptimal_of_isSPNE G hPI hF' hy) G.nil_mem).2 x ⟨hx, hb⟩
      List.nil_suffix

omit [DecidableEq H] in
/-- In a two-player zero-sum game the second player's continuation payoff is the negative of
the first's. -/
theorem cont_zeroSum {G : ExtensiveForm (Fin 2) A H} (hzs : ∀ z, G.payoff 1 z = -G.payoff 0 z)
    (f : H → A → ℝ) (x : List A) : cont G f x 1 = -cont G f x 0 := by
  unfold cont
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [hzs]
  ring

omit [DecidableEq H] in
/-- **Exercise 9.B.4** (MWG, p. 302). In a finite two-player zero-sum game of perfect
information, all subgame perfect Nash equilibria give the same payoffs (from every node). -/
theorem exercise_9_B_4 {G : ExtensiveForm (Fin 2) A H} (hPI : G.PerfectInformation)
    (hzs : ∀ z, G.payoff 1 z = -G.payoff 0 z) {F F' : Fin 2 → H → A → ℝ}
    (hF : IsSPNE G F) (hF' : IsSPNE G F') {x : List A} (hx : x ∈ G.nodes) (i : Fin 2) :
    cont G (G.assemble F) x i = cont G (G.assemble F') x i := by
  classical
  have key : ∀ n, ∀ x ∈ G.nodes, G.nodes.sup List.length - x.length ≤ n →
      cont G (G.assemble F) x 0 = cont G (G.assemble F') x 0 := by
    intro n
    induction n with
    | zero =>
      intro y hy hn
      have hterm : G.IsTerminal y := by
        refine ⟨hy, fun b hb => ?_⟩
        have := G.length_le_sup hb
        simp only [List.length_cons] at this
        omega
      rw [cont_terminal _ _ hterm, cont_terminal _ _ hterm]
    | succ n ih =>
      intro y hy hn
      rcases (G.isDecision_or_isTerminal hy).1 with hdec | hterm
      · have hchild : ∀ a ∈ G.avail (G.info y),
            cont G (G.assemble F) (a :: y) 0 = cont G (G.assemble F') (a :: y) 0 := by
          intro a ha
          have hmem := G.cons_mem_of_mem_avail hdec ha
          have hl := G.length_le_sup hmem
          simp only [List.length_cons] at hl
          exact ih (a :: y) hmem (by simp only [List.length_cons]; omega)
        -- the mover's continuation payoff is the maximum over the successors
        have hmaxval : ∀ (P : Fin 2 → H → A → ℝ), IsSPNE G P → ∀ j,
            G.player (G.info y) = some j →
            (∀ a ∈ G.avail (G.info y), cont G (G.assemble P) (a :: y) j ≤
              cont G (G.assemble P) y j) ∧
            ∃ a ∈ G.avail (G.info y), cont G (G.assemble P) y j ≤
              cont G (G.assemble P) (a :: y) j := by
          intro P hP j hj
          refine ⟨oneShotOptimal_of_isSPNE G hPI hP hdec j hj, ?_⟩
          by_contra hno
          push Not at hno
          have := cont_decision G (G.assemble P) hdec j
          have hlt : ∑ a ∈ G.avail (G.info y), G.assemble P (G.info y) a *
              cont G (G.assemble P) (a :: y) j ≤
              ∑ a ∈ G.avail (G.info y), G.assemble P (G.info y) a *
                cont G (G.assemble P) y j :=
            Finset.sum_le_sum fun a ha =>
              mul_le_mul_of_nonneg_left (hno a ha).le (assemble_nonneg G hP.1 _ _)
          rw [← Finset.sum_mul, assemble_sum G hP.1, one_mul, ← this] at hlt
          obtain ⟨a, ha⟩ := G.avail_nonempty (G.info y)
          have h1 := hno a ha
          have hsum0 : ∑ a ∈ G.avail (G.info y), G.assemble P (G.info y) a *
              (cont G (G.assemble P) y j - cont G (G.assemble P) (a :: y) j) = 0 := by
            simp_rw [mul_sub]
            rw [Finset.sum_sub_distrib, ← Finset.sum_mul, assemble_sum G hP.1, one_mul, ← this,
              sub_self]
          have hnn : ∀ b ∈ G.avail (G.info y), 0 ≤ G.assemble P (G.info y) b *
              (cont G (G.assemble P) y j - cont G (G.assemble P) (b :: y) j) :=
            fun b hb => mul_nonneg (assemble_nonneg G hP.1 _ _) (by linarith [hno b hb])
          have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum0
          have hall : ∀ b ∈ G.avail (G.info y), G.assemble P (G.info y) b = 0 := by
            intro b hb
            rcases mul_eq_zero.1 (hz b hb) with h | h
            · exact h
            · linarith [hno b hb]
          have := assemble_sum G hP.1 (G.info y)
          rw [Finset.sum_eq_zero hall] at this
          norm_num at this
        cases hk : G.player (G.info y) with
        | none =>
          rw [cont_decision _ _ hdec, cont_decision _ (G.assemble F') hdec,
            G.assemble_of_none _ hk, G.assemble_of_none _ hk]
          exact Finset.sum_congr rfl fun a ha => by rw [hchild a ha]
        | some j =>
          obtain ⟨h1, a, ha, h2⟩ := hmaxval F hF j hk
          obtain ⟨h1', a', ha', h2'⟩ := hmaxval F' hF' j hk
          have hj' : ∀ P : Fin 2 → H → A → ℝ, ∀ y',
              cont G (G.assemble P) y' j = if j = 0 then cont G (G.assemble P) y' 0
                else -cont G (G.assemble P) y' 0 := by
            intro P y'
            fin_cases j
            · simp
            · simp [cont_zeroSum hzs]
          simp only [hj'] at h1 h2 h1' h2'
          split_ifs at h1 h2 h1' h2' with hj0
          · have e1 := h1 a' ha'
            have e2 := h1' a ha
            rw [hchild a' ha'] at e1
            rw [← hchild a ha] at e2
            linarith
          · have e1 := h1 a' ha'
            have e2 := h1' a ha
            rw [hchild a' ha'] at e1
            rw [← hchild a ha] at e2
            linarith
      · rw [cont_terminal _ _ hterm, cont_terminal _ _ hterm]
  have h0 := key _ x hx le_rfl
  fin_cases i
  · exact h0
  · simp only [Fin.mk_one, Fin.isValue]
    rw [cont_zeroSum hzs, cont_zeroSum hzs, h0]

end MWG.DynamicGames

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The generalized backward induction procedure

MWG, Section 9.B, pp. 277-278: Proposition 9.B.3.

Fix a subgame `S` of `Γ_E` with initial node `x₀` and a profile `σ^S` that is an SPNE in `S`
(`IsSPNEIn`). The reduced game `Γ̂_E` replaces `S` by a terminal node with the payoffs
`cont(σ^S, x₀)`. A profile `F` of `Γ̂_E` (its moves outside `S`) is evaluated through the
spliced profile `splice σ^S F` (moves of `σ^S` at the information sets of `S`, of `F`
elsewhere), whose continuation payoff at `x₀` is the reduced game's terminal payoff
(`cont_splice_root`). `IsSPNEReduced` is subgame perfection in `Γ̂_E`: no player gains by
changing her moves outside `S`, in any subgame of `Γ_E` not lying strictly inside `S` (these
are the subgames of `Γ̂_E`).

* `proposition_9_B_3_i`: in any SPNE `σ` of `Γ_E` whose play in `S` is `σ^S`, the moves outside
  `S` form an SPNE of `Γ̂_E`.
* `proposition_9_B_3_ii`: if `F` is an SPNE of `Γ̂_E`, the profile playing `σ^S` in `S` and `F`
  elsewhere is an SPNE of `Γ_E`.
-/

namespace MWG.DynamicGames

open MWG.NoncooperativeGames MWG.NoncooperativeGames.ExtensiveForm

variable {I A H : Type*} (G : ExtensiveForm I A H) [DecidableEq A] [Fintype A] [DecidableEq I]
  [DecidableEq H]

/-- The information set `k` belongs to the subgame starting at `x₀`. -/
def InSub (x₀ : List A) (k : H) : Prop := ∃ y, G.IsDecision y ∧ x₀ <:+ y ∧ G.info y = k

open Classical in
/-- The profile playing `σS` at the information sets of the subgame at `x₀` and `F`
elsewhere. -/
noncomputable def splice (x₀ : List A) (σS F : I → H → A → ℝ) : I → H → A → ℝ :=
  fun i k => if InSub G x₀ k then σS i k else F i k

/-- `σS` is a subgame perfect Nash equilibrium of the subgame starting at `x₀`. -/
def IsSPNEIn (x₀ : List A) (σS : I → H → A → ℝ) : Prop :=
  IsBehaviorProfile G σS ∧ ∀ y, IsSubgameRoot G y → x₀ <:+ y → InducesNashAt G σS y

omit [DecidableEq H] in
/-- An SPNE of `Γ_E` is an SPNE of every subgame. -/
theorem isSPNEIn_of_isSPNE {σ : I → H → A → ℝ} (h : IsSPNE G σ) (x₀ : List A) :
    IsSPNEIn G x₀ σ :=
  ⟨h.1, fun y hy _ => h.2 y hy⟩

/-- **Proposition 9.B.3, the reduced game** (MWG, p. 277). `F` is a subgame perfect Nash
equilibrium of the reduced game `Γ̂_E` in which the subgame at `x₀` is replaced by the payoffs
of `σS`: in every subgame not lying strictly inside the subgame at `x₀`, no player gains by
changing her moves outside it. -/
def IsSPNEReduced (x₀ : List A) (σS F : I → H → A → ℝ) : Prop :=
  IsBehaviorProfile G (splice G x₀ σS F) ∧ ∀ y, IsSubgameRoot G y → ¬ x₀ <:+ y →
    ∀ i g, G.IsBehaviorStrategy i g →
      cont G (G.assemble (splice G x₀ σS (Function.update F i g))) y i ≤
        cont G (G.assemble (splice G x₀ σS F)) y i

omit [Fintype A] [DecidableEq A] [DecidableEq I] [DecidableEq H] in
theorem inSub_of_suffix {x₀ y : List A} (hy : G.IsDecision y) (h : x₀ <:+ y) :
    InSub G x₀ (G.info y) := ⟨y, hy, h, rfl⟩

open Classical in
omit [DecidableEq A] [Fintype A] [DecidableEq I] [DecidableEq H] in
/-- The moves of a spliced profile. -/
theorem assemble_splice (x₀ : List A) (σS F : I → H → A → ℝ) (k : H) :
    G.assemble (splice G x₀ σS F) k =
      if InSub G x₀ k then G.assemble σS k else G.assemble F k := by
  classical
  cases hk : G.player k with
  | none => simp only [G.assemble_of_none _ hk, ite_self]
  | some j => simp only [G.assemble_of_some _ hk, splice]

omit [DecidableEq I] [DecidableEq H] in
/-- In the reduced game the subgame's root is a terminal node with the payoffs of `σS`. -/
theorem cont_splice_root (x₀ : List A) (σS F : I → H → A → ℝ) (i : I) :
    cont G (G.assemble (splice G x₀ σS F)) x₀ i = cont G (G.assemble σS) x₀ i :=
  cont_congr G (fun y hy hxy => by
    simp only [assemble_splice, inSub_of_suffix G hy hxy, ↓reduceIte]) i

open Classical in
omit [DecidableEq I] [DecidableEq H] in
/-- Below a subgame root, the information sets of nodes after an entry node of the subgame lie
in it; the entry nodes of the subgame from a node not inside it are at most its root. -/
theorem entryNodes_inSub {x₀ : List A} (hx₀ : IsSubgameRoot G x₀) {y : List A}
    (hy : ¬ x₀ <:+ y) {x : List A} (hx : x ∈ entryNodes G (InSub G x₀) y) : x = x₀ := by
  classical
  rw [mem_entryNodes] at hx
  obtain ⟨hxd, hyx, ⟨w, hw, hxw, hwk⟩, hmin⟩ := hx
  have hx₀x : x₀ <:+ x := hx₀.2.2 w hw hxw x hxd hwk.symm
  by_contra hne
  have hyx₀ : y <:+ x₀ := by
    rcases le_total y.length x₀.length with hl | hl
    · exact List.suffix_of_suffix_length_le hyx hx₀x hl
    · exact absurd (List.suffix_of_suffix_length_le hx₀x hyx hl) hy
  exact hmin x₀ hx₀.1 hyx₀ hx₀x (Ne.symm hne) ⟨x₀, hx₀.1, List.suffix_refl _, rfl⟩

omit [DecidableEq A] [Fintype A] [DecidableEq H] in
/-- The deviation of player `i` to `g` within the spliced profile. -/
theorem assemble_update_splice (x₀ : List A) (σS F : I → H → A → ℝ) (i : I)
    (g : H → A → ℝ) (k : H) (hk : ¬ InSub G x₀ k) :
    G.assemble (Function.update (splice G x₀ σS F) i g) k =
      G.assemble (splice G x₀ σS (Function.update F i g)) k := by
  classical
  rw [assemble_splice]
  simp only [hk, ↓reduceIte]
  cases hp : G.player k with
  | none => rw [G.assemble_of_none _ hp, G.assemble_of_none _ hp]
  | some j =>
    rw [G.assemble_of_some _ hp, G.assemble_of_some _ hp]
    by_cases hj : j = i
    · subst hj
      simp
    · simp [Function.update_of_ne hj, splice, hk]

omit [DecidableEq H] in
/-- **Proposition 9.B.3(ii)** (MWG, p. 277). If `σS` is an SPNE in the subgame `S` starting at
`x₀` and `F` is an SPNE of the reduced game, then the profile playing `σS` in `S` and `F`
elsewhere is an SPNE of `Γ_E`. -/
theorem proposition_9_B_3_ii {x₀ : List A} (hx₀ : IsSubgameRoot G x₀)
    {σS F : I → H → A → ℝ} (hS : IsSPNEIn G x₀ σS) (hF : IsSPNEReduced G x₀ σS F) :
    IsSPNE G (splice G x₀ σS F) := by
  classical
  refine ⟨hF.1, fun y hy i g hg => ?_⟩
  by_cases hxy : x₀ <:+ y
  · -- inside the subgame the spliced profile is `σS`
    have h1 : cont G (G.assemble (Function.update (splice G x₀ σS F) i g)) y i =
        cont G (G.assemble (Function.update σS i g)) y i := by
      refine cont_congr G (fun w hw hyw => ?_) i
      have hin := inSub_of_suffix G hw (hxy.trans hyw)
      cases hp : G.player (G.info w) with
      | none => simp only [G.assemble_of_none _ hp]
      | some j =>
        rw [G.assemble_of_some _ hp, G.assemble_of_some _ hp]
        by_cases hj : j = i
        · subst hj; simp
        · simp [Function.update_of_ne hj, splice, hin]
    have h2 : cont G (G.assemble (splice G x₀ σS F)) y i = cont G (G.assemble σS) y i :=
      cont_congr G (fun w hw hyw => by
        simp only [assemble_splice, inSub_of_suffix G hw (hxy.trans hyw), ↓reduceIte]) i
    rw [h1, h2]
    exact hS.2 y hy hxy i g hg
  · -- outside: first replace the deviation inside `S` by `σS`, then use the reduced game
    have hoff : ∀ k, ¬ InSub G x₀ k →
        G.assemble (Function.update (splice G x₀ σS F) i g) k =
          G.assemble (splice G x₀ σS (Function.update F i g)) k :=
      fun k hk => assemble_update_splice G x₀ σS F i g k hk
    have hdec := cont_sub_eq_sum_entry G (InSub G x₀) hoff hy.1.1 i
    have hroot : cont G (G.assemble (Function.update (splice G x₀ σS F) i g)) x₀ i ≤
        cont G (G.assemble (splice G x₀ σS (Function.update F i g))) x₀ i := by
      rw [cont_splice_root]
      have h1 : cont G (G.assemble (Function.update (splice G x₀ σS F) i g)) x₀ i =
          cont G (G.assemble (Function.update σS i g)) x₀ i := by
        refine cont_congr G (fun w hw hyw => ?_) i
        have hin := inSub_of_suffix G hw hyw
        cases hp : G.player (G.info w) with
        | none => simp only [G.assemble_of_none _ hp]
        | some j =>
          rw [G.assemble_of_some _ hp, G.assemble_of_some _ hp]
          by_cases hj : j = i
          · subst hj; simp
          · simp [Function.update_of_ne hj, splice, hin]
      rw [h1]
      exact hS.2 x₀ hx₀ (List.suffix_refl _) i g hg
    have hle : cont G (G.assemble (Function.update (splice G x₀ σS F) i g)) y i ≤
        cont G (G.assemble (splice G x₀ σS (Function.update F i g))) y i := by
      rw [← sub_nonpos, hdec]
      refine Finset.sum_nonpos fun x hx => ?_
      obtain rfl := entryNodes_inSub G hx₀ hxy hx
      exact mul_nonpos_of_nonneg_of_nonpos (reachFrom_nonneg G
        (assemble_nonneg G (isBehaviorProfile_update G hF.1 hg)) _ _) (sub_nonpos.2 hroot)
    exact hle.trans (hF.2 y hy hxy i g hg)

omit [DecidableEq H] in
/-- **Proposition 9.B.3(i)** (MWG, p. 277). In any SPNE `σ` of `Γ_E` whose play in the subgame
`S` at `x₀` is that of `σS`, the players' moves outside `S` form an SPNE of the reduced game. -/
theorem proposition_9_B_3_i {x₀ : List A} {σS σ : I → H → A → ℝ} (hσ : IsSPNE G σ)
    (hagree : ∀ k, InSub G x₀ k → G.assemble σ k = G.assemble σS k) :
    IsSPNEReduced G x₀ σS σ := by
  classical
  have hsp : G.assemble (splice G x₀ σS σ) = G.assemble σ := by
    funext k
    rw [assemble_splice]
    split_ifs with h
    · exact (hagree k h).symm
    · rfl
  refine ⟨?_, fun y hy _ i g hg => ?_⟩
  · intro j k hk
    have h := hσ.1 j k hk
    have e1 := congrFun hsp k
    rw [G.assemble_of_some _ hk, G.assemble_of_some _ hk] at e1
    rw [e1]
    exact h
  · -- the reduced-game deviation is a deviation of `Γ_E` keeping `σS`'s moves inside `S`
    set g' : H → A → ℝ := fun k => if InSub G x₀ k then σ i k else g k
    have hg' : G.IsBehaviorStrategy i g' := fun k hk => by
      simp only [g']
      split_ifs
      · exact hσ.1 i k hk
      · exact hg k hk
    have heq : G.assemble (splice G x₀ σS (Function.update σ i g)) =
        G.assemble (Function.update σ i g') := by
      funext k
      rw [assemble_splice]
      cases hp : G.player k with
      | none =>
        simp only [G.assemble_of_none _ hp]
        split_ifs <;> rfl
      | some j =>
        have e2 : G.assemble (Function.update σ i g') k = Function.update σ i g' j k :=
          G.assemble_of_some _ hp
        have e3 : G.assemble (Function.update σ i g) k = Function.update σ i g j k :=
          G.assemble_of_some _ hp
        rw [e2, e3]
        split_ifs with h
        · rw [← hagree k h, G.assemble_of_some _ hp]
          by_cases hj : j = i
          · subst hj; simp [g', h]
          · simp [Function.update_of_ne hj]
        · by_cases hj : j = i
          · subst hj; simp [g', h]
          · simp [Function.update_of_ne hj]
    rw [heq, hsp]
    exact hσ.2 y hy i g' hg'

end MWG.DynamicGames

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Beliefs, sequential rationality, weak perfect Bayesian and sequential equilibrium

MWG, Section 9.C, pp. 282-292.

* `IsBeliefSystem` is **Definition 9.C.1**; `condPayoff G f μ k i` is
  `E[u_i | H, μ, σ] = ∑_{x ∈ H} μ(x) cont(x)`; `SeqRationalAt` / `SeqRational` are
  **Definition 9.C.2**; `probInfo` is `Prob(H | σ)` and `BayesConsistent` is condition (ii)
  of **Definition 9.C.3** (`IsWeakPBE`).
* `proposition_9_C_1` (**Proposition 9.C.1**, Exercise 9.C.1): in a game with perfect recall, a
  profile is a Nash equilibrium iff there is a system of beliefs, derived from the profile by
  Bayes' rule whenever possible, for which it is sequentially rational at every information
  set reached with positive probability. Hence every weak PBE is a Nash equilibrium
  (`isNashB_of_isWeakPBE`).
* `IsConsistent` and `IsSequentialEq` are **Definition 9.C.4**: beliefs are limits of the
  Bayes beliefs of totally mixed profiles converging to the strategies.
  `isWeakPBE_of_isSequentialEq`: every sequential equilibrium is a weak PBE (p. 290).
* `proposition_9_C_2` (**Proposition 9.C.2**): with perfect recall, the strategies of a
  sequential equilibrium form a subgame perfect Nash equilibrium.

Departures. The propositions are proved for games with perfect recall (MWG does not state the
hypothesis; Chapter 9 works with behaviour strategies, which presupposes it). The assessment
in `IsSequentialEq` includes that `μ` is a system of beliefs (automatic when nature's moves
have full support).
-/

namespace MWG.DynamicGames

open MWG.NoncooperativeGames MWG.NoncooperativeGames.ExtensiveForm Filter Topology

variable {I A H : Type*} (G : ExtensiveForm I A H) [DecidableEq A] [Fintype A] [DecidableEq I]
  [DecidableEq H]

/-- **Definition 9.C.1** (MWG, p. 283). A system of beliefs: a probability `μ(x) ∈ [0, 1]` for
each decision node, summing to one over every information set. -/
def IsBeliefSystem (μ : List A → ℝ) : Prop :=
  (∀ x, G.IsDecision x → 0 ≤ μ x ∧ μ x ≤ 1) ∧ ∀ k, ∑ x ∈ G.infoSet k, μ x = 1

/-- **Section 9.C** (MWG, p. 284). `E[u_i | H, μ, σ]`: player `i`'s expected continuation
payoff at information set `k` when the nodes of `k` have probabilities `μ` and play
continues according to the moves `f`. -/
def condPayoff (f : H → A → ℝ) (μ : List A → ℝ) (k : H) (i : I) : ℝ :=
  ∑ x ∈ G.infoSet k, μ x * cont G f x i

/-- **Definition 9.C.2** (MWG, p. 284). The profile `F` is sequentially rational at
information set `k` given beliefs `μ`: the player moving at `k` cannot raise
`E[u_i | k, μ, ·]` by switching to any other (behaviour) strategy. -/
def SeqRationalAt (F : I → H → A → ℝ) (μ : List A → ℝ) (k : H) : Prop :=
  ∀ i, G.player k = some i → ∀ g, G.IsBehaviorStrategy i g →
    condPayoff G (G.assemble (Function.update F i g)) μ k i ≤ condPayoff G (G.assemble F) μ k i

/-- **Definition 9.C.2** (MWG, p. 284). Sequential rationality at every information set. -/
def SeqRational (F : I → H → A → ℝ) (μ : List A → ℝ) : Prop := ∀ k, SeqRationalAt G F μ k

/-- **Section 9.C** (MWG, p. 284). `Prob(H | σ) = ∑_{x ∈ H} Prob(x | σ)`. -/
def probInfo (f : H → A → ℝ) (k : H) : ℝ := ∑ x ∈ G.infoSet k, G.reach f x

/-- **Definition 9.C.3(ii)** (MWG, p. 285). Beliefs are derived from the profile through Bayes'
rule whenever possible: `μ(x) = Prob(x | σ) / Prob(H | σ)` when `Prob(H | σ) > 0`. -/
def BayesConsistent (F : I → H → A → ℝ) (μ : List A → ℝ) : Prop :=
  ∀ k, 0 < probInfo G (G.assemble F) k →
    ∀ x ∈ G.infoSet k, μ x = G.reach (G.assemble F) x / probInfo G (G.assemble F) k

/-- **Definition 9.C.3** (MWG, p. 285). A weak perfect Bayesian equilibrium `(σ, μ)`. -/
def IsWeakPBE (F : I → H → A → ℝ) (μ : List A → ℝ) : Prop :=
  IsBehaviorProfile G F ∧ IsBeliefSystem G μ ∧ SeqRational G F μ ∧ BayesConsistent G F μ

omit [DecidableEq I] in
/-- Membership in an information set. -/
theorem mem_infoSet {k : H} {x : List A} : x ∈ G.infoSet k ↔ G.IsDecision x ∧ G.info x = k := by
  simp [infoSet, decisionNodes, IsDecision, and_assoc]

omit [DecidableEq A] [Fintype A] [DecidableEq I] [DecidableEq H] in
/-- Perfect recall condition (ii) for decision nodes. -/
theorem recall_pred {i : I} (hR : G.RecallFor i) {x x' y : List A} (hx : G.IsDecision x)
    (hx' : G.IsDecision x') (hi : G.player (G.info x) = some i) (he : G.info x = G.info x')
    {a : A} (hy : a :: y <:+ x) (hyi : G.player (G.info y) = some i) :
    ∃ y', G.IsDecision y' ∧ a :: y' <:+ x' ∧ G.info y' = G.info y := by
  obtain ⟨y', -, hy', hinfo⟩ := hR x hx.1 x' hx'.1 hx.2 hx'.2 hi he y
    (G.mem_of_suffix ((List.suffix_cons a y).trans hy) hx.1) a hy hyi
  exact ⟨y', G.isDecision_of_cons_mem (G.mem_of_suffix hy' hx'.1), hy', hinfo⟩

omit [Fintype A] [DecidableEq I] [DecidableEq H] [DecidableEq A] in
/-- No absent-mindedness: two comparable nodes of one information set coincide. -/
theorem eq_of_absentMinded (hNA : G.NoAbsentMindedness) {w x : List A} (hw : G.IsDecision w)
    (hx : G.IsDecision x) (he : G.info w = G.info x) (hwx : w <:+ x) : w = x := by
  classical
  by_contra hne
  exact hNA w hw.1 x hx.1 hw.2 hx.2 he ⟨hwx, hne⟩

omit [DecidableEq H] in
/-- With perfect recall, the first nodes of player `i` after `y` form a union of information
sets, provided no information set is broken at `y`. -/
theorem entry_closed {i : I} (hR : G.RecallFor i) {y : List A}
    (hbr : ∀ w, G.IsDecision w → y <:+ w → ∀ w', G.IsDecision w' → G.info w' = G.info w →
      y <:+ w')
    {x x' : List A} (hx : x ∈ entryNodes G (fun k => G.player k = some i) y)
    (hx' : G.IsDecision x') (he : G.info x' = G.info x) :
    x' ∈ entryNodes G (fun k => G.player k = some i) y := by
  rw [mem_entryNodes] at hx ⊢
  obtain ⟨hdx, hyx, hDx, hmin⟩ := hx
  refine ⟨hx', hbr x hdx hyx x' hx' he, by rw [he]; exact hDx, fun w hw hyw hwx' hne hDw => ?_⟩
  obtain ⟨b, hb⟩ := exists_cons_suffix hwx' hne
  obtain ⟨y'', hy'', hby'', hinfo⟩ := recall_pred G hR hx' hdx (by rw [he]; exact hDx) he hb hDw
  have hy''x : y'' <:+ x := (List.suffix_cons b y'').trans hby''
  have hne'' : y'' ≠ x := by
    rintro rfl
    have := hby''.length_le
    simp at this
  exact hmin y'' hy'' (hbr w hw hyw y'' hy'' hinfo) hy''x hne'' (by rw [hinfo]; exact hDw)

omit [DecidableEq I] in
/-- Grouping a sum over a union of information sets by information set. -/
theorem sum_eq_sum_infoSet {E : Finset (List A)} (hE : ∀ x ∈ E, G.IsDecision x)
    (hcl : ∀ x ∈ E, ∀ x', G.IsDecision x' → G.info x' = G.info x → x' ∈ E) (φ : List A → ℝ) :
    ∑ x ∈ E, φ x = ∑ k ∈ E.image G.info, ∑ x ∈ G.infoSet k, φ x := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := G.info) (t := E.image G.info)
    (fun x hx => Finset.mem_image_of_mem _ hx)]
  refine Finset.sum_congr rfl fun k hk => ?_
  obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.1 hk
  congr 1
  ext x
  simp only [Finset.mem_filter, mem_infoSet]
  exact ⟨fun ⟨hx, he⟩ => ⟨hE x hx, he⟩, fun ⟨hx, he⟩ => ⟨hcl x₀ hx₀ x hx he, he⟩⟩

omit [DecidableEq A] [Fintype A] [DecidableEq H] in
/-- The moves of `update F i g` agree with those of `F` off player `i`'s information sets. -/
theorem assemble_update_eq_off (F : I → H → A → ℝ) (i : I) (g : H → A → ℝ) (k : H)
    (hk : ¬ G.player k = some i) : G.assemble F k = G.assemble (Function.update F i g) k := by
  cases hk' : G.player k with
  | none => rw [assemble_update_of_none G F i g hk']
  | some j =>
    have hji : j ≠ i := fun h => hk (h ▸ hk')
    rw [assemble_update_of_ne G F g hk' hji]

omit [DecidableEq I] in
/-- Reach probabilities of decision nodes in an information set are at most `Prob(H)`. -/
theorem reach_le_probInfo {f : H → A → ℝ} (hf : ∀ k a, 0 ≤ f k a) {k : H} {x : List A}
    (hx : x ∈ G.infoSet k) : G.reach f x ≤ probInfo G f k :=
  Finset.single_le_sum (fun y _ => G.reach_nonneg hf y) hx

/-- The sum of the player's deviation gains over her first information sets (perfect recall):
`U_i(σ) − U_i(σ̃_i, σ_{-i}) = ∑_{H first} ∑_{x ∈ H} P(x) (cont(x) − cont~(x))`. -/
theorem nash_gap_eq {i : I} (hR : G.RecallFor i) (F : I → H → A → ℝ) (g : H → A → ℝ) :
    cont G (G.assemble F) [] i - cont G (G.assemble (Function.update F i g)) [] i =
      ∑ k ∈ (entryNodes G (fun k => G.player k = some i) []).image G.info,
        ∑ x ∈ G.infoSet k, G.reach (G.assemble F) x *
          (cont G (G.assemble F) x i - cont G (G.assemble (Function.update F i g)) x i) := by
  rw [cont_sub_eq_sum_entry G (fun k => G.player k = some i)
    (fun k hk => assemble_update_eq_off G F i g k hk) G.nil_mem]
  simp_rw [reachFrom_nil]
  exact sum_eq_sum_infoSet G (fun x hx => ((mem_entryNodes G).1 hx).1)
    (fun x hx x' hx' he => entry_closed G hR (fun _ _ _ _ _ _ => List.nil_suffix) hx hx' he) _

/-- The belief system derived from `F` by Bayes' rule where possible and uniform elsewhere. -/
noncomputable def bayesOrUniform (f : H → A → ℝ) (x : List A) : ℝ :=
  if 0 < probInfo G f (G.info x) then G.reach f x / probInfo G f (G.info x)
  else 1 / ((G.infoSet (G.info x)).card : ℝ)

omit [DecidableEq I] in
/-- `bayesOrUniform` is a system of beliefs derived by Bayes' rule whenever possible. -/
theorem bayesOrUniform_spec {F : I → H → A → ℝ} (hF : IsBehaviorProfile G F) :
    IsBeliefSystem G (bayesOrUniform G (G.assemble F)) ∧
      BayesConsistent G F (bayesOrUniform G (G.assemble F)) := by
  have hf := assemble_nonneg G hF
  refine ⟨⟨fun x hx => ?_, fun k => ?_⟩, fun k hk x hx => ?_⟩
  · have hxk : x ∈ G.infoSet (G.info x) := (mem_infoSet G).2 ⟨hx, rfl⟩
    have hcard : (1 : ℝ) ≤ ((G.infoSet (G.info x)).card : ℝ) := by
      exact_mod_cast Finset.card_pos.2 ⟨x, hxk⟩
    unfold bayesOrUniform
    split_ifs with hp
    · exact ⟨div_nonneg (G.reach_nonneg hf x) hp.le,
        (div_le_one hp).2 (reach_le_probInfo G hf hxk)⟩
    · exact ⟨by positivity, (div_le_one (by linarith)).2 hcard⟩
  · have hinfo : ∀ x ∈ G.infoSet k, G.info x = k := fun x hx => ((mem_infoSet G).1 hx).2
    rw [Finset.sum_congr rfl fun x hx => by rw [bayesOrUniform, hinfo x hx]]
    by_cases hp : 0 < probInfo G (G.assemble F) k
    · simp only [hp, ite_true]
      rw [← Finset.sum_div]
      exact div_self hp.ne'
    · simp only [hp, ite_false, Finset.sum_const, nsmul_eq_mul]
      have hne : (G.infoSet k).Nonempty := (G.infoSet_partition).1 k
      have : ((G.infoSet k).card : ℝ) ≠ 0 := by exact_mod_cast hne.card_pos.ne'
      field_simp
  · have hxk : G.info x = k := ((mem_infoSet G).1 hx).2
    simp only [bayesOrUniform, hxk, hk, ite_true]

/-- **Proposition 9.C.1** (MWG, p. 285; Exercise 9.C.1). In a game with perfect recall, a
behaviour profile `σ` is a Nash equilibrium iff there is a system of beliefs `μ` such that
(i) `σ` is sequentially rational given `μ` at every information set `H` with
`Prob(H | σ) > 0`, and (ii) `μ` is derived from `σ` through Bayes' rule whenever possible. -/
theorem proposition_9_C_1 (hPR : G.PerfectRecall) (F : I → H → A → ℝ) :
    IsNashB G F ↔ IsBehaviorProfile G F ∧ ∃ μ, IsBeliefSystem G μ ∧
      (∀ k, 0 < probInfo G (G.assemble F) k → SeqRationalAt G F μ k) ∧ BayesConsistent G F μ := by
  constructor
  · intro hN
    have hF := hN.1
    have hf := assemble_nonneg G hF
    obtain ⟨hμ, hB⟩ := bayesOrUniform_spec G hF
    refine ⟨hF, bayesOrUniform G (G.assemble F), hμ, fun k hk i hi g hg => ?_, hB⟩
    classical
    -- the deviation `g` at and after `k`, `F i` elsewhere
    let Aft : H → Prop := fun k' => ∃ x ∈ G.infoSet k, ∃ w ∈ G.decisionNodes, x <:+ w ∧
      G.info w = k'
    let g' : H → A → ℝ := fun k' => if Aft k' then g k' else F i k'
    have hg' : G.IsBehaviorStrategy i g' := fun k' hk' => by
      simp only [g']
      split_ifs
      · exact hg k' hk'
      · exact hF i k' hk'
    have hdev := hN.2 i g' hg'
    let D : H → Prop := fun k' => G.player k' = some i ∧ Aft k'
    have hoff : ∀ k', ¬ D k' → G.assemble F k' = G.assemble (Function.update F i g') k' := by
      intro k' hk'
      by_cases hpi : G.player k' = some i
      · have hA : ¬ Aft k' := fun h => hk' ⟨hpi, h⟩
        rw [assemble_update_self G F g' hpi, G.assemble_of_some _ hpi]
        simp only [g', hA, ite_false]
      · exact assemble_update_eq_off G F i g' k' hpi
    have hdec := cont_sub_eq_sum_entry G D hoff G.nil_mem i
    -- the entry nodes of `D` are exactly the nodes of `k`
    have hE : entryNodes G D [] = G.infoSet k := by
      ext x
      rw [mem_entryNodes, mem_infoSet]
      constructor
      · rintro ⟨hx, -, ⟨hpx, x₀, hx₀, w₁, hw₁, hx₀w, hwinfo⟩, hmin⟩
        rw [mem_infoSet] at hx₀
        rw [mem_decisionNodes] at hw₁
        refine ⟨hx, ?_⟩
        by_cases h01 : x₀ = w₁
        · subst h01
          rw [← hwinfo, hx₀.2]
        · exfalso
          obtain ⟨b, hb⟩ := exists_cons_suffix hx₀w h01
          obtain ⟨y', hy', hby', hinfo⟩ := recall_pred G (hPR.2 i) hw₁ hx
            (by rw [hwinfo]; exact hpx) hwinfo hb (by rw [hx₀.2]; exact hi)
          have hy'x : y' <:+ x := (List.suffix_cons b y').trans hby'
          have hne : y' ≠ x := by
            rintro rfl
            have := hby'.length_le
            simp at this
          refine hmin y' hy' List.nil_suffix hy'x hne ⟨by rw [hinfo, hx₀.2]; exact hi, ?_⟩
          exact ⟨y', (mem_infoSet G).2 ⟨hy', by rw [hinfo, hx₀.2]⟩, y',
            (mem_decisionNodes G).2 hy', List.suffix_refl _, rfl⟩
      · rintro ⟨hx, hxk⟩
        refine ⟨hx, List.nil_suffix, ⟨by rw [hxk]; exact hi, x, (mem_infoSet G).2 ⟨hx, hxk⟩, x,
          (mem_decisionNodes G).2 hx, List.suffix_refl _, rfl⟩, ?_⟩
        rintro w hw - hwx hne ⟨hpw, x₀, hx₀, w₁, hw₁, hx₀w, hwinfo⟩
        rw [mem_infoSet] at hx₀
        rw [mem_decisionNodes] at hw₁
        by_cases h01 : x₀ = w₁
        · subst h01
          exact hne (eq_of_absentMinded G hPR.1 hw hx (by rw [← hwinfo, hx₀.2, hxk]) hwx)
        · obtain ⟨b, hb⟩ := exists_cons_suffix hx₀w h01
          obtain ⟨y', hy', hby', hinfo⟩ := recall_pred G (hPR.2 i) hw₁ hw
            (by rw [hwinfo]; exact hpw) hwinfo hb (by rw [hx₀.2]; exact hi)
          have hy'x : y' <:+ x := ((List.suffix_cons b y').trans hby').trans hwx
          have := eq_of_absentMinded G hPR.1 hy' hx (by rw [hinfo, hx₀.2, hxk]) hy'x
          subst this
          have := hby'.length_le
          have := hwx.length_le
          simp at *
          omega
    -- after `k`, `g'` coincides with `g`
    have hafter : ∀ x ∈ G.infoSet k, cont G (G.assemble (Function.update F i g')) x i =
        cont G (G.assemble (Function.update F i g)) x i := by
      intro x hx
      refine cont_congr G (fun w hw hxw => ?_) i
      have hA : Aft (G.info w) := ⟨x, hx, w, (mem_decisionNodes G).2 hw, hxw, rfl⟩
      by_cases hpi : G.player (G.info w) = some i
      · rw [assemble_update_self G F g' hpi, assemble_update_self G F g hpi]
        simp only [g', hA, ite_true]
      · rw [← assemble_update_eq_off G F i g' _ hpi, ← assemble_update_eq_off G F i g _ hpi]
    rw [hE] at hdec
    have hsum : 0 ≤ ∑ x ∈ G.infoSet k, G.reach (G.assemble F) x *
        (cont G (G.assemble F) x i - cont G (G.assemble (Function.update F i g)) x i) := by
      have := sub_nonneg.2 hdev
      rw [hdec] at this
      simp_rw [reachFrom_nil] at this
      rwa [Finset.sum_congr rfl fun x hx => by rw [← hafter x hx]]
    have hreach : ∀ x ∈ G.infoSet k, G.reach (G.assemble F) x =
        probInfo G (G.assemble F) k * bayesOrUniform G (G.assemble F) x := by
      intro x hx
      rw [hB k hk x hx]
      field_simp
    rw [Finset.sum_congr rfl fun x hx => by rw [hreach x hx]] at hsum
    simp_rw [mul_assoc] at hsum
    rw [← Finset.mul_sum] at hsum
    have h2 := nonneg_of_mul_nonneg_right hsum hk
    simp_rw [mul_sub] at h2
    rw [Finset.sum_sub_distrib] at h2
    unfold condPayoff
    linarith
  · rintro ⟨hF, μ, hμ, hSR, hB⟩
    refine ⟨hF, fun i g hg => ?_⟩
    have hf := assemble_nonneg G hF
    rw [← sub_nonneg, nash_gap_eq G (hPR.2 i)]
    refine Finset.sum_nonneg fun k hk => ?_
    obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.1 hk
    have hpi : G.player (G.info x₀) = some i := ((mem_entryNodes G).1 hx₀).2.2.1
    by_cases hp : 0 < probInfo G (G.assemble F) (G.info x₀)
    · have hreach : ∀ x ∈ G.infoSet (G.info x₀), G.reach (G.assemble F) x =
          probInfo G (G.assemble F) (G.info x₀) * μ x := by
        intro x hx
        rw [hB _ hp x hx]
        field_simp
      rw [Finset.sum_congr rfl fun x hx => by rw [hreach x hx]]
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum]
      refine mul_nonneg hp.le ?_
      have := hSR _ hp i hpi g hg
      unfold condPayoff at this
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib]
      linarith
    · have hzero : ∀ x ∈ G.infoSet (G.info x₀), G.reach (G.assemble F) x = 0 := by
        intro x hx
        have h0 : probInfo G (G.assemble F) (G.info x₀) = 0 :=
          le_antisymm (not_lt.1 hp) (Finset.sum_nonneg fun y _ => G.reach_nonneg hf y)
        exact le_antisymm (h0 ▸ reach_le_probInfo G hf hx) (G.reach_nonneg hf x)
      rw [Finset.sum_eq_zero fun x hx => by rw [hzero x hx, zero_mul]]

/-- **Section 9.C** (MWG, p. 286). With perfect recall, a weak perfect Bayesian equilibrium is a
Nash equilibrium. -/
theorem isNashB_of_isWeakPBE (hPR : G.PerfectRecall) {F : I → H → A → ℝ} {μ : List A → ℝ}
    (h : IsWeakPBE G F μ) : IsNashB G F :=
  (proposition_9_C_1 G hPR F).2 ⟨h.1, μ, h.2.1, fun k _ => h.2.2.1 k, h.2.2.2⟩

/-- A totally mixed behaviour profile: every player puts positive probability on every
available action at each of her information sets (MWG, p. 284). -/
def IsTotallyMixedB (F : I → H → A → ℝ) : Prop :=
  IsBehaviorProfile G F ∧ ∀ i k, G.player k = some i → ∀ a ∈ G.avail k, 0 < F i k a

/-- The beliefs derived from the moves `f` by Bayes' rule: `Prob(x | σ) / Prob(H(x) | σ)`. -/
noncomputable def bayesBelief (f : H → A → ℝ) (x : List A) : ℝ :=
  G.reach f x / probInfo G f (G.info x)

/-- **Definition 9.C.4(ii)** (MWG, p. 290). The assessment `(σ, μ)` is consistent: there are
totally mixed profiles `σᵏ → σ` whose Bayes beliefs converge to `μ`. -/
def IsConsistent (F : I → H → A → ℝ) (μ : List A → ℝ) : Prop :=
  ∃ Fs : ℕ → I → H → A → ℝ, (∀ n, IsTotallyMixedB G (Fs n)) ∧ Tendsto Fs atTop (𝓝 F) ∧
    ∀ x, G.IsDecision x → Tendsto (fun n => bayesBelief G (G.assemble (Fs n)) x) atTop (𝓝 (μ x))

/-- **Definition 9.C.4** (MWG, p. 290). A sequential equilibrium: a behaviour profile and a
system of beliefs such that (i) the profile is sequentially rational given the beliefs and
(ii) the assessment is consistent. -/
def IsSequentialEq (F : I → H → A → ℝ) (μ : List A → ℝ) : Prop :=
  IsBehaviorProfile G F ∧ IsBeliefSystem G μ ∧ SeqRational G F μ ∧ IsConsistent G F μ

omit [DecidableEq A] [Fintype A] [DecidableEq I] [DecidableEq H] in
/-- The moves of a profile depend continuously on the profile. -/
theorem tendsto_assemble {Fs : ℕ → I → H → A → ℝ} {F : I → H → A → ℝ}
    (h : Tendsto Fs atTop (𝓝 F)) (k : H) (a : A) :
    Tendsto (fun n => G.assemble (Fs n) k a) atTop (𝓝 (G.assemble F k a)) := by
  cases hk : G.player k with
  | none =>
    simp only [G.assemble_of_none _ hk]
    exact tendsto_const_nhds
  | some j =>
    simp only [G.assemble_of_some _ hk]
    exact tendsto_pi_nhds.1 (tendsto_pi_nhds.1 (tendsto_pi_nhds.1 h j) k) a

omit [Fintype A] [DecidableEq I] [DecidableEq H] in
/-- Reach probabilities depend continuously on the profile. -/
theorem tendsto_reachFrom {Fs : ℕ → I → H → A → ℝ} {F : I → H → A → ℝ}
    (h : Tendsto Fs atTop (𝓝 F)) (x z : List A) :
    Tendsto (fun n => reachFrom G (G.assemble (Fs n)) x z) atTop
      (𝓝 (reachFrom G (G.assemble F) x z)) := by
  induction z with
  | nil =>
    simp only [reachFrom]
    exact tendsto_const_nhds
  | cons a z ih =>
    simp only [reachFrom]
    split_ifs
    · exact tendsto_const_nhds
    · exact ih.mul (tendsto_assemble G h _ _)

omit [Fintype A] [DecidableEq I] [DecidableEq H] [DecidableEq A] in
/-- Reach probabilities depend continuously on the profile. -/
theorem tendsto_reach {Fs : ℕ → I → H → A → ℝ} {F : I → H → A → ℝ}
    (h : Tendsto Fs atTop (𝓝 F)) (z : List A) :
    Tendsto (fun n => G.reach (G.assemble (Fs n)) z) atTop (𝓝 (G.reach (G.assemble F) z)) := by
  classical
  simp_rw [← reachFrom_nil]
  exact tendsto_reachFrom G h [] z

/-- **Section 9.C** (MWG, p. 290). Every sequential equilibrium is a weak perfect Bayesian
equilibrium: the limiting beliefs coincide with the Bayes beliefs on the equilibrium path. -/
theorem isWeakPBE_of_isSequentialEq {F : I → H → A → ℝ} {μ : List A → ℝ}
    (h : IsSequentialEq G F μ) : IsWeakPBE G F μ := by
  obtain ⟨hF, hμ, hSR, Fs, -, hlim, hbel⟩ := h
  refine ⟨hF, hμ, hSR, fun k hk x hx => ?_⟩
  obtain ⟨hxd, hxk⟩ := (mem_infoSet G).1 hx
  have h1 := hbel x hxd
  have h2 : Tendsto (fun n => bayesBelief G (G.assemble (Fs n)) x) atTop
      (𝓝 (G.reach (G.assemble F) x / probInfo G (G.assemble F) k)) := by
    unfold bayesBelief
    rw [hxk]
    exact (tendsto_reach G hlim x).div
      (tendsto_finsetSum _ fun y _ => tendsto_reach G hlim y) hk.ne'
  exact tendsto_nhds_unique h1 h2

omit [DecidableEq I] in
/-- Consistent beliefs inside a subgame: on an information set `k` lying after the subgame
root `x₀`, the probabilities `P(x | x₀)` are proportional to the beliefs. -/
theorem reachFrom_prop_of_consistent {F : I → H → A → ℝ} {μ : List A → ℝ}
    (hμ : IsBeliefSystem G μ) (hc : IsConsistent G F μ) {x₀ : List A} {k : H}
    (hk : ∀ x ∈ G.infoSet k, x₀ <:+ x) :
    ∃ c, 0 ≤ c ∧ ∀ x ∈ G.infoSet k, reachFrom G (G.assemble F) x₀ x = c * μ x := by
  obtain ⟨Fs, hFs, hlim, hbel⟩ := hc
  set R : ℕ → ℝ := fun n => ∑ x ∈ G.infoSet k, reachFrom G (G.assemble (Fs n)) x₀ x
  have hR : Tendsto R atTop (𝓝 (∑ x ∈ G.infoSet k, reachFrom G (G.assemble F) x₀ x)) :=
    tendsto_finsetSum _ fun x _ => tendsto_reachFrom G hlim x₀ x
  have hprob : ∀ n, probInfo G (G.assemble (Fs n)) k =
      G.reach (G.assemble (Fs n)) x₀ * R n := by
    intro n
    simp only [probInfo, R, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x hx => reach_eq_mul_reachFrom G _ (hk x hx)
  have hf : ∀ n, ∀ x ∈ G.infoSet k, bayesBelief G (G.assemble (Fs n)) x =
      G.reach (G.assemble (Fs n)) x / probInfo G (G.assemble (Fs n)) k := fun n x hx => by
    rw [bayesBelief, ((mem_infoSet G).1 hx).2]
  have hfB := fun n => assemble_nonneg G (hFs n).1
  have hfF : ∀ k a, 0 ≤ G.assemble F k a := fun k a =>
    ge_of_tendsto' (tendsto_assemble G hlim k a) fun n => hfB n k a
  refine ⟨∑ x ∈ G.infoSet k, reachFrom G (G.assemble F) x₀ x,
    Finset.sum_nonneg fun x _ => reachFrom_nonneg G hfF _ _, fun x hx => ?_⟩
  by_cases hfreq : ∃ᶠ n in atTop, probInfo G (G.assemble (Fs n)) k = 0
  · exfalso
    have hz : ∀ y ∈ G.infoSet k, μ y = 0 := by
      intro y hy
      refine tendsto_nhds_unique_of_frequently_eq (hbel y ((mem_infoSet G).1 hy).1)
        tendsto_const_nhds (hfreq.mono fun n hn => ?_)
      rw [hf n y hy, hn, div_zero]
    have := hμ.2 k
    rw [Finset.sum_eq_zero hz] at this
    norm_num at this
  · rw [not_frequently] at hfreq
    have hev : ∀ᶠ n in atTop, reachFrom G (G.assemble (Fs n)) x₀ x =
        R n * bayesBelief G (G.assemble (Fs n)) x := by
      filter_upwards [hfreq] with n hn
      rw [hf n x hx, hprob n, reach_eq_mul_reachFrom G _ (hk x hx)]
      have h0 : G.reach (G.assemble (Fs n)) x₀ ≠ 0 := fun h0 => hn (by rw [hprob n, h0, zero_mul])
      have h1 : R n ≠ 0 := fun h1 => hn (by rw [hprob n, h1, mul_zero])
      field_simp
    exact tendsto_nhds_unique (tendsto_reachFrom G hlim x₀ x)
      ((hR.mul (hbel x ((mem_infoSet G).1 hx).1)).congr' (hev.mono fun n hn => hn.symm))

/-- **Proposition 9.C.2** (MWG, p. 291). In a game with perfect recall, in every sequential
equilibrium `(σ, μ)` the strategy profile `σ` is a subgame perfect Nash equilibrium. -/
theorem proposition_9_C_2 (hPR : G.PerfectRecall) {F : I → H → A → ℝ} {μ : List A → ℝ}
    (h : IsSequentialEq G F μ) : IsSPNE G F := by
  obtain ⟨hF, hμ, hSR, hc⟩ := h
  refine ⟨hF, fun x₀ hx₀ i g hg => ?_⟩
  rw [← sub_nonneg, cont_sub_eq_sum_entry G (fun k => G.player k = some i)
    (fun k hk => assemble_update_eq_off G F i g k hk) hx₀.1.1 i]
  have hbr := hx₀.2.2
  rw [sum_eq_sum_infoSet G (fun x hx => ((mem_entryNodes G).1 hx).1)
    (fun x hx x' hx' he => entry_closed G (hPR.2 i) hbr hx hx' he)]
  refine Finset.sum_nonneg fun k hk => ?_
  obtain ⟨x₁, hx₁, rfl⟩ := Finset.mem_image.1 hk
  have hpi : G.player (G.info x₁) = some i := ((mem_entryNodes G).1 hx₁).2.2.1
  have hin : ∀ x ∈ G.infoSet (G.info x₁), x₀ <:+ x := fun x hx =>
    hbr x₁ ((mem_entryNodes G).1 hx₁).1 ((mem_entryNodes G).1 hx₁).2.1 x
      ((mem_infoSet G).1 hx).1 ((mem_infoSet G).1 hx).2
  obtain ⟨c, hc0, hcμ⟩ := reachFrom_prop_of_consistent G hμ hc hin
  rw [Finset.sum_congr rfl fun x hx => by rw [hcμ x hx]]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  refine mul_nonneg hc0 ?_
  have := hSR _ i hpi g hg
  unfold condPayoff at this
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  linarith

/-- **Section 9.C** (MWG, p. 291). With perfect recall, every sequential equilibrium is both a
weak perfect Bayesian equilibrium and a subgame perfect Nash equilibrium. -/
theorem isSequentialEq_strengthens (hPR : G.PerfectRecall) {F : I → H → A → ℝ}
    {μ : List A → ℝ} (h : IsSequentialEq G F μ) : IsWeakPBE G F μ ∧ IsSPNE G F :=
  ⟨isWeakPBE_of_isSequentialEq G h, proposition_9_C_2 G hPR h⟩

end MWG.DynamicGames

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Finite and infinite horizon bilateral bargaining

MWG, Appendix A of Chapter 9, pp. 296-299 (Examples 9.AA.1 and 9.AA.2), and Exercise 9.B.12.

Two players (`0` is MWG's player 1) divide `v` dollars. In period `t = 0, 1, 2, …` (MWG's period
`t + 1`) the proposer, player `0` in even and player `1` in odd periods, offers the responder
an amount `y ∈ [0, v]`; the responder accepts or rejects. Agreement in period `t` on offer `y`
gives the proposer `δ_i^t (v − y)` and the responder `δ_j^t y`. The horizon `T : ℕ∞` is the
number of periods (`⊤`: Rubinstein's infinite horizon); without agreement both get `0`.

Histories at a proposal node are the lists of rejected offers (most recent first). A
`Profile` gives the offer `prop h` at every history and the response `resp h y` to every offer
at every history; player `i`'s strategy is its part at the nodes where `i` moves. Every
proposal node `h` and every response node `(h, y)` begins a subgame. `IsSPNE` is subgame
perfection: at every (feasible, live) node no player gains by any change of her strategy.
Values are measured in dollars of the period of the node.

* `value_le_of_bound`: a discounted one-shot bound (the infinite-horizon one-stage deviation
  argument used to verify that a profile is subgame perfect).
* `value_ge_of_isSPNE`, `value_le_of_isSPNE`: the Shaked-Sutton bounds `v − δ_j M_j` and
  `v − δ_j m_j` on the proposer's SPNE payoff.
* `example_9_AA_2` (Rubinstein, with `δ₁ = δ₂`) and `exercise_9_B_12` (different discount
  factors): the SPNE exists and is unique; player `i` proposing earns
  `v (1 − δ_j) / (1 − δ_i δ_j)`; agreement is immediate.
* `example_9_AA_1`: the finite horizon game has a unique SPNE; the first proposer earns
  `v (1 − (−δ)^T) / (1 + δ)`, which for odd `T` is `v [1 − δ + δ² − ⋯ + δ^{T−1}]` and for even
  `T` is `v − δ v₁*(T − 1)`, and tends to `v / (1 + δ)` (`example_9_AA_1_limit`).
-/

namespace MWG.DynamicGames

/-- The data of an alternating-offer bargaining game: the surplus `v > 0`, discount factors
`δ_i ∈ (0, 1)` and the horizon `T` (number of periods; `⊤` for the infinite horizon). -/
structure BargainingGame where
  /-- The amount to be divided. -/
  v : ℝ
  /-- The players' discount factors. -/
  δ : Fin 2 → ℝ
  /-- The horizon: the number of periods. -/
  T : ℕ∞
  v_pos : 0 < v
  δ_pos : ∀ i, 0 < δ i
  δ_lt_one : ∀ i, δ i < 1

/-- A strategy profile of the bargaining game: the offer at every history and the response to
every offer at every history (`true` = accept). -/
structure BargainingProfile where
  /-- The offer made to the responder at history `h`. -/
  prop : List ℝ → ℝ
  /-- The response at history `h` to offer `y`. -/
  resp : List ℝ → ℝ → Bool

namespace BargainingGame

/-- The proposer in period `t`: player `0` (MWG's player 1) in even periods. -/
def proposer (t : ℕ) : Fin 2 := if t % 2 = 0 then 0 else 1

/-- The other player. -/
def other (i : Fin 2) : Fin 2 := if i = 0 then 1 else 0

theorem other_ne (i : Fin 2) : other i ≠ i := by fin_cases i <;> decide

theorem ne_other (i : Fin 2) : i ≠ other i := (other_ne i).symm

theorem other_other (i : Fin 2) : other (other i) = i := by fin_cases i <;> decide

theorem eq_or_eq_other (i j : Fin 2) : j = i ∨ j = other i := by
  fin_cases i <;> fin_cases j <;> decide

theorem proposer_succ (t : ℕ) : proposer (t + 1) = other (proposer t) := by
  unfold proposer other
  rcases Nat.mod_two_eq_zero_or_one t with h | h
  · have : (t + 1) % 2 = 1 := by omega
    simp [h, this]
  · have : (t + 1) % 2 = 0 := by omega
    simp [h, this]

variable (B : BargainingGame)

/-- Player `i`'s share (undiscounted) of an agreement on offer `y` in period `t`. -/
def share (i : Fin 2) (t : ℕ) (y : ℝ) : ℝ := if proposer t = i then B.v - y else y

theorem share_proposer (t : ℕ) (y : ℝ) : B.share (proposer t) t y = B.v - y := by
  simp [share]

theorem share_other (t : ℕ) (y : ℝ) : B.share (other (proposer t)) t y = y := by
  simp [share, ne_other]

/-- Period `t` is within the horizon. -/
def Live (t : ℕ) : Prop := (t : ℕ∞) < B.T

theorem live_of_le {s t : ℕ} (ht : B.Live t) (hst : s ≤ t) : B.Live s :=
  lt_of_le_of_lt (Nat.cast_le.2 hst) ht

/-- The history after `t` further rejections, when offers follow `σ`. -/
def path (σ : BargainingProfile) (h : List ℝ) : ℕ → List ℝ
  | 0 => h
  | t + 1 => σ.prop (path σ h t) :: path σ h t

theorem length_path (σ : BargainingProfile) (h : List ℝ) (t : ℕ) :
    (path σ h t).length = h.length + t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [path, ih]; omega

theorem path_succ (σ : BargainingProfile) (h : List ℝ) (t : ℕ) :
    path σ h (t + 1) = path σ (σ.prop h :: h) t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [path, ih, path]

/-- Agreement is reached `t` periods after history `h` (if the earlier offers were rejected). -/
def Agrees (σ : BargainingProfile) (h : List ℝ) (t : ℕ) : Prop :=
  B.Live (h.length + t) ∧ σ.resp (path σ h t) (σ.prop (path σ h t)) = true

open Classical in
/-- Player `i`'s payoff from the proposal node `h` under `σ`, in dollars of the period of `h`:
`δ_i^T × share` if the first agreement is `T` periods later, `0` without agreement. -/
noncomputable def value (σ : BargainingProfile) (h : List ℝ) (i : Fin 2) : ℝ :=
  if hx : ∃ t, B.Agrees σ h t then
    B.δ i ^ Nat.find hx * B.share i (h.length + Nat.find hx) (σ.prop (path σ h (Nat.find hx)))
  else 0

open Classical in
/-- Player `i`'s payoff from the response node `(h, y)`. -/
noncomputable def respValue (σ : BargainingProfile) (h : List ℝ) (y : ℝ) (i : Fin 2) : ℝ :=
  if B.Live h.length ∧ σ.resp h y = true then B.share i h.length y
  else B.δ i * B.value σ (y :: h) i

open Classical in
theorem value_of_exists {σ : BargainingProfile} {h : List ℝ} (hx : ∃ t, B.Agrees σ h t)
    (i : Fin 2) : B.value σ h i = B.δ i ^ Nat.find hx *
      B.share i (h.length + Nat.find hx) (σ.prop (path σ h (Nat.find hx))) := by
  unfold value
  split_ifs
  rfl

theorem value_of_not_exists {σ : BargainingProfile} {h : List ℝ} (hx : ¬ ∃ t, B.Agrees σ h t)
    (i : Fin 2) : B.value σ h i = 0 := by
  unfold value
  split_ifs
  rfl

theorem respValue_accept {σ : BargainingProfile} {h : List ℝ} {y : ℝ} (hl : B.Live h.length)
    (hy : σ.resp h y = true) (i : Fin 2) : B.respValue σ h y i = B.share i h.length y := by
  unfold respValue
  split_ifs with hc
  · rfl
  · exact absurd ⟨hl, hy⟩ hc

theorem respValue_reject {σ : BargainingProfile} {h : List ℝ} {y : ℝ}
    (hy : σ.resp h y = false) (i : Fin 2) : B.respValue σ h y i = B.δ i * B.value σ (y :: h) i := by
  unfold respValue
  split_ifs with hc
  · simp [hy] at hc
  · rfl

/-- Beyond the horizon nothing is agreed. -/
theorem value_of_not_live {σ : BargainingProfile} {h : List ℝ} (hl : ¬ B.Live h.length)
    (i : Fin 2) : B.value σ h i = 0 :=
  B.value_of_not_exists (fun ⟨t, ht⟩ => hl (B.live_of_le ht.1 (by omega))) i

/-- The value at a proposal node is the value at the response node to the offer made there. -/
theorem value_eq_respValue (σ : BargainingProfile) {h : List ℝ} (hl : B.Live h.length)
    (i : Fin 2) : B.value σ h i = B.respValue σ h (σ.prop h) i := by
  classical
  have hshift : ∀ t, B.Agrees σ h (t + 1) ↔ B.Agrees σ (σ.prop h :: h) t := by
    intro t
    simp only [Agrees, path_succ, List.length_cons,
      show h.length + (t + 1) = h.length + 1 + t by omega]
  by_cases h0 : σ.resp h (σ.prop h) = true
  · have hA : B.Agrees σ h 0 := ⟨by simpa using hl, by simpa [path] using h0⟩
    have hx : ∃ t, B.Agrees σ h t := ⟨0, hA⟩
    rw [B.value_of_exists hx, B.respValue_accept hl h0]
    have hf : Nat.find hx = 0 := (Nat.find_eq_zero hx).2 hA
    simp only [hf, pow_zero, one_mul, add_zero, path]
  · have h0' : σ.resp h (σ.prop h) = false := by simpa using h0
    rw [B.respValue_reject h0']
    have hA0 : ¬ B.Agrees σ h 0 := fun h' => h0 (by simpa [path] using h'.2)
    by_cases hx' : ∃ t, B.Agrees σ (σ.prop h :: h) t
    · have hx : ∃ t, B.Agrees σ h t := let ⟨t, ht⟩ := hx'; ⟨t + 1, (hshift t).2 ht⟩
      have hx2 : ∃ t, B.Agrees σ h (t + 1) := let ⟨t, ht⟩ := hx'; ⟨t, (hshift t).2 ht⟩
      have hf : Nat.find hx = Nat.find hx' + 1 := by
        rw [Nat.find_comp_succ hx hx2 hA0]
        congr 1
        exact Nat.find_congr' (hshift _)
      rw [B.value_of_exists hx, B.value_of_exists hx', hf, path_succ, pow_succ]
      simp only [List.length_cons, show h.length + (Nat.find hx' + 1) =
        h.length + 1 + Nat.find hx' by omega]
      ring
    · have hx : ¬ ∃ t, B.Agrees σ h t := by
        rintro ⟨t, ht⟩
        cases t with
        | zero => exact hA0 ht
        | succ t => exact hx' ⟨t, (hshift t).1 ht⟩
      rw [B.value_of_not_exists hx, B.value_of_not_exists hx', mul_zero]

/-- The value from `h` depends only on the moves at histories at least as long as `h`. -/
theorem value_congr {σ σ' : BargainingProfile} {h : List ℝ}
    (hp : ∀ h', h.length ≤ h'.length → σ.prop h' = σ'.prop h')
    (hr : ∀ h' y, h.length ≤ h'.length → σ.resp h' y = σ'.resp h' y) (i : Fin 2) :
    B.value σ h i = B.value σ' h i := by
  classical
  have hpath : ∀ t, path σ h t = path σ' h t := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
      rw [path, path, ih, hp _ (by rw [length_path]; omega)]
  have hA : ∀ t, B.Agrees σ h t ↔ B.Agrees σ' h t := by
    intro t
    unfold Agrees
    rw [hpath, hp _ (by rw [length_path]; omega), hr _ _ (by rw [length_path]; omega)]
  by_cases hx : ∃ t, B.Agrees σ h t
  · have hx' : ∃ t, B.Agrees σ' h t := let ⟨t, ht⟩ := hx; ⟨t, (hA t).1 ht⟩
    rw [B.value_of_exists hx, B.value_of_exists hx']
    have hf : Nat.find hx = Nat.find hx' := Nat.find_congr' (hA _)
    rw [hf, hpath, hp _ (by rw [length_path]; omega)]
  · have hx' : ¬ ∃ t, B.Agrees σ' h t := fun ⟨t, ht⟩ => hx ⟨t, (hA t).2 ht⟩
    rw [B.value_of_not_exists hx, B.value_of_not_exists hx']

/-- Offers are feasible: `prop h ∈ [0, v]` at every history. -/
def Feasible (σ : BargainingProfile) : Prop := ∀ h, σ.prop h ∈ Set.Icc 0 B.v

/-- A history of feasible offers. -/
def ValidHist (h : List ℝ) : Prop := ∀ y ∈ h, y ∈ Set.Icc 0 B.v

theorem validHist_cons {h : List ℝ} (hh : B.ValidHist h) {y : ℝ} (hy : y ∈ Set.Icc 0 B.v) :
    B.ValidHist (y :: h) := by
  intro z hz
  rcases List.mem_cons.1 hz with rfl | hz
  · exact hy
  · exact hh z hz

/-- Shares of a feasible offer are in `[0, v]` and add up to `v`. -/
theorem share_mem (i : Fin 2) (t : ℕ) {y : ℝ} (hy : y ∈ Set.Icc 0 B.v) :
    0 ≤ B.share i t y ∧ B.share i t y ≤ B.v := by
  unfold share
  split_ifs <;> constructor <;> linarith [hy.1, hy.2]

theorem share_add (i : Fin 2) (t : ℕ) (y : ℝ) : B.share i t y + B.share (other i) t y = B.v := by
  unfold share
  rcases eq_or_eq_other i (proposer t) with h | h
  · rw [h]; simp [ne_other]
  · rw [h]; simp [other_ne]

/-- Payoffs are in `[0, v]` and the two players' payoffs add up to at most `v`. -/
theorem value_bounds {σ : BargainingProfile} (hσ : B.Feasible σ) (h : List ℝ) (i : Fin 2) :
    0 ≤ B.value σ h i ∧ B.value σ h i + B.value σ h (other i) ≤ B.v := by
  classical
  by_cases hx : ∃ t, B.Agrees σ h t
  · rw [B.value_of_exists hx, B.value_of_exists hx]
    set T := Nat.find hx
    set y := σ.prop (path σ h T)
    have hy := hσ (path σ h T)
    have h1 := B.share_mem i (h.length + T) hy
    have h2 := B.share_mem (other i) (h.length + T) hy
    have hadd := B.share_add i (h.length + T) y
    have hd1 : B.δ i ^ T ≤ 1 := pow_le_one₀ (B.δ_pos i).le (B.δ_lt_one i).le
    have hd2 : B.δ (other i) ^ T ≤ 1 := pow_le_one₀ (B.δ_pos _).le (B.δ_lt_one _).le
    have hp1 : 0 ≤ B.δ i ^ T := pow_nonneg (B.δ_pos i).le T
    have hp2 : 0 ≤ B.δ (other i) ^ T := pow_nonneg (B.δ_pos _).le T
    refine ⟨mul_nonneg hp1 h1.1, ?_⟩
    nlinarith [mul_le_of_le_one_left h1.1 hd1, mul_le_of_le_one_left h2.1 hd2]
  · rw [B.value_of_not_exists hx, B.value_of_not_exists hx]
    exact ⟨le_rfl, by linarith [B.v_pos]⟩

/-- Player `i`'s deviation from `σ` to `σ'`: `σ'` agrees with `σ` wherever `i` does not move. -/
def IsDeviation (i : Fin 2) (σ σ' : BargainingProfile) : Prop :=
  (∀ h, proposer h.length ≠ i → σ'.prop h = σ.prop h) ∧
    ∀ h y, proposer h.length = i → σ'.resp h y = σ.resp h y

/-- **Definition 9.B.2 for the bargaining game** (MWG, pp. 275 and 296-298). A subgame perfect
Nash equilibrium: at every feasible proposal node `h` within the horizon and at every response
node `(h, y)` with `y ∈ [0, v]`, no player gains by deviating to any feasible strategy. -/
def IsSPNE (σ : BargainingProfile) : Prop :=
  B.Feasible σ ∧ ∀ i σ', B.Feasible σ' → IsDeviation i σ σ' → ∀ h, B.ValidHist h →
    B.Live h.length → B.value σ' h i ≤ B.value σ h i ∧
      ∀ y ∈ Set.Icc 0 B.v, B.respValue σ' h y i ≤ B.respValue σ h y i

open Classical in
/-- Changing only the response at the node `(h₀, y₀)`. -/
noncomputable def setResp (σ : BargainingProfile) (h₀ : List ℝ) (y₀ : ℝ) (b : Bool) :
    BargainingProfile where
  prop := σ.prop
  resp h y := if h = h₀ ∧ y = y₀ then b else σ.resp h y

open Classical in
/-- Changing only the offer at the history `h₀`. -/
noncomputable def setProp (σ : BargainingProfile) (h₀ : List ℝ) (y₀ : ℝ) : BargainingProfile where
  prop h := if h = h₀ then y₀ else σ.prop h
  resp := σ.resp

theorem setResp_value (σ : BargainingProfile) (h₀ : List ℝ) (y₀ : ℝ) (b : Bool) (i : Fin 2) :
    B.value (setResp σ h₀ y₀ b) (y₀ :: h₀) i = B.value σ (y₀ :: h₀) i := by
  refine B.value_congr (σ := setResp σ h₀ y₀ b) (σ' := σ) (fun _ _ => rfl) (fun h' y hl => ?_) i
  have : h' ≠ h₀ := fun he => by rw [he] at hl; simp at hl
  simp [setResp, this]

theorem setProp_value (σ : BargainingProfile) (h₀ : List ℝ) (y₀ y : ℝ) (i : Fin 2) :
    B.value (setProp σ h₀ y₀) (y :: h₀) i = B.value σ (y :: h₀) i := by
  refine B.value_congr (σ := setProp σ h₀ y₀) (σ' := σ) (fun h' hl => ?_) (fun _ _ _ => rfl) i
  have : h' ≠ h₀ := fun he => by rw [he] at hl; simp at hl
  simp [setProp, this]

theorem setResp_isDeviation (σ : BargainingProfile) (h₀ : List ℝ) (y₀ : ℝ) (b : Bool) :
    IsDeviation (other (proposer h₀.length)) σ (setResp σ h₀ y₀ b) := by
  refine ⟨fun _ _ => rfl, fun h y hh => ?_⟩
  have : h ≠ h₀ := fun he => by rw [he] at hh; exact other_ne _ hh.symm
  simp [setResp, this]

theorem setProp_isDeviation (σ : BargainingProfile) (h₀ : List ℝ) (y₀ : ℝ) :
    IsDeviation (proposer h₀.length) σ (setProp σ h₀ y₀) := by
  refine ⟨fun h hh => ?_, fun _ _ _ => rfl⟩
  have : h ≠ h₀ := fun he => by rw [he] at hh; exact hh rfl
  simp [setProp, this]

theorem setResp_feasible {σ : BargainingProfile} (hσ : B.Feasible σ) (h₀ : List ℝ) (y₀ : ℝ)
    (b : Bool) : B.Feasible (setResp σ h₀ y₀ b) := hσ

theorem setProp_feasible {σ : BargainingProfile} (hσ : B.Feasible σ) (h₀ : List ℝ) {y₀ : ℝ}
    (hy : y₀ ∈ Set.Icc 0 B.v) : B.Feasible (setProp σ h₀ y₀) := by
  intro h
  simp only [setProp]
  split_ifs
  · exact hy
  · exact hσ h

/-- In an SPNE the responder accepts an offer that beats her continuation payoff. -/
theorem accept_of_gt {σ : BargainingProfile} (hσ : B.IsSPNE σ) {h : List ℝ} (hv : B.ValidHist h)
    (hl : B.Live h.length) {y : ℝ} (hy : y ∈ Set.Icc 0 B.v)
    (hgt : B.δ (other (proposer h.length)) * B.value σ (y :: h) (other (proposer h.length)) < y) :
    σ.resp h y = true := by
  by_contra hrej
  have hrej' : σ.resp h y = false := by simpa using hrej
  have := (hσ.2 _ _ (B.setResp_feasible hσ.1 h y true) (setResp_isDeviation σ h y true) h hv
    hl).2 y hy
  rw [B.respValue_accept hl (by simp [setResp]), B.respValue_reject hrej', share_other] at this
  linarith

/-- In an SPNE the responder rejects an offer below her continuation payoff. -/
theorem reject_of_lt {σ : BargainingProfile} (hσ : B.IsSPNE σ) {h : List ℝ} (hv : B.ValidHist h)
    (hl : B.Live h.length) {y : ℝ} (hy : y ∈ Set.Icc 0 B.v)
    (hlt : y < B.δ (other (proposer h.length)) * B.value σ (y :: h) (other (proposer h.length))) :
    σ.resp h y = false := by
  by_contra hacc
  have hacc' : σ.resp h y = true := by simpa using hacc
  have := (hσ.2 _ _ (B.setResp_feasible hσ.1 h y false) (setResp_isDeviation σ h y false) h hv
    hl).2 y hy
  rw [B.respValue_reject (by simp [setResp]), B.setResp_value, B.respValue_accept hl hacc',
    share_other] at this
  linarith

/-- In an SPNE the proposer does at least as well as with any other feasible offer. -/
theorem respValue_le_value {σ : BargainingProfile} (hσ : B.IsSPNE σ) {h : List ℝ}
    (hv : B.ValidHist h) (hl : B.Live h.length) {y : ℝ} (hy : y ∈ Set.Icc 0 B.v) :
    B.respValue σ h y (proposer h.length) ≤ B.value σ h (proposer h.length) := by
  have := (hσ.2 _ _ (B.setProp_feasible hσ.1 h hy) (setProp_isDeviation σ h y) h hv hl).1
  rw [B.value_eq_respValue _ hl] at this
  have hp : (setProp σ h y).prop h = y := by simp [setProp]
  rw [hp] at this
  unfold respValue at this ⊢
  rw [B.setProp_value] at this
  exact this

/-- **Shaked-Sutton lower bound** (MWG, p. 298). In an SPNE, if the responder can expect at
most `M` as the next proposer after any rejection, the proposer earns at least
`v − δ_j M`. -/
theorem value_ge_of_isSPNE {σ : BargainingProfile} (hσ : B.IsSPNE σ) {h : List ℝ}
    (hv : B.ValidHist h) (hl : B.Live h.length) {M : ℝ}
    (hM : ∀ y ∈ Set.Icc 0 B.v, B.value σ (y :: h) (other (proposer h.length)) ≤ M) :
    B.v - B.δ (other (proposer h.length)) * M ≤ B.value σ h (proposer h.length) := by
  set p := proposer h.length
  set r := other p
  have hM0 : 0 ≤ M := le_trans (B.value_bounds hσ.1 _ r).1 (hM 0 ⟨le_rfl, B.v_pos.le⟩)
  have hval0 := (B.value_bounds hσ.1 h p).1
  by_contra hlt
  push Not at hlt
  set ε := (B.v - B.δ r * M - B.value σ h p) / 2 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  set y := B.δ r * M + ε
  have hδr := B.δ_pos r
  have hy : y ∈ Set.Icc 0 B.v := ⟨by positivity, by simp only [y]; linarith⟩
  have hacc : σ.resp h y = true := by
    refine B.accept_of_gt hσ hv hl hy ?_
    have := hM y hy
    have : B.δ r * B.value σ (y :: h) r ≤ B.δ r * M := mul_le_mul_of_nonneg_left this hδr.le
    simp only [y]
    linarith
  have := B.respValue_le_value hσ hv hl hy
  rw [B.respValue_accept hl hacc, share_proposer] at this
  simp only [y] at this
  linarith

/-- **Shaked-Sutton upper bound** (MWG, p. 298). In an SPNE, if the responder can expect at
least `m ≥ 0` as the next proposer after any rejection, the proposer earns at most
`v − δ_j m`. -/
theorem value_le_of_isSPNE {σ : BargainingProfile} (hσ : B.IsSPNE σ) {h : List ℝ}
    (hv : B.ValidHist h) (hl : B.Live h.length) {m : ℝ} (hm0 : 0 ≤ m)
    (hm : ∀ y ∈ Set.Icc 0 B.v, m ≤ B.value σ (y :: h) (other (proposer h.length))) :
    B.value σ h (proposer h.length) ≤ B.v - B.δ (other (proposer h.length)) * m := by
  set p := proposer h.length
  set r := other p
  set y := σ.prop h
  have hy := hσ.1 h
  rw [B.value_eq_respValue σ hl]
  cases hacc : σ.resp h y with
  | true =>
    rw [B.respValue_accept hl hacc, share_proposer]
    have hge : B.δ r * B.value σ (y :: h) r ≤ y := by
      by_contra hlt
      push Not at hlt
      have := B.reject_of_lt hσ hv hl hy hlt
      rw [hacc] at this
      exact Bool.noConfusion this
    have := mul_le_mul_of_nonneg_left (hm y hy) (B.δ_pos r).le
    linarith
  | false =>
    rw [B.respValue_reject hacc]
    have hb := B.value_bounds hσ.1 (y :: h) p
    have hmv : m ≤ B.v := le_trans (hm y hy) (by linarith [(B.value_bounds hσ.1 (y :: h) r).1,
      (B.value_bounds hσ.1 (y :: h) r).2, other_other p ▸ hb.1])
    have h1 : B.value σ (y :: h) p ≤ B.v - m := by
      have := hm y hy
      linarith [hb.2]
    have hδp := B.δ_pos p
    have hδp1 := B.δ_lt_one p
    have hδr := B.δ_pos r
    have hδr1 := B.δ_lt_one r
    have : B.δ p * B.value σ (y :: h) p ≤ B.δ p * (B.v - m) :=
      mul_le_mul_of_nonneg_left h1 hδp.le
    nlinarith

/-- **Discounted one-stage deviation bound.** If `bnd ≥ 0` bounds player `i`'s payoff of an
immediate agreement at every live node, and `δ_i bnd(next) ≤ bnd` after every rejection, then
`bnd` bounds player `i`'s payoff from every node. -/
theorem value_le_of_bound {σ : BargainingProfile} {i : Fin 2} (bnd : List ℝ → ℝ)
    (h0 : ∀ h, 0 ≤ bnd h)
    (hacc : ∀ h, B.Live h.length → σ.resp h (σ.prop h) = true →
      B.share i h.length (σ.prop h) ≤ bnd h)
    (hrej : ∀ h, B.Live h.length → σ.resp h (σ.prop h) = false →
      B.δ i * bnd (σ.prop h :: h) ≤ bnd h)
    (h : List ℝ) : B.value σ h i ≤ bnd h := by
  classical
  have key : ∀ T h, (∀ s < T, ¬ B.Agrees σ h s) → B.Agrees σ h T →
      B.δ i ^ T * B.share i (h.length + T) (σ.prop (path σ h T)) ≤ bnd h := by
    intro T
    induction T with
    | zero =>
      intro h _ hA
      simpa [path] using hacc h (by simpa using hA.1) (by simpa [path] using hA.2)
    | succ T ih =>
      intro h hmin hA
      have hl : B.Live h.length := B.live_of_le hA.1 (by omega)
      have hrej0 : σ.resp h (σ.prop h) = false := by
        have := hmin 0 (by omega)
        by_contra hc
        exact this ⟨by simpa using hl, by simpa [path] using hc⟩
      have hshift : ∀ t, B.Agrees σ h (t + 1) ↔ B.Agrees σ (σ.prop h :: h) t := by
        intro t
        simp only [Agrees, path_succ, List.length_cons,
          show h.length + (t + 1) = h.length + 1 + t by omega]
      have := ih (σ.prop h :: h) (fun s hs h' => hmin (s + 1) (by omega) ((hshift s).2 h'))
        ((hshift T).1 hA)
      rw [path_succ, pow_succ, show h.length + (T + 1) = (σ.prop h :: h).length + T by
        simp; omega]
      have hδ := (B.δ_pos i).le
      calc B.δ i ^ T * B.δ i * B.share i ((σ.prop h :: h).length + T)
            (σ.prop (path σ (σ.prop h :: h) T))
          = B.δ i * (B.δ i ^ T * B.share i ((σ.prop h :: h).length + T)
            (σ.prop (path σ (σ.prop h :: h) T))) := by ring
        _ ≤ B.δ i * bnd (σ.prop h :: h) := mul_le_mul_of_nonneg_left this hδ
        _ ≤ bnd h := hrej h hl hrej0
  by_cases hx : ∃ t, B.Agrees σ h t
  · rw [B.value_of_exists hx]
    exact key _ h (fun s hs => Nat.find_min hx hs) (Nat.find_spec hx)
  · rw [B.value_of_not_exists hx]
    exact h0 h

/-- In an SPNE, if the responder's continuation value after rejecting is the same number `X`
for every offer, and the proposer earns `v − δ_j X` while a rejected offer would give her
less, then the SPNE strategies at `h` are determined: the proposer offers exactly `δ_j X` and
the responder accepts exactly the offers `y ≥ δ_j X`. -/
theorem strategies_determined {σ : BargainingProfile} (hσ : B.IsSPNE σ) {h : List ℝ}
    (hv : B.ValidHist h) (hl : B.Live h.length) {X : ℝ}
    (hX : ∀ y ∈ Set.Icc 0 B.v, B.value σ (y :: h) (other (proposer h.length)) = X)
    (hval : B.value σ h (proposer h.length) = B.v - B.δ (other (proposer h.length)) * X)
    (hrej : B.δ (proposer h.length) * (B.v - X) < B.v - B.δ (other (proposer h.length)) * X) :
    σ.prop h = B.δ (other (proposer h.length)) * X ∧
      ∀ y ∈ Set.Icc 0 B.v, σ.resp h y = true ↔ B.δ (other (proposer h.length)) * X ≤ y := by
  set p := proposer h.length
  set r := other p
  set y₀ := σ.prop h
  have hy₀ := hσ.1 h
  have hacc0 : σ.resp h y₀ = true := by
    by_contra hc
    have hc' : σ.resp h y₀ = false := by simpa using hc
    have h1 := B.value_eq_respValue σ hl p
    rw [B.respValue_reject hc', hval] at h1
    have hb := B.value_bounds hσ.1 (y₀ :: h) p
    have h2 : B.value σ (y₀ :: h) p ≤ B.v - X := by
      have := hX y₀ hy₀
      have h3 := hb.2
      rw [show other p = r from rfl, this] at h3
      linarith
    have := mul_le_mul_of_nonneg_left h2 (B.δ_pos p).le
    linarith
  have hprop : y₀ = B.δ r * X := by
    have h1 := B.value_eq_respValue σ hl p
    rw [B.respValue_accept hl hacc0, share_proposer, hval] at h1
    linarith
  refine ⟨hprop, fun y hy => ⟨fun hacc => ?_, fun hge => ?_⟩⟩
  · by_contra hlt
    push Not at hlt
    have := B.reject_of_lt hσ hv hl hy (by rw [hX y hy]; exact hlt)
    rw [hacc] at this
    exact Bool.noConfusion this
  · rcases hge.lt_or_eq with hgt | heq
    · exact B.accept_of_gt hσ hv hl hy (by rw [hX y hy]; exact hgt)
    · rw [← heq, ← hprop]
      exact hacc0

end BargainingGame

end MWG.DynamicGames

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Uniqueness of the SPNE in the alternating-offer bargaining games

MWG, Appendix A of Chapter 9, pp. 296-299: Examples 9.AA.1 (Stahl's finite horizon game) and
9.AA.2 (Rubinstein's infinite horizon game), and Exercise 9.B.12 (different discount factors).

* `threshold c`: the profile in which the period-`t` proposer offers `c t` and the responder
  accepts exactly the offers `y ≥ c t`. `threshold_isSPNE`: if `c t` is the responder's
  discounted continuation value (`c t = δ_j (v − c (t+1))`, and `0` in the last period) the
  profile is an SPNE (proved with the discounted one-stage deviation bound).
* `exercise_9_B_12` (Rubinstein with discount factors `δ₁, δ₂`): there is a unique SPNE. In
  it the proposer `i` offers `δ_j x_j` and earns `x_i = v (1 − δ_j) / (1 − δ_i δ_j)`; the
  responder accepts exactly the offers of at least `δ_j x_j`; agreement is immediate.
  `example_9_AA_2` is the case `δ₁ = δ₂ = δ`: player 1 earns `v / (1 + δ)`, player 2
  `δ v / (1 + δ)`.
* `example_9_AA_1` (finite horizon `T`, common `δ`): unique SPNE; from a node with `n` periods
  left the proposer earns `P n = v (1 − (−δ)^n) / (1 + δ)`, with MWG's closed forms for odd and
  even `T` (`example_9_AA_1_odd`, `example_9_AA_1_even`) and limit `v / (1 + δ)` as
  `T → ∞` (`example_9_AA_1_limit`; the infinite-horizon outcome is the limit, p. 299).
-/

namespace MWG.DynamicGames

namespace BargainingGame

variable (B : BargainingGame)

/-- The threshold profile: in period `t` the proposer offers `c t`; the responder accepts
exactly the offers `y ≥ c t`. -/
noncomputable def threshold (c : ℕ → ℝ) : BargainingProfile where
  prop h := c h.length
  resp h y := decide (c h.length ≤ y)

/-- Payoffs of a threshold profile from a live node: the proposer gets `v − c t`, the
responder `c t` (immediate agreement). -/
theorem value_threshold (c : ℕ → ℝ) {h : List ℝ} (hl : B.Live h.length) :
    B.value (threshold c) h (proposer h.length) = B.v - c h.length ∧
      B.value (threshold c) h (other (proposer h.length)) = c h.length := by
  have hacc : (threshold c).resp h ((threshold c).prop h) = true := by simp [threshold]
  rw [B.value_eq_respValue _ hl, B.value_eq_respValue _ hl, B.respValue_accept hl hacc,
    B.respValue_accept hl hacc, share_proposer, share_other]
  exact ⟨rfl, rfl⟩

/-- **Threshold profiles are SPNE** (MWG, pp. 296-299). If `c t ∈ [0, v]` for all `t`, and in
every live period `c t` is the responder's discounted value as the next proposer
(`c t = δ_j (v − c (t + 1))` if period `t + 1` is live, `c t = 0` if `t` is the last period),
then `threshold c` is a subgame perfect Nash equilibrium. -/
theorem threshold_isSPNE {c : ℕ → ℝ} (hc0 : ∀ t, c t ∈ Set.Icc 0 B.v)
    (hc1 : ∀ t, B.Live (t + 1) → c t = B.δ (other (proposer t)) * (B.v - c (t + 1)))
    (hc2 : ∀ t, B.Live t → ¬ B.Live (t + 1) → c t = 0) : B.IsSPNE (threshold c) := by
  classical
  refine ⟨fun h => hc0 h.length, fun i σ' hσ' hdev h hv hl => ?_⟩
  -- the bound: the threshold profile's value
  let bnd : List ℝ → ℝ := fun h => if B.Live h.length then
    (if proposer h.length = i then B.v - c h.length else c h.length) else 0
  have hbnd_val : ∀ h, B.value (threshold c) h i = bnd h := by
    intro h
    simp only [bnd]
    split_ifs with hl' hp
    · rw [← hp]; exact (B.value_threshold c hl').1
    · rcases eq_or_eq_other (proposer h.length) i with h1 | h1
      · exact absurd h1.symm hp
      · rw [h1]; exact (B.value_threshold c hl').2
    · exact B.value_of_not_live hl' i
  have hbnd0 : ∀ h, 0 ≤ bnd h := by
    intro h
    simp only [bnd]
    split_ifs
    · linarith [(hc0 h.length).2]
    · exact (hc0 h.length).1
    · exact le_rfl
  have hδi := B.δ_pos i
  have hδi1 := B.δ_lt_one i
  -- the deviation's value is bounded by `bnd`
  have hle : ∀ h, B.value σ' h i ≤ bnd h := by
    refine B.value_le_of_bound bnd hbnd0 (fun h hl hacc => ?_) (fun h hl hrej => ?_)
    · simp only [bnd, hl, ite_true]
      split_ifs with hp
      · have hr : σ'.resp h (σ'.prop h) = (threshold c).resp h (σ'.prop h) := hdev.2 h _ hp
        rw [hacc] at hr
        have hr' : c h.length ≤ σ'.prop h := by simpa [threshold] using hr.symm
        rw [← hp, share_proposer]
        linarith
      · have hpr : σ'.prop h = c h.length := hdev.1 h hp
        rcases eq_or_eq_other (proposer h.length) i with h1 | h1
        · exact absurd h1.symm hp
        · rw [hpr, h1, share_other]
    · have hlen : (σ'.prop h :: h).length = h.length + 1 := rfl
      have hbl : bnd h = if proposer h.length = i then B.v - c h.length else c h.length := by
        simp only [bnd, hl, ite_true]
      rw [hbl]
      by_cases hl1 : B.Live (h.length + 1)
      · have hbn : bnd (σ'.prop h :: h) = if proposer (h.length + 1) = i then
            B.v - c (h.length + 1) else c (h.length + 1) := by
          simp only [bnd, hlen, hl1, ite_true]
        rw [hbn, proposer_succ]
        have h1 := hc1 h.length hl1
        have hc := hc0 (h.length + 1)
        rcases eq_or_eq_other i (proposer h.length) with hp | hp
        · rw [hp] at h1 ⊢
          simp only [other_ne, ite_false, ite_true]
          have hδo := B.δ_pos (other i)
          have hδo1 := B.δ_lt_one (other i)
          rw [h1]
          nlinarith [mul_nonneg (sub_nonneg.2 hc.2) (sub_nonneg.2 hδo1.le),
            mul_nonneg hc.1 (sub_nonneg.2 hδi1.le)]
        · rw [hp, other_other] at h1 ⊢
          simp only [other_ne, ite_false, ite_true]
          rw [h1]
      · have hbn : bnd (σ'.prop h :: h) = 0 := by simp only [bnd, hlen, hl1, ite_false]
        rw [hbn, mul_zero, ← hbl]
        exact hbnd0 h
  refine ⟨by rw [hbnd_val]; exact hle h, fun y hy => ?_⟩
  have hyh : B.value σ' (y :: h) i ≤ B.value (threshold c) (y :: h) i := by
    rw [hbnd_val]; exact hle _
  by_cases hp : proposer h.length = i
  · have hr : σ'.resp h y = (threshold c).resp h y := hdev.2 h y hp
    unfold respValue
    rw [hr]
    split_ifs
    · exact le_rfl
    · exact mul_le_mul_of_nonneg_left hyh hδi.le
  · have hi : other (proposer h.length) = i := by
      rcases eq_or_eq_other (proposer h.length) i with h2 | h2
      · exact absurd h2.symm hp
      · exact h2.symm
    -- the threshold responder's value is `max y (c t)`
    have hcont : B.δ i * B.value (threshold c) (y :: h) i = c h.length := by
      rw [hbnd_val]
      simp only [bnd, List.length_cons, proposer_succ, hi, ite_true]
      by_cases hl1 : B.Live (h.length + 1)
      · simp only [hl1, ite_true]
        have := hc1 h.length hl1
        rw [hi] at this
        rw [this]
      · simp only [hl1, ite_false, mul_zero]
        exact (hc2 h.length hl hl1).symm
    have hthr : max y (c h.length) ≤ B.respValue (threshold c) h y i := by
      by_cases hyc : c h.length ≤ y
      · rw [B.respValue_accept hl (by simp [threshold, hyc]), ← hi, share_other]
        exact max_le le_rfl hyc
      · rw [B.respValue_reject (by simp [threshold, hyc]), hcont]
        exact max_le (le_of_lt (not_le.1 hyc)) le_rfl
    refine le_trans ?_ hthr
    unfold respValue
    split_ifs with hacc
    · rw [← hi, share_other]
      exact le_max_left _ _
    · calc B.δ i * B.value σ' (y :: h) i ≤ B.δ i * B.value (threshold c) (y :: h) i :=
            mul_le_mul_of_nonneg_left hyh hδi.le
        _ = c h.length := hcont
        _ ≤ max y (c h.length) := le_max_right _ _

/-- Proposer `i`'s Rubinstein payoff `x_i = v (1 − δ_j) / (1 − δ_i δ_j)`. -/
noncomputable def xstar (i : Fin 2) : ℝ :=
  B.v * (1 - B.δ (other i)) / (1 - B.δ i * B.δ (other i))

theorem one_sub_mul_pos (i : Fin 2) : 0 < 1 - B.δ i * B.δ (other i) := by
  have := B.δ_lt_one i
  have := B.δ_lt_one (other i)
  have := B.δ_pos i
  have := B.δ_pos (other i)
  nlinarith

/-- `x_i + δ_j x_j = v`: the proposer's share plus the responder's discounted value. -/
theorem xstar_add (i : Fin 2) : B.xstar i + B.δ (other i) * B.xstar (other i) = B.v := by
  have h1 := B.one_sub_mul_pos i
  have h2 := B.one_sub_mul_pos (other i)
  unfold xstar
  rw [other_other]
  have hne : 1 - B.δ i * B.δ (other i) ≠ 0 := h1.ne'
  have hne' : 1 - B.δ (other i) * B.δ i ≠ 0 := by rw [mul_comm]; exact hne
  field_simp
  ring

theorem xstar_mem (i : Fin 2) : B.xstar i ∈ Set.Icc 0 B.v ∧ 0 < B.xstar i := by
  have h1 := B.one_sub_mul_pos i
  have hv := B.v_pos
  have hd := B.δ_lt_one (other i)
  have hd0 := B.δ_pos (other i)
  have hdi := B.δ_pos i
  have hdi1 := B.δ_lt_one i
  have hpos : 0 < B.xstar i := by unfold xstar; apply div_pos <;> nlinarith
  refine ⟨⟨hpos.le, ?_⟩, hpos⟩
  unfold xstar
  rw [div_le_iff₀ h1]
  nlinarith [mul_pos (mul_pos hv hd0) (sub_pos.2 hdi1)]

/-- The Rubinstein offer in period `t`: the responder's discounted value `δ_j x_j`. -/
noncomputable def rubOffer (t : ℕ) : ℝ := B.δ (other (proposer t)) * B.xstar (other (proposer t))

theorem rubOffer_mem (t : ℕ) : B.rubOffer t ∈ Set.Icc 0 B.v := by
  have h := B.xstar_mem (other (proposer t))
  have hd := B.δ_pos (other (proposer t))
  have hd1 := B.δ_lt_one (other (proposer t))
  unfold rubOffer
  constructor
  · exact mul_nonneg hd.le h.1.1
  · nlinarith [h.1.2]

/-- In the infinite horizon game every period is live. -/
theorem live_of_top (hT : B.T = ⊤) (t : ℕ) : B.Live t := by
  unfold Live
  rw [hT]
  exact ENat.natCast_lt_top t

/-- The stationary Rubinstein profile is an SPNE of the infinite horizon game. -/
theorem rubinstein_isSPNE (hT : B.T = ⊤) : B.IsSPNE (threshold B.rubOffer) := by
  refine B.threshold_isSPNE B.rubOffer_mem (fun t _ => ?_)
    (fun t _ h => absurd (B.live_of_top hT (t + 1)) h)
  unfold rubOffer
  rw [proposer_succ, other_other]
  have := B.xstar_add (other (proposer t))
  rw [other_other] at this
  rw [show B.v - B.δ (proposer t) * B.xstar (proposer t) = B.xstar (other (proposer t)) by
    linarith]

/-- SPNE payoffs of the proposer, over all SPNE and all feasible histories where `i` proposes. -/
def spnePayoffs (i : Fin 2) : Set ℝ :=
  {x | ∃ σ, B.IsSPNE σ ∧ ∃ h, B.ValidHist h ∧ proposer h.length = i ∧ x = B.value σ h i}

theorem validHist_nil : B.ValidHist [] := fun _ h => absurd h List.not_mem_nil

/-- **Rubinstein's theorem, payoffs** (MWG, Example 9.AA.2, p. 298; Exercise 9.B.12). In the
infinite horizon game, in every SPNE and at every feasible proposal node, the proposer `i`
earns exactly `x_i = v (1 − δ_j) / (1 − δ_i δ_j)`. -/
theorem rubinstein_value (hT : B.T = ⊤) {σ : BargainingProfile} (hσ : B.IsSPNE σ)
    {h : List ℝ} (hv : B.ValidHist h) :
    B.value σ h (proposer h.length) = B.xstar (proposer h.length) := by
  have hbdd : ∀ i, BddAbove (B.spnePayoffs i) ∧ BddBelow (B.spnePayoffs i) := fun i =>
    ⟨⟨B.v, fun x ⟨σ, hσ, h, _, _, hx⟩ => by
      rw [hx]
      have := B.value_bounds hσ.1 h i
      have := (B.value_bounds hσ.1 h (other i)).1
      linarith⟩,
    ⟨0, fun x ⟨σ, hσ, h, _, _, hx⟩ => by rw [hx]; exact (B.value_bounds hσ.1 h i).1⟩⟩
  have hne : ∀ i, (B.spnePayoffs i).Nonempty := by
    intro i
    rcases eq_or_eq_other 0 i with h0 | h1
    · exact ⟨_, threshold B.rubOffer, B.rubinstein_isSPNE hT, [], B.validHist_nil,
        by rw [h0]; rfl, rfl⟩
    · refine ⟨_, threshold B.rubOffer, B.rubinstein_isSPNE hT, [0],
        B.validHist_cons B.validHist_nil ⟨le_rfl, B.v_pos.le⟩, ?_, rfl⟩
      rw [h1]; rfl
  set M : Fin 2 → ℝ := fun i => sSup (B.spnePayoffs i)
  set m : Fin 2 → ℝ := fun i => sInf (B.spnePayoffs i)
  have hm0 : ∀ i, 0 ≤ m i := fun i =>
    le_csInf (hne i) fun x ⟨σ, hσ, h, _, _, hx⟩ => by rw [hx]; exact (B.value_bounds hσ.1 h i).1
  -- the two Shaked-Sutton bounds at any SPNE node
  have hnext : ∀ σ, B.IsSPNE σ → ∀ h, B.ValidHist h → ∀ y ∈ Set.Icc 0 B.v,
      B.value σ (y :: h) (other (proposer h.length)) ∈
        B.spnePayoffs (other (proposer h.length)) := fun σ hσ h hv y hy =>
    ⟨σ, hσ, y :: h, B.validHist_cons hv hy, proposer_succ _, rfl⟩
  have hlo : ∀ i, B.v - B.δ (other i) * M (other i) ≤ m i := by
    intro i
    refine le_csInf (hne i) fun x ⟨σ, hσ, h, hv, hp, hx⟩ => ?_
    rw [hx, ← hp]
    exact B.value_ge_of_isSPNE hσ hv (B.live_of_top hT _) fun y hy =>
      le_csSup (hbdd _).1 (hnext σ hσ h hv y hy)
  have hhi : ∀ i, M i ≤ B.v - B.δ (other i) * m (other i) := by
    intro i
    refine csSup_le (hne i) fun x ⟨σ, hσ, h, hv, hp, hx⟩ => ?_
    rw [hx, ← hp]
    exact B.value_le_of_isSPNE hσ hv (B.live_of_top hT _) (hm0 _) fun y hy =>
      csInf_le (hbdd _).2 (hnext σ hσ h hv y hy)
  have hsolve : ∀ i, M i ≤ B.xstar i ∧ B.xstar i ≤ m i := by
    intro i
    have h1 := hhi i
    have h2 := hlo (other i)
    have h3 := hlo i
    have h4 := hhi (other i)
    rw [other_other] at h2 h4
    have hd := B.δ_pos (other i)
    have hdi := B.δ_pos i
    have hD := B.one_sub_mul_pos i
    unfold xstar
    constructor
    · rw [le_div_iff₀ hD]
      have : B.δ (other i) * (B.v - B.δ i * M i) ≤ B.δ (other i) * m (other i) :=
        mul_le_mul_of_nonneg_left h2 hd.le
      nlinarith
    · rw [div_le_iff₀ hD]
      have : B.δ (other i) * M (other i) ≤ B.δ (other i) * (B.v - B.δ i * m i) :=
        mul_le_mul_of_nonneg_left h4 hd.le
      nlinarith
  set i := proposer h.length
  have hx : B.value σ h i ∈ B.spnePayoffs i := ⟨σ, hσ, h, hv, rfl, rfl⟩
  have h1 := le_csSup (hbdd i).1 hx
  have h2 := csInf_le (hbdd i).2 hx
  have := hsolve i
  linarith [this.1, this.2]

/-- **Exercise 9.B.12** (MWG, p. 303; Rubinstein 1982). The infinite horizon bargaining game
with discount factors `δ₁, δ₂ ∈ (0, 1)` has a unique SPNE (on feasible histories): the
proposer `i` offers `δ_j x_j` with `x_j = v (1 − δ_i) / (1 − δ_i δ_j)`, the responder `j`
accepts exactly the offers `y ≥ δ_j x_j`; agreement is immediate, player 1 earning
`x_1 = v (1 − δ₂) / (1 − δ₁ δ₂)` and player 2 earning `v − x_1`. -/
theorem exercise_9_B_12 (hT : B.T = ⊤) :
    B.IsSPNE (threshold B.rubOffer) ∧
    ∀ σ, B.IsSPNE σ → ∀ h, B.ValidHist h →
      σ.prop h = (threshold B.rubOffer).prop h ∧
      (∀ y ∈ Set.Icc 0 B.v, σ.resp h y = (threshold B.rubOffer).resp h y) ∧
      B.value σ h (proposer h.length) = B.xstar (proposer h.length) ∧
      B.value σ h (other (proposer h.length)) = B.v - B.xstar (proposer h.length) := by
  refine ⟨B.rubinstein_isSPNE hT, fun σ hσ h hv => ?_⟩
  set p := proposer h.length
  have hl := B.live_of_top hT h.length
  have hX : ∀ y ∈ Set.Icc 0 B.v, B.value σ (y :: h) (other p) = B.xstar (other p) :=
    fun y hy => by
      have := B.rubinstein_value hT hσ (B.validHist_cons hv hy)
      simpa [List.length_cons, proposer_succ] using this
  have hval : B.value σ h p = B.v - B.δ (other p) * B.xstar (other p) := by
    rw [B.rubinstein_value hT hσ hv]
    have := B.xstar_add p
    linarith
  have hrej : B.δ p * (B.v - B.xstar (other p)) < B.v - B.δ (other p) * B.xstar (other p) := by
    have h1 := B.xstar_add p
    have h2 := B.xstar_add (other p)
    rw [other_other] at h2
    have hx := (B.xstar_mem p).2
    have hd := B.δ_pos p
    have hd1 := B.δ_lt_one p
    rw [show B.v - B.xstar (other p) = B.δ p * B.xstar p by linarith,
      show B.v - B.δ (other p) * B.xstar (other p) = B.xstar p by linarith]
    have : 0 < B.xstar p * (1 - B.δ p) * (1 + B.δ p) :=
      mul_pos (mul_pos hx (sub_pos.2 hd1)) (by linarith)
    nlinarith
  obtain ⟨hprop, hresp⟩ := B.strategies_determined hσ hv hl hX hval hrej
  refine ⟨hprop, fun y hy => ?_, B.rubinstein_value hT hσ hv, ?_⟩
  · have := hresp y hy
    change σ.resp h y = decide (B.rubOffer h.length ≤ y)
    unfold rubOffer
    by_cases hc : B.δ (other p) * B.xstar (other p) ≤ y
    · rw [this.2 hc]
      exact (decide_eq_true hc).symm
    · rw [decide_eq_false hc]
      cases hb : σ.resp h y
      · rfl
      · exact absurd (this.1 hb) hc
  · -- the responder gets the agreed offer
    have hacc : σ.resp h (σ.prop h) = true := (hresp _ (hσ.1 h)).2 (by rw [hprop])
    rw [B.value_eq_respValue σ hl, B.respValue_accept hl hacc, share_other, hprop]
    have := B.xstar_add p
    linarith

/-- **Example 9.AA.2** (MWG, p. 298; Rubinstein 1982). With a common discount factor `δ`, the
infinite horizon alternating-offer game has a unique SPNE: a player who has just received an
offer accepts iff it gives her at least `δ v / (1 + δ)`, and a proposer offers exactly
`δ v / (1 + δ)`; agreement is immediate, with payoffs `v / (1 + δ)` and `δ v / (1 + δ)`. -/
theorem example_9_AA_2 (hT : B.T = ⊤) (hδ : B.δ 0 = B.δ 1) :
    B.IsSPNE (threshold B.rubOffer) ∧
    (∀ t, B.rubOffer t = B.δ 0 * B.v / (1 + B.δ 0)) ∧
    ∀ σ, B.IsSPNE σ → ∀ h, B.ValidHist h →
      σ.prop h = B.δ 0 * B.v / (1 + B.δ 0) ∧
      (∀ y ∈ Set.Icc 0 B.v, σ.resp h y = true ↔ B.δ 0 * B.v / (1 + B.δ 0) ≤ y) ∧
      B.value σ h (proposer h.length) = B.v / (1 + B.δ 0) ∧
      B.value σ h (other (proposer h.length)) = B.δ 0 * B.v / (1 + B.δ 0) := by
  have hall : ∀ i, B.δ i = B.δ 0 := fun i => by fin_cases i <;> simp [hδ]
  have hx : ∀ i, B.xstar i = B.v / (1 + B.δ 0) := by
    intro i
    unfold xstar
    rw [hall i, hall (other i)]
    have h1 : (1 : ℝ) + B.δ 0 ≠ 0 := by linarith [B.δ_pos 0]
    have h2 : (1 : ℝ) - B.δ 0 ≠ 0 := by linarith [B.δ_lt_one 0]
    have h3 : (1 : ℝ) - B.δ 0 * B.δ 0 = (1 - B.δ 0) * (1 + B.δ 0) := by ring
    rw [h3]
    field_simp
  have hoff : ∀ t, B.rubOffer t = B.δ 0 * B.v / (1 + B.δ 0) := by
    intro t
    unfold rubOffer
    rw [hx, hall]
    ring
  obtain ⟨hS, hU⟩ := B.exercise_9_B_12 hT
  refine ⟨hS, hoff, fun σ hσ h hv => ?_⟩
  obtain ⟨hp, hr, hv1, hv2⟩ := hU σ hσ h hv
  refine ⟨by rw [hp]; exact hoff _, fun y hy => ?_, by rw [hv1, hx], ?_⟩
  · rw [hr y hy]
    simp [threshold, hoff]
  · rw [hv2, hx]
    have h1 : (1 : ℝ) + B.δ 0 ≠ 0 := by linarith [B.δ_pos 0]
    field_simp
    ring

/-- The finite horizon proposer payoffs with `n` periods left: `P 0 = 0`,
`P (n + 1) = v − δ P n`. -/
noncomputable def finP (v δ : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => v - δ * finP v δ n

theorem finP_mem {v δ : ℝ} (hv : 0 < v) (hδ0 : 0 < δ) (hδ1 : δ < 1) (n : ℕ) :
    finP v δ n ∈ Set.Icc 0 v := by
  induction n with
  | zero => exact ⟨le_rfl, hv.le⟩
  | succ n ih =>
    simp only [finP]
    constructor <;> nlinarith [ih.1, ih.2]

/-- `P n = v (1 − (−δ)^n) / (1 + δ)`. -/
theorem finP_eq {v δ : ℝ} (hδ0 : 0 < δ) (n : ℕ) :
    finP v δ n = v * (1 - (-δ) ^ n) / (1 + δ) := by
  have h1 : (1 : ℝ) + δ ≠ 0 := by linarith
  induction n with
  | zero => simp [finP]
  | succ n ih =>
    simp only [finP, ih, pow_succ]
    field_simp
    ring

/-- **Example 9.AA.1** (MWG, pp. 296-297; Stahl 1972). In the `T`-period alternating-offer game
with common discount factor `δ`, there is a unique SPNE. From a node with `n ≥ 1` periods
left, the proposer offers `δ P (n − 1)` and earns `P n`, the responder accepts exactly the
offers `y ≥ δ P (n − 1)`; in particular player 1 earns `v₁*(T) = P T` and player 2
`v − v₁*(T)`, agreement being immediate. -/
theorem example_9_AA_1 (N : ℕ) (hT : B.T = N) (hδ : B.δ 0 = B.δ 1) :
    B.IsSPNE (threshold fun t => B.δ 0 * finP B.v (B.δ 0) (N - t - 1)) ∧
    ∀ σ, B.IsSPNE σ → ∀ h, B.ValidHist h → h.length < N →
      B.value σ h (proposer h.length) = finP B.v (B.δ 0) (N - h.length) ∧
      σ.prop h = B.δ 0 * finP B.v (B.δ 0) (N - h.length - 1) ∧
      ∀ y ∈ Set.Icc 0 B.v, σ.resp h y = true ↔ B.δ 0 * finP B.v (B.δ 0) (N - h.length - 1) ≤ y := by
  have hall : ∀ i, B.δ i = B.δ 0 := fun i => by fin_cases i <;> simp [hδ]
  set δ := B.δ 0
  have hδ0 : 0 < δ := B.δ_pos 0
  have hδ1 : δ < 1 := B.δ_lt_one 0
  have hlive : ∀ t, B.Live t ↔ t < N := fun t => by
    unfold Live
    rw [hT]
    exact Nat.cast_lt
  have hP := finP_mem B.v_pos hδ0 hδ1
  refine ⟨B.threshold_isSPNE (fun t => ?_) (fun t ht => ?_) (fun t ht ht1 => ?_), ?_⟩
  · have := hP (N - t - 1)
    exact ⟨mul_nonneg hδ0.le this.1, by nlinarith [this.1, this.2]⟩
  · rw [hlive] at ht
    show δ * finP B.v δ (N - t - 1) =
      B.δ (other (proposer t)) * (B.v - δ * finP B.v δ (N - (t + 1) - 1))
    rw [hall, show N - t - 1 = (N - (t + 1) - 1) + 1 by omega, finP]
  · rw [hlive] at ht ht1
    have : N - t - 1 = 0 := by omega
    simp only [this, finP, mul_zero]
  · intro σ hσ
    -- induction on the number of periods left
    have key : ∀ n, ∀ h, B.ValidHist h → h.length + n = N → 1 ≤ n →
        B.value σ h (proposer h.length) = finP B.v δ n := by
      intro n
      induction n with
      | zero => intro h _ _ hn; omega
      | succ n ih =>
        intro h hv hn _
        have hl : B.Live h.length := (hlive _).2 (by omega)
        have hnext : ∀ y ∈ Set.Icc 0 B.v,
            B.value σ (y :: h) (other (proposer h.length)) = finP B.v δ n := by
          intro y hy
          rcases Nat.eq_zero_or_pos n with h0 | h0
          · subst h0
            rw [B.value_of_not_live (by rw [hlive]; simp; omega)]
            rfl
          · have := ih (y :: h) (B.validHist_cons hv hy) (by simp; omega) h0
            simpa [proposer_succ] using this
        have hge := B.value_ge_of_isSPNE hσ hv hl (M := finP B.v δ n)
          fun y hy => (hnext y hy).le
        have hle := B.value_le_of_isSPNE hσ hv hl (hP n).1 fun y hy => (hnext y hy).ge
        rw [hall] at hge hle
        simp only [finP]
        linarith
    intro h hv hlt
    have hl : B.Live h.length := (hlive _).2 hlt
    have hval := key (N - h.length) h hv (by omega) (by omega)
    have hX : ∀ y ∈ Set.Icc 0 B.v,
        B.value σ (y :: h) (other (proposer h.length)) = finP B.v δ (N - h.length - 1) := by
      intro y hy
      by_cases hN : h.length + 1 < N
      · have := key (N - h.length - 1) (y :: h) (B.validHist_cons hv hy) (by simp; omega)
          (by omega)
        simpa [proposer_succ] using this
      · rw [B.value_of_not_live (by rw [hlive]; simp; omega),
          show N - h.length - 1 = 0 by omega]
        rfl
    have hval' : B.value σ h (proposer h.length) =
        B.v - B.δ (other (proposer h.length)) * finP B.v δ (N - h.length - 1) := by
      rw [hval, hall]
      obtain ⟨n, hn⟩ : ∃ n, N - h.length = n + 1 := ⟨N - h.length - 1, by omega⟩
      rw [hn, finP, Nat.add_sub_cancel]
    have hrej : B.δ (proposer h.length) * (B.v - finP B.v δ (N - h.length - 1)) <
        B.v - B.δ (other (proposer h.length)) * finP B.v δ (N - h.length - 1) := by
      rw [hall, hall]
      nlinarith [B.v_pos]
    obtain ⟨hp, hr⟩ := B.strategies_determined hσ hv hl hX hval' hrej
    rw [hall] at hp hr
    exact ⟨hval, hp, hr⟩

/-- **Example 9.AA.1** (MWG, p. 297). For odd `T`, player 1's SPNE payoff is
`v₁*(T) = v [1 − δ + δ² − ⋯ + δ^{T−1}] = v [(1 − δ)(1 − δ^{T−1}) / (1 − δ²) + δ^{T−1}]`. -/
theorem example_9_AA_1_odd {v δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) {T : ℕ} (hT : Odd T) :
    finP v δ T = v * ∑ k ∈ Finset.range T, (-δ) ^ k ∧
      finP v δ T = v * ((1 - δ) * (1 - δ ^ (T - 1)) / (1 - δ ^ 2) + δ ^ (T - 1)) := by
  have h1 : (1 : ℝ) + δ ≠ 0 := by linarith
  have h2 : (1 : ℝ) - δ ^ 2 ≠ 0 := by nlinarith
  have h3 : (-1 - δ : ℝ) ≠ 0 := fun h => by linarith
  have h4 : (-δ - 1 : ℝ) ≠ 0 := fun h => by linarith
  obtain ⟨k, rfl⟩ := hT
  constructor
  · rw [finP_eq hδ0, geom_sum_eq (by linarith : (-δ : ℝ) ≠ 1)]
    field_simp
    ring
  · rw [finP_eq hδ0, show 2 * k + 1 - 1 = 2 * k by omega, pow_succ, pow_mul, neg_sq]
    rw [pow_mul]
    field_simp
    ring

/-- **Example 9.AA.1** (MWG, p. 297). For even `T`, player 1 earns `v − δ v₁*(T − 1)`. -/
theorem example_9_AA_1_even {v δ : ℝ} {T : ℕ} (hT : Even T) (hT0 : 0 < T) :
    finP v δ T = v - δ * finP v δ (T - 1) := by
  obtain ⟨k, rfl⟩ := hT
  rw [show k + k = (k + k - 1) + 1 by omega, finP]
  rfl

/-- **Example 9.AA.1** (MWG, p. 297). As the horizon grows, player 1's payoff converges to
`v / (1 + δ)` and player 2's to `δ v / (1 + δ)`: the infinite-horizon payoffs. -/
theorem example_9_AA_1_limit {v δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    Filter.Tendsto (fun T => finP v δ T) Filter.atTop (nhds (v / (1 + δ))) ∧
      Filter.Tendsto (fun T => v - finP v δ T) Filter.atTop (nhds (δ * v / (1 + δ))) := by
  have hpow : Filter.Tendsto (fun n : ℕ => (-δ) ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by rw [abs_neg, abs_of_pos hδ0]; exact hδ1)
  have h1 : Filter.Tendsto (fun T => finP v δ T) Filter.atTop (nhds (v / (1 + δ))) := by
    simp_rw [finP_eq hδ0]
    have := ((tendsto_const_nhds (x := (1 : ℝ))).sub hpow).const_mul v |>.div_const (1 + δ)
    simpa using this
  refine ⟨h1, ?_⟩
  have := (tendsto_const_nhds (x := v)).sub h1
  convert this using 2
  have : (1 : ℝ) + δ ≠ 0 := by linarith
  field_simp
  ring

end BargainingGame

end MWG.DynamicGames

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The agent normal form and extensive form trembling-hand perfection

MWG, Appendix B of Chapter 9, pp. 299-300.

* `Agent G`: the personal information sets of `Γ_E`; `agentForm G` is the extensive form in
  which each information set is controlled by a separate agent maximising the payoff of the
  player who owns it (Selten's agent form). Its normal form `agentNF G` is the **agent normal
  form** (MWG, p. 299).
* `agentProfile G σ`: the behaviour profile of `Γ_E` given by a mixed profile `σ` of the agent
  normal form (an agent's pure strategies are the actions at its information set,
  `agentEquiv`). `agentNF_mixedPayoff`: without absent-mindedness, agent `H`'s payoff in the
  agent normal form at `σ` is the expected payoff of its owner in `Γ_E` under
  `agentProfile G σ` (via Kuhn's construction of Chapter 7).
* `IsEFTHP` is **Definition 9.BB.1**; `exists_isEFTHP`: every finite game has an extensive form
  trembling-hand perfect Nash equilibrium (Selten 1975; Chapter 8's Exercise 8.F.3 applied to
  the agent normal form).
-/

namespace MWG.DynamicGames

open MWG.NoncooperativeGames MWG.NoncooperativeGames.ExtensiveForm MWG.SimultaneousMoveGames

variable {I A H : Type*} (G : ExtensiveForm I A H) [DecidableEq A] [Fintype A] [DecidableEq I]
  [DecidableEq H]

/-- An agent: a personal (non-nature) information set. -/
abbrev Agent := {k : H // G.player k ≠ none}

/-- The player who owns an agent. -/
def owner (ag : Agent G) : I := (G.player ag.1).get (Option.isSome_iff_ne_none.2 ag.2)

omit [DecidableEq A] [Fintype A] [DecidableEq I] [DecidableEq H] in
theorem player_owner (ag : Agent G) : G.player ag.1 = some (owner G ag) := by
  simp [owner]

/-- **Appendix 9.B** (MWG, p. 299). Selten's agent form: the same tree, information sets and
moves of nature, with a separate agent at every personal information set, whose payoff is
that of the player owning the information set. -/
def agentForm : ExtensiveForm (Agent G) A H where
  nodes := G.nodes
  nil_mem := G.nil_mem
  tail_mem := G.tail_mem
  info := G.info
  avail := G.avail
  avail_spec := G.avail_spec
  info_surj := G.info_surj
  player k := if h : G.player k = none then none else some ⟨k, h⟩
  natureProb := G.natureProb
  nature_nonneg := fun k hk => G.nature_nonneg k (by by_contra h; simp [h] at hk)
  nature_zero := fun k hk => G.nature_zero k (by by_contra h; simp [h] at hk)
  nature_sum := fun k hk => G.nature_sum k (by by_contra h; simp [h] at hk)
  payoff ag z := G.payoff (owner G ag) z

omit [DecidableEq A] [Fintype A] [DecidableEq I] [DecidableEq H] in
theorem agentForm_player_none {k : H} : (agentForm G).player k = none ↔ G.player k = none := by
  simp only [agentForm]
  split_ifs with h <;> simp [h]

omit [DecidableEq A] [Fintype A] [DecidableEq I] [DecidableEq H] in
theorem agentForm_player_some {k : H} {ag : Agent G} :
    (agentForm G).player k = some ag ↔ k = ag.1 := by
  simp only [agentForm]
  split_ifs with h
  · simp only [false_iff]
    rintro rfl
    exact ag.2 h
  · constructor
    · intro he
      simp only [Option.some.injEq] at he
      rw [← he]
    · rintro rfl
      rfl

/-- **Appendix 9.B** (MWG, p. 299). The agent normal form of `Γ_E`. -/
def agentNF [Fintype H] : NormalForm (Agent G) (agentForm G).PureStrategy :=
  (agentForm G).toNormalForm

/-- The pure strategy of an agent playing action `a` at its information set. -/
def agentPure (ag : Agent G) (a : {a // a ∈ G.avail ag.1}) : (agentForm G).PureStrategy ag :=
  fun k => ⟨a.1, by
    have : k.1 = ag.1 := (agentForm_player_some G).1 k.2
    change a.1 ∈ G.avail k.1
    rw [this]
    exact a.2⟩

/-- The agent's own information set as one of its information sets in the agent form. -/
def agentSelf (ag : Agent G) : (agentForm G).InfoSetOf ag :=
  ⟨ag.1, (agentForm_player_some G).2 rfl⟩

/-- An agent's pure strategies are its actions. -/
def agentEquiv (ag : Agent G) : {a // a ∈ G.avail ag.1} ≃ (agentForm G).PureStrategy ag where
  toFun := agentPure G ag
  invFun s := ⟨(s (agentSelf G ag)).1, (s (agentSelf G ag)).2⟩
  left_inv a := rfl
  right_inv s := by
    funext k
    have hk : k = agentSelf G ag := Subtype.ext ((agentForm_player_some G).1 k.2)
    subst hk
    rfl

/-- The move probabilities of agent `ag` given its mixed strategy `σ ag`. -/
def agentBeh (σ : (ag : Agent G) → (agentForm G).PureStrategy ag → ℝ) (ag : Agent G) :
    H → A → ℝ :=
  fun _ a => if ha : a ∈ G.avail ag.1 then σ ag (agentPure G ag ⟨a, ha⟩) else 0

/-- The behaviour profile of `Γ_E` given by a mixed profile of the agent normal form. -/
def agentProfile (σ : (ag : Agent G) → (agentForm G).PureStrategy ag → ℝ) : I → H → A → ℝ :=
  fun _ k a => if h : G.player k = none then 0 else agentBeh G σ ⟨k, h⟩ k a

omit [Fintype A] [DecidableEq I] [DecidableEq H] in
theorem assemble_agentProfile (σ : (ag : Agent G) → (agentForm G).PureStrategy ag → ℝ) :
    G.assemble (agentProfile G σ) = (agentForm G).assemble (agentBeh G σ) := by
  funext k
  cases hk : G.player k with
  | none =>
    rw [G.assemble_of_none _ hk, (agentForm G).assemble_of_none _
      ((agentForm_player_none G).2 hk)]
    rfl
  | some i =>
    have hne : G.player k ≠ none := by rw [hk]; simp
    rw [G.assemble_of_some _ hk, (agentForm G).assemble_of_some _
      ((agentForm_player_some G (ag := ⟨k, hne⟩)).2 rfl)]
    funext a
    simp [agentProfile, hne]

omit [Fintype A] [DecidableEq I] [DecidableEq H] in
/-- The moves of `agentProfile G σ` at agent `ag`'s information set. -/
theorem assemble_agentProfile_apply (σ : (ag : Agent G) → (agentForm G).PureStrategy ag → ℝ)
    (ag : Agent G) (a : A) :
    G.assemble (agentProfile G σ) ag.1 a =
      if ha : a ∈ G.avail ag.1 then σ ag (agentPure G ag ⟨a, ha⟩) else 0 := by
  rw [assemble_agentProfile, (agentForm G).assemble_of_some _
    ((agentForm_player_some G (ag := ag)).2 rfl)]
  rfl

omit [Fintype A] [DecidableEq I] in
/-- A mixed profile of the agent normal form gives a behaviour profile of `Γ_E`. -/
theorem isBehaviorProfile_agentProfile [Fintype H]
    {σ : (ag : Agent G) → (agentForm G).PureStrategy ag → ℝ}
    (hσ : ∀ ag, IsMixedStrategy (σ ag)) : IsBehaviorProfile G (agentProfile G σ) := by
  intro i k hk
  have hne : G.player k ≠ none := by rw [hk]; simp
  set ag : Agent G := ⟨k, hne⟩
  have happ := assemble_agentProfile_apply G σ ag
  rw [G.assemble_of_some _ hk] at happ
  refine ⟨fun a => ?_, fun a ha => ?_, ?_⟩
  · rw [happ]
    split_ifs
    · exact (hσ ag).1 _
    · exact le_rfl
  · rw [happ]
    split_ifs with h
    · exact absurd h ha
    · rfl
  · rw [Finset.sum_congr rfl fun a _ => happ a, ← Finset.sum_coe_sort]
    simp only [Finset.coe_mem, ↓reduceDIte]
    have := Equiv.sum_comp (agentEquiv G ag) (σ ag)
    rw [← (hσ ag).2, ← this]
    rfl

omit [Fintype A] [DecidableEq A] [DecidableEq I] [DecidableEq H] in
/-- The agent form has no absent-mindedness when `Γ_E` has none. -/
theorem agentForm_noAbsentMindedness (hNA : G.NoAbsentMindedness) :
    (agentForm G).NoAbsentMindedness := hNA

omit [DecidableEq A] [Fintype A] [DecidableEq H] [DecidableEq I] in
/-- Reach probabilities in the agent form are those of `Γ_E`. -/
theorem reach_agentForm (f : H → A → ℝ) (z : List A) : (agentForm G).reach f z = G.reach f z := by
  induction z with
  | nil => rfl
  | cons a z ih => rw [reach_cons, reach_cons, ih]; rfl

omit [DecidableEq I] in
/-- **Appendix 9.B** (MWG, p. 299). Agent `ag`'s payoff in the agent normal form at the mixed
profile `σ` is the expected payoff of its owner in `Γ_E` under the behaviour profile given by
`σ`. -/
theorem agentNF_mixedPayoff [Fintype H] (hNA : G.NoAbsentMindedness)
    {σ : (ag : Agent G) → (agentForm G).PureStrategy ag → ℝ}
    (hσ : ∀ ag, IsMixedStrategy (σ ag)) (ag : Agent G) :
    (agentNF G).mixedPayoff σ ag = cont G (G.assemble (agentProfile G σ)) [] (owner G ag) := by
  have hmix : ∀ ag', σ ag' = (agentForm G).mixedOfBehavior (i := ag') (agentBeh G σ ag') := by
    intro ag'
    funext s
    unfold mixedOfBehavior
    rw [Fintype.prod_eq_single (agentSelf G ag') fun k hk =>
      absurd (Subtype.ext ((agentForm_player_some G).1 k.2) : k = agentSelf G ag') hk]
    have : s = agentPure G ag' ⟨(s (agentSelf G ag')).1, (s (agentSelf G ag')).2⟩ :=
      ((agentEquiv G ag').right_inv s).symm
    simp only [agentBeh]
    split_ifs with hm
    · conv_lhs => rw [this]
    · exact absurd (s (agentSelf G ag')).2 hm
  have hbeh : ∀ ag', (agentForm G).IsBehaviorStrategy ag' (agentBeh G σ ag') := by
    intro ag' k hk
    have hk' : k = ag'.1 := (agentForm_player_some G).1 hk
    subst hk'
    have h := isBehaviorProfile_agentProfile G hσ (owner G ag') ag'.1 (player_owner G ag')
    have happ := assemble_agentProfile_apply G σ ag'
    rw [G.assemble_of_some _ (player_owner G ag')] at happ
    refine ⟨fun a => ?_, fun a ha => ?_, ?_⟩
    · have := h.1 a
      rw [happ] at this
      exact this
    · have := h.2.1 a ha
      rw [happ] at this
      exact this
    · have := h.2.2
      rw [Finset.sum_congr rfl fun a _ => happ a] at this
      exact this
  rw [agentNF, mixedPayoff_toNormalForm, cont_nil]
  refine Finset.sum_congr rfl fun z hz => ?_
  have hzn : z ∈ G.nodes := ((mem_terminals G).1 hz).1
  rw [mixedOutcome_factor]
  have hw : ∀ ag', (agentForm G).mixedWeight (σ ag') z =
      (agentForm G).weight (some ag') (agentBeh G σ ag') z := by
    intro ag'
    rw [hmix ag']
    exact (agentForm G).mixedWeight_mixedOfBehavior (agentForm_noAbsentMindedness G hNA)
      (hbeh ag') z hzn
  simp_rw [hw]
  rw [← (agentForm G).reach_assemble_factor, ← assemble_agentProfile, reach_agentForm]
  rfl

/-- **Definition 9.BB.1** (MWG, p. 299). A behaviour profile of `Γ_E` is an extensive form
trembling-hand perfect Nash equilibrium if it is (the behaviour profile of) a normal form
trembling-hand perfect Nash equilibrium of the agent normal form. -/
def IsEFTHP [Fintype H] (F : I → H → A → ℝ) : Prop :=
  IsBehaviorProfile G F ∧ ∃ σ, IsTHP (agentNF G) σ ∧
    ∀ k, G.player k ≠ none → G.assemble F k = G.assemble (agentProfile G σ) k

omit [DecidableEq A] [Fintype A] [DecidableEq I] [DecidableEq H] in
/-- Every agent has a pure strategy. -/
theorem agent_nonempty (ag : Agent G) : Nonempty ((agentForm G).PureStrategy ag) := by
  obtain ⟨a, ha⟩ := G.avail_nonempty ag.1
  exact ⟨agentPure G ag ⟨a, ha⟩⟩

omit [DecidableEq I] in
/-- **Appendix 9.B** (MWG, p. 299; Selten 1975). Every finite game in extensive form has an
extensive form trembling-hand perfect Nash equilibrium. -/
theorem exists_isEFTHP [Fintype H] : ∃ F, IsEFTHP G F := by
  have := agent_nonempty G
  obtain ⟨σ, hσ⟩ := exercise_8_F_3 (agentNF G)
  have hmix : ∀ ag, IsMixedStrategy (σ ag) := fun ag => hσ.1.1 ag
  exact ⟨agentProfile G σ, isBehaviorProfile_agentProfile G hmix, σ, hσ, fun _ _ => rfl⟩

end MWG.DynamicGames

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The one-shot deviation principle for consistent assessments

MWG, Section 9.C and Appendix B (pp. 290-292 and 300). To verify sequential rationality
(Definition 9.C.2) it suffices, for a consistent assessment in a game with perfect recall, to
rule out deviations at a single information set followed by the equilibrium continuation:
`oneShot_consistent`. This is the step behind MWG's claim (p. 300) that every extensive form
trembling-hand perfect equilibrium is a sequential equilibrium.

* `NatureFullSupport`: nature puts positive probability on every available move (Kreps and
  Wilson's standing assumption; then totally mixed profiles reach every node,
  `reach_pos_of_totallyMixed`).
* `entry_cons_closed`, `entry_cons_unique`: with perfect recall, player `i`'s first nodes after
  the move `b` at her information set `k` form whole information sets, each node being reached
  from a unique node of `k`.
* `propagate_consistent`: consistent beliefs at a later information set of player `i` are
  derived from the beliefs at `k` by Bayes' rule (the limit of the Bayes relation along the
  totally mixed sequence).
* `oneShot_consistent`: with perfect recall, nature's full support and a consistent assessment,
  if no player can gain by changing her move at one information set (keeping the rest of the
  profile), then the profile is sequentially rational.
-/

namespace MWG.DynamicGames

open MWG.NoncooperativeGames MWG.NoncooperativeGames.ExtensiveForm Filter Topology

variable {I A H : Type*} (G : ExtensiveForm I A H) [DecidableEq A] [Fintype A] [DecidableEq I]
  [DecidableEq H]

/-- Nature puts positive probability on every available move. -/
def NatureFullSupport : Prop :=
  ∀ k, G.player k = none → ∀ a ∈ G.avail k, 0 < G.natureProb k a

omit [DecidableEq A] [Fintype A] [DecidableEq I] [DecidableEq H] in
/-- Under a totally mixed profile, with nature's full support, every node is reached with
positive probability. -/
theorem reach_pos_of_totallyMixed (hN : NatureFullSupport G) {F : I → H → A → ℝ}
    (hF : IsTotallyMixedB G F) {x : List A} (hx : x ∈ G.nodes) :
    0 < G.reach (G.assemble F) x := by
  induction x with
  | nil => simp
  | cons a x ih =>
    rw [reach_cons]
    have ha : a ∈ G.avail (G.info x) := G.mem_avail_of_cons_mem hx
    refine mul_pos (ih (G.mem_of_cons_mem hx)) ?_
    cases hk : G.player (G.info x) with
    | none => rw [G.assemble_of_none _ hk]; exact hN _ hk a ha
    | some j => rw [G.assemble_of_some _ hk]; exact hF.2 j _ hk a ha

omit [DecidableEq I] in
/-- Under a totally mixed profile, with nature's full support, every information set is
reached with positive probability. -/
theorem probInfo_pos (hN : NatureFullSupport G) {F : I → H → A → ℝ}
    (hF : IsTotallyMixedB G F) (k : H) : 0 < probInfo G (G.assemble F) k := by
  obtain ⟨x, hx⟩ := (G.infoSet_partition).1 k
  exact lt_of_lt_of_le (reach_pos_of_totallyMixed G hN hF ((mem_infoSet G).1 hx).1.1)
    (reach_le_probInfo G (assemble_nonneg G hF.1) hx)

omit [DecidableEq I] in
/-- Bayes beliefs at a reached information set sum to one. -/
theorem sum_bayesBelief {f : H → A → ℝ} {k : H} (hk : 0 < probInfo G f k) :
    ∑ x ∈ G.infoSet k, bayesBelief G f x = 1 := by
  rw [Finset.sum_congr rfl fun x hx => by rw [bayesBelief, ((mem_infoSet G).1 hx).2],
    ← Finset.sum_div]
  exact div_self hk.ne'

/-- The set of first nodes of player `i` after the move `b` at node `x`. -/
abbrev iEntry (i : I) (b : A) (x : List A) : Finset (List A) :=
  entryNodes G (fun k => G.player k = some i) (b :: x)

omit [DecidableEq I] in
/-- With perfect recall, a node of `k` preceding a node `x'` is unique. -/
theorem entry_cons_unique (hNA : G.NoAbsentMindedness) {k : H} {x x₁ x' : List A} {b b₁ : A}
    (hx : x ∈ G.infoSet k) (hx₁ : x₁ ∈ G.infoSet k) (h : b :: x <:+ x')
    (h₁ : b₁ :: x₁ <:+ x') : x = x₁ := by
  rw [mem_infoSet] at hx hx₁
  have hs : x <:+ x' := (List.suffix_cons b x).trans h
  have hs₁ : x₁ <:+ x' := (List.suffix_cons b₁ x₁).trans h₁
  rcases le_total x.length x₁.length with hl | hl
  · exact eq_of_absentMinded G hNA hx.1 hx₁.1 (by rw [hx.2, hx₁.2])
      (List.suffix_of_suffix_length_le hs hs₁ hl)
  · exact (eq_of_absentMinded G hNA hx₁.1 hx.1 (by rw [hx.2, hx₁.2])
      (List.suffix_of_suffix_length_le hs₁ hs hl)).symm

/-- **Perfect recall closure.** If `x'` is a first node of player `i` after the move `b` at a
node of her information set `k`, then so is every node of `H(x')`. -/
theorem entry_cons_closed (hPR : G.PerfectRecall) {i : I} {k : H} (hk : G.player k = some i)
    {b : A} {x x' x'' : List A} (hx : x ∈ G.infoSet k) (hx' : x' ∈ iEntry G i b x)
    (hx'' : G.IsDecision x'') (he : G.info x'' = G.info x') :
    ∃ x₁ ∈ G.infoSet k, x'' ∈ iEntry G i b x₁ := by
  rw [mem_infoSet] at hx
  rw [mem_entryNodes] at hx'
  obtain ⟨hdx', hbx', hDx', hmin⟩ := hx'
  obtain ⟨x₁, hx₁, hbx₁, hinfo⟩ := recall_pred G (hPR.2 i) hdx' hx'' hDx' he.symm hbx'
    (by rw [hx.2]; exact hk)
  refine ⟨x₁, (mem_infoSet G).2 ⟨hx₁, by rw [hinfo, hx.2]⟩, ?_⟩
  rw [mem_entryNodes]
  refine ⟨hx'', hbx₁, by rw [he]; exact hDx', fun w hw hbw hwx hne hDw => ?_⟩
  obtain ⟨a', ha'⟩ := exists_cons_suffix hwx hne
  obtain ⟨w', hw', haw', hinfo'⟩ := recall_pred G (hPR.2 i) hx'' hdx' (by rw [he]; exact hDx')
    he ha' hDw
  have hw'x' : w' <:+ x' := (List.suffix_cons a' w').trans haw'
  have hw'ne : w' ≠ x' := by
    rintro rfl
    have := haw'.length_le
    simp at this
  -- `w'` and `b :: x` are both predecessors of `x'`
  rcases le_or_gt (b :: x).length w'.length with hl | hl
  · exact hmin w' hw' (List.suffix_of_suffix_length_le hbx' hw'x' hl) hw'x' hw'ne
      (by rw [hinfo']; exact hDw)
  · have hw'x0 : w' <:+ x := by
      have hw'x : w' <:+ b :: x := List.suffix_of_suffix_length_le hw'x' hbx' hl.le
      rcases List.suffix_cons_iff.1 hw'x with h | h
      · rw [h] at hl
        exact absurd hl (lt_irrefl _)
      · exact h
    by_cases hwx0 : w' = x
    · subst hwx0
      -- `w` lies strictly after `x₁` in `k`: absent-mindedness
      have : x₁ = w := eq_of_absentMinded G hPR.1 hx₁ hw (by rw [hinfo, ← hinfo', hx.2])
        ((List.suffix_cons b x₁).trans hbw)
      subst this
      have := hbw.length_le
      simp at this
    · obtain ⟨a'', ha''⟩ := exists_cons_suffix hw'x0 hwx0
      obtain ⟨ŵ, hŵ, haŵ, hinfoŵ⟩ := recall_pred G (hPR.2 i) hx.1 hx₁
        (by rw [hx.2]; exact hk) (by rw [hinfo, hx.2]) ha'' (by rw [hinfo']; exact hDw)
      have hŵw : ŵ <:+ w :=
        ((List.suffix_cons a'' ŵ).trans haŵ).trans ((List.suffix_cons b x₁).trans hbw)
      have := eq_of_absentMinded G hPR.1 hŵ hw (by rw [hinfoŵ, hinfo']) hŵw
      subst this
      have h1 := haŵ.length_le
      have h2 := hbw.length_le
      simp at h1 h2
      omega

/-- The weight that the beliefs `μ` at player `i`'s information set `k`, followed by the move
`b` and then by the moves `f`, put on a first later node `x'` of player `i`. -/
noncomputable def propW (f : H → A → ℝ) (μ : List A → ℝ) (i : I) (k : H) (b : A)
    (x' : List A) : ℝ :=
  ∑ x ∈ G.infoSet k, if x' ∈ iEntry G i b x then μ x * reachFrom G f (b :: x) x' else 0

/-- **Bayes propagation for consistent beliefs.** With perfect recall and nature's full
support, for a consistent assessment the weight `propW` that the beliefs at `k` and the move
`b` put on a later information set `k'` of the same player is proportional to the beliefs at
`k'`; and when it is not zero, every node of `k'` follows a node of `k` by the move `b`. -/
theorem propagate_consistent (hPR : G.PerfectRecall) (hN : NatureFullSupport G)
    {F : I → H → A → ℝ} {μ : List A → ℝ} (hc : IsConsistent G F μ) {i : I} {k : H}
    (hk : G.player k = some i) {b : A} (hb : b ∈ G.avail k) (k' : H) :
    ∃ c, 0 ≤ c ∧ (∀ x' ∈ G.infoSet k', propW G (G.assemble F) μ i k b x' = c * μ x') ∧
      (c ≠ 0 → ∀ x'' ∈ G.infoSet k', ∃ x ∈ G.infoSet k, b :: x <:+ x'') := by
  obtain ⟨Fs, hFs, hlim, hbel⟩ := hc
  have hFnn : ∀ k a, 0 ≤ G.assemble F k a := fun k a =>
    ge_of_tendsto' (tendsto_assemble G hlim k a) fun n => assemble_nonneg G (hFs n).1 k a
  have hμnn : ∀ x, G.IsDecision x → 0 ≤ μ x := fun x hx =>
    ge_of_tendsto' (hbel x hx) fun n => div_nonneg
      (G.reach_nonneg (assemble_nonneg G (hFs n).1) x)
      (Finset.sum_nonneg fun y _ => G.reach_nonneg (assemble_nonneg G (hFs n).1) y)
  by_cases hR : ∃ x' ∈ G.infoSet k', ∃ x ∈ G.infoSet k, x' ∈ iEntry G i b x
  · obtain ⟨x'₀, hx'₀, x₀, hx₀, hE₀⟩ := hR
    have hall : ∀ x'' ∈ G.infoSet k', ∃ x ∈ G.infoSet k, x'' ∈ iEntry G i b x :=
      fun x'' hx'' => entry_cons_closed G hPR hk hx₀ hE₀ ((mem_infoSet G).1 hx'').1
        (by rw [((mem_infoSet G).1 hx'').2, ((mem_infoSet G).1 hx'₀).2])
    set fn : ℕ → H → A → ℝ := fun n => G.assemble (Fs n)
    have hP : ∀ n k, 0 < probInfo G (fn n) k := fun n k => probInfo_pos G hN (hFs n) k
    have hfb : ∀ n, 0 < fn n k b := fun n => by
      simp only [fn]
      rw [G.assemble_of_some _ hk]
      exact (hFs n).2 i k hk b hb
    -- the exact Bayes relation along the sequence
    have hWn : ∀ n, ∀ x' ∈ G.infoSet k', propW G (fn n) (bayesBelief G (fn n)) i k b x' =
        probInfo G (fn n) k' / (probInfo G (fn n) k * fn n k b) * bayesBelief G (fn n) x' := by
      intro n x' hx'
      obtain ⟨x₁, hx₁, hE₁⟩ := hall x' hx'
      unfold propW
      rw [Finset.sum_eq_single x₁ (fun x hx hne => by
        split_ifs with h
        · exact absurd (entry_cons_unique G hPR.1 hx hx₁ ((mem_entryNodes G).1 h).2.1
            ((mem_entryNodes G).1 hE₁).2.1) hne
        · rfl) (fun h => absurd hx₁ h)]
      simp only [hE₁, ↓reduceIte]
      obtain ⟨hx₁d, hx₁k⟩ := (mem_infoSet G).1 hx₁
      have hbx' := ((mem_entryNodes G).1 hE₁).2.1
      have hreach : G.reach (fn n) x' = G.reach (fn n) x₁ * fn n k b *
          reachFrom G (fn n) (b :: x₁) x' := by
        rw [reach_eq_mul_reachFrom G _ ((List.suffix_cons b x₁).trans hbx'),
          reachFrom_trans G _ (List.suffix_cons b x₁) hbx', reachFrom_cons_self, hx₁k]
        ring
      unfold bayesBelief
      rw [hx₁k, ((mem_infoSet G).1 hx').2, hreach]
      have h1 := (hP n k).ne'
      have h2 := (hP n k').ne'
      have h3 := (hfb n).ne'
      field_simp
    have hconv : ∀ x', Tendsto (fun n => propW G (fn n) (bayesBelief G (fn n)) i k b x') atTop
        (𝓝 (propW G (G.assemble F) μ i k b x')) := by
      intro x'
      unfold propW
      refine tendsto_finsetSum _ fun x hx => ?_
      by_cases h : x' ∈ iEntry G i b x
      · simp only [h, ↓reduceIte]
        exact (hbel x ((mem_infoSet G).1 hx).1).mul (tendsto_reachFrom G hlim _ _)
      · simp only [h, ↓reduceIte]
        exact tendsto_const_nhds
    set c := ∑ x' ∈ G.infoSet k', propW G (G.assemble F) μ i k b x'
    have hsum : ∀ n, ∑ x' ∈ G.infoSet k', propW G (fn n) (bayesBelief G (fn n)) i k b x' =
        probInfo G (fn n) k' / (probInfo G (fn n) k * fn n k b) := by
      intro n
      rw [Finset.sum_congr rfl (hWn n), ← Finset.mul_sum, sum_bayesBelief G (hP n k'), mul_one]
    have hκ : Tendsto (fun n => probInfo G (fn n) k' / (probInfo G (fn n) k * fn n k b)) atTop
        (𝓝 c) := (tendsto_finsetSum _ fun x' _ => hconv x').congr hsum
    have hWnn : ∀ x', 0 ≤ propW G (G.assemble F) μ i k b x' := fun x' =>
      Finset.sum_nonneg fun x hx => by
        split_ifs
        · exact mul_nonneg (hμnn x ((mem_infoSet G).1 hx).1) (reachFrom_nonneg G hFnn _ _)
        · exact le_rfl
    refine ⟨c, Finset.sum_nonneg fun x' _ => hWnn x', fun x' hx' => ?_, fun _ x'' hx'' => ?_⟩
    · exact tendsto_nhds_unique (hconv x')
        ((hκ.mul (hbel x' ((mem_infoSet G).1 hx').1)).congr fun n => (hWn n x' hx').symm)
    · obtain ⟨x, hx, hE⟩ := hall x'' hx''
      exact ⟨x, hx, ((mem_entryNodes G).1 hE).2.1⟩
  · push Not at hR
    refine ⟨0, le_rfl, fun x' hx' => ?_, fun h => absurd rfl h⟩
    rw [zero_mul]
    exact Finset.sum_eq_zero fun x hx => by simp [hR x' hx' x hx]

/-- **One-shot deviation principle for consistent assessments** (MWG, pp. 290 and 300). In a
game with perfect recall in which nature's moves have full support, let `(σ, μ)` be a
consistent assessment such that at each information set `k` of player `i` no move `b` followed
by `σ` gives `i` a higher expected payoff under `μ` than `σ` itself. Then `σ` is sequentially
rational for player `i`: no deviation to any behaviour strategy raises `E[u_i | k, μ, ·]`. -/
theorem oneShot_consistent (hPR : G.PerfectRecall) (hN : NatureFullSupport G)
    {F : I → H → A → ℝ} {μ : List A → ℝ} (hc : IsConsistent G F μ) {i : I}
    (hone : ∀ k, G.player k = some i → ∀ b ∈ G.avail k,
      ∑ x ∈ G.infoSet k, μ x * cont G (G.assemble F) (b :: x) i ≤
        condPayoff G (G.assemble F) μ k i)
    {g : H → A → ℝ} (hg : G.IsBehaviorStrategy i g) {k : H} (hk : G.player k = some i) :
    condPayoff G (G.assemble (Function.update F i g)) μ k i ≤
      condPayoff G (G.assemble F) μ k i := by
  set f := G.assemble F
  set f' := G.assemble (Function.update F i g)
  have hoff : ∀ k, ¬ (fun k => G.player k = some i) k → f k = f' k := fun k hk =>
    assemble_update_eq_off G F i g k hk
  set Xi := G.decisionNodes.filter fun x => G.player (G.info x) = some i
  set Dm := G.nodes.sup List.length
  suffices key : ∀ n, ∀ k, G.player k = some i → (∀ x ∈ G.infoSet k, Dm - x.length ≤ n) →
      condPayoff G f' μ k i ≤ condPayoff G f μ k i from
    key Dm k hk fun x _ => Nat.sub_le _ _
  intro n
  induction n with
  | zero =>
    intro k _ hd
    obtain ⟨x, hx⟩ := (G.infoSet_partition).1 k
    obtain ⟨⟨_, b, hb⟩, -⟩ := (mem_infoSet G).1 hx
    have h1 := G.length_le_sup hb
    have h2 := hd x hx
    simp only [List.length_cons] at h1
    omega
  | succ n ih =>
    intro k hk hd
    -- the continuation after the first move, decomposed at the next nodes of player `i`
    have hT : ∀ b ∈ G.avail k, 0 ≤ ∑ x ∈ G.infoSet k, μ x * ∑ x' ∈ iEntry G i b x,
        reachFrom G f (b :: x) x' * (cont G f x' i - cont G f' x' i) := by
      intro b hb
      have hsub : ∀ x, iEntry G i b x ⊆ Xi := fun x x' hx' => by
        rw [mem_entryNodes] at hx'
        simp only [Xi, Finset.mem_filter, mem_decisionNodes]
        exact ⟨hx'.1, hx'.2.2.1⟩
      have h1 : ∀ x ∈ G.infoSet k, μ x * ∑ x' ∈ iEntry G i b x,
          reachFrom G f (b :: x) x' * (cont G f x' i - cont G f' x' i) =
          ∑ x' ∈ Xi, (if x' ∈ iEntry G i b x then μ x * reachFrom G f (b :: x) x' else 0) *
            (cont G f x' i - cont G f' x' i) := by
        intro x _
        rw [Finset.mul_sum]
        rw [Finset.sum_congr rfl fun x' hx' => by
          rw [show μ x * (reachFrom G f (b :: x) x' * (cont G f x' i - cont G f' x' i)) =
            (if x' ∈ iEntry G i b x then μ x * reachFrom G f (b :: x) x' else 0) *
            (cont G f x' i - cont G f' x' i) by simp only [hx', ↓reduceIte]; ring]]
        exact Finset.sum_subset (hsub x) fun x' _ hx' => by simp [hx']
      rw [Finset.sum_congr rfl h1, Finset.sum_comm]
      simp_rw [← Finset.sum_mul]
      change 0 ≤ ∑ x' ∈ Xi, propW G f μ i k b x' * (cont G f x' i - cont G f' x' i)
      rw [sum_eq_sum_infoSet G (E := Xi)
        (fun x hx => (mem_decisionNodes G).1 (Finset.mem_filter.1 hx).1)
        (fun x hx x' hx' he => by
          simp only [Xi, Finset.mem_filter, mem_decisionNodes] at hx ⊢
          exact ⟨hx', by rw [he]; exact hx.2⟩)]
      refine Finset.sum_nonneg fun k' hk' => ?_
      obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.1 hk'
      have hk'i : G.player (G.info x₀) = some i := (Finset.mem_filter.1 hx₀).2
      obtain ⟨c, hc0, hcμ, hdeep⟩ := propagate_consistent G hPR hN hc hk hb (G.info x₀)
      rw [Finset.sum_congr rfl fun x' hx' => by rw [hcμ x' hx']]
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum]
      by_cases hc' : c = 0
      · rw [hc', zero_mul]
      · refine mul_nonneg hc0 ?_
        have hdepth : ∀ x'' ∈ G.infoSet (G.info x₀), Dm - x''.length ≤ n := by
          intro x'' hx''
          obtain ⟨x, hx, hbx⟩ := hdeep hc' x'' hx''
          have := hd x hx
          have := hbx.length_le
          simp only [List.length_cons] at this
          omega
        have := ih _ hk'i hdepth
        unfold condPayoff at this
        simp_rw [mul_sub]
        rw [Finset.sum_sub_distrib]
        linarith
    have hcf' : ∀ x ∈ G.infoSet k, cont G f' x i = ∑ b ∈ G.avail k, g k b *
        (cont G f (b :: x) i - ∑ x' ∈ iEntry G i b x,
          reachFrom G f (b :: x) x' * (cont G f x' i - cont G f' x' i)) := by
      intro x hx
      obtain ⟨hxd, hxk⟩ := (mem_infoSet G).1 hx
      have hf'k : f' k = g k := assemble_update_self G F g hk
      rw [cont_decision G f' hxd, hxk, hf'k]
      refine Finset.sum_congr rfl fun b hb => ?_
      have hbx : b :: x ∈ G.nodes := G.cons_mem_of_mem_avail hxd (by rw [hxk]; exact hb)
      have := cont_sub_eq_sum_entry G (fun k => G.player k = some i) hoff hbx i
      rw [← this]
      ring
    have hlhs : condPayoff G f' μ k i = ∑ b ∈ G.avail k, g k b *
        (∑ x ∈ G.infoSet k, μ x * cont G f (b :: x) i - ∑ x ∈ G.infoSet k, μ x *
          ∑ x' ∈ iEntry G i b x, reachFrom G f (b :: x) x' * (cont G f x' i - cont G f' x' i)) := by
      unfold condPayoff
      rw [Finset.sum_congr rfl fun x hx => by rw [hcf' x hx, Finset.mul_sum], Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [hlhs]
    calc ∑ b ∈ G.avail k, g k b * (∑ x ∈ G.infoSet k, μ x * cont G f (b :: x) i -
          ∑ x ∈ G.infoSet k, μ x * ∑ x' ∈ iEntry G i b x,
            reachFrom G f (b :: x) x' * (cont G f x' i - cont G f' x' i))
        ≤ ∑ b ∈ G.avail k, g k b * condPayoff G f μ k i :=
          Finset.sum_le_sum fun b hb => mul_le_mul_of_nonneg_left
            (by linarith [hT b hb, hone k hk b hb]) ((hg k hk).1 b)
      _ = condPayoff G f μ k i := by rw [← Finset.sum_mul, (hg k hk).2.2, one_mul]

end MWG.DynamicGames

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Extensive form trembling-hand perfection implies sequential equilibrium; existence

MWG, Appendix B of Chapter 9, p. 300: "every extensive form trembling-hand perfect Nash
equilibrium is a sequential equilibrium". Since every finite game has an extensive form
trembling-hand perfect equilibrium (Selten), sequential equilibria exist, and with
Proposition 9.C.2 so do subgame perfect Nash equilibria (Exercise 9.B.8).

* `isSequentialEq_of_isEFTHP`: in a game with perfect recall in which nature's moves have full
  support, the strategies of an extensive form trembling-hand perfect equilibrium, with beliefs
  that are a limit of the Bayes beliefs along (a subsequence of) its trembling sequence, form a
  sequential equilibrium. In the perturbed agent games each agent's equilibrium move is optimal
  given the Bayes beliefs (`agent_best_iff`); in the limit no move at a single information set
  is profitable, and the one-shot deviation principle for consistent assessments
  (`oneShot_consistent`) gives sequential rationality.
* `exists_isSequentialEq` (existence of sequential equilibrium, Kreps and Wilson 1982),
  `isSPNE_of_isEFTHP` (every EFTHP is subgame perfect, p. 300) and `exercise_9_B_8` (every
  finite game, here with perfect recall and full-support moves of nature, has a mixed strategy
  SPNE).
-/

namespace MWG.DynamicGames

open MWG.NoncooperativeGames MWG.NoncooperativeGames.ExtensiveForm MWG.SimultaneousMoveGames
  Filter Topology

variable {I A H : Type*} (G : ExtensiveForm I A H) [DecidableEq A] [Fintype A] [DecidableEq I]
  [DecidableEq H]

omit [DecidableEq I] [DecidableEq H] in
/-- Continuation payoffs depend continuously on the profile. -/
theorem tendsto_cont {Fs : ℕ → I → H → A → ℝ} {F : I → H → A → ℝ}
    (h : Tendsto Fs atTop (𝓝 F)) (x : List A) (i : I) :
    Tendsto (fun n => cont G (G.assemble (Fs n)) x i) atTop
      (𝓝 (cont G (G.assemble F) x i)) := by
  unfold cont
  exact tendsto_finsetSum _ fun z _ => (tendsto_reachFrom G h x z).mul tendsto_const_nhds

omit [DecidableEq I] in
/-- Without absent-mindedness, the entry nodes of the single information set `k` are its
nodes. -/
theorem entryNodes_single (hNA : G.NoAbsentMindedness) (k : H) :
    entryNodes G (fun k' => k' = k) [] = G.infoSet k := by
  ext x
  rw [mem_entryNodes, mem_infoSet]
  constructor
  · rintro ⟨hx, -, hk, -⟩
    exact ⟨hx, hk⟩
  · rintro ⟨hx, hk⟩
    refine ⟨hx, List.nil_suffix, hk, fun w hw _ hwx hne hwk => hne ?_⟩
    exact eq_of_absentMinded G hNA hw hx (by rw [hwk, hk]) hwx

omit [DecidableEq I] in
/-- Without absent-mindedness, replacing the move at `H(x)` by a sure move `c` makes the
continuation from `x` that from `c :: x`. -/
theorem cont_update_dirac (hNA : G.NoAbsentMindedness) (f : H → A → ℝ) {x : List A}
    (hx : G.IsDecision x) {c : A} (hc : c ∈ G.avail (G.info x)) (i : I) :
    cont G (Function.update f (G.info x) (dirac c)) x i = cont G f (c :: x) i := by
  rw [cont_decision _ _ hx, Function.update_self]
  simp only [dirac, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq' (G.avail (G.info x))]
  simp only [hc, ↓reduceIte]
  refine cont_congr G (fun y hy hcy => ?_) i
  have hne : G.info y ≠ G.info x := fun he => by
    have := eq_of_absentMinded G hNA hx hy he.symm ((List.suffix_cons c x).trans hcy)
    subst this
    have := hcy.length_le
    simp at this
  rw [Function.update_of_ne hne]

omit [DecidableEq I] in
/-- **Agent best responses and beliefs.** With sure moves `a, b` at information set `k`, the
payoff difference of the mover is `∑_{x ∈ k} P(x) (cont(a :: x) − cont(b :: x))`. -/
theorem cont_update_dirac_sub (hNA : G.NoAbsentMindedness) (f : H → A → ℝ) (k : H) {a b : A}
    (ha : a ∈ G.avail k) (hb : b ∈ G.avail k) (i : I) :
    cont G (Function.update f k (dirac a)) [] i - cont G (Function.update f k (dirac b)) [] i =
      ∑ x ∈ G.infoSet k, G.reach f x * (cont G f (a :: x) i - cont G f (b :: x) i) := by
  have hoff : ∀ c, ∀ k', ¬ (fun k'' => k'' = k) k' →
      f k' = Function.update f k (dirac c) k' := fun c k' hk' => by
    rw [Function.update_of_ne hk']
  have h1 := cont_sub_eq_sum_entry G (fun k' => k' = k) (hoff a) G.nil_mem i
  have h2 := cont_sub_eq_sum_entry G (fun k' => k' = k) (hoff b) G.nil_mem i
  rw [entryNodes_single G hNA] at h1 h2
  have hc : ∀ c ∈ G.avail k, ∀ x ∈ G.infoSet k,
      cont G (Function.update f k (dirac c)) x i = cont G f (c :: x) i := by
    intro c hc x hx
    obtain ⟨hxd, hxk⟩ := (mem_infoSet G).1 hx
    rw [← hxk]
    exact cont_update_dirac G hNA f hxd (by rw [hxk]; exact hc) i
  rw [Finset.sum_congr rfl fun x hx => by rw [hc a ha x hx, reachFrom_nil]] at h1
  rw [Finset.sum_congr rfl fun x hx => by rw [hc b hb x hx, reachFrom_nil]] at h2
  have : cont G (Function.update f k (dirac a)) [] i -
      cont G (Function.update f k (dirac b)) [] i =
      (cont G f [] i - cont G (Function.update f k (dirac b)) [] i) -
        (cont G f [] i - cont G (Function.update f k (dirac a)) [] i) := by ring
  rw [this, h1, h2, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun x _ => by ring

omit [Fintype A] [DecidableEq I] in
/-- The agent profile with agent `ag` switched to the sure move `c`. -/
theorem assemble_agentProfile_update [Fintype H]
    (σ : (ag : Agent G) → (agentForm G).PureStrategy ag → ℝ) (ag : Agent G) {c : A}
    (hc : c ∈ G.avail ag.1) :
    G.assemble (agentProfile G (Function.update σ ag (pureMixed (agentPure G ag ⟨c, hc⟩)))) =
      Function.update (G.assemble (agentProfile G σ)) ag.1 (dirac c) := by
  funext k a
  by_cases hk : k = ag.1
  · subst hk
    rw [Function.update_self, assemble_agentProfile_apply, dirac]
    simp only [Function.update_self, pureMixed]
    by_cases ha : a ∈ G.avail ag.1
    · simp only [ha, ↓reduceDIte]
      by_cases hac : a = c
      · subst hac
        simp
      · have hne : agentPure G ag ⟨a, ha⟩ ≠ agentPure G ag ⟨c, hc⟩ := fun h =>
          hac (congrArg Subtype.val ((agentEquiv G ag).injective h))
        simp [hne, hac]
    · have hac : a ≠ c := fun h => ha (h ▸ hc)
      simp [ha, hac]
  · rw [Function.update_of_ne hk]
    cases hp : G.player k with
    | none => rw [G.assemble_of_none _ hp, G.assemble_of_none _ hp]
    | some j =>
      have hne : G.player k ≠ none := by rw [hp]; simp
      have hag : (⟨k, hne⟩ : Agent G) ≠ ag := fun h => hk (congrArg Subtype.val h)
      rw [G.assemble_of_some _ hp, G.assemble_of_some _ hp]
      simp [agentProfile, hne, agentBeh, Function.update_of_ne hag]

/-- **Appendix 9.B** (MWG, p. 300). In a game with perfect recall in which nature's moves have
full support, every extensive form trembling-hand perfect Nash equilibrium is (the strategy
profile of) a sequential equilibrium. -/
theorem isSequentialEq_of_isEFTHP [Fintype H] (hPR : G.PerfectRecall)
    (hN : NatureFullSupport G) {F : I → H → A → ℝ} (hF : IsEFTHP G F) :
    ∃ μ, IsSequentialEq G F μ := by
  obtain ⟨hFb, σ, ⟨-, ε, σs, hε, hε0, hσs, hlim⟩, hFσ⟩ := hF
  have hmix : ∀ n ag, IsMixedStrategy (σs n ag) := fun n ag =>
    isMixedStrategy_of_mem_perturbedSet (hε n) ((hσs n).1 ag)
  -- the trembling sequence as behaviour profiles of `Γ_E`
  let Fs : ℕ → I → H → A → ℝ := fun n i k a =>
    if G.player k = some i then agentProfile G (σs n) i k a else F i k a
  have hasm : ∀ n, G.assemble (Fs n) = G.assemble (agentProfile G (σs n)) := by
    intro n
    funext k
    cases hp : G.player k with
    | none => rw [G.assemble_of_none _ hp, G.assemble_of_none _ hp]
    | some j =>
      rw [G.assemble_of_some _ hp, G.assemble_of_some _ hp]
      funext a
      simp [Fs, hp]
  have hTM : ∀ n, IsTotallyMixedB G (Fs n) := by
    intro n
    have hb := isBehaviorProfile_agentProfile G (hmix n)
    refine ⟨fun i k hk => ?_, fun i k hk a ha => ?_⟩
    · have := hb i k hk
      simp only [Fs, hk, ite_true]
      exact this
    · simp only [Fs, hk, ite_true]
      have hne : G.player k ≠ none := by rw [hk]; simp
      have := assemble_agentProfile_apply G (σs n) ⟨k, hne⟩ a
      rw [G.assemble_of_some _ hk] at this
      rw [this]
      simp only [ha, ↓reduceDIte]
      exact lt_of_lt_of_le ((hε n).1 _ _).1 (((hσs n).1 _).1 _)
  have hFsF : Tendsto Fs atTop (𝓝 F) := by
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun k => tendsto_pi_nhds.2 fun a => ?_
    by_cases hk : G.player k = some i
    · simp only [Fs, hk, ite_true]
      have hne : G.player k ≠ none := by rw [hk]; simp
      have h2 : F i k a = G.assemble (agentProfile G σ) k a := by
        have := congrFun (hFσ k hne) a
        rw [G.assemble_of_some _ hk] at this
        exact this
      have h1 : G.assemble (agentProfile G σ) k a = if ha : a ∈ G.avail k then
          σ ⟨k, hne⟩ (agentPure G ⟨k, hne⟩ ⟨a, ha⟩) else 0 :=
        assemble_agentProfile_apply G σ ⟨k, hne⟩ a
      rw [h2, h1]
      have happ : ∀ n, agentProfile G (σs n) i k a =
          if ha : a ∈ G.avail k then σs n ⟨k, hne⟩ (agentPure G ⟨k, hne⟩ ⟨a, ha⟩) else 0 := by
        intro n
        have := assemble_agentProfile_apply G (σs n) ⟨k, hne⟩ a
        rw [G.assemble_of_some _ hk] at this
        exact this
      simp only [happ]
      split_ifs with ha
      · exact tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hlim _) _
      · exact tendsto_const_nhds
    · simp only [Fs, hk, ite_false]
      exact tendsto_const_nhds
  -- a convergent subsequence of the Bayes beliefs
  set D := G.decisionNodes
  set v : ℕ → D → ℝ := fun n x => bayesBelief G (G.assemble (Fs n)) x.1
  set K : Set (D → ℝ) := Set.pi Set.univ fun _ => Set.Icc 0 1
  have hK : IsCompact K := isCompact_univ_pi fun _ => isCompact_Icc
  have hP : ∀ n k, 0 < probInfo G (G.assemble (Fs n)) k := fun n k =>
    probInfo_pos G hN (hTM n) k
  have hvK : ∀ n, v n ∈ K := by
    intro n x _
    have hx := (mem_decisionNodes G).1 x.2
    have hxk : x.1 ∈ G.infoSet (G.info x.1) := (mem_infoSet G).2 ⟨hx, rfl⟩
    have hf := assemble_nonneg G (hTM n).1
    exact ⟨div_nonneg (G.reach_nonneg hf _) (hP n _).le,
      (div_le_one (hP n _)).2 (reach_le_probInfo G hf hxk)⟩
  obtain ⟨μv, hμK, φ, hφ, hμlim⟩ := hK.tendsto_subseq hvK
  let μ : List A → ℝ := fun x => if hx : x ∈ D then μv ⟨x, hx⟩ else 0
  have hbel : ∀ x, G.IsDecision x → Tendsto (fun n => bayesBelief G (G.assemble (Fs (φ n))) x)
      atTop (𝓝 (μ x)) := by
    intro x hx
    have hxD : x ∈ D := (mem_decisionNodes G).2 hx
    simp only [μ, hxD, ↓reduceDIte]
    exact tendsto_pi_nhds.1 hμlim ⟨x, hxD⟩
  have hcons : IsConsistent G F μ :=
    ⟨Fs ∘ φ, fun n => hTM (φ n), hFsF.comp hφ.tendsto_atTop, hbel⟩
  have hμ : IsBeliefSystem G μ := by
    refine ⟨fun x hx => ?_, fun k => ?_⟩
    · have hxD : x ∈ D := (mem_decisionNodes G).2 hx
      simp only [μ, hxD, ↓reduceDIte]
      exact hμK ⟨x, hxD⟩ (Set.mem_univ _)
    · refine tendsto_nhds_unique (tendsto_finsetSum _ fun x hx =>
        hbel x ((mem_infoSet G).1 hx).1) ?_
      simp only [sum_bayesBelief G (hP _ k)]
      exact tendsto_const_nhds
  -- no move at a single information set is profitable in the limit
  have hone : ∀ i k, G.player k = some i → ∀ b ∈ G.avail k,
      ∑ x ∈ G.infoSet k, μ x * cont G (G.assemble F) (b :: x) i ≤
        condPayoff G (G.assemble F) μ k i := by
    intro i k hk b hb
    have hne : G.player k ≠ none := by rw [hk]; simp
    set ag : Agent G := ⟨k, hne⟩
    have hown : owner G ag = i := by
      have := player_owner G ag
      rw [hk] at this
      exact (Option.some.inj this).symm
    set Q : (H → A → ℝ) → (List A → ℝ) → A → ℝ := fun f m c =>
      ∑ x ∈ G.infoSet k, m x * cont G f (c :: x) i
    have hQlim : ∀ c, Tendsto (fun n => Q (G.assemble (Fs (φ n)))
        (bayesBelief G (G.assemble (Fs (φ n)))) c) atTop (𝓝 (Q (G.assemble F) μ c)) := by
      intro c
      exact tendsto_finsetSum _ fun x hx => (hbel x ((mem_infoSet G).1 hx).1).mul
        (tendsto_cont G (hFsF.comp hφ.tendsto_atTop) _ i)
    -- every move played with positive probability is a best move in the limit
    have hbest : ∀ a ∈ G.avail k, 0 < G.assemble F k a →
        Q (G.assemble F) μ b ≤ Q (G.assemble F) μ a := by
      intro a ha hpos
      set sa := agentPure G ag ⟨a, ha⟩
      set sb := agentPure G ag ⟨b, hb⟩
      have hσa : 0 < σ ag sa := by
        have h2 := congrFun (hFσ k hne) a
        have h1 := assemble_agentProfile_apply G σ ag a
        have ha' : a ∈ G.avail ag.1 := ha
        simp only [ha', ↓reduceDIte] at h1
        exact lt_of_lt_of_eq hpos (h2.trans h1)
      have hev : ∀ᶠ n in atTop, ε (φ n) ag sa < σs (φ n) ag sa := by
        have h1 : Tendsto (fun n => σs (φ n) ag sa - ε (φ n) ag sa) atTop
            (𝓝 (σ ag sa - 0)) :=
          ((tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hlim ag) sa).comp hφ.tendsto_atTop).sub
            ((hε0 ag sa).comp hφ.tendsto_atTop)
        rw [sub_zero] at h1
        filter_upwards [h1.eventually (lt_mem_nhds hσa)] with n hn
        linarith
      refine le_of_tendsto_of_tendsto (hQlim b) (hQlim a) ?_
      filter_upwards [hev] with n hn
      set fn := G.assemble (Fs (φ n))
      have hnb : (agentNF G).mixedPayoff (Function.update (σs (φ n)) ag (pureMixed sb)) ag ≤
          (agentNF G).mixedPayoff (Function.update (σs (φ n)) ag (pureMixed sa)) ag := by
        by_contra hlt
        push Not at hlt
        have := perturbedNash_eq_of_not_best (hσs (φ n)) ag hlt
        linarith
      have hmixU : ∀ s, ∀ ag', IsMixedStrategy
          (Function.update (σs (φ n)) ag (pureMixed s) ag') := by
        intro s ag'
        by_cases h : ag' = ag
        · subst h
          rw [Function.update_self]
          exact isMixedStrategy_pureMixed s
        · rw [Function.update_of_ne h]
          exact hmix _ ag'
      rw [agentNF_mixedPayoff G hPR.1 (hmixU sb), agentNF_mixedPayoff G hPR.1 (hmixU sa),
        assemble_agentProfile_update G _ ag hb, assemble_agentProfile_update G _ ag ha,
        hown, ← hasm] at hnb
      have hdiff := cont_update_dirac_sub G hPR.1 fn k ha hb i
      have hsum : 0 ≤ ∑ x ∈ G.infoSet k, G.reach fn x * (cont G fn (a :: x) i -
          cont G fn (b :: x) i) := by
        rw [← hdiff]
        exact sub_nonneg.2 hnb
      have hPk := hP (φ n) k
      have : Q fn (bayesBelief G fn) a - Q fn (bayesBelief G fn) b =
          (∑ x ∈ G.infoSet k, G.reach fn x * (cont G fn (a :: x) i - cont G fn (b :: x) i)) /
            probInfo G fn k := by
        simp only [Q]
        rw [← Finset.sum_sub_distrib, Finset.sum_div]
        refine Finset.sum_congr rfl fun x hx => ?_
        rw [bayesBelief, ((mem_infoSet G).1 hx).2]
        ring
      have := div_nonneg hsum hPk.le
      linarith
    -- the expected payoff at `k` is the average of the `Q`-values
    have hV : condPayoff G (G.assemble F) μ k i =
        ∑ a ∈ G.avail k, G.assemble F k a * Q (G.assemble F) μ a := by
      have h1 : ∀ x ∈ G.infoSet k, μ x * cont G (G.assemble F) x i =
          ∑ a ∈ G.avail k, G.assemble F k a * (μ x * cont G (G.assemble F) (a :: x) i) := by
        intro x hx
        rw [cont_decision G _ ((mem_infoSet G).1 hx).1, ((mem_infoSet G).1 hx).2,
          Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => by ring
      unfold condPayoff
      rw [Finset.sum_congr rfl h1, Finset.sum_comm]
      exact Finset.sum_congr rfl fun a _ => by simp only [Q]; rw [Finset.mul_sum]
    rw [hV]
    have hsum1 := assemble_sum G hFb k
    calc ∑ x ∈ G.infoSet k, μ x * cont G (G.assemble F) (b :: x) i
        = ∑ a ∈ G.avail k, G.assemble F k a * Q (G.assemble F) μ b := by
          rw [← Finset.sum_mul, hsum1, one_mul]
      _ ≤ ∑ a ∈ G.avail k, G.assemble F k a * Q (G.assemble F) μ a := by
          refine Finset.sum_le_sum fun a ha => ?_
          rcases (assemble_nonneg G hFb k a).lt_or_eq with hpos | hz
          · exact mul_le_mul_of_nonneg_left (hbest a ha hpos) hpos.le
          · rw [← hz, zero_mul, zero_mul]
  refine ⟨μ, hFb, hμ, fun k i hk g hg => ?_, hcons⟩
  exact oneShot_consistent G hPR hN hcons (hone i) hg hk

/-- **Existence of sequential equilibrium** (Kreps and Wilson 1982; MWG, pp. 290 and 300). Every
finite game with perfect recall in which nature's moves have full support has a sequential
equilibrium. -/
theorem exists_isSequentialEq [Finite H] (hPR : G.PerfectRecall) (hN : NatureFullSupport G) :
    ∃ F μ, IsSequentialEq G F μ := by
  have := Fintype.ofFinite H
  obtain ⟨F, hF⟩ := exists_isEFTHP G
  obtain ⟨μ, hμ⟩ := isSequentialEq_of_isEFTHP G hPR hN hF
  exact ⟨F, μ, hμ⟩

/-- **Appendix 9.B** (MWG, p. 300). Every extensive form trembling-hand perfect Nash equilibrium
is subgame perfect (perfect recall, nature with full support). -/
theorem isSPNE_of_isEFTHP [Fintype H] (hPR : G.PerfectRecall) (hN : NatureFullSupport G)
    {F : I → H → A → ℝ} (hF : IsEFTHP G F) : IsSPNE G F := by
  obtain ⟨μ, hμ⟩ := isSequentialEq_of_isEFTHP G hPR hN hF
  exact proposition_9_C_2 G hPR hμ

omit [DecidableEq H] in
/-- **Exercise 9.B.8** (MWG, p. 302). Every finite game `Γ_E` (here: with perfect recall and
moves of nature with full support) has a mixed (behaviour) strategy subgame perfect Nash
equilibrium. -/
theorem exercise_9_B_8 [Finite H] (hPR : G.PerfectRecall) (hN : NatureFullSupport G) :
    ∃ F, IsSPNE G F := by
  classical
  obtain ⟨F, μ, hμ⟩ := exists_isSequentialEq G hPR hN
  exact ⟨F, proposition_9_C_2 G hPR hμ⟩

end MWG.DynamicGames

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The entry game

MWG, Example 9.B.1 and Figures 9.B.1-9.B.2 (pp. 268-270).

Encoding: players `Fin 2` (`0` = the entrant E, `1` = the incumbent I); information sets
`Fin 2` (`0` = E's decision, `1` = I's decision after entry), and player `k` moves at
information set `k`. Actions `Fin 2`: for E `0` = Out and `1` = In; for I `0` = Fight and
`1` = Accommodate. A pure profile is a choice `c k` at each information set; `pureMoves c` is
the behaviour profile playing `c` for sure.

* `example_9_B_1_nash`: the pure Nash equilibria are exactly (out, fight if E plays "in") and
  (in, accommodate if E plays "in").
* `example_9_B_1_not_spne`: (out, fight) is not subgame perfect: fighting is not optimal in
  the post-entry subgame (an empty threat).
* `example_9_B_1_spne`: (in, accommodate) is the unique SPNE (Proposition 9.B.2), obtained by
  backward induction (the reduced game of Figure 9.B.2 gives E the payoff 2 after "in").
* `example_9_B_1_subgames`: the game has two subgames, the whole game and the post-entry
  subgame (p. 275).
-/

namespace MWG.DynamicGames

open MWG.NoncooperativeGames MWG.NoncooperativeGames.ExtensiveForm

/-- The behaviour profile in which the choice `c k` is made for sure at each information
set. -/
def pureMoves {I A H : Type*} [DecidableEq A] (c : H → A) : I → H → A → ℝ :=
  fun _ k => dirac (c k)

/-- A sure choice of available actions is a behaviour profile. -/
theorem isBehaviorProfile_pureMoves {I A H : Type*} [DecidableEq A] {G : ExtensiveForm I A H}
    {c : H → A} (hc : ∀ k, c k ∈ G.avail k) : IsBehaviorProfile G (pureMoves (I := I) c) := by
  intro i k _
  refine ⟨fun a => by unfold pureMoves dirac; split_ifs <;> norm_num, fun a ha => ?_, ?_⟩
  · have : a ≠ c k := fun h => ha (h ▸ hc k)
    simp [pureMoves, dirac, this]
  · simp only [pureMoves, dirac]
    rw [Finset.sum_ite_eq' (G.avail k)]
    simp [hc k]

/-- Payoffs `(u_E, u_I)` at the terminal nodes of the entry game (Figure 9.B.1). -/
def entryPay (i : Fin 2) (z : List (Fin 2)) : ℝ :=
  if z = [0] then (if i = 0 then 0 else 2)
  else if z = [0, 1] then (if i = 0 then -3 else -1)
  else if z = [1, 1] then (if i = 0 then 2 else 1) else 0

/-- **Example 9.B.1, Figure 9.B.1** (MWG, pp. 268-269). The entry game: E chooses Out or In;
after entry I chooses Fight or Accommodate. -/
def entryGame : ExtensiveForm (Fin 2) (Fin 2) (Fin 2) where
  nodes := {[], [0], [1], [0, 1], [1, 1]}
  nil_mem := by decide
  tail_mem := by decide
  info x := if x = [] then 0 else 1
  avail _ := Finset.univ
  avail_spec := by decide
  info_surj := by decide
  player k := some k
  natureProb _ _ := 0
  nature_nonneg := fun _ hk => absurd hk (by simp)
  nature_zero := fun _ hk => absurd hk (by simp)
  nature_sum := fun _ hk => absurd hk (by simp)
  payoff := entryPay

theorem entryGame_nodes : entryGame.nodes = {[], [0], [1], [0, 1], [1, 1]} := rfl
theorem entryGame_info (x : List (Fin 2)) : entryGame.info x = if x = [] then 0 else 1 := rfl
theorem entryGame_avail (k : Fin 2) : entryGame.avail k = Finset.univ := rfl
theorem entryGame_player (k : Fin 2) : entryGame.player k = some k := rfl
theorem entryGame_payoff : entryGame.payoff = entryPay := rfl

theorem entryGame_assemble (F : Fin 2 → Fin 2 → Fin 2 → ℝ) (k : Fin 2) :
    entryGame.assemble F k = F k k := entryGame.assemble_of_some F rfl

/-- The continuation payoffs of the entry game. -/
theorem entryGame_cont (f : Fin 2 → Fin 2 → ℝ) (i : Fin 2) :
    cont entryGame f [] i = f 0 0 * entryPay i [0] +
      f 0 1 * (f 1 0 * entryPay i [0, 1] + f 1 1 * entryPay i [1, 1]) ∧
    cont entryGame f [1] i = f 1 0 * entryPay i [0, 1] + f 1 1 * entryPay i [1, 1] := by
  constructor <;>
  simp [cont_unfold, entryGame, Fin.sum_univ_two]

/-- **Example 9.B.1** (MWG, p. 269). The entry game is a finite game of perfect information. -/
theorem example_9_B_1_perfectInformation : entryGame.PerfectInformation := by
  unfold ExtensiveForm.PerfectInformation
  decide

/-- **Example 9.B.1** (MWG, p. 269). The pure strategy Nash equilibria are exactly
`(σ_E, σ_I) = (out, fight if E plays "in")` and `(in, accommodate if E plays "in")`. -/
theorem example_9_B_1_nash (a b : Fin 2) :
    IsNashB entryGame (pureMoves ![a, b]) ↔ (a = 0 ∧ b = 0) ∨ (a = 1 ∧ b = 1) := by
  have hB : IsBehaviorProfile entryGame (pureMoves (I := Fin 2) ![a, b]) :=
    isBehaviorProfile_pureMoves fun _ => Finset.mem_univ _
  constructor
  · intro h
    by_contra hne
    fin_cases a <;> fin_cases b <;> simp at hne
    · -- (out, accommodate): E gains by entering
      have := h.2 0 (fun _ => dirac 1) fun k hk => by
        have hk0 : k = 0 := by simpa [entryGame] using hk
        subst hk0
        exact (isBehaviorProfile_pureMoves (G := entryGame) (c := fun _ => (1 : Fin 2))
          fun _ => Finset.mem_univ _) 0 0 rfl
      simp [(entryGame_cont _ _).1, entryGame_assemble, pureMoves, dirac, entryPay] at this
      norm_num at this
    · -- (in, fight): E gains by staying out
      have := h.2 0 (fun _ => dirac 0) fun k hk => by
        have hk0 : k = 0 := by simpa [entryGame] using hk
        subst hk0
        exact (isBehaviorProfile_pureMoves (G := entryGame) (c := fun _ => (0 : Fin 2))
          fun _ => Finset.mem_univ _) 0 0 rfl
      simp [(entryGame_cont _ _).1, entryGame_assemble, pureMoves, dirac, entryPay] at this
      norm_num at this
  · intro h
    refine ⟨hB, ?_⟩
    rw [Fin.forall_fin_two]
    constructor <;> intro g hg <;>
    · have hg0 := (hg _ rfl).1
      have hg1 := (hg _ rfl).2.2
      simp only [entryGame, Fin.sum_univ_two] at hg1
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp [(entryGame_cont _ _).1, entryGame_assemble, pureMoves, dirac, entryPay] <;>
        nlinarith [hg0 0, hg0 1]

/-- The decision nodes of the entry game. -/
theorem entryGame_decisionNodes : entryGame.decisionNodes = {[], [1]} := by decide

/-- The terminal nodes of the entry game. -/
theorem entryGame_terminals : entryGame.terminals = {[0], [0, 1], [1, 1]} := by decide

/-- **Example 9.B.1** (MWG, p. 275). The game has two subgames: the game as a whole and the
post-entry subgame starting at I's decision node. -/
theorem example_9_B_1_subgames (x : List (Fin 2)) :
    IsSubgameRoot entryGame x ↔ x = [] ∨ x = [1] := by
  constructor
  · intro h
    have := (mem_decisionNodes _).2 h.1
    rw [entryGame_decisionNodes] at this
    simpa using this
  · rintro (rfl | rfl) <;>
      exact isSubgameRoot_of_perfectInformation _ example_9_B_1_perfectInformation
        (by unfold IsDecision; simp [entryGame])

/-- **Example 9.B.1** (MWG, pp. 269-275). `(out, fight if E plays "in")` is not subgame
perfect: in the post-entry subgame accommodating gives I `1 > −1`. -/
theorem example_9_B_1_not_spne : ¬ IsSPNE entryGame (pureMoves ![0, 0]) := by
  intro h
  have := h.2 [1] ((example_9_B_1_subgames _).2 (Or.inr rfl)) 1 (fun _ => dirac 1) fun k hk => by
    have hk1 : k = 1 := by simpa [entryGame] using hk
    subst hk1
    exact (isBehaviorProfile_pureMoves (G := entryGame) (c := fun _ => (1 : Fin 2))
      fun _ => Finset.mem_univ _) 1 1 rfl
  simp [(entryGame_cont _ _).2, entryGame_assemble, pureMoves, dirac, entryPay] at this
  norm_num at this

/-- **Example 9.B.1, Figure 9.B.2** (MWG, pp. 270 and 275). `(in, accommodate if E plays
"in")` is the unique subgame perfect Nash equilibrium (in behaviour strategies): backward
induction first has I accommodate, then E enter in the reduced game. -/
theorem example_9_B_1_spne :
    IsSPNE entryGame (pureMoves ![1, 1]) ∧ ∀ F, IsSPNE entryGame F →
      ∀ k, entryGame.assemble F k = entryGame.assemble (pureMoves ![1, 1]) k := by
  have hPI := example_9_B_1_perfectInformation
  have hB : IsBehaviorProfile entryGame (pureMoves (I := Fin 2) ![(1 : Fin 2), 1]) :=
    isBehaviorProfile_pureMoves fun _ => Finset.mem_univ _
  have hS : IsSPNE entryGame (pureMoves ![1, 1]) := by
    refine isSPNE_of_oneShotOptimal _ hB fun x hx => ?_
    intro j hj a _
    have hx' := (mem_decisionNodes _).2 hx
    rw [entryGame_decisionNodes] at hx'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
    rcases hx' with rfl | rfl
    · obtain rfl : j = 0 := by simpa [entryGame_player, entryGame_info] using hj.symm
      fin_cases a <;>
      simp [cont_unfold, entryGame_nodes, entryGame_info, entryGame_avail, entryGame_payoff,
        Fin.sum_univ_two, entryGame_assemble, pureMoves, dirac, entryPay]
    · obtain rfl : j = 1 := by simpa [entryGame_player, entryGame_info] using hj.symm
      fin_cases a <;>
      simp [cont_unfold, entryGame_nodes, entryGame_info, entryGame_avail, entryGame_payoff,
        Fin.sum_univ_two, entryGame_assemble, pureMoves, dirac, entryPay]
  refine ⟨hS, fun F hF k => (proposition_9_B_2 _ hPI).2 (fun k => by simp [entryGame])
    (fun i z hz z' hz' he => ?_) F _ hF hS k⟩
  rw [entryGame_terminals] at hz hz'
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz hz'
  have hz1 := hz
  have hz2 := hz'
  fin_cases i <;> rcases hz1 with rfl | rfl | rfl <;> rcases hz2 with rfl | rfl | rfl <;>
    simp [entryGame, entryPay] at he ⊢ <;> norm_num at he

end MWG.DynamicGames

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Entry with two entry strategies

MWG, Examples 9.C.1 and 9.C.3 (Figures 9.C.1 and 9.C.3, pp. 282-288) and Exercise 9.C.2.

The entrant E chooses Out (`0`), In₁ (`1`) or In₂ (`2`); the incumbent I observes entry but not
which entry strategy was used, and chooses Fight (`0`) or Accommodate (`1`) at its single
information set `1` = `{[1], [2]}`. `entryTwo o t` has payoffs `o` after Out and `t e f` after
entry strategy `e` (`0` = In₁, `1` = In₂) and response `f`.

* `example_9_C_1_nash`, `example_9_C_1_spne`: in Figure 9.C.1 both (out, fight) and
  (in₁, accommodate) are Nash equilibria, and as the only subgame is the whole game both are
  subgame perfect.
* `example_9_C_1_weakPBE`: (in₁, accommodate) with belief `1` on the left node is the unique
  weak perfect Bayesian equilibrium, pure or mixed; (out, fight) is part of no weak PBE.
* `example_9_C_3`: in Figure 9.C.3 with `γ > 0` the unique weak PBE has E playing
  `(0, 2/3, 1/3)`, I fighting with probability `1/(γ + 2)` and `μ₁ = 2/3`.
* `exercise_9_C_2`: for `γ ∈ (−1, 0)` every weak PBE has E staying out with I fighting with
  probability at least `max(3/4, 2/(2 − γ))` and `μ₁ ≥ 2/3` (with `μ₁ = 2/3` unless I fights
  for sure), or (for `γ ≥ −2/3`) E entering with In₁ twice as likely as In₂, I fighting with
  probability `1/(γ + 2)` and `μ₁ = 2/3`; each of these is a weak PBE.
-/

namespace MWG.DynamicGames

open MWG.NoncooperativeGames MWG.NoncooperativeGames.ExtensiveForm

/-- Payoffs of the entry game with two entry strategies. -/
def entryTwoPay (o : Fin 2 → ℝ) (t : Fin 2 → Fin 2 → Fin 2 → ℝ) (i : Fin 2)
    (z : List (Fin 3)) : ℝ :=
  if z = [0] then o i else if z = [0, 1] then t 0 0 i else if z = [1, 1] then t 0 1 i
  else if z = [0, 2] then t 1 0 i else if z = [1, 2] then t 1 1 i else 0

/-- The entry game with two entry strategies (Figures 9.C.1, 9.C.3, 9.D.1(a), 9.BB.2). -/
def entryTwo (o : Fin 2 → ℝ) (t : Fin 2 → Fin 2 → Fin 2 → ℝ) :
    ExtensiveForm (Fin 2) (Fin 3) (Fin 2) where
  nodes := {[], [0], [1], [2], [0, 1], [1, 1], [0, 2], [1, 2]}
  nil_mem := by decide
  tail_mem := by decide
  info x := if x = [] then 0 else 1
  avail k := if k = 0 then Finset.univ else {0, 1}
  avail_spec := by decide
  info_surj := by decide
  player k := some k
  natureProb _ _ := 0
  nature_nonneg := fun _ hk => absurd hk (by simp)
  nature_zero := fun _ hk => absurd hk (by simp)
  nature_sum := fun _ hk => absurd hk (by simp)
  payoff := entryTwoPay o t

variable (o : Fin 2 → ℝ) (t : Fin 2 → Fin 2 → Fin 2 → ℝ)

theorem entryTwo_assemble (F : Fin 2 → Fin 2 → Fin 3 → ℝ) (k : Fin 2) :
    (entryTwo o t).assemble F k = F k k := (entryTwo o t).assemble_of_some F rfl

/-- Continuation payoffs in the entry game with two entry strategies. -/
theorem entryTwo_cont (f : Fin 2 → Fin 3 → ℝ) (i : Fin 2) :
    cont (entryTwo o t) f [1] i = f 1 0 * t 0 0 i + f 1 1 * t 0 1 i ∧
    cont (entryTwo o t) f [2] i = f 1 0 * t 1 0 i + f 1 1 * t 1 1 i ∧
    cont (entryTwo o t) f [] i = f 0 0 * o i + f 0 1 * (f 1 0 * t 0 0 i + f 1 1 * t 0 1 i) +
      f 0 2 * (f 1 0 * t 1 0 i + f 1 1 * t 1 1 i) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [cont_unfold, entryTwo, entryTwoPay, Fin.sum_univ_three]

theorem entryTwo_infoSet : (entryTwo o t).infoSet 0 = {[]} ∧
    (entryTwo o t).infoSet 1 = {[1], [2]} :=
  ⟨(by decide : (entryTwo (fun _ => 0) (fun _ _ _ => 0)).infoSet 0 = {[]}),
    (by decide : (entryTwo (fun _ => 0) (fun _ _ _ => 0)).infoSet 1 = {[1], [2]})⟩

/-- Expected payoffs at the two information sets given beliefs `μ`. -/
theorem entryTwo_condPayoff (f : Fin 2 → Fin 3 → ℝ) (μ : List (Fin 3) → ℝ) (i : Fin 2) :
    condPayoff (entryTwo o t) f μ 0 i = μ [] * cont (entryTwo o t) f [] i ∧
    condPayoff (entryTwo o t) f μ 1 i =
      μ [1] * cont (entryTwo o t) f [1] i + μ [2] * cont (entryTwo o t) f [2] i := by
  unfold condPayoff
  rw [(entryTwo_infoSet o t).1, (entryTwo_infoSet o t).2]
  simp

theorem entryTwo_reach (f : Fin 2 → Fin 3 → ℝ) :
    (entryTwo o t).reach f [1] = f 0 1 ∧ (entryTwo o t).reach f [2] = f 0 2 ∧
      probInfo (entryTwo o t) f 1 = f 0 1 + f 0 2 := by
  refine ⟨by simp [entryTwo], by simp [entryTwo], ?_⟩
  unfold probInfo
  rw [(entryTwo_infoSet o t).2]
  simp [entryTwo]

/-- Facts about a behaviour profile of the game. -/
theorem entryTwo_behavior {F : Fin 2 → Fin 2 → Fin 3 → ℝ}
    (hF : IsBehaviorProfile (entryTwo o t) F) :
    (∀ a, 0 ≤ F 0 0 a) ∧ F 0 0 0 + F 0 0 1 + F 0 0 2 = 1 ∧ (∀ a, 0 ≤ F 1 1 a) ∧
      F 1 1 0 + F 1 1 1 = 1 := by
  have h0 := hF 0 0 rfl
  have h1 := hF 1 1 rfl
  exact ⟨h0.1, by simpa [entryTwo, Fin.sum_univ_three] using h0.2.2, h1.1,
    by simpa [entryTwo] using h1.2.2⟩

/-- A behaviour strategy of `E` or `I` sending probability one to `a` at its own information
set. -/
theorem entryTwo_dirac_beh (i : Fin 2) {a : Fin 3} (ha : a ∈ (entryTwo o t).avail i) :
    (entryTwo o t).IsBehaviorStrategy i (fun _ => dirac a) := by
  intro k hk
  have hki : k = i := by simpa [entryTwo] using hk
  subst hki
  refine ⟨fun b => by beta_reduce; unfold dirac; split_ifs <;> norm_num, fun b hb => ?_, ?_⟩
  · have : b ≠ a := fun h => hb (h ▸ ha)
    simp [dirac, this]
  · simp only [dirac]
    rw [Finset.sum_ite_eq']
    simp [ha]

/-- The payoffs of Figure 9.C.1 after entry: `(u_E, u_I)` = (−1, −1), (3, 0), (−1, −1),
(2, 1). -/
abbrev fig9C1 : ExtensiveForm (Fin 2) (Fin 3) (Fin 2) :=
  entryTwo ![0, 2] ![![![-1, -1], ![3, 0]], ![![-1, -1], ![2, 1]]]

theorem entryTwo_beh0 {g : Fin 2 → Fin 3 → ℝ} (hg : (entryTwo o t).IsBehaviorStrategy 0 g) :
    (∀ a, 0 ≤ g 0 a) ∧ g 0 0 + g 0 1 + g 0 2 = 1 :=
  ⟨(hg 0 rfl).1, by simpa [entryTwo, Fin.sum_univ_three] using (hg 0 rfl).2.2⟩

theorem entryTwo_beh1 {g : Fin 2 → Fin 3 → ℝ} (hg : (entryTwo o t).IsBehaviorStrategy 1 g) :
    (∀ a, 0 ≤ g 1 a) ∧ g 1 0 + g 1 1 = 1 :=
  ⟨(hg 1 rfl).1, by simpa [entryTwo] using (hg 1 rfl).2.2⟩

/-- The only subgame of the entry game with two entry strategies is the game itself. -/
theorem entryTwo_subgames {x : List (Fin 3)} (hx : IsSubgameRoot (entryTwo o t) x) : x = [] := by
  have hd := hx.1
  have hmem := (mem_decisionNodes _).2 hd
  rw [show (entryTwo o t).decisionNodes = {[], [1], [2]} from
    (by decide : (entryTwo (fun _ => 0) (fun _ _ _ => 0)).decisionNodes = {[], [1], [2]})] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl
  · rfl
  · exact absurd (hx.2.1 [2] (by unfold IsDecision; simp [entryTwo]) (by simp [entryTwo]))
      (by simp)
  · exact absurd (hx.2.1 [1] (by unfold IsDecision; simp [entryTwo]) (by simp [entryTwo]))
      (by simp)

/-- **Example 9.C.1** (MWG, p. 282). In Figure 9.C.1 both (out, fight if entry occurs) and
(in₁, accommodate if entry occurs) are Nash equilibria. -/
theorem example_9_C_1_nash :
    IsNashB fig9C1 (pureMoves ![0, 0]) ∧ IsNashB fig9C1 (pureMoves ![1, 1]) := by
  have hB : ∀ a b : Fin 3, b ∈ ({0, 1} : Finset (Fin 3)) →
      IsBehaviorProfile fig9C1 (pureMoves (I := Fin 2) ![a, b]) := fun a b hb =>
    isBehaviorProfile_pureMoves fun k => by
      fin_cases k
      · simp [fig9C1, entryTwo]
      · simpa [fig9C1, entryTwo] using hb
  refine ⟨⟨hB 0 0 (by decide), ?_⟩, ⟨hB 1 1 (by decide), ?_⟩⟩ <;>
  · rw [Fin.forall_fin_two]
    constructor <;> intro g hg
    · obtain ⟨h0, h1⟩ := entryTwo_beh0 _ _ hg
      simp [fig9C1, (entryTwo_cont _ _ _ _).2.2, entryTwo_assemble, pureMoves, dirac]
      nlinarith [h0 0, h0 1, h0 2]
    · obtain ⟨h0, h1⟩ := entryTwo_beh1 _ _ hg
      simp [fig9C1, (entryTwo_cont _ _ _ _).2.2, entryTwo_assemble, pureMoves, dirac] <;>
      nlinarith [h0 0, h0 1, h0 2]

/-- **Example 9.C.1** (MWG, p. 282). The only subgame is the game as a whole, so both Nash
equilibria are subgame perfect (Exercise 9.B.2(a)): subgame perfection is of no use here. -/
theorem example_9_C_1_spne :
    IsSPNE fig9C1 (pureMoves ![0, 0]) ∧ IsSPNE fig9C1 (pureMoves ![1, 1]) :=
  ⟨exercise_9_B_2a _ (fun _ hx => entryTwo_subgames _ _ hx) example_9_C_1_nash.1,
    exercise_9_B_2a _ (fun _ hx => entryTwo_subgames _ _ hx) example_9_C_1_nash.2⟩

/-- The beliefs putting probability one on the left node of I's information set. -/
def leftBelief (x : List (Fin 3)) : ℝ := if x = [2] then 0 else 1

/-- **Example 9.C.1 continued** (MWG, p. 286). (in₁, accommodate if entry occurs) with
beliefs `μ(left) = 1` is a weak perfect Bayesian equilibrium, and it is the unique weak PBE
(pure or mixed): in every weak PBE I accommodates, E plays in₁ and `μ(left) = 1`. In
particular the Nash equilibrium (out, fight) is not part of any weak PBE. -/
theorem example_9_C_1_weakPBE :
    IsWeakPBE fig9C1 (pureMoves ![1, 1]) leftBelief ∧
    ∀ F μ, IsWeakPBE fig9C1 F μ → F 1 1 0 = 0 ∧ F 1 1 1 = 1 ∧ F 0 0 0 = 0 ∧ F 0 0 1 = 1 ∧
      F 0 0 2 = 0 ∧ μ [1] = 1 ∧ μ [2] = 0 := by
  have hc := entryTwo_cont ![0, 2] ![![![-1, -1], ![3, 0]], ![![-1, -1], ![2, 1]]]
  have hcp := entryTwo_condPayoff ![0, 2] ![![![-1, -1], ![3, 0]], ![![-1, -1], ![2, 1]]]
  have hr := entryTwo_reach ![0, 2] ![![![-1, -1], ![3, 0]], ![![-1, -1], ![2, 1]]]
  have hI := entryTwo_infoSet ![0, 2] ![![![-1, -1], ![3, 0]], ![![-1, -1], ![2, 1]]]
  constructor
  · refine ⟨example_9_C_1_nash.2.1, ⟨fun x _ => ?_, ?_⟩, ?_, ?_⟩
    · unfold leftBelief; split_ifs <;> norm_num
    · rw [Fin.forall_fin_two]
      exact ⟨by rw [hI.1]; simp [leftBelief], by rw [hI.2]; simp [leftBelief]⟩
    · intro k
      fin_cases k <;> intro i hi g hg <;> have hi' : i = _ := Option.some.inj hi.symm <;>
        subst hi'
      · obtain ⟨h0, h1⟩ := entryTwo_beh0 _ _ hg
        simp [fig9C1, (hcp _ _ _).1, (hc _ _).2.2, entryTwo_assemble, pureMoves, dirac,
          leftBelief]
        nlinarith [h0 0, h0 1, h0 2]
      · obtain ⟨h0, h1⟩ := entryTwo_beh1 _ _ hg
        simp [fig9C1, (hcp _ _ _).2, (hc _ _).1, (hc _ _).2.1, entryTwo_assemble, pureMoves,
          dirac, leftBelief]
        nlinarith [h0 0, h0 1]
    · refine Fin.forall_fin_two.2 ⟨fun hk x hx => ?_, fun hk x hx => ?_⟩
      · rw [hI.1] at hx
        simp only [Finset.mem_singleton] at hx
        subst hx
        simp [probInfo, hI.1, leftBelief]
      · rw [hI.2] at hx
        simp only [fig9C1, (hr _).2.2, entryTwo_assemble, pureMoves, dirac] at hk ⊢
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> simp [(hr _).1, (hr _).2.1, entryTwo_assemble, pureMoves,
          dirac, leftBelief]
  · intro F μ ⟨hF, hμ, hSR, hB⟩
    obtain ⟨hp0, hp1, hq0, hq1⟩ := entryTwo_behavior _ _ hF
    have hμ0 : μ [] = 1 := by simpa [hI.1] using hμ.2 0
    have hμ1 : μ [1] + μ [2] = 1 := by simpa [hI.2] using hμ.2 1
    have hμn1 := (hμ.1 [1] (by unfold IsDecision; simp [fig9C1, entryTwo])).1
    have hμn2 := (hμ.1 [2] (by unfold IsDecision; simp [fig9C1, entryTwo])).1
    -- I accommodates
    have hacc := hSR 1 1 rfl (fun _ => dirac 1) (entryTwo_dirac_beh _ _ 1 (by simp [entryTwo]))
    simp [fig9C1, (hcp _ _ _).2, (hc _ _).1, (hc _ _).2.1, entryTwo_assemble, dirac] at hacc
    have hq : F 1 1 0 = 0 := by nlinarith [hq0 0, hq0 1]
    have hq' : F 1 1 1 = 1 := by linarith
    -- E plays in₁
    have hin := hSR 0 0 rfl (fun _ => dirac 1) (entryTwo_dirac_beh _ _ 0 (by simp [entryTwo]))
    simp [fig9C1, (hcp _ _ _).1, (hc _ _).2.2, entryTwo_assemble, dirac, hμ0, hq, hq'] at hin
    have hp : F 0 0 1 = 1 := by nlinarith [hp0 0, hp0 1, hp0 2]
    have hpz0 : F 0 0 0 = 0 := by nlinarith [hp0 0, hp0 1, hp0 2]
    have hpz2 : F 0 0 2 = 0 := by nlinarith [hp0 0, hp0 1, hp0 2]
    -- Bayes' rule at I's information set
    have hpos : 0 < probInfo fig9C1 (fig9C1.assemble F) 1 := by
      simp only [fig9C1, (hr _).2.2, entryTwo_assemble, hp, hpz2]
      norm_num
    have h1 := hB 1 hpos [1] (by rw [hI.2]; simp)
    have h2 := hB 1 hpos [2] (by rw [hI.2]; simp)
    simp only [fig9C1, (hr _).1, (hr _).2.1, (hr _).2.2, entryTwo_assemble, hp, hpz2] at h1 h2
    norm_num at h1 h2
    exact ⟨hq, hq', hpz0, hp, hpz2, h1, h2⟩

/-- The conditions of a weak perfect Bayesian equilibrium of the entry game with two entry
strategies, written out: E's and I's one-move deviations and Bayes' rule at I's information
set. -/
theorem entryTwo_weakPBE_facts {F : Fin 2 → Fin 2 → Fin 3 → ℝ} {μ : List (Fin 3) → ℝ}
    (hW : IsWeakPBE (entryTwo o t) F μ) :
    (∀ a, 0 ≤ F 0 0 a) ∧ F 0 0 0 + F 0 0 1 + F 0 0 2 = 1 ∧ (∀ a, 0 ≤ F 1 1 a) ∧
    F 1 1 0 + F 1 1 1 = 1 ∧ μ [1] + μ [2] = 1 ∧ 0 ≤ μ [1] ∧ 0 ≤ μ [2] ∧
    (μ [1] * t 0 0 1 + μ [2] * t 1 0 1 ≤
      μ [1] * (F 1 1 0 * t 0 0 1 + F 1 1 1 * t 0 1 1) +
        μ [2] * (F 1 1 0 * t 1 0 1 + F 1 1 1 * t 1 1 1)) ∧
    (μ [1] * t 0 1 1 + μ [2] * t 1 1 1 ≤
      μ [1] * (F 1 1 0 * t 0 0 1 + F 1 1 1 * t 0 1 1) +
        μ [2] * (F 1 1 0 * t 1 0 1 + F 1 1 1 * t 1 1 1)) ∧
    (∀ v ∈ ({o 0, F 1 1 0 * t 0 0 0 + F 1 1 1 * t 0 1 0, F 1 1 0 * t 1 0 0 + F 1 1 1 * t 1 1 0} :
      Set ℝ), v ≤ F 0 0 0 * o 0 + F 0 0 1 * (F 1 1 0 * t 0 0 0 + F 1 1 1 * t 0 1 0) +
        F 0 0 2 * (F 1 1 0 * t 1 0 0 + F 1 1 1 * t 1 1 0)) ∧
    (0 < F 0 0 1 + F 0 0 2 → μ [1] = F 0 0 1 / (F 0 0 1 + F 0 0 2) ∧
      μ [2] = F 0 0 2 / (F 0 0 1 + F 0 0 2)) := by
  obtain ⟨hF, hμ, hSR, hB⟩ := hW
  obtain ⟨hp0, hp1, hq0, hq1⟩ := entryTwo_behavior o t hF
  have hI := entryTwo_infoSet o t
  have hc := entryTwo_cont o t
  have hcp := entryTwo_condPayoff o t
  have hr := entryTwo_reach o t
  have hμ0 : μ [] = 1 := by simpa [hI.1] using hμ.2 0
  have hμ1 : μ [1] + μ [2] = 1 := by simpa [hI.2] using hμ.2 1
  have hd1 : (entryTwo o t).IsDecision [1] := by unfold IsDecision; simp [entryTwo]
  have hd2 : (entryTwo o t).IsDecision [2] := by unfold IsDecision; simp [entryTwo]
  have hIdev : ∀ a : Fin 3, a ∈ ({0, 1} : Finset (Fin 3)) →
      μ [1] * cont (entryTwo o t) (fun _ => dirac a) [1] 1 +
        μ [2] * cont (entryTwo o t) (fun _ => dirac a) [2] 1 ≤
      μ [1] * cont (entryTwo o t) ((entryTwo o t).assemble F) [1] 1 +
        μ [2] * cont (entryTwo o t) ((entryTwo o t).assemble F) [2] 1 := by
    intro a ha
    have h := hSR 1 1 rfl (fun _ => dirac a)
      (entryTwo_dirac_beh o t 1 (by simpa [entryTwo] using ha))
    rw [(hcp _ _ _).2, (hcp _ _ _).2] at h
    refine le_trans (le_of_eq ?_) h
    congr 2
  refine ⟨hp0, hp1, hq0, hq1, hμ1, (hμ.1 _ hd1).1, (hμ.1 _ hd2).1, ?_, ?_, ?_, fun hpos => ?_⟩
  · have h := hIdev 0 (by decide)
    simpa [(hc _ _).1, (hc _ _).2.1, entryTwo_assemble, dirac] using h
  · have h := hIdev 1 (by decide)
    simpa [(hc _ _).1, (hc _ _).2.1, entryTwo_assemble, dirac] using h
  · intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    have key : ∀ a : Fin 3, cont (entryTwo o t) ((entryTwo o t).assemble
        (Function.update F 0 (fun _ => dirac a))) [] 0 ≤
        cont (entryTwo o t) ((entryTwo o t).assemble F) [] 0 := by
      intro a
      have h := hSR 0 0 rfl (fun _ => dirac a) (entryTwo_dirac_beh o t 0 (by simp [entryTwo]))
      rw [(hcp _ _ _).1, (hcp _ _ _).1, hμ0, one_mul, one_mul] at h
      exact h
    rcases hv with rfl | rfl | rfl
    · have := key 0
      simpa [(hc _ _).2.2, entryTwo_assemble, dirac] using this
    · have := key 1
      simpa [(hc _ _).2.2, entryTwo_assemble, dirac] using this
    · have := key 2
      simpa [(hc _ _).2.2, entryTwo_assemble, dirac] using this
  · have hp : 0 < probInfo (entryTwo o t) ((entryTwo o t).assemble F) 1 := by
      rw [(hr _).2.2, entryTwo_assemble]
      exact hpos
    have h1 := hB 1 hp [1] (by rw [hI.2]; simp)
    have h2 := hB 1 hp [2] (by rw [hI.2]; simp)
    rw [(hr _).1, (hr _).2.2, entryTwo_assemble] at h1
    rw [(hr _).2.1, (hr _).2.2, entryTwo_assemble] at h2
    exact ⟨h1, h2⟩

/-- **Example 9.C.3, Figure 9.C.3** (MWG, pp. 287-288): payoffs after entry `(−1, −1)`,
`(3, −2)` (in₁) and `(γ, −1)`, `(2, 1)` (in₂). -/
abbrev fig9C3 (γ : ℝ) : ExtensiveForm (Fin 2) (Fin 3) (Fin 2) :=
  entryTwo ![0, 2] ![![![-1, -1], ![3, -2]], ![![γ, -1], ![2, 1]]]

/-- Example 9.C.3, I's optimality: if `μ₁ < 2/3` I accommodates for sure. -/
theorem fig9C3_acc {μ1 q : ℝ} (hq0 : 0 ≤ q) (hlt : μ1 < 2 / 3)
    (hIa : μ1 * (-2) + (1 - μ1) * 1 ≤ μ1 * (q * (-1) + (1 - q) * (-2)) +
      (1 - μ1) * (q * (-1) + (1 - q) * 1)) : q = 0 := by
  nlinarith [mul_nonneg hq0 (sub_nonneg.2 hlt.le)]

/-- Example 9.C.3, I's optimality: if `μ₁ > 2/3` I fights for sure. -/
theorem fig9C3_fight {μ1 q : ℝ} (hq1 : q ≤ 1) (hgt : 2 / 3 < μ1)
    (hIf : μ1 * (-1) + (1 - μ1) * (-1) ≤ μ1 * (q * (-1) + (1 - q) * (-2)) +
      (1 - μ1) * (q * (-1) + (1 - q) * 1)) : q = 1 := by
  by_contra hne
  have : q < 1 := lt_of_le_of_ne hq1 hne
  nlinarith [mul_pos (sub_pos.2 hgt) (sub_pos.2 this)]

/-- Example 9.C.3, E's optimality: the moves played with positive probability are best. -/
theorem fig9C3_best {p0 p1 p2 v1 v2 : ℝ} (hp0 : 0 ≤ p0) (hp1 : 0 ≤ p1) (hp2 : 0 ≤ p2)
    (hsum : p0 + p1 + p2 = 1) (hE0 : 0 ≤ p1 * v1 + p2 * v2) (hE1 : v1 ≤ p1 * v1 + p2 * v2)
    (hE2 : v2 ≤ p1 * v1 + p2 * v2) :
    (0 < p1 → p1 * v1 + p2 * v2 = v1) ∧ (0 < p2 → p1 * v1 + p2 * v2 = v2) ∧
      (0 < p0 → p1 * v1 + p2 * v2 = 0) := by
  have hz : p1 * (p1 * v1 + p2 * v2 - v1) + p2 * (p1 * v1 + p2 * v2 - v2) +
      p0 * (p1 * v1 + p2 * v2) = 0 := by
    have : p0 = 1 - p1 - p2 := by linarith
    rw [this]
    ring
  have t1 := mul_nonneg hp1 (sub_nonneg.2 hE1)
  have t2 := mul_nonneg hp2 (sub_nonneg.2 hE2)
  have t3 := mul_nonneg hp0 hE0
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have : p1 * (p1 * v1 + p2 * v2 - v1) = 0 := by linarith
    rcases mul_eq_zero.1 this with h' | h'
    · linarith
    · linarith
  · have : p2 * (p1 * v1 + p2 * v2 - v2) = 0 := by linarith
    rcases mul_eq_zero.1 this with h' | h'
    · linarith
    · linarith
  · have : p0 * (p1 * v1 + p2 * v2) = 0 := by linarith
    rcases mul_eq_zero.1 this with h' | h'
    · linarith
    · exact h'

/-- The scalar conditions of a weak PBE of Figure 9.C.3: `p` E's mixed move, `q` the
probability that I fights, `μ1` the belief on the left node. -/
theorem fig9C3_scalar {γ : ℝ} {F : Fin 2 → Fin 2 → Fin 3 → ℝ} {μ : List (Fin 3) → ℝ}
    (hW : IsWeakPBE (fig9C3 γ) F μ) :
    0 ≤ F 0 0 0 ∧ 0 ≤ F 0 0 1 ∧ 0 ≤ F 0 0 2 ∧ F 0 0 0 + F 0 0 1 + F 0 0 2 = 1 ∧
    0 ≤ F 1 1 0 ∧ F 1 1 0 ≤ 1 ∧ 0 ≤ μ [1] ∧ μ [1] ≤ 1 ∧
    μ [1] * (-1) + (1 - μ [1]) * (-1) ≤ μ [1] * (F 1 1 0 * (-1) + (1 - F 1 1 0) * (-2)) +
      (1 - μ [1]) * (F 1 1 0 * (-1) + (1 - F 1 1 0) * 1) ∧
    μ [1] * (-2) + (1 - μ [1]) * 1 ≤ μ [1] * (F 1 1 0 * (-1) + (1 - F 1 1 0) * (-2)) +
      (1 - μ [1]) * (F 1 1 0 * (-1) + (1 - F 1 1 0) * 1) ∧
    0 ≤ F 0 0 1 * (F 1 1 0 * (-1) + (1 - F 1 1 0) * 3) +
      F 0 0 2 * (F 1 1 0 * γ + (1 - F 1 1 0) * 2) ∧
    F 1 1 0 * (-1) + (1 - F 1 1 0) * 3 ≤ F 0 0 1 * (F 1 1 0 * (-1) + (1 - F 1 1 0) * 3) +
      F 0 0 2 * (F 1 1 0 * γ + (1 - F 1 1 0) * 2) ∧
    F 1 1 0 * γ + (1 - F 1 1 0) * 2 ≤ F 0 0 1 * (F 1 1 0 * (-1) + (1 - F 1 1 0) * 3) +
      F 0 0 2 * (F 1 1 0 * γ + (1 - F 1 1 0) * 2) ∧
    (0 < F 0 0 1 + F 0 0 2 → μ [1] = F 0 0 1 / (F 0 0 1 + F 0 0 2)) := by
  obtain ⟨hp, hp1, hq, hq1, hμ1, hμa, hμb, hIf, hIa, hE, hB⟩ := entryTwo_weakPBE_facts _ _ hW
  have hμ2 : μ [2] = 1 - μ [1] := by linarith
  have hr1 : F 1 1 1 = 1 - F 1 1 0 := by linarith
  have hE0 := hE _ (Set.mem_insert _ _)
  have hE1 := hE _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hE2 := hE _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  simp only [hμ2, hr1] at hIf hIa hE0 hE1 hE2
  refine ⟨hp 0, hp 1, hp 2, hp1, hq 0, by linarith [hq 1], hμa, by linarith, ?_, ?_, ?_, ?_, ?_,
    fun h => (hB h).1⟩
  · simpa using hIf
  · simpa using hIa
  · simpa using hE0
  · simpa using hE1
  · simpa using hE2

/-- **Example 9.C.3** (MWG, p. 288). For `γ > 0` every weak PBE has E playing
`(σ₀, σ₁, σ₂) = (0, 2/3, 1/3)`, I fighting with probability `σ_F = 1/(γ + 2)` and
`μ₁ = 2/3`. -/
theorem example_9_C_3_unique {γ : ℝ} (hγ : 0 < γ) {F : Fin 2 → Fin 2 → Fin 3 → ℝ}
    {μ : List (Fin 3) → ℝ} (hW : IsWeakPBE (fig9C3 γ) F μ) :
    F 0 0 0 = 0 ∧ F 0 0 1 = 2 / 3 ∧ F 0 0 2 = 1 / 3 ∧ F 1 1 0 = 1 / (γ + 2) ∧
      μ [1] = 2 / 3 := by
  obtain ⟨hp0, hp1, hp2, hsum, hq0, hq1, hμa, hμb, hIf, hIa, hE0, hE1, hE2, hB⟩ :=
    fig9C3_scalar hW
  obtain ⟨b1, b2, b0⟩ := fig9C3_best hp0 hp1 hp2 hsum hE0 hE1 hE2
  rcases lt_trichotomy (μ [1]) (2 / 3) with hlt | heq | hgt
  · exfalso
    have hq := fig9C3_acc hq0 hlt hIa
    rw [hq] at hE1 hE2 hE0
    have h1 : F 0 0 1 = 1 := by nlinarith
    have := hB (by linarith)
    rw [h1, show F 0 0 2 = 0 by linarith] at this
    norm_num at this
    linarith
  · have hpos : 0 < F 0 0 1 + F 0 0 2 := by
      by_contra hn
      push Not at hn
      have h1 : F 0 0 1 = 0 := by linarith
      have h2 : F 0 0 2 = 0 := by linarith
      rw [h1, h2] at hE1 hE2
      nlinarith
    have hb1 := hB hpos
    have hratio : F 0 0 1 = 2 * F 0 0 2 := by
      rw [heq] at hb1
      field_simp at hb1
      linarith
    have hp2pos : 0 < F 0 0 2 := by linarith
    have e1 := b1 (by linarith)
    have e2 := b2 hp2pos
    have hqv : F 1 1 0 * (γ + 2) = 1 := by linear_combination e1 - e2
    have hγ2 : γ + 2 ≠ 0 := by linarith
    have hqf : F 1 1 0 = 1 / (γ + 2) := by field_simp; linarith
    have hqhalf : F 1 1 0 < 1 / 2 := by
      rw [hqf, div_lt_div_iff₀ (by linarith) (by norm_num)]
      linarith
    have hp00 : F 0 0 0 = 0 := by
      by_contra hne
      have := b0 (lt_of_le_of_ne hp0 (Ne.symm hne))
      linarith
    exact ⟨hp00, by linarith, by linarith, hqf, heq⟩
  · exfalso
    have hq := fig9C3_fight hq1 hgt hIf
    rw [hq] at hE2
    norm_num at hE2
    have hp2le : F 0 0 2 ≤ 1 := by linarith
    have hz1 : F 0 0 1 = 0 := by nlinarith [mul_nonneg hγ.le (sub_nonneg.2 hp2le)]
    have hpin : F 0 0 2 = 1 := by
      by_contra hne
      have : F 0 0 2 < 1 := lt_of_le_of_ne hp2le hne
      nlinarith [mul_pos hγ (sub_pos.2 this)]
    have := hB (by linarith)
    rw [hpin, hz1] at this
    norm_num at this
    linarith

/-- Sufficient conditions for a weak PBE of the entry game with two entry strategies: no
profitable pure deviation at either information set, and Bayes' rule at I's information set
when it is reached. -/
theorem entryTwo_weakPBE_of {F : Fin 2 → Fin 2 → Fin 3 → ℝ} {μ : List (Fin 3) → ℝ}
    (hF : IsBehaviorProfile (entryTwo o t) F) (hμ0 : μ [] = 1) (hμ1 : μ [1] + μ [2] = 1)
    (hμa : 0 ≤ μ [1]) (hμb : 0 ≤ μ [2])
    (hIf : μ [1] * t 0 0 1 + μ [2] * t 1 0 1 ≤
      μ [1] * (F 1 1 0 * t 0 0 1 + F 1 1 1 * t 0 1 1) +
        μ [2] * (F 1 1 0 * t 1 0 1 + F 1 1 1 * t 1 1 1))
    (hIa : μ [1] * t 0 1 1 + μ [2] * t 1 1 1 ≤
      μ [1] * (F 1 1 0 * t 0 0 1 + F 1 1 1 * t 0 1 1) +
        μ [2] * (F 1 1 0 * t 1 0 1 + F 1 1 1 * t 1 1 1))
    (hE : ∀ v ∈ ({o 0, F 1 1 0 * t 0 0 0 + F 1 1 1 * t 0 1 0,
      F 1 1 0 * t 1 0 0 + F 1 1 1 * t 1 1 0} : Set ℝ),
      v ≤ F 0 0 0 * o 0 + F 0 0 1 * (F 1 1 0 * t 0 0 0 + F 1 1 1 * t 0 1 0) +
        F 0 0 2 * (F 1 1 0 * t 1 0 0 + F 1 1 1 * t 1 1 0))
    (hB : 0 < F 0 0 1 + F 0 0 2 → μ [1] = F 0 0 1 / (F 0 0 1 + F 0 0 2) ∧
      μ [2] = F 0 0 2 / (F 0 0 1 + F 0 0 2)) :
    IsWeakPBE (entryTwo o t) F μ := by
  have hI := entryTwo_infoSet o t
  have hc := entryTwo_cont o t
  have hcp := entryTwo_condPayoff o t
  have hr := entryTwo_reach o t
  have hdn : (entryTwo o t).decisionNodes = {[], [1], [2]} :=
    (by decide : (entryTwo (fun _ => 0) (fun _ _ _ => 0)).decisionNodes = {[], [1], [2]})
  refine ⟨hF, ⟨fun x hx => ?_, Fin.forall_fin_two.2 ⟨by simp [hI.1, hμ0], by simp [hI.2, hμ1]⟩⟩,
    Fin.forall_fin_two.2 ⟨fun i hi g hg => ?_, fun i hi g hg => ?_⟩,
    Fin.forall_fin_two.2 ⟨fun hk x hx => ?_, fun hk x hx => ?_⟩⟩
  · have hx' := (mem_decisionNodes _).2 hx
    rw [hdn] at hx'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
    rcases hx' with rfl | rfl | rfl
    · rw [hμ0]; norm_num
    · exact ⟨hμa, by linarith⟩
    · exact ⟨hμb, by linarith⟩
  · obtain rfl : i = 0 := (Option.some.inj hi).symm
    obtain ⟨g0, g1⟩ := entryTwo_beh0 o t hg
    rw [(hcp _ _ _).1, (hcp _ _ _).1, (hc _ _).2.2, (hc _ _).2.2]
    simp only [entryTwo_assemble, Function.update_self, hμ0, one_mul]
    rw [Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)]
    have e0 := hE _ (Set.mem_insert _ _)
    have e1 := hE _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    have e2 := hE _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
    have hs : ∀ V : ℝ, (g 0 0 + g 0 1 + g 0 2) * V = V := fun V => by rw [g1, one_mul]
    nlinarith [mul_le_mul_of_nonneg_left e0 (g0 0), mul_le_mul_of_nonneg_left e1 (g0 1),
      mul_le_mul_of_nonneg_left e2 (g0 2), hs (F 0 0 0 * o 0 +
        F 0 0 1 * (F 1 1 0 * t 0 0 0 + F 1 1 1 * t 0 1 0) +
        F 0 0 2 * (F 1 1 0 * t 1 0 0 + F 1 1 1 * t 1 1 0))]
  · obtain rfl : i = 1 := (Option.some.inj hi).symm
    obtain ⟨g0, g1⟩ := entryTwo_beh1 o t hg
    rw [(hcp _ _ _).2, (hcp _ _ _).2, (hc _ _).1, (hc _ _).1, (hc _ _).2.1, (hc _ _).2.1]
    simp only [entryTwo_assemble, Function.update_self]
    have hs : ∀ V : ℝ, (g 1 0 + g 1 1) * V = V := fun V => by rw [g1, one_mul]
    nlinarith [mul_le_mul_of_nonneg_left hIf (g0 0), mul_le_mul_of_nonneg_left hIa (g0 1),
      hs (μ [1] * (F 1 1 0 * t 0 0 1 + F 1 1 1 * t 0 1 1) +
        μ [2] * (F 1 1 0 * t 1 0 1 + F 1 1 1 * t 1 1 1))]
  · rw [hI.1] at hx
    simp only [Finset.mem_singleton] at hx
    subst hx
    simp [probInfo, hI.1, hμ0]
  · rw [hI.2] at hx
    rw [(hr _).2.2, entryTwo_assemble] at hk ⊢
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · rw [(hr _).1, entryTwo_assemble]; exact (hB hk).1
    · rw [(hr _).2.1, entryTwo_assemble]; exact (hB hk).2

/-- The profile of Example 9.C.3: E plays `(0, 2/3, 1/3)`, I fights with probability
`1/(γ + 2)`. -/
noncomputable def fig9C3Profile (γ : ℝ) : Fin 2 → Fin 2 → Fin 3 → ℝ :=
  fun i _ => if i = 0 then ![0, 2 / 3, 1 / 3] else ![1 / (γ + 2), (γ + 1) / (γ + 2), 0]

/-- The beliefs of Example 9.C.3: `μ₁ = 2/3`. -/
noncomputable def fig9C3Belief (x : List (Fin 3)) : ℝ :=
  if x = [1] then 2 / 3 else if x = [2] then 1 / 3 else 1

/-- **Example 9.C.3** (MWG, p. 288). For `γ > 0`, `(σ₀, σ₁, σ₂) = (0, 2/3, 1/3)`,
`σ_F = 1/(γ + 2)` and `μ₁ = 2/3` form a weak perfect Bayesian equilibrium (the unique one by
`example_9_C_3_unique`). The same holds for `γ ≥ −2/3` (used in Exercise 9.C.2). -/
theorem example_9_C_3_exists {γ : ℝ} (hγ : -2 / 3 ≤ γ) :
    IsWeakPBE (fig9C3 γ) (fig9C3Profile γ) fig9C3Belief := by
  have hγ2 : γ + 2 ≠ 0 := by linarith
  have hpos : 0 < γ + 2 := by linarith
  have v00 : fig9C3Profile γ 0 0 0 = 0 := rfl
  have v01 : fig9C3Profile γ 0 0 1 = 2 / 3 := rfl
  have v02 : fig9C3Profile γ 0 0 2 = 1 / 3 := rfl
  have v10 : fig9C3Profile γ 1 1 0 = 1 / (γ + 2) := rfl
  have v11 : fig9C3Profile γ 1 1 1 = (γ + 1) / (γ + 2) := rfl
  have v12 : fig9C3Profile γ 1 1 2 = 0 := rfl
  have m0 : fig9C3Belief [] = 1 := rfl
  have m1 : fig9C3Belief [1] = 2 / 3 := rfl
  have m2 : fig9C3Belief [2] = 1 / 3 := rfl
  have hval : (1 / (γ + 2)) * (-1) + (γ + 1) / (γ + 2) * 3 = (3 * γ + 2) / (γ + 2) ∧
      (1 / (γ + 2)) * γ + (γ + 1) / (γ + 2) * 2 = (3 * γ + 2) / (γ + 2) := by
    constructor <;> field_simp <;> ring
  have hV : 0 ≤ (3 * γ + 2) / (γ + 2) := div_nonneg (by linarith) hpos.le
  refine entryTwo_weakPBE_of _ _ ?_ m0 (by rw [m1, m2]; norm_num) (by rw [m1]; norm_num)
    (by rw [m2]; norm_num) ?_ ?_ ?_ ?_
  · refine Fin.forall_fin_two.2 ⟨fun k hk => ?_, fun k hk => ?_⟩
    · obtain rfl : k = 0 := by simpa [entryTwo] using hk
      refine ⟨fun a => ?_, fun a ha => by simp [entryTwo] at ha, ?_⟩
      · fin_cases a <;> norm_num [fig9C3Profile]
      · simp only [entryTwo, ↓reduceIte, Fin.sum_univ_three, v00, v01, v02]
        norm_num
    · obtain rfl : k = 1 := by simpa [entryTwo] using hk
      have hav : (fig9C3 γ).avail 1 = {0, 1} := rfl
      refine ⟨fun a => ?_, fun a ha => ?_, ?_⟩
      · fin_cases a
        · exact v10 ▸ by positivity
        · exact v11 ▸ div_nonneg (by linarith) hpos.le
        · exact v12 ▸ le_rfl
      · fin_cases a <;> simp [hav] at ha
        exact v12
      · rw [hav, Finset.sum_pair (by decide), v10, v11]
        field_simp
        ring
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, m1, m2, v10, v11]
    field_simp
    ring_nf
    exact le_rfl
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, m1, m2, v10, v11]
    field_simp
    ring_nf
    exact le_rfl
  · intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, v00, v01, v02,
      v10, v11, hval.1, hval.2]
    rcases hv with rfl | rfl | rfl
    · simp only [Matrix.cons_val_zero]
      linarith
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, v10, v11, hval.1]
      linarith
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, v10, v11, hval.2]
      linarith
  · intro _
    rw [m1, m2, v01, v02]
    norm_num

/-- **Exercise 9.C.2** (MWG, p. 304). For `γ ∈ (−1, 0)` every weak PBE of the game of
Example 9.C.3 is of one of two kinds: (i) E stays out, and either `μ₁ > 2/3` and I fights for
sure, or `μ₁ = 2/3` and I fights with probability `σ_F ≥ 3/4` and `(2 − γ) σ_F ≥ 2`; or
(ii) `γ ≥ −2/3`, `μ₁ = 2/3`, `σ_F = 1/(γ + 2)` and E enters with In₁ twice as likely as
In₂. -/
theorem exercise_9_C_2 {γ : ℝ} (hγ1 : -1 < γ) (hγ0 : γ < 0) {F : Fin 2 → Fin 2 → Fin 3 → ℝ}
    {μ : List (Fin 3) → ℝ} (hW : IsWeakPBE (fig9C3 γ) F μ) :
    (F 0 0 1 = 0 ∧ F 0 0 2 = 0 ∧ ((2 / 3 < μ [1] ∧ F 1 1 0 = 1) ∨
      (μ [1] = 2 / 3 ∧ 3 / 4 ≤ F 1 1 0 ∧ 2 ≤ (2 - γ) * F 1 1 0))) ∨
    (μ [1] = 2 / 3 ∧ -2 / 3 ≤ γ ∧ F 1 1 0 * (γ + 2) = 1 ∧ F 0 0 1 = 2 * F 0 0 2 ∧
      0 < F 0 0 2) := by
  obtain ⟨hp0, hp1, hp2, hsum, hq0, hq1, hμa, hμb, hIf, hIa, hE0, hE1, hE2, hB⟩ :=
    fig9C3_scalar hW
  obtain ⟨b1, b2, -⟩ := fig9C3_best hp0 hp1 hp2 hsum hE0 hE1 hE2
  rcases lt_trichotomy (μ [1]) (2 / 3) with hlt | heq | hgt
  · exfalso
    have hq := fig9C3_acc hq0 hlt hIa
    rw [hq] at hE1
    have h1 : F 0 0 1 = 1 := by nlinarith
    have := hB (by linarith)
    rw [h1, show F 0 0 2 = 0 by linarith] at this
    norm_num at this
    linarith
  · by_cases hpos : 0 < F 0 0 1 + F 0 0 2
    · right
      have hb1 := hB hpos
      have hratio : F 0 0 1 = 2 * F 0 0 2 := by
        rw [heq] at hb1
        field_simp at hb1
        linarith
      have hp2pos : 0 < F 0 0 2 := by linarith
      have e1 := b1 (by linarith)
      have e2 := b2 hp2pos
      have hqv : F 1 1 0 * (γ + 2) = 1 := by linear_combination e1 - e2
      have hq34 : F 1 1 0 ≤ 3 / 4 := by linarith
      refine ⟨heq, ?_, hqv, hratio, hp2pos⟩
      nlinarith
    · left
      push Not at hpos
      have h1 : F 0 0 1 = 0 := by linarith
      have h2 : F 0 0 2 = 0 := by linarith
      rw [h1, h2] at hE1 hE2
      refine ⟨h1, h2, Or.inr ⟨heq, by linarith, by nlinarith⟩⟩
  · left
    have hq := fig9C3_fight hq1 hgt hIf
    rw [hq] at hE0
    norm_num at hE0
    have h1 : F 0 0 1 = 0 := by nlinarith
    have h2 : F 0 0 2 = 0 := by nlinarith
    exact ⟨h1, h2, Or.inl ⟨hgt, hq⟩⟩

/-- **Exercise 9.C.2** (MWG, p. 304). Both kinds occur: for `γ ∈ (−1, 0)`, E staying out with
I fighting and belief `1` on the left node is a weak PBE; for `γ ∈ [−2/3, 0)` so is the mixed
entry profile of Example 9.C.3. -/
theorem exercise_9_C_2_exists {γ : ℝ} (hγ0 : γ < 0) :
    IsWeakPBE (fig9C3 γ) (pureMoves ![0, 0]) leftBelief ∧
      (-2 / 3 ≤ γ → IsWeakPBE (fig9C3 γ) (fig9C3Profile γ) fig9C3Belief) := by
  refine ⟨?_, fun h => example_9_C_3_exists h⟩
  refine entryTwo_weakPBE_of _ _ (isBehaviorProfile_pureMoves fun k => by
    fin_cases k <;> simp [entryTwo]) (by simp [leftBelief]) (by simp [leftBelief])
    (by simp [leftBelief]) (by simp [leftBelief]) ?_ ?_ ?_ ?_
  · simp [leftBelief, pureMoves, dirac]
  · simp [leftBelief, pureMoves, dirac]
  · intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl <;> simp [pureMoves, dirac]
    linarith
  · intro h
    simp [pureMoves, dirac] at h

/-- **Figure 9.D.1(a)** (MWG, pp. 292-293): the entry game of Figure 9.C.1 in which I would
fight if E entered with In₁. -/
abbrev fig9D1a : ExtensiveForm (Fin 2) (Fin 3) (Fin 2) :=
  entryTwo ![0, 2] ![![![-3, -1], ![1, -2]], ![![-2, -1], ![3, 1]]]

/-- **Section 9.D, Figure 9.D.1(a)** (MWG, pp. 292-293). E staying out, I fighting after entry
and beliefs `[1]` on In₁ form a weak PBE; but In₁ is strictly dominated by In₂ for E whatever
I does after entry, so these beliefs are unreasonable (forward induction). -/
theorem figure_9_D_1a :
    IsWeakPBE fig9D1a (pureMoves ![0, 0]) leftBelief ∧
      ∀ q : ℝ, 0 ≤ q → q ≤ 1 → q * (-3) + (1 - q) * 1 < q * (-2) + (1 - q) * 3 := by
  refine ⟨?_, fun q _ hq1 => by linarith⟩
  refine entryTwo_weakPBE_of _ _ (isBehaviorProfile_pureMoves fun k => by
    fin_cases k <;> simp [entryTwo]) (by simp [leftBelief]) (by simp [leftBelief])
    (by simp [leftBelief]) (by simp [leftBelief]) ?_ ?_ ?_ ?_
  · simp [leftBelief, pureMoves, dirac]
  · simp [leftBelief, pureMoves, dirac]
  · intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl <;> simp [pureMoves, dirac]
  · intro h
    simp [pureMoves, dirac] at h

end MWG.DynamicGames

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Entry followed by a simultaneous-move game

MWG, Examples 9.B.3, 9.B.4 and 9.C.5 (Figures 9.B.4-9.B.7, 9.C.5, 9.D.3; pp. 273-279 and
289-295) and Exercise 9.B.6.

E chooses Out (`0`) or In (`1`) at information set `0`; after entry E chooses an action at
information set `1` and I, without observing it, an action at information set `2`
(`{[0, 1], [1, 1]}`). `entrySim o s` has payoffs `o` after Out and `s e f` when E plays `e` and
I plays `f` after entry.

* Example 9.B.3 (actions `0` = Fight, `1` = Accommodate): `example_9_B_3_nash` (the three pure
  Nash equilibria), `example_9_B_3_spne` (((in, accommodate), accommodate) is the unique SPNE:
  in the post-entry subgame accommodating is strictly dominant for E, then optimal for I).
* `example_9_C_5`: ((out, accommodate if in), fight if E plays "in") with beliefs on the
  "fight" node is a weak PBE that is not subgame perfect, and every sequential equilibrium has
  the unique SPNE strategies (Proposition 9.C.2).
* Example 9.B.4 (actions `0` = Small niche, `1` = Large niche): `example_9_B_4` (two pure
  SPNE), `exercise_9_B_6` (the mixed equilibrium of the post-entry subgame, with each firm
  choosing the small niche with probability `2/9`, and the SPNE in which E stays out).
* `figure_9_D_3`: entering to target the small niche is strictly dominated for E by staying
  out (forward induction).
-/

namespace MWG.DynamicGames

open MWG.NoncooperativeGames MWG.NoncooperativeGames.ExtensiveForm

/-- Payoffs of the entry game followed by a simultaneous-move game. -/
def entrySimPay (o : Fin 2 → ℝ) (s : Fin 2 → Fin 2 → Fin 2 → ℝ) (i : Fin 2)
    (z : List (Fin 2)) : ℝ :=
  if z = [0] then o i else if z = [0, 0, 1] then s 0 0 i else if z = [1, 0, 1] then s 0 1 i
  else if z = [0, 1, 1] then s 1 0 i else if z = [1, 1, 1] then s 1 1 i else 0

/-- The information set of a node of the entry game followed by a simultaneous-move game. -/
def entrySimInfo (x : List (Fin 2)) : Fin 3 := if x = [] then 0 else if x = [1] then 1 else 2

/-- **Figures 9.B.4 and 9.B.6** (MWG, pp. 274 and 279). Entry followed by a simultaneous-move
game between E and I. -/
def entrySim (o : Fin 2 → ℝ) (s : Fin 2 → Fin 2 → Fin 2 → ℝ) :
    ExtensiveForm (Fin 2) (Fin 2) (Fin 3) where
  nodes := {[], [0], [1], [0, 1], [1, 1], [0, 0, 1], [1, 0, 1], [0, 1, 1], [1, 1, 1]}
  nil_mem := by decide
  tail_mem := by decide
  info := entrySimInfo
  avail _ := Finset.univ
  avail_spec := by decide
  info_surj := by decide
  player k := if k = 2 then some 1 else some 0
  natureProb _ _ := 0
  nature_nonneg := fun k hk => absurd hk (by split_ifs <;> simp)
  nature_zero := fun k hk => absurd hk (by split_ifs <;> simp)
  nature_sum := fun k hk => absurd hk (by split_ifs <;> simp)
  payoff := entrySimPay o s

variable (o : Fin 2 → ℝ) (s : Fin 2 → Fin 2 → Fin 2 → ℝ)

theorem entrySim_assemble (F : Fin 2 → Fin 3 → Fin 2 → ℝ) :
    (entrySim o s).assemble F 0 = F 0 0 ∧ (entrySim o s).assemble F 1 = F 0 1 ∧
      (entrySim o s).assemble F 2 = F 1 2 :=
  ⟨(entrySim o s).assemble_of_some F rfl, (entrySim o s).assemble_of_some F rfl,
    (entrySim o s).assemble_of_some F rfl⟩

/-- Continuation payoffs of the entry game followed by a simultaneous-move game. -/
theorem entrySim_cont (f : Fin 3 → Fin 2 → ℝ) (i : Fin 2) :
    cont (entrySim o s) f [0, 1] i = f 2 0 * s 0 0 i + f 2 1 * s 0 1 i ∧
    cont (entrySim o s) f [1, 1] i = f 2 0 * s 1 0 i + f 2 1 * s 1 1 i ∧
    cont (entrySim o s) f [1] i = f 1 0 * (f 2 0 * s 0 0 i + f 2 1 * s 0 1 i) +
      f 1 1 * (f 2 0 * s 1 0 i + f 2 1 * s 1 1 i) ∧
    cont (entrySim o s) f [] i = f 0 0 * o i + f 0 1 * (f 1 0 * (f 2 0 * s 0 0 i +
      f 2 1 * s 0 1 i) + f 1 1 * (f 2 0 * s 1 0 i + f 2 1 * s 1 1 i)) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [cont_unfold, entrySim, entrySimPay, entrySimInfo, Fin.sum_univ_two]

theorem entrySim_decisionNodes : (entrySim o s).decisionNodes = {[], [1], [0, 1], [1, 1]} :=
  (by decide : (entrySim (fun _ => 0) (fun _ _ _ => 0)).decisionNodes =
    {[], [1], [0, 1], [1, 1]})

/-- The subgames of the entry game followed by a simultaneous-move game: the whole game and
the post-entry subgame (MWG, p. 275). -/
theorem entrySim_subgames (x : List (Fin 2)) :
    IsSubgameRoot (entrySim o s) x ↔ x = [] ∨ x = [1] := by
  have hdn := entrySim_decisionNodes o s
  have hdec : ∀ y, (entrySim o s).IsDecision y ↔ y = [] ∨ y = [1] ∨ y = [0, 1] ∨ y = [1, 1] :=
    fun y => by rw [← mem_decisionNodes, hdn]; simp
  constructor
  · intro h
    rcases (hdec x).1 h.1 with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd (h.2.1 [1, 1] ((hdec _).2 (by simp)) rfl) (by simp)
    · exact absurd (h.2.1 [0, 1] ((hdec _).2 (by simp)) rfl) (by simp)
  · have hinfo : ∀ y, (entrySim o s).info y = entrySimInfo y := fun _ => rfl
    rintro (rfl | rfl)
    · refine ⟨(hdec _).2 (by simp), fun y hy he => ?_, fun _ _ _ _ _ _ => List.nil_suffix⟩
      rcases (hdec y).1 hy with rfl | rfl | rfl | rfl <;> simp_all [entrySimInfo]
    · refine ⟨(hdec _).2 (by simp), fun y hy he => ?_, fun y hy hxy y' hy' he => ?_⟩
      · rcases (hdec y).1 hy with rfl | rfl | rfl | rfl <;> simp_all [entrySimInfo]
      · rcases (hdec y).1 hy with rfl | rfl | rfl | rfl <;>
        rcases (hdec y').1 hy' with rfl | rfl | rfl | rfl <;>
        simp_all [entrySimInfo]

theorem entrySim_beh (i : Fin 2) {g : Fin 3 → Fin 2 → ℝ}
    (hg : (entrySim o s).IsBehaviorStrategy i g) (k : Fin 3)
    (hk : (if k = 2 then some (1 : Fin 2) else some 0) = some i) :
    0 ≤ g k 0 ∧ 0 ≤ g k 1 ∧ g k 0 + g k 1 = 1 := by
  have h := hg k hk
  exact ⟨h.1 0, h.1 1, by simpa [entrySim] using h.2.2⟩

/-- The payoffs of Example 9.B.3 (`0` = Fight, `1` = Accommodate). -/
abbrev fig9B4 : ExtensiveForm (Fin 2) (Fin 2) (Fin 3) :=
  entrySim ![0, 2] ![![![-3, -1], ![1, -2]], ![![-2, -1], ![3, 1]]]

/-- **Example 9.B.3** (MWG, p. 273). The three pure strategy Nash equilibria:
((out, accommodate if in), fight if E plays "in"), ((out, fight if in), fight if E plays "in")
and ((in, accommodate if in), accommodate if E plays "in"). -/
theorem example_9_B_3_nash :
    IsNashB fig9B4 (pureMoves ![0, 1, 0]) ∧ IsNashB fig9B4 (pureMoves ![0, 0, 0]) ∧
      IsNashB fig9B4 (pureMoves ![1, 1, 1]) := by
  have hc := entrySim_cont ![0, 2] ![![![-3, -1], ![1, -2]], ![![-2, -1], ![3, 1]]]
  have hB : ∀ c : Fin 3 → Fin 2, IsBehaviorProfile fig9B4 (pureMoves (I := Fin 2) c) :=
    fun c => isBehaviorProfile_pureMoves fun _ => Finset.mem_univ _
  refine ⟨⟨hB _, ?_⟩, ⟨hB _, ?_⟩, ⟨hB _, ?_⟩⟩ <;>
  · rw [Fin.forall_fin_two]
    constructor <;> intro g hg
    · obtain ⟨a0, a1, a2⟩ := entrySim_beh _ _ 0 hg 0 (by simp)
      obtain ⟨b0, b1, b2⟩ := entrySim_beh _ _ 0 hg 1 (by simp)
      simp [(hc _ _).2.2.2, entrySim_assemble, pureMoves, dirac]
      nlinarith [mul_nonneg a0 b0, mul_nonneg a1 b0, mul_nonneg a0 b1, mul_nonneg a1 b1]
    · obtain ⟨a0, a1, a2⟩ := entrySim_beh _ _ 1 hg 2 (by simp)
      simp [(hc _ _).2.2.2, entrySim_assemble, pureMoves, dirac] <;>
      nlinarith

/-- **Example 9.B.3** (MWG, pp. 275 and 278). ((in, accommodate if in), accommodate if E plays
"in") is the unique subgame perfect Nash equilibrium: in the post-entry subgame accommodating
is strictly dominant for E, so I accommodates, and then E enters. -/
theorem example_9_B_3_spne :
    IsSPNE fig9B4 (pureMoves ![1, 1, 1]) ∧ ∀ F, IsSPNE fig9B4 F →
      F 0 0 1 = 1 ∧ F 0 1 1 = 1 ∧ F 1 2 1 = 1 := by
  have hc := entrySim_cont ![0, 2] ![![![-3, -1], ![1, -2]], ![![-2, -1], ![3, 1]]]
  have hsub := entrySim_subgames ![0, 2] ![![![-3, -1], ![1, -2]], ![![-2, -1], ![3, 1]]]
  constructor
  · refine ⟨isBehaviorProfile_pureMoves fun _ => Finset.mem_univ _, fun x hx => ?_⟩
    rcases (hsub x).1 hx with rfl | rfl <;> rw [InducesNashAt, Fin.forall_fin_two] <;>
      constructor <;> intro g hg
    · obtain ⟨a0, a1, a2⟩ := entrySim_beh _ _ 0 hg 0 (by simp)
      obtain ⟨b0, b1, b2⟩ := entrySim_beh _ _ 0 hg 1 (by simp)
      simp [(hc _ _).2.2.2, entrySim_assemble, pureMoves, dirac]
      nlinarith [mul_nonneg a0 b0, mul_nonneg a1 b0, mul_nonneg a0 b1, mul_nonneg a1 b1]
    · obtain ⟨a0, a1, a2⟩ := entrySim_beh _ _ 1 hg 2 (by simp)
      simp [(hc _ _).2.2.2, entrySim_assemble, pureMoves, dirac]
      nlinarith
    · obtain ⟨b0, b1, b2⟩ := entrySim_beh _ _ 0 hg 1 (by simp)
      simp [(hc _ _).2.2.1, entrySim_assemble, pureMoves, dirac]
      nlinarith
    · obtain ⟨a0, a1, a2⟩ := entrySim_beh _ _ 1 hg 2 (by simp)
      simp [(hc _ _).2.2.1, entrySim_assemble, pureMoves, dirac]
      nlinarith
  · intro F hF
    have hb0 := entrySim_beh _ _ 0 (hF.1 0) 0 (by simp)
    have hb1 := entrySim_beh _ _ 0 (hF.1 0) 1 (by simp)
    have hb2 := entrySim_beh _ _ 1 (hF.1 1) 2 (by simp)
    have hdev : ∀ (i : Fin 2) (k : Fin 3) (a : Fin 2),
        (if k = 2 then some (1 : Fin 2) else some 0) = some i →
        fig9B4.IsBehaviorStrategy i (Function.update (F i) k (dirac a)) := by
      intro i k a hk k' hk'
      by_cases hkk : k' = k
      · subst hkk
        simp only [Function.update_self]
        exact (isBehaviorProfile_pureMoves (I := Fin 2) (G := fig9B4) (c := fun _ => a)
          fun _ => Finset.mem_univ _) i k' hk'
      · rw [Function.update_of_ne hkk]
        exact hF.1 i k' hk'
    -- in the post-entry subgame E accommodates
    have hE1 := hF.2 [1] ((hsub _).2 (Or.inr rfl)) 0 _ (hdev 0 1 1 (by simp))
    simp [(hc _ _).2.2.1, entrySim_assemble, dirac] at hE1
    have hp : F 0 1 1 = 1 := by nlinarith [mul_nonneg hb1.1 hb2.2.1]
    -- then I accommodates
    have hI1 := hF.2 [1] ((hsub _).2 (Or.inr rfl)) 1 _ (hdev 1 2 1 (by simp))
    simp [(hc _ _).2.2.1, entrySim_assemble, hp, show F 0 1 0 = 0 by linarith, dirac] at hI1
    have hq : F 1 2 1 = 1 := by nlinarith
    -- then E enters
    have hE0 := hF.2 [] ((hsub _).2 (Or.inl rfl)) 0 _ (hdev 0 0 1 (by simp))
    simp [(hc _ _).2.2.2, entrySim_assemble, hp, hq, show F 0 1 0 = 0 by linarith,
      show F 1 2 0 = 0 by linarith, dirac] at hE0
    exact ⟨by nlinarith, hp, hq⟩

theorem entrySim_infoSet : (entrySim o s).infoSet 0 = {[]} ∧ (entrySim o s).infoSet 1 = {[1]} ∧
    (entrySim o s).infoSet 2 = {[0, 1], [1, 1]} :=
  ⟨(by decide : (entrySim (fun _ => 0) (fun _ _ _ => 0)).infoSet 0 = {[]}),
    (by decide : (entrySim (fun _ => 0) (fun _ _ _ => 0)).infoSet 1 = {[1]}),
    (by decide : (entrySim (fun _ => 0) (fun _ _ _ => 0)).infoSet 2 = {[0, 1], [1, 1]})⟩

theorem entrySim_reach (f : Fin 3 → Fin 2 → ℝ) :
    (entrySim o s).reach f [] = 1 ∧ (entrySim o s).reach f [1] = f 0 1 ∧
      (entrySim o s).reach f [0, 1] = f 0 1 * f 1 0 ∧
      (entrySim o s).reach f [1, 1] = f 0 1 * f 1 1 := by
  refine ⟨rfl, ?_, ?_, ?_⟩ <;> simp [entrySim, entrySimInfo]

theorem fin3_cases {P : Fin 3 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) (k : Fin 3) : P k := by
  fin_cases k
  · exact h0
  · exact h1
  · exact h2

theorem entrySim_perfectRecall : (entrySim o s).PerfectRecall := by
  have : (entrySim (fun _ => 0) (fun _ _ _ => 0)).PerfectRecall := by
    refine ⟨by unfold ExtensiveForm.NoAbsentMindedness; decide, fun i => ?_⟩
    unfold ExtensiveForm.RecallFor
    fin_cases i <;> decide
  exact this

/-- The beliefs of Figure 9.C.5: I believes that E fought. -/
def fightBelief (x : List (Fin 2)) : ℝ := if x = [1, 1] then 0 else 1

/-- **Example 9.C.5, Figure 9.C.5** (MWG, pp. 289-291). ((out, accommodate if in), fight if E
plays "in") with I's beliefs putting probability one on E having fought is a weak perfect
Bayesian equilibrium, but it is not subgame perfect. The unique sequential equilibrium
strategies are those of the unique SPNE ((in, accommodate), accommodate) (Proposition 9.C.2),
and a sequential equilibrium exists. -/
theorem example_9_C_5 :
    IsWeakPBE fig9B4 (pureMoves ![0, 1, 0]) fightBelief ∧
    ¬ IsSPNE fig9B4 (pureMoves ![0, 1, 0]) ∧
    (∀ F μ, IsSequentialEq fig9B4 F μ → F 0 0 1 = 1 ∧ F 0 1 1 = 1 ∧ F 1 2 1 = 1) ∧
    ∃ F μ, IsSequentialEq fig9B4 F μ := by
  have hc := entrySim_cont ![0, 2] ![![![-3, -1], ![1, -2]], ![![-2, -1], ![3, 1]]]
  have hI := entrySim_infoSet ![0, 2] ![![![-3, -1], ![1, -2]], ![![-2, -1], ![3, 1]]]
  have hdn := entrySim_decisionNodes ![0, 2] ![![![-3, -1], ![1, -2]], ![![-2, -1], ![3, 1]]]
  have hsub := entrySim_subgames ![0, 2] ![![![-3, -1], ![1, -2]], ![![-2, -1], ![3, 1]]]
  have hPR : fig9B4.PerfectRecall := entrySim_perfectRecall _ _
  have hr := entrySim_reach ![0, 2] ![![![-3, -1], ![1, -2]], ![![-2, -1], ![3, 1]]]
  have hN : NatureFullSupport fig9B4 := fun k hk =>
    absurd hk (by simp only [fig9B4, entrySim]; split_ifs <;> simp)
  have hB := isBehaviorProfile_pureMoves (I := Fin 2) (G := fig9B4) (c := ![0, 1, 0])
    fun _ => Finset.mem_univ _
  refine ⟨⟨hB, ⟨fun x hx => ?_, ?_⟩, ?_, ?_⟩, fun h => ?_, fun F μ hFμ => ?_, ?_⟩
  · unfold fightBelief; split_ifs <;> norm_num
  · exact fin3_cases (by simp [hI.1, fightBelief]) (by simp [hI.2.1, fightBelief])
      (by simp [hI.2.2, fightBelief])
  · intro k i hi g hg
    fin_cases k
    · obtain rfl : i = 0 := (Option.some.inj hi).symm
      obtain ⟨a0, a1, a2⟩ := entrySim_beh _ _ 0 hg 0 (by simp)
      obtain ⟨b0, b1, b2⟩ := entrySim_beh _ _ 0 hg 1 (by simp)
      simp [condPayoff, hI.1, fightBelief, (hc _ _).2.2.2, entrySim_assemble, pureMoves, dirac]
      nlinarith [mul_nonneg a1 b0, mul_nonneg a1 b1]
    · obtain rfl : i = 0 := (Option.some.inj hi).symm
      obtain ⟨b0, b1, b2⟩ := entrySim_beh _ _ 0 hg 1 (by simp)
      simp [condPayoff, hI.2.1, fightBelief, (hc _ _).2.2.1, entrySim_assemble, pureMoves,
        dirac]
      nlinarith
    · obtain rfl : i = 1 := (Option.some.inj hi).symm
      obtain ⟨c0, c1, c2⟩ := entrySim_beh _ _ 1 hg 2 (by simp)
      simp [condPayoff, hI.2.2, fightBelief, (hc _ _).1, entrySim_assemble,
        pureMoves, dirac]
      nlinarith
  · refine fin3_cases (fun hk x hx => ?_) (fun hk x hx => ?_) (fun hk x hx => ?_)
    · rw [hI.1] at hx
      simp only [Finset.mem_singleton] at hx
      subst hx
      simp [probInfo, hI.1, fightBelief]
    · exfalso
      simp [probInfo, hI.2.1, (hr _).2.1, entrySim_assemble, pureMoves, dirac] at hk
    · exfalso
      simp [probInfo, hI.2.2, (hr _).2.2.1, (hr _).2.2.2, entrySim_assemble, pureMoves,
        dirac] at hk
  · have := h.2 [1] ((hsub _).2 (Or.inr rfl)) 1 (fun _ => dirac 1)
      (fun k hk => (isBehaviorProfile_pureMoves (I := Fin 2) (G := fig9B4)
        (c := fun _ => (1 : Fin 2)) fun _ => Finset.mem_univ _) 1 k hk)
    simp [(hc _ _).2.2.1, entrySim_assemble, pureMoves, dirac] at this
    norm_num at this
  · exact (example_9_B_3_spne.2 F (proposition_9_C_2 _ hPR hFμ))
  · exact exists_isSequentialEq _ hPR hN

/-- The payoffs of the Niche Choice game, Example 9.B.4 (`0` = Small niche, `1` = Large
niche). -/
abbrev nicheGame : ExtensiveForm (Fin 2) (Fin 2) (Fin 3) :=
  entrySim ![0, 2] ![![![-6, -6], ![-1, 1]], ![![1, -1], ![-3, -3]]]

/-- **Example 9.B.4, Figures 9.B.6-9.B.7** (MWG, pp. 278-279). The Niche Choice game has the
two pure strategy SPNE ((in, large niche if in), small niche if E plays "in") and ((out, small
niche if in), large niche if E plays "in"). -/
theorem example_9_B_4 :
    IsSPNE nicheGame (pureMoves ![1, 1, 0]) ∧ IsSPNE nicheGame (pureMoves ![0, 0, 1]) := by
  have hc := entrySim_cont ![0, 2] ![![![-6, -6], ![-1, 1]], ![![1, -1], ![-3, -3]]]
  have hsub := entrySim_subgames ![0, 2] ![![![-6, -6], ![-1, 1]], ![![1, -1], ![-3, -3]]]
  constructor <;>
  · refine ⟨isBehaviorProfile_pureMoves fun _ => Finset.mem_univ _, fun x hx => ?_⟩
    rcases (hsub x).1 hx with rfl | rfl <;> rw [InducesNashAt, Fin.forall_fin_two] <;>
      constructor <;> intro g hg
    · obtain ⟨a0, a1, a2⟩ := entrySim_beh _ _ 0 hg 0 (by simp)
      obtain ⟨b0, b1, b2⟩ := entrySim_beh _ _ 0 hg 1 (by simp)
      simp [(hc _ _).2.2.2, entrySim_assemble, pureMoves, dirac]
      nlinarith [mul_nonneg a0 b0, mul_nonneg a1 b0, mul_nonneg a0 b1, mul_nonneg a1 b1]
    · obtain ⟨a0, a1, a2⟩ := entrySim_beh _ _ 1 hg 2 (by simp)
      simp [(hc _ _).2.2.2, entrySim_assemble, pureMoves, dirac] <;>
      nlinarith
    · obtain ⟨b0, b1, b2⟩ := entrySim_beh _ _ 0 hg 1 (by simp)
      simp [(hc _ _).2.2.1, entrySim_assemble, pureMoves, dirac]
      nlinarith
    · obtain ⟨a0, a1, a2⟩ := entrySim_beh _ _ 1 hg 2 (by simp)
      simp [(hc _ _).2.2.1, entrySim_assemble, pureMoves, dirac]
      nlinarith

/-- The profile of Exercise 9.B.6: E stays out; after entry each firm targets the small niche
with probability `2/9`. -/
noncomputable def nicheMixed : Fin 2 → Fin 3 → Fin 2 → ℝ :=
  fun _ k => if k = 0 then ![1, 0] else ![2 / 9, 7 / 9]

/-- **Exercise 9.B.6** (MWG, p. 302). In the post-entry subgame of the Niche Choice game there
is a mixed equilibrium in which each firm chooses the small niche with probability `2/9`; it
gives E the payoff `−19/9 < 0`. Hence there is an SPNE inducing it, in which E stays out, and
in every SPNE that induces this post-entry play E stays out. -/
theorem exercise_9_B_6 :
    cont nicheGame (nicheGame.assemble nicheMixed) [1] 0 = -19 / 9 ∧
    IsSPNE nicheGame nicheMixed ∧
    ∀ F, IsSPNE nicheGame F → F 0 1 = ![2 / 9, 7 / 9] → F 1 2 = ![2 / 9, 7 / 9] →
      F 0 0 0 = 1 := by
  have hc := entrySim_cont ![0, 2] ![![![-6, -6], ![-1, 1]], ![![1, -1], ![-3, -3]]]
  have hsub := entrySim_subgames ![0, 2] ![![![-6, -6], ![-1, 1]], ![![1, -1], ![-3, -3]]]
  have hval : nicheMixed 0 0 = ![1, 0] ∧ nicheMixed 0 1 = ![2 / 9, 7 / 9] ∧
      nicheMixed 1 2 = ![2 / 9, 7 / 9] := ⟨rfl, rfl, rfl⟩
  refine ⟨?_, ⟨fun i k _ => ?_, fun x hx => ?_⟩, fun F hF h1 h2 => ?_⟩
  · simp [(hc _ _).2.2.1, entrySim_assemble, hval]
    norm_num
  · refine ⟨fun a => ?_, fun a ha => absurd (Finset.mem_univ a) ha, ?_⟩
    · fin_cases a <;> simp [nicheMixed] <;> split_ifs <;> norm_num
    · simp [nicheMixed, entrySim, Fin.sum_univ_two]
      split_ifs <;> norm_num
  · rcases (hsub x).1 hx with rfl | rfl <;> rw [InducesNashAt, Fin.forall_fin_two] <;>
      constructor <;> intro g hg
    · obtain ⟨a0, a1, a2⟩ := entrySim_beh _ _ 0 hg 0 (by simp)
      obtain ⟨b0, b1, b2⟩ := entrySim_beh _ _ 0 hg 1 (by simp)
      simp [(hc _ _).2.2.2, entrySim_assemble, hval]
      nlinarith [mul_nonneg a1 b0, mul_nonneg a1 b1]
    · obtain ⟨a0, a1, a2⟩ := entrySim_beh _ _ 1 hg 2 (by simp)
      simp [(hc _ _).2.2.2, entrySim_assemble, hval]
    · obtain ⟨b0, b1, b2⟩ := entrySim_beh _ _ 0 hg 1 (by simp)
      simp [(hc _ _).2.2.1, entrySim_assemble, hval]
      nlinarith
    · obtain ⟨a0, a1, a2⟩ := entrySim_beh _ _ 1 hg 2 (by simp)
      simp [(hc _ _).2.2.1, entrySim_assemble, hval]
      nlinarith
  · have hb0 := entrySim_beh _ _ 0 (hF.1 0) 0 (by simp)
    have hdev : nicheGame.IsBehaviorStrategy 0 (Function.update (F 0) 0 (dirac 0)) := by
      intro k hk
      by_cases hkk : k = 0
      · subst hkk
        simp only [Function.update_self]
        exact (isBehaviorProfile_pureMoves (I := Fin 2) (G := nicheGame) (c := fun _ => 0)
          fun _ => Finset.mem_univ _) 0 0 hk
      · rw [Function.update_of_ne hkk]
        exact hF.1 0 k hk
    have := hF.2 [] ((hsub _).2 (Or.inl rfl)) 0 _ hdev
    simp [(hc _ _).2.2.2, entrySim_assemble, h1, h2, dirac] at this
    nlinarith

/-- **Section 9.D, Figure 9.D.3** (MWG, pp. 294-295). Entering and targeting the small niche
is strictly dominated for E by staying out, whatever I does after entry. -/
theorem figure_9_D_3 (q : ℝ) (hq0 : 0 ≤ q) :
    q * (-6) + (1 - q) * (-1) < 0 := by linarith

end MWG.DynamicGames

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# A three-player game of perfect information

MWG, Example 9.B.2 (Figure 9.B.3, pp. 271-272) and Exercises 9.B.1 and 9.B.3.

Players `0, 1, 2` are MWG's players 1, 2, 3. Information sets (singletons): `0` = player 1 at
the root (`L` = `0`, `R` = `1`); `1` = player 3 after `L`; `2` = player 2 after `R` (`a` = `0`,
`b` = `1`); `3` = player 3 after `R, a`; `4` = player 3 after `R, b` (`ℓ` = `0`, `r` = `1`).
A pure profile is a choice `c k ∈ {0, 1}` at each information set.

* `example_9_B_2`: backward induction gives `σ₁ = R`, `σ₂ = a`, and `σ₃ = r` after `L`, `r`
  after `(R, a)`, `ℓ` after `(R, b)`; it is the unique SPNE (Proposition 9.B.2: no player has
  equal payoffs at two terminal nodes).
* `exercise_9_B_1`: the game has five subgames, one for each decision node.
* `exercise_9_B_3`: the pure strategy Nash equilibria (with pure deviations, Definition 8.D.1
  for the induced normal form) are exactly six profiles; the backward-induction profile is one
  of them, and the other five are not subgame perfect (they violate sequential rationality).
-/

namespace MWG.DynamicGames

open MWG.NoncooperativeGames MWG.NoncooperativeGames.ExtensiveForm

/-- The information sets of Figure 9.B.3. -/
def threeInfo (x : List (Fin 2)) : Fin 5 :=
  if x = [0] then 1 else if x = [1] then 2 else if x = [0, 1] then 3 else if x = [1, 1] then 4
  else 0

/-- The payoffs `(u₁, u₂, u₃)` of Figure 9.B.3 as integers. -/
def threePayZ (z : List (Fin 2)) : Fin 3 → ℤ :=
  if z = [0, 0] then ![2, 0, 1] else if z = [1, 0] then ![-1, 5, 6]
  else if z = [0, 0, 1] then ![3, 1, 2] else if z = [1, 0, 1] then ![5, 4, 4]
  else if z = [0, 1, 1] then ![0, -1, 7] else if z = [1, 1, 1] then ![-2, 2, 0] else 0

/-- **Example 9.B.2, Figure 9.B.3(a)** (MWG, p. 271). A three-player finite game of perfect
information. -/
def threeGame : ExtensiveForm (Fin 3) (Fin 2) (Fin 5) where
  nodes := {[], [0], [1], [0, 0], [1, 0], [0, 1], [1, 1], [0, 0, 1], [1, 0, 1], [0, 1, 1],
    [1, 1, 1]}
  nil_mem := by decide
  tail_mem := by decide
  info := threeInfo
  avail _ := Finset.univ
  avail_spec := by decide
  info_surj := by decide
  player := ![some 0, some 2, some 1, some 2, some 2]
  natureProb _ _ := 0
  nature_nonneg := fun k hk => absurd hk (by fin_cases k <;> simp)
  nature_zero := fun k hk => absurd hk (by fin_cases k <;> simp)
  nature_sum := fun k hk => absurd hk (by fin_cases k <;> simp)
  payoff i z := threePayZ z i

theorem threeGame_nodes : threeGame.nodes = {[], [0], [1], [0, 0], [1, 0], [0, 1], [1, 1],
    [0, 0, 1], [1, 0, 1], [0, 1, 1], [1, 1, 1]} := rfl
theorem threeGame_info : threeGame.info = threeInfo := rfl
theorem threeGame_avail (k : Fin 5) : threeGame.avail k = Finset.univ := rfl
theorem threeGame_payoff (i : Fin 3) (z : List (Fin 2)) : threeGame.payoff i z = threePayZ z i :=
  rfl

/-- The payoff of the terminal node reached by the pure choices `c`. -/
def threeOutcome (c : Fin 5 → Fin 2) (i : Fin 3) : ℤ :=
  if c 0 = 0 then threePayZ [c 1, 0] i
  else if c 2 = 0 then threePayZ [c 3, 0, 1] i else threePayZ [c 4, 1, 1] i

theorem two_cases (x : Fin 2) : x = 0 ∨ x = 1 := by fin_cases x <;> simp

/-- The expected payoff of pure choices is the payoff of the terminal node they reach. -/
theorem threeGame_cont_pure (c : Fin 5 → Fin 2) (i : Fin 3) :
    cont threeGame (threeGame.assemble (pureMoves c)) [] i = threeOutcome c i := by
  have hasm : ∀ k, threeGame.assemble (pureMoves c) k = dirac (c k) := fun k => by
    fin_cases k <;> exact threeGame.assemble_of_some _ rfl
  rcases two_cases (c 0) with h0 | h0 <;> rcases two_cases (c 1) with h1 | h1 <;>
    rcases two_cases (c 2) with h2 | h2 <;> rcases two_cases (c 3) with h3 | h3 <;>
    rcases two_cases (c 4) with h4 | h4 <;>
    simp [cont_unfold, threeGame_nodes, threeGame_info, threeGame_avail, threeGame_payoff,
      threeInfo, hasm, dirac, h0, h1, h2, h3, h4, threeOutcome, threePayZ, Fin.sum_univ_two]

/-- Pure strategy Nash equilibrium (Definition 8.D.1 for the induced normal form): no player
gains by changing her choices at her own information sets. -/
def IsPureNash3 (c : Fin 5 → Fin 2) : Prop :=
  ∀ i c', (∀ k, threeGame.player k ≠ some i → c' k = c k) →
    cont threeGame (threeGame.assemble (pureMoves c')) [] i ≤
      cont threeGame (threeGame.assemble (pureMoves c)) [] i

/-- The backward-induction profile of Example 9.B.2. -/
def threeBI : Fin 5 → Fin 2 := ![1, 1, 0, 1, 0]

/-- **Exercise 9.B.3** (MWG, p. 301). The pure strategy Nash equilibria of the game of
Example 9.B.2 are exactly the six profiles `(σ₁; σ₃ after L; σ₂; σ₃ after (R,a); σ₃ after
(R,b))` = `(L; r; b; ℓ; r)`, `(L; r; b; r; r)`, `(R; ℓ; a; r; ℓ)`, `(R; ℓ; a; r; r)`,
`(R; r; a; r; ℓ)` (backward induction) and `(R; r; a; r; r)`. -/
theorem exercise_9_B_3_nash (c : Fin 5 → Fin 2) :
    IsPureNash3 c ↔ c ∈ ({![0, 1, 1, 0, 1], ![0, 1, 1, 1, 1], ![1, 0, 0, 1, 0],
      ![1, 0, 0, 1, 1], ![1, 1, 0, 1, 0], ![1, 1, 0, 1, 1]} : Finset (Fin 5 → Fin 2)) := by
  have key : IsPureNash3 c ↔ ∀ i c', (∀ k, threeGame.player k ≠ some i → c' k = c k) →
      threeOutcome c' i ≤ threeOutcome c i := by
    unfold IsPureNash3
    simp only [threeGame_cont_pure, Int.cast_le]
  rw [key]
  clear key
  have hp : ∀ k, threeGame.player k = ![some 0, some 2, some 1, some 2, some 2] k := fun _ => rfl
  simp only [hp]
  revert c
  decide

/-- **Example 9.B.2** (MWG, pp. 271-272). Backward induction identifies `σ₁ = R`, `σ₂ = a`
after `R`, and `σ₃ = r` after `L`, `r` after `(R, a)`, `ℓ` after `(R, b)`; this profile is the
unique subgame perfect Nash equilibrium (Proposition 9.B.2). -/
theorem example_9_B_2 :
    IsSPNE threeGame (pureMoves threeBI) ∧ ∀ F, IsSPNE threeGame F →
      ∀ k, threeGame.assemble F k = dirac (threeBI k) := by
  have hPI : threeGame.PerfectInformation := by
    unfold ExtensiveForm.PerfectInformation; decide
  have hB : IsBehaviorProfile threeGame (pureMoves (I := Fin 3) threeBI) :=
    isBehaviorProfile_pureMoves fun _ => Finset.mem_univ _
  have hasm : ∀ k, threeGame.assemble (pureMoves threeBI) k = dirac (threeBI k) := fun k => by
    fin_cases k <;> exact threeGame.assemble_of_some _ rfl
  have hasm' : ∀ k, threeGame.assemble (pureMoves ![1, 1, 0, 1, 0]) k =
      dirac (![1, 1, 0, 1, 0] k) := hasm
  have hS : IsSPNE threeGame (pureMoves threeBI) := by
    refine isSPNE_of_oneShotOptimal _ hB fun x hx j hj a _ => ?_
    have hx' := (mem_decisionNodes _).2 hx
    rw [show threeGame.decisionNodes = {[], [0], [1], [0, 1], [1, 1]} by decide] at hx'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
    rcases hx' with rfl | rfl | rfl | rfl | rfl <;>
    · cases hj
      rcases two_cases a with rfl | rfl <;>
        simp [cont_unfold, threeGame_nodes, threeGame_info, threeGame_avail, threeGame_payoff,
          threeInfo, hasm', dirac, threeBI, threePayZ, Fin.sum_univ_two] <;> norm_num
  refine ⟨hS, fun F hF k => ?_⟩
  rw [← hasm k]
  refine (proposition_9_B_2 _ hPI).2 (fun k => by fin_cases k <;> simp [threeGame])
    (fun i z hz z' hz' he => ?_) F _ hF hS k
  rw [show threeGame.terminals = {[0, 0], [1, 0], [0, 0, 1], [1, 0, 1], [0, 1, 1], [1, 1, 1]}
    by decide] at hz hz'
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz hz'
  simp only [threeGame] at he
  fin_cases i <;> rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hz' with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [threePayZ] at he ⊢ <;>
    norm_num at he

/-- **Exercise 9.B.1** (MWG, p. 301). The game of Example 9.B.2 has five subgames: every one of
its five decision nodes initiates a subgame (perfect information). -/
theorem exercise_9_B_1 :
    (∀ x, IsSubgameRoot threeGame x ↔ x ∈ threeGame.decisionNodes) ∧
      threeGame.decisionNodes.card = 5 := by
  have hPI : threeGame.PerfectInformation := by
    unfold ExtensiveForm.PerfectInformation; decide
  refine ⟨fun x => ⟨fun h => (mem_decisionNodes _).2 h.1, fun h =>
    isSubgameRoot_of_perfectInformation _ hPI ((mem_decisionNodes _).1 h)⟩, by decide⟩

/-- **Exercise 9.B.3** (MWG, p. 301). The backward-induction profile is a Nash equilibrium,
and the other five pure Nash equilibria are not subgame perfect: each prescribes, at some
decision node, a move that is not optimal given the continuation play (sequential
rationality fails). -/
theorem exercise_9_B_3 :
    IsPureNash3 threeBI ∧ ∀ c, IsPureNash3 c → c ≠ threeBI → ¬ IsSPNE threeGame (pureMoves c) := by
  refine ⟨(exercise_9_B_3_nash _).2 (by decide), fun c _ hne hS => hne ?_⟩
  funext k
  have h := example_9_B_2.2 _ hS k
  have hk : threeGame.assemble (pureMoves c) k = dirac (c k) := by
    fin_cases k <;> exact threeGame.assemble_of_some _ rfl
  rw [hk] at h
  have := congrFun h (c k)
  simp only [dirac, ite_true] at this
  split_ifs at this with h'
  · exact h'
  · norm_num at this

end MWG.DynamicGames

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Further examples and exercises of Chapter 9

* `proposition_9_B_3_instance`: Proposition 9.B.3 applied to Example 9.B.3 with the post-entry
  subgame: the SPNE restricted to the reduced game is an SPNE of the reduced game, and splicing
  back gives an SPNE (MWG, p. 278).
* `example_9_C_1_bayes`: the Bayes computation of p. 285: if E plays Out, In₁, In₂ with
  probabilities `1/4, 1/2, 1/4`, I's information set is reached with probability `3/4` and the
  conditional probabilities of its nodes are `2/3` and `1/3`.
* `figure_9_D_1b`: in the variant of the Niche Choice game of Figure 9.D.1(b), E staying out
  with I targeting the large niche and believing E chose the small niche is a weak PBE, while
  the small niche is strictly dominated by Out for E (MWG, pp. 292-293).
* `exercise_9_B_4_instance`: Exercise 9.B.4 applied to Matching Pennies Version B (Chapter 7),
  a two-player zero-sum game of perfect information.
* `rubinsteinHalf`, `example_9_AA_2_instance`, `example_9_AA_1_instance`: the bargaining
  games with `v = 1`, `δ = 1/2`, infinite horizon and horizon `3`.
* `exercise_9_B_5b`: in Maskin's game with player 1 moving first, player 2 has `m₂ ^ m₁`
  strategies (with simultaneous moves the strategies are the actions, `m₁` and `m₂`).
-/

namespace MWG.DynamicGames

open MWG.NoncooperativeGames MWG.NoncooperativeGames.ExtensiveForm

/-- **Proposition 9.B.3, an instance** (MWG, pp. 277-278). In Example 9.B.3, with `S` the
post-entry subgame: the unique SPNE restricted to the moves outside `S` is an SPNE of the
reduced game, and playing the subgame's SPNE in `S` and the reduced game's SPNE outside it
gives an SPNE of the whole game. -/
theorem proposition_9_B_3_instance :
    IsSPNEReduced fig9B4 [1] (pureMoves ![1, 1, 1]) (pureMoves ![1, 1, 1]) ∧
      IsSPNE fig9B4 (splice fig9B4 [1] (pureMoves ![1, 1, 1]) (pureMoves ![1, 1, 1])) := by
  have h := example_9_B_3_spne.1
  have hred := proposition_9_B_3_i fig9B4 h (x₀ := [1]) (fun _ _ => rfl)
  exact ⟨hred, proposition_9_B_3_ii fig9B4
    ((entrySim_subgames _ _ [1]).2 (Or.inr rfl)) (isSPNEIn_of_isSPNE fig9B4 h [1]) hred⟩

/-- **Section 9.C** (MWG, p. 285). In Example 9.C.1, if E plays Out, In₁ and In₂ with
probabilities `1/4, 1/2, 1/4`, I's information set is reached with probability `3/4`; by
Bayes' rule the left node has conditional probability `2/3` and the right node `1/3`. -/
theorem example_9_C_1_bayes (F : Fin 2 → Fin 2 → Fin 3 → ℝ) (hF : F 0 0 = ![1 / 4, 1 / 2, 1 / 4]) :
    probInfo fig9C1 (fig9C1.assemble F) 1 = 3 / 4 ∧
      bayesBelief fig9C1 (fig9C1.assemble F) [1] = 2 / 3 ∧
      bayesBelief fig9C1 (fig9C1.assemble F) [2] = 1 / 3 := by
  have hr := entryTwo_reach ![0, 2] ![![![-1, -1], ![3, 0]], ![![-1, -1], ![2, 1]]]
  have hasm : fig9C1.assemble F 0 = F 0 0 := entryTwo_assemble _ _ F 0
  have hi1 : fig9C1.info [1] = 1 := rfl
  have hi2 : fig9C1.info [2] = 1 := rfl
  unfold bayesBelief
  rw [hi1, hi2, (hr _).2.2, (hr _).1, (hr _).2.1, hasm, hF]
  norm_num

/-- **Figure 9.D.1(b)** (MWG, p. 293): E chooses Out, Small niche or Large niche; I, without
observing E's niche, chooses Small (`0`) or Large (`1`). -/
abbrev fig9D1b : ExtensiveForm (Fin 2) (Fin 3) (Fin 2) :=
  entryTwo ![0, 2] ![![![-6, -6], ![-1, 1]], ![![1, -1], ![-3, -3]]]

/-- **Section 9.D, Figure 9.D.1(b)** (MWG, pp. 292-293). E staying out, I targeting the large
niche and believing that E chose the small niche form a weak PBE; but the small niche is
strictly dominated for E by staying out (`−6` and `−1` are below `0`), so these beliefs are
unreasonable (forward induction). -/
theorem figure_9_D_1b :
    IsWeakPBE fig9D1b (pureMoves ![0, 1]) leftBelief ∧
      ∀ q : ℝ, 0 ≤ q → q ≤ 1 → q * (-6) + (1 - q) * (-1) < 0 := by
  refine ⟨?_, fun q _ hq1 => by linarith⟩
  refine entryTwo_weakPBE_of _ _ (isBehaviorProfile_pureMoves fun k => by
    fin_cases k <;> simp [entryTwo]) (by simp [leftBelief]) (by simp [leftBelief])
    (by simp [leftBelief]) (by simp [leftBelief]) ?_ ?_ ?_ ?_
  · norm_num [leftBelief, pureMoves, dirac]
  · norm_num [leftBelief, pureMoves, dirac]
  · intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl <;> simp [pureMoves, dirac]
  · intro h
    simp [pureMoves, dirac] at h

/-- **Exercise 9.B.5(b)** (MWG, p. 302). If player 1 moves first and player 2 observes her
move, player 1 has `m₁` strategies and player 2's strategies are the functions `M₁ → M₂`, of
which there are `m₂ ^ m₁`. -/
theorem exercise_9_B_5b (M₁ M₂ : Type*) [Fintype M₁] [DecidableEq M₁] [Fintype M₂] :
    Fintype.card (M₁ → M₂) = Fintype.card M₂ ^ Fintype.card M₁ := Fintype.card_fun

/-- **Exercise 9.B.4, an instance** (MWG, p. 302). Matching Pennies Version B (Chapter 7,
Figure 7.C.1) is a two-player zero-sum game of perfect information; it has a pure SPNE and all
its SPNE give the same payoffs. -/
theorem exercise_9_B_4_instance :
    ∃ F, IsSPNE matchingPenniesB F ∧ ∀ F', IsSPNE matchingPenniesB F' → ∀ i,
      cont matchingPenniesB (matchingPenniesB.assemble F') [] i =
        cont matchingPenniesB (matchingPenniesB.assemble F) [] i := by
  have hPI := example_7_C_1.1
  have hzs : ∀ z, matchingPenniesB.payoff 1 z = -matchingPenniesB.payoff 0 z := fun z => by
    simp [matchingPenniesB_payoff_def]
  obtain ⟨s, hs⟩ := (proposition_9_B_2 _ hPI).1
  exact ⟨pureB _ s, hs, fun F' hF' i =>
    exercise_9_B_4 hPI hzs hF' hs matchingPenniesB.nil_mem i⟩

/-- The bargaining game with `v = 1`, `δ₁ = δ₂ = 1/2` and horizon `T`. -/
noncomputable def bargainHalf (T : ℕ∞) : BargainingGame where
  v := 1
  δ := fun _ => 1 / 2
  T := T
  v_pos := one_pos
  δ_pos := fun _ => by norm_num
  δ_lt_one := fun _ => by norm_num

/-- **Example 9.AA.2, an instance** (MWG, p. 298). With `v = 1` and `δ = 1/2` the unique SPNE
of the infinite horizon game has the proposer offer `1/3` and keep `2/3`. -/
theorem example_9_AA_2_instance :
    (bargainHalf ⊤).IsSPNE (BargainingGame.threshold (bargainHalf ⊤).rubOffer) ∧
    ∀ σ, (bargainHalf ⊤).IsSPNE σ →
      σ.prop [] = 1 / 3 ∧ (bargainHalf ⊤).value σ [] 0 = 2 / 3 := by
  have h := (bargainHalf ⊤).example_9_AA_2 rfl rfl
  refine ⟨h.1, fun σ hσ => ?_⟩
  obtain ⟨hp, -, hv, -⟩ := h.2.2 σ hσ [] (bargainHalf ⊤).validHist_nil
  refine ⟨by rw [hp]; norm_num [bargainHalf], ?_⟩
  have : BargainingGame.proposer ([] : List ℝ).length = 0 := rfl
  rw [this] at hv
  rw [hv]
  norm_num [bargainHalf]

/-- **Example 9.AA.1, an instance** (MWG, p. 297). With `v = 1`, `δ = 1/2` and three periods,
player 1 earns `v₁*(3) = 1 − 1/2 + 1/4 = 3/4` in every SPNE. -/
theorem example_9_AA_1_instance :
    ∀ σ, (bargainHalf 3).IsSPNE σ → (bargainHalf 3).value σ [] 0 = 3 / 4 := by
  intro σ hσ
  have h := ((bargainHalf 3).example_9_AA_1 3 rfl rfl).2 σ hσ [] (bargainHalf 3).validHist_nil
    (by norm_num)
  have hp : BargainingGame.proposer ([] : List ℝ).length = 0 := rfl
  rw [hp] at h
  rw [h.1]
  norm_num [BargainingGame.finP, bargainHalf]

end MWG.DynamicGames

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Counterexamples to two printed claims of Section 9.B

* **Propositions 9.B.1 and 9.B.2** (MWG, pp. 272 and 276) claim uniqueness of the
  backward-induction profile and of the SPNE whenever no player has the same payoffs at two
  terminal nodes. With moves of nature this fails (`natureGame`): a single player chooses `L`
  (payoff `1`) or `R`, after which nature picks the payoff `0` or `2` with probability `1/2`.
  The three terminal payoffs are distinct, yet `L` and `R` are both derived through backward
  induction and both SPNE (`proposition_9_B_1_nature_counterexample`,
  `proposition_9_B_2_nature_counterexample`). The corrected statements (no moves of nature)
  are `proposition_9_B_1` and `proposition_9_B_2`.
* **Exercise 9.B.4** (MWG, p. 302) claims unique SPNE payoffs in finite zero-sum games of
  perfect information. With three players it fails (`zeroSum3Game`): player 1 chooses between
  payoffs `(0, 1, −1)` and `(0, −1, 1)`; both choices are SPNE, with different payoffs for
  players 2 and 3 (`exercise_9_B_4_three_player_counterexample`). The corrected statement is the
  two-player `exercise_9_B_4`.

`assemble_pureB_pureOfChoice`: the moves of the pure profile `pureOfChoice c` are those of
`pureMoves c`.
-/

namespace MWG.DynamicGames

open MWG.NoncooperativeGames MWG.NoncooperativeGames.ExtensiveForm

/-- The moves of the pure profile choosing `c k` at every information set are the sure moves
`pureMoves c` (nature moves by `ρ` in both). -/
theorem assemble_pureB_pureOfChoice {I A H : Type*} [DecidableEq A] [DecidableEq I]
    (G : ExtensiveForm I A H)
    (c : H → A) (hc : ∀ k, c k ∈ G.avail k) :
    G.assemble (pureB G (pureOfChoice G c hc)) = G.assemble (pureMoves (I := I) c) := by
  funext k a
  cases hk : G.player k with
  | none => rw [G.assemble_of_none _ hk, G.assemble_of_none _ hk]
  | some j =>
    rw [assemble_pureB, G.pureProfile_apply _ hk, G.assemble_of_some _ hk]
    simp only [pureOfChoice, pureOfFun_apply, pureMoves, dirac]
    by_cases h : a = c k
    · simp [h]
    · simp [h, Ne.symm h]

/-- Payoffs of the one-player game with a move of nature: `L` gives `1`; after `R` nature
gives `0` or `2`. -/
def naturePay (z : List (Fin 2)) : ℝ :=
  if z = [0] then 1 else if z = [0, 1] then 0 else if z = [1, 1] then 2 else 0

/-- **Correction to Propositions 9.B.1-9.B.2** (MWG, pp. 272 and 276). A one-player game of
perfect information with a move of nature: the player chooses `L` (`0`) or `R` (`1`) at
information set `0`; after `R` nature (information set `1`) chooses `0` or `1` with probability
`1/2` each. -/
noncomputable def natureGame : ExtensiveForm (Fin 1) (Fin 2) (Fin 2) where
  nodes := {[], [0], [1], [0, 1], [1, 1]}
  nil_mem := by decide
  tail_mem := by decide
  info x := if x = [] then 0 else 1
  avail _ := Finset.univ
  avail_spec := by decide
  info_surj := by decide
  player k := if k = 0 then some 0 else none
  natureProb _ _ := 1 / 2
  nature_nonneg := fun _ _ _ => by norm_num
  nature_zero := fun _ _ a ha => absurd (Finset.mem_univ a) ha
  nature_sum := fun _ _ => by norm_num [Fin.sum_univ_two]
  payoff _ := naturePay

theorem natureGame_perfectInformation : natureGame.PerfectInformation := by
  unfold ExtensiveForm.PerfectInformation
  decide

/-- The continuation payoffs of `natureGame` from its two decision nodes. -/
theorem natureGame_cont (f : Fin 2 → Fin 2 → ℝ) (i : Fin 1) :
    cont natureGame f [] i = f 0 0 * 1 + f 0 1 * (f 1 0 * 0 + f 1 1 * 2) ∧
    cont natureGame f [0] i = 1 ∧ cont natureGame f [1] i = f 1 0 * 0 + f 1 1 * 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [cont_unfold, natureGame, Fin.sum_univ_two, naturePay]

theorem natureGame_terminals : natureGame.terminals = {[0], [0, 1], [1, 1]} := by decide

theorem natureGame_decisionNodes : natureGame.decisionNodes = {[], [1]} := by decide

/-- No player has the same payoffs at two distinct terminal nodes of `natureGame`. -/
theorem natureGame_payoff_injective :
    ∀ i, ∀ z ∈ natureGame.terminals, ∀ z' ∈ natureGame.terminals,
      natureGame.payoff i z = natureGame.payoff i z' → z = z' := by
  intro i z hz z' hz' he
  rw [natureGame_terminals] at hz hz'
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz hz'
  rcases hz with rfl | rfl | rfl <;> rcases hz' with rfl | rfl | rfl <;>
    simp [natureGame, naturePay] at he ⊢

/-- Both sure choices are one-shot optimal at every decision node of `natureGame`: from the
root, `L` gives `1` and `R` gives `(0 + 2)/2 = 1`. -/
theorem natureGame_oneShot (b : Fin 2) :
    ∀ x, natureGame.IsDecision x → OneShotOptimalAt natureGame (pureMoves ![b, 0]) x := by
  intro x hx j hj a _
  have hx' := (mem_decisionNodes _).2 hx
  rw [natureGame_decisionNodes] at hx'
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
  rcases hx' with rfl | rfl
  · have hasm : natureGame.assemble (pureMoves (I := Fin 1) ![b, 0]) 0 = dirac b :=
      natureGame.assemble_of_some _ rfl
    have hasm1 : natureGame.assemble (pureMoves (I := Fin 1) ![b, 0]) 1 = fun _ => 1 / 2 :=
      natureGame.assemble_of_none _ rfl
    obtain ⟨h1, h2, h3⟩ := natureGame_cont (natureGame.assemble (pureMoves ![b, 0])) j
    simp only [hasm, hasm1] at h1 h3
    fin_cases a
    · change cont _ _ [0] j ≤ _
      rw [h1, h2]
      fin_cases b <;> norm_num [dirac]
    · change cont _ _ [1] j ≤ _
      rw [h1, h3]
      fin_cases b <;> norm_num [dirac]
  · simp [natureGame] at hj

/-- **Correction to Proposition 9.B.2** (MWG, p. 276). With a move of nature, distinct terminal
payoffs do not give a unique SPNE: in `natureGame` (perfect information, no player with equal
payoffs at two terminal nodes) both `L` and `R` are SPNE, and they prescribe different moves.
So the uniqueness clause needs the hypothesis "no moves of nature" (`proposition_9_B_2`). -/
theorem proposition_9_B_2_nature_counterexample :
    natureGame.PerfectInformation ∧
    (∀ i, ∀ z ∈ natureGame.terminals, ∀ z' ∈ natureGame.terminals,
      natureGame.payoff i z = natureGame.payoff i z' → z = z') ∧
    IsSPNE natureGame (pureMoves ![0, 0]) ∧ IsSPNE natureGame (pureMoves ![1, 0]) ∧
    natureGame.assemble (pureMoves ![0, 0]) 0 ≠ natureGame.assemble (pureMoves ![1, 0]) 0 := by
  refine ⟨natureGame_perfectInformation, natureGame_payoff_injective,
    isSPNE_of_oneShotOptimal _ (isBehaviorProfile_pureMoves fun _ => Finset.mem_univ _)
      (natureGame_oneShot 0),
    isSPNE_of_oneShotOptimal _ (isBehaviorProfile_pureMoves fun _ => Finset.mem_univ _)
      (natureGame_oneShot 1), fun h => ?_⟩
  have h0 := congrFun h 0
  rw [natureGame.assemble_of_some _ (show natureGame.player 0 = some 0 from rfl),
    natureGame.assemble_of_some _ (show natureGame.player 0 = some 0 from rfl)] at h0
  simp [pureMoves, dirac] at h0

/-- **Correction to Proposition 9.B.1** (MWG, p. 272). With a move of nature, distinct terminal
payoffs do not give a unique profile derived through backward induction: `natureGame` has two
(choosing `L` and choosing `R`). The uniqueness clause of `proposition_9_B_1` assumes that
nature does not move. -/
theorem proposition_9_B_1_nature_counterexample :
    natureGame.PerfectInformation ∧
    (∀ i, ∀ z ∈ natureGame.terminals, ∀ z' ∈ natureGame.terminals,
      natureGame.payoff i z = natureGame.payoff i z' → z = z') ∧
    ¬ ∃! s : (i : Fin 1) → natureGame.PureStrategy i, IsBackwardInduction natureGame s := by
  refine ⟨natureGame_perfectInformation, natureGame_payoff_injective, ?_⟩
  rintro ⟨s, -, huniq⟩
  have hc : ∀ b : Fin 2, ∀ k, (![b, 0] : Fin 2 → Fin 2) k ∈ natureGame.avail k :=
    fun _ _ => Finset.mem_univ _
  have hBI : ∀ b : Fin 2, IsBackwardInduction natureGame (pureOfChoice natureGame _ (hc b)) := by
    intro b x hx
    unfold OneShotOptimalAt
    rw [assemble_pureB_pureOfChoice]
    exact natureGame_oneShot b x hx
  have h01 := (huniq _ (hBI 0)).trans (huniq _ (hBI 1)).symm
  have := congrArg (fun t => (t 0 ⟨0, rfl⟩).1) h01
  simp [pureOfChoice] at this

/-- Payoffs `(u₁, u₂, u₃)` of the three-player zero-sum game: `(0, 1, −1)` after `0` and
`(0, −1, 1)` after `1`. -/
def zeroSum3Pay (i : Fin 3) (z : List (Fin 2)) : ℝ :=
  if z = [0] then ![0, 1, -1] i else if z = [1] then ![0, -1, 1] i else 0

/-- **Correction to Exercise 9.B.4** (MWG, p. 302). A three-player zero-sum game of perfect
information: player 1 (`0`) chooses between the terminal nodes `[0]` and `[1]`. -/
def zeroSum3Game : ExtensiveForm (Fin 3) (Fin 2) (Fin 1) where
  nodes := {[], [0], [1]}
  nil_mem := by decide
  tail_mem := by decide
  info _ := 0
  avail _ := Finset.univ
  avail_spec := by decide
  info_surj := by decide
  player _ := some 0
  natureProb _ _ := 0
  nature_nonneg := fun _ hk => absurd hk (by simp)
  nature_zero := fun _ hk => absurd hk (by simp)
  nature_sum := fun _ hk => absurd hk (by simp)
  payoff := zeroSum3Pay

/-- The continuation payoffs of `zeroSum3Game` from the root. -/
theorem zeroSum3Game_cont (f : Fin 1 → Fin 2 → ℝ) (i : Fin 3) :
    cont zeroSum3Game f [] i = f 0 0 * zeroSum3Pay i [0] + f 0 1 * zeroSum3Pay i [1] ∧
    cont zeroSum3Game f [0] i = zeroSum3Pay i [0] ∧
    cont zeroSum3Game f [1] i = zeroSum3Pay i [1] := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [cont_unfold, zeroSum3Game, Fin.sum_univ_two]

/-- **Correction to Exercise 9.B.4** (MWG, p. 302). With three players, zero-sum games of
perfect information can have SPNE with different payoffs: in `zeroSum3Game` (payoffs summing
to zero at every node) player 1 is indifferent, both of her choices are SPNE, and player 2 gets
`1` in one and `−1` in the other. The corrected statement is the two-player
`exercise_9_B_4`. -/
theorem exercise_9_B_4_three_player_counterexample :
    zeroSum3Game.PerfectInformation ∧ (∀ z, ∑ i, zeroSum3Game.payoff i z = 0) ∧
    IsSPNE zeroSum3Game (pureMoves ![0]) ∧ IsSPNE zeroSum3Game (pureMoves ![1]) ∧
    cont zeroSum3Game (zeroSum3Game.assemble (pureMoves ![0])) [] 1 = 1 ∧
    cont zeroSum3Game (zeroSum3Game.assemble (pureMoves ![1])) [] 1 = -1 := by
  have hasm : ∀ b : Fin 2, zeroSum3Game.assemble (pureMoves (I := Fin 3) ![b]) 0 = dirac b :=
    fun _ => zeroSum3Game.assemble_of_some _ rfl
  have hopt : ∀ b : Fin 2, ∀ x, zeroSum3Game.IsDecision x →
      OneShotOptimalAt zeroSum3Game (pureMoves ![b]) x := by
    intro b x hx j hj a _
    have hx' := (mem_decisionNodes _).2 hx
    have hD : zeroSum3Game.decisionNodes = {[]} := by decide
    rw [hD, Finset.mem_singleton] at hx'
    subst hx'
    obtain rfl : j = 0 := by simpa [zeroSum3Game] using hj.symm
    obtain ⟨h1, h2, h3⟩ := zeroSum3Game_cont (zeroSum3Game.assemble (pureMoves ![b])) 0
    rw [hasm] at h1
    fin_cases a
    · change cont _ _ [0] 0 ≤ _
      rw [h1, h2]
      fin_cases b <;> norm_num [dirac, zeroSum3Pay]
    · change cont _ _ [1] 0 ≤ _
      rw [h1, h3]
      fin_cases b <;> norm_num [dirac, zeroSum3Pay]
  refine ⟨by unfold ExtensiveForm.PerfectInformation; decide, fun z => ?_,
    isSPNE_of_oneShotOptimal _ (isBehaviorProfile_pureMoves fun _ => Finset.mem_univ _) (hopt 0),
    isSPNE_of_oneShotOptimal _ (isBehaviorProfile_pureMoves fun _ => Finset.mem_univ _) (hopt 1),
    ?_, ?_⟩
  · simp only [zeroSum3Game, zeroSum3Pay, Fin.sum_univ_three]
    split_ifs <;> simp
  · rw [(zeroSum3Game_cont _ 1).1, hasm]
    norm_num [dirac, zeroSum3Pay]
  · rw [(zeroSum3Game_cont _ 1).1, hasm]
    norm_num [dirac, zeroSum3Pay]

end MWG.DynamicGames

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The Centipede game

MWG, Example 9.B.5 and Figure 9.B.8 (pp. 281-282; Rosenthal 1981).

Two players alternate saying "stop" (`0`) or "continue" (`1`), player 1 (`0`) first. Both start
with one dollar; a player who continues loses one dollar from her pile and her opponent gains
two (`centPile`). The game `centipede n` has `n + 1` decision nodes: the node after `k`
continues is `List.replicate k 1` (information set `k`), stopping there ends the game at
`0 :: List.replicate k 1`, and after `n + 1` continues the game ends. MWG's game is
`centipede 197` (198 decision nodes, both piles reaching 100 dollars).

* `centPile_even`, `centPile_odd`, `example_9_B_5_payoffs`: the piles after `2m` continues are
  `(m + 1, m + 1)` and after `2m + 1` continues `(m, m + 3)`; in particular the payoffs `(1, 1)`,
  `(0, 3)`, `(2, 2)`, `(97, 100)`, `(99, 99)`, `(98, 101)` and `(100, 100)` of Figure 9.B.8.
* `example_9_B_5`: the game is of perfect information; saying "stop" everywhere is an SPNE; in
  every SPNE (in behaviour strategies) both players say "stop" for sure at every decision node;
  every SPNE gives both players `1`; and the backward-induction profile is unique.
* `example_9_B_5_ties`: Proposition 9.B.2's sufficient condition for uniqueness fails (player 1
  gets `1` at two terminal nodes), so uniqueness is proved directly: continuing always costs the
  mover exactly one dollar once the opponent stops next (`centPile_succ_mover`).
-/

namespace MWG.DynamicGames

open MWG.NoncooperativeGames MWG.NoncooperativeGames.ExtensiveForm

/-- The player who moves after `k` continues: player 1 (`0`) if `k` is even, player 2 (`1`)
if `k` is odd. -/
def centMover (k : ℕ) : Fin 2 := if k % 2 = 0 then 0 else 1

/-- The players' piles after `k` continues: each continue takes one dollar from the mover's
pile and puts two in her opponent's. -/
def centPile : ℕ → Fin 2 → ℝ
  | 0 => fun _ => 1
  | k + 1 => fun i => if i = centMover k then centPile k i - 1 else centPile k i + 2

/-- Continuing costs the mover one dollar. -/
theorem centPile_succ_mover (k : ℕ) :
    centPile (k + 1) (centMover k) = centPile k (centMover k) - 1 := by
  simp [centPile]

theorem centPile_succ (k : ℕ) (i : Fin 2) :
    centPile (k + 1) i = if i = centMover k then centPile k i - 1 else centPile k i + 2 := rfl

/-- The piles after an even number `2m` of continues are `(m + 1, m + 1)`. -/
theorem centPile_even (m : ℕ) (i : Fin 2) : centPile (2 * m) i = m + 1 ∧
    centPile (2 * m + 1) 0 = m ∧ centPile (2 * m + 1) 1 = m + 3 := by
  have hE : ∀ m : ℕ, (∀ i, centPile (2 * m) i = m + 1) →
      centPile (2 * m + 1) 0 = m ∧ centPile (2 * m + 1) 1 = m + 3 := by
    intro m h
    have hm : centMover (2 * m) = 0 := by simp [centMover]
    rw [centPile_succ, centPile_succ, hm, h, h]
    norm_num
    ring
  induction m generalizing i with
  | zero =>
    have h : ∀ i, centPile (2 * 0) i = (0 : ℕ) + 1 := fun i => by simp [centPile]
    exact ⟨h i, hE 0 h⟩
  | succ m ih =>
    have hO := hE m fun i => (ih i).1
    have hm : centMover (2 * m + 1) = 1 := by simp [centMover]
    have h : ∀ i, centPile (2 * (m + 1)) i = (m + 1 : ℕ) + 1 := by
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Fin.forall_fin_two,
        centPile_succ (2 * m + 1) 0, centPile_succ (2 * m + 1) 1, hm, hO.1, hO.2]
      push_cast
      constructor <;> ring
    exact ⟨h i, hE (m + 1) h⟩

/-- The piles after an odd number `2m + 1` of continues are `(m, m + 3)`. -/
theorem centPile_odd (m : ℕ) : centPile (2 * m + 1) 0 = m ∧ centPile (2 * m + 1) 1 = m + 3 :=
  ⟨(centPile_even m 0).2.1, (centPile_even m 0).2.2⟩

/-- **Example 9.B.5, Figure 9.B.8** (MWG, p. 282). The payoffs `(u₁, u₂)` after `0, 1, 2, 195,
196, 197` continues and at the end (`198` continues): `(1, 1)`, `(0, 3)`, `(2, 2)`, `(97, 100)`,
`(99, 99)`, `(98, 101)`, `(100, 100)`. -/
theorem example_9_B_5_payoffs :
    (centPile 0 0, centPile 0 1) = (1, 1) ∧ (centPile 1 0, centPile 1 1) = (0, 3) ∧
    (centPile 2 0, centPile 2 1) = (2, 2) ∧ (centPile 195 0, centPile 195 1) = (97, 100) ∧
    (centPile 196 0, centPile 196 1) = (99, 99) ∧ (centPile 197 0, centPile 197 1) = (98, 101) ∧
    (centPile 198 0, centPile 198 1) = (100, 100) := by
  have ev : ∀ m : ℕ, centPile (2 * m) 0 = m + 1 ∧ centPile (2 * m) 1 = m + 1 ∧
      centPile (2 * m + 1) 0 = m ∧ centPile (2 * m + 1) 1 = m + 3 := fun m =>
    ⟨(centPile_even m 0).1, (centPile_even m 1).1, (centPile_even m 0).2⟩
  obtain ⟨a0, a1, b0, b1⟩ := ev 0
  obtain ⟨c0, c1, -, -⟩ := ev 1
  obtain ⟨-, -, d0, d1⟩ := ev 97
  obtain ⟨e0, e1, f0, f1⟩ := ev 98
  obtain ⟨g0, g1, -, -⟩ := ev 99
  norm_num at a0 a1 b0 b1 c0 c1 d0 d1 e0 e1 f0 f1 g0 g1
  simp only [a0, a1, b0, b1, c0, c1, d0, d1, e0, e1, f0, f1, g0, g1]
  norm_num

/-- The nodes of the Centipede game with `n + 1` decision nodes. -/
def centNodes (n : ℕ) : Finset (List (Fin 2)) :=
  (Finset.range (n + 2)).image (fun k => List.replicate k 1) ∪
    (Finset.range (n + 1)).image (fun k => 0 :: List.replicate k 1)

theorem mem_centNodes {n : ℕ} {x : List (Fin 2)} : x ∈ centNodes n ↔
    (∃ k, k ≤ n + 1 ∧ x = List.replicate k 1) ∨ ∃ k, k ≤ n ∧ x = 0 :: List.replicate k 1 := by
  simp only [centNodes, Finset.mem_union, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro (⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩)
    · exact Or.inl ⟨k, by omega, rfl⟩
    · exact Or.inr ⟨k, by omega, rfl⟩
  · rintro (⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩)
    · exact Or.inl ⟨k, by omega, rfl⟩
    · exact Or.inr ⟨k, by omega, rfl⟩

/-- A stop node is not on the "continue" path. -/
theorem zero_cons_ne_replicate (l : List (Fin 2)) (j : ℕ) : 0 :: l ≠ List.replicate j 1 := by
  intro h
  have : (0 : Fin 2) ∈ List.replicate j 1 := h ▸ List.mem_cons_self
  simp [List.mem_replicate] at this

/-- The nodes with a successor are the nodes after `k ≤ n` continues. -/
theorem cons_mem_centNodes {n : ℕ} {b : Fin 2} {x : List (Fin 2)} :
    b :: x ∈ centNodes n ↔ ∃ k, k ≤ n ∧ x = List.replicate k 1 := by
  rw [mem_centNodes]
  constructor
  · rintro (⟨j, hj, h⟩ | ⟨j, hj, h⟩)
    · cases j with
      | zero => simp at h
      | succ k =>
        rw [List.replicate_succ, List.cons.injEq] at h
        exact ⟨k, by omega, h.2⟩
    · rw [List.cons.injEq] at h
      exact ⟨j, hj, h.2⟩
  · rintro ⟨k, hk, rfl⟩
    fin_cases b
    · exact Or.inr ⟨k, hk, rfl⟩
    · exact Or.inl ⟨k + 1, by omega, rfl⟩

/-- **Example 9.B.5, Figure 9.B.8** (MWG, pp. 281-282). The Centipede game with `n + 1`
decision nodes (MWG's game has `n = 197`). Information set `k` is the node after `k` continues;
the payoffs at a terminal node are the piles after its number of continues. -/
def centipede (n : ℕ) : ExtensiveForm (Fin 2) (Fin 2) (Fin (n + 1)) where
  nodes := centNodes n
  nil_mem := mem_centNodes.2 (Or.inl ⟨0, by omega, rfl⟩)
  tail_mem := by
    intro x hx
    rcases mem_centNodes.1 hx with ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
    · exact mem_centNodes.2 (Or.inl ⟨k - 1, by omega, by simp [List.tail_replicate]⟩)
    · exact mem_centNodes.2 (Or.inl ⟨k, by omega, rfl⟩)
  info x := ⟨min x.length n, by omega⟩
  avail _ := Finset.univ
  avail_spec := fun _ _ ⟨_, hb⟩ a => by
    simp only [Finset.mem_univ, iff_true]
    exact cons_mem_centNodes.2 (cons_mem_centNodes.1 hb)
  info_surj := fun k => ⟨List.replicate k 1,
    mem_centNodes.2 (Or.inl ⟨k, by omega, rfl⟩), ⟨0, cons_mem_centNodes.2 ⟨k, by omega, rfl⟩⟩,
    Fin.ext (by simp; omega)⟩
  player k := some (centMover k)
  natureProb _ _ := 0
  nature_nonneg := fun _ hk => absurd hk (by simp)
  nature_zero := fun _ hk => absurd hk (by simp)
  nature_sum := fun _ hk => absurd hk (by simp)
  payoff i z := centPile (z.count 1) i

variable {n : ℕ}

theorem centipede_isDecision {k : ℕ} (hk : k ≤ n) :
    (centipede n).IsDecision (List.replicate k 1) :=
  ⟨mem_centNodes.2 (Or.inl ⟨k, by omega, rfl⟩), 0, cons_mem_centNodes.2 ⟨k, hk, rfl⟩⟩

theorem centipede_info {k : ℕ} (hk : k ≤ n) :
    (centipede n).info (List.replicate k 1) = ⟨k, by omega⟩ :=
  Fin.ext (by simp [centipede]; omega)

/-- The decision nodes are the nodes after `k ≤ n` continues. -/
theorem centipede_isDecision_iff {x : List (Fin 2)} :
    (centipede n).IsDecision x ↔ ∃ k, k ≤ n ∧ x = List.replicate k 1 := by
  constructor
  · rintro ⟨-, b, hb⟩
    exact cons_mem_centNodes.1 hb
  · rintro ⟨k, hk, rfl⟩
    exact centipede_isDecision hk

/-- Stopping after `k ≤ n` continues ends the game with the piles after `k` continues. -/
theorem centipede_cont_stop (f : Fin (n + 1) → Fin 2 → ℝ) {k : ℕ} (hk : k ≤ n) (i : Fin 2) :
    cont (centipede n) f (0 :: List.replicate k 1) i = centPile k i := by
  have ht : (centipede n).IsTerminal (0 :: List.replicate k 1) :=
    ⟨mem_centNodes.2 (Or.inr ⟨k, hk, rfl⟩), fun b hb => by
      obtain ⟨j, -, hj⟩ := cons_mem_centNodes.1 hb
      exact zero_cons_ne_replicate _ _ hj⟩
  rw [cont_terminal _ _ ht]
  simp [centipede]

/-- After `n + 1` continues the game ends with the piles after `n + 1` continues. -/
theorem centipede_cont_end (f : Fin (n + 1) → Fin 2 → ℝ) (i : Fin 2) :
    cont (centipede n) f (List.replicate (n + 1) 1) i = centPile (n + 1) i := by
  have ht : (centipede n).IsTerminal (List.replicate (n + 1) 1) :=
    ⟨mem_centNodes.2 (Or.inl ⟨n + 1, le_rfl, rfl⟩), fun b hb => by
      obtain ⟨j, hj, he⟩ := cons_mem_centNodes.1 hb
      have := congrArg List.length he
      simp at this
      omega⟩
  rw [cont_terminal _ _ ht]
  simp [centipede]

/-- The backward-induction recursion at the node after `k ≤ n` continues. -/
theorem centipede_cont_decision (f : Fin (n + 1) → Fin 2 → ℝ) {k : ℕ} (hk : k ≤ n) (i : Fin 2) :
    cont (centipede n) f (List.replicate k 1) i =
      f ⟨k, by omega⟩ 0 * centPile k i +
        f ⟨k, by omega⟩ 1 * cont (centipede n) f (List.replicate (k + 1) 1) i := by
  rw [cont_decision _ _ (centipede_isDecision hk), centipede_info hk]
  have havail : (centipede n).avail ⟨k, by omega⟩ = Finset.univ := rfl
  rw [havail, Fin.sum_univ_two, centipede_cont_stop f hk]
  rfl

/-- The step of backward induction: if play after `k + 1` continues gives the piles after
`k + 1` continues, a one-shot optimal mover after `k` continues stops for sure. -/
theorem centipede_step {F : Fin 2 → Fin (n + 1) → Fin 2 → ℝ}
    (hF : IsBehaviorProfile (centipede n) F) {k : ℕ} (hk : k ≤ n)
    (hopt : OneShotOptimalAt (centipede n) F (List.replicate k 1))
    (hnext : ∀ i, cont (centipede n) ((centipede n).assemble F) (List.replicate (k + 1) 1) i =
      centPile (k + 1) i) :
    (centipede n).assemble F ⟨k, by omega⟩ 1 = 0 ∧
      (centipede n).assemble F ⟨k, by omega⟩ 0 = 1 ∧
      ∀ i, cont (centipede n) ((centipede n).assemble F) (List.replicate k 1) i = centPile k i := by
  set f := (centipede n).assemble F
  have hsum : f ⟨k, by omega⟩ 0 + f ⟨k, by omega⟩ 1 = 1 := by
    have := assemble_sum _ hF ⟨k, by omega⟩
    rwa [show (centipede n).avail ⟨k, by omega⟩ = Finset.univ from rfl, Fin.sum_univ_two] at this
  have h0 : 0 ≤ f ⟨k, by omega⟩ 0 := assemble_nonneg _ hF ⟨k, by omega⟩ 0
  have h1 : 0 ≤ f ⟨k, by omega⟩ 1 := assemble_nonneg _ hF ⟨k, by omega⟩ 1
  have hst := hopt (centMover k) (by rw [centipede_info hk]; rfl) 0 (Finset.mem_univ _)
  rw [centipede_cont_stop f hk, centipede_cont_decision f hk, hnext,
    centPile_succ_mover] at hst
  have key : f ⟨k, by omega⟩ 0 * centPile k (centMover k) +
      f ⟨k, by omega⟩ 1 * (centPile k (centMover k) - 1) =
      (f ⟨k, by omega⟩ 0 + f ⟨k, by omega⟩ 1) * centPile k (centMover k) - f ⟨k, by omega⟩ 1 := by
    ring
  rw [key, hsum] at hst
  have hq : f ⟨k, by omega⟩ 1 = 0 := by linarith
  have hp : f ⟨k, by omega⟩ 0 = 1 := by linarith
  refine ⟨hq, hp, fun i => ?_⟩
  rw [centipede_cont_decision f hk, hq, hp]
  ring

/-- Under the moves `f` with "stop" at every information set, play from the node after
`k ≤ n + 1` continues gives the piles after `k` continues. -/
theorem centipede_cont_stopAll {f : Fin (n + 1) → Fin 2 → ℝ}
    (hf : ∀ k, f k 0 = 1 ∧ f k 1 = 0) :
    ∀ k, k ≤ n + 1 → ∀ i, cont (centipede n) f (List.replicate k 1) i = centPile k i := by
  suffices h : ∀ j k, k + j = n + 1 → ∀ i,
      cont (centipede n) f (List.replicate k 1) i = centPile k i from
    fun k hk => h (n + 1 - k) k (by omega)
  intro j
  induction j with
  | zero =>
    intro k hk i
    obtain rfl : k = n + 1 := by omega
    exact centipede_cont_end f i
  | succ j ih =>
    intro k hk i
    rw [centipede_cont_decision f (by omega), ih (k + 1) (by omega), (hf _).1, (hf _).2]
    ring

/-- **Example 9.B.5** (MWG, pp. 281-282). The Centipede game is a finite game of perfect
information; saying "stop" at every decision node is a subgame perfect Nash equilibrium; in
every SPNE (in behaviour strategies) both players say "stop" for sure at every decision node,
so that the game ends at once and each player receives `1`; and the profile derived through
backward induction is unique. -/
theorem example_9_B_5 :
    (centipede n).PerfectInformation ∧ IsSPNE (centipede n) (pureMoves fun _ => 0) ∧
    (∀ F, IsSPNE (centipede n) F → ∀ k, (centipede n).assemble F k = dirac 0) ∧
    (∀ F, IsSPNE (centipede n) F → ∀ i, cont (centipede n) ((centipede n).assemble F) [] i = 1) ∧
    ∃! s : (i : Fin 2) → (centipede n).PureStrategy i, IsBackwardInduction (centipede n) s := by
  have hPI : (centipede n).PerfectInformation := by
    intro x _ x' _ hb hb' he
    obtain ⟨k, hk, rfl⟩ := cons_mem_centNodes.1 hb.choose_spec
    obtain ⟨k', hk', rfl⟩ := cons_mem_centNodes.1 hb'.choose_spec
    rw [centipede_info hk, centipede_info hk'] at he
    simp only [Fin.mk.injEq] at he
    rw [he]
  -- every SPNE stops everywhere
  have hall : ∀ F, IsSPNE (centipede n) F → (∀ k, k ≤ n + 1 → ∀ i,
      cont (centipede n) ((centipede n).assemble F) (List.replicate k 1) i = centPile k i) ∧
      ∀ k : Fin (n + 1), (centipede n).assemble F k = dirac 0 := by
    intro F hF
    have hopt : ∀ k, k ≤ n → OneShotOptimalAt (centipede n) F (List.replicate k 1) :=
      fun k hk => oneShotOptimal_of_isSPNE _ hPI hF (centipede_isDecision hk)
    have hc : ∀ k, k ≤ n + 1 → ∀ i,
        cont (centipede n) ((centipede n).assemble F) (List.replicate k 1) i = centPile k i := by
      suffices h : ∀ j k, k + j = n + 1 → ∀ i,
          cont (centipede n) ((centipede n).assemble F) (List.replicate k 1) i = centPile k i from
        fun k hk => h (n + 1 - k) k (by omega)
      intro j
      induction j with
      | zero =>
        intro k hk i
        obtain rfl : k = n + 1 := by omega
        exact centipede_cont_end _ i
      | succ j ih =>
        intro k hk
        exact (centipede_step hF.1 (by omega) (hopt k (by omega)) (ih (k + 1) (by omega))).2.2
    refine ⟨hc, fun k => ?_⟩
    obtain ⟨hq, hp, -⟩ := centipede_step hF.1 (Nat.lt_succ_iff.1 k.2) (hopt k (by omega))
      (hc (k + 1) (by omega))
    funext a
    fin_cases a
    · simpa [dirac] using hp
    · simpa [dirac] using hq
  have hS : IsSPNE (centipede n) (pureMoves fun _ => 0) := by
    have hB : IsBehaviorProfile (centipede n) (pureMoves (I := Fin 2) fun _ => (0 : Fin 2)) :=
      isBehaviorProfile_pureMoves fun _ => Finset.mem_univ _
    have hf : ∀ k, (centipede n).assemble (pureMoves (I := Fin 2) fun _ => (0 : Fin 2)) k 0 = 1 ∧
        (centipede n).assemble (pureMoves (I := Fin 2) fun _ => (0 : Fin 2)) k 1 = 0 := by
      intro k
      rw [(centipede n).assemble_of_some _ (show (centipede n).player k = some (centMover k)
        from rfl)]
      simp [pureMoves, dirac]
    refine isSPNE_of_oneShotOptimal _ hB fun x hx => ?_
    obtain ⟨k, hk, rfl⟩ := centipede_isDecision_iff.1 hx
    intro j hj a _
    obtain rfl : j = centMover k := by
      rw [centipede_info hk] at hj
      exact (Option.some.inj hj).symm
    fin_cases a
    · change cont _ _ (0 :: List.replicate k 1) (centMover k) ≤ _
      rw [centipede_cont_stop _ hk, centipede_cont_stopAll hf k (by omega)]
    · change cont _ _ (List.replicate (k + 1) 1) (centMover k) ≤ _
      rw [centipede_cont_stopAll hf k (by omega), centipede_cont_stopAll hf (k + 1) (by omega),
        centPile_succ_mover]
      linarith
  refine ⟨hPI, hS, fun F hF => (hall F hF).2, fun F hF i => ?_, ?_⟩
  · have := (hall F hF).1 0 (by omega) i
    simpa [centPile] using this
  · have hNA := (centipede n).noAbsentMindedness_of_perfectInformation hPI
    obtain ⟨s, hs⟩ := exists_backwardInduction _ hPI
    refine ⟨s, hs, fun s' hs' => pure_eq_of_assemble_eq _ fun k => ?_⟩
    rw [(hall _ (isSPNE_of_oneShotOptimal _ (isBehaviorProfile_pureB _ s') hs')).2 k,
      (hall _ (isSPNE_of_oneShotOptimal _ (isBehaviorProfile_pureB _ s) hs)).2 k]

/-- **Example 9.B.5** (MWG, pp. 281-282). Player 1 receives `1` both when she stops at once and
when the game stops after three continues, so the sufficient condition of Proposition 9.B.2
(no player with equal payoffs at two terminal nodes) fails and `example_9_B_5` proves
uniqueness directly. -/
theorem example_9_B_5_ties (hn : 3 ≤ n) :
    [0] ∈ (centipede n).terminals ∧ [0, 1, 1, 1] ∈ (centipede n).terminals ∧
    (centipede n).payoff 0 [0] = (centipede n).payoff 0 [0, 1, 1, 1] := by
  have ht : ∀ k, k ≤ n → 0 :: List.replicate k 1 ∈ (centipede n).terminals := fun k hk =>
    (mem_terminals _).2 ⟨mem_centNodes.2 (Or.inr ⟨k, hk, rfl⟩), fun b hb => by
      obtain ⟨j, -, hj⟩ := cons_mem_centNodes.1 hb
      exact zero_cons_ne_replicate _ _ hj⟩
  refine ⟨ht 0 (by omega), ht 3 hn, ?_⟩
  simp [centipede, centPile, centMover]
  norm_num

end MWG.DynamicGames

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The joint venture entry game

MWG, Example 9.C.2 and Figure 9.C.2 (pp. 286-287).

Players: `0` = firm E1, `1` = firm E2, `2` = the incumbent I. Information sets: `0` = E1 at the
start (Out `0`, Enter on own `1`, Propose joint venture `2`); `1` = E2 after a proposal
(Accept `0`, Decline `1`); `2` = E1 after E2 declines (In `0`, Out `1`); `3` = I's
information set `{[1], [0, 2], [0, 1, 2]}` (left: E1 alone; middle: joint venture; right: E1
alone after E2 declined), where I chooses Fight `0` or Accommodate `1`.

* `example_9_C_2_weakPBE`: ((propose joint venture, in if E2 declines), accept, accommodate)
  with belief `1` on the middle node is a weak PBE, and it is the unique weak PBE: in every
  weak PBE `(σ, μ)` (behaviour strategies) these moves are played for sure and `μ` puts
  probability one on the middle node.
* `example_9_C_2_spne`: ((out, out if E2 declines), decline, fight) is an SPNE (the only
  subgame is the whole game, and it is a Nash equilibrium).
-/

namespace MWG.DynamicGames

open MWG.NoncooperativeGames MWG.NoncooperativeGames.ExtensiveForm

/-- Payoffs `(u_E1, u_E2, u_I)` of Figure 9.C.2. -/
def jvPay (i : Fin 3) (z : List (Fin 3)) : ℝ :=
  if z = [0] then ![0, 0, 3] i
  else if z = [0, 1] then ![-1, 0, 2] i else if z = [1, 1] then ![2, 0, 1] i
  else if z = [0, 0, 2] then ![1, 1, -2] i else if z = [1, 0, 2] then ![4, 4, 0] i
  else if z = [0, 0, 1, 2] then ![-1, 0, 2] i else if z = [1, 0, 1, 2] then ![2, 0, 1] i
  else if z = [1, 1, 2] then ![0, 0, 3] i else 0

/-- The information sets of Figure 9.C.2. -/
def jvInfo (x : List (Fin 3)) : Fin 4 :=
  if x = [] then 0 else if x = [2] then 1 else if x = [1, 2] then 2 else 3

/-- **Example 9.C.2, Figure 9.C.2** (MWG, pp. 286-287). The joint venture entry game. -/
def jvGame : ExtensiveForm (Fin 3) (Fin 3) (Fin 4) where
  nodes := {[], [0], [1], [2], [0, 1], [1, 1], [0, 2], [1, 2], [0, 0, 2], [1, 0, 2], [0, 1, 2],
    [1, 1, 2], [0, 0, 1, 2], [1, 0, 1, 2]}
  nil_mem := by decide
  tail_mem := by decide
  info := jvInfo
  avail k := if k = 0 then Finset.univ else {0, 1}
  avail_spec := by decide
  info_surj := by decide
  player := ![some 0, some 1, some 0, some 2]
  natureProb _ _ := 0
  nature_nonneg := fun k hk => absurd hk (by fin_cases k <;> simp)
  nature_zero := fun k hk => absurd hk (by fin_cases k <;> simp)
  nature_sum := fun k hk => absurd hk (by fin_cases k <;> simp)
  payoff := jvPay

/-- Continuation payoffs in the joint venture game. -/
theorem jvGame_cont (f : Fin 4 → Fin 3 → ℝ) (i : Fin 3) :
    cont jvGame f [1] i = f 3 0 * ![-1, 0, 2] i + f 3 1 * ![2, 0, 1] i ∧
    cont jvGame f [0, 2] i = f 3 0 * ![1, 1, -2] i + f 3 1 * ![4, 4, 0] i ∧
    cont jvGame f [1, 2] i = f 2 0 * (f 3 0 * ![-1, 0, 2] i + f 3 1 * ![2, 0, 1] i) +
      f 2 1 * ![0, 0, 3] i ∧
    cont jvGame f [2] i = f 1 0 * (f 3 0 * ![1, 1, -2] i + f 3 1 * ![4, 4, 0] i) +
      f 1 1 * (f 2 0 * (f 3 0 * ![-1, 0, 2] i + f 3 1 * ![2, 0, 1] i) + f 2 1 * ![0, 0, 3] i) ∧
    cont jvGame f [] i = f 0 0 * ![0, 0, 3] i +
      f 0 1 * (f 3 0 * ![-1, 0, 2] i + f 3 1 * ![2, 0, 1] i) +
      f 0 2 * (f 1 0 * (f 3 0 * ![1, 1, -2] i + f 3 1 * ![4, 4, 0] i) +
        f 1 1 * (f 2 0 * (f 3 0 * ![-1, 0, 2] i + f 3 1 * ![2, 0, 1] i) +
          f 2 1 * ![0, 0, 3] i)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [cont_unfold, jvGame, jvPay, jvInfo, Fin.sum_univ_three]

theorem jvGame_infoSet : jvGame.infoSet 0 = {[]} ∧ jvGame.infoSet 1 = {[2]} ∧
    jvGame.infoSet 2 = {[1, 2]} ∧ jvGame.infoSet 3 = {[1], [0, 2], [0, 1, 2]} := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

theorem jvGame_assemble (F : Fin 3 → Fin 4 → Fin 3 → ℝ) :
    jvGame.assemble F 0 = F 0 0 ∧ jvGame.assemble F 1 = F 1 1 ∧ jvGame.assemble F 2 = F 0 2 ∧
      jvGame.assemble F 3 = F 2 3 :=
  ⟨jvGame.assemble_of_some _ rfl, jvGame.assemble_of_some _ rfl,
    jvGame.assemble_of_some _ rfl, jvGame.assemble_of_some _ rfl⟩

/-- The moves of a profile: player `![0, 1, 0, 2] k` moves at information set `k`. -/
theorem jvGame_assemble_eq (F : Fin 3 → Fin 4 → Fin 3 → ℝ) :
    jvGame.assemble F = fun k => F (![0, 1, 0, 2] k) k := by
  funext k
  have hk4 : ∀ k : Fin 4, k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by decide
  rcases hk4 k with rfl | rfl | rfl | rfl <;> exact jvGame.assemble_of_some _ rfl

/-- Expected payoffs at the information sets given beliefs `μ`. -/
theorem jvGame_condPayoff (f : Fin 4 → Fin 3 → ℝ) (μ : List (Fin 3) → ℝ) (i : Fin 3) :
    condPayoff jvGame f μ 0 i = μ [] * cont jvGame f [] i ∧
    condPayoff jvGame f μ 1 i = μ [2] * cont jvGame f [2] i ∧
    condPayoff jvGame f μ 2 i = μ [1, 2] * cont jvGame f [1, 2] i ∧
    condPayoff jvGame f μ 3 i = μ [1] * cont jvGame f [1] i +
      μ [0, 2] * cont jvGame f [0, 2] i + μ [0, 1, 2] * cont jvGame f [0, 1, 2] i := by
  obtain ⟨h0, h1, h2, h3⟩ := jvGame_infoSet
  unfold condPayoff
  rw [h0, h1, h2, h3]
  refine ⟨by simp, by simp, by simp, ?_⟩
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

/-- The behaviour strategy of player `i` that plays `a` at information set `k` and follows
`F i` elsewhere. -/
theorem jvGame_beh_update {F : Fin 3 → Fin 4 → Fin 3 → ℝ} (hF : IsBehaviorProfile jvGame F)
    {i : Fin 3} {k : Fin 4} {a : Fin 3} (ha : a ∈ jvGame.avail k) :
    jvGame.IsBehaviorStrategy i (Function.update (F i) k (dirac a)) := by
  intro k' hk'
  by_cases hkk : k' = k
  · subst hkk
    simp only [Function.update_self]
    refine ⟨fun b => by unfold dirac; split_ifs <;> norm_num, fun b hb => ?_, ?_⟩
    · have : b ≠ a := fun h => hb (h ▸ ha)
      simp [dirac, this]
    · simp only [dirac]
      rw [Finset.sum_ite_eq']
      simp [ha]
  · simp only [Function.update_of_ne hkk]
    exact hF i k' hk'

/-- Facts about a behaviour profile of the joint venture game. -/
theorem jvGame_behavior {F : Fin 3 → Fin 4 → Fin 3 → ℝ} (hF : IsBehaviorProfile jvGame F) :
    (∀ a, 0 ≤ F 0 0 a) ∧ F 0 0 0 + F 0 0 1 + F 0 0 2 = 1 ∧ (∀ a, 0 ≤ F 1 1 a) ∧
      F 1 1 0 + F 1 1 1 = 1 ∧ (∀ a, 0 ≤ F 0 2 a) ∧ F 0 2 0 + F 0 2 1 = 1 ∧
      (∀ a, 0 ≤ F 2 3 a) ∧ F 2 3 0 + F 2 3 1 = 1 := by
  have h0 := hF 0 0 rfl
  have h1 := hF 1 1 rfl
  have h2 := hF 0 2 rfl
  have h3 := hF 2 3 rfl
  exact ⟨h0.1, by simpa [jvGame, Fin.sum_univ_three] using h0.2.2, h1.1,
    by simpa [jvGame] using h1.2.2, h2.1, by simpa [jvGame] using h2.2.2, h3.1,
    by simpa [jvGame] using h3.2.2⟩

/-- Reach probabilities in the joint venture game. -/
theorem jvGame_reach (f : Fin 4 → Fin 3 → ℝ) :
    jvGame.reach f [1] = f 0 1 ∧ jvGame.reach f [2] = f 0 2 ∧
    jvGame.reach f [0, 2] = f 0 2 * f 1 0 ∧ jvGame.reach f [1, 2] = f 0 2 * f 1 1 ∧
    jvGame.reach f [0, 1, 2] = f 0 2 * f 1 1 * f 2 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [jvGame, jvInfo]

/-- The probabilities of reaching the information sets. -/
theorem jvGame_probInfo (f : Fin 4 → Fin 3 → ℝ) :
    probInfo jvGame f 0 = 1 ∧ probInfo jvGame f 1 = f 0 2 ∧
    probInfo jvGame f 2 = f 0 2 * f 1 1 ∧
    probInfo jvGame f 3 = f 0 1 + f 0 2 * f 1 0 + f 0 2 * f 1 1 * f 2 0 := by
  obtain ⟨hI0, hI1, hI2, hI3⟩ := jvGame_infoSet
  obtain ⟨r1, r2, r3, r4, r5⟩ := jvGame_reach f
  unfold probInfo
  rw [hI0, hI1, hI2, hI3, Finset.sum_insert (by decide), Finset.sum_insert (by decide)]
  simp [r1, r2, r3, r4, r5, add_assoc]

/-- The beliefs of the weak PBE: probability one on the middle node of I's information set
(and on the singleton information sets). -/
def jvBelief (x : List (Fin 3)) : ℝ := if x = [1] ∨ x = [0, 1, 2] then 0 else 1

/-- **Example 9.C.2** (MWG, pp. 286-287). ((propose joint venture, in if E2 declines), accept,
accommodate if entry occurs) with beliefs `μ(middle node) = 1` is a weak perfect Bayesian
equilibrium; and it is the unique weak PBE: in every weak PBE `(σ, μ)` E1 proposes the joint
venture, E2 accepts, I accommodates, E1 enters if E2 declines, and `μ` puts probability one on
the middle node of I's information set. -/
theorem example_9_C_2_weakPBE :
    IsWeakPBE jvGame (pureMoves ![2, 0, 0, 1]) jvBelief ∧
    ∀ F μ, IsWeakPBE jvGame F μ →
      F 0 0 2 = 1 ∧ F 1 1 0 = 1 ∧ F 2 3 1 = 1 ∧ F 0 2 0 = 1 ∧
      μ [0, 2] = 1 ∧ μ [1] = 0 ∧ μ [0, 1, 2] = 0 := by
  obtain ⟨hI0, hI1, hI2, hI3⟩ := jvGame_infoSet
  have hc := jvGame_cont
  have hcp := jvGame_condPayoff
  have hr := jvGame_reach
  have hpi := jvGame_probInfo
  have hk4 : ∀ k : Fin 4, k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by decide
  constructor
  · have hB : IsBehaviorProfile jvGame (pureMoves (I := Fin 3) ![2, 0, 0, 1]) :=
      isBehaviorProfile_pureMoves fun k => by fin_cases k <;> simp [jvGame]
    refine ⟨hB, ⟨fun x _ => ?_, fun k => ?_⟩, fun k => ?_, fun k hk x hx => ?_⟩
    · unfold jvBelief; split_ifs <;> norm_num
    · rcases hk4 k with rfl | rfl | rfl | rfl
      · simp [hI0, jvBelief]
      · simp [hI1, jvBelief]
      · simp [hI2, jvBelief]
      · rw [hI3, Finset.sum_insert (by decide), Finset.sum_insert (by decide)]
        simp [jvBelief]
    · intro i hi g hg
      rcases hk4 k with rfl | rfl | rfl | rfl
      · obtain rfl : i = 0 := (Option.some.inj (hi : some 0 = some i)).symm
        have h0 := (hg 0 rfl).1
        have h1 := (hg 0 rfl).2.2
        simp only [jvGame, Fin.sum_univ_three, ↓reduceIte] at h1
        rw [(hcp _ _ _).1, (hcp _ _ _).1, (hc _ _).2.2.2.2, (hc _ _).2.2.2.2]
        simp [jvGame_assemble_eq, pureMoves, dirac, jvBelief]
        nlinarith [h0 0, h0 1, h0 2]
      · obtain rfl : i = 1 := (Option.some.inj (hi : some 1 = some i)).symm
        have h0 := (hg 1 rfl).1
        have h1 := (hg 1 rfl).2.2
        simp [jvGame] at h1
        rw [(hcp _ _ _).2.1, (hcp _ _ _).2.1, (hc _ _).2.2.2.1, (hc _ _).2.2.2.1]
        simp [jvGame_assemble_eq, pureMoves, dirac, jvBelief]
        nlinarith [h0 0, h0 1]
      · obtain rfl : i = 0 := (Option.some.inj (hi : some 0 = some i)).symm
        have h0 := (hg 2 rfl).1
        have h1 := (hg 2 rfl).2.2
        simp [jvGame] at h1
        rw [(hcp _ _ _).2.2.1, (hcp _ _ _).2.2.1, (hc _ _).2.2.1, (hc _ _).2.2.1]
        simp [jvGame_assemble_eq, pureMoves, dirac, jvBelief]
        nlinarith [h0 0, h0 1]
      · obtain rfl : i = 2 := (Option.some.inj (hi : some 2 = some i)).symm
        have h0 := (hg 3 rfl).1
        have h1 := (hg 3 rfl).2.2
        simp [jvGame] at h1
        rw [(hcp _ _ _).2.2.2, (hcp _ _ _).2.2.2, (hc _ _).2.1, (hc _ _).2.1]
        simp [jvGame_assemble_eq, pureMoves, dirac, jvBelief]
        nlinarith [h0 0, h0 1]
    · rcases hk4 k with rfl | rfl | rfl | rfl
      · rw [hI0, Finset.mem_singleton] at hx
        subst hx
        rw [(hpi _).1]
        simp [jvBelief]
      · rw [hI1, Finset.mem_singleton] at hx
        subst hx
        rw [(hpi _).2.1, (hr _).2.1]
        simp [jvGame_assemble_eq, pureMoves, dirac, jvBelief]
      · rw [(hpi _).2.2.1] at hk
        simp [jvGame_assemble_eq, pureMoves, dirac] at hk
      · rw [hI3] at hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rw [(hpi _).2.2.2]
        rcases hx with rfl | rfl | rfl
        · rw [(hr _).1]
          simp [jvGame_assemble_eq, pureMoves, dirac, jvBelief]
        · rw [(hr _).2.2.1]
          simp [jvGame_assemble_eq, pureMoves, dirac, jvBelief]
        · rw [(hr _).2.2.2.2]
          simp [jvGame_assemble_eq, pureMoves, dirac, jvBelief]
  · intro F μ ⟨hF, hμ, hSR, hBy⟩
    obtain ⟨hp0, hp1, hq0, hq1, hr0, hr1, hs0, hs1⟩ := jvGame_behavior hF
    have hμ1 : μ [2] = 1 := by simpa [hI1] using hμ.2 1
    have hμ0 : μ [] = 1 := by simpa [hI0] using hμ.2 0
    have hμ2 : μ [1, 2] = 1 := by simpa [hI2] using hμ.2 2
    -- E2 accepts
    have hacc := hSR 1 1 rfl _ (jvGame_beh_update hF (i := 1) (k := 1) (a := 0) (by decide))
    rw [(hcp _ _ _).2.1, (hcp _ _ _).2.1, (hc _ _).2.2.2.1, (hc _ _).2.2.2.1] at hacc
    replace hacc : F 2 3 0 + F 2 3 1 * 4 ≤ F 1 1 0 * (F 2 3 0 + F 2 3 1 * 4) := by
      simpa [jvGame_assemble_eq, hμ1, dirac] using hacc
    have hE2 : F 1 1 0 = 1 := by nlinarith [hq0 0, hq0 1, hs0 0, hs0 1]
    have hE2' : F 1 1 1 = 0 := by linarith
    -- E1 proposes the joint venture
    have hjv := hSR 0 0 rfl _ (jvGame_beh_update hF (i := 0) (k := 0) (a := 2) (by decide))
    rw [(hcp _ _ _).1, (hcp _ _ _).1, (hc _ _).2.2.2.2, (hc _ _).2.2.2.2] at hjv
    replace hjv : F 2 3 0 + F 2 3 1 * 4 ≤
        F 0 0 1 * (-F 2 3 0 + F 2 3 1 * 2) + F 0 0 2 * (F 2 3 0 + F 2 3 1 * 4) := by
      simpa [jvGame_assemble_eq, hμ0, dirac, hE2, hE2'] using hjv
    have hV : 1 ≤ F 2 3 0 + 4 * F 2 3 1 := by nlinarith [hs0 0, hs0 1]
    have e : F 0 0 0 * (F 2 3 0 + F 2 3 1 * 4) + F 0 0 1 * (F 2 3 0 + F 2 3 1 * 4) +
        F 0 0 2 * (F 2 3 0 + F 2 3 1 * 4) = F 2 3 0 + F 2 3 1 * 4 := by
      rw [← add_mul, ← add_mul, hp1, one_mul]
    have e2 : F 0 0 1 * F 2 3 0 + F 0 0 1 * F 2 3 1 = F 0 0 1 := by
      rw [← mul_add, hs1, mul_one]
    have hkey : F 0 0 0 * (F 2 3 0 + 4 * F 2 3 1) + 2 * F 0 0 1 ≤ 0 := by linarith
    have hP0 : F 0 0 0 = 0 := by nlinarith [hp0 0, hp0 1]
    have hP1 : F 0 0 1 = 0 := by nlinarith [hp0 0, hp0 1]
    have hP2 : F 0 0 2 = 1 := by linarith
    -- Bayes' rule at I's information set
    have hpos : 0 < probInfo jvGame (jvGame.assemble F) 3 := by
      rw [(hpi _).2.2.2]
      norm_num [jvGame_assemble_eq, hP1, hP2, hE2, hE2']
    have hprob : probInfo jvGame (jvGame.assemble F) 3 = 1 := by
      rw [(hpi _).2.2.2]
      norm_num [jvGame_assemble_eq, hP1, hP2, hE2, hE2']
    have b1 := hBy 3 hpos [1] (by rw [hI3]; simp)
    have b2 := hBy 3 hpos [0, 2] (by rw [hI3]; simp)
    have b3 := hBy 3 hpos [0, 1, 2] (by rw [hI3]; simp)
    rw [hprob, (hr _).1] at b1
    rw [hprob, (hr _).2.2.1] at b2
    rw [hprob, (hr _).2.2.2.2] at b3
    replace b1 : μ [1] = 0 := by simpa [jvGame_assemble_eq, hP1] using b1
    replace b2 : μ [0, 2] = 1 := by simpa [jvGame_assemble_eq, hP2, hE2] using b2
    replace b3 : μ [0, 1, 2] = 0 := by simpa [jvGame_assemble_eq, hE2'] using b3
    -- I accommodates
    have hIa := hSR 3 2 rfl _ (jvGame_beh_update hF (i := 2) (k := 3) (a := 1) (by decide))
    rw [(hcp _ _ _).2.2.2, (hcp _ _ _).2.2.2, b1, b2, b3] at hIa
    simp [(hc _ _).2.1, jvGame_assemble_eq, dirac] at hIa
    have hI : F 2 3 1 = 1 := by nlinarith [hs0 0, hs0 1]
    have hI' : F 2 3 0 = 0 := by linarith
    -- E1 enters after E2 declines
    have hin := hSR 2 0 rfl _ (jvGame_beh_update hF (i := 0) (k := 2) (a := 0) (by decide))
    rw [(hcp _ _ _).2.2.1, (hcp _ _ _).2.2.1, (hc _ _).2.2.1, (hc _ _).2.2.1] at hin
    simp [jvGame_assemble_eq, hμ2, dirac, hI, hI'] at hin
    have hE1 : F 0 2 0 = 1 := by nlinarith [hr0 0, hr0 1]
    exact ⟨hP2, hE2, hI, hE1, b2, b1, b3⟩

/-- The only subgame of the joint venture game is the game as a whole: every other decision
node either shares I's information set or has a successor in it together with the node `[1]`
outside. -/
theorem jvGame_subgames {x : List (Fin 3)} (hx : IsSubgameRoot jvGame x) : x = [] := by
  have hmem := (mem_decisionNodes _).2 hx.1
  rw [show jvGame.decisionNodes = {[], [1], [2], [0, 2], [1, 2], [0, 1, 2]} by decide] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  have hd : ∀ y ∈ ({[1], [0, 2], [0, 1, 2]} : Finset (List (Fin 3))), jvGame.IsDecision y := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl <;> exact ⟨by decide, 0, by decide⟩
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · exact absurd (hx.2.1 [0, 2] (hd _ (by simp)) rfl) (by decide)
  · exact absurd (hx.2.2 [0, 2] (hd _ (by simp)) (by decide) [1] (hd _ (by simp)) rfl)
      (by decide)
  · exact absurd (hx.2.1 [1] (hd _ (by simp)) rfl) (by decide)
  · exact absurd (hx.2.2 [0, 1, 2] (hd _ (by simp)) (by decide) [1] (hd _ (by simp)) rfl)
      (by decide)
  · exact absurd (hx.2.1 [1] (hd _ (by simp)) rfl) (by decide)

/-- **Example 9.C.2** (MWG, p. 287). The weak PBE is not the only Nash equilibrium, nor the only
SPNE: ((out, out if E2 declines), decline, fight if entry occurs) is a subgame perfect Nash
equilibrium (the only subgame is the whole game, and no player gains by deviating). -/
theorem example_9_C_2_spne : IsSPNE jvGame (pureMoves ![0, 1, 1, 0]) := by
  have hB : IsBehaviorProfile jvGame (pureMoves (I := Fin 3) ![0, 1, 1, 0]) :=
    isBehaviorProfile_pureMoves fun k => by fin_cases k <;> simp [jvGame]
  refine exercise_9_B_2a _ (fun _ hx => jvGame_subgames hx) ⟨hB, fun i g hg => ?_⟩
  rw [(jvGame_cont _ _).2.2.2.2, (jvGame_cont _ _).2.2.2.2]
  have hi3 : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide
  rcases hi3 i with rfl | rfl | rfl
  · have h0 := (hg 0 rfl).1
    have h2 := (hg 2 rfl).1
    simp [jvGame_assemble_eq, pureMoves, dirac]
    nlinarith [h0 1, h0 2, h2 0]
  · simp [jvGame_assemble_eq, pureMoves, dirac]
  · simp [jvGame_assemble_eq, pureMoves, dirac]

end MWG.DynamicGames

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Weak PBE with unreasonable beliefs, and its unique sequential equilibrium

MWG, Example 9.C.4 and Figure 9.C.4 (pp. 289 and 291).

Nature (information set `0`) chooses left (`0`) or right (`1`) with probability `1/2`; player 1
(`0`), not observing nature, chooses `x` (`0`, ending the game with payoffs `(2, 10)`) or `y`
(`1`) at information set `1 = {[0], [1]}`; after `y`, player 2 (`1`), observing neither, chooses
`ℓ` (`0`) or `r` (`1`) at information set `2 = {[1, 0], [1, 1]}`.

* `example_9_C_4_weakPBE`: `(x, ℓ)` with beliefs `(1/2, 1/2)` for player 1 and `(0.9, 0.1)` for
  player 2 is a weak PBE (player 2's information set is off the equilibrium path).
* `example_9_C_4_consistent_beliefs`: every consistent assessment gives player 2 beliefs
  `(1/2, 1/2)` (player 1's deviation to `y` cannot depend on nature's move), so the weak PBE's
  beliefs are not consistent (`example_9_C_4_not_consistent`).
* `example_9_C_4_sequential`: `(y, r)` with beliefs `(1/2, 1/2)` at both information sets is the
  unique sequential equilibrium.
-/

namespace MWG.DynamicGames

open MWG.NoncooperativeGames MWG.NoncooperativeGames.ExtensiveForm Filter Topology

/-- Payoffs `(u₁, u₂)` of Figure 9.C.4. -/
def ncPay (i : Fin 2) (z : List (Fin 2)) : ℝ :=
  if z = [0, 0] ∨ z = [0, 1] then ![2, 10] i
  else if z = [0, 1, 0] ∨ z = [0, 1, 1] then ![0, 5] i
  else if z = [1, 1, 0] then ![5, 2] i else if z = [1, 1, 1] then ![5, 10] i else 0

/-- **Example 9.C.4, Figure 9.C.4** (MWG, p. 289). -/
noncomputable def ncGame : ExtensiveForm (Fin 2) (Fin 2) (Fin 3) where
  nodes := {[], [0], [1], [0, 0], [1, 0], [0, 1], [1, 1], [0, 1, 0], [1, 1, 0], [0, 1, 1],
    [1, 1, 1]}
  nil_mem := by decide
  tail_mem := by decide
  info x := if x = [] then 0 else if x.length = 1 then 1 else 2
  avail _ := Finset.univ
  avail_spec := by decide
  info_surj := by decide
  player := ![none, some 0, some 1]
  natureProb k _ := if k = 0 then 1 / 2 else 0
  nature_nonneg := fun k _ _ => by split_ifs <;> norm_num
  nature_zero := fun _ _ a ha => absurd (Finset.mem_univ a) ha
  nature_sum := fun k hk => by
    have : k = 0 := by fin_cases k <;> simp_all
    subst this
    norm_num [Fin.sum_univ_two]
  payoff := ncPay

theorem ncGame_assemble (F : Fin 2 → Fin 3 → Fin 2 → ℝ) :
    ncGame.assemble F 0 = (fun _ => 1 / 2) ∧ ncGame.assemble F 1 = F 0 1 ∧
      ncGame.assemble F 2 = F 1 2 :=
  ⟨by rw [ncGame.assemble_of_none _ rfl]; rfl, ncGame.assemble_of_some _ rfl,
    ncGame.assemble_of_some _ rfl⟩

/-- Continuation payoffs in the game of Figure 9.C.4. -/
theorem ncGame_cont (f : Fin 3 → Fin 2 → ℝ) (i : Fin 2) :
    cont ncGame f [1, 0] i = f 2 0 * ![0, 5] i + f 2 1 * ![5, 2] i ∧
    cont ncGame f [1, 1] i = f 2 0 * ![0, 5] i + f 2 1 * ![5, 10] i ∧
    cont ncGame f [0] i = f 1 0 * ![2, 10] i + f 1 1 * (f 2 0 * ![0, 5] i + f 2 1 * ![5, 2] i) ∧
    cont ncGame f [1] i =
      f 1 0 * ![2, 10] i + f 1 1 * (f 2 0 * ![0, 5] i + f 2 1 * ![5, 10] i) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [cont_unfold, ncGame, ncPay, Fin.sum_univ_two]

theorem ncGame_infoSet : ncGame.infoSet 0 = {[]} ∧ ncGame.infoSet 1 = {[0], [1]} ∧
    ncGame.infoSet 2 = {[1, 0], [1, 1]} := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

theorem ncGame_condPayoff (f : Fin 3 → Fin 2 → ℝ) (μ : List (Fin 2) → ℝ) (i : Fin 2) :
    condPayoff ncGame f μ 1 i = μ [0] * cont ncGame f [0] i + μ [1] * cont ncGame f [1] i ∧
    condPayoff ncGame f μ 2 i = μ [1, 0] * cont ncGame f [1, 0] i +
      μ [1, 1] * cont ncGame f [1, 1] i := by
  obtain ⟨-, h1, h2⟩ := ncGame_infoSet
  unfold condPayoff
  rw [h1, h2]
  constructor <;> rw [Finset.sum_insert (by decide), Finset.sum_singleton]

theorem ncGame_reach (f : Fin 3 → Fin 2 → ℝ) :
    ncGame.reach f [0] = f 0 0 ∧ ncGame.reach f [1] = f 0 1 ∧
    ncGame.reach f [1, 0] = f 0 0 * f 1 1 ∧ ncGame.reach f [1, 1] = f 0 1 * f 1 1 ∧
    probInfo ncGame f 0 = 1 ∧ probInfo ncGame f 1 = f 0 0 + f 0 1 ∧
    probInfo ncGame f 2 = f 0 0 * f 1 1 + f 0 1 * f 1 1 := by
  obtain ⟨h0, h1, h2⟩ := ncGame_infoSet
  refine ⟨by simp [ncGame], by simp [ncGame], by simp [ncGame], by simp [ncGame], ?_, ?_, ?_⟩ <;>
    unfold probInfo
  · rw [h0]; simp
  · rw [h1, Finset.sum_insert (by decide), Finset.sum_singleton]; simp [ncGame]
  · rw [h2, Finset.sum_insert (by decide), Finset.sum_singleton]; simp [ncGame]

/-- The beliefs of the weak PBE of Example 9.C.4: `(1/2, 1/2)` for player 1 and `(0.9, 0.1)` for
player 2. -/
noncomputable def ncBelief (x : List (Fin 2)) : ℝ :=
  if x = [0] ∨ x = [1] then 1 / 2 else if x = [1, 0] then 9 / 10
  else if x = [1, 1] then 1 / 10 else 1

/-- The beliefs `(1/2, 1/2)` at both information sets. -/
noncomputable def ncHalf (x : List (Fin 2)) : ℝ := if x = [] then 1 else 1 / 2

theorem ncGame_beh {g : Fin 3 → Fin 2 → ℝ} {i : Fin 2} {k : Fin 3}
    (hg : ncGame.IsBehaviorStrategy i g) (hk : ncGame.player k = some i) :
    (∀ a, 0 ≤ g k a) ∧ g k 0 + g k 1 = 1 :=
  ⟨(hg k hk).1, by simpa [ncGame, Fin.sum_univ_two] using (hg k hk).2.2⟩

theorem ncGame_k3 (k : Fin 3) : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp

/-- The beliefs `ncBelief` and `ncHalf` are systems of beliefs. -/
theorem ncGame_beliefSystems : IsBeliefSystem ncGame ncBelief ∧ IsBeliefSystem ncGame ncHalf := by
  obtain ⟨h0, h1, h2⟩ := ncGame_infoSet
  refine ⟨⟨fun x _ => ?_, fun k => ?_⟩, ⟨fun x _ => ?_, fun k => ?_⟩⟩
  · unfold ncBelief; split_ifs <;> norm_num
  · rcases ncGame_k3 k with rfl | rfl | rfl
    · simp [h0, ncBelief]
    · rw [h1, Finset.sum_insert (by decide), Finset.sum_singleton]; norm_num [ncBelief]
    · rw [h2, Finset.sum_insert (by decide), Finset.sum_singleton]; norm_num [ncBelief]
  · unfold ncHalf; split_ifs <;> norm_num
  · rcases ncGame_k3 k with rfl | rfl | rfl
    · simp [h0, ncHalf]
    · rw [h1, Finset.sum_insert (by decide), Finset.sum_singleton]; norm_num [ncHalf]
    · rw [h2, Finset.sum_insert (by decide), Finset.sum_singleton]; norm_num [ncHalf]

/-- **Example 9.C.4** (MWG, p. 289). Player 1 playing `x`, player 2 playing `ℓ`, with beliefs
`(1/2, 1/2)` for player 1 and `(0.9, 0.1)` for player 2, is a weak perfect Bayesian
equilibrium. -/
theorem example_9_C_4_weakPBE : IsWeakPBE ncGame (pureMoves ![0, 0, 0]) ncBelief := by
  obtain ⟨h0, h1, h2⟩ := ncGame_infoSet
  have hB : IsBehaviorProfile ncGame (pureMoves (I := Fin 2) ![0, 0, 0]) :=
    isBehaviorProfile_pureMoves fun _ => Finset.mem_univ _
  refine ⟨hB, ncGame_beliefSystems.1, fun k i hi g hg => ?_, fun k hk x hx => ?_⟩
  · have hA := ncGame_assemble (Function.update (pureMoves ![0, 0, 0]) i g)
    have hA' := ncGame_assemble (pureMoves ![0, 0, 0])
    rcases ncGame_k3 k with rfl | rfl | rfl
    · exact absurd hi (by simp [ncGame])
    · obtain rfl : i = 0 := (Option.some.inj (hi : some 0 = some i)).symm
      obtain ⟨hg0, hg1⟩ := ncGame_beh hg (k := 1) rfl
      rw [(ncGame_condPayoff _ _ _).1, (ncGame_condPayoff _ _ _).1, (ncGame_cont _ _).2.2.1,
        (ncGame_cont _ _).2.2.1, (ncGame_cont _ _).2.2.2, (ncGame_cont _ _).2.2.2, hA.2.1,
        hA.2.2, hA'.2.1, hA'.2.2]
      simp [pureMoves, dirac, ncBelief]
      nlinarith [hg0 0, hg0 1]
    · obtain rfl : i = 1 := (Option.some.inj (hi : some 1 = some i)).symm
      obtain ⟨hg0, hg1⟩ := ncGame_beh hg (k := 2) rfl
      rw [(ncGame_condPayoff _ _ _).2, (ncGame_condPayoff _ _ _).2, (ncGame_cont _ _).1,
        (ncGame_cont _ _).1, (ncGame_cont _ _).2.1, (ncGame_cont _ _).2.1, hA.2.2, hA'.2.2]
      simp [pureMoves, dirac, ncBelief]
      nlinarith [hg0 0, hg0 1]
  · have hA' := ncGame_assemble (pureMoves ![0, 0, 0])
    obtain ⟨r0, r1, r10, r11, p0, p1, p2⟩ := ncGame_reach (ncGame.assemble (pureMoves ![0, 0, 0]))
    rcases ncGame_k3 k with rfl | rfl | rfl
    · rw [h0, Finset.mem_singleton] at hx
      subst hx
      simp [p0, ncBelief]
    · rw [h1] at hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · rw [r0, p1, hA'.1]; norm_num [ncBelief]
      · rw [r1, p1, hA'.1]; norm_num [ncBelief]
    · rw [p2, hA'.2.1] at hk
      simp [pureMoves, dirac] at hk

/-- Beliefs derived from a totally mixed profile by Bayes' rule are `1/2` at the nodes of both
players' information sets. -/
theorem ncGame_bayes_half {F : Fin 2 → Fin 3 → Fin 2 → ℝ} (hTM : IsTotallyMixedB ncGame F)
    {x : List (Fin 2)} (hx : x = [1, 0] ∨ x = [1, 1] ∨ x = [0] ∨ x = [1]) :
    bayesBelief ncGame (ncGame.assemble F) x = 1 / 2 := by
  have hA := ncGame_assemble F
  obtain ⟨r0, r1, r10, r11, -, p1, p2⟩ := ncGame_reach (ncGame.assemble F)
  have hpos : 0 < F 0 1 1 := hTM.2 0 1 rfl 1 (Finset.mem_univ _)
  unfold bayesBelief
  rcases hx with rfl | rfl | rfl | rfl
  · rw [show ncGame.info [1, 0] = 2 from rfl, r10, p2, hA.1, hA.2.1]
    field_simp
    ring
  · rw [show ncGame.info [1, 1] = 2 from rfl, r11, p2, hA.1, hA.2.1]
    field_simp
    ring
  · rw [show ncGame.info [0] = 1 from rfl, r0, p1, hA.1]
    norm_num
  · rw [show ncGame.info [1] = 1 from rfl, r1, p1, hA.1]
    norm_num

/-- **Example 9.C.4 continued** (MWG, p. 291). All beliefs derived from totally mixed strategies
give equal probability to the two nodes of player 2's information set; so every consistent
assessment has `μ([y, left]) = μ([y, right]) = 1/2`, and also `1/2` at player 1's nodes. -/
theorem example_9_C_4_consistent_beliefs {F : Fin 2 → Fin 3 → Fin 2 → ℝ} {μ : List (Fin 2) → ℝ}
    (h : IsConsistent ncGame F μ) :
    μ [1, 0] = 1 / 2 ∧ μ [1, 1] = 1 / 2 ∧ μ [0] = 1 / 2 ∧ μ [1] = 1 / 2 := by
  obtain ⟨Fs, hTM, -, hbel⟩ := h
  have hconst : ∀ x, x = [1, 0] ∨ x = [1, 1] ∨ x = [0] ∨ x = [1] →
      ∀ n, bayesBelief ncGame (ncGame.assemble (Fs n)) x = 1 / 2 :=
    fun x hx n => ncGame_bayes_half (hTM n) hx
  have hlim : ∀ x, ncGame.IsDecision x → (x = [1, 0] ∨ x = [1, 1] ∨ x = [0] ∨ x = [1]) →
      μ x = 1 / 2 := fun x hd hx =>
    tendsto_nhds_unique (hbel x hd) (by simp only [hconst x hx]; exact tendsto_const_nhds)
  have hd : ∀ x ∈ ({[1, 0], [1, 1], [0], [1]} : Finset (List (Fin 2))), ncGame.IsDecision x := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> exact ⟨by decide, 0, by decide⟩
  exact ⟨hlim _ (hd _ (by simp)) (by simp), hlim _ (hd _ (by simp)) (by simp),
    hlim _ (hd _ (by simp)) (by simp), hlim _ (hd _ (by simp)) (by simp)⟩

/-- **Example 9.C.4** (MWG, p. 289). The beliefs of the weak PBE `example_9_C_4_weakPBE` are not
consistent: no sequence of totally mixed strategies generates them. -/
theorem example_9_C_4_not_consistent (F : Fin 2 → Fin 3 → Fin 2 → ℝ) :
    ¬ IsConsistent ncGame F ncBelief := fun h => by
  have := (example_9_C_4_consistent_beliefs h).1
  norm_num [ncBelief] at this

/-- Playing `a` at information set `k` and following `F i` elsewhere is a behaviour strategy. -/
theorem ncGame_beh_update {F : Fin 2 → Fin 3 → Fin 2 → ℝ} (hF : IsBehaviorProfile ncGame F)
    (i : Fin 2) (k : Fin 3) (a : Fin 2) :
    ncGame.IsBehaviorStrategy i (Function.update (F i) k (dirac a)) := by
  intro k' hk'
  by_cases hkk : k' = k
  · subst hkk
    simp only [Function.update_self]
    refine ⟨fun b => by unfold dirac; split_ifs <;> norm_num,
      fun b hb => absurd (Finset.mem_univ b) hb, ?_⟩
    simp only [dirac]
    rw [Finset.sum_ite_eq']
    simp [ncGame]
  · simp only [Function.update_of_ne hkk]
    exact hF i k' hk'

/-- **Example 9.C.4 continued** (MWG, p. 291). `(y, r)` with beliefs `(1/2, 1/2)` at both
information sets is a sequential equilibrium, and it is the unique one: in every sequential
equilibrium player 1 plays `y` and player 2 plays `r` for sure, with beliefs `1/2`. -/
theorem example_9_C_4_sequential :
    IsSequentialEq ncGame (pureMoves ![0, 1, 1]) ncHalf ∧
    ∀ F μ, IsSequentialEq ncGame F μ → F 0 1 1 = 1 ∧ F 1 2 1 = 1 ∧
      μ [1, 0] = 1 / 2 ∧ μ [1, 1] = 1 / 2 := by
  have hB : IsBehaviorProfile ncGame (pureMoves (I := Fin 2) ![0, 1, 1]) :=
    isBehaviorProfile_pureMoves fun _ => Finset.mem_univ _
  constructor
  · refine ⟨hB, ncGame_beliefSystems.2, fun k i hi g hg => ?_, ?_⟩
    · have hA := ncGame_assemble (Function.update (pureMoves ![0, 1, 1]) i g)
      have hA' := ncGame_assemble (pureMoves ![0, 1, 1])
      rcases ncGame_k3 k with rfl | rfl | rfl
      · exact absurd hi (by simp [ncGame])
      · obtain rfl : i = 0 := (Option.some.inj (hi : some 0 = some i)).symm
        obtain ⟨hg0, hg1⟩ := ncGame_beh hg (k := 1) rfl
        rw [(ncGame_condPayoff _ _ _).1, (ncGame_condPayoff _ _ _).1, (ncGame_cont _ _).2.2.1,
          (ncGame_cont _ _).2.2.1, (ncGame_cont _ _).2.2.2, (ncGame_cont _ _).2.2.2, hA.2.1,
          hA.2.2, hA'.2.1, hA'.2.2]
        simp [pureMoves, dirac, ncHalf]
        nlinarith [hg0 0, hg0 1]
      · obtain rfl : i = 1 := (Option.some.inj (hi : some 1 = some i)).symm
        obtain ⟨hg0, hg1⟩ := ncGame_beh hg (k := 2) rfl
        rw [(ncGame_condPayoff _ _ _).2, (ncGame_condPayoff _ _ _).2, (ncGame_cont _ _).1,
          (ncGame_cont _ _).1, (ncGame_cont _ _).2.1, (ncGame_cont _ _).2.1, hA.2.2, hA'.2.2]
        simp [pureMoves, dirac, ncHalf]
        nlinarith [hg0 0, hg0 1]
    · -- the trembles: each player puts `1 / (2 (n + 1))` on every action
      set ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hε
      have hε0 : ∀ n, 0 < ε n := fun n => by positivity
      have hε1 : ∀ n, ε n ≤ 1 := fun n => by
        rw [hε, div_le_one (by positivity)]
        linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
      set Fs : ℕ → Fin 2 → Fin 3 → Fin 2 → ℝ :=
        fun n i k a => (1 - ε n) * pureMoves ![0, 1, 1] i k a + ε n / 2 with hFs
      have hdir : ∀ (i : Fin 2) (k : Fin 3) (a : Fin 2),
          0 ≤ pureMoves (I := Fin 2) (![0, 1, 1] : Fin 3 → Fin 2) i k a := by
        intro i k a; unfold pureMoves dirac; split_ifs <;> norm_num
      have hTM : ∀ n, IsTotallyMixedB ncGame (Fs n) := by
        intro n
        refine ⟨fun i k _ => ⟨fun a => ?_, fun a ha => absurd (Finset.mem_univ a) ha, ?_⟩,
          fun i k _ a _ => ?_⟩
        · have := hε0 n
          simp only [hFs]
          nlinarith [hdir i k a, hε1 n]
        · rw [show ncGame.avail k = Finset.univ from rfl]
          simp only [hFs, Fin.sum_univ_two, pureMoves, dirac]
          have h2 : ∀ c : Fin 2, (if (0 : Fin 2) = c then (1 : ℝ) else 0) +
              (if (1 : Fin 2) = c then 1 else 0) = 1 := by
            intro c; fin_cases c <;> norm_num
          linear_combination (1 - ε n) * h2 (![0, 1, 1] k)
        · have := hε0 n
          simp only [hFs]
          nlinarith [hdir i k a, hε1 n]
      have hlimε : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
      have hlim : Tendsto Fs atTop (𝓝 (pureMoves ![0, 1, 1])) := by
        refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun k => tendsto_pi_nhds.2 fun a => ?_
        have h1 : Tendsto (fun n => (1 - ε n) * pureMoves (I := Fin 2)
            (![0, 1, 1] : Fin 3 → Fin 2) i k a + ε n / 2) atTop
            (𝓝 ((1 - 0) * pureMoves (I := Fin 2) (![0, 1, 1] : Fin 3 → Fin 2) i k a + 0 / 2)) :=
          ((tendsto_const_nhds.sub hlimε).mul tendsto_const_nhds).add (hlimε.div_const 2)
        simpa [hFs] using h1
      refine ⟨Fs, hTM, hlim, fun x hx => ?_⟩
      have hmem := (mem_decisionNodes _).2 hx
      rw [show ncGame.decisionNodes = {[], [0], [1], [1, 0], [1, 1]} by decide] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with rfl | hx'
      · have : ∀ n, bayesBelief ncGame (ncGame.assemble (Fs n)) [] = 1 := by
          intro n
          unfold bayesBelief
          rw [show ncGame.info [] = 0 from rfl, (ncGame_reach _).2.2.2.2.1]
          simp
        simp only [this, ncHalf, ↓reduceIte]
        exact tendsto_const_nhds
      · have hne : x ≠ [] := by rcases hx' with rfl | rfl | rfl | rfl <;> simp
        have : ∀ n, bayesBelief ncGame (ncGame.assemble (Fs n)) x = 1 / 2 := fun n =>
          ncGame_bayes_half (hTM n) (by tauto)
        simp only [this, ncHalf, hne, ↓reduceIte]
        exact tendsto_const_nhds
  · intro F μ ⟨hF, hμ, hSR, hC⟩
    obtain ⟨b10, b11, b0, b1⟩ := example_9_C_4_consistent_beliefs hC
    obtain ⟨hp0, hp1⟩ := ncGame_beh (hF 0) (k := 1) rfl
    obtain ⟨hq0, hq1⟩ := ncGame_beh (hF 1) (k := 2) rfl
    -- player 2 plays r
    have hr := hSR 2 1 rfl _ (ncGame_beh_update hF 1 2 1)
    have hA := ncGame_assemble (Function.update F 1 (Function.update (F 1) 2 (dirac 1)))
    have hA' := ncGame_assemble F
    rw [(ncGame_condPayoff _ _ _).2, (ncGame_condPayoff _ _ _).2, (ncGame_cont _ _).1,
      (ncGame_cont _ _).1, (ncGame_cont _ _).2.1, (ncGame_cont _ _).2.1, hA.2.2, hA'.2.2,
      b10, b11] at hr
    simp [dirac] at hr
    have hR : F 1 2 1 = 1 := by nlinarith [hq0 0, hq0 1]
    have hR' : F 1 2 0 = 0 := by linarith
    -- player 1 plays y
    have hy := hSR 1 0 rfl _ (ncGame_beh_update hF 0 1 1)
    have hA1 := ncGame_assemble (Function.update F 0 (Function.update (F 0) 1 (dirac 1)))
    rw [(ncGame_condPayoff _ _ _).1, (ncGame_condPayoff _ _ _).1, (ncGame_cont _ _).2.2.1,
      (ncGame_cont _ _).2.2.1, (ncGame_cont _ _).2.2.2, (ncGame_cont _ _).2.2.2, hA1.2.1,
      hA1.2.2, hA'.2.1, hA'.2.2, b0, b1] at hy
    simp [dirac, hR, hR'] at hy
    have hY : F 0 1 1 = 1 := by nlinarith [hp0 0, hp0 1]
    exact ⟨hY, hR, b10, b11⟩

end MWG.DynamicGames

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Extensive form trembling-hand perfection in examples

MWG, Appendix B, Figures 9.BB.1 and 9.BB.2 (pp. 299-301).

* `isEFTHP_eq_zero_of_worse`: in an extensive form trembling-hand perfect equilibrium, an agent
  never plays an action `a` that does worse than another action `b` against every totally mixed
  profile (in the agent normal form `a` is then never a best response in any perturbed game).
* `figure_9_BB_2`: in the entry game of Figure 9.BB.2, (out, fight) with beliefs on In₁ is a
  sequential equilibrium, but it is not extensive form trembling-hand perfect: in every EFTHP
  the incumbent accommodates for sure (fighting is worse against every totally mixed
  profile, since it is never better at In₁ and worse at In₂).
-/

namespace MWG.DynamicGames

open MWG.NoncooperativeGames MWG.NoncooperativeGames.ExtensiveForm MWG.SimultaneousMoveGames
  Filter Topology

variable {I A H : Type*} (G : ExtensiveForm I A H) [DecidableEq A] [Fintype A] [DecidableEq I]
  [DecidableEq H]

omit [DecidableEq I] in
/-- **Appendix B** (MWG, p. 300). In an extensive form trembling-hand perfect equilibrium of a
game without absent-mindedness, the agent at information set `k` puts probability zero on an
action `a` that is worse for its owner than another action `b` against every totally mixed
profile. -/
theorem isEFTHP_eq_zero_of_worse [Fintype H] (hNA : G.NoAbsentMindedness) {F : I → H → A → ℝ}
    (hF : IsEFTHP G F) {k : H} {i : I} (hk : G.player k = some i) {a b : A}
    (ha : a ∈ G.avail k) (hb : b ∈ G.avail k)
    (hworse : ∀ Fp, IsTotallyMixedB G Fp →
      ∑ x ∈ G.infoSet k, G.reach (G.assemble Fp) x *
        (cont G (G.assemble Fp) (a :: x) i - cont G (G.assemble Fp) (b :: x) i) < 0) :
    G.assemble F k a = 0 := by
  obtain ⟨-, σ, ⟨-, ε, σs, hε, hε0, hσs, hlim⟩, hFσ⟩ := hF
  have hne : G.player k ≠ none := by rw [hk]; simp
  set ag : Agent G := ⟨k, hne⟩
  have hown : owner G ag = i := by
    have := player_owner G ag
    rw [hk] at this
    exact (Option.some.inj this).symm
  set sa := agentPure G ag ⟨a, ha⟩
  set sb := agentPure G ag ⟨b, hb⟩
  have hmix : ∀ n ag', IsMixedStrategy (σs n ag') := fun n ag' =>
    isMixedStrategy_of_mem_perturbedSet (hε n) ((hσs n).1 ag')
  have heq : ∀ n, σs n ag sa = ε n ag sa := by
    intro n
    refine perturbedNash_eq_of_not_best (hσs n) ag (b := sb) ?_
    have hmixU : ∀ s, ∀ ag', IsMixedStrategy (Function.update (σs n) ag (pureMixed s) ag') := by
      intro s ag'
      by_cases h : ag' = ag
      · subst h
        rw [Function.update_self]
        exact isMixedStrategy_pureMixed s
      · rw [Function.update_of_ne h]
        exact hmix n ag'
    rw [agentNF_mixedPayoff G hNA (hmixU sa), agentNF_mixedPayoff G hNA (hmixU sb),
      assemble_agentProfile_update G _ ag ha, assemble_agentProfile_update G _ ag hb, hown]
    have hdiff := cont_update_dirac_sub G hNA (G.assemble (agentProfile G (σs n))) k ha hb i
    have hTM : IsTotallyMixedB G (agentProfile G (σs n)) := by
      refine ⟨isBehaviorProfile_agentProfile G (hmix n), fun j k' hk' c hc => ?_⟩
      have hne' : G.player k' ≠ none := by rw [hk']; simp
      have := assemble_agentProfile_apply G (σs n) ⟨k', hne'⟩ c
      rw [G.assemble_of_some _ hk'] at this
      rw [this]
      simp only [hc, ↓reduceDIte]
      exact lt_of_lt_of_le ((hε n).1 _ _).1 (((hσs n).1 _).1 _)
    have := hworse _ hTM
    rw [← hdiff] at this
    linarith
  have h1 : Tendsto (fun n => σs n ag sa) atTop (𝓝 (σ ag sa)) :=
    tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hlim ag) sa
  have h2 : Tendsto (fun n => σs n ag sa) atTop (𝓝 0) := by
    simp only [heq]
    exact hε0 ag sa
  have hσ0 : σ ag sa = 0 := tendsto_nhds_unique h1 h2
  rw [hFσ k hne, assemble_agentProfile_apply G σ ag a]
  split_ifs with h
  · exact hσ0
  · exact absurd ha h

/-- **Figure 9.BB.2** (MWG, p. 301): payoffs after entry `(−1, 0)`, `(3, 0)` (In₁) and
`(−1, −1)`, `(2, 1)` (In₂). -/
abbrev fig9BB2 : ExtensiveForm (Fin 2) (Fin 3) (Fin 2) :=
  entryTwo ![0, 2] ![![![-1, 0], ![3, 0]], ![![-1, -1], ![2, 1]]]

theorem entryTwo_noAbsentMindedness (o : Fin 2 → ℝ) (t : Fin 2 → Fin 2 → Fin 2 → ℝ) :
    (entryTwo o t).NoAbsentMindedness := by
  have : (entryTwo (fun _ => 0) (fun _ _ _ => 0)).NoAbsentMindedness := by
    unfold ExtensiveForm.NoAbsentMindedness; decide
  exact this

/-- In the entry game with two entry strategies, E staying out and I choosing `0`,
with beliefs putting probability one on In₁, is a consistent assessment: E trembles to In₁ with
probability `ε` and to In₂ with probability `ε²`, I trembles with probability `ε`. -/
theorem entryTwo_consistent_leftBelief_zero (o : Fin 2 → ℝ) (t : Fin 2 → Fin 2 → Fin 2 → ℝ) :
    IsConsistent (entryTwo o t) (pureMoves ![0, 0]) leftBelief := by
  have hr := entryTwo_reach o t
  have hI := entryTwo_infoSet o t
  -- trembles: E plays In₁ with probability `ε`, In₂ with `ε²`; I deviates with `ε`
  set ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 2) with hε
  have hε0 : ∀ n, 0 < ε n := fun n => by positivity
  have hε1 : ∀ n, ε n ≤ 1 / 2 := fun n => by
    simp only [hε]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  set Fs : ℕ → Fin 2 → Fin 2 → Fin 3 → ℝ := fun n _ k =>
    if k = 0 then ![1 - ε n - ε n ^ 2, ε n, ε n ^ 2]
    else ![1 - ε n, ε n, 0] with hFs
  have hTM : ∀ n, IsTotallyMixedB (entryTwo o t) (Fs n) := by
    intro n
    have e0 := hε0 n
    have e1 := hε1 n
    have hsq : ε n ^ 2 ≤ ε n / 2 := by nlinarith
    refine ⟨fun i k hk => ?_, fun i k hk a ha => ?_⟩
    · obtain rfl : k = i := Option.some.inj hk
      fin_cases k
      · refine ⟨fun a => ?_, fun a ha => absurd (by simp [entryTwo]) ha, ?_⟩
        · fin_cases a <;> simp [hFs] <;> nlinarith
        · simp [hFs, entryTwo, Fin.sum_univ_three]
          ring
      · refine ⟨fun a => ?_, fun a ha => ?_, ?_⟩
        · fin_cases a <;> simp [hFs] <;> linarith
        · have : a = 2 := by
            fin_cases a <;> simp [entryTwo] at ha ⊢
          subst this
          simp [hFs]
        · simp [hFs, entryTwo]
    · obtain rfl : k = i := Option.some.inj hk
      fin_cases k
      · fin_cases a <;> simp [hFs] <;> nlinarith
      · fin_cases a <;> simp [hFs, entryTwo] at ha ⊢ <;> linarith
  have hlimε : Tendsto ε atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)
    refine h.congr fun n => ?_
    simp only [hε, Nat.cast_add, Nat.cast_one]
    ring
  have hlim : Tendsto Fs atTop (𝓝 (pureMoves ![0, 0])) := by
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun k => tendsto_pi_nhds.2 fun a => ?_
    have hsq : Tendsto (fun n => ε n ^ 2) atTop (𝓝 0) := by
      simpa using hlimε.pow 2
    fin_cases k <;> fin_cases a
    · simpa [hFs, pureMoves, dirac] using
        ((tendsto_const_nhds (x := (1 : ℝ))).sub hlimε).sub hsq
    · simpa [hFs, pureMoves, dirac] using hlimε
    · simpa [hFs, pureMoves, dirac] using hsq
    · simpa [hFs, pureMoves, dirac] using (tendsto_const_nhds (x := (1 : ℝ))).sub hlimε
    · simpa [hFs, pureMoves, dirac] using hlimε
    · simp [hFs, pureMoves, dirac]
  refine ⟨Fs, hTM, hlim, fun x hx => ?_⟩
  have hdn : (entryTwo o t).decisionNodes = {[], [1], [2]} :=
    (by decide : (entryTwo (fun _ => 0) (fun _ _ _ => 0)).decisionNodes = {[], [1], [2]})
  have hmem := (mem_decisionNodes _).2 hx
  rw [hdn] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  have hasm : ∀ n, (entryTwo o t).assemble (Fs n) 0 = Fs n 0 0 := fun n => entryTwo_assemble _ _ _ 0
  have hprob : ∀ n, probInfo (entryTwo o t) ((entryTwo o t).assemble (Fs n)) 1 = ε n + ε n ^ 2 := by
    intro n
    rw [(hr _).2.2, hasm]
    simp [hFs]
  rcases hmem with rfl | rfl | rfl
  · have : ∀ n, bayesBelief (entryTwo o t) ((entryTwo o t).assemble (Fs n)) [] = 1 := by
      intro n
      unfold bayesBelief probInfo
      rw [show (entryTwo o t).info [] = 0 from rfl, hI.1]
      simp
    simp only [this, leftBelief]
    exact tendsto_const_nhds
  · have : ∀ n, bayesBelief (entryTwo o t) ((entryTwo o t).assemble (Fs n)) [1] =
        1 / (1 + ε n) := by
      intro n
      unfold bayesBelief
      rw [show (entryTwo o t).info [1] = 1 from rfl, hprob, (hr _).1, hasm]
      have := hε0 n
      simp only [hFs, ↓reduceIte, Matrix.cons_val_one, Matrix.cons_val_zero]
      field_simp
    simp only [this, leftBelief]
    have := ((tendsto_const_nhds (x := (1 : ℝ))).add hlimε).inv₀ (by norm_num)
    simpa using this
  · have : ∀ n, bayesBelief (entryTwo o t) ((entryTwo o t).assemble (Fs n)) [2] =
        ε n / (1 + ε n) := by
      intro n
      unfold bayesBelief
      rw [show (entryTwo o t).info [2] = 1 from rfl, hprob, (hr _).2.1, hasm]
      have := hε0 n
      simp only [hFs, ↓reduceIte]
      simp
      field_simp
    simp only [this, leftBelief]
    have h : Tendsto (fun n => ε n / (1 + ε n)) atTop (𝓝 (0 / (1 + 0))) :=
      hlimε.div (tendsto_const_nhds.add hlimε) (by norm_num)
    simpa using h

/-- In the entry game with two entry strategies, E staying out and I choosing `1`,
with beliefs putting probability one on In₁, is a consistent assessment: E trembles to In₁ with
probability `ε` and to In₂ with probability `ε²`, I trembles with probability `ε`. -/
theorem entryTwo_consistent_leftBelief_one (o : Fin 2 → ℝ) (t : Fin 2 → Fin 2 → Fin 2 → ℝ) :
    IsConsistent (entryTwo o t) (pureMoves ![0, 1]) leftBelief := by
  have hr := entryTwo_reach o t
  have hI := entryTwo_infoSet o t
  -- trembles: E plays In₁ with probability `ε`, In₂ with `ε²`; I deviates with `ε`
  set ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 2) with hε
  have hε0 : ∀ n, 0 < ε n := fun n => by positivity
  have hε1 : ∀ n, ε n ≤ 1 / 2 := fun n => by
    simp only [hε]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  set Fs : ℕ → Fin 2 → Fin 2 → Fin 3 → ℝ := fun n _ k =>
    if k = 0 then ![1 - ε n - ε n ^ 2, ε n, ε n ^ 2]
    else ![ε n, 1 - ε n, 0] with hFs
  have hTM : ∀ n, IsTotallyMixedB (entryTwo o t) (Fs n) := by
    intro n
    have e0 := hε0 n
    have e1 := hε1 n
    have hsq : ε n ^ 2 ≤ ε n / 2 := by nlinarith
    refine ⟨fun i k hk => ?_, fun i k hk a ha => ?_⟩
    · obtain rfl : k = i := Option.some.inj hk
      fin_cases k
      · refine ⟨fun a => ?_, fun a ha => absurd (by simp [entryTwo]) ha, ?_⟩
        · fin_cases a <;> simp [hFs] <;> nlinarith
        · simp [hFs, entryTwo, Fin.sum_univ_three]
          ring
      · refine ⟨fun a => ?_, fun a ha => ?_, ?_⟩
        · fin_cases a <;> simp [hFs] <;> linarith
        · have : a = 2 := by
            fin_cases a <;> simp [entryTwo] at ha ⊢
          subst this
          simp [hFs]
        · simp [hFs, entryTwo]
    · obtain rfl : k = i := Option.some.inj hk
      fin_cases k
      · fin_cases a <;> simp [hFs] <;> nlinarith
      · fin_cases a <;> simp [hFs, entryTwo] at ha ⊢ <;> linarith
  have hlimε : Tendsto ε atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)
    refine h.congr fun n => ?_
    simp only [hε, Nat.cast_add, Nat.cast_one]
    ring
  have hlim : Tendsto Fs atTop (𝓝 (pureMoves ![0, 1])) := by
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun k => tendsto_pi_nhds.2 fun a => ?_
    have hsq : Tendsto (fun n => ε n ^ 2) atTop (𝓝 0) := by
      simpa using hlimε.pow 2
    fin_cases k <;> fin_cases a
    · simpa [hFs, pureMoves, dirac] using
        ((tendsto_const_nhds (x := (1 : ℝ))).sub hlimε).sub hsq
    · simpa [hFs, pureMoves, dirac] using hlimε
    · simpa [hFs, pureMoves, dirac] using hsq
    · simpa [hFs, pureMoves, dirac] using hlimε
    · simpa [hFs, pureMoves, dirac] using (tendsto_const_nhds (x := (1 : ℝ))).sub hlimε
    · simp [hFs, pureMoves, dirac]
  refine ⟨Fs, hTM, hlim, fun x hx => ?_⟩
  have hdn : (entryTwo o t).decisionNodes = {[], [1], [2]} :=
    (by decide : (entryTwo (fun _ => 0) (fun _ _ _ => 0)).decisionNodes = {[], [1], [2]})
  have hmem := (mem_decisionNodes _).2 hx
  rw [hdn] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  have hasm : ∀ n, (entryTwo o t).assemble (Fs n) 0 = Fs n 0 0 := fun n => entryTwo_assemble _ _ _ 0
  have hprob : ∀ n, probInfo (entryTwo o t) ((entryTwo o t).assemble (Fs n)) 1 = ε n + ε n ^ 2 := by
    intro n
    rw [(hr _).2.2, hasm]
    simp [hFs]
  rcases hmem with rfl | rfl | rfl
  · have : ∀ n, bayesBelief (entryTwo o t) ((entryTwo o t).assemble (Fs n)) [] = 1 := by
      intro n
      unfold bayesBelief probInfo
      rw [show (entryTwo o t).info [] = 0 from rfl, hI.1]
      simp
    simp only [this, leftBelief]
    exact tendsto_const_nhds
  · have : ∀ n, bayesBelief (entryTwo o t) ((entryTwo o t).assemble (Fs n)) [1] =
        1 / (1 + ε n) := by
      intro n
      unfold bayesBelief
      rw [show (entryTwo o t).info [1] = 1 from rfl, hprob, (hr _).1, hasm]
      have := hε0 n
      simp only [hFs, ↓reduceIte, Matrix.cons_val_one, Matrix.cons_val_zero]
      field_simp
    simp only [this, leftBelief]
    have := ((tendsto_const_nhds (x := (1 : ℝ))).add hlimε).inv₀ (by norm_num)
    simpa using this
  · have : ∀ n, bayesBelief (entryTwo o t) ((entryTwo o t).assemble (Fs n)) [2] =
        ε n / (1 + ε n) := by
      intro n
      unfold bayesBelief
      rw [show (entryTwo o t).info [2] = 1 from rfl, hprob, (hr _).2.1, hasm]
      have := hε0 n
      simp only [hFs, ↓reduceIte]
      simp
      field_simp
    simp only [this, leftBelief]
    have h : Tendsto (fun n => ε n / (1 + ε n)) atTop (𝓝 (0 / (1 + 0))) :=
      hlimε.div (tendsto_const_nhds.add hlimε) (by norm_num)
    simpa using h

/-- **Figure 9.BB.2** (MWG, pp. 300-301). (out, fight if entry occurs) with beliefs putting
probability one on In₁ is a sequential equilibrium; but it is not extensive form
trembling-hand perfect: in every EFTHP the incumbent accommodates for sure. -/
theorem figure_9_BB_2 :
    IsSequentialEq fig9BB2 (pureMoves ![0, 0]) leftBelief ∧
    ∀ F, IsEFTHP fig9BB2 F → fig9BB2.assemble F 1 0 = 0 := by
  have hc := entryTwo_cont ![0, 2] ![![![-1, 0], ![3, 0]], ![![-1, -1], ![2, 1]]]
  have hr := entryTwo_reach ![0, 2] ![![![-1, 0], ![3, 0]], ![![-1, -1], ![2, 1]]]
  have hI := entryTwo_infoSet ![0, 2] ![![![-1, 0], ![3, 0]], ![![-1, -1], ![2, 1]]]
  have hB : IsBehaviorProfile fig9BB2 (pureMoves (I := Fin 2) ![0, 0]) :=
    isBehaviorProfile_pureMoves fun k => by fin_cases k <;> simp [entryTwo]
  constructor
  · have hW : IsWeakPBE fig9BB2 (pureMoves ![0, 0]) leftBelief := by
      refine entryTwo_weakPBE_of _ _ hB (by simp [leftBelief]) (by simp [leftBelief])
        (by simp [leftBelief]) (by simp [leftBelief]) ?_ ?_ ?_ ?_
      · norm_num [leftBelief, pureMoves, dirac]
      · norm_num [leftBelief, pureMoves, dirac]
      · intro v hv
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
        rcases hv with rfl | rfl | rfl <;> simp [pureMoves, dirac]
      · intro h
        simp [pureMoves, dirac] at h
    exact ⟨hB, hW.2.1, hW.2.2.1, entryTwo_consistent_leftBelief_zero _ _⟩
  · intro F hF
    refine isEFTHP_eq_zero_of_worse _ (entryTwo_noAbsentMindedness _ _) hF rfl
      (b := 1) (by simp [entryTwo]) (by simp [entryTwo]) fun Fp hTM => ?_
    have hpos : 0 < Fp 0 0 2 := hTM.2 0 0 rfl 2 (by simp [entryTwo])
    rw [hI.2, Finset.sum_insert (by decide), Finset.sum_singleton, (hr _).1, (hr _).2.1,
      entryTwo_assemble]
    simp [cont_unfold, entryTwo, entryTwoPay]
    linarith

/-- Payoffs `(u₁, u₂)` of Figure 9.BB.1: `R` gives `(2, 2)`; after `NR`, `(L, ℓ)` gives `(4, 1)`,
`(L, r)` gives `(1, 0)`, `(M, ℓ)` gives `(0, 0)` and `(M, r)` gives `(0, 1)`. -/
def bb1Pay (i : Fin 2) (z : List (Fin 2)) : ℝ :=
  if z = [1] then 2 else if z = [0, 0, 0] then ![4, 1] i else if z = [1, 0, 0] then ![1, 0] i
  else if z = [1, 1, 0] then ![0, 1] i else 0

/-- **Figure 9.BB.1** (MWG, p. 300; van Damme 1983). Player 1 (`0`) chooses `NR` (`0`) or `R`
(`1`) at information set `0`; after `NR` she chooses `L` (`0`) or `M` (`1`) at information set
`1`; player 2 (`1`), not observing that choice, chooses `ℓ` (`0`) or `r` (`1`) at information
set `2 = {[0, 0], [1, 0]}`. -/
def bb1Game : ExtensiveForm (Fin 2) (Fin 2) (Fin 3) where
  nodes := {[], [0], [1], [0, 0], [1, 0], [0, 0, 0], [1, 0, 0], [0, 1, 0], [1, 1, 0]}
  nil_mem := by decide
  tail_mem := by decide
  info x := if x = [] then 0 else if x = [0] then 1 else 2
  avail _ := Finset.univ
  avail_spec := by decide
  info_surj := by decide
  player := ![some 0, some 0, some 1]
  natureProb _ _ := 0
  nature_nonneg := fun k hk => absurd hk (by fin_cases k <;> simp)
  nature_zero := fun k hk => absurd hk (by fin_cases k <;> simp)
  nature_sum := fun k hk => absurd hk (by fin_cases k <;> simp)
  payoff := bb1Pay

theorem bb1Game_assemble (F : Fin 2 → Fin 3 → Fin 2 → ℝ) :
    bb1Game.assemble F 0 = F 0 0 ∧ bb1Game.assemble F 1 = F 0 1 ∧
      bb1Game.assemble F 2 = F 1 2 :=
  ⟨bb1Game.assemble_of_some _ rfl, bb1Game.assemble_of_some _ rfl,
    bb1Game.assemble_of_some _ rfl⟩

/-- Continuation payoffs in the game of Figure 9.BB.1. -/
theorem bb1Game_cont (f : Fin 3 → Fin 2 → ℝ) (i : Fin 2) :
    cont bb1Game f [0] i = f 1 0 * (f 2 0 * ![4, 1] i + f 2 1 * ![1, 0] i) +
      f 1 1 * (f 2 1 * ![0, 1] i) ∧
    cont bb1Game f [] i = f 0 0 * (f 1 0 * (f 2 0 * ![4, 1] i + f 2 1 * ![1, 0] i) +
      f 1 1 * (f 2 1 * ![0, 1] i)) + f 0 1 * 2 := by
  constructor <;> simp [cont_unfold, bb1Game, bb1Pay, Fin.sum_univ_two]

theorem bb1Game_decisionNodes : bb1Game.decisionNodes = {[], [0], [0, 0], [1, 0]} := by decide

/-- The subgames of Figure 9.BB.1 start at the initial node and at player 1's second decision
node. -/
theorem bb1Game_subgames (x : List (Fin 2)) : IsSubgameRoot bb1Game x ↔ x = [] ∨ x = [0] := by
  have hD : ∀ y, bb1Game.IsDecision y ↔ y = [] ∨ y = [0] ∨ y = [0, 0] ∨ y = [1, 0] := by
    intro y
    rw [← mem_decisionNodes, bb1Game_decisionNodes]
    simp
  constructor
  · intro hx
    rcases (hD x).1 hx.1 with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd (hx.2.1 [1, 0] ((hD _).2 (by simp)) rfl) (by decide)
    · exact absurd (hx.2.1 [0, 0] ((hD _).2 (by simp)) rfl) (by decide)
  · rintro (rfl | rfl)
    · refine ⟨(hD _).2 (by simp), fun y hy he => ?_, fun _ _ _ _ _ _ => List.nil_suffix⟩
      rcases (hD y).1 hy with rfl | rfl | rfl | rfl <;>
        first | rfl | exact absurd he (by decide)
    · refine ⟨(hD _).2 (by simp), fun y hy he => ?_, fun y hy hxy y' hy' he => ?_⟩
      · rcases (hD y).1 hy with rfl | rfl | rfl | rfl <;>
          first | rfl | exact absurd he (by decide)
      · rcases (hD y).1 hy with rfl | rfl | rfl | rfl <;>
          rcases (hD y').1 hy' with rfl | rfl | rfl | rfl <;>
          first | decide | exact absurd hxy (by decide) | exact absurd he (by decide)

theorem bb1Game_perfectRecall : bb1Game.PerfectRecall := by
  refine ⟨by unfold ExtensiveForm.NoAbsentMindedness; decide, fun i => ?_⟩
  unfold ExtensiveForm.RecallFor
  fin_cases i <;> decide

/-- Playing `a` at information set `k` and following `F i` elsewhere. -/
theorem bb1Game_beh_update {F : Fin 2 → Fin 3 → Fin 2 → ℝ} (hF : IsBehaviorProfile bb1Game F)
    (i : Fin 2) (k : Fin 3) (a : Fin 2) :
    bb1Game.IsBehaviorStrategy i (Function.update (F i) k (dirac a)) := by
  intro k' hk'
  by_cases hkk : k' = k
  · subst hkk
    simp only [Function.update_self]
    refine ⟨fun b => by unfold dirac; split_ifs <;> norm_num,
      fun b hb => absurd (Finset.mem_univ b) hb, ?_⟩
    simp only [dirac]
    rw [Finset.sum_ite_eq']
    simp [bb1Game]
  · simp only [Function.update_of_ne hkk]
    exact hF i k' hk'

/-- **Figure 9.BB.1** (MWG, p. 299). `((NR, L), ℓ)` is the unique subgame perfect Nash
equilibrium: it is an SPNE, and every SPNE (in behaviour strategies) plays `NR`, `L` and `ℓ` for
sure. -/
theorem figure_9_BB_1_spne :
    IsSPNE bb1Game (pureMoves ![0, 0, 0]) ∧ ∀ F, IsSPNE bb1Game F → ∀ k,
      bb1Game.assemble F k = bb1Game.assemble (pureMoves ![0, 0, 0]) k := by
  have hc := bb1Game_cont
  have hB : IsBehaviorProfile bb1Game (pureMoves (I := Fin 2) ![0, 0, 0]) :=
    isBehaviorProfile_pureMoves fun _ => Finset.mem_univ _
  have hbeh : ∀ {g : Fin 3 → Fin 2 → ℝ} {i : Fin 2} {k : Fin 3},
      bb1Game.IsBehaviorStrategy i g → bb1Game.player k = some i →
      (∀ a, 0 ≤ g k a) ∧ g k 0 + g k 1 = 1 := fun hg hk =>
    ⟨(hg _ hk).1, by simpa [bb1Game, Fin.sum_univ_two] using (hg _ hk).2.2⟩
  constructor
  · refine ⟨hB, fun x hx i g hg => ?_⟩
    have hA := bb1Game_assemble (Function.update (pureMoves ![0, 0, 0]) i g)
    have hA' := bb1Game_assemble (pureMoves ![0, 0, 0])
    have hi2 : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    rcases (bb1Game_subgames x).1 hx with rfl | rfl <;> rcases hi2 with rfl | rfl
    · obtain ⟨g0, g0s⟩ := hbeh hg (k := 0) rfl
      obtain ⟨g1, g1s⟩ := hbeh hg (k := 1) rfl
      rw [(hc _ _).2, (hc _ _).2, hA.1, hA.2.1, hA.2.2, hA'.1, hA'.2.1, hA'.2.2]
      simp [pureMoves, dirac]
      nlinarith [g0 0, g0 1, g1 0, g1 1, mul_nonneg (g0 0) (g1 1)]
    · obtain ⟨g2, g2s⟩ := hbeh hg (k := 2) rfl
      rw [(hc _ _).2, (hc _ _).2, hA.1, hA.2.1, hA.2.2, hA'.1, hA'.2.1, hA'.2.2]
      simp [pureMoves, dirac]
      nlinarith [g2 0, g2 1]
    · obtain ⟨g1, g1s⟩ := hbeh hg (k := 1) rfl
      rw [(hc _ _).1, (hc _ _).1, hA.2.1, hA.2.2, hA'.2.1, hA'.2.2]
      simp [pureMoves, dirac]
      nlinarith [g1 0, g1 1]
    · obtain ⟨g2, g2s⟩ := hbeh hg (k := 2) rfl
      rw [(hc _ _).1, (hc _ _).1, hA.2.1, hA.2.2, hA'.2.1, hA'.2.2]
      simp [pureMoves, dirac]
      nlinarith [g2 0, g2 1]
  · intro F hF
    have hA := bb1Game_assemble F
    obtain ⟨p0, p0s⟩ := hbeh (hF.1 0) (k := 0) rfl
    obtain ⟨p1, p1s⟩ := hbeh (hF.1 0) (k := 1) rfl
    obtain ⟨q, qs⟩ := hbeh (hF.1 1) (k := 2) rfl
    have hsub : IsSubgameRoot bb1Game [0] := (bb1Game_subgames _).2 (Or.inr rfl)
    have hroot : IsSubgameRoot bb1Game [] := (bb1Game_subgames _).2 (Or.inl rfl)
    -- player 1 plays `L` in the subgame
    have hL := hF.2 [0] hsub 0 _ (bb1Game_beh_update hF.1 0 1 0)
    have hAL := bb1Game_assemble (Function.update F 0 (Function.update (F 0) 1 (dirac 0)))
    rw [(hc _ _).1, (hc _ _).1, hAL.2.1, hAL.2.2, hA.2.1, hA.2.2] at hL
    simp [dirac] at hL
    have hpL : F 0 1 0 = 1 := by nlinarith [q 0, q 1, p1 0, p1 1]
    have hpM : F 0 1 1 = 0 := by linarith
    -- player 2 plays `ℓ`
    have hl := hF.2 [0] hsub 1 _ (bb1Game_beh_update hF.1 1 2 0)
    have hAl := bb1Game_assemble (Function.update F 1 (Function.update (F 1) 2 (dirac 0)))
    rw [(hc _ _).1, (hc _ _).1, hAl.2.1, hAl.2.2, hA.2.1, hA.2.2] at hl
    simp [dirac, hpL, hpM] at hl
    have hq : F 1 2 0 = 1 := by linarith [q 1]
    have hq' : F 1 2 1 = 0 := by linarith
    -- player 1 plays `NR`
    have hN := hF.2 [] hroot 0 _ (bb1Game_beh_update hF.1 0 0 0)
    have hAN := bb1Game_assemble (Function.update F 0 (Function.update (F 0) 0 (dirac 0)))
    rw [(hc _ _).2, (hc _ _).2, hAN.1, hAN.2.1, hAN.2.2, hA.1, hA.2.1, hA.2.2] at hN
    simp [dirac, hpL, hpM, hq, hq'] at hN
    have hNR : F 0 0 0 = 1 := by linarith [p0 1]
    have hNR' : F 0 0 1 = 0 := by linarith
    have hk3 : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide
    intro k
    rcases hk3 k with rfl | rfl | rfl <;> funext a <;> fin_cases a <;>
      simp [hA, pureMoves, dirac, bb1Game_assemble, hNR, hNR', hpL, hpM, hq, hq']

/-- **Figure 9.BB.1** (MWG, p. 300). The unique extensive form trembling-hand perfect Nash
equilibrium is `((NR, L), ℓ)`: an EFTHP exists (`exists_isEFTHP`), and every EFTHP is subgame
perfect (`isSPNE_of_isEFTHP`), hence plays `NR`, `L` and `ℓ`. -/
theorem figure_9_BB_1_efthp :
    (∃ F, IsEFTHP bb1Game F ∧ ∀ k,
      bb1Game.assemble F k = bb1Game.assemble (pureMoves ![0, 0, 0]) k) ∧
    ∀ F, IsEFTHP bb1Game F → ∀ k,
      bb1Game.assemble F k = bb1Game.assemble (pureMoves ![0, 0, 0]) k := by
  have hN : NatureFullSupport bb1Game := fun k hk => absurd hk (by fin_cases k <;> simp [bb1Game])
  have huniq : ∀ F, IsEFTHP bb1Game F → ∀ k,
      bb1Game.assemble F k = bb1Game.assemble (pureMoves ![0, 0, 0]) k := fun F hF =>
    figure_9_BB_1_spne.2 F (isSPNE_of_isEFTHP _ bb1Game_perfectRecall hN hF)
  obtain ⟨F, hF⟩ := exists_isEFTHP bb1Game
  exact ⟨⟨F, hF, huniq F hF⟩, huniq⟩

/-- Player 1's payoffs in the normal form of Figure 9.BB.1; player 1's strategies are
`(NR, L)`, `(NR, M)`, `(R, L)`, `(R, M)` (`0, 1, 2, 3`) and player 2's are `ℓ`, `r` (`0, 1`). -/
def bb1U₁ (a : Fin 4) (b : Fin 2) : ℝ :=
  if a = 0 then (if b = 0 then 4 else 1) else if a = 1 then 0 else 2

/-- Player 2's payoffs in the normal form of Figure 9.BB.1. -/
def bb1U₂ (a : Fin 4) (b : Fin 2) : ℝ :=
  if a = 0 then (if b = 0 then 1 else 0) else if a = 1 then (if b = 0 then 0 else 1) else 2

/-- The normal form strategy of player 1 choosing `c₀` at the start and `c₁` after `NR`. -/
def bb1Row (c₀ c₁ : Fin 2) : Fin 4 :=
  if c₀ = 0 then (if c₁ = 0 then 0 else 1) else (if c₁ = 0 then 2 else 3)

/-- **Figure 9.BB.1** (MWG, p. 299). The normal form: the expected payoff of the pure profile
choosing `c k` at each information set is the bimatrix entry of player 1's strategy
`(c 0, c 1)` and player 2's `c 2`. -/
theorem bb1_normalForm (c : Fin 3 → Fin 2) (i : Fin 2) :
    cont bb1Game (bb1Game.assemble (pureMoves c)) [] i =
      (bimatrix bb1U₁ bb1U₂).payoff i (pp (bb1Row (c 0) (c 1)) (c 2)) := by
  have hA := bb1Game_assemble (pureMoves (I := Fin 2) c)
  rw [(bb1Game_cont _ _).2, hA.1, hA.2.1, hA.2.2]
  have h2 : ∀ x : Fin 2, x = 0 ∨ x = 1 := by decide
  simp only [pureMoves, dirac, bimatrix, pp_zero, pp_one, bb1Row, bb1U₁, bb1U₂]
  rcases h2 (c 0) with h0 | h0 <;> rcases h2 (c 1) with h1 | h1 <;>
    rcases h2 (c 2) with h3 | h3 <;> rcases h2 i with rfl | rfl <;>
    simp [h0, h1, h3]

/-- In the normal form of Figure 9.BB.1, a mixed strategy of player 1 giving at least `2`
against both `ℓ` and `r` puts no weight on `(NR, L)` and `(NR, M)`. -/
theorem bb1_row_two {x : Fin 4 → ℝ} (h0 : ∀ a, 0 ≤ x a) (h1 : ∑ a, x a = 1)
    (hr : 2 ≤ ∑ a, x a * bb1U₁ a 1) : x 0 = 0 ∧ x 1 = 0 := by
  simp only [Fin.sum_univ_four, bb1U₁] at h1 hr
  norm_num at hr
  constructor <;> linarith [h0 0, h0 1, h0 2, h0 3]

/-- **Figure 9.BB.1** (MWG, p. 299). The strategy profiles `((R, L), r)` and `((R, M), r)` are
normal form trembling-hand perfect Nash equilibria (of the normal form `bb1_normalForm`), though
not subgame perfect: each is a Nash equilibrium in which no player uses a weakly dominated
strategy (Chapter 8's two-player converse of Proposition 8.F.2). -/
theorem figure_9_BB_1_normalTHP (a : Fin 4) (ha : a = 2 ∨ a = 3) :
    IsTHP (bimatrix bb1U₁ bb1U₂) (pureProfile (pp a (1 : Fin 2))) := by
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have htwo : ∀ k : Fin 2, k = 0 ∨ k = 1 := by decide
  have hU : ∀ b, bb1U₁ a b = 2 ∧ bb1U₂ a b = 2 := by
    intro b; rcases ha with rfl | rfl <;> simp [bb1U₁, bb1U₂]
  have hNE : IsNashEquilibrium (bimatrix bb1U₁ bb1U₂) (pp a (1 : Fin 2)) :=
    (bimatrix_isNash_iff _ _ _ _).2 ⟨fun a' => by
      rw [(hU 1).1]; fin_cases a' <;> norm_num [bb1U₁], fun b' => by
      rw [(hU 1).2, (hU b').2]⟩
  refine isTHP_of_not_weaklyDominated_two _ h01 htwo ((corollary_8_D_1 _ _).1 hNE) fun k => ?_
  rintro ⟨τ', hτ', hdom⟩
  obtain ⟨hle, s, hlt⟩ := (mixedWeaklyDominates_iff_pure _ _ _ _).1 hdom
  have hU1 : ∀ b : S2 4 2 1, bb1U₁ a b = 2 := fun b => (hU b).1
  rcases htwo k with rfl | rfl
  · set x : Fin 4 → ℝ := τ' with hx
    have h0 : ∀ b : Fin 4, 0 ≤ x b := hτ'.1
    have h2 : ∑ b : Fin 4, x b = 1 := hτ'.2
    have hL : ∀ s' : (i : Fin 2) → S2 4 2 i,
        (bimatrix bb1U₁ bb1U₂).mixedPayoff
          (Function.update (pureProfile s') 0 (pureProfile (pp a (1 : Fin 2)) 0)) 0 =
        bb1U₁ a (s' 1) := fun s' => by
      rw [show pureProfile (pp a (1 : Fin 2)) 0 = pureMixed (pp a (1 : Fin 2) 0) from rfl,
        mixedPayoff_pureProfile_update]
      simp [bimatrix, Function.update]
    have e1 : 2 ≤ ∑ b, x b * bb1U₁ b 1 := by
      have := hle (pp 0 1)
      rwa [hL, bimatrix_mixed_vs_pure_zero, hU1] at this
    obtain ⟨hx0, hx1⟩ := bb1_row_two h0 h2 e1
    rw [hL, bimatrix_mixed_vs_pure_zero, hU1] at hlt
    simp only [Fin.sum_univ_four, Fin.sum_univ_four] at hlt h2
    rw [← hx, hx0, hx1] at hlt
    have hb : ∀ b : S2 4 2 1, bb1U₁ 2 b = 2 ∧ bb1U₁ 3 b = 2 := fun b => by simp [bb1U₁]
    rw [(hb _).1, (hb _).2] at hlt
    linarith
  · set y : Fin 2 → ℝ := τ' with hy
    have h0 : ∀ b : Fin 2, 0 ≤ y b := hτ'.1
    have h2 : ∑ b : Fin 2, y b = 1 := hτ'.2
    have hL : ∀ s' : (i : Fin 2) → S2 4 2 i,
        (bimatrix bb1U₁ bb1U₂).mixedPayoff
          (Function.update (pureProfile s') 1 (pureProfile (pp a (1 : Fin 2)) 1)) 1 =
        bb1U₂ (s' 0) 1 := fun s' => by
      rw [show pureProfile (pp a (1 : Fin 2)) 1 = pureMixed (pp a (1 : Fin 2) 1) from rfl,
        mixedPayoff_pureProfile_update]
      simp [bimatrix, Function.update]
    have e1 : bb1U₂ 1 1 ≤ ∑ b, y b * bb1U₂ 1 b := by
      have := hle (pp 1 0)
      rwa [hL, bimatrix_mixed_vs_pure_one] at this
    simp only [Fin.sum_univ_two, bb1U₂] at e1 h2
    norm_num at e1
    have hy1 : y 1 = 1 := by linarith [h0 0]
    have hy0 : y 0 = 0 := by linarith
    rw [hL, bimatrix_mixed_vs_pure_one] at hlt
    simp only [Fin.sum_univ_two] at hlt
    rw [← hy, hy0, hy1] at hlt
    simp at hlt

end MWG.DynamicGames

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Forward induction: equilibrium domination and sequential equilibria

MWG, Section 9.D, footnote 15 and Figure 9.D.2 (pp. 292-294).

* `footnote_15_D_1a`, `footnote_15_D_1b`: the weak PBE of Figures 9.D.1(a) and 9.D.1(b) are
  sequential equilibria (E trembles to the dominated entry strategy with probability `ε` and to
  the other with `ε²`).
* `fig9D2`, `figure_9_D_2`: in the Niche Choice variant of Figure 9.D.2 (the incumbent also
  moves after "out"), E staying out, I playing `R` after "out" and the large niche after entry,
  with I believing E chose the small niche, is a weak PBE and a sequential equilibrium; "small
  niche" is no longer strictly dominated by "out" (against `L` after "out" and the large niche
  after entry it gives `−1 > −10`), but it is **equilibrium dominated**: whatever I does after
  entry it gives at most `−1 < 0`, E's equilibrium payoff.
-/

namespace MWG.DynamicGames

open MWG.NoncooperativeGames MWG.NoncooperativeGames.ExtensiveForm Filter Topology

/-- **Footnote 15** (MWG, p. 292). The weak PBE of Figure 9.D.1(a) (E out, I fights, belief on
In₁) is a sequential equilibrium. -/
theorem footnote_15_D_1a : IsSequentialEq fig9D1a (pureMoves ![0, 0]) leftBelief :=
  ⟨figure_9_D_1a.1.1, figure_9_D_1a.1.2.1, figure_9_D_1a.1.2.2.1,
    entryTwo_consistent_leftBelief_zero _ _⟩

/-- **Footnote 15** (MWG, p. 292). The weak PBE of Figure 9.D.1(b) (E out, I targets the large
niche, belief on the small niche) is a sequential equilibrium. -/
theorem footnote_15_D_1b : IsSequentialEq fig9D1b (pureMoves ![0, 1]) leftBelief :=
  ⟨figure_9_D_1b.1.1, figure_9_D_1b.1.2.1, figure_9_D_1b.1.2.2.1,
    entryTwo_consistent_leftBelief_one _ _⟩

/-- Payoffs `(u_E, u_I)` of Figure 9.D.2. -/
def fig9D2Pay (i : Fin 2) (z : List (Fin 3)) : ℝ :=
  if z = [0, 0] then ![-10, -10] i else if z = [1, 0] then ![0, 2] i
  else if z = [0, 1] then ![-6, -6] i else if z = [1, 1] then ![-1, 1] i
  else if z = [0, 2] then ![1, -1] i else if z = [1, 2] then ![-3, -3] i else 0

/-- **Figure 9.D.2** (MWG, p. 294). E chooses Out (`0`), Small niche (`1`) or Large niche (`2`);
after Out, I chooses `L` (`0`) or `R` (`1`) (information set `1`); after entry I, not observing
the niche, chooses Small (`0`) or Large (`1`) (information set `2 = {[1], [2]}`). -/
def fig9D2 : ExtensiveForm (Fin 2) (Fin 3) (Fin 3) where
  nodes := {[], [0], [1], [2], [0, 0], [1, 0], [0, 1], [1, 1], [0, 2], [1, 2]}
  nil_mem := by decide
  tail_mem := by decide
  info x := if x = [] then 0 else if x = [0] then 1 else 2
  avail k := if k = 0 then Finset.univ else {0, 1}
  avail_spec := by decide
  info_surj := by decide
  player := ![some 0, some 1, some 1]
  natureProb _ _ := 0
  nature_nonneg := fun k hk => absurd hk (by fin_cases k <;> simp)
  nature_zero := fun k hk => absurd hk (by fin_cases k <;> simp)
  nature_sum := fun k hk => absurd hk (by fin_cases k <;> simp)
  payoff := fig9D2Pay

theorem fig9D2_assemble (F : Fin 2 → Fin 3 → Fin 3 → ℝ) :
    fig9D2.assemble F 0 = F 0 0 ∧ fig9D2.assemble F 1 = F 1 1 ∧ fig9D2.assemble F 2 = F 1 2 :=
  ⟨fig9D2.assemble_of_some _ rfl, fig9D2.assemble_of_some _ rfl, fig9D2.assemble_of_some _ rfl⟩

theorem fig9D2_cont (f : Fin 3 → Fin 3 → ℝ) (i : Fin 2) :
    cont fig9D2 f [0] i = f 1 0 * ![-10, -10] i + f 1 1 * ![0, 2] i ∧
    cont fig9D2 f [1] i = f 2 0 * ![-6, -6] i + f 2 1 * ![-1, 1] i ∧
    cont fig9D2 f [2] i = f 2 0 * ![1, -1] i + f 2 1 * ![-3, -3] i ∧
    cont fig9D2 f [] i = f 0 0 * (f 1 0 * ![-10, -10] i + f 1 1 * ![0, 2] i) +
      f 0 1 * (f 2 0 * ![-6, -6] i + f 2 1 * ![-1, 1] i) +
      f 0 2 * (f 2 0 * ![1, -1] i + f 2 1 * ![-3, -3] i) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [cont_unfold, fig9D2, fig9D2Pay, Fin.sum_univ_three]

theorem fig9D2_infoSet : fig9D2.infoSet 0 = {[]} ∧ fig9D2.infoSet 1 = {[0]} ∧
    fig9D2.infoSet 2 = {[1], [2]} := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

theorem fig9D2_reach (f : Fin 3 → Fin 3 → ℝ) :
    fig9D2.reach f [0] = f 0 0 ∧ fig9D2.reach f [1] = f 0 1 ∧ fig9D2.reach f [2] = f 0 2 ∧
    probInfo fig9D2 f 0 = 1 ∧ probInfo fig9D2 f 1 = f 0 0 ∧
    probInfo fig9D2 f 2 = f 0 1 + f 0 2 := by
  obtain ⟨h0, h1, h2⟩ := fig9D2_infoSet
  refine ⟨by simp [fig9D2], by simp [fig9D2], by simp [fig9D2], ?_, ?_, ?_⟩ <;> unfold probInfo
  · rw [h0]; simp
  · rw [h1]; simp [fig9D2]
  · rw [h2, Finset.sum_insert (by decide), Finset.sum_singleton]; simp [fig9D2]

theorem fig9D2_condPayoff (f : Fin 3 → Fin 3 → ℝ) (μ : List (Fin 3) → ℝ) (i : Fin 2) :
    condPayoff fig9D2 f μ 0 i = μ [] * cont fig9D2 f [] i ∧
    condPayoff fig9D2 f μ 1 i = μ [0] * cont fig9D2 f [0] i ∧
    condPayoff fig9D2 f μ 2 i = μ [1] * cont fig9D2 f [1] i + μ [2] * cont fig9D2 f [2] i := by
  obtain ⟨h0, h1, h2⟩ := fig9D2_infoSet
  unfold condPayoff
  rw [h0, h1, h2]
  refine ⟨by simp, by simp, ?_⟩
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]

/-- **Figure 9.D.2** (MWG, pp. 293-294). E staying out, I playing `R` after "out" and the large
niche after entry, with I believing E chose the small niche, is a weak perfect Bayesian
equilibrium and a sequential equilibrium. "Small niche" is not strictly dominated by "out"
(if I plays `L` after "out" and the large niche after entry, "small niche" gives `−1` and
"out" gives `−10`), but it is equilibrium dominated: whatever I does after entry, "small
niche" gives E at most `−1 < 0`, E's equilibrium payoff. -/
theorem figure_9_D_2 :
    IsWeakPBE fig9D2 (pureMoves ![0, 1, 1]) leftBelief ∧
    IsSequentialEq fig9D2 (pureMoves ![0, 1, 1]) leftBelief ∧
    cont fig9D2 (fig9D2.assemble (pureMoves ![0, 0, 1])) [0] 0 <
      cont fig9D2 (fig9D2.assemble (pureMoves ![0, 0, 1])) [1] 0 ∧
    cont fig9D2 (fig9D2.assemble (pureMoves ![0, 1, 1])) [] 0 = 0 ∧
    ∀ f : Fin 3 → Fin 3 → ℝ, (∀ a, 0 ≤ f 2 a) → f 2 0 + f 2 1 = 1 →
      cont fig9D2 f [1] 0 ≤ -1 := by
  obtain ⟨hI0, hI1, hI2⟩ := fig9D2_infoSet
  have hc := fig9D2_cont
  have hcp := fig9D2_condPayoff
  have hr := fig9D2_reach
  have hB : IsBehaviorProfile fig9D2 (pureMoves (I := Fin 2) ![0, 1, 1]) :=
    isBehaviorProfile_pureMoves fun k => by fin_cases k <;> simp [fig9D2]
  have hk3 : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide
  have hW : IsWeakPBE fig9D2 (pureMoves ![0, 1, 1]) leftBelief := by
    have hA := fig9D2_assemble (pureMoves ![0, 1, 1])
    refine ⟨hB, ⟨fun x _ => ?_, fun k => ?_⟩, fun k i hi g hg => ?_, fun k hk x hx => ?_⟩
    · unfold leftBelief; split_ifs <;> norm_num
    · rcases hk3 k with rfl | rfl | rfl
      · simp [hI0, leftBelief]
      · simp [hI1, leftBelief]
      · rw [hI2, Finset.sum_insert (by decide), Finset.sum_singleton]; simp [leftBelief]
    · have hA' := fig9D2_assemble (Function.update (pureMoves ![0, 1, 1]) i g)
      rcases hk3 k with rfl | rfl | rfl
      · obtain rfl : i = 0 := (Option.some.inj (hi : some 0 = some i)).symm
        have h0 := (hg 0 rfl).1
        have h1 := (hg 0 rfl).2.2
        simp only [fig9D2, Fin.sum_univ_three, ↓reduceIte] at h1
        rw [(hcp _ _ _).1, (hcp _ _ _).1, (hc _ _).2.2.2, (hc _ _).2.2.2, hA.1, hA.2.1,
          hA.2.2, hA'.1, hA'.2.1, hA'.2.2]
        simp [pureMoves, dirac, leftBelief]
        nlinarith [h0 0, h0 1, h0 2]
      · obtain rfl : i = 1 := (Option.some.inj (hi : some 1 = some i)).symm
        have h0 := (hg 1 rfl).1
        have h1 := (hg 1 rfl).2.2
        simp [fig9D2] at h1
        rw [(hcp _ _ _).2.1, (hcp _ _ _).2.1, (hc _ _).1, (hc _ _).1, hA.2.1, hA'.2.1]
        simp [pureMoves, dirac, leftBelief]
        nlinarith [h0 0, h0 1]
      · obtain rfl : i = 1 := (Option.some.inj (hi : some 1 = some i)).symm
        have h0 := (hg 2 rfl).1
        have h1 := (hg 2 rfl).2.2
        simp [fig9D2] at h1
        rw [(hcp _ _ _).2.2, (hcp _ _ _).2.2, (hc _ _).2.1, (hc _ _).2.1, (hc _ _).2.2.1,
          (hc _ _).2.2.1, hA.2.2, hA'.2.2]
        simp [pureMoves, dirac, leftBelief]
        nlinarith [h0 0, h0 1]
    · rcases hk3 k with rfl | rfl | rfl
      · rw [hI0, Finset.mem_singleton] at hx
        subst hx
        rw [(hr _).2.2.2.1]
        simp [leftBelief]
      · rw [hI1, Finset.mem_singleton] at hx
        subst hx
        rw [(hr _).2.2.2.2.1, (hr _).1]
        simp [hA.1, pureMoves, dirac, leftBelief]
      · rw [(hr _).2.2.2.2.2, hA.1] at hk
        simp [pureMoves, dirac] at hk
  refine ⟨hW, ⟨hB, hW.2.1, hW.2.2.1, ?_⟩, ?_, ?_, fun f hf0 hf1 => ?_⟩
  · -- trembles: E plays Small with probability `ε` and Large with `ε²`; I deviates with `ε`
    set ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 2) with hε
    have hε0 : ∀ n, 0 < ε n := fun n => by positivity
    have hε1 : ∀ n, ε n ≤ 1 / 2 := fun n => by
      simp only [hε]
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    set Fs : ℕ → Fin 2 → Fin 3 → Fin 3 → ℝ := fun n _ k =>
      if k = 0 then ![1 - ε n - ε n ^ 2, ε n, ε n ^ 2] else ![ε n, 1 - ε n, 0] with hFs
    have hTM : ∀ n, IsTotallyMixedB fig9D2 (Fs n) := by
      intro n
      have e0 := hε0 n
      have e1 := hε1 n
      have hsq : ε n ^ 2 ≤ ε n / 2 := by nlinarith
      refine ⟨fun i k hk => ?_, fun i k hk a ha => ?_⟩
      · rcases hk3 k with rfl | rfl | rfl
        · refine ⟨fun a => ?_, fun a ha => absurd (by simp [fig9D2]) ha, ?_⟩
          · fin_cases a <;> simp [hFs] <;> nlinarith
          · simp [hFs, fig9D2, Fin.sum_univ_three]
            ring
        all_goals
          refine ⟨fun a => ?_, fun a ha => ?_, ?_⟩
          · fin_cases a <;> simp [hFs] <;> linarith
          · have : a = 2 := by
              fin_cases a <;> simp [fig9D2] at ha ⊢
            subst this
            simp [hFs]
          · simp [hFs, fig9D2]
      · rcases hk3 k with rfl | rfl | rfl
        · fin_cases a <;> simp [hFs] <;> nlinarith
        all_goals fin_cases a <;> simp [hFs, fig9D2] at ha ⊢ <;> linarith
    have hlimε : Tendsto ε atTop (𝓝 0) := by
      have h : Tendsto (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)
      refine h.congr fun n => ?_
      simp only [hε, Nat.cast_add, Nat.cast_one]
      ring
    have hlim : Tendsto Fs atTop (𝓝 (pureMoves ![0, 1, 1])) := by
      refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun k => tendsto_pi_nhds.2 fun a => ?_
      have hsq : Tendsto (fun n => ε n ^ 2) atTop (𝓝 0) := by
        simpa using hlimε.pow 2
      rcases hk3 k with rfl | rfl | rfl
      · fin_cases a
        · simpa [hFs, pureMoves, dirac] using
            ((tendsto_const_nhds (x := (1 : ℝ))).sub hlimε).sub hsq
        · simpa [hFs, pureMoves, dirac] using hlimε
        · simpa [hFs, pureMoves, dirac] using hsq
      all_goals
        fin_cases a
        · simpa [hFs, pureMoves, dirac] using hlimε
        · simpa [hFs, pureMoves, dirac] using (tendsto_const_nhds (x := (1 : ℝ))).sub hlimε
        · simp [hFs, pureMoves, dirac]
    refine ⟨Fs, hTM, hlim, fun x hx => ?_⟩
    have hmem := (mem_decisionNodes _).2 hx
    rw [show fig9D2.decisionNodes = {[], [0], [1], [2]} by decide] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    have hasm : ∀ n, fig9D2.assemble (Fs n) 0 = Fs n 0 0 := fun n => (fig9D2_assemble _).1
    have hprob : ∀ n, probInfo fig9D2 (fig9D2.assemble (Fs n)) 2 = ε n + ε n ^ 2 := by
      intro n
      rw [(hr _).2.2.2.2.2, hasm]
      simp [hFs]
    rcases hmem with rfl | rfl | rfl | rfl
    · have : ∀ n, bayesBelief fig9D2 (fig9D2.assemble (Fs n)) [] = 1 := by
        intro n
        unfold bayesBelief
        rw [show fig9D2.info [] = 0 from rfl, (hr _).2.2.2.1]
        simp
      simp only [this, leftBelief]
      exact tendsto_const_nhds
    · have : ∀ n, bayesBelief fig9D2 (fig9D2.assemble (Fs n)) [0] = 1 := by
        intro n
        unfold bayesBelief
        rw [show fig9D2.info [0] = 1 from rfl, (hr _).2.2.2.2.1, (hr _).1, hasm]
        have : Fs n 0 0 0 ≠ 0 := by
          have := hε1 n
          have := hε0 n
          simp only [hFs, ↓reduceIte, Matrix.cons_val_zero]
          nlinarith
        field_simp
      simp only [this, leftBelief]
      exact tendsto_const_nhds
    · have : ∀ n, bayesBelief fig9D2 (fig9D2.assemble (Fs n)) [1] = 1 / (1 + ε n) := by
        intro n
        unfold bayesBelief
        rw [show fig9D2.info [1] = 2 from rfl, hprob, (hr _).2.1, hasm]
        have := hε0 n
        simp only [hFs, ↓reduceIte, Matrix.cons_val_one, Matrix.cons_val_zero]
        field_simp
      simp only [this, leftBelief]
      have := ((tendsto_const_nhds (x := (1 : ℝ))).add hlimε).inv₀ (by norm_num)
      simpa using this
    · have : ∀ n, bayesBelief fig9D2 (fig9D2.assemble (Fs n)) [2] = ε n / (1 + ε n) := by
        intro n
        unfold bayesBelief
        rw [show fig9D2.info [2] = 2 from rfl, hprob, (hr _).2.2.1, hasm]
        have := hε0 n
        simp only [hFs, ↓reduceIte]
        simp
        field_simp
      simp only [this, leftBelief]
      have h : Tendsto (fun n => ε n / (1 + ε n)) atTop (𝓝 (0 / (1 + 0))) :=
        hlimε.div (tendsto_const_nhds.add hlimε) (by norm_num)
      simpa using h
  · have hA := fig9D2_assemble (pureMoves ![0, 0, 1])
    rw [(hc _ _).1, (hc _ _).2.1, hA.2.1, hA.2.2]
    norm_num [pureMoves, dirac]
  · have hA := fig9D2_assemble (pureMoves ![0, 1, 1])
    rw [(hc _ _).2.2.2, hA.1, hA.2.1, hA.2.2]
    norm_num [pureMoves, dirac]
  · rw [(hc _ _).2.1]
    simp
    nlinarith [hf0 0, hf0 1]

end MWG.DynamicGames

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Successive play of simultaneous-move games

MWG, Proposition 9.B.4 (pp. 279-280).

The game `Γ_E` in which the simultaneous-move games `Γᵗ_N = [I, {Δ(Sᵗᵢ)}, {uᵗᵢ}]`,
`t = 0, …, T − 1`, are played in succession, with the pure strategies played in each game
observed before the next, and payoffs summed. A **history** of length `n` is the list of pure
profiles played in periods `0, …, n − 1` (`RHist S n`); a (behaviour) strategy of player `i`
assigns to every history of length `n` a mixed strategy of `Γⁿ_N`. Every history starts a
subgame, and `rval N F i k n h` is player `i`'s expected payoff in the `k` periods following the
history `h` of length `n`. `IsRSPNE` is subgame perfection: at every history of length `n < T`
no player gains by switching to another behaviour strategy.

* `proposition_9_B_4`: if every `Γᵗ_N` has a unique (mixed) Nash equilibrium `σᵗ`, then playing
  `σᵗ` in period `t` regardless of history is an SPNE, and it is the unique SPNE: every SPNE plays
  `σⁿ` after every history of length `n < T`, and gives the payoff `∑_{t ≥ n} uᵗᵢ(σᵗ)`.
* `pd_unique_nash`, `proposition_9_B_4_instance`: the Prisoner's Dilemma (Chapter 8) has the
  unique mixed Nash equilibrium (confess, confess), so in its `T`-fold repetition the unique SPNE
  confesses after every history.

Departure: the model is the direct history-based description of `Γ_E` (subgames are the
histories), not Chapter 7's `ExtensiveForm` tree; no bridge to the tree is built.
-/

namespace MWG.DynamicGames

open MWG.NoncooperativeGames MWG.SimultaneousMoveGames

variable {I : Type*} [Fintype I] [DecidableEq I] {S : ℕ → I → Type*}
  [∀ t i, Fintype (S t i)] [∀ t i, DecidableEq (S t i)]

/-- A history of length `n`: the pure strategy profiles played in periods `0, …, n − 1`. -/
abbrev RHist (S : ℕ → I → Type*) (n : ℕ) := (t : Fin n) → (i : I) → S t i

/-- The history `h` followed by the profile `s` played in period `n`. -/
def rsnoc {n : ℕ} (h : RHist S n) (s : (i : I) → S n i) : RHist S (n + 1) :=
  Fin.snoc (α := fun t : Fin (n + 1) => (i : I) → S t i) h s

/-- **Proposition 9.B.4** (MWG, p. 279). Player `i`'s expected payoff over the `k` periods
following the history `h` of length `n`, when after each history `h'` of length `n'` player `j`
plays the mixed strategy `F j n' h'` of `Γ^{n'}_N`. -/
def rval (N : (t : ℕ) → NormalForm I (S t)) (F : (i : I) → (n : ℕ) → RHist S n → S n i → ℝ)
    (i : I) : ℕ → (n : ℕ) → RHist S n → ℝ
  | 0, _, _ => 0
  | k + 1, n, h => ∑ s : (j : I) → S n j,
      (∏ j, F j n h (s j)) * ((N n).payoff i s + rval N F i k (n + 1) (rsnoc h s))

/-- A behaviour strategy profile of the `T`-period game: a mixed strategy of `Γⁿ_N` after every
history of length `n < T`. -/
def IsRBehavior (T : ℕ) (F : (i : I) → (n : ℕ) → RHist S n → S n i → ℝ) : Prop :=
  ∀ i, ∀ n < T, ∀ h : RHist S n, IsMixedStrategy (F i n h)

/-- **Definition 9.B.2 for successive simultaneous-move games** (MWG, pp. 275 and 279). Every
history of length `n < T` starts a subgame; `F` is subgame perfect if in each of them no player
gains by switching to another behaviour strategy. -/
def IsRSPNE (N : (t : ℕ) → NormalForm I (S t)) (T : ℕ)
    (F : (i : I) → (n : ℕ) → RHist S n → S n i → ℝ) : Prop :=
  IsRBehavior T F ∧ ∀ n < T, ∀ h : RHist S n, ∀ i (g : (n : ℕ) → RHist S n → S n i → ℝ),
    (∀ n' < T, ∀ h', IsMixedStrategy (g n' h')) →
      rval N (Function.update F i g) i (T - n) n h ≤ rval N F i (T - n) n h

omit [∀ t i, DecidableEq (S t i)] in
/-- The payoff in the `k` periods after a history of length `m` depends only on play from
period `m` on. -/
theorem rval_congr (N : (t : ℕ) → NormalForm I (S t))
    {F F' : (i : I) → (n : ℕ) → RHist S n → S n i → ℝ} {m : ℕ}
    (hFF : ∀ j, ∀ n, m ≤ n → F j n = F' j n) (i : I) (k : ℕ) (h : RHist S m) :
    rval N F i k m h = rval N F' i k m h := by
  induction k generalizing m with
  | zero => rfl
  | succ k ih =>
    simp only [rval]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [ih (fun j n hn => hFF j n (by omega)) (rsnoc h s)]
    congr 1
    exact Finset.prod_congr rfl fun j _ => by rw [hFF j m le_rfl]

/-- The mixed profile played after the history `h` of length `n`. -/
def rstage (F : (i : I) → (n : ℕ) → RHist S n → S n i → ℝ) (n : ℕ) (h : RHist S n) :
    (j : I) → S n j → ℝ := fun j => F j n h

omit [Fintype I] [∀ t i, Fintype (S t i)] [∀ t i, DecidableEq (S t i)] in
theorem rstage_update (F : (i : I) → (n : ℕ) → RHist S n → S n i → ℝ) (i : I)
    (g : (n : ℕ) → RHist S n → S n i → ℝ) (n : ℕ) (h : RHist S n) :
    rstage (Function.update F i g) n h = Function.update (rstage F n h) i (g n h) := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp [rstage]
  · simp [rstage, Function.update_of_ne hj]

omit [∀ t i, DecidableEq (S t i)] in
/-- If the continuation payoff after every profile of period `n` is `c`, the payoff from a
history of length `n` is the period-`n` expected payoff plus `c`. -/
theorem rval_succ_of_const (N : (t : ℕ) → NormalForm I (S t))
    (F : (i : I) → (n : ℕ) → RHist S n → S n i → ℝ) (i : I) (k n : ℕ) (h : RHist S n) {c : ℝ}
    (hsum : ∀ j, ∑ a, F j n h a = 1)
    (hc : ∀ s, rval N F i k (n + 1) (rsnoc h s) = c) :
    rval N F i (k + 1) n h = (N n).mixedPayoff (rstage F n h) i + c := by
  simp only [rval, hc, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
    sum_prod_mixed_eq_one hsum, one_mul]
  rfl

omit [∀ t i, DecidableEq (S t i)] in
/-- The step of backward induction: if play after every profile of period `n` gives each
player a fixed continuation payoff, an SPNE plays a Nash equilibrium of `Γⁿ_N` after every
history of length `n`. -/
theorem isMixedNash_rstage_of_isRSPNE {N : (t : ℕ) → NormalForm I (S t)} {T : ℕ}
    {F : (i : I) → (n : ℕ) → RHist S n → S n i → ℝ} (hF : IsRSPNE N T F) {n : ℕ} (hn : n < T)
    (h : RHist S n) {c : I → ℝ}
    (hc : ∀ i s, rval N F i (T - n - 1) (n + 1) (rsnoc h s) = c i) :
    IsMixedNash (N n) (rstage F n h) := by
  refine ⟨fun j => hF.1 j n hn h, fun i τ hτ => ?_⟩
  set g : (n' : ℕ) → RHist S n' → S n' i → ℝ := Function.update (F i) n (fun _ => τ)
  have hg : ∀ n' < T, ∀ h', IsMixedStrategy (g n' h') := by
    intro n' hn' h'
    by_cases hnn : n' = n
    · subst hnn
      simp only [g, Function.update_self]
      exact hτ
    · simp only [g, Function.update_of_ne hnn]
      exact hF.1 i n' hn' h'
  have hdev := hF.2 n hn h i g hg
  have hk : T - n = T - n - 1 + 1 := by omega
  rw [hk] at hdev
  have hlater : ∀ j n', n + 1 ≤ n' → Function.update F i g j n' = F j n' := by
    intro j n' hn'
    by_cases hj : j = i
    · subst hj
      simp only [Function.update_self, g]
      exact Function.update_of_ne (by omega) _ _
    · exact congrFun (Function.update_of_ne hj g F) n'
  have hsum : ∀ (P : (i : I) → (n : ℕ) → RHist S n → S n i → ℝ), IsRBehavior T P →
      ∀ j, ∑ a, P j n h a = 1 := fun P hP j => (hP j n hn h).2
  have hupd : IsRBehavior T (Function.update F i g) := by
    intro j n' hn' h'
    by_cases hj : j = i
    · subst hj
      simp only [Function.update_self]
      exact hg n' hn' h'
    · simp only [Function.update_of_ne hj]
      exact hF.1 j n' hn' h'
  rw [rval_succ_of_const N _ i _ n h (hsum _ hupd) (c := c i) fun s => by
      rw [rval_congr N hlater i _ (rsnoc h s), hc],
    rval_succ_of_const N _ i _ n h (hsum _ hF.1) (c := c i) fun s => hc i s,
    rstage_update] at hdev
  have : g n h = τ := by simp [g]
  rw [this] at hdev
  linarith

omit [∀ t i, DecidableEq (S t i)] in
/-- **Proposition 9.B.4** (MWG, pp. 279-280). Suppose each simultaneous-move game `Γᵗ_N`,
`t < T`, has a unique (mixed) Nash equilibrium `σᵗ`. Then playing `σᵗ` in game `t` regardless of
what has happened previously is a subgame perfect Nash equilibrium of `Γ_E`, and it is the
unique one: every SPNE plays `σⁿ` after every history of length `n < T`, and gives every player
`i` the payoff `∑_{n ≤ t < T} uᵗᵢ(σᵗ)` from every history of length `n`. -/
theorem proposition_9_B_4 (N : (t : ℕ) → NormalForm I (S t)) (T : ℕ)
    (σ : (t : ℕ) → (i : I) → S t i → ℝ)
    (hσ : ∀ t < T, IsMixedNash (N t) (σ t) ∧ ∀ τ, IsMixedNash (N t) τ → τ = σ t) :
    IsRSPNE N T (fun i n _ => σ n i) ∧
    ∀ F, IsRSPNE N T F → (∀ n < T, ∀ h : RHist S n, rstage F n h = σ n) ∧
      ∀ n ≤ T, ∀ (h : RHist S n) i,
        rval N F i (T - n) n h = ∑ t ∈ Finset.Ico n T, (N t).mixedPayoff (σ t) i := by
  have hsplit : ∀ n, n < T → ∀ i, ∑ t ∈ Finset.Ico n T, (N t).mixedPayoff (σ t) i =
      (N n).mixedPayoff (σ n) i + ∑ t ∈ Finset.Ico (n + 1) T, (N t).mixedPayoff (σ t) i :=
    fun n hn i => Finset.sum_eq_sum_Ico_succ_bot hn _
  -- uniqueness
  have huniq : ∀ F, IsRSPNE N T F → (∀ n < T, ∀ h : RHist S n, rstage F n h = σ n) ∧
      ∀ n ≤ T, ∀ (h : RHist S n) i,
        rval N F i (T - n) n h = ∑ t ∈ Finset.Ico n T, (N t).mixedPayoff (σ t) i := by
    intro F hF
    have hval : ∀ k n, n + k = T → ∀ (h : RHist S n) i,
        rval N F i k n h = ∑ t ∈ Finset.Ico n T, (N t).mixedPayoff (σ t) i := by
      intro k
      induction k with
      | zero =>
        intro n hn h i
        obtain rfl : n = T := by omega
        simp [rval]
      | succ k ih =>
        intro n hn h i
        have hnT : n < T := by omega
        have hk : T - n - 1 = k := by omega
        have hc : ∀ i s, rval N F i (T - n - 1) (n + 1) (rsnoc h s) =
            ∑ t ∈ Finset.Ico (n + 1) T, (N t).mixedPayoff (σ t) i := fun i s => by
          rw [hk]; exact ih (n + 1) (by omega) _ i
        have hNE := isMixedNash_rstage_of_isRSPNE hF hnT h hc
        have heq := (hσ n hnT).2 _ hNE
        rw [rval_succ_of_const N F i k n h (fun j => (hF.1 j n hnT h).2) (fun s => by
          rw [← hk]; exact hc i s), heq, hsplit n hnT]
    refine ⟨fun n hn h => ?_, fun n hn h i => hval (T - n) n (by omega) h i⟩
    exact (hσ n hn).2 _ (isMixedNash_rstage_of_isRSPNE hF hn h fun i s =>
      hval (T - n - 1) (n + 1) (by omega) _ i)
  refine ⟨⟨fun i n hn _ => (hσ n hn).1.1 i, fun n hn h i g hg => ?_⟩, huniq⟩
  -- existence: no deviation gains, by induction on the number of remaining periods
  set F : (i : I) → (n : ℕ) → RHist S n → S n i → ℝ := fun i n _ => σ n i
  have key : ∀ k n, n + k ≤ T → ∀ h : RHist S n,
      rval N (Function.update F i g) i k n h ≤
        ∑ t ∈ Finset.Ico n (n + k), (N t).mixedPayoff (σ t) i ∧
      rval N F i k n h = ∑ t ∈ Finset.Ico n (n + k), (N t).mixedPayoff (σ t) i := by
    intro k
    induction k with
    | zero => intro n _ h; simp [rval]
    | succ k ih =>
      intro n hn h
      have hnT : n < T := by omega
      have hs : ∑ t ∈ Finset.Ico n (n + (k + 1)), (N t).mixedPayoff (σ t) i =
          (N n).mixedPayoff (σ n) i + ∑ t ∈ Finset.Ico (n + 1) (n + 1 + k),
            (N t).mixedPayoff (σ t) i := by
        rw [show n + 1 + k = n + (k + 1) by ring]
        exact Finset.sum_eq_sum_Ico_succ_bot (by omega) _
      rw [hs]
      have hsumU : ∀ j, ∑ a, Function.update F i g j n h a = 1 := by
        intro j
        by_cases hj : j = i
        · subst hj; simp only [Function.update_self]; exact (hg n hnT h).2
        · simp only [Function.update_of_ne hj, F]; exact ((hσ n hnT).1.1 j).2
      constructor
      · -- the deviation earns at most the equilibrium payoff in period `n` and after
        have hle : rval N (Function.update F i g) i (k + 1) n h ≤
            (N n).mixedPayoff (rstage (Function.update F i g) n h) i +
              ∑ t ∈ Finset.Ico (n + 1) (n + 1 + k), (N t).mixedPayoff (σ t) i := by
          simp only [rval]
          have hP : ∀ s : (j : I) → S n j, 0 ≤ ∏ j, Function.update F i g j n h (s j) := by
            intro s
            refine Finset.prod_nonneg fun j _ => ?_
            by_cases hj : j = i
            · subst hj; simp only [Function.update_self]; exact (hg n hnT h).1 _
            · simp only [Function.update_of_ne hj, F]; exact ((hσ n hnT).1.1 j).1 _
          calc ∑ s : (j : I) → S n j, (∏ j, Function.update F i g j n h (s j)) *
                ((N n).payoff i s + rval N (Function.update F i g) i k (n + 1) (rsnoc h s))
              ≤ ∑ s : (j : I) → S n j, (∏ j, Function.update F i g j n h (s j)) *
                ((N n).payoff i s + ∑ t ∈ Finset.Ico (n + 1) (n + 1 + k),
                  (N t).mixedPayoff (σ t) i) :=
                Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left
                  (add_le_add le_rfl (ih (n + 1) (by omega) _).1) (hP s)
            _ = _ := by
                simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
                  sum_prod_mixed_eq_one hsumU, one_mul]
                rfl
        refine hle.trans (add_le_add ?_ le_rfl)
        rw [rstage_update]
        have : rstage F n h = σ n := rfl
        rw [this]
        exact (hσ n hnT).1.2 i _ (hg n hnT h)
      · rw [rval_succ_of_const N F i k n h (fun j => ((hσ n hnT).1.1 j).2)
          (fun s => (ih (n + 1) (by omega) _).2)]
        rfl
  have h1 := (key (T - n) n (by omega) h).1
  have h2 := (key (T - n) n (by omega) h).2
  rw [h2]
  exact h1

/-- **Figure 8.B.1** (MWG, p. 237), used in Proposition 9.B.4. The Prisoner's Dilemma has a
unique Nash equilibrium, pure or mixed: both prisoners confess (`1`), a strictly dominant
strategy. -/
theorem pd_unique_nash :
    IsMixedNash (bimatrix pdU₁ pdU₂) (pureProfile (pp (1 : Fin 2) (1 : Fin 2))) ∧
    ∀ τ, IsMixedNash (bimatrix pdU₁ pdU₂) τ → τ = pureProfile (pp (1 : Fin 2) (1 : Fin 2)) := by
  refine ⟨(corollary_8_D_1 _ _).1 ((bimatrix_isNash_iff _ _ _ _).2
    ⟨fun a' => by fin_cases a' <;> norm_num [pdU₁], fun b' => by fin_cases b' <;> norm_num [pdU₂]⟩),
    fun τ hτ => ?_⟩
  set x : Fin 2 → ℝ := τ 0 with hxdef
  set y : Fin 2 → ℝ := τ 1 with hydef
  have hx : IsMixedStrategy x := hτ.1 0
  have hy : IsMixedStrategy y := hτ.1 1
  have hτ' : IsMixedNash (bimatrix pdU₁ pdU₂) (mp x y) := (eq_mp τ) ▸ hτ
  obtain ⟨h1, h2⟩ := (bimatrix_isMixedNash_support _ _ hx hy).1 hτ'
  have hx2 : x 0 + x 1 = 1 := by simpa [Fin.sum_univ_two] using hx.2
  have hy2 : y 0 + y 1 = 1 := by simpa [Fin.sum_univ_two] using hy.2
  have hx0 : x 0 = 0 := by
    by_contra hne
    have := h1 0 (lt_of_le_of_ne (hx.1 0) (Ne.symm hne)) 1
    simp only [Fin.sum_univ_two, pdU₁] at this
    norm_num at this
    linarith [hy.1 0, hy.1 1]
  have hy0 : y 0 = 0 := by
    by_contra hne
    have := h2 0 (lt_of_le_of_ne (hy.1 0) (Ne.symm hne)) 1
    simp only [Fin.sum_univ_two, pdU₂] at this
    norm_num at this
    linarith [hx.1 0, hx.1 1]
  have hx1 : x 1 = 1 := by linarith
  have hy1 : y 1 = 1 := by linarith
  have ex : x = pureMixed (1 : Fin 2) := by
    funext a; fin_cases a <;> simp [pureMixed, hx0, hx1]
  have ey : y = pureMixed (1 : Fin 2) := by
    funext a; fin_cases a <;> simp [pureMixed, hy0, hy1]
  rw [eq_mp τ, eq_mp (pureProfile (pp (1 : Fin 2) (1 : Fin 2)))]
  change mp x y = mp (pureMixed (1 : Fin 2)) (pureMixed (1 : Fin 2))
  rw [ex, ey]

/-- **Proposition 9.B.4, an instance** (MWG, p. 279). In the `T`-fold repetition of the
Prisoner's Dilemma, confessing after every history is the unique subgame perfect Nash
equilibrium. -/
theorem proposition_9_B_4_instance (T : ℕ) :
    IsRSPNE (S := fun _ => S2 2 2) (fun _ => bimatrix pdU₁ pdU₂) T
      (fun i _ _ => pureProfile (pp (1 : Fin 2) (1 : Fin 2)) i) ∧
    ∀ F, IsRSPNE (S := fun _ => S2 2 2) (fun _ => bimatrix pdU₁ pdU₂) T F →
      ∀ n < T, ∀ h, rstage F n h = pureProfile (pp (1 : Fin 2) (1 : Fin 2)) := by
  obtain ⟨hE, hU⟩ := proposition_9_B_4 (S := fun _ => S2 2 2) (fun _ => bimatrix pdU₁ pdU₂) T
    (fun _ => pureProfile (pp (1 : Fin 2) (1 : Fin 2))) fun _ _ => pd_unique_nash
  exact ⟨hE, fun F hF => (hU F hF).1⟩

end MWG.DynamicGames

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Maskin's first-mover game

MWG, Exercise 9.B.5(c)-(e) (p. 302). Two players choose actions `m₁ ∈ M₁` and `m₂ ∈ M₂` with
payoffs `φ₁(m₁, m₂)` and `φ₂(m₁, m₂)`. In game (a) they move simultaneously; in game (b)
player 1 moves first and player 2 observes `m₁`, so a strategy of player 2 is a function
`s₂ : M₁ → M₂` (Exercise 9.B.5(b), `exercise_9_B_5b`).

Game (b) is a finite game of perfect information whose subgames are the whole game and the
`|M₁|` subgames after player 1's moves, so its (pure) SPNE are the profiles found by backward
induction: `s₂ m₁'` is a best reply of player 2 after every `m₁'`, and `m₁` is a best reply of
player 1 against `s₂` (`IsMaskinSPNE`). A (pure) Nash equilibrium of (b) only requires player
2's reply on the path to be optimal (`IsMaskinNash`).

* `exercise_9_B_5c`: if (b) has two distinct SPNE, there are two distinct pairs of moves between
  which player 1 or player 2 is indifferent; `exercise_9_B_5c_instance`.
* `exercise_9_B_5d`: if player 2 is never indifferent between distinct pairs of moves and
  `(a, b)` is a pure Nash equilibrium of (a), every SPNE of (b) gives player 1 at least
  `φ₁(a, b)`; `exercise_9_B_5d_instance`. `exercise_9_B_5d_nash`: this fails for Nash
  equilibria of (b).
* `exercise_9_B_5e_ties`, `exercise_9_B_5e_mixed`: the conclusion of (d) fails if player 2 has
  ties, or if the pure Nash equilibrium is replaced by a mixed one.

Departure (an encoding): the SPNE of (b) are pure profiles given by their backward-induction
characterisation rather than by Chapter 7's `ExtensiveForm` (corrections, item 9).
-/

namespace MWG.DynamicGames

open MWG.NoncooperativeGames MWG.SimultaneousMoveGames

variable {M₁ M₂ : Type*}

/-- **Exercise 9.B.5(b)** (MWG, p. 302). A pure subgame perfect Nash equilibrium `(m₁, s₂)` of
the game in which player 1 moves first: after every move `m₁'` player 2's reply `s₂ m₁'` is a
best reply, and `m₁` is a best reply of player 1 against `s₂` (backward induction; the subgames
are the game itself and the subgames after each `m₁'`). -/
def IsMaskinSPNE (φ₁ φ₂ : M₁ → M₂ → ℝ) (m₁ : M₁) (s₂ : M₁ → M₂) : Prop :=
  (∀ m₁' m₂', φ₂ m₁' m₂' ≤ φ₂ m₁' (s₂ m₁')) ∧ ∀ m₁', φ₁ m₁' (s₂ m₁') ≤ φ₁ m₁ (s₂ m₁)

/-- **Exercise 9.B.5(b)** (MWG, p. 302). A pure Nash equilibrium `(m₁, s₂)` of the game in which
player 1 moves first: no strategy `s₂' : M₁ → M₂` of player 2 and no move `m₁'` of player 1 is a
profitable deviation. -/
def IsMaskinNash (φ₁ φ₂ : M₁ → M₂ → ℝ) (m₁ : M₁) (s₂ : M₁ → M₂) : Prop :=
  (∀ s₂' : M₁ → M₂, φ₂ m₁ (s₂' m₁) ≤ φ₂ m₁ (s₂ m₁)) ∧ ∀ m₁', φ₁ m₁' (s₂ m₁') ≤ φ₁ m₁ (s₂ m₁)

/-- **Exercise 9.B.5(a)** (MWG, p. 302). A pure Nash equilibrium `(a, b)` of the simultaneous
game. -/
def IsMaskinSimNash (φ₁ φ₂ : M₁ → M₂ → ℝ) (a : M₁) (b : M₂) : Prop :=
  (∀ a', φ₁ a' b ≤ φ₁ a b) ∧ ∀ b', φ₂ a b' ≤ φ₂ a b

/-- Every SPNE of (b) is a Nash equilibrium of (b). -/
theorem IsMaskinSPNE.isMaskinNash {φ₁ φ₂ : M₁ → M₂ → ℝ} {m₁ : M₁} {s₂ : M₁ → M₂}
    (h : IsMaskinSPNE φ₁ φ₂ m₁ s₂) : IsMaskinNash φ₁ φ₂ m₁ s₂ :=
  ⟨fun s₂' => h.1 m₁ (s₂' m₁), h.2⟩

/-- **Exercise 9.B.5(c)** (MWG, p. 302). If the game in (b) has two distinct SPNE, then there
are two pairs of moves `(m₁, m₂) ≠ (m₁', m₂')` with `φ₁(m₁, m₂) = φ₁(m₁', m₂')` or
`φ₂(m₁, m₂) = φ₂(m₁', m₂')`. -/
theorem exercise_9_B_5c {φ₁ φ₂ : M₁ → M₂ → ℝ} {m₁ m₁' : M₁} {s₂ s₂' : M₁ → M₂}
    (h : IsMaskinSPNE φ₁ φ₂ m₁ s₂) (h' : IsMaskinSPNE φ₁ φ₂ m₁' s₂')
    (hne : (m₁, s₂) ≠ (m₁', s₂')) :
    ∃ p q : M₁ × M₂, p ≠ q ∧ (φ₁ p.1 p.2 = φ₁ q.1 q.2 ∨ φ₂ p.1 p.2 = φ₂ q.1 q.2) := by
  by_cases hs : s₂ = s₂'
  · subst hs
    have hm : m₁ ≠ m₁' := fun hm => hne (by rw [hm])
    refine ⟨(m₁, s₂ m₁), (m₁', s₂ m₁'), fun he => hm (Prod.ext_iff.1 he).1, Or.inl ?_⟩
    exact le_antisymm (h'.2 m₁) (h.2 m₁')
  · obtain ⟨k, hk⟩ := Function.ne_iff.1 hs
    refine ⟨(k, s₂ k), (k, s₂' k), fun he => hk (Prod.ext_iff.1 he).2, Or.inr ?_⟩
    exact le_antisymm (h'.1 k (s₂ k)) (h.1 k (s₂' k))

/-- **Exercise 9.B.5(d)** (MWG, p. 302). Suppose player 2 is never indifferent between two
distinct pairs of moves, and `(a, b)` is a pure strategy Nash equilibrium of the simultaneous
game (a). Then in every SPNE of (b) player 1's payoff is at least `π₁ = φ₁(a, b)`. -/
theorem exercise_9_B_5d {φ₁ φ₂ : M₁ → M₂ → ℝ}
    (hno : ∀ m₁ m₂ m₁' m₂', (m₁ ≠ m₁' ∨ m₂ ≠ m₂') → φ₂ m₁ m₂ ≠ φ₂ m₁' m₂')
    {a : M₁} {b : M₂} (hab : IsMaskinSimNash φ₁ φ₂ a b) {m₁ : M₁} {s₂ : M₁ → M₂}
    (h : IsMaskinSPNE φ₁ φ₂ m₁ s₂) : φ₁ a b ≤ φ₁ m₁ (s₂ m₁) := by
  have hsa : s₂ a = b := by
    by_contra hne
    exact hno a (s₂ a) a b (Or.inr hne) (le_antisymm (hab.2 (s₂ a)) (h.1 a b))
  rw [← hsa]
  exact h.2 a

/-- The game of the counterexample to the Nash version of Exercise 9.B.5(d): player 1's
payoffs `[[2, 0], [1, -1]]`. -/
def maskinD₁ : Fin 2 → Fin 2 → ℝ := ![![2, 0], ![1, -1]]

/-- Player 2's payoffs `[[3, 2], [1, 0]]` (no ties). -/
def maskinD₂ : Fin 2 → Fin 2 → ℝ := ![![3, 2], ![1, 0]]

theorem maskinD₂_noTies :
    ∀ m₁ m₂ m₁' m₂' : Fin 2, (m₁ ≠ m₁' ∨ m₂ ≠ m₂') → maskinD₂ m₁ m₂ ≠ maskinD₂ m₁' m₂' := by
  intro m₁ m₂ m₁' m₂' hne
  fin_cases m₁ <;> fin_cases m₂ <;> fin_cases m₁' <;> fin_cases m₂' <;>
    simp_all [maskinD₂]

/-- **Exercise 9.B.5(d), an instance** (MWG, p. 302). In the game `maskinD₁`, `maskinD₂` player 2
has no ties, `(0, 0)` is a pure Nash equilibrium of (a) with `π₁ = 2`, and the unique SPNE of
(b), `(0, s₂)` with `s₂ = (0 ↦ 0, 1 ↦ 0)`, gives player 1 the payoff `2`. -/
theorem exercise_9_B_5d_instance :
    IsMaskinSimNash maskinD₁ maskinD₂ 0 0 ∧ IsMaskinSPNE maskinD₁ maskinD₂ 0 ![0, 0] ∧
      maskinD₁ 0 (![0, 0] 0) = 2 := by
  refine ⟨⟨fun a' => ?_, fun b' => ?_⟩, ⟨fun m₁' m₂' => ?_, fun m₁' => ?_⟩, by simp [maskinD₁]⟩
  · fin_cases a' <;> norm_num [maskinD₁]
  · fin_cases b' <;> norm_num [maskinD₂]
  · fin_cases m₁' <;> fin_cases m₂' <;> norm_num [maskinD₂]
  · fin_cases m₁' <;> norm_num [maskinD₁]

/-- **Exercise 9.B.5(d), second question** (MWG, p. 302). The bound need not hold for a Nash
equilibrium of (b): in the game `maskinD₁`, `maskinD₂` (player 2 has no ties, `(0, 0)` is a pure
Nash equilibrium of (a) giving player 1 `π₁ = 2`), the profile in which player 1 plays `1` and
player 2 threatens `s₂ = (0 ↦ 1, 1 ↦ 0)` is a Nash equilibrium of (b) giving player 1 only `1`.
-/
theorem exercise_9_B_5d_nash :
    (∀ m₁ m₂ m₁' m₂' : Fin 2, (m₁ ≠ m₁' ∨ m₂ ≠ m₂') → maskinD₂ m₁ m₂ ≠ maskinD₂ m₁' m₂') ∧
    IsMaskinSimNash maskinD₁ maskinD₂ 0 0 ∧ maskinD₁ 0 0 = 2 ∧
    IsMaskinNash maskinD₁ maskinD₂ 1 ![1, 0] ∧ maskinD₁ 1 (![1, 0] 1) = 1 := by
  refine ⟨maskinD₂_noTies, exercise_9_B_5d_instance.1, by simp [maskinD₁],
    ⟨fun s₂' => ?_, fun m₁' => ?_⟩, by simp [maskinD₁]⟩
  · rcases (by decide : ∀ k : Fin 2, k = 0 ∨ k = 1) (s₂' 1) with h | h <;>
      simp [h, maskinD₂]
  · fin_cases m₁' <;> norm_num [maskinD₁]

/-- The game of Exercise 9.B.5(e) with ties for player 2: `M₁ = {0}`, `M₂ = {0, 1}`. -/
def maskinTie₁ : Fin 1 → Fin 2 → ℝ := fun _ m₂ => if m₂ = 0 then 1 else 0

/-- **Exercise 9.B.5(e), ties** (MWG, p. 302). If condition (ii) holds for some distinct pairs
the conclusion of (d) fails: with `M₁ = {0}`, player 2 indifferent everywhere and
`φ₁(0, 0) = 1`, `φ₁(0, 1) = 0`, `(0, 0)` is a pure Nash equilibrium of (a) giving `π₁ = 1`, but
`(0, 0 ↦ 1)` is an SPNE of (b) giving player 1 the payoff `0`. -/
theorem exercise_9_B_5e_ties :
    IsMaskinSimNash maskinTie₁ (fun _ _ => 0) 0 0 ∧ maskinTie₁ 0 0 = 1 ∧
      IsMaskinSPNE maskinTie₁ (fun _ _ => 0) 0 (fun _ => 1) ∧ maskinTie₁ 0 1 = 0 := by
  refine ⟨⟨fun a' => ?_, fun _ => le_rfl⟩, by simp [maskinTie₁],
    ⟨fun _ _ => le_rfl, fun m₁' => ?_⟩, by simp [maskinTie₁]⟩
  · fin_cases a'
    exact le_rfl
  · fin_cases m₁'
    exact le_rfl

/-- Player 1's payoffs in the game of Exercise 9.B.5(e) with a mixed equilibrium:
`[[1, -1], [-1, 1]]`. -/
def maskinMix₁ : Fin 2 → Fin 2 → ℝ := ![![1, -1], ![-1, 1]]

/-- Player 2's payoffs `[[-1, 1], [2, -2]]` (no ties). -/
def maskinMix₂ : Fin 2 → Fin 2 → ℝ := ![![-1, 1], ![2, -2]]

theorem maskinMix_spne_iff (m₁ : Fin 2) (s₂ : Fin 2 → Fin 2) :
    IsMaskinSPNE maskinMix₁ maskinMix₂ m₁ s₂ ↔ s₂ 0 = 1 ∧ s₂ 1 = 0 := by
  constructor
  · intro h
    have h0 := h.1 0 1
    have h1 := h.1 1 0
    refine ⟨?_, ?_⟩
    · rcases (by decide : ∀ k : Fin 2, k = 0 ∨ k = 1) (s₂ 0) with he | he
      · rw [he] at h0
        norm_num [maskinMix₂] at h0
      · exact he
    · rcases (by decide : ∀ k : Fin 2, k = 0 ∨ k = 1) (s₂ 1) with he | he
      · exact he
      · rw [he] at h1
        norm_num [maskinMix₂] at h1
  · rintro ⟨h0, h1⟩
    refine ⟨fun m₁' m₂' => ?_, fun m₁' => ?_⟩
    · fin_cases m₁' <;> fin_cases m₂' <;> simp [h0, h1, maskinMix₂]
    · fin_cases m₁' <;> fin_cases m₁ <;> simp [h0, h1, maskinMix₁]

/-- **Exercise 9.B.5(c), an instance** (MWG, p. 302). The game `maskinMix₁`, `maskinMix₂` has
two distinct SPNE, `(0, s₂)` and `(1, s₂)` with `s₂ = (0 ↦ 1, 1 ↦ 0)`; player 1 is indifferent
between the distinct pairs `(0, 1)` and `(1, 0)`. -/
theorem exercise_9_B_5c_instance :
    IsMaskinSPNE maskinMix₁ maskinMix₂ 0 ![1, 0] ∧ IsMaskinSPNE maskinMix₁ maskinMix₂ 1 ![1, 0] ∧
      maskinMix₁ 0 1 = maskinMix₁ 1 0 :=
  ⟨(maskinMix_spne_iff 0 _).2 ⟨rfl, rfl⟩, (maskinMix_spne_iff 1 _).2 ⟨rfl, rfl⟩,
    by simp [maskinMix₁]⟩

/-- **Exercise 9.B.5(e), mixed equilibria** (MWG, p. 302). The conclusion of (d) fails if the
pure strategy Nash equilibrium of (a) is replaced by a mixed one: in the game `maskinMix₁`,
`maskinMix₂` player 2 has no ties, player 1 playing `0` with probability `2/3` and player 2
playing `0` with probability `1/2` is a mixed Nash equilibrium of (a) giving player 1 the payoff
`0`, but every SPNE of (b) gives player 1 the payoff `−1`. -/
theorem exercise_9_B_5e_mixed :
    (∀ m₁ m₂ m₁' m₂' : Fin 2, (m₁ ≠ m₁' ∨ m₂ ≠ m₂') → maskinMix₂ m₁ m₂ ≠ maskinMix₂ m₁' m₂') ∧
    IsMixedNash (bimatrix maskinMix₁ maskinMix₂) (mp ![2 / 3, 1 / 3] ![1 / 2, 1 / 2]) ∧
    (bimatrix maskinMix₁ maskinMix₂).mixedPayoff (mp ![2 / 3, 1 / 3] ![1 / 2, 1 / 2]) 0 = 0 ∧
    ∀ m₁ s₂, IsMaskinSPNE maskinMix₁ maskinMix₂ m₁ s₂ → maskinMix₁ m₁ (s₂ m₁) = -1 := by
  have hx : IsMixedStrategy (![2 / 3, 1 / 3] : Fin 2 → ℝ) := by
    refine ⟨fun a => ?_, ?_⟩
    · fin_cases a <;> norm_num
    · simp [Fin.sum_univ_two]
      norm_num
  have hy : IsMixedStrategy (![1 / 2, 1 / 2] : Fin 2 → ℝ) := by
    refine ⟨fun a => ?_, ?_⟩
    · fin_cases a <;> norm_num
    · simp [Fin.sum_univ_two]
      norm_num
  refine ⟨?_, ?_, ?_, fun m₁ s₂ h => ?_⟩
  · intro m₁ m₂ m₁' m₂' hne
    fin_cases m₁ <;> fin_cases m₂ <;> fin_cases m₁' <;> fin_cases m₂' <;>
      simp_all [maskinMix₂] <;> norm_num
  · refine (bimatrix_isMixedNash_iff _ _ hx hy).2 ⟨fun a' => ?_, fun b' => ?_⟩
    · fin_cases a' <;> simp [Fin.sum_univ_two, maskinMix₁]
    · fin_cases b' <;> simp [Fin.sum_univ_two, maskinMix₂] <;> norm_num
  · rw [(bimatrix_mixedPayoff _ _ _).1]
    simp [Fin.sum_univ_two, maskinMix₁]
  · obtain ⟨h0, h1⟩ := (maskinMix_spne_iff m₁ s₂).1 h
    fin_cases m₁ <;> simp [h0, h1, maskinMix₁]

end MWG.DynamicGames

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# A simultaneous-move game played twice

MWG, Exercise 9.B.9 (p. 302) and footnote 10 (p. 280), in the history model of
Proposition 9.B.4 (`MWGDynamicGames/Repeated.lean`).

* `augGame`, `isRSPNE_two_iff`: generalized backward induction for two periods. A behaviour
  profile `F` of the twice-played game is subgame perfect iff after every first-period profile
  it plays a (mixed) Nash equilibrium of `Γ¹_N`, and in the first period it plays a Nash
  equilibrium of `Γ⁰_N` augmented by the second-period equilibrium payoffs.
* `rpure`, `isRSPNE_two_pure_iff`: the same for pure strategy profiles.
* Exercise 9.B.9: the stage game has the pure Nash equilibria `(a₂, b₂)` and `(a₃, b₃)` only
  (`tw_nash_iff`). `exercise_9_B_9`: a pure profile is a pure SPNE iff after every first-period
  outcome it plays `(a₂, b₂)` or `(a₃, b₃)`, and no player gains by deviating in the first period
  given the second-period play this triggers. `exercise_9_B_9_first`: a first-period profile is
  played in some pure SPNE iff it is not `(a₂, b₃)` or `(a₃, b₂)` (a first-period deviation can
  be punished by at most `5 − 1 = 4`). `footnote_10`: ((a₁, b₁), then (a₂, b₂) after (a₁, b₁)
  and (a₃, b₃) otherwise) is a pure SPNE — history dependence with multiple stage equilibria.

Actions are numbered from `0`: `aₖ` and `bₖ` are `k − 1`.
-/

namespace MWG.DynamicGames

open MWG.NoncooperativeGames MWG.SimultaneousMoveGames

variable {I : Type*} [Fintype I] [DecidableEq I] {S : ℕ → I → Type*}
  [∀ t i, Fintype (S t i)] [∀ t i, DecidableEq (S t i)]

omit [∀ t i, DecidableEq (S t i)] in
/-- The payoff in the one period after a history is the stage game's mixed payoff. -/
theorem rval_one (N : (t : ℕ) → NormalForm I (S t))
    (F : (i : I) → (n : ℕ) → RHist S n → S n i → ℝ) (i : I) (n : ℕ) (h : RHist S n) :
    rval N F i 1 n h = (N n).mixedPayoff (rstage F n h) i := by
  simp only [rval, add_zero]
  rfl

/-- **Generalized backward induction, two periods** (MWG, pp. 277-280). The first-period game
`Γ⁰_N` with payoffs augmented by the second-period payoffs that `F` prescribes after each
first-period profile. -/
def augGame (N : (t : ℕ) → NormalForm I (S t)) (F : (i : I) → (n : ℕ) → RHist S n → S n i → ℝ)
    (h0 : RHist S 0) : NormalForm I (S 0) where
  payoff i s := (N 0).payoff i s + (N 1).mixedPayoff (rstage F 1 (rsnoc h0 s)) i

omit [∀ t i, DecidableEq (S t i)] in
/-- The payoff of the twice-played game is the augmented first-period game's mixed payoff. -/
theorem rval_two (N : (t : ℕ) → NormalForm I (S t))
    (F : (i : I) → (n : ℕ) → RHist S n → S n i → ℝ) (i : I) (h0 : RHist S 0) :
    rval N F i 2 0 h0 = (augGame N F h0).mixedPayoff (rstage F 0 h0) i := by
  simp only [rval, add_zero]
  rfl

omit [∀ t i, DecidableEq (S t i)] in
/-- **Generalized backward induction, two periods** (MWG, pp. 277-280). A behaviour profile `F`
of the game in which `Γ⁰_N` and then `Γ¹_N` are played (with the first-period profile observed)
is a subgame perfect Nash equilibrium iff after every first-period profile it plays a Nash
equilibrium of `Γ¹_N`, and in the first period it plays a Nash equilibrium of the augmented
game `augGame N F`. -/
theorem isRSPNE_two_iff (N : (t : ℕ) → NormalForm I (S t))
    (F : (i : I) → (n : ℕ) → RHist S n → S n i → ℝ) :
    IsRSPNE N 2 F ↔ IsRBehavior 2 F ∧ (∀ h : RHist S 1, IsMixedNash (N 1) (rstage F 1 h)) ∧
      ∀ h0 : RHist S 0, IsMixedNash (augGame N F h0) (rstage F 0 h0) := by
  constructor
  · intro hF
    refine ⟨hF.1, fun h => isMixedNash_rstage_of_isRSPNE hF (by norm_num) h (c := fun _ => 0)
      (fun _ _ => rfl), fun h0 => ⟨fun j => hF.1 j 0 (by norm_num) h0, fun i τ hτ => ?_⟩⟩
    set g : (n : ℕ) → RHist S n → S n i → ℝ := Function.update (F i) 0 (fun _ => τ) with hgd
    have hg : ∀ n' < 2, ∀ h', IsMixedStrategy (g n' h') := by
      intro n' hn' h'
      by_cases hnn : n' = 0
      · subst hnn
        simp only [g, Function.update_self]
        exact hτ
      · simp only [g, Function.update_of_ne hnn]
        exact hF.1 i n' hn' h'
    have hdev := hF.2 0 (by norm_num) h0 i g hg
    have h1 : ∀ h' : RHist S 1, rstage (Function.update F i g) 1 h' = rstage F 1 h' := by
      intro h'
      have hg1 : g 1 h' = rstage F 1 h' i := by
        simp only [g, Function.update_of_ne (by norm_num : (1 : ℕ) ≠ 0)]
        rfl
      rw [rstage_update, hg1, Function.update_eq_self]
    have haug : augGame N (Function.update F i g) h0 = augGame N F h0 := by
      simp only [augGame, h1]
    have hg0 : g 0 h0 = τ := by simp [g]
    rw [Nat.sub_zero, rval_two, rval_two, haug, rstage_update, hg0] at hdev
    exact hdev
  · rintro ⟨hB, h1, h0⟩
    refine ⟨hB, fun n hn h i g hg => ?_⟩
    have hupd : IsRBehavior 2 (Function.update F i g) := by
      intro j n' hn' h'
      by_cases hj : j = i
      · subst hj
        simp only [Function.update_self]
        exact hg n' hn' h'
      · simp only [Function.update_of_ne hj]
        exact hB j n' hn' h'
    rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl
    · rw [Nat.sub_zero, rval_two, rval_two]
      calc (augGame N (Function.update F i g) h).mixedPayoff
            (rstage (Function.update F i g) 0 h) i
          ≤ (augGame N F h).mixedPayoff (rstage (Function.update F i g) 0 h) i := by
            unfold NormalForm.mixedPayoff
            refine Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left ?_
              (Finset.prod_nonneg fun j _ => (hupd j 0 (by norm_num) h).1 _)
            simp only [augGame]
            rw [rstage_update]
            exact add_le_add le_rfl ((h1 _).2 i _ (hg 1 (by norm_num) _))
        _ ≤ _ := by
            rw [rstage_update]
            exact (h0 h).2 i _ (hg 0 (by norm_num) h)
    · rw [show 2 - 1 = 1 from rfl, rval_one, rval_one, rstage_update]
      exact (h1 h).2 i _ (hg 1 (by norm_num) h)

/-- A pure strategy profile of the successive game: after the history `h` of length `n` the
players play the pure profile `p n h`. -/
def rpure (p : (n : ℕ) → RHist S n → (i : I) → S n i) :
    (i : I) → (n : ℕ) → RHist S n → S n i → ℝ :=
  fun i n h => pureMixed (p n h i)

/-- **Generalized backward induction, two periods, pure strategies** (MWG, pp. 277-280). A pure
profile `p` is a subgame perfect Nash equilibrium of the twice-played game iff after every
first-period profile it plays a pure Nash equilibrium of `Γ¹_N`, and no player gains by a
unilateral first-period deviation, given the second-period play that the deviation
triggers. -/
theorem isRSPNE_two_pure_iff (N : (t : ℕ) → NormalForm I (S t))
    (p : (n : ℕ) → RHist S n → (i : I) → S n i) :
    IsRSPNE N 2 (rpure p) ↔ (∀ h : RHist S 1, IsNashEquilibrium (N 1) (p 1 h)) ∧
      ∀ (h0 : RHist S 0) (i : I) (t : S 0 i),
        (N 0).payoff i (Function.update (p 0 h0) i t) +
            (N 1).payoff i (p 1 (rsnoc h0 (Function.update (p 0 h0) i t))) ≤
          (N 0).payoff i (p 0 h0) + (N 1).payoff i (p 1 (rsnoc h0 (p 0 h0))) := by
  have hst : ∀ n (h : RHist S n), rstage (rpure p) n h = pureProfile (p n h) := fun _ _ => rfl
  have hB : IsRBehavior 2 (rpure p) := fun i n _ h => isMixedStrategy_pureMixed (p n h i)
  rw [isRSPNE_two_iff]
  simp only [hst, ← corollary_8_D_1, hB, true_and]
  refine and_congr Iff.rfl (forall_congr' fun h0 => ?_)
  simp only [IsNashEquilibrium, augGame, hst, mixedPayoff_pureProfile]

/-- Player 1's payoffs in the game of Exercise 9.B.9 (rows `a₁, a₂, a₃`, columns
`b₁, b₂, b₃`). -/
def twU₁ : Fin 3 → Fin 3 → ℝ := ![![10, 2, 0], ![12, 5, 0], ![13, 0, 1]]

/-- Player 2's payoffs in the game of Exercise 9.B.9. -/
def twU₂ : Fin 3 → Fin 3 → ℝ := ![![10, 12, 13], ![2, 5, 0], ![0, 0, 1]]

/-- The stage game of Exercise 9.B.9 in every period. -/
abbrev twS : ℕ → Fin 2 → Type := fun _ => S2 3 3

/-- **Exercise 9.B.9** (MWG, p. 302). The stage game has exactly two pure Nash equilibria,
`(a₂, b₂)` and `(a₃, b₃)`. -/
theorem tw_nash_iff (a b : Fin 3) :
    IsNashEquilibrium (bimatrix twU₁ twU₂) (pp a b) ↔ (a = 1 ∧ b = 1) ∨ (a = 2 ∧ b = 2) := by
  rw [bimatrix_isNash_iff]
  fin_cases a <;> fin_cases b <;> simp [Fin.forall_fin_succ, twU₁, twU₂] <;> norm_num

theorem pp_inj {m n : ℕ} (a a' : Fin m) (b b' : Fin n) : pp a b = pp a' b' ↔ a = a' ∧ b = b' :=
  ⟨fun h => ⟨congrFun h 0, congrFun h 1⟩, by rintro ⟨rfl, rfl⟩; rfl⟩

theorem tw_nash_iff' (s : (i : Fin 2) → S2 3 3 i) :
    IsNashEquilibrium (bimatrix twU₁ twU₂) s ↔ s = pp 1 1 ∨ s = pp 2 2 := by
  obtain ⟨a, b, rfl⟩ : ∃ a b : Fin 3, s = pp a b := ⟨s 0, s 1, eq_pp s⟩
  rw [tw_nash_iff, pp_inj, pp_inj]

/-- **Exercise 9.B.9** (MWG, p. 302). The pure strategy subgame perfect Nash equilibria of the
twice-played game: a pure profile `p` is an SPNE iff after every first-period outcome the
players play `(a₂, b₂)` or `(a₃, b₃)`, and no player gains by deviating in the first period,
given the second-period play that the deviation triggers. -/
theorem exercise_9_B_9 (p : (n : ℕ) → RHist twS n → (i : Fin 2) → S2 3 3 i) :
    IsRSPNE (S := twS) (fun _ => bimatrix twU₁ twU₂) 2 (rpure p) ↔
      (∀ h : RHist twS 1, p 1 h = pp 1 1 ∨ p 1 h = pp 2 2) ∧
      ∀ (h0 : RHist twS 0) (i : Fin 2) (t : S2 3 3 i),
        (bimatrix twU₁ twU₂).payoff i (Function.update (p 0 h0) i t) +
            (bimatrix twU₁ twU₂).payoff i (p 1 (rsnoc h0 (Function.update (p 0 h0) i t))) ≤
          (bimatrix twU₁ twU₂).payoff i (p 0 h0) +
            (bimatrix twU₁ twU₂).payoff i (p 1 (rsnoc h0 (p 0 h0))) := by
  rw [isRSPNE_two_pure_iff]
  simp only [tw_nash_iff']

/-- The pure profile of the existence part of Exercise 9.B.9: play `(a, b)` in the first period;
then `(a₂, b₂)` if `(a, b)` was played and `(a₃, b₃)` otherwise. -/
def twProfile (a b : Fin 3) : (n : ℕ) → RHist twS n → (i : Fin 2) → S2 3 3 i :=
  fun n h => if hn : 0 < n then (if h ⟨0, hn⟩ = pp a b then pp 1 1 else pp 2 2) else pp a b

theorem rsnoc_zero (h0 : RHist twS 0) (s : (i : Fin 2) → S2 3 3 i) :
    rsnoc h0 s ⟨0, Nat.one_pos⟩ = s := by
  simp [rsnoc, Fin.snoc]

theorem tw_payoff_cont (s : (i : Fin 2) → S2 3 3 i) (hs : s = pp 1 1 ∨ s = pp 2 2) (i : Fin 2) :
    1 ≤ (bimatrix twU₁ twU₂).payoff i s ∧ (bimatrix twU₁ twU₂).payoff i s ≤ 5 := by
  rcases hs with rfl | rfl <;> fin_cases i <;> norm_num [twU₁, twU₂]

/-- **Exercise 9.B.9, existence** (MWG, p. 302). If `(a, b)` is neither `(a₂, b₃)` nor
`(a₃, b₂)`, playing `(a, b)` and then `(a₂, b₂)` after `(a, b)` and `(a₃, b₃)` otherwise is a pure
strategy SPNE. -/
theorem twProfile_isRSPNE (a b : Fin 3) (hn1 : ¬ (a = 1 ∧ b = 2)) (hn2 : ¬ (a = 2 ∧ b = 1)) :
    IsRSPNE (S := twS) (fun _ => bimatrix twU₁ twU₂) 2 (rpure (twProfile a b)) := by
  refine (exercise_9_B_9 _).2 ⟨fun h => ?_, fun h0 i t => ?_⟩
  · simp only [twProfile, Nat.one_pos, ↓reduceDIte]
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  · have hp0 : twProfile a b 0 h0 = pp a b := by simp [twProfile]
    have hq : ∀ s, twProfile a b 1 (rsnoc h0 s) = if s = pp a b then pp 1 1 else pp 2 2 := by
      intro s
      simp only [twProfile, Nat.one_pos, ↓reduceDIte, rsnoc_zero]
    rw [hp0, hq, hq]
    simp only [↓reduceIte]
    have hgain0 : ∀ t : Fin 3, twU₁ t b ≤ twU₁ a b + 4 := by
      intro t
      fin_cases a <;> fin_cases b <;> fin_cases t <;> simp_all [twU₁] <;> norm_num
    have hgain1 : ∀ t : Fin 3, twU₂ a t ≤ twU₂ a b + 4 := by
      intro t
      fin_cases a <;> fin_cases b <;> fin_cases t <;> simp_all [twU₂] <;> norm_num
    rcases (by decide : ∀ k : Fin 2, k = 0 ∨ k = 1) i with rfl | rfl
    · simp only [Function.update_eq_self_iff, pp_zero, pp_one, bimatrix_payoff_zero]
      split_ifs with ht
      · rw [ht]
        exact le_rfl
      · have := hgain0 t
        norm_num [twU₁] at this ⊢
        linarith
    · simp only [Function.update_eq_self_iff, pp_zero, pp_one, bimatrix_payoff_one]
      split_ifs with ht
      · rw [ht]
        exact le_rfl
      · have := hgain1 t
        norm_num [twU₂] at this ⊢
        linarith

/-- **Exercise 9.B.9** (MWG, p. 302). A first-period profile `(a, b)` is played in some pure
strategy SPNE iff it is neither `(a₂, b₃)` nor `(a₃, b₂)`: every other first-period profile
leaves each player a deviation gain of at most `4 = 5 − 1`, which the switch from `(a₂, b₂)` to
`(a₃, b₃)` in the second period deters; at `(a₂, b₃)` player 2 gains `5`, at `(a₃, b₂)`
player 1 gains `5`. -/
theorem exercise_9_B_9_first (a b : Fin 3) :
    (∃ p : (n : ℕ) → RHist twS n → (i : Fin 2) → S2 3 3 i,
        IsRSPNE (S := twS) (fun _ => bimatrix twU₁ twU₂) 2 (rpure p) ∧
        ∀ h0 : RHist twS 0, p 0 h0 = pp a b) ↔
      ¬ (a = 1 ∧ b = 2) ∧ ¬ (a = 2 ∧ b = 1) := by
  constructor
  · rintro ⟨p, hp, hab⟩
    obtain ⟨h1, h0⟩ := (exercise_9_B_9 p).1 hp
    set e : RHist twS 0 := fun t => absurd t.2 (Nat.not_lt_zero _)
    have hdev0 : ∀ t : Fin 3, twU₁ t b ≤ twU₁ a b + 4 := by
      intro t
      have := h0 e 0 t
      have c1 := tw_payoff_cont _ (h1 (rsnoc e (Function.update (p 0 e) 0 t))) 0
      have c2 := tw_payoff_cont _ (h1 (rsnoc e (p 0 e))) 0
      rw [hab e] at this
      simp only [bimatrix_update_zero, bimatrix_payoff_zero, pp_zero, pp_one] at this
      simp only [bimatrix_payoff_zero] at c1 c2
      rw [hab e] at c1 c2
      simp only [↓reduceIte] at this
      linarith
    have hdev1 : ∀ t : Fin 3, twU₂ a t ≤ twU₂ a b + 4 := by
      intro t
      have := h0 e 1 t
      have c1 := tw_payoff_cont _ (h1 (rsnoc e (Function.update (p 0 e) 1 t))) 1
      have c2 := tw_payoff_cont _ (h1 (rsnoc e (p 0 e))) 1
      rw [hab e] at this
      simp only [bimatrix_update_one, bimatrix_payoff_one, pp_zero, pp_one] at this
      simp only [bimatrix_payoff_one] at c1 c2
      rw [hab e] at c1 c2
      simp only [Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, ↓reduceIte] at this
      linarith
    refine ⟨?_, ?_⟩
    · rintro ⟨rfl, rfl⟩
      have := hdev1 1
      norm_num [twU₂] at this
    · rintro ⟨rfl, rfl⟩
      have := hdev0 1
      norm_num [twU₁] at this
  · rintro ⟨hn1, hn2⟩
    exact ⟨twProfile a b, twProfile_isRSPNE a b hn1 hn2, fun h0 => by simp [twProfile]⟩

/-- **Footnote 10** (MWG, p. 280). With multiple stage equilibria the SPNE play can depend on
history: in the game of Exercise 9.B.9, playing `(a₁, b₁)` in the first period, then `(a₂, b₂)`
if `(a₁, b₁)` was played and `(a₃, b₃)` otherwise, is a pure strategy SPNE (although
`(a₁, b₁)` is not a Nash equilibrium of the stage game). -/
theorem footnote_10 :
    IsRSPNE (S := twS) (fun _ => bimatrix twU₁ twU₂) 2 (rpure (twProfile 0 0)) ∧
      ¬ IsNashEquilibrium (bimatrix twU₁ twU₂) (pp 0 0) := by
  refine ⟨twProfile_isRSPNE 0 0 (by decide) (by decide), fun h => ?_⟩
  rcases (tw_nash_iff 0 0).1 h with ⟨h0, -⟩ | ⟨h0, -⟩ <;> exact absurd h0 (by decide)

end MWG.DynamicGames

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Iterated weak dominance and backward induction

MWG, Exercise 9.D.1 (p. 305): in a finite game of perfect information with no moves of nature
in which no player has the same payoffs at two terminal nodes (the condition of
Proposition 9.B.2 for a unique SPNE), there is an order of iterated removal of weakly dominated
strategies after which every surviving strategy profile has the SPNE outcome.

* `IsWDominatedIn`, `WDDeletionStep`: iterated deletion of weakly dominated strategies
  (Definition 8.B.3 within the remaining strategy sets; several strategies of several players
  may be removed at once), for any normal form game.
* `OnPath G f x w`: the moves `f` lead from node `x` to node `w`. `cont_onPath`, `cont_agree`:
  for pure moves, continuation payoffs are determined by the moves along the realised path.
* `biSets G s n`: the strategies of each player that follow the backward-induction profile `s`
  at every own decision node of length at least `n` that they do not exclude by their own
  earlier moves. `biSets_step`: going from `biSets (n + 1)` to `biSets n` removes only weakly
  dominated strategies: a strategy deviating at a node `y` of length `n` that it does not
  exclude is weakly dominated by the strategy that follows `s` in the subgame at `y` (strictly
  worse against rivals that lead to `y`; `towards`).
* `exercise_9_D_1`: the deletion order "deepest nodes first" ends in `biSets 0`, where every
  surviving profile follows the SPNE path and gives the SPNE payoffs; `exercise_9_D_1_instance`
  (the entry game of Example 9.B.1).

MWG notes that any order of deletion gives the result (Moulin, 1981); that stronger claim is
not formalized.
-/

namespace MWG.DynamicGames

open MWG.NoncooperativeGames MWG.NoncooperativeGames.ExtensiveForm MWG.SimultaneousMoveGames

/-- **Definition 8.B.3 within remaining sets** (MWG, pp. 238-240). Within the remaining strategy
sets `T`, the strategy `s` of player `i` is weakly dominated by a remaining strategy `s'`: at
least as good against every remaining profile of the rivals and strictly better against
one. -/
def IsWDominatedIn {J : Type*} {S : J → Type*} [DecidableEq J] (N : NormalForm J S)
    (T : (i : J) → Set (S i)) (i : J) (s : S i) : Prop :=
  ∃ s' ∈ T i, (∀ r : (j : J) → S j, (∀ j, j ≠ i → r j ∈ T j) →
      N.payoff i (Function.update r i s) ≤ N.payoff i (Function.update r i s')) ∧
    ∃ r : (j : J) → S j, (∀ j, j ≠ i → r j ∈ T j) ∧
      N.payoff i (Function.update r i s) < N.payoff i (Function.update r i s')

/-- **Section 8.B** (MWG, p. 240). One step of iterated deletion of weakly dominated strategies:
`T'` keeps a subset of each `T_i`, and every removed strategy is weakly dominated in the game
restricted to `T`. -/
def WDDeletionStep {J : Type*} {S : J → Type*} [DecidableEq J] (N : NormalForm J S)
    (T T' : (i : J) → Set (S i)) : Prop :=
  (∀ i, T' i ⊆ T i) ∧ ∀ i, ∀ s ∈ T i, s ∉ T' i → IsWDominatedIn N T i s

variable {I A H : Type*} (G : ExtensiveForm I A H) [DecidableEq A] [Fintype A] [DecidableEq I]

/-- The moves `f` lead from node `x` to node `w`: every move on the path from `x` to `w` has
probability one. -/
def OnPath (f : H → A → ℝ) (x w : List A) : Prop :=
  ∀ b v, x <:+ v → b :: v <:+ w → f (G.info v) b = 1

/-- Pure moves: probabilities `0` or `1`, zero off the available actions, summing to one. -/
def IsPureMoves (f : H → A → ℝ) : Prop :=
  (∀ k a, f k a = 0 ∨ f k a = 1) ∧ (∀ k a, a ∉ G.avail k → f k a = 0) ∧
    ∀ k, ∑ a ∈ G.avail k, f k a = 1

omit [DecidableEq A] [Fintype A] [DecidableEq I] in
theorem onPath_self (f : H → A → ℝ) (x : List A) : OnPath G f x x := by
  intro b v hxv hbv
  have h1 := hxv.length_le
  have h2 := hbv.length_le
  simp only [List.length_cons] at h2
  omega

omit [DecidableEq A] [Fintype A] [DecidableEq I] in
theorem OnPath.mono {f : H → A → ℝ} {x w w' : List A} (h : OnPath G f x w') (hw : w <:+ w') :
    OnPath G f x w :=
  fun b v hxv hbv => h b v hxv (hbv.trans hw)

omit [DecidableEq A] [Fintype A] [DecidableEq I] in
theorem OnPath.cons {f : H → A → ℝ} {x w : List A} (h : OnPath G f x w) (hxw : x <:+ w)
    {a : A} (ha : f (G.info w) a = 1) : OnPath G f x (a :: w) := by
  intro b v hxv hbv
  rcases List.suffix_cons_iff.1 hbv with he | he
  · obtain ⟨rfl, rfl⟩ := List.cons.inj he
    exact ha
  · exact h b v hxv he

omit [DecidableEq A] [Fintype A] [DecidableEq I] in
theorem OnPath.trans {f : H → A → ℝ} {x w : List A} (h1 : OnPath G f [] x) (hxw : x <:+ w)
    (h2 : OnPath G f x w) : OnPath G f [] w := by
  intro b v _ hbv
  rcases List.suffix_or_suffix_of_suffix hxw hbv with h | h
  · rcases List.suffix_cons_iff.1 h with he | he
    · exact h1 b v List.nil_suffix (he ▸ List.suffix_refl x)
    · exact h2 b v he hbv
  · exact h1 b v List.nil_suffix h

omit [DecidableEq I] in
/-- With pure moves, the continuation payoff at a decision node is that of the successor
chosen there. -/
theorem cont_step {f : H → A → ℝ} (hf : IsPureMoves G f) {y : List A} (hy : G.IsDecision y)
    {a : A} (ha : f (G.info y) a = 1) (i : I) : cont G f y i = cont G f (a :: y) i := by
  have haav : a ∈ G.avail (G.info y) := by
    by_contra h
    rw [hf.2.1 _ a h] at ha
    norm_num at ha
  have hzero : ∀ b ∈ G.avail (G.info y), b ≠ a → f (G.info y) b = 0 := by
    intro b hb hba
    have hs := hf.2.2 (G.info y)
    rw [← Finset.add_sum_erase _ _ haav, ha] at hs
    have hnn : ∀ c ∈ (G.avail (G.info y)).erase a, 0 ≤ f (G.info y) c := fun c _ => by
      rcases hf.1 (G.info y) c with h | h <;> simp [h]
    exact (Finset.sum_eq_zero_iff_of_nonneg hnn).1 (by linarith) b
      (Finset.mem_erase.2 ⟨hba, hb⟩)
  rw [cont_decision G f hy, Finset.sum_eq_single_of_mem a haav fun b hb hba => by
    rw [hzero b hb hba, zero_mul], ha, one_mul]

omit [DecidableEq I] in
/-- With pure moves, the continuation payoff from `x` equals that from any node `y` on the
path from `x`. -/
theorem cont_onPath {f : H → A → ℝ} (hf : IsPureMoves G f) {x y : List A} (hxy : x <:+ y)
    (hy : y ∈ G.nodes) (hp : OnPath G f x y) (i : I) : cont G f x i = cont G f y i := by
  induction y with
  | nil =>
    rw [List.eq_nil_of_suffix_nil hxy]
  | cons a y ih =>
    rcases List.suffix_cons_iff.1 hxy with he | he
    · rw [he]
    · rw [ih he (G.mem_of_cons_mem hy) (hp.mono G (List.suffix_cons a y)),
        cont_step G hf (G.isDecision_of_cons_mem hy) (hp a y he (List.suffix_refl _))]

omit [DecidableEq I] in
/-- With pure moves `f`, the continuation payoff from `y` does not change if the moves change
only off the path that `f` takes from `y`. -/
theorem cont_agree {f g : H → A → ℝ} (hf : IsPureMoves G f) {y : List A} (hy : y ∈ G.nodes)
    (h : ∀ w, G.IsDecision w → y <:+ w → OnPath G f y w → f (G.info w) = g (G.info w))
    (i : I) : cont G f y i = cont G g y i := by
  suffices key : ∀ n, ∀ y ∈ G.nodes, G.nodes.sup List.length - y.length ≤ n →
      (∀ w, G.IsDecision w → y <:+ w → OnPath G f y w → f (G.info w) = g (G.info w)) →
      cont G f y i = cont G g y i from key _ y hy le_rfl h
  intro n
  induction n with
  | zero =>
    intro y hy hn _
    have hterm : G.IsTerminal y := by
      refine ⟨hy, fun b hb => ?_⟩
      have := G.length_le_sup hb
      simp only [List.length_cons] at this
      omega
    rw [cont_terminal _ _ hterm, cont_terminal _ _ hterm]
  | succ n ih =>
    intro y hy hn h
    rcases (G.isDecision_or_isTerminal hy).1 with hdec | hterm
    · have hfy := h y hdec (List.suffix_refl y) (onPath_self G f y)
      rw [cont_decision _ _ hdec, cont_decision _ g hdec, ← hfy]
      refine Finset.sum_congr rfl fun a ha => ?_
      rcases hf.1 (G.info y) a with h0 | h1
      · rw [h0, zero_mul, zero_mul]
      · rw [h1]
        have hmem := G.cons_mem_of_mem_avail hdec ha
        have hl := G.length_le_sup hmem
        simp only [List.length_cons] at hl
        refine congrArg _ (ih (a :: y) hmem (by simp only [List.length_cons]; omega)
          fun w hw haw hp => h w hw ((List.suffix_cons a y).trans haw) ?_)
        intro b v hyv hbv
        by_cases hvy : v = y
        · subst hvy
          have := suffix_unique hbv haw (by simp)
          rw [(List.cons.inj this).1]
          exact h1
        · obtain ⟨c, hc⟩ := exists_cons_suffix hyv (Ne.symm hvy)
          have hca : c :: y = a :: y := suffix_unique (hc.trans ((List.suffix_cons b v).trans
            hbv)) haw (by simp)
          rw [hca] at hc
          exact hp b v hc hbv
    · rw [cont_terminal _ _ hterm, cont_terminal _ _ hterm]

omit [Fintype A] in
/-- Without moves of nature the moves of a pure profile are pure. -/
theorem isPureMoves_pureProfile (hN : ∀ k, G.player k ≠ none)
    (s : (i : I) → G.PureStrategy i) : IsPureMoves G (G.pureProfile s) := by
  refine ⟨fun k a => ?_, fun k a ha => ?_, fun k => G.sum_pureProfile s k⟩
  · obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.1 (hN k)
    rw [G.pureProfile_apply s hj]
    split_ifs <;> simp
  · obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.1 (hN k)
    rw [G.pureProfile_apply s hj]
    have : (s j ⟨k, hj⟩).1 ≠ a := fun he => ha (he ▸ (s j ⟨k, hj⟩).2)
    simp [this]

/-- Player `j`'s strategy `σ` does not exclude node `y` by its own moves: at each of `j`'s
decision nodes on the path to `y`, `σ` takes the action leading towards `y`. -/
def Permits (j : I) (σ : G.PureStrategy j) (y : List A) : Prop :=
  ∀ b v (hv : G.player (G.info v) = some j), b :: v <:+ y → (σ ⟨G.info v, hv⟩).1 = b

/-- The strategies of player `j` that follow the backward-induction profile `s` at every own
decision node of length at least `n` that they do not exclude by their own moves. -/
def biSets (s : (i : I) → G.PureStrategy i) (n : ℕ) (j : I) : Set (G.PureStrategy j) :=
  {σ | ∀ y (hy : G.player (G.info y) = some j), G.IsDecision y → n ≤ y.length →
    Permits G j σ y → σ ⟨G.info y, hy⟩ = s j ⟨G.info y, hy⟩}

omit [Fintype A] in
theorem pureProfile_eq_one_iff (s : (i : I) → G.PureStrategy i) {k : H} {j : I}
    (hk : G.player k = some j) (a : A) : G.pureProfile s k a = 1 ↔ (s j ⟨k, hk⟩).1 = a := by
  rw [G.pureProfile_apply s hk]
  split_ifs with h <;> simp [h]

omit [Fintype A] in
theorem permits_of_onPath (s : (i : I) → G.PureStrategy i) {w : List A}
    (h : OnPath G (G.pureProfile s) [] w) (j : I) : Permits G j (s j) w :=
  fun b v hv hbv => (pureProfile_eq_one_iff G s hv b).1 (h b v List.nil_suffix hbv)

omit [Fintype A] in
/-- If every component of `t` lies in `biSets s m`, at decision nodes of length at least `m` on
the path of `t`, `t` makes the moves of `s`. -/
theorem biSets_agree (hN : ∀ k, G.player k ≠ none) (s t : (i : I) → G.PureStrategy i)
    {m : ℕ} (ht : ∀ k, t k ∈ biSets G s m k) {w : List A} (hw : G.IsDecision w)
    (hl : m ≤ w.length) (hp : OnPath G (G.pureProfile t) [] w) :
    G.pureProfile t (G.info w) = G.pureProfile s (G.info w) := by
  obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.1 (hN (G.info w))
  have he := ht j w hj hw hl (permits_of_onPath G t hp j)
  funext a
  rw [G.pureProfile_apply t hj, G.pureProfile_apply s hj, he]

/-- From a node of length at least `m` on the path of `t` (all of whose components lie in
`biSets s m`), the continuation payoffs of `t` are those of `s`. -/
theorem cont_biSets (hN : ∀ k, G.player k ≠ none) (s t : (i : I) → G.PureStrategy i)
    {m : ℕ} (ht : ∀ k, t k ∈ biSets G s m k) {x : List A} (hx : x ∈ G.nodes)
    (hl : m ≤ x.length) (hp : OnPath G (G.pureProfile t) [] x) (i : I) :
    cont G (G.pureProfile t) x i = cont G (G.pureProfile s) x i :=
  cont_agree G (isPureMoves_pureProfile G hN t) hx (fun _ hw hxw hpw =>
    biSets_agree G hN s t ht hw (hl.trans hxw.length_le) (hp.trans G hxw hpw)) i

omit [Fintype A] in
/-- Every surviving profile at stage `0` follows the path of `s`. -/
theorem onPath_biSets_iff (hN : ∀ k, G.player k ≠ none) (s t : (i : I) → G.PureStrategy i)
    (ht : ∀ k, t k ∈ biSets G s 0 k) {w : List A} (hw : w ∈ G.nodes) :
    OnPath G (G.pureProfile t) [] w ↔ OnPath G (G.pureProfile s) [] w := by
  induction w with
  | nil => exact ⟨fun _ => onPath_self G _ [], fun _ => onPath_self G _ []⟩
  | cons a w ih =>
    have hw' := G.mem_of_cons_mem hw
    have hdec := G.isDecision_of_cons_mem hw
    constructor
    · intro h
      have h1 := (ih hw').1 (h.mono G (List.suffix_cons a w))
      refine h1.cons G List.nil_suffix ?_
      rw [← biSets_agree G hN s t ht hdec (Nat.zero_le _) (h.mono G (List.suffix_cons a w))]
      exact h a w List.nil_suffix (List.suffix_refl _)
    · intro h
      have h1 := (ih hw').2 (h.mono G (List.suffix_cons a w))
      refine h1.cons G List.nil_suffix ?_
      rw [biSets_agree G hN s t ht hdec (Nat.zero_le _) h1]
      exact h a w List.nil_suffix (List.suffix_refl _)

omit [DecidableEq A] [Fintype A] [DecidableEq I] in
/-- Under perfect information the information sets of the subgame at `y` are those of the
decision nodes following `y`. -/
theorem inSub_iff_of_pi (hPI : G.PerfectInformation) {y v : List A} (hv : G.IsDecision v) :
    InSub G y (G.info v) ↔ y <:+ v := by
  constructor
  · rintro ⟨w, hw, hyw, he⟩
    rw [← hPI w hw.1 v hv.1 hw.2 hv.2 he]
    exact hyw
  · exact fun h => inSub_of_suffix G hv h

open Classical in
/-- The strategy of player `k` that takes the actions leading to node `y` at the nodes on the
path to `y`, and follows `s` elsewhere. -/
noncomputable def towards (s : (i : I) → G.PureStrategy i) {y : List A} (hy : y ∈ G.nodes)
    (k : I) : G.PureStrategy k := fun h =>
  if hex : ∃ b v, b :: v <:+ y ∧ G.info v = h.1 then
    ⟨hex.choose, by
      obtain ⟨v, hv, he⟩ := hex.choose_spec
      have hm := G.mem_avail_of_cons_mem (G.mem_of_suffix hv hy)
      rwa [he] at hm⟩
  else s k h

omit [DecidableEq A] [DecidableEq I] in
theorem towards_on_path (hPI : G.PerfectInformation) (s : (i : I) → G.PureStrategy i)
    {y : List A} (hy : y ∈ G.nodes) {b : A} {v : List A} (hbv : b :: v <:+ y) {k : I}
    (hk : G.player (G.info v) = some k) : (towards G s hy k ⟨G.info v, hk⟩).1 = b := by
  have hex : ∃ b' v', b' :: v' <:+ y ∧ G.info v' = G.info v := ⟨b, v, hbv, rfl⟩
  simp only [towards, hex, ↓reduceDIte]
  obtain ⟨v', hv', he⟩ := hex.choose_spec
  have hvd : G.IsDecision v := G.isDecision_of_cons_mem (G.mem_of_suffix hbv hy)
  have hvd' : G.IsDecision v' := G.isDecision_of_cons_mem (G.mem_of_suffix hv' hy)
  have hvv : v' = v := hPI v' hvd'.1 v hvd.1 hvd'.2 hvd.2 he
  subst hvv
  exact (List.cons.inj (suffix_unique hv' hbv (by simp))).1

omit [DecidableEq A] [DecidableEq I] in
theorem towards_mem (hPI : G.PerfectInformation) (s : (i : I) → G.PureStrategy i)
    {y : List A} (hy : y ∈ G.nodes) {n : ℕ} (hyl : y.length = n) (k : I) :
    towards G s hy k ∈ biSets G s (n + 1) k := by
  intro y' hy' hdec hl _
  have hex : ¬ ∃ b v, b :: v <:+ y ∧ G.info v = G.info y' := by
    rintro ⟨b, v, hbv, he⟩
    have hvd : G.IsDecision v := G.isDecision_of_cons_mem (G.mem_of_suffix hbv hy)
    have := hPI v hvd.1 y' hdec.1 hvd.2 hdec.2 he
    subst this
    have := hbv.length_le
    simp only [List.length_cons] at this
    omega
  simp only [towards, hex, ↓reduceDIte]

/-- **Backward induction is strict without ties** (MWG, p. 276). With no moves of nature and no
ties, the mover at a decision node strictly prefers the backward-induction move to any other
move, given the continuation play. -/
theorem bi_strict (hN : ∀ k, G.player k ≠ none)
    (hinj : ∀ i, ∀ z ∈ G.terminals, ∀ z' ∈ G.terminals, G.payoff i z = G.payoff i z' → z = z')
    {s : (i : I) → G.PureStrategy i} (hs : IsBackwardInduction G s) {x : List A}
    (hx : G.IsDecision x) {j : I} (hj : G.player (G.info x) = some j) {a : A}
    (ha : a ∈ G.avail (G.info x)) (hne : a ≠ (s j ⟨G.info x, hj⟩).1) :
    cont G (G.pureProfile s) (a :: x) j <
      cont G (G.pureProfile s) ((s j ⟨G.info x, hj⟩).1 :: x) j := by
  set a' := (s j ⟨G.info x, hj⟩).1
  have hB := isBehaviorProfile_pureB G s
  obtain ⟨z, hz, haz, hcz⟩ :=
    (oneShotOptimal_unique G hN hinj hB hB hs hs (G.cons_mem_of_mem_avail hx ha)).1
  obtain ⟨z', hz', haz', hcz'⟩ := (oneShotOptimal_unique G hN hinj hB hB hs hs
    (G.cons_mem_of_mem_avail hx (s j ⟨G.info x, hj⟩).2)).1
  have hstep : cont G (G.pureProfile s) x j = cont G (G.pureProfile s) (a' :: x) j :=
    cont_step G (isPureMoves_pureProfile G hN s) hx
      ((pureProfile_eq_one_iff G s hj a').2 rfl) j
  have hle : cont G (G.pureProfile s) (a :: x) j ≤ cont G (G.pureProfile s) (a' :: x) j := by
    rw [← hstep]
    exact hs x hx j hj a ha
  refine lt_of_le_of_ne hle fun he => hne ?_
  rw [← assemble_pureB] at he
  rw [(hcz j).1, (hcz' j).1] at he
  have hzz := hinj j z hz z' hz' he
  subst hzz
  exact (List.cons.inj (suffix_unique haz haz' (by simp))).1

omit [DecidableEq A] [Fintype A] [DecidableEq I] in
theorem biSets_mono (s : (i : I) → G.PureStrategy i) (n : ℕ) (j : I) :
    biSets G s n j ⊆ biSets G s (n + 1) j :=
  fun _ hσ y hy hd hl hp => hσ y hy hd (by omega) hp

/-- **Exercise 9.D.1, one deletion step** (MWG, p. 305). Going from `biSets s (n + 1)` to
`biSets s n` removes only strategies that are weakly dominated in the game restricted to
`biSets s (n + 1)`: a strategy of player `j` deviating from `s` at a node `y` of length `n` that
it does not exclude is weakly dominated by the strategy that follows `s` in the subgame at
`y`. -/
theorem biSets_step (hPI : G.PerfectInformation) (hN : ∀ k, G.player k ≠ none)
    (hinj : ∀ i, ∀ z ∈ G.terminals, ∀ z' ∈ G.terminals, G.payoff i z = G.payoff i z' → z = z')
    {s : (i : I) → G.PureStrategy i} (hs : IsBackwardInduction G s) (n : ℕ) :
    WDDeletionStep G.toNormalForm (biSets G s (n + 1)) (biSets G s n) := by
  classical
  refine ⟨biSets_mono G s n, fun j σ hσ hσn => ?_⟩
  -- the node where `σ` deviates
  obtain ⟨y, hy, hdec, hnl, hperm, hdev⟩ : ∃ y, ∃ hy : G.player (G.info y) = some j,
      G.IsDecision y ∧ n ≤ y.length ∧ Permits G j σ y ∧
        σ ⟨G.info y, hy⟩ ≠ s j ⟨G.info y, hy⟩ := by
    by_contra hno
    push Not at hno
    exact hσn fun y hy hd hl hp => hno y hy hd hl hp
  have hyl : y.length = n := by
    by_contra hne
    exact hdev (hσ y hy hdec (by omega) hperm)
  set a := (σ ⟨G.info y, hy⟩).1 with ha_def
  set a' := (s j ⟨G.info y, hy⟩).1 with ha'_def
  have hne : a ≠ a' := fun he => hdev (Subtype.ext he)
  -- the dominating strategy: follow `s` in the subgame at `y`
  set σ' : G.PureStrategy j := fun k => if InSub G y k.1 then s j k else σ k with hσ'_def
  have hσ'y : σ' ⟨G.info y, hy⟩ = s j ⟨G.info y, hy⟩ := by
    simp [hσ'_def, inSub_of_suffix G hdec (List.suffix_refl y)]
  have hσ'mem : σ' ∈ biSets G s (n + 1) j := by
    intro y' hy' hd' hl' hp'
    by_cases hin : InSub G y (G.info y')
    · simp [hσ'_def, hin]
    · have hσ'e : σ' ⟨G.info y', hy'⟩ = σ ⟨G.info y', hy'⟩ := by simp [hσ'_def, hin]
      rw [hσ'e]
      refine hσ y' hy' hd' hl' fun b v hv hbv => ?_
      have hvd : G.IsDecision v := G.isDecision_of_cons_mem (G.mem_of_suffix hbv hd'.1)
      have hnin : ¬ InSub G y (G.info v) := by
        rw [inSub_iff_of_pi G hPI hvd]
        intro hyv
        exact hin ((inSub_iff_of_pi G hPI hd').2
          (hyv.trans ((List.suffix_cons b v).trans hbv)))
      have := hp' b v hv hbv
      simp only [hσ'_def, hnin, ↓reduceIte] at this
      exact this
  -- the payoffs, as continuation payoffs
  have hpay : ∀ t : (i : I) → G.PureStrategy i,
      G.toNormalForm.payoff j t = cont G (G.pureProfile t) [] j :=
    fun t => toNormalForm_payoff_eq_cont G t j
  have hP := fun t => isPureMoves_pureProfile G hN t
  -- the two profiles differ only in the subgame at `y`
  have hdiff : ∀ r : (i : I) → G.PureStrategy i, ∀ v, G.IsDecision v →
      ¬ InSub G y (G.info v) → G.pureProfile (Function.update r j σ) (G.info v) =
        G.pureProfile (Function.update r j σ') (G.info v) := by
    intro r v hv hnin
    obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.1 (hN (G.info v))
    funext b
    rw [G.pureProfile_apply _ hk, G.pureProfile_apply _ hk]
    by_cases hkj : k = j
    · subst hkj
      simp [hσ'_def, hnin]
    · simp [Function.update_of_ne hkj]
  -- the comparison when the rivals lead to `y`
  have hcomp : ∀ r : (i : I) → G.PureStrategy i, (∀ k, k ≠ j → r k ∈ biSets G s (n + 1) k) →
      OnPath G (G.pureProfile (Function.update r j σ)) [] y →
      cont G (G.pureProfile (Function.update r j σ)) [] j =
          cont G (G.pureProfile s) (a :: y) j ∧
        cont G (G.pureProfile (Function.update r j σ')) [] j =
          cont G (G.pureProfile s) (a' :: y) j := by
    intro r hr hpath
    have hmem : ∀ τ ∈ biSets G s (n + 1) j, ∀ k,
        Function.update r j τ k ∈ biSets G s (n + 1) k := by
      intro τ hτ k
      by_cases hkj : k = j
      · subst hkj
        simpa using hτ
      · simpa [Function.update_of_ne hkj] using hr k hkj
    have hpath' : OnPath G (G.pureProfile (Function.update r j σ')) [] y := by
      intro b v _ hbv
      have hvd : G.IsDecision v := G.isDecision_of_cons_mem (G.mem_of_suffix hbv hdec.1)
      have hnin : ¬ InSub G y (G.info v) := by
        rw [inSub_iff_of_pi G hPI hvd]
        intro hyv
        have h1 := hyv.length_le
        have h2 := hbv.length_le
        simp only [List.length_cons] at h2
        omega
      rw [← hdiff r v hvd hnin]
      exact hpath b v List.nil_suffix hbv
    have hplay : G.pureProfile (Function.update r j σ) (G.info y) a = 1 :=
      (pureProfile_eq_one_iff G _ hy a).2 (by simp [ha_def])
    have hplay' : G.pureProfile (Function.update r j σ') (G.info y) a' = 1 :=
      (pureProfile_eq_one_iff G _ hy a').2 (by simp [ha'_def, hσ'y])
    have hay : a :: y ∈ G.nodes := G.cons_mem_of_mem_avail hdec (σ ⟨G.info y, hy⟩).2
    have hay' : a' :: y ∈ G.nodes := G.cons_mem_of_mem_avail hdec (s j ⟨G.info y, hy⟩).2
    constructor
    · rw [cont_onPath G (hP _) List.nil_suffix hdec.1 hpath, cont_step G (hP _) hdec hplay]
      exact cont_biSets G hN s _ (hmem σ hσ) hay (by simp [hyl])
        (hpath.cons G List.nil_suffix hplay) j
    · rw [cont_onPath G (hP _) List.nil_suffix hdec.1 hpath', cont_step G (hP _) hdec hplay']
      exact cont_biSets G hN s _ (hmem σ' hσ'mem) hay' (by simp [hyl])
        (hpath'.cons G List.nil_suffix hplay') j
  have hbi : cont G (G.pureProfile s) (a :: y) j < cont G (G.pureProfile s) (a' :: y) j :=
    bi_strict G hN hinj hs hdec hy (σ ⟨G.info y, hy⟩).2 hne
  refine ⟨σ', hσ'mem, fun r hr => ?_, ?_⟩
  · rw [hpay, hpay]
    by_cases hpath : OnPath G (G.pureProfile (Function.update r j σ)) [] y
    · obtain ⟨h1, h2⟩ := hcomp r hr hpath
      rw [h1, h2]
      exact hbi.le
    · refine (cont_agree G (hP _) G.nil_mem (fun w hw _ hpw => ?_) j).le
      refine hdiff r w hw fun hin => hpath ?_
      exact hpw.mono G ((inSub_iff_of_pi G hPI hw).1 hin)
  · refine ⟨towards G s hdec.1, fun k _ => towards_mem G hPI s hdec.1 hyl k, ?_⟩
    have hpath : OnPath G (G.pureProfile (Function.update (towards G s hdec.1) j σ)) [] y := by
      intro b v _ hbv
      have hvd : G.IsDecision v := G.isDecision_of_cons_mem (G.mem_of_suffix hbv hdec.1)
      obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.1 (hN (G.info v))
      refine (pureProfile_eq_one_iff G _ hk b).2 ?_
      by_cases hkj : k = j
      · subst hkj
        simpa using hperm b v hk hbv
      · simpa [Function.update_of_ne hkj] using towards_on_path G hPI s hdec.1 hbv hk
    obtain ⟨h1, h2⟩ := hcomp _ (fun k _ => towards_mem G hPI s hdec.1 hyl k) hpath
    rw [hpay, hpay, h1, h2]
    exact hbi

omit [DecidableEq A] [Fintype A] [DecidableEq I] in
theorem biSets_top (s : (i : I) → G.PureStrategy i) (j : I) :
    biSets G s (G.nodes.sup List.length + 1) j = Set.univ := by
  ext σ
  simp only [Set.mem_univ, iff_true]
  intro y _ hd hl _
  have := G.length_le_sup hd.1
  omega

/-- **Exercise 9.D.1** (MWG, p. 305). In a finite game of perfect information with no moves of
nature in which no player has the same payoffs at two terminal nodes (the condition of
Proposition 9.B.2 for a unique SPNE), there is a pure SPNE `s` and an order of iterated removal
of weakly dominated strategies (in the normal form) such that `s` survives and every surviving
strategy profile follows the same path as `s` and gives every player the same payoff. The
order removes, deepest decision nodes first, the strategies that deviate from backward induction
at a node they do not exclude by their own moves. -/
theorem exercise_9_D_1 (hPI : G.PerfectInformation) (hN : ∀ k, G.player k ≠ none)
    (hinj : ∀ i, ∀ z ∈ G.terminals, ∀ z' ∈ G.terminals, G.payoff i z = G.payoff i z' → z = z') :
    ∃ s : (i : I) → G.PureStrategy i, IsSPNE G (pureB G s) ∧
      ∃ T : (i : I) → Set (G.PureStrategy i),
        Relation.ReflTransGen (WDDeletionStep G.toNormalForm) (fullSets G.PureStrategy) T ∧
        (∀ i, s i ∈ T i) ∧ ∀ t : (i : I) → G.PureStrategy i, (∀ i, t i ∈ T i) →
          (∀ w ∈ G.nodes, OnPath G (G.pureProfile t) [] w ↔ OnPath G (G.pureProfile s) [] w) ∧
          ∀ i, G.toNormalForm.payoff i t = G.toNormalForm.payoff i s := by
  obtain ⟨s, hs⟩ := exists_backwardInduction G hPI
  refine ⟨s, isSPNE_of_oneShotOptimal G (isBehaviorProfile_pureB G s) hs, biSets G s 0, ?_,
    fun i y hy _ _ _ => rfl, fun t ht => ⟨fun w hw => onPath_biSets_iff G hN s t ht hw,
      fun i => ?_⟩⟩
  · set M := G.nodes.sup List.length + 1
    have key : ∀ k ≤ M, Relation.ReflTransGen (WDDeletionStep G.toNormalForm)
        (fullSets G.PureStrategy) (biSets G s (M - k)) := by
      intro k
      induction k with
      | zero =>
        intro _
        have : biSets G s (M - 0) = fullSets G.PureStrategy := by
          funext j
          exact biSets_top G s j
        rw [this]
      | succ k ih =>
        intro hk
        have he : M - k = M - (k + 1) + 1 := by omega
        refine (ih (by omega)).tail ?_
        rw [he]
        exact biSets_step G hPI hN hinj hs _
    simpa using key M le_rfl
  · rw [toNormalForm_payoff_eq_cont, toNormalForm_payoff_eq_cont]
    exact cont_biSets G hN s t ht G.nil_mem le_rfl (onPath_self G _ []) i

/-- **Exercise 9.D.1, an instance** (MWG, pp. 268 and 305). The entry game of Example 9.B.1
satisfies the hypotheses of Exercise 9.D.1 (perfect information, no moves of nature, no player
with equal payoffs at two terminal nodes), so iterated deletion of weakly dominated strategies
in a suitable order leaves only profiles with the SPNE outcome. -/
theorem exercise_9_D_1_instance :
    entryGame.PerfectInformation ∧ (∀ k, entryGame.player k ≠ none) ∧
    (∀ i, ∀ z ∈ entryGame.terminals, ∀ z' ∈ entryGame.terminals,
      entryGame.payoff i z = entryGame.payoff i z' → z = z') ∧
    ∃ s : (i : Fin 2) → entryGame.PureStrategy i, IsSPNE entryGame (pureB entryGame s) ∧
      ∃ T : (i : Fin 2) → Set (entryGame.PureStrategy i),
        Relation.ReflTransGen (WDDeletionStep entryGame.toNormalForm)
          (fullSets entryGame.PureStrategy) T ∧
        (∀ i, s i ∈ T i) ∧ ∀ t : (i : Fin 2) → entryGame.PureStrategy i, (∀ i, t i ∈ T i) →
          (∀ w ∈ entryGame.nodes, OnPath entryGame (entryGame.pureProfile t) [] w ↔
            OnPath entryGame (entryGame.pureProfile s) [] w) ∧
          ∀ i, entryGame.toNormalForm.payoff i t = entryGame.toNormalForm.payoff i s := by
  have hPI := example_9_B_1_perfectInformation
  have hN : ∀ k, entryGame.player k ≠ none := fun k => by simp [entryGame_player]
  have hinj : ∀ i, ∀ z ∈ entryGame.terminals, ∀ z' ∈ entryGame.terminals,
      entryGame.payoff i z = entryGame.payoff i z' → z = z' := by
    intro i z hz z' hz' he
    rw [entryGame_terminals] at hz hz'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz hz'
    rcases hz with rfl | rfl | rfl <;> rcases hz' with rfl | rfl | rfl <;>
      first | rfl | (fin_cases i <;> norm_num [entryGame_payoff, entryPay] at he)
  exact ⟨hPI, hN, hinj, exercise_9_D_1 entryGame hPI hN hinj⟩

end MWG.DynamicGames

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Entry followed by a coordination game

MWG, Exercise 9.B.10 (p. 303). Example 9.B.3's game (E chooses Out or In; after entry E and I
simultaneously choose Fight (`0`) or Accommodate (`1`)) is changed so that when both
accommodate, instead of receiving `(3, 1)` they play the simultaneous-move game
`[[(3, 1), (0, 0)], [(0, 0), (x, 3)]]` (E chooses `U` = `0` or `D` = `1`, I chooses `ℓ` = `0` or
`r` = `1`).

Nodes: `[]` (E: out/in, information set `0`), `[1]` (E: fight/accommodate, set `1`),
`{[0, 1], [1, 1]}` (I: fight/accommodate, set `2`), `[1, 1, 1]` (E: `U`/`D`, set `3`),
`{[0, 1, 1, 1], [1, 1, 1, 1]}` (I: `ℓ`/`r`, set `4`).

* `ec_subgames`: the subgames start at `[]`, `[1]` and `[1, 1, 1]`.
* `exercise_9_B_10_pure`: for every `x`, the pure strategy SPNE are ((in, accommodate, `U`),
  (accommodate, `ℓ`)), and, exactly when `x ≥ 1`, also ((in, accommodate, `D`),
  (accommodate, `r`)). For `0 ≤ x < 1` the coordination equilibrium `(D, r)` exists but cannot
  be part of a pure SPNE: with `(x, 3)` after (accommodate, accommodate) the post-entry game
  has no pure equilibrium.
* `exercise_9_B_10_neg`: for `x < 0` the SPNE is unique (among all behaviour profiles): `D` is
  strictly dominated in the coordination game, and the game reduces to Example 9.B.3.
* `exercise_9_B_10_mixed`: mixed equilibria of the coordination game matter for `x ≥ 0`: for
  `x = 3`, E entering and accommodating, I accommodating, and the mixed coordination
  equilibrium (`U` with probability `3/4`, `ℓ` with probability `1/2`) is a further SPNE,
  giving E the payoff `3/2`.
* `IsSPNE.pure_dev`, `assemble_pureMoves`: general facts on pure profiles used in the proofs.
-/

namespace MWG.DynamicGames

open MWG.NoncooperativeGames MWG.NoncooperativeGames.ExtensiveForm

/-- Without moves of nature, the moves of `pureMoves c` are the sure moves `c k`. -/
theorem assemble_pureMoves {I A H : Type*} [DecidableEq A] {G : ExtensiveForm I A H}
    (hN : ∀ k, G.player k ≠ none) (c : H → A) :
    G.assemble (pureMoves (I := I) c) = fun k => dirac (c k) := by
  funext k
  obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.1 (hN k)
  rw [G.assemble_of_some _ hj]
  rfl

/-- In an SPNE given by sure moves `c`, no player gains in a subgame by changing her move at
one of her information sets. -/
theorem IsSPNE.pure_dev {I A H : Type*} [DecidableEq A] [Fintype A] [DecidableEq I]
    [DecidableEq H] {G : ExtensiveForm I A H} {c : H → A} (h : IsSPNE G (pureMoves (I := I) c))
    (hc : ∀ k, c k ∈ G.avail k) {x : List A} (hx : IsSubgameRoot G x) {k : H} {i : I}
    (hk : G.player k = some i) {a : A} (ha : a ∈ G.avail k) :
    cont G (G.assemble (pureMoves (I := I) (Function.update c k a))) x i ≤
      cont G (G.assemble (pureMoves (I := I) c)) x i := by
  classical
  have hc' : ∀ k', Function.update c k a k' ∈ G.avail k' := by
    intro k'
    by_cases hkk : k' = k
    · subst hkk
      simpa using ha
    · simpa [Function.update_of_ne hkk] using hc k'
  have hdev := h.2 x hx i _ ((isBehaviorProfile_pureMoves (G := G) (I := I) hc') i)
  have heq : G.assemble (pureMoves (I := I) (Function.update c k a)) =
      G.assemble (Function.update (pureMoves (I := I) c) i
        (pureMoves (I := I) (Function.update c k a) i)) := by
    funext k'
    cases hk' : G.player k' with
    | none => rw [G.assemble_of_none _ hk', G.assemble_of_none _ hk']
    | some j =>
      rw [G.assemble_of_some _ hk', G.assemble_of_some _ hk']
      by_cases hji : j = i
      · subst hji
        simp
      · rw [Function.update_of_ne hji]
        have hkk : k' ≠ k := by
          rintro rfl
          rw [hk] at hk'
          exact hji (Option.some.inj hk').symm
        simp [pureMoves, Function.update_of_ne hkk]
  rw [heq]
  exact hdev

/-- The information sets of the game of Exercise 9.B.10. -/
def ecInfo (l : List (Fin 2)) : Fin 5 :=
  if l = [] then 0 else if l = [1] then 1 else if l = [0, 1] ∨ l = [1, 1] then 2
  else if l = [1, 1, 1] then 3 else 4

/-- The payoffs `(u_E, u_I)` of the game of Exercise 9.B.10 (Example 9.B.3's payoffs, with
the coordination game after (accommodate, accommodate)). -/
def ecPay (x : ℝ) (i : Fin 2) (l : List (Fin 2)) : ℝ :=
  if l = [0] then (if i = 0 then 0 else 2)
  else if l = [0, 0, 1] then (if i = 0 then -3 else -1)
  else if l = [1, 0, 1] then (if i = 0 then 1 else -2)
  else if l = [0, 1, 1] then (if i = 0 then -2 else -1)
  else if l = [0, 0, 1, 1, 1] then (if i = 0 then 3 else 1)
  else if l = [1, 1, 1, 1, 1] then (if i = 0 then x else 3) else 0

/-- **Exercise 9.B.10** (MWG, p. 303). The entry game of Example 9.B.3 in which (accommodate,
accommodate) is followed by the coordination game `[[(3, 1), (0, 0)], [(0, 0), (x, 3)]]`. -/
def ecGame (x : ℝ) : ExtensiveForm (Fin 2) (Fin 2) (Fin 5) where
  nodes := {[], [0], [1], [0, 1], [1, 1], [0, 0, 1], [1, 0, 1], [0, 1, 1], [1, 1, 1],
    [0, 1, 1, 1], [1, 1, 1, 1], [0, 0, 1, 1, 1], [1, 0, 1, 1, 1], [0, 1, 1, 1, 1],
    [1, 1, 1, 1, 1]}
  nil_mem := by decide
  tail_mem := by decide
  info := ecInfo
  avail _ := Finset.univ
  avail_spec := by decide
  info_surj := by decide
  player k := if k = 2 ∨ k = 4 then some 1 else some 0
  natureProb _ _ := 0
  nature_nonneg := fun k hk => absurd hk (by split_ifs <;> simp)
  nature_zero := fun k hk => absurd hk (by split_ifs <;> simp)
  nature_sum := fun k hk => absurd hk (by split_ifs <;> simp)
  payoff := ecPay x

theorem ec_noNature (x : ℝ) (k : Fin 5) : (ecGame x).player k ≠ none := by
  simp only [ecGame]
  split_ifs <;> simp

theorem ec_assemble (x : ℝ) (F : Fin 2 → Fin 5 → Fin 2 → ℝ) (k : Fin 5) :
    (ecGame x).assemble F k = F (if k = 2 ∨ k = 4 then 1 else 0) k := by
  have : (ecGame x).player k = some (if k = 2 ∨ k = 4 then 1 else 0) := by
    simp only [ecGame]
    split_ifs <;> rfl
  rw [(ecGame x).assemble_of_some F this]

/-- The continuation payoffs of the game of Exercise 9.B.10 at the roots of its subgames. -/
theorem ec_cont (x : ℝ) (f : Fin 5 → Fin 2 → ℝ) (i : Fin 2) :
    cont (ecGame x) f [1, 1, 1] i = f 3 0 * (f 4 0 * ecPay x i [0, 0, 1, 1, 1] +
      f 4 1 * ecPay x i [1, 0, 1, 1, 1]) + f 3 1 * (f 4 0 * ecPay x i [0, 1, 1, 1, 1] +
      f 4 1 * ecPay x i [1, 1, 1, 1, 1]) ∧
    cont (ecGame x) f [1] i = f 1 0 * (f 2 0 * ecPay x i [0, 0, 1] +
      f 2 1 * ecPay x i [1, 0, 1]) + f 1 1 * (f 2 0 * ecPay x i [0, 1, 1] +
      f 2 1 * cont (ecGame x) f [1, 1, 1] i) ∧
    cont (ecGame x) f [] i = f 0 0 * ecPay x i [0] + f 0 1 * cont (ecGame x) f [1] i := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [cont_unfold, ecGame, ecInfo, Fin.sum_univ_two]

theorem ec_cont3 (x : ℝ) (f : Fin 5 → Fin 2 → ℝ) (i : Fin 2) :
    cont (ecGame x) f [1, 1, 1] i = f 3 0 * (f 4 0 * ecPay x i [0, 0, 1, 1, 1] +
      f 4 1 * ecPay x i [1, 0, 1, 1, 1]) + f 3 1 * (f 4 0 * ecPay x i [0, 1, 1, 1, 1] +
      f 4 1 * ecPay x i [1, 1, 1, 1, 1]) := (ec_cont x f i).1

theorem ec_cont1 (x : ℝ) (f : Fin 5 → Fin 2 → ℝ) (i : Fin 2) :
    cont (ecGame x) f [1] i = f 1 0 * (f 2 0 * ecPay x i [0, 0, 1] +
      f 2 1 * ecPay x i [1, 0, 1]) + f 1 1 * (f 2 0 * ecPay x i [0, 1, 1] +
      f 2 1 * cont (ecGame x) f [1, 1, 1] i) := (ec_cont x f i).2.1

theorem ec_cont0 (x : ℝ) (f : Fin 5 → Fin 2 → ℝ) (i : Fin 2) :
    cont (ecGame x) f [] i = f 0 0 * ecPay x i [0] + f 0 1 * cont (ecGame x) f [1] i :=
  (ec_cont x f i).2.2

theorem ec_decisionNodes (x : ℝ) :
    (ecGame x).decisionNodes = {[], [1], [0, 1], [1, 1], [1, 1, 1], [0, 1, 1, 1], [1, 1, 1, 1]} :=
  (by decide : (ecGame 0).decisionNodes =
    {[], [1], [0, 1], [1, 1], [1, 1, 1], [0, 1, 1, 1], [1, 1, 1, 1]})

/-- The subgames of the game of Exercise 9.B.10: the whole game, the post-entry game and the
coordination game. -/
theorem ec_subgames (x : ℝ) (y : List (Fin 2)) :
    IsSubgameRoot (ecGame x) y ↔ y = [] ∨ y = [1] ∨ y = [1, 1, 1] := by
  have hdn := ec_decisionNodes x
  have hdec : ∀ y, (ecGame x).IsDecision y ↔ y = [] ∨ y = [1] ∨ y = [0, 1] ∨ y = [1, 1] ∨
      y = [1, 1, 1] ∨ y = [0, 1, 1, 1] ∨ y = [1, 1, 1, 1] :=
    fun y => by rw [← mem_decisionNodes, hdn]; simp
  have hinfo : ∀ y, (ecGame x).info y = ecInfo y := fun _ => rfl
  constructor
  · intro h
    rcases (hdec y).1 h.1 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact absurd (h.2.1 [1, 1] ((hdec _).2 (by simp)) rfl) (by simp)
    · exact absurd (h.2.1 [0, 1] ((hdec _).2 (by simp)) rfl) (by simp)
    · exact Or.inr (Or.inr rfl)
    · exact absurd (h.2.1 [1, 1, 1, 1] ((hdec _).2 (by simp)) rfl) (by simp)
    · exact absurd (h.2.1 [0, 1, 1, 1] ((hdec _).2 (by simp)) rfl) (by simp)
  · rintro (rfl | rfl | rfl)
    · refine ⟨(hdec _).2 (by simp), fun y hy he => ?_, fun _ _ _ _ _ _ => List.nil_suffix⟩
      rcases (hdec y).1 hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp_all [ecInfo]
    · refine ⟨(hdec _).2 (by simp), fun y hy he => ?_, fun y hy hxy y' hy' he => ?_⟩
      · rcases (hdec y).1 hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp_all [ecInfo]
      · rcases (hdec y).1 hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        rcases (hdec y').1 hy' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        revert he hxy <;> simp only [hinfo] <;> decide
    · refine ⟨(hdec _).2 (by simp), fun y hy he => ?_, fun y hy hxy y' hy' he => ?_⟩
      · rcases (hdec y).1 hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp_all [ecInfo]
      · rcases (hdec y).1 hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        rcases (hdec y').1 hy' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        revert he hxy <;> simp only [hinfo] <;> decide

theorem ec_beh (x : ℝ) (i : Fin 2) {g : Fin 5 → Fin 2 → ℝ}
    (hg : (ecGame x).IsBehaviorStrategy i g) (k : Fin 5)
    (hk : (if k = 2 ∨ k = 4 then some (1 : Fin 2) else some 0) = some i) :
    0 ≤ g k 0 ∧ 0 ≤ g k 1 ∧ g k 0 + g k 1 = 1 := by
  have h := hg k hk
  exact ⟨h.1 0, h.1 1, by simpa [ecGame] using h.2.2⟩

theorem ec_spne_U (x : ℝ) : IsSPNE (ecGame x) (pureMoves ![1, 1, 1, 0, 0]) := by
  refine ⟨isBehaviorProfile_pureMoves fun _ => Finset.mem_univ _, fun y hy => ?_⟩
  rcases (ec_subgames x y).1 hy with rfl | rfl | rfl <;> rw [InducesNashAt, Fin.forall_fin_two] <;>
    constructor <;> intro g hg
  all_goals first
    | (obtain ⟨a0, a1, a2⟩ := ec_beh x 0 hg 0 (by simp)
       obtain ⟨b0, b1, b2⟩ := ec_beh x 0 hg 1 (by simp)
       obtain ⟨d0, d1, d2⟩ := ec_beh x 0 hg 3 (by simp)
       simp [ec_cont0, ec_cont1, ec_cont3, ec_assemble, pureMoves, dirac, ecPay]
       nlinarith [mul_nonneg a1 b0, mul_nonneg a1 b1, mul_nonneg (mul_nonneg a1 b1) d0,
         mul_nonneg (mul_nonneg a1 b1) d1, mul_nonneg b1 d1, mul_nonneg b1 d0])
    | (obtain ⟨e0, e1, e2⟩ := ec_beh x 1 hg 2 (by simp)
       obtain ⟨f0, f1, f2⟩ := ec_beh x 1 hg 4 (by simp)
       simp [ec_cont0, ec_cont1, ec_cont3, ec_assemble, pureMoves, dirac, ecPay]
       nlinarith [mul_nonneg e1 f0, mul_nonneg e1 f1, mul_nonneg e0 f0, mul_nonneg e0 f1])

theorem ec_spne_D (x : ℝ) (hx : 1 ≤ x) : IsSPNE (ecGame x) (pureMoves ![1, 1, 1, 1, 1]) := by
  refine ⟨isBehaviorProfile_pureMoves fun _ => Finset.mem_univ _, fun y hy => ?_⟩
  have hx0 : 0 ≤ x - 1 := by linarith
  rcases (ec_subgames x y).1 hy with rfl | rfl | rfl <;> rw [InducesNashAt, Fin.forall_fin_two] <;>
    constructor <;> intro g hg
  all_goals first
    | (obtain ⟨a0, a1, a2⟩ := ec_beh x 0 hg 0 (by simp)
       obtain ⟨b0, b1, b2⟩ := ec_beh x 0 hg 1 (by simp)
       obtain ⟨d0, d1, d2⟩ := ec_beh x 0 hg 3 (by simp)
       have h3 : x * g 0 1 * g 1 1 * (g 3 0 + g 3 1) = x * g 0 1 * g 1 1 := by rw [d2, mul_one]
       have h4 : x * g 0 1 * (g 1 0 + g 1 1) = x * g 0 1 := by rw [b2, mul_one]
       have h5 : x * g 1 1 * (g 3 0 + g 3 1) = x * g 1 1 := by rw [d2, mul_one]
       simp [ec_cont0, ec_cont1, ec_cont3, ec_assemble, pureMoves, dirac, ecPay]
       nlinarith [h3, h4, h5, mul_nonneg a1 b0, mul_nonneg a1 b1, mul_nonneg (mul_nonneg a1 b1) d0,
         mul_nonneg (mul_nonneg a1 b1) d1, mul_nonneg b1 d1, mul_nonneg b1 d0,
         mul_nonneg hx0 (mul_nonneg a1 b0), mul_nonneg hx0 b0, mul_nonneg hx0 a0,
         mul_nonneg (by linarith : (0 : ℝ) ≤ x) (mul_nonneg (mul_nonneg a1 b1) d0),
         mul_nonneg (by linarith : (0 : ℝ) ≤ x) (mul_nonneg b1 d0),
         mul_nonneg (by linarith : (0 : ℝ) ≤ x) d0, mul_nonneg (by linarith : (0 : ℝ) ≤ x) a0])
    | (obtain ⟨e0, e1, e2⟩ := ec_beh x 1 hg 2 (by simp)
       obtain ⟨f0, f1, f2⟩ := ec_beh x 1 hg 4 (by simp)
       simp [ec_cont0, ec_cont1, ec_cont3, ec_assemble, pureMoves, dirac, ecPay]
       nlinarith [mul_nonneg e1 f0, mul_nonneg e1 f1, mul_nonneg e0 f0, mul_nonneg e0 f1])

/-- **Exercise 9.B.10** (MWG, p. 303). The pure strategy subgame perfect Nash equilibria, for
every `x`: ((in, accommodate, `U`), (accommodate, `ℓ`)) always, and ((in, accommodate, `D`),
(accommodate, `r`)) exactly when `x ≥ 1`. (Moves are listed by information set: E's entry,
E's post-entry move, I's post-entry move, E's and I's moves in the coordination game.) -/
theorem exercise_9_B_10_pure (x : ℝ) (c : Fin 5 → Fin 2) :
    IsSPNE (ecGame x) (pureMoves c) ↔ c = ![1, 1, 1, 0, 0] ∨ (1 ≤ x ∧ c = ![1, 1, 1, 1, 1]) := by
  have hN := ec_noNature x
  have hsub := ec_subgames x
  have hA := fun c' : Fin 5 → Fin 2 => assemble_pureMoves (G := ecGame x) (I := Fin 2) hN c'
  constructor
  · intro h
    have d : ∀ y, y = [] ∨ y = [1] ∨ y = [1, 1, 1] → ∀ (k : Fin 5) (a : Fin 2),
        cont (ecGame x) (fun k' => dirac (Function.update c k a k')) y
            (if k = 2 ∨ k = 4 then 1 else 0) ≤
          cont (ecGame x) (fun k' => dirac (c k')) y (if k = 2 ∨ k = 4 then 1 else 0) := by
      intro y hy k a
      have := h.pure_dev (fun _ => Finset.mem_univ _) ((hsub y).2 hy) (k := k)
        (i := if k = 2 ∨ k = 4 then 1 else 0) (by simp only [ecGame]; split_ifs <;> rfl)
        (Finset.mem_univ a)
      rwa [hA, hA] at this
    have d30 := d [1, 1, 1] (by simp) 3 0
    have d31 := d [1, 1, 1] (by simp) 3 1
    have d40 := d [1, 1, 1] (by simp) 4 0
    have d41 := d [1, 1, 1] (by simp) 4 1
    have d10 := d [1] (by simp) 1 0
    have d11 := d [1] (by simp) 1 1
    have d20 := d [1] (by simp) 2 0
    have d21 := d [1] (by simp) 2 1
    have d00 := d [] (by simp) 0 0
    have d01 := d [] (by simp) 0 1
    clear d
    simp only [ec_cont0, ec_cont1, ec_cont3] at d30 d31 d40 d41 d10 d11 d20 d21 d00 d01
    obtain ⟨c0, c1, c2, c3, c4, rfl⟩ : ∃ c0 c1 c2 c3 c4 : Fin 2, c = ![c0, c1, c2, c3, c4] :=
      ⟨c 0, c 1, c 2, c 3, c 4, by funext k; fin_cases k <;> rfl⟩
    have h2 : ∀ k : Fin 2, k = 0 ∨ k = 1 := by decide
    rcases h2 c0 with rfl | rfl <;> rcases h2 c1 with rfl | rfl <;>
      rcases h2 c2 with rfl | rfl <;> rcases h2 c3 with rfl | rfl <;>
      rcases h2 c4 with rfl | rfl <;>
      norm_num [dirac, Function.update_apply, ecPay] at * <;>
      first | exact Or.inl rfl | linarith
  · rintro (rfl | ⟨hx, rfl⟩)
    · exact ec_spne_U x
    · exact ec_spne_D x hx

/-- **Exercise 9.B.10, `x < 0`** (MWG, p. 303). If `x < 0`, `D` is strictly dominated by `U` in
the coordination game, so its unique equilibrium is `(U, ℓ)` with payoffs `(3, 1)`, and the game
reduces to Example 9.B.3: the unique SPNE (among all behaviour profiles) is ((in, accommodate,
`U`), (accommodate, `ℓ`)). -/
theorem exercise_9_B_10_neg (x : ℝ) (hx : x < 0) :
    IsSPNE (ecGame x) (pureMoves ![1, 1, 1, 0, 0]) ∧ ∀ F, IsSPNE (ecGame x) F →
      F 0 0 1 = 1 ∧ F 0 1 1 = 1 ∧ F 1 2 1 = 1 ∧ F 0 3 0 = 1 ∧ F 1 4 0 = 1 := by
  refine ⟨ec_spne_U x, fun F hF => ?_⟩
  have hsub := ec_subgames x
  have hb0 := ec_beh x 0 (hF.1 0) 0 (by simp)
  have hb1 := ec_beh x 0 (hF.1 0) 1 (by simp)
  have hb2 := ec_beh x 1 (hF.1 1) 2 (by simp)
  have hb3 := ec_beh x 0 (hF.1 0) 3 (by simp)
  have hb4 := ec_beh x 1 (hF.1 1) 4 (by simp)
  have hdev : ∀ (i : Fin 2) (k : Fin 5) (a : Fin 2),
      (if k = 2 ∨ k = 4 then some (1 : Fin 2) else some 0) = some i →
      (ecGame x).IsBehaviorStrategy i (Function.update (F i) k (dirac a)) := by
    intro i k a hk k' hk'
    by_cases hkk : k' = k
    · subst hkk
      simp only [Function.update_self]
      exact (isBehaviorProfile_pureMoves (I := Fin 2) (G := ecGame x) (c := fun _ => a)
        fun _ => Finset.mem_univ _) i k' hk'
    · rw [Function.update_of_ne hkk]
      exact hF.1 i k' hk'
  have hpos : 0 < 3 * F 1 4 0 - x * F 1 4 1 := by
    rcases eq_or_lt_of_le hb4.1 with h | h
    · have h1 : F 1 4 1 = 1 := by linarith [hb4.2.2]
      rw [← h, h1]
      linarith
    · nlinarith [mul_nonneg hb4.2.1 (neg_nonneg.2 hx.le)]
  -- in the coordination game E plays `U`
  have hE3 := hF.2 [1, 1, 1] ((hsub _).2 (by simp)) 0 _ (hdev 0 3 0 (by simp))
  simp [ec_cont3, ec_assemble, dirac, ecPay] at hE3
  have hU : F 0 3 1 = 0 := by
    by_contra hne
    have h1 : 0 < F 0 3 1 := lt_of_le_of_ne hb3.2.1 (Ne.symm hne)
    nlinarith [mul_pos h1 hpos]
  have hU0 : F 0 3 0 = 1 := by linarith [hb3.2.2]
  -- then I plays `ℓ`
  have hI4 := hF.2 [1, 1, 1] ((hsub _).2 (by simp)) 1 _ (hdev 1 4 0 (by simp))
  simp [ec_cont3, ec_assemble, dirac, ecPay, hU, hU0] at hI4
  have hl : F 1 4 0 = 1 := by linarith [hb4.2.2]
  have hl1 : F 1 4 1 = 0 := by linarith [hb4.2.2]
  -- in the post-entry game E accommodates
  have hE1 := hF.2 [1] ((hsub _).2 (by simp)) 0 _ (hdev 0 1 1 (by simp))
  simp [ec_cont1, ec_cont3, ec_assemble, dirac, ecPay, hU, hU0, hl, hl1] at hE1
  have hp : F 0 1 1 = 1 := by nlinarith [mul_nonneg hb1.1 hb2.2.1]
  have hp0 : F 0 1 0 = 0 := by linarith [hb1.2.2]
  -- then I accommodates
  have hI2 := hF.2 [1] ((hsub _).2 (by simp)) 1 _ (hdev 1 2 1 (by simp))
  simp [ec_cont1, ec_cont3, ec_assemble, dirac, ecPay, hU, hU0, hl, hl1, hp, hp0] at hI2
  have hq : F 1 2 1 = 1 := by nlinarith [hb2.2.2]
  have hq0 : F 1 2 0 = 0 := by linarith [hb2.2.2]
  -- then E enters
  have hE0 := hF.2 [] ((hsub _).2 (by simp)) 0 _ (hdev 0 0 1 (by simp))
  simp [ec_cont0, ec_cont1, ec_cont3, ec_assemble, dirac, ecPay, hU, hU0, hl, hl1, hp, hp0, hq,
    hq0] at hE0
  exact ⟨by nlinarith [hb0.2.2], hp, hq, hU0, hl⟩

/-- The profile of `exercise_9_B_10_mixed`: E enters and accommodates, I accommodates, and in
the coordination game E plays `U` with probability `3/4` and I plays `ℓ` with probability
`1/2`. -/
noncomputable def ecMixed : Fin 2 → Fin 5 → Fin 2 → ℝ :=
  fun _ k => if k = 3 then ![3 / 4, 1 / 4] else if k = 4 then ![1 / 2, 1 / 2] else ![0, 1]

/-- **Exercise 9.B.10, mixed equilibria** (MWG, p. 303). The mixed equilibria of the
coordination game matter for the answer when `x ≥ 0`: for `x = 3`, entering and accommodating,
with the mixed coordination equilibrium (`U` with probability `3/4`, `ℓ` with probability
`1/2`) after (accommodate, accommodate), is a further SPNE, giving E the payoff `3/2` (the pure
SPNE give `3` and `x = 3`). -/
theorem exercise_9_B_10_mixed :
    IsSPNE (ecGame 3) ecMixed ∧ cont (ecGame 3) ((ecGame 3).assemble ecMixed) [] 0 = 3 / 2 := by
  have hval : ecMixed 0 0 = ![0, 1] ∧ ecMixed 0 1 = ![0, 1] ∧ ecMixed 1 2 = ![0, 1] ∧
      ecMixed 0 3 = ![3 / 4, 1 / 4] ∧ ecMixed 1 4 = ![1 / 2, 1 / 2] := ⟨rfl, rfl, rfl, rfl, rfl⟩
  refine ⟨⟨fun i k _ => ?_, fun y hy => ?_⟩, ?_⟩
  · refine ⟨fun a => ?_, fun a ha => absurd (Finset.mem_univ a) ha, ?_⟩
    · fin_cases a <;> simp [ecMixed] <;> split_ifs <;> norm_num
    · simp [ecMixed, ecGame, Fin.sum_univ_two]
      split_ifs <;> norm_num
  · rcases (ec_subgames 3 y).1 hy with rfl | rfl | rfl <;>
      rw [InducesNashAt, Fin.forall_fin_two] <;> constructor <;> intro g hg
    all_goals first
      | (obtain ⟨a0, a1, a2⟩ := ec_beh 3 0 hg 0 (by simp)
         obtain ⟨b0, b1, b2⟩ := ec_beh 3 0 hg 1 (by simp)
         obtain ⟨d0, d1, d2⟩ := ec_beh 3 0 hg 3 (by simp)
         simp [ec_cont0, ec_cont1, ec_cont3, ec_assemble, hval, ecPay]
         nlinarith [mul_nonneg a1 b0, mul_nonneg a1 b1, mul_nonneg (mul_nonneg a1 b1) d0,
           mul_nonneg (mul_nonneg a1 b1) d1, mul_nonneg b1 d1, mul_nonneg b1 d0])
      | (obtain ⟨e0, e1, e2⟩ := ec_beh 3 1 hg 2 (by simp)
         obtain ⟨f0, f1, f2⟩ := ec_beh 3 1 hg 4 (by simp)
         simp [ec_cont0, ec_cont1, ec_cont3, ec_assemble, hval, ecPay]
         nlinarith [mul_nonneg e1 f0, mul_nonneg e1 f1, mul_nonneg e0 f0, mul_nonneg e0 f1])
  · simp [ec_cont0, ec_cont1, ec_cont3, ec_assemble, hval, ecPay]
    norm_num

end MWG.DynamicGames

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Strict backward induction

Tools for solving concrete finite games of perfect information by backward induction
(MWG, Section 9.B, pp. 270-276), used for Exercise 9.B.14.

* `cont_dirac_play`: with sure moves `c` (no moves of nature), the continuation payoff from a
  node is the payoff at the terminal node reached by following `c`, computed by iterating one
  step of play.
* `isSPNE_of_weak_bi`: sure moves that are optimal at every decision node given the continuation
  play form an SPNE.
* `eq_dirac_of_strict_bi`: if at every decision node after `x₀` the mover strictly prefers the
  move `c` to every other move (given the continuation play of `c`), every SPNE (in behaviour
  strategies) plays `c` at every decision node after `x₀`. Unlike Proposition 9.B.2 this needs no
  assumption on ties at terminal nodes, only strictness along the backward-induction solution.
-/

namespace MWG.DynamicGames

open MWG.NoncooperativeGames MWG.NoncooperativeGames.ExtensiveForm

variable {I A H : Type*} (G : ExtensiveForm I A H) [DecidableEq A] [Fintype A] [DecidableEq I]

omit [Fintype A] [DecidableEq I] in
theorem isPureMoves_dirac {c : H → A} (hc : ∀ k, c k ∈ G.avail k) :
    IsPureMoves G (fun k => dirac (c k)) := by
  refine ⟨fun k a => ?_, fun k a ha => ?_, fun k => ?_⟩
  · change dirac (c k) a = 0 ∨ dirac (c k) a = 1
    unfold dirac
    split_ifs <;> simp
  · have : a ≠ c k := fun he => ha (he ▸ hc k)
    simp [dirac, this]
  · simp only [dirac]
    rw [Finset.sum_ite_eq' (G.avail k)]
    simp [hc k]

/-- One step of play with sure moves `c`: at a decision node the move `c` is taken, a terminal
node is left unchanged. -/
def bstep (c : H → A) (l : List A) : List A :=
  if ∃ b, b :: l ∈ G.nodes then c (G.info l) :: l else l

omit [DecidableEq I] in
/-- With sure moves `c`, the continuation payoff from node `x` is the payoff at the terminal node
reached from `x` by following `c`: iterate `bstep` at least as often as the length of the
longest node. -/
theorem cont_dirac_play {c : H → A} (hc : ∀ k, c k ∈ G.avail k) {n : ℕ}
    (hn : ∀ y ∈ G.nodes, y.length ≤ n) {x : List A} (hx : x ∈ G.nodes) (i : I) :
    cont G (fun k => dirac (c k)) x i = G.payoff i ((bstep G c)^[n] x) := by
  suffices key : ∀ m, ∀ x ∈ G.nodes, n ≤ x.length + m →
      cont G (fun k => dirac (c k)) x i = G.payoff i ((bstep G c)^[m] x) from
    key n x hx (by omega)
  intro m
  induction m with
  | zero =>
    intro y hy hl
    have hterm : G.IsTerminal y := by
      refine ⟨hy, fun b hb => ?_⟩
      have := hn _ hb
      simp only [List.length_cons] at this
      omega
    rw [cont_terminal _ _ hterm]
    rfl
  | succ m ih =>
    intro y hy hl
    rcases (G.isDecision_or_isTerminal hy).1 with hdec | hterm
    · have hb : bstep G c y = c (G.info y) :: y := by
        simp only [bstep, hdec.2, ↓reduceIte]
      rw [Function.iterate_succ_apply, hb,
        cont_step G (isPureMoves_dirac G hc) hdec (by simp [dirac] : dirac (c (G.info y))
          (c (G.info y)) = 1)]
      exact ih _ (G.cons_mem_of_mem_avail hdec (hc _)) (by simp only [List.length_cons]; omega)
    · have hb : bstep G c y = y := by
        have : ¬ ∃ b, b :: y ∈ G.nodes := fun ⟨b, hb⟩ => hterm.2 b hb
        simp only [bstep, this, ↓reduceIte]
      rw [Function.iterate_fixed hb, cont_terminal _ _ hterm]

/-- **Backward induction** (MWG, pp. 270-276). Sure moves `c` (no moves of nature) such that at
every decision node the mover's continuation payoff after `c` is at least that after any other
move form a subgame perfect Nash equilibrium. -/
theorem isSPNE_of_weak_bi (hN : ∀ k, G.player k ≠ none) {c : H → A}
    (hc : ∀ k, c k ∈ G.avail k)
    (hweak : ∀ x, G.IsDecision x → ∀ j, G.player (G.info x) = some j → ∀ a ∈ G.avail (G.info x),
      cont G (fun k => dirac (c k)) (a :: x) j ≤
        cont G (fun k => dirac (c k)) (c (G.info x) :: x) j) :
    IsSPNE G (pureMoves (I := I) c) := by
  refine isSPNE_of_oneShotOptimal G (isBehaviorProfile_pureMoves hc) fun x hx j hj a ha => ?_
  rw [assemble_pureMoves hN, cont_step G (isPureMoves_dirac G hc) hx
    (by simp [dirac] : dirac (c (G.info x)) (c (G.info x)) = 1)]
  exact hweak x hx j hj a ha

/-- **Strict backward induction** (MWG, p. 276). Suppose that at every decision node `x` after
`x₀` the mover strictly prefers `c (H(x))` to every other move, given the continuation play of
`c`. Then every subgame perfect Nash equilibrium of a game of perfect information without moves
of nature plays `c` at every decision node after `x₀`. -/
theorem eq_dirac_of_strict_bi (hPI : G.PerfectInformation)
    (hN : ∀ k, G.player k ≠ none) {c : H → A} (hc : ∀ k, c k ∈ G.avail k) {x₀ : List A}
    (hstrict : ∀ x, G.IsDecision x → x₀ <:+ x → ∀ j, G.player (G.info x) = some j →
      ∀ a ∈ G.avail (G.info x), a ≠ c (G.info x) →
        cont G (fun k => dirac (c k)) (a :: x) j <
          cont G (fun k => dirac (c k)) (c (G.info x) :: x) j)
    {F : I → H → A → ℝ} (hF : IsSPNE G F) :
    ∀ x, G.IsDecision x → x₀ <:+ x → G.assemble F (G.info x) = dirac (c (G.info x)) := by
  set P : H → A → ℝ := fun k => dirac (c k)
  suffices key : ∀ n, ∀ y ∈ G.nodes, x₀ <:+ y → G.nodes.sup List.length - y.length ≤ n →
      ∀ x, G.IsDecision x → y <:+ x → G.assemble F (G.info x) = P (G.info x) by
    intro x hx hx₀
    exact key _ x hx.1 hx₀ le_rfl x hx (List.suffix_refl x)
  intro n
  induction n with
  | zero =>
    intro y hy _ hn x hx hyx
    have hterm : G.IsTerminal y := by
      refine ⟨hy, fun b hb => ?_⟩
      have := G.length_le_sup hb
      simp only [List.length_cons] at this
      omega
    have := G.eq_of_terminal_suffix hterm hx.1 hyx
    subst this
    exact absurd ⟨hx, hterm⟩ (G.isDecision_or_isTerminal hy).2
  | succ n ih =>
    intro y hy hy₀ hn
    rcases (G.isDecision_or_isTerminal hy).1 with hdec | hterm
    · have hchild : ∀ a ∈ G.avail (G.info y), ∀ x, G.IsDecision x → a :: y <:+ x →
          G.assemble F (G.info x) = P (G.info x) := by
        intro a ha
        have hmem := G.cons_mem_of_mem_avail hdec ha
        have hl := G.length_le_sup hmem
        simp only [List.length_cons] at hl
        exact ih (a :: y) hmem (hy₀.trans (List.suffix_cons a y))
          (by simp only [List.length_cons]; omega)
      have hcont : ∀ a ∈ G.avail (G.info y), ∀ i,
          cont G (G.assemble F) (a :: y) i = cont G P (a :: y) i :=
        fun a ha i => cont_congr G (fun w hw haw => hchild a ha w hw haw) i
      have hy' : G.assemble F (G.info y) = P (G.info y) := by
        obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.1 (hN (G.info y))
        set a₀ := c (G.info y)
        have ha₀ : a₀ ∈ G.avail (G.info y) := hc _
        have hopt := oneShotOptimal_of_isSPNE G hPI hF hdec j hj
        have hsum := cont_decision G (G.assemble F) hdec j
        have hge := hopt a₀ ha₀
        have hnn : ∀ a ∈ G.avail (G.info y), 0 ≤ G.assemble F (G.info y) a *
            (cont G P (a₀ :: y) j - cont G P (a :: y) j) := by
          intro a ha
          refine mul_nonneg (assemble_nonneg G hF.1 _ _) ?_
          by_cases hae : a = a₀
          · rw [hae, sub_self]
          · linarith [hstrict y hdec hy₀ j hj a ha hae]
        have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 (by
          refine le_antisymm ?_ (Finset.sum_nonneg hnn)
          simp_rw [mul_sub]
          rw [Finset.sum_sub_distrib, ← Finset.sum_mul, assemble_sum G hF.1, one_mul]
          have : ∑ a ∈ G.avail (G.info y), G.assemble F (G.info y) a * cont G P (a :: y) j =
              cont G (G.assemble F) y j := by
            rw [hsum]
            exact Finset.sum_congr rfl fun a ha => by rw [hcont a ha j]
          rw [this, ← hcont a₀ ha₀ j]
          linarith)
        have hoff : ∀ a ∈ G.avail (G.info y), a ≠ a₀ → G.assemble F (G.info y) a = 0 := by
          intro a ha hne
          rcases mul_eq_zero.1 (hzero a ha) with h | h
          · exact h
          · linarith [hstrict y hdec hy₀ j hj a ha hne]
        have hon : G.assemble F (G.info y) a₀ = 1 := by
          have := assemble_sum G hF.1 (G.info y)
          rw [← Finset.add_sum_erase _ _ ha₀, Finset.sum_eq_zero fun a ha =>
            hoff a (Finset.mem_of_mem_erase ha) (Finset.ne_of_mem_erase ha), add_zero] at this
          exact this
        funext a
        simp only [P, dirac]
        split_ifs with h
        · rw [h]
          exact hon
        · by_cases ha : a ∈ G.avail (G.info y)
          · exact hoff a ha h
          · rw [G.assemble_of_some _ hj]
            exact (hF.1 j _ hj).2.1 a ha
      intro x hx hyx
      by_cases hxy : x = y
      · rw [hxy]
        exact hy'
      · obtain ⟨b, hb⟩ := exists_cons_suffix hyx (Ne.symm hxy)
        exact hchild b (G.mem_avail_of_cons_mem (G.mem_of_suffix hb hx.1)) x hx hb
    · intro x hx hyx
      have := G.eq_of_terminal_suffix hterm hx.1 hyx
      subst this
      exact absurd ⟨hx, hterm⟩ (G.isDecision_or_isTerminal hy).2

end MWG.DynamicGames

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Three-period entry deterrence

MWG, Exercise 9.B.14 (pp. 303-304). At time 0 the entrant E decides whether to enter at cost
`K > 0`; then in each of three production periods `t = 0, 1, 2` in which E is active the game
of Figure 9.Ex.1 is played: E first decides whether to stay in or exit; if E stays, the incumbent
I fights (payoffs `(−1, y)`) or accommodates (`(1, z)`); once E exits it is out for good, earning
`0` while I earns `x` per period. Payoffs are discounted by `δ`. Assumptions (A.1) `x > z > y`,
(A.2) `y + δx > (1 + δ)z`, (A.3) `1 + δ > K`.

The games are finite games of perfect information without moves of nature: `deterA` (part (a))
and `deterB` (part (b): after a fight E is forced out of the market). Actions: `1` = enter /
stay / accommodate, `0` = stay out / exit / fight. Nodes are histories (most recent action
first), and every decision node is its own information set (E's nodes are listed first).

* `exercise_9_B_14a`: under (A.1) (only `z > y` is used) and (A.3), with `δ > 0`, the unique
  SPNE is: E enters and stays in after every history, I accommodates after every history.
* `exercise_9_B_14b`: with the financial constraint, under (A.1) (`z > y`) and (A.2), with
  `δ > 0`, the SPNE strategies after entry are unique: E stays in periods 0 and 2 and exits in
  period 1; I accommodates in periods 0 and 2 and fights in period 1. On the equilibrium path
  E enters iff `K < 1` (payoff `1 − K`), exits in period 1, and I accommodates once. The answer
  depends on `K` beyond (A.3): if `K < 1` the unique SPNE has E entering, if `K > 1` the unique
  SPNE has E staying out, and if `K = 1` both are SPNE (and every SPNE plays the unique
  post-entry strategies).
* `exercise_9_B_14_instance`: `(x, z, y, δ) = (4, 1, 0, 1/2)` satisfies the assumptions, with
  `K = 1/2` and `K = 5/4`.

The proofs use strict backward induction (`eq_dirac_of_strict_bi`) and compute continuation
payoffs by following the sure moves to a terminal node (`cont_dirac_play`, `decide`).
-/

namespace MWG.DynamicGames

open MWG.NoncooperativeGames MWG.NoncooperativeGames.ExtensiveForm

/-- The nodes of the game of Exercise 9.B.14(a). -/
def dtNodesA : Finset (List (Fin 2)) :=
  {[], [0], [1], [0, 1], [1, 1], [0, 1, 1], [0, 0, 1, 1], [1, 0, 1, 1], [0, 1, 0, 1, 1],
    [0, 0, 1, 0, 1, 1], [1, 0, 1, 0, 1, 1], [0, 1, 0, 1, 0, 1, 1], [1, 1, 0, 1, 0, 1, 1],
    [1, 1, 0, 1, 1], [0, 1, 1, 0, 1, 1], [1, 1, 1, 0, 1, 1], [0, 1, 1, 1, 0, 1, 1],
    [1, 1, 1, 1, 0, 1, 1], [1, 1, 1], [0, 1, 1, 1], [1, 1, 1, 1], [0, 1, 1, 1, 1],
    [0, 0, 1, 1, 1, 1], [1, 0, 1, 1, 1, 1], [0, 1, 0, 1, 1, 1, 1], [1, 1, 0, 1, 1, 1, 1],
    [1, 1, 1, 1, 1], [0, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1], [0, 1, 1, 1, 1, 1, 1],
    [1, 1, 1, 1, 1, 1, 1]}

/-- The information sets (one per decision node) of the game of Exercise 9.B.14(a): E's
nodes first. -/
def dtInfoA (l : List (Fin 2)) : Fin 15 :=
  if l = [1] then 1 else if l = [0, 1, 1] then 2 else if l = [0, 1, 0, 1, 1] then 3 else
  if l = [1, 1, 0, 1, 1] then 4 else if l = [1, 1, 1] then 5 else
  if l = [0, 1, 1, 1, 1] then 6 else if l = [1, 1, 1, 1, 1] then 7 else if l = [1, 1] then 8 else
  if l = [1, 0, 1, 1] then 9 else if l = [1, 0, 1, 0, 1, 1] then 10 else
  if l = [1, 1, 1, 0, 1, 1] then 11 else if l = [1, 1, 1, 1] then 12 else
  if l = [1, 0, 1, 1, 1, 1] then 13 else if l = [1, 1, 1, 1, 1, 1] then 14 else 0

/-- The payoffs `(u_E, u_I)` of the game of Exercise 9.B.14(a). -/
def dtPayA (x y z δ K : ℝ) (i : Fin 2) (l : List (Fin 2)) : ℝ :=
  if l = [0] then
    (if i = 0 then 0 else x + δ * x + δ ^ 2 * x)
  else if l = [0, 1] then
    (if i = 0 then -K else x + δ * x + δ ^ 2 * x)
  else if l = [0, 0, 1, 1] then
    (if i = 0 then -K - 1 else y + δ * x + δ ^ 2 * x)
  else if l = [0, 0, 1, 0, 1, 1] then
    (if i = 0 then -K - 1 - δ else y + δ * y + δ ^ 2 * x)
  else if l = [0, 1, 0, 1, 0, 1, 1] then
    (if i = 0 then -K - 1 - δ - δ ^ 2 else y + δ * y + δ ^ 2 * y)
  else if l = [1, 1, 0, 1, 0, 1, 1] then
    (if i = 0 then -K - 1 - δ + δ ^ 2 else y + δ * y + δ ^ 2 * z)
  else if l = [0, 1, 1, 0, 1, 1] then
    (if i = 0 then -K - 1 + δ else y + δ * z + δ ^ 2 * x)
  else if l = [0, 1, 1, 1, 0, 1, 1] then
    (if i = 0 then -K - 1 + δ - δ ^ 2 else y + δ * z + δ ^ 2 * y)
  else if l = [1, 1, 1, 1, 0, 1, 1] then
    (if i = 0 then -K - 1 + δ + δ ^ 2 else y + δ * z + δ ^ 2 * z)
  else if l = [0, 1, 1, 1] then
    (if i = 0 then -K + 1 else z + δ * x + δ ^ 2 * x)
  else if l = [0, 0, 1, 1, 1, 1] then
    (if i = 0 then -K + 1 - δ else z + δ * y + δ ^ 2 * x)
  else if l = [0, 1, 0, 1, 1, 1, 1] then
    (if i = 0 then -K + 1 - δ - δ ^ 2 else z + δ * y + δ ^ 2 * y)
  else if l = [1, 1, 0, 1, 1, 1, 1] then
    (if i = 0 then -K + 1 - δ + δ ^ 2 else z + δ * y + δ ^ 2 * z)
  else if l = [0, 1, 1, 1, 1, 1] then
    (if i = 0 then -K + 1 + δ else z + δ * z + δ ^ 2 * x)
  else if l = [0, 1, 1, 1, 1, 1, 1] then
    (if i = 0 then -K + 1 + δ - δ ^ 2 else z + δ * z + δ ^ 2 * y)
  else if l = [1, 1, 1, 1, 1, 1, 1] then
    (if i = 0 then -K + 1 + δ + δ ^ 2 else z + δ * z + δ ^ 2 * z)
  else 0

/-- **Exercise 9.B.14(a)** (MWG, pp. 303-304). -/
def deterA (x y z δ K : ℝ) : ExtensiveForm (Fin 2) (Fin 2) (Fin 15) where
  nodes := dtNodesA
  nil_mem := by decide
  tail_mem := by decide
  info := dtInfoA
  avail _ := Finset.univ
  avail_spec := by decide
  info_surj := by decide
  player k := if (k : ℕ) < 8 then some 0 else some 1
  natureProb _ _ := 0
  nature_nonneg := fun k hk => absurd hk (by split_ifs <;> simp)
  nature_zero := fun k hk => absurd hk (by split_ifs <;> simp)
  nature_sum := fun k hk => absurd hk (by split_ifs <;> simp)
  payoff := dtPayA x y z δ K

/-- One step of play with sure moves `c` in the game of Exercise 9.B.14(a). -/
def dtStepA (c : Fin 15 → Fin 2) : List (Fin 2) → List (Fin 2) :=
  bstep (deterA 0 0 0 0 0) c

theorem dtA_decisionNodes (x y z δ K : ℝ) :
    (deterA x y z δ K).decisionNodes =
      {[], [1], [1, 1], [0, 1, 1], [1, 0, 1, 1], [0, 1, 0, 1, 1], [1, 0, 1, 0, 1, 1], [1, 1, 0,
        1, 1], [1, 1, 1, 0, 1, 1], [1, 1, 1], [1, 1, 1, 1], [0, 1, 1, 1, 1], [1, 0, 1, 1, 1, 1],
        [1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1]} :=
  (by decide : (deterA 0 0 0 0 0).decisionNodes =
    {[], [1], [1, 1], [0, 1, 1], [1, 0, 1, 1], [0, 1, 0, 1, 1], [1, 0, 1, 0, 1, 1], [1, 1, 0, 1,
      1], [1, 1, 1, 0, 1, 1], [1, 1, 1], [1, 1, 1, 1], [0, 1, 1, 1, 1], [1, 0, 1, 1, 1, 1], [1,
      1, 1, 1, 1], [1, 1, 1, 1, 1, 1]})

theorem dtA_noNature (x y z δ K : ℝ) (k : Fin 15) : (deterA x y z δ K).player k ≠ none := by
  simp only [deterA]
  split_ifs <;> simp

theorem dtA_perfectInformation (x y z δ K : ℝ) : (deterA x y z δ K).PerfectInformation := by
  unfold ExtensiveForm.PerfectInformation
  change ∀ l ∈ dtNodesA, ∀ l' ∈ dtNodesA, (∃ b, b :: l ∈ dtNodesA) →
    (∃ b, b :: l' ∈ dtNodesA) → dtInfoA l = dtInfoA l' → l = l'
  decide

/-- Continuation payoffs of sure moves `c` in the game of Exercise 9.B.14(a): the payoff at the
terminal node reached by following `c`. -/
theorem dtA_cont (x y z δ K : ℝ) (c : Fin 15 → Fin 2) {l : List (Fin 2)}
    (hl : l ∈ dtNodesA) (i : Fin 2) :
    cont (deterA x y z δ K) (fun k => dirac (c k)) l i =
      (deterA x y z δ K).payoff i ((bstep (deterA x y z δ K) c)^[7] l) :=
  cont_dirac_play (deterA x y z δ K) (fun _ => Finset.mem_univ _)
    (fun l hl => (by decide : ∀ l ∈ dtNodesA, l.length ≤ 7) l hl) hl i

theorem dtA_step (x y z δ K : ℝ) (c : Fin 15 → Fin 2) :
    bstep (deterA x y z δ K) c = dtStepA c := rfl

/-- The nodes of the game of Exercise 9.B.14(b). -/
def dtNodesB : Finset (List (Fin 2)) :=
  {[], [0], [1], [0, 1], [1, 1], [0, 1, 1], [1, 1, 1], [0, 1, 1, 1], [1, 1, 1, 1],
    [0, 1, 1, 1, 1], [1, 1, 1, 1, 1], [0, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1],
    [0, 1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1, 1]}

/-- The information sets (one per decision node) of the game of Exercise 9.B.14(b): E's
nodes first. -/
def dtInfoB (l : List (Fin 2)) : Fin 7 :=
  if l = [1] then 1 else if l = [1, 1, 1] then 2 else if l = [1, 1, 1, 1, 1] then 3 else
  if l = [1, 1] then 4 else if l = [1, 1, 1, 1] then 5 else if l = [1, 1, 1, 1, 1, 1] then 6 else
  0

/-- The payoffs `(u_E, u_I)` of the game of Exercise 9.B.14(b). -/
def dtPayB (x y z δ K : ℝ) (i : Fin 2) (l : List (Fin 2)) : ℝ :=
  if l = [0] then
    (if i = 0 then 0 else x + δ * x + δ ^ 2 * x)
  else if l = [0, 1] then
    (if i = 0 then -K else x + δ * x + δ ^ 2 * x)
  else if l = [0, 1, 1] then
    (if i = 0 then -K - 1 else y + δ * x + δ ^ 2 * x)
  else if l = [0, 1, 1, 1] then
    (if i = 0 then -K + 1 else z + δ * x + δ ^ 2 * x)
  else if l = [0, 1, 1, 1, 1] then
    (if i = 0 then -K + 1 - δ else z + δ * y + δ ^ 2 * x)
  else if l = [0, 1, 1, 1, 1, 1] then
    (if i = 0 then -K + 1 + δ else z + δ * z + δ ^ 2 * x)
  else if l = [0, 1, 1, 1, 1, 1, 1] then
    (if i = 0 then -K + 1 + δ - δ ^ 2 else z + δ * z + δ ^ 2 * y)
  else if l = [1, 1, 1, 1, 1, 1, 1] then
    (if i = 0 then -K + 1 + δ + δ ^ 2 else z + δ * z + δ ^ 2 * z)
  else 0

/-- **Exercise 9.B.14(b)** (MWG, pp. 303-304). -/
def deterB (x y z δ K : ℝ) : ExtensiveForm (Fin 2) (Fin 2) (Fin 7) where
  nodes := dtNodesB
  nil_mem := by decide
  tail_mem := by decide
  info := dtInfoB
  avail _ := Finset.univ
  avail_spec := by decide
  info_surj := by decide
  player k := if (k : ℕ) < 4 then some 0 else some 1
  natureProb _ _ := 0
  nature_nonneg := fun k hk => absurd hk (by split_ifs <;> simp)
  nature_zero := fun k hk => absurd hk (by split_ifs <;> simp)
  nature_sum := fun k hk => absurd hk (by split_ifs <;> simp)
  payoff := dtPayB x y z δ K

/-- One step of play with sure moves `c` in the game of Exercise 9.B.14(b). -/
def dtStepB (c : Fin 7 → Fin 2) : List (Fin 2) → List (Fin 2) :=
  bstep (deterB 0 0 0 0 0) c

theorem dtB_decisionNodes (x y z δ K : ℝ) :
    (deterB x y z δ K).decisionNodes =
      {[], [1], [1, 1], [1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1]} :=
  (by decide : (deterB 0 0 0 0 0).decisionNodes =
    {[], [1], [1, 1], [1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1]})

theorem dtB_noNature (x y z δ K : ℝ) (k : Fin 7) : (deterB x y z δ K).player k ≠ none := by
  simp only [deterB]
  split_ifs <;> simp

theorem dtB_perfectInformation (x y z δ K : ℝ) : (deterB x y z δ K).PerfectInformation := by
  unfold ExtensiveForm.PerfectInformation
  change ∀ l ∈ dtNodesB, ∀ l' ∈ dtNodesB, (∃ b, b :: l ∈ dtNodesB) →
    (∃ b, b :: l' ∈ dtNodesB) → dtInfoB l = dtInfoB l' → l = l'
  decide

/-- Continuation payoffs of sure moves `c` in the game of Exercise 9.B.14(b): the payoff at the
terminal node reached by following `c`. -/
theorem dtB_cont (x y z δ K : ℝ) (c : Fin 7 → Fin 2) {l : List (Fin 2)}
    (hl : l ∈ dtNodesB) (i : Fin 2) :
    cont (deterB x y z δ K) (fun k => dirac (c k)) l i =
      (deterB x y z δ K).payoff i ((bstep (deterB x y z δ K) c)^[7] l) :=
  cont_dirac_play (deterB x y z δ K) (fun _ => Finset.mem_univ _)
    (fun l hl => (by decide : ∀ l ∈ dtNodesB, l.length ≤ 7) l hl) hl i

theorem dtB_step (x y z δ K : ℝ) (c : Fin 7 → Fin 2) :
    bstep (deterB x y z δ K) c = dtStepB c := rfl


/-- The backward-induction moves in Exercise 9.B.14(a): enter, stay and accommodate
everywhere. -/
def cA : Fin 15 → Fin 2 := fun _ => 1

/-- In the game of Exercise 9.B.14(a), at every decision node the mover strictly prefers the
move of `cA` given the continuation play of `cA`. -/
theorem dtA_strict (x y z δ K : ℝ) (hδ : 0 < δ) (hzy : y < z) (hK : K < 1 + δ) :
    ∀ l, (deterA x y z δ K).IsDecision l → ([] : List (Fin 2)) <:+ l → ∀ j,
      (deterA x y z δ K).player ((deterA x y z δ K).info l) = some j →
      ∀ a ∈ (deterA x y z δ K).avail ((deterA x y z δ K).info l),
        a ≠ cA ((deterA x y z δ K).info l) →
        cont (deterA x y z δ K) (fun k => dirac (cA k)) (a :: l) j <
          cont (deterA x y z δ K) (fun k => dirac (cA k))
            (cA ((deterA x y z δ K).info l) :: l) j := by
  intro l hl _ j hj a _ hne
  have hl' := (mem_decisionNodes (deterA x y z δ K)).2 hl
  rw [dtA_decisionNodes] at hl'
  simp only [Finset.mem_insert, Finset.mem_singleton] at hl'
  rcases hl' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · -- node []
    obtain rfl : j = 0 := Option.some.inj (hj.symm.trans rfl)
    rcases (by decide : ∀ k : Fin 2, k = 0 ∨ k = 1) a with rfl | rfl
    · change cont (deterA x y z δ K) (fun k => dirac (cA k)) [0] 0 <
          cont (deterA x y z δ K) (fun k => dirac (cA k)) [1] 0
      rw [dtA_cont x y z δ K _ (by decide), dtA_cont x y z δ K _ (by decide), dtA_step,
        (by decide : (dtStepA cA)^[7] [0] = [0]),
        (by decide : (dtStepA cA)^[7] [1] = [1, 1, 1, 1, 1, 1, 1])]
      rw [show (deterA x y z δ K).payoff 0 [0] = 0 from rfl,
        show (deterA x y z δ K).payoff 0 [1, 1, 1, 1, 1, 1, 1] = -K + 1 + δ + δ ^ 2 from rfl]
      nlinarith [mul_pos hδ hδ, mul_lt_mul_of_pos_left hzy hδ,
        mul_lt_mul_of_pos_left hzy (mul_pos hδ hδ)]
    · exact absurd rfl hne
  · -- node [1]
    obtain rfl : j = 0 := Option.some.inj (hj.symm.trans rfl)
    rcases (by decide : ∀ k : Fin 2, k = 0 ∨ k = 1) a with rfl | rfl
    · change cont (deterA x y z δ K) (fun k => dirac (cA k)) [0, 1] 0 <
          cont (deterA x y z δ K) (fun k => dirac (cA k)) [1, 1] 0
      rw [dtA_cont x y z δ K _ (by decide), dtA_cont x y z δ K _ (by decide), dtA_step,
        (by decide : (dtStepA cA)^[7] [0, 1] = [0, 1]),
        (by decide : (dtStepA cA)^[7] [1, 1] = [1, 1, 1, 1, 1, 1, 1])]
      rw [show (deterA x y z δ K).payoff 0 [0, 1] = -K from rfl,
        show (deterA x y z δ K).payoff 0 [1, 1, 1, 1, 1, 1, 1] = -K + 1 + δ + δ ^ 2 from rfl]
      nlinarith [mul_pos hδ hδ, mul_lt_mul_of_pos_left hzy hδ,
        mul_lt_mul_of_pos_left hzy (mul_pos hδ hδ)]
    · exact absurd rfl hne
  · -- node [1, 1]
    obtain rfl : j = 1 := Option.some.inj (hj.symm.trans rfl)
    rcases (by decide : ∀ k : Fin 2, k = 0 ∨ k = 1) a with rfl | rfl
    · change cont (deterA x y z δ K) (fun k => dirac (cA k)) [0, 1, 1] 1 <
          cont (deterA x y z δ K) (fun k => dirac (cA k)) [1, 1, 1] 1
      rw [dtA_cont x y z δ K _ (by decide), dtA_cont x y z δ K _ (by decide), dtA_step,
        (by decide : (dtStepA cA)^[7] [0, 1, 1] = [1, 1, 1, 1, 0, 1, 1]),
        (by decide : (dtStepA cA)^[7] [1, 1, 1] = [1, 1, 1, 1, 1, 1, 1])]
      rw [show (deterA x y z δ K).payoff 1 [1, 1, 1, 1, 0, 1, 1] = y + δ * z + δ ^ 2 * z from rfl,
        show (deterA x y z δ K).payoff 1 [1, 1, 1, 1, 1, 1, 1] = z + δ * z + δ ^ 2 * z from rfl]
      nlinarith [mul_pos hδ hδ, mul_lt_mul_of_pos_left hzy hδ,
        mul_lt_mul_of_pos_left hzy (mul_pos hδ hδ)]
    · exact absurd rfl hne
  · -- node [0, 1, 1]
    obtain rfl : j = 0 := Option.some.inj (hj.symm.trans rfl)
    rcases (by decide : ∀ k : Fin 2, k = 0 ∨ k = 1) a with rfl | rfl
    · change cont (deterA x y z δ K) (fun k => dirac (cA k)) [0, 0, 1, 1] 0 <
          cont (deterA x y z δ K) (fun k => dirac (cA k)) [1, 0, 1, 1] 0
      rw [dtA_cont x y z δ K _ (by decide), dtA_cont x y z δ K _ (by decide), dtA_step,
        (by decide : (dtStepA cA)^[7] [0, 0, 1, 1] = [0, 0, 1, 1]),
        (by decide : (dtStepA cA)^[7] [1, 0, 1, 1] = [1, 1, 1, 1, 0, 1, 1])]
      rw [show (deterA x y z δ K).payoff 0 [0, 0, 1, 1] = -K - 1 from rfl,
        show (deterA x y z δ K).payoff 0 [1, 1, 1, 1, 0, 1, 1] = -K - 1 + δ + δ ^ 2 from rfl]
      nlinarith [mul_pos hδ hδ, mul_lt_mul_of_pos_left hzy hδ,
        mul_lt_mul_of_pos_left hzy (mul_pos hδ hδ)]
    · exact absurd rfl hne
  · -- node [1, 0, 1, 1]
    obtain rfl : j = 1 := Option.some.inj (hj.symm.trans rfl)
    rcases (by decide : ∀ k : Fin 2, k = 0 ∨ k = 1) a with rfl | rfl
    · change cont (deterA x y z δ K) (fun k => dirac (cA k)) [0, 1, 0, 1, 1] 1 <
          cont (deterA x y z δ K) (fun k => dirac (cA k)) [1, 1, 0, 1, 1] 1
      rw [dtA_cont x y z δ K _ (by decide), dtA_cont x y z δ K _ (by decide), dtA_step,
        (by decide : (dtStepA cA)^[7] [0, 1, 0, 1, 1] = [1, 1, 0, 1, 0, 1, 1]),
        (by decide : (dtStepA cA)^[7] [1, 1, 0, 1, 1] = [1, 1, 1, 1, 0, 1, 1])]
      rw [show (deterA x y z δ K).payoff 1 [1, 1, 0, 1, 0, 1, 1] = y + δ * y + δ ^ 2 * z from rfl,
        show (deterA x y z δ K).payoff 1 [1, 1, 1, 1, 0, 1, 1] = y + δ * z + δ ^ 2 * z from rfl]
      nlinarith [mul_pos hδ hδ, mul_lt_mul_of_pos_left hzy hδ,
        mul_lt_mul_of_pos_left hzy (mul_pos hδ hδ)]
    · exact absurd rfl hne
  · -- node [0, 1, 0, 1, 1]
    obtain rfl : j = 0 := Option.some.inj (hj.symm.trans rfl)
    rcases (by decide : ∀ k : Fin 2, k = 0 ∨ k = 1) a with rfl | rfl
    · change cont (deterA x y z δ K) (fun k => dirac (cA k)) [0, 0, 1, 0, 1, 1] 0 <
          cont (deterA x y z δ K) (fun k => dirac (cA k)) [1, 0, 1, 0, 1, 1] 0
      rw [dtA_cont x y z δ K _ (by decide), dtA_cont x y z δ K _ (by decide), dtA_step,
        (by decide : (dtStepA cA)^[7] [0, 0, 1, 0, 1, 1] = [0, 0, 1, 0, 1, 1]),
        (by decide : (dtStepA cA)^[7] [1, 0, 1, 0, 1, 1] = [1, 1, 0, 1, 0, 1, 1])]
      rw [show (deterA x y z δ K).payoff 0 [0, 0, 1, 0, 1, 1] = -K - 1 - δ from rfl,
        show (deterA x y z δ K).payoff 0 [1, 1, 0, 1, 0, 1, 1] = -K - 1 - δ + δ ^ 2 from rfl]
      nlinarith [mul_pos hδ hδ, mul_lt_mul_of_pos_left hzy hδ,
        mul_lt_mul_of_pos_left hzy (mul_pos hδ hδ)]
    · exact absurd rfl hne
  · -- node [1, 0, 1, 0, 1, 1]
    obtain rfl : j = 1 := Option.some.inj (hj.symm.trans rfl)
    rcases (by decide : ∀ k : Fin 2, k = 0 ∨ k = 1) a with rfl | rfl
    · change cont (deterA x y z δ K) (fun k => dirac (cA k)) [0, 1, 0, 1, 0, 1, 1] 1 <
          cont (deterA x y z δ K) (fun k => dirac (cA k)) [1, 1, 0, 1, 0, 1, 1] 1
      rw [dtA_cont x y z δ K _ (by decide), dtA_cont x y z δ K _ (by decide), dtA_step,
        (by decide : (dtStepA cA)^[7] [0, 1, 0, 1, 0, 1, 1] = [0, 1, 0, 1, 0, 1, 1]),
        (by decide : (dtStepA cA)^[7] [1, 1, 0, 1, 0, 1, 1] = [1, 1, 0, 1, 0, 1, 1])]
      rw [show (deterA x y z δ K).payoff 1 [0, 1, 0, 1, 0, 1, 1] = y + δ * y + δ ^ 2 * y from rfl,
        show (deterA x y z δ K).payoff 1 [1, 1, 0, 1, 0, 1, 1] = y + δ * y + δ ^ 2 * z from rfl]
      nlinarith [mul_pos hδ hδ, mul_lt_mul_of_pos_left hzy hδ,
        mul_lt_mul_of_pos_left hzy (mul_pos hδ hδ)]
    · exact absurd rfl hne
  · -- node [1, 1, 0, 1, 1]
    obtain rfl : j = 0 := Option.some.inj (hj.symm.trans rfl)
    rcases (by decide : ∀ k : Fin 2, k = 0 ∨ k = 1) a with rfl | rfl
    · change cont (deterA x y z δ K) (fun k => dirac (cA k)) [0, 1, 1, 0, 1, 1] 0 <
          cont (deterA x y z δ K) (fun k => dirac (cA k)) [1, 1, 1, 0, 1, 1] 0
      rw [dtA_cont x y z δ K _ (by decide), dtA_cont x y z δ K _ (by decide), dtA_step,
        (by decide : (dtStepA cA)^[7] [0, 1, 1, 0, 1, 1] = [0, 1, 1, 0, 1, 1]),
        (by decide : (dtStepA cA)^[7] [1, 1, 1, 0, 1, 1] = [1, 1, 1, 1, 0, 1, 1])]
      rw [show (deterA x y z δ K).payoff 0 [0, 1, 1, 0, 1, 1] = -K - 1 + δ from rfl,
        show (deterA x y z δ K).payoff 0 [1, 1, 1, 1, 0, 1, 1] = -K - 1 + δ + δ ^ 2 from rfl]
      nlinarith [mul_pos hδ hδ, mul_lt_mul_of_pos_left hzy hδ,
        mul_lt_mul_of_pos_left hzy (mul_pos hδ hδ)]
    · exact absurd rfl hne
  · -- node [1, 1, 1, 0, 1, 1]
    obtain rfl : j = 1 := Option.some.inj (hj.symm.trans rfl)
    rcases (by decide : ∀ k : Fin 2, k = 0 ∨ k = 1) a with rfl | rfl
    · change cont (deterA x y z δ K) (fun k => dirac (cA k)) [0, 1, 1, 1, 0, 1, 1] 1 <
          cont (deterA x y z δ K) (fun k => dirac (cA k)) [1, 1, 1, 1, 0, 1, 1] 1
      rw [dtA_cont x y z δ K _ (by decide), dtA_cont x y z δ K _ (by decide), dtA_step,
        (by decide : (dtStepA cA)^[7] [0, 1, 1, 1, 0, 1, 1] = [0, 1, 1, 1, 0, 1, 1]),
        (by decide : (dtStepA cA)^[7] [1, 1, 1, 1, 0, 1, 1] = [1, 1, 1, 1, 0, 1, 1])]
      rw [show (deterA x y z δ K).payoff 1 [0, 1, 1, 1, 0, 1, 1] = y + δ * z + δ ^ 2 * y from rfl,
        show (deterA x y z δ K).payoff 1 [1, 1, 1, 1, 0, 1, 1] = y + δ * z + δ ^ 2 * z from rfl]
      nlinarith [mul_pos hδ hδ, mul_lt_mul_of_pos_left hzy hδ,
        mul_lt_mul_of_pos_left hzy (mul_pos hδ hδ)]
    · exact absurd rfl hne
  · -- node [1, 1, 1]
    obtain rfl : j = 0 := Option.some.inj (hj.symm.trans rfl)
    rcases (by decide : ∀ k : Fin 2, k = 0 ∨ k = 1) a with rfl | rfl
    · change cont (deterA x y z δ K) (fun k => dirac (cA k)) [0, 1, 1, 1] 0 <
          cont (deterA x y z δ K) (fun k => dirac (cA k)) [1, 1, 1, 1] 0
      rw [dtA_cont x y z δ K _ (by decide), dtA_cont x y z δ K _ (by decide), dtA_step,
        (by decide : (dtStepA cA)^[7] [0, 1, 1, 1] = [0, 1, 1, 1]),
        (by decide : (dtStepA cA)^[7] [1, 1, 1, 1] = [1, 1, 1, 1, 1, 1, 1])]
      rw [show (deterA x y z δ K).payoff 0 [0, 1, 1, 1] = -K + 1 from rfl,
        show (deterA x y z δ K).payoff 0 [1, 1, 1, 1, 1, 1, 1] = -K + 1 + δ + δ ^ 2 from rfl]
      nlinarith [mul_pos hδ hδ, mul_lt_mul_of_pos_left hzy hδ,
        mul_lt_mul_of_pos_left hzy (mul_pos hδ hδ)]
    · exact absurd rfl hne
  · -- node [1, 1, 1, 1]
    obtain rfl : j = 1 := Option.some.inj (hj.symm.trans rfl)
    rcases (by decide : ∀ k : Fin 2, k = 0 ∨ k = 1) a with rfl | rfl
    · change cont (deterA x y z δ K) (fun k => dirac (cA k)) [0, 1, 1, 1, 1] 1 <
          cont (deterA x y z δ K) (fun k => dirac (cA k)) [1, 1, 1, 1, 1] 1
      rw [dtA_cont x y z δ K _ (by decide), dtA_cont x y z δ K _ (by decide), dtA_step,
        (by decide : (dtStepA cA)^[7] [0, 1, 1, 1, 1] = [1, 1, 0, 1, 1, 1, 1]),
        (by decide : (dtStepA cA)^[7] [1, 1, 1, 1, 1] = [1, 1, 1, 1, 1, 1, 1])]
      rw [show (deterA x y z δ K).payoff 1 [1, 1, 0, 1, 1, 1, 1] = z + δ * y + δ ^ 2 * z from rfl,
        show (deterA x y z δ K).payoff 1 [1, 1, 1, 1, 1, 1, 1] = z + δ * z + δ ^ 2 * z from rfl]
      nlinarith [mul_pos hδ hδ, mul_lt_mul_of_pos_left hzy hδ,
        mul_lt_mul_of_pos_left hzy (mul_pos hδ hδ)]
    · exact absurd rfl hne
  · -- node [0, 1, 1, 1, 1]
    obtain rfl : j = 0 := Option.some.inj (hj.symm.trans rfl)
    rcases (by decide : ∀ k : Fin 2, k = 0 ∨ k = 1) a with rfl | rfl
    · change cont (deterA x y z δ K) (fun k => dirac (cA k)) [0, 0, 1, 1, 1, 1] 0 <
          cont (deterA x y z δ K) (fun k => dirac (cA k)) [1, 0, 1, 1, 1, 1] 0
      rw [dtA_cont x y z δ K _ (by decide), dtA_cont x y z δ K _ (by decide), dtA_step,
        (by decide : (dtStepA cA)^[7] [0, 0, 1, 1, 1, 1] = [0, 0, 1, 1, 1, 1]),
        (by decide : (dtStepA cA)^[7] [1, 0, 1, 1, 1, 1] = [1, 1, 0, 1, 1, 1, 1])]
      rw [show (deterA x y z δ K).payoff 0 [0, 0, 1, 1, 1, 1] = -K + 1 - δ from rfl,
        show (deterA x y z δ K).payoff 0 [1, 1, 0, 1, 1, 1, 1] = -K + 1 - δ + δ ^ 2 from rfl]
      nlinarith [mul_pos hδ hδ, mul_lt_mul_of_pos_left hzy hδ,
        mul_lt_mul_of_pos_left hzy (mul_pos hδ hδ)]
    · exact absurd rfl hne
  · -- node [1, 0, 1, 1, 1, 1]
    obtain rfl : j = 1 := Option.some.inj (hj.symm.trans rfl)
    rcases (by decide : ∀ k : Fin 2, k = 0 ∨ k = 1) a with rfl | rfl
    · change cont (deterA x y z δ K) (fun k => dirac (cA k)) [0, 1, 0, 1, 1, 1, 1] 1 <
          cont (deterA x y z δ K) (fun k => dirac (cA k)) [1, 1, 0, 1, 1, 1, 1] 1
      rw [dtA_cont x y z δ K _ (by decide), dtA_cont x y z δ K _ (by decide), dtA_step,
        (by decide : (dtStepA cA)^[7] [0, 1, 0, 1, 1, 1, 1] = [0, 1, 0, 1, 1, 1, 1]),
        (by decide : (dtStepA cA)^[7] [1, 1, 0, 1, 1, 1, 1] = [1, 1, 0, 1, 1, 1, 1])]
      rw [show (deterA x y z δ K).payoff 1 [0, 1, 0, 1, 1, 1, 1] = z + δ * y + δ ^ 2 * y from rfl,
        show (deterA x y z δ K).payoff 1 [1, 1, 0, 1, 1, 1, 1] = z + δ * y + δ ^ 2 * z from rfl]
      nlinarith [mul_pos hδ hδ, mul_lt_mul_of_pos_left hzy hδ,
        mul_lt_mul_of_pos_left hzy (mul_pos hδ hδ)]
    · exact absurd rfl hne
  · -- node [1, 1, 1, 1, 1]
    obtain rfl : j = 0 := Option.some.inj (hj.symm.trans rfl)
    rcases (by decide : ∀ k : Fin 2, k = 0 ∨ k = 1) a with rfl | rfl
    · change cont (deterA x y z δ K) (fun k => dirac (cA k)) [0, 1, 1, 1, 1, 1] 0 <
          cont (deterA x y z δ K) (fun k => dirac (cA k)) [1, 1, 1, 1, 1, 1] 0
      rw [dtA_cont x y z δ K _ (by decide), dtA_cont x y z δ K _ (by decide), dtA_step,
        (by decide : (dtStepA cA)^[7] [0, 1, 1, 1, 1, 1] = [0, 1, 1, 1, 1, 1]),
        (by decide : (dtStepA cA)^[7] [1, 1, 1, 1, 1, 1] = [1, 1, 1, 1, 1, 1, 1])]
      rw [show (deterA x y z δ K).payoff 0 [0, 1, 1, 1, 1, 1] = -K + 1 + δ from rfl,
        show (deterA x y z δ K).payoff 0 [1, 1, 1, 1, 1, 1, 1] = -K + 1 + δ + δ ^ 2 from rfl]
      nlinarith [mul_pos hδ hδ, mul_lt_mul_of_pos_left hzy hδ,
        mul_lt_mul_of_pos_left hzy (mul_pos hδ hδ)]
    · exact absurd rfl hne
  · -- node [1, 1, 1, 1, 1, 1]
    obtain rfl : j = 1 := Option.some.inj (hj.symm.trans rfl)
    rcases (by decide : ∀ k : Fin 2, k = 0 ∨ k = 1) a with rfl | rfl
    · change cont (deterA x y z δ K) (fun k => dirac (cA k)) [0, 1, 1, 1, 1, 1, 1] 1 <
          cont (deterA x y z δ K) (fun k => dirac (cA k)) [1, 1, 1, 1, 1, 1, 1] 1
      rw [dtA_cont x y z δ K _ (by decide), dtA_cont x y z δ K _ (by decide), dtA_step,
        (by decide : (dtStepA cA)^[7] [0, 1, 1, 1, 1, 1, 1] = [0, 1, 1, 1, 1, 1, 1]),
        (by decide : (dtStepA cA)^[7] [1, 1, 1, 1, 1, 1, 1] = [1, 1, 1, 1, 1, 1, 1])]
      rw [show (deterA x y z δ K).payoff 1 [0, 1, 1, 1, 1, 1, 1] = z + δ * z + δ ^ 2 * y from rfl,
        show (deterA x y z δ K).payoff 1 [1, 1, 1, 1, 1, 1, 1] = z + δ * z + δ ^ 2 * z from rfl]
      nlinarith [mul_pos hδ hδ, mul_lt_mul_of_pos_left hzy hδ,
        mul_lt_mul_of_pos_left hzy (mul_pos hδ hδ)]
    · exact absurd rfl hne


/-- The backward-induction moves in Exercise 9.B.14(b), with entry decision `e`: stay in
periods 0 and 2, exit in period 1; accommodate in periods 0 and 2, fight in period 1. -/
def cB (e : Fin 2) : Fin 7 → Fin 2 := ![e, 1, 0, 1, 1, 0, 1]

/-- In the game of Exercise 9.B.14(b), at every decision node after entry the mover strictly
prefers the move of `cB e` given the continuation play of `cB e`. -/
theorem dtB_strict (x y z δ K : ℝ) (hδ : 0 < δ) (hzy : y < z) (hA2 : (1 + δ) * z < y + δ * x)
    (e : Fin 2) :
    ∀ l, (deterB x y z δ K).IsDecision l → ([1] : List (Fin 2)) <:+ l → ∀ j,
      (deterB x y z δ K).player ((deterB x y z δ K).info l) = some j →
      ∀ a ∈ (deterB x y z δ K).avail ((deterB x y z δ K).info l),
        a ≠ cB e ((deterB x y z δ K).info l) →
        cont (deterB x y z δ K) (fun k => dirac (cB e k)) (a :: l) j <
          cont (deterB x y z δ K) (fun k => dirac (cB e k))
            (cB e ((deterB x y z δ K).info l) :: l) j := by
  intro l hl hx₀ j hj a _ hne
  have hl' := (mem_decisionNodes (deterB x y z δ K)).2 hl
  rw [dtB_decisionNodes] at hl'
  simp only [Finset.mem_insert, Finset.mem_singleton] at hl'
  rcases hl' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- node []
    exact absurd hx₀ (by decide)
  · -- node [1]
    obtain rfl : j = 0 := Option.some.inj (hj.symm.trans rfl)
    rcases (by decide : ∀ k : Fin 2, k = 0 ∨ k = 1) a with rfl | rfl
    · change cont (deterB x y z δ K) (fun k => dirac (cB e k)) [0, 1] 0 <
          cont (deterB x y z δ K) (fun k => dirac (cB e k)) [1, 1] 0
      rw [dtB_cont x y z δ K _ (by decide), dtB_cont x y z δ K _ (by decide), dtB_step,
        (by decide : ∀ e : Fin 2, (dtStepB (cB e))^[7] [0, 1] = [0, 1]) e,
        (by decide : ∀ e : Fin 2, (dtStepB (cB e))^[7] [1, 1] = [0, 1, 1, 1]) e]
      rw [show (deterB x y z δ K).payoff 0 [0, 1] = -K from rfl,
        show (deterB x y z δ K).payoff 0 [0, 1, 1, 1] = -K + 1 from rfl]
      nlinarith [mul_pos hδ hδ, mul_lt_mul_of_pos_left hzy hδ,
        mul_lt_mul_of_pos_left hzy (mul_pos hδ hδ), mul_lt_mul_of_pos_left hA2 hδ]
    · exact absurd rfl hne
  · -- node [1, 1]
    obtain rfl : j = 1 := Option.some.inj (hj.symm.trans rfl)
    rcases (by decide : ∀ k : Fin 2, k = 0 ∨ k = 1) a with rfl | rfl
    · change cont (deterB x y z δ K) (fun k => dirac (cB e k)) [0, 1, 1] 1 <
          cont (deterB x y z δ K) (fun k => dirac (cB e k)) [1, 1, 1] 1
      rw [dtB_cont x y z δ K _ (by decide), dtB_cont x y z δ K _ (by decide), dtB_step,
        (by decide : ∀ e : Fin 2, (dtStepB (cB e))^[7] [0, 1, 1] = [0, 1, 1]) e,
        (by decide : ∀ e : Fin 2, (dtStepB (cB e))^[7] [1, 1, 1] = [0, 1, 1, 1]) e]
      rw [show (deterB x y z δ K).payoff 1 [0, 1, 1] = y + δ * x + δ ^ 2 * x from rfl,
        show (deterB x y z δ K).payoff 1 [0, 1, 1, 1] = z + δ * x + δ ^ 2 * x from rfl]
      nlinarith [mul_pos hδ hδ, mul_lt_mul_of_pos_left hzy hδ,
        mul_lt_mul_of_pos_left hzy (mul_pos hδ hδ), mul_lt_mul_of_pos_left hA2 hδ]
    · exact absurd rfl hne
  · -- node [1, 1, 1]
    obtain rfl : j = 0 := Option.some.inj (hj.symm.trans rfl)
    rcases (by decide : ∀ k : Fin 2, k = 0 ∨ k = 1) a with rfl | rfl
    · exact absurd rfl hne
    · change cont (deterB x y z δ K) (fun k => dirac (cB e k)) [1, 1, 1, 1] 0 <
          cont (deterB x y z δ K) (fun k => dirac (cB e k)) [0, 1, 1, 1] 0
      rw [dtB_cont x y z δ K _ (by decide), dtB_cont x y z δ K _ (by decide), dtB_step,
        (by decide : ∀ e : Fin 2, (dtStepB (cB e))^[7] [1, 1, 1, 1] = [0, 1, 1, 1, 1]) e,
        (by decide : ∀ e : Fin 2, (dtStepB (cB e))^[7] [0, 1, 1, 1] = [0, 1, 1, 1]) e]
      rw [show (deterB x y z δ K).payoff 0 [0, 1, 1, 1, 1] = -K + 1 - δ from rfl,
        show (deterB x y z δ K).payoff 0 [0, 1, 1, 1] = -K + 1 from rfl]
      nlinarith [mul_pos hδ hδ, mul_lt_mul_of_pos_left hzy hδ,
        mul_lt_mul_of_pos_left hzy (mul_pos hδ hδ), mul_lt_mul_of_pos_left hA2 hδ]
  · -- node [1, 1, 1, 1]
    obtain rfl : j = 1 := Option.some.inj (hj.symm.trans rfl)
    rcases (by decide : ∀ k : Fin 2, k = 0 ∨ k = 1) a with rfl | rfl
    · exact absurd rfl hne
    · change cont (deterB x y z δ K) (fun k => dirac (cB e k)) [1, 1, 1, 1, 1] 1 <
          cont (deterB x y z δ K) (fun k => dirac (cB e k)) [0, 1, 1, 1, 1] 1
      rw [dtB_cont x y z δ K _ (by decide), dtB_cont x y z δ K _ (by decide), dtB_step,
        (by decide : ∀ e : Fin 2, (dtStepB (cB e))^[7] [1, 1, 1, 1, 1] = [1, 1, 1, 1, 1, 1, 1]) e,
        (by decide : ∀ e : Fin 2, (dtStepB (cB e))^[7] [0, 1, 1, 1, 1] = [0, 1, 1, 1, 1]) e]
      rw [show (deterB x y z δ K).payoff 1 [1, 1, 1, 1, 1, 1, 1] = z + δ * z + δ ^ 2 * z from rfl,
        show (deterB x y z δ K).payoff 1 [0, 1, 1, 1, 1] = z + δ * y + δ ^ 2 * x from rfl]
      nlinarith [mul_pos hδ hδ, mul_lt_mul_of_pos_left hzy hδ,
        mul_lt_mul_of_pos_left hzy (mul_pos hδ hδ), mul_lt_mul_of_pos_left hA2 hδ]
  · -- node [1, 1, 1, 1, 1]
    obtain rfl : j = 0 := Option.some.inj (hj.symm.trans rfl)
    rcases (by decide : ∀ k : Fin 2, k = 0 ∨ k = 1) a with rfl | rfl
    · change cont (deterB x y z δ K) (fun k => dirac (cB e k)) [0, 1, 1, 1, 1, 1] 0 <
          cont (deterB x y z δ K) (fun k => dirac (cB e k)) [1, 1, 1, 1, 1, 1] 0
      rw [dtB_cont x y z δ K _ (by decide), dtB_cont x y z δ K _ (by decide), dtB_step,
        (by decide : ∀ e : Fin 2, (dtStepB (cB e))^[7] [0, 1, 1, 1, 1, 1] = [0, 1, 1, 1, 1, 1]) e,
        (by decide : ∀ e : Fin 2, (dtStepB (cB e))^[7] [1, 1, 1, 1, 1, 1] =
          [1, 1, 1, 1, 1, 1, 1]) e]
      rw [show (deterB x y z δ K).payoff 0 [0, 1, 1, 1, 1, 1] = -K + 1 + δ from rfl,
        show (deterB x y z δ K).payoff 0 [1, 1, 1, 1, 1, 1, 1] = -K + 1 + δ + δ ^ 2 from rfl]
      nlinarith [mul_pos hδ hδ, mul_lt_mul_of_pos_left hzy hδ,
        mul_lt_mul_of_pos_left hzy (mul_pos hδ hδ), mul_lt_mul_of_pos_left hA2 hδ]
    · exact absurd rfl hne
  · -- node [1, 1, 1, 1, 1, 1]
    obtain rfl : j = 1 := Option.some.inj (hj.symm.trans rfl)
    rcases (by decide : ∀ k : Fin 2, k = 0 ∨ k = 1) a with rfl | rfl
    · change cont (deterB x y z δ K) (fun k => dirac (cB e k)) [0, 1, 1, 1, 1, 1, 1] 1 <
          cont (deterB x y z δ K) (fun k => dirac (cB e k)) [1, 1, 1, 1, 1, 1, 1] 1
      rw [dtB_cont x y z δ K _ (by decide), dtB_cont x y z δ K _ (by decide), dtB_step,
        (by decide : ∀ e : Fin 2, (dtStepB (cB e))^[7] [0, 1, 1, 1, 1, 1, 1] =
          [0, 1, 1, 1, 1, 1, 1]) e,
        (by decide : ∀ e : Fin 2, (dtStepB (cB e))^[7] [1, 1, 1, 1, 1, 1, 1] =
          [1, 1, 1, 1, 1, 1, 1]) e]
      rw [show (deterB x y z δ K).payoff 1 [0, 1, 1, 1, 1, 1, 1] = z + δ * z + δ ^ 2 * y from rfl,
        show (deterB x y z δ K).payoff 1 [1, 1, 1, 1, 1, 1, 1] = z + δ * z + δ ^ 2 * z from rfl]
      nlinarith [mul_pos hδ hδ, mul_lt_mul_of_pos_left hzy hδ,
        mul_lt_mul_of_pos_left hzy (mul_pos hδ hδ), mul_lt_mul_of_pos_left hA2 hδ]
    · exact absurd rfl hne


/-- The value of entering in Exercise 9.B.14(b): `1 − K` (E stays in period 0, I accommodates,
E exits in period 1); staying out gives `0`. -/
theorem dtB_root (x y z δ K : ℝ) (e : Fin 2) :
    cont (deterB x y z δ K) (fun k => dirac (cB e k)) [1] 0 = -K + 1 ∧
      cont (deterB x y z δ K) (fun k => dirac (cB e k)) [0] 0 = 0 := by
  rw [dtB_cont x y z δ K _ (by decide), dtB_cont x y z δ K _ (by decide), dtB_step,
    (by decide : ∀ e : Fin 2, (dtStepB (cB e))^[7] [1] = [0, 1, 1, 1]) e,
    (by decide : ∀ e : Fin 2, (dtStepB (cB e))^[7] [0] = [0]) e]
  exact ⟨rfl, rfl⟩

theorem dtB_after_root : ∀ l ∈ dtNodesB, (∃ b, b :: l ∈ dtNodesB) → l ≠ [] →
    ([1] : List (Fin 2)) <:+ l := by
  decide

/-- **Exercise 9.B.14(a)** (MWG, pp. 303-304). Without the financial constraint, under (A.1)
(`z > y`) and (A.3) (`K < 1 + δ`), with `δ > 0`, the unique subgame perfect Nash equilibrium is:
E enters and stays in after every history; I accommodates after every history. (Every SPNE, in
behaviour strategies, plays these moves at every decision node.) -/
theorem exercise_9_B_14a (x y z δ K : ℝ) (hδ : 0 < δ) (hzy : y < z) (hK : K < 1 + δ) :
    IsSPNE (deterA x y z δ K) (pureMoves cA) ∧ ∀ F, IsSPNE (deterA x y z δ K) F →
      ∀ l, (deterA x y z δ K).IsDecision l →
        (deterA x y z δ K).assemble F ((deterA x y z δ K).info l) = dirac 1 := by
  have hs := dtA_strict x y z δ K hδ hzy hK
  refine ⟨isSPNE_of_weak_bi _ (dtA_noNature x y z δ K) (fun _ => Finset.mem_univ _)
    fun l hl j hj a ha => ?_, fun F hF l hl => ?_⟩
  · by_cases hac : a = cA ((deterA x y z δ K).info l)
    · rw [hac]
    · exact (hs l hl List.nil_suffix j hj a ha hac).le
  · exact eq_dirac_of_strict_bi _ (dtA_perfectInformation x y z δ K) (dtA_noNature x y z δ K)
      (fun _ => Finset.mem_univ _) hs hF l hl List.nil_suffix

/-- **Exercise 9.B.14(b)** (MWG, p. 304). With the financial constraint (a single fight forces E
out of the market), under (A.1) (`z > y`) and (A.2) (`y + δx > (1 + δ)z`), with `δ > 0`:
after entry the SPNE strategies are unique — E stays in period 0, exits in period 1 (if still
active) and stays in period 2; I accommodates in periods 0 and 2 and fights in period 1. Entry
depends on `K` beyond (A.3): if `K < 1` the unique SPNE has E entering (`cB 1`), if `K > 1` the
unique SPNE has E staying out (`cB 0`), and if `K = 1` both are SPNE. -/
theorem exercise_9_B_14b (x y z δ K : ℝ) (hδ : 0 < δ) (hzy : y < z)
    (hA2 : (1 + δ) * z < y + δ * x) :
    (∀ F, IsSPNE (deterB x y z δ K) F → ∀ e, ∀ l, (deterB x y z δ K).IsDecision l →
      ([1] : List (Fin 2)) <:+ l →
        (deterB x y z δ K).assemble F ((deterB x y z δ K).info l) =
          dirac (cB e ((deterB x y z δ K).info l))) ∧
    (K < 1 → IsSPNE (deterB x y z δ K) (pureMoves (cB 1)) ∧ ∀ F, IsSPNE (deterB x y z δ K) F →
      ∀ l, (deterB x y z δ K).IsDecision l →
        (deterB x y z δ K).assemble F ((deterB x y z δ K).info l) =
          dirac (cB 1 ((deterB x y z δ K).info l))) ∧
    (1 < K → IsSPNE (deterB x y z δ K) (pureMoves (cB 0)) ∧ ∀ F, IsSPNE (deterB x y z δ K) F →
      ∀ l, (deterB x y z δ K).IsDecision l →
        (deterB x y z δ K).assemble F ((deterB x y z δ K).info l) =
          dirac (cB 0 ((deterB x y z δ K).info l))) ∧
    (K = 1 → IsSPNE (deterB x y z δ K) (pureMoves (cB 1)) ∧
      IsSPNE (deterB x y z δ K) (pureMoves (cB 0))) := by
  have hPI := dtB_perfectInformation x y z δ K
  have hN := dtB_noNature x y z δ K
  have hc : ∀ e (k : Fin 7), cB e k ∈ (deterB x y z δ K).avail k := fun _ _ => Finset.mem_univ _
  -- strictness everywhere, given strictness at the root
  have hall : ∀ e, ((∀ a, a ≠ cB e 0 →
      cont (deterB x y z δ K) (fun k => dirac (cB e k)) [a] 0 <
        cont (deterB x y z δ K) (fun k => dirac (cB e k)) [cB e 0] 0)) →
      ∀ l, (deterB x y z δ K).IsDecision l → ([] : List (Fin 2)) <:+ l → ∀ j,
        (deterB x y z δ K).player ((deterB x y z δ K).info l) = some j →
        ∀ a ∈ (deterB x y z δ K).avail ((deterB x y z δ K).info l),
          a ≠ cB e ((deterB x y z δ K).info l) →
          cont (deterB x y z δ K) (fun k => dirac (cB e k)) (a :: l) j <
            cont (deterB x y z δ K) (fun k => dirac (cB e k))
              (cB e ((deterB x y z δ K).info l) :: l) j := by
    intro e hroot l hl _ j hj a ha hne
    by_cases hl0 : l = []
    · subst hl0
      obtain rfl : j = 0 := Option.some.inj (hj.symm.trans rfl)
      exact hroot a hne
    · exact dtB_strict x y z δ K hδ hzy hA2 e l hl (dtB_after_root l hl.1 hl.2 hl0) j hj a ha hne
  -- weak optimality everywhere, given weak optimality at the root
  have hweak : ∀ e, ((∀ a,
      cont (deterB x y z δ K) (fun k => dirac (cB e k)) [a] 0 ≤
        cont (deterB x y z δ K) (fun k => dirac (cB e k)) [cB e 0] 0)) →
      IsSPNE (deterB x y z δ K) (pureMoves (cB e)) := by
    intro e hroot
    refine isSPNE_of_weak_bi _ hN (hc e) fun l hl j hj a ha => ?_
    by_cases hac : a = cB e ((deterB x y z δ K).info l)
    · rw [hac]
    · by_cases hl0 : l = []
      · subst hl0
        obtain rfl : j = 0 := Option.some.inj (hj.symm.trans rfl)
        exact hroot a
      · exact (dtB_strict x y z δ K hδ hzy hA2 e l hl (dtB_after_root l hl.1 hl.2 hl0) j hj a ha
          hac).le
  have h2 : ∀ k : Fin 2, k = 0 ∨ k = 1 := by decide
  refine ⟨fun F hF e l hl hl1 => eq_dirac_of_strict_bi _ hPI hN (hc e)
      (dtB_strict x y z δ K hδ hzy hA2 e) hF l hl hl1, fun hK => ?_, fun hK => ?_, fun hK => ?_⟩
  · have hroot : ∀ a, a ≠ cB 1 0 → cont (deterB x y z δ K) (fun k => dirac (cB 1 k)) [a] 0 <
        cont (deterB x y z δ K) (fun k => dirac (cB 1 k)) [cB 1 0] 0 := by
      intro a hne
      rcases h2 a with rfl | rfl
      · change cont (deterB x y z δ K) (fun k => dirac (cB 1 k)) [0] 0 <
          cont (deterB x y z δ K) (fun k => dirac (cB 1 k)) [1] 0
        rw [(dtB_root x y z δ K 1).1, (dtB_root x y z δ K 1).2]
        linarith
      · exact absurd rfl hne
    refine ⟨hweak 1 fun a => ?_, fun F hF l hl => eq_dirac_of_strict_bi _ hPI hN (hc 1)
      (hall 1 hroot) hF l hl List.nil_suffix⟩
    by_cases hae : a = cB 1 0
    · rw [hae]
    · exact (hroot a hae).le
  · have hroot : ∀ a, a ≠ cB 0 0 → cont (deterB x y z δ K) (fun k => dirac (cB 0 k)) [a] 0 <
        cont (deterB x y z δ K) (fun k => dirac (cB 0 k)) [cB 0 0] 0 := by
      intro a hne
      rcases h2 a with rfl | rfl
      · exact absurd rfl hne
      · change cont (deterB x y z δ K) (fun k => dirac (cB 0 k)) [1] 0 <
          cont (deterB x y z δ K) (fun k => dirac (cB 0 k)) [0] 0
        rw [(dtB_root x y z δ K 0).1, (dtB_root x y z δ K 0).2]
        linarith
    refine ⟨hweak 0 fun a => ?_, fun F hF l hl => eq_dirac_of_strict_bi _ hPI hN (hc 0)
      (hall 0 hroot) hF l hl List.nil_suffix⟩
    by_cases hae : a = cB 0 0
    · rw [hae]
    · exact (hroot a hae).le
  · refine ⟨hweak 1 fun a => ?_, hweak 0 fun a => ?_⟩ <;> rcases h2 a with rfl | rfl
    · change cont (deterB x y z δ K) (fun k => dirac (cB 1 k)) [0] 0 ≤
        cont (deterB x y z δ K) (fun k => dirac (cB 1 k)) [1] 0
      rw [(dtB_root x y z δ K 1).1, (dtB_root x y z δ K 1).2]
      linarith
    · exact le_rfl
    · exact le_rfl
    · change cont (deterB x y z δ K) (fun k => dirac (cB 0 k)) [1] 0 ≤
        cont (deterB x y z δ K) (fun k => dirac (cB 0 k)) [0] 0
      rw [(dtB_root x y z δ K 0).1, (dtB_root x y z δ K 0).2]
      linarith

/-- **Exercise 9.B.14, an instance** (MWG, p. 304). `(x, z, y, δ) = (4, 1, 0, 1/2)` satisfies
(A.1)-(A.3) with `K = 1/2` and with `K = 5/4`; with `K = 1/2` the unique SPNE of (b) has E
entering, with `K = 5/4` it has E staying out, and in (a) E enters for both values. -/
theorem exercise_9_B_14_instance :
    ((4 : ℝ) > 1 ∧ (1 : ℝ) > 0 ∧ (0 : ℝ) + 1 / 2 * 4 > (1 + 1 / 2) * 1 ∧ 1 + (1 : ℝ) / 2 > 5 / 4) ∧
    IsSPNE (deterA 4 0 1 (1 / 2) (5 / 4)) (pureMoves cA) ∧
    IsSPNE (deterB 4 0 1 (1 / 2) (1 / 2)) (pureMoves (cB 1)) ∧
    IsSPNE (deterB 4 0 1 (1 / 2) (5 / 4)) (pureMoves (cB 0)) := by
  refine ⟨by norm_num, (exercise_9_B_14a 4 0 1 (1 / 2) (5 / 4) (by norm_num) (by norm_num)
    (by norm_num)).1, ((exercise_9_B_14b 4 0 1 (1 / 2) (1 / 2) (by norm_num) (by norm_num)
    (by norm_num)).2.1 (by norm_num)).1, ((exercise_9_B_14b 4 0 1 (1 / 2) (5 / 4) (by norm_num)
    (by norm_num) (by norm_num)).2.2.1 (by norm_num)).1⟩

end MWG.DynamicGames

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Bargaining with offer costs

MWG, Exercises 9.B.7 and 9.B.13 (pp. 302-303): the alternating-offer game of Example 9.AA.1
(Appendix A, pp. 296-297) without discounting, where making an offer costs the proposer
`c ∈ (0, v)`, incurred whether or not the offer is accepted.

The game reuses the histories and profiles of `MWGDynamicGames.Bargaining` (`BargainingProfile`,
the lists of rejected offers, `BargainingGame.path`, `BargainingGame.proposer`). Agreement in
period `t` on the offer `y` gives the responder `y` and the proposer `v − y`, minus each player's
total offer costs; without agreement each player loses her offer costs. The horizon `T : ℕ∞`
is the number of periods (`⊤`: Exercise 9.B.13). Payoffs are in `WithBot ℝ`: perpetual
disagreement in the infinite game means infinitely many offers, so payoff `⊥` (`−∞`).

* `firstStop`: the payoff of a stream of flows `f k` stopped at the first `k` with
  `c k = false` with terminal payoff `g k`; its recursion `firstStop_eq` and the one-stage
  bound `firstStop_le`.
* `OfferCostGame.threshold_isSPNE`: a threshold profile (the period-`n` proposer offers `a n`,
  the responder accepts exactly the offers `y ≥ a n`) is an SPNE when `a n` is the responder's
  value as the next proposer, `a n = v − c − a (n + 1)` (and `a n = 0` in the last period).
* `exercise_9_B_7`: with `T` periods the SPNE is unique; with `m` periods left the proposer
  offers `W (m − 1)`, the responder accepts exactly the offers `y ≥ W (m − 1)`, where
  `W k = v − c` for odd `k` and `0` for even `k`; player 1 gets `W T` and player 2 `W (T − 1)`:
  `(v − c, 0)` if `T` is odd and `(0, v − c)` if `T` is even. `exercise_9_B_7_limit`: the
  outcome has no limit as `T → ∞`.
* `exercise_9_B_13`: in the infinite game, every SPNE gives payoffs `a, b ≥ 0` with
  `a + b ≤ v − c` (in every subgame), and every split `(a, v − c − a)`, `a ∈ [0, v − c]`, is
  the payoff of an SPNE with immediate agreement; so the SPNE is not unique
  (`exercise_9_B_13_not_unique`), and player 1's set of SPNE payoffs is exactly `[0, v − c]`
  (`exercise_9_B_13_payoffs`). `exercise_9_B_13_delay`: if `v < 2c` agreement is immediate in
  every SPNE; if `v ≥ 2c` there is an SPNE in which the first offer is rejected
  (`delayProfile`, verified with the one-stage deviation principle `isSPNE_of_oneStage`).
-/

namespace MWG.DynamicGames

open Classical in
/-- The payoff of the flow stream `f` stopped at the first `k` with `c k = false`, with
terminal payoff `g k` there; `⊥` if the stream never stops. -/
noncomputable def firstStop (c : ℕ → Bool) (f : ℕ → ℝ) (g : ℕ → WithBot ℝ) : WithBot ℝ :=
  if hx : ∃ k, c k = false then
    (((∑ k ∈ Finset.range (Nat.find hx), f k : ℝ)) : WithBot ℝ) + g (Nat.find hx)
  else ⊥

open Classical in
theorem firstStop_of_exists {c : ℕ → Bool} (f : ℕ → ℝ) (g : ℕ → WithBot ℝ)
    (hx : ∃ k, c k = false) : firstStop c f g =
      (((∑ k ∈ Finset.range (Nat.find hx), f k : ℝ)) : WithBot ℝ) + g (Nat.find hx) := by
  unfold firstStop
  split_ifs
  rfl

theorem firstStop_of_not_exists {c : ℕ → Bool} (f : ℕ → ℝ) (g : ℕ → WithBot ℝ)
    (hx : ¬ ∃ k, c k = false) : firstStop c f g = ⊥ := by
  unfold firstStop
  split_ifs
  rfl

/-- The recursion of a stopped stream. -/
theorem firstStop_eq (c : ℕ → Bool) (f : ℕ → ℝ) (g : ℕ → WithBot ℝ) :
    firstStop c f g = if c 0 = true then ((f 0 : ℝ) : WithBot ℝ) +
      firstStop (fun k => c (k + 1)) (fun k => f (k + 1)) (fun k => g (k + 1)) else g 0 := by
  classical
  by_cases h0 : c 0 = true
  · simp only [h0, ↓reduceIte]
    by_cases hx' : ∃ k, c (k + 1) = false
    · have hx : ∃ k, c k = false := let ⟨k, hk⟩ := hx'; ⟨k + 1, hk⟩
      have hf : Nat.find hx = Nat.find hx' + 1 :=
        Nat.find_comp_succ hx hx' (by simp [h0])
      rw [firstStop_of_exists f g hx, firstStop_of_exists _ _ hx', hf,
        Finset.sum_range_succ', WithBot.coe_add, add_comm (((∑ k ∈ Finset.range _, _ : ℝ)) :
          WithBot ℝ), add_assoc]
    · have hx : ¬ ∃ k, c k = false := by
        rintro ⟨k, hk⟩
        cases k with
        | zero => simp [h0] at hk
        | succ k => exact hx' ⟨k, hk⟩
      rw [firstStop_of_not_exists f g hx, firstStop_of_not_exists _ _ hx', WithBot.add_bot]
  · have h0' : c 0 = false := by simpa using h0
    have hx : ∃ k, c k = false := ⟨0, h0'⟩
    have hf : Nat.find hx = 0 := (Nat.find_eq_zero hx).2 h0'
    rw [firstStop_of_exists f g hx, hf]
    simp [h0']

/-- **One-stage bound for stopped streams.** If `f k + b (k + 1) ≤ b k` whenever the stream
continues and `g k ≤ b k` where it stops, then `b 0` bounds the stopped payoff. -/
theorem firstStop_le {c : ℕ → Bool} {f : ℕ → ℝ} {g : ℕ → WithBot ℝ} (b : ℕ → ℝ)
    (hc : ∀ k, c k = true → f k + b (k + 1) ≤ b k)
    (hg : ∀ k, c k = false → g k ≤ b k) : firstStop c f g ≤ b 0 := by
  classical
  have key : ∀ K (c : ℕ → Bool) (f : ℕ → ℝ) (g : ℕ → WithBot ℝ) (b : ℕ → ℝ),
      (∀ k, c k = true → f k + b (k + 1) ≤ b k) → (∀ k, c k = false → g k ≤ b k) →
      (∀ j < K, c j = true) → c K = false →
      (((∑ k ∈ Finset.range K, f k : ℝ)) : WithBot ℝ) + g K ≤ b 0 := by
    intro K
    induction K with
    | zero =>
      intro c f g b _ hg _ hK
      simpa using hg 0 hK
    | succ K ih =>
      intro c f g b hc hg hj hK
      have h1 := ih (fun k => c (k + 1)) (fun k => f (k + 1)) (fun k => g (k + 1))
        (fun k => b (k + 1)) (fun k hk => hc (k + 1) hk) (fun k hk => hg (k + 1) hk)
        (fun j hj' => hj (j + 1) (by omega)) hK
      have h2 := hc 0 (hj 0 (by omega))
      rw [Finset.sum_range_succ', WithBot.coe_add, add_comm (((∑ k ∈ Finset.range _, _ : ℝ)) :
          WithBot ℝ), add_assoc]
      calc ((f 0 : ℝ) : WithBot ℝ) + ((((∑ k ∈ Finset.range K, f (k + 1) : ℝ)) : WithBot ℝ) +
            g (K + 1)) ≤ ((f 0 : ℝ) : WithBot ℝ) + ((b 1 : ℝ) : WithBot ℝ) := by
            gcongr
        _ ≤ b 0 := by
            rw [← WithBot.coe_add]
            exact WithBot.coe_le_coe.2 h2
  by_cases hx : ∃ k, c k = false
  · rw [firstStop_of_exists f g hx]
    exact key _ c f g b hc hg (fun j hj => by simpa using Nat.find_min hx hj) (Nat.find_spec hx)
  · rw [firstStop_of_not_exists f g hx]
    exact bot_le

/-- The sum of two stopped streams with the same stopping rule. -/
theorem firstStop_add (c : ℕ → Bool) (f f' : ℕ → ℝ) (g g' : ℕ → WithBot ℝ) :
    firstStop c f g + firstStop c f' g' = firstStop c (fun k => f k + f' k) (fun k => g k + g' k)
    := by
  classical
  by_cases hx : ∃ k, c k = false
  · rw [firstStop_of_exists f g hx, firstStop_of_exists f' g' hx, firstStop_of_exists _ _ hx,
      Finset.sum_add_distrib, WithBot.coe_add]
    abel
  · rw [firstStop_of_not_exists f g hx, firstStop_of_not_exists f' g' hx,
      firstStop_of_not_exists _ _ hx, WithBot.bot_add]

/-- The bargaining game with offer costs (MWG, Exercises 9.B.7 and 9.B.13, pp. 302-303): the
surplus `v`, the cost `c ∈ (0, v)` of making an offer and the horizon `T` (number of periods;
`⊤` for the infinite horizon). There is no discounting. -/
structure OfferCostGame where
  /-- The amount to be divided. -/
  v : ℝ
  /-- The cost of making an offer. -/
  c : ℝ
  /-- The horizon: the number of periods. -/
  T : ℕ∞
  c_pos : 0 < c
  c_lt_v : c < v

namespace OfferCostGame

open BargainingGame (proposer other other_ne ne_other other_other eq_or_eq_other proposer_succ
  path path_succ length_path setResp setProp IsDeviation setResp_isDeviation
  setProp_isDeviation)

variable (G : OfferCostGame)

/-- Period `n` is within the horizon. -/
def Live (n : ℕ) : Prop := (n : ℕ∞) < G.T

/-- Player `i`'s share (before costs) of an agreement on the offer `y` in period `n`. -/
def share (i : Fin 2) (n : ℕ) (y : ℝ) : ℝ := if proposer n = i then G.v - y else y

/-- Player `i`'s offer cost in period `n`: `c` if she is the proposer. -/
def offerCost (i : Fin 2) (n : ℕ) : ℝ := if proposer n = i then G.c else 0

theorem share_proposer (n : ℕ) (y : ℝ) : G.share (proposer n) n y = G.v - y := by
  simp [share]

theorem share_other (n : ℕ) (y : ℝ) : G.share (other (proposer n)) n y = y := by
  simp [share, ne_other]

theorem offerCost_proposer (n : ℕ) : G.offerCost (proposer n) n = G.c := by
  simp [offerCost]

theorem offerCost_other (n : ℕ) : G.offerCost (other (proposer n)) n = 0 := by
  simp [offerCost, ne_other]

open Classical in
/-- Player `i`'s payoff from the proposal node `h` under `σ`, counting the costs of the offers
made from `h` on: her share of the first agreement minus her offer costs, `−`(her offer costs)
if the horizon ends without agreement, and `⊥` under perpetual disagreement. -/
noncomputable def value (σ : BargainingProfile) (h : List ℝ) (i : Fin 2) : WithBot ℝ :=
  firstStop
    (fun k => decide (G.Live (h.length + k)) && !σ.resp (path σ h k) (σ.prop (path σ h k)))
    (fun k => -G.offerCost i (h.length + k))
    (fun k => if G.Live (h.length + k) then
      ((G.share i (h.length + k) (σ.prop (path σ h k)) - G.offerCost i (h.length + k) : ℝ) :
        WithBot ℝ) else 0)

open Classical in
/-- Player `i`'s payoff from the response node `(h, y)` (period `h.length` live). -/
noncomputable def respValue (σ : BargainingProfile) (h : List ℝ) (y : ℝ) (i : Fin 2) :
    WithBot ℝ :=
  if σ.resp h y = true then ((G.share i h.length y - G.offerCost i h.length : ℝ) : WithBot ℝ)
  else ((-G.offerCost i h.length : ℝ) : WithBot ℝ) + G.value σ (y :: h) i

/-- Beyond the horizon payoffs (from then on) are `0`. -/
theorem value_of_not_live {σ : BargainingProfile} {h : List ℝ} (hl : ¬ G.Live h.length)
    (i : Fin 2) : G.value σ h i = 0 := by
  unfold value
  rw [firstStop_eq]
  simp [hl]

/-- The value at a live proposal node is the value at the response node to the offer made. -/
theorem value_eq_respValue (σ : BargainingProfile) {h : List ℝ} (hl : G.Live h.length)
    (i : Fin 2) : G.value σ h i = G.respValue σ h (σ.prop h) i := by
  unfold value respValue
  rw [firstStop_eq]
  cases hr : σ.resp h (σ.prop h) with
  | true => simp [hl, path, hr]
  | false =>
    simp only [path, add_zero, hl, decide_true, hr, Bool.not_false, Bool.and_self,
      ↓reduceIte, Bool.false_eq_true]
    congr 1
    unfold value
    congr 1
    · funext k
      rw [← path_succ, List.length_cons, show h.length + 1 + k = h.length + (k + 1) by omega]
      rfl
    · funext k
      rw [List.length_cons, show h.length + 1 + k = h.length + (k + 1) by omega]
    · funext k
      rw [← path_succ, List.length_cons, show h.length + 1 + k = h.length + (k + 1) by omega]
      rfl

theorem respValue_accept {σ : BargainingProfile} {h : List ℝ} {y : ℝ} (hy : σ.resp h y = true)
    (i : Fin 2) : G.respValue σ h y i = ((G.share i h.length y - G.offerCost i h.length : ℝ) :
      WithBot ℝ) := by
  simp [respValue, hy]

theorem respValue_reject {σ : BargainingProfile} {h : List ℝ} {y : ℝ} (hy : σ.resp h y = false)
    (i : Fin 2) : G.respValue σ h y i =
      ((-G.offerCost i h.length : ℝ) : WithBot ℝ) + G.value σ (y :: h) i := by
  simp [respValue, hy]

/-- The value from `h` depends only on the moves at histories at least as long as `h`. -/
theorem value_congr {σ σ' : BargainingProfile} {h : List ℝ}
    (hp : ∀ h', h.length ≤ h'.length → σ.prop h' = σ'.prop h')
    (hr : ∀ h' y, h.length ≤ h'.length → σ.resp h' y = σ'.resp h' y) (i : Fin 2) :
    G.value σ h i = G.value σ' h i := by
  have hpath : ∀ t, path σ h t = path σ' h t := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
      rw [path, path, ih, hp _ (by rw [length_path]; omega)]
  unfold value
  congr 1
  · funext k
    rw [hpath, hp _ (by rw [length_path]; omega), hr _ _ (by rw [length_path]; omega)]
  · funext k
    rw [hpath, hp _ (by rw [length_path]; omega)]

theorem setResp_value (σ : BargainingProfile) (h₀ : List ℝ) (y₀ : ℝ) (b : Bool) (i : Fin 2) :
    G.value (setResp σ h₀ y₀ b) (y₀ :: h₀) i = G.value σ (y₀ :: h₀) i := by
  refine G.value_congr (σ := setResp σ h₀ y₀ b) (σ' := σ) (fun _ _ => rfl) (fun h' y hl => ?_) i
  have : h' ≠ h₀ := fun he => by rw [he] at hl; simp at hl
  simp [setResp, this]

theorem setProp_value (σ : BargainingProfile) (h₀ : List ℝ) (y₀ y : ℝ) (i : Fin 2) :
    G.value (setProp σ h₀ y₀) (y :: h₀) i = G.value σ (y :: h₀) i := by
  refine G.value_congr (σ := setProp σ h₀ y₀) (σ' := σ) (fun h' hl => ?_) (fun _ _ _ => rfl) i
  have : h' ≠ h₀ := fun he => by rw [he] at hl; simp at hl
  simp [setProp, this]

/-- **One-stage deviation bound with offer costs.** If `bnd ≥ 0` beyond the horizon, `bnd h`
bounds player `i`'s payoff of an agreement at `h`, and `bnd` covers the offer cost plus `bnd`
at the next node after a rejection, then `bnd` bounds player `i`'s payoff from every node. -/
theorem value_le_of_bound {σ : BargainingProfile} {i : Fin 2} (bnd : List ℝ → ℝ)
    (hnl : ∀ h, ¬ G.Live h.length → 0 ≤ bnd h)
    (hacc : ∀ h, G.Live h.length → σ.resp h (σ.prop h) = true →
      G.share i h.length (σ.prop h) - G.offerCost i h.length ≤ bnd h)
    (hrej : ∀ h, G.Live h.length → σ.resp h (σ.prop h) = false →
      -G.offerCost i h.length + bnd (σ.prop h :: h) ≤ bnd h)
    (h : List ℝ) : G.value σ h i ≤ bnd h := by
  unfold value
  refine firstStop_le (fun k => bnd (path σ h k)) (fun k hk => ?_) (fun k hk => ?_)
  · simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true]
      at hk
    have := hrej (path σ h k) (by rw [length_path]; exact hk.1) hk.2
    rw [length_path] at this
    exact this
  · by_cases hl : G.Live (h.length + k)
    · have hr : σ.resp (path σ h k) (σ.prop (path σ h k)) = true := by
        simpa [hl] using hk
      have := hacc (path σ h k) (by rw [length_path]; exact hl) hr
      rw [length_path] at this
      simp only [hl, ↓reduceIte]
      exact WithBot.coe_le_coe.2 this
    · have := hnl (path σ h k) (by rw [length_path]; exact hl)
      simp only [hl, ↓reduceIte]
      exact WithBot.coe_le_coe.2 this

/-- Offers are feasible: `prop h ∈ [0, v]` at every history. -/
def Feasible (σ : BargainingProfile) : Prop := ∀ h, σ.prop h ∈ Set.Icc 0 G.v

/-- A history of feasible offers. -/
def ValidHist (h : List ℝ) : Prop := ∀ y ∈ h, y ∈ Set.Icc 0 G.v

theorem validHist_cons {h : List ℝ} (hh : G.ValidHist h) {y : ℝ} (hy : y ∈ Set.Icc 0 G.v) :
    G.ValidHist (y :: h) := by
  intro z hz
  rcases List.mem_cons.1 hz with rfl | hz
  · exact hy
  · exact hh z hz

/-- **Definition 9.B.2 for the bargaining game with offer costs** (MWG, pp. 275 and 302-303).
A subgame perfect Nash equilibrium: at every feasible proposal node `h` within the horizon and
at every response node `(h, y)` with `y ∈ [0, v]`, no player gains by deviating to any feasible
strategy. -/
def IsSPNE (σ : BargainingProfile) : Prop :=
  G.Feasible σ ∧ ∀ i σ', G.Feasible σ' → IsDeviation i σ σ' → ∀ h, G.ValidHist h →
    G.Live h.length → G.value σ' h i ≤ G.value σ h i ∧
      ∀ y ∈ Set.Icc 0 G.v, G.respValue σ' h y i ≤ G.respValue σ h y i

/-- In an SPNE the responder accepts an offer that beats her continuation payoff. -/
theorem accept_of_gt {σ : BargainingProfile} (hσ : G.IsSPNE σ) {h : List ℝ}
    (hv : G.ValidHist h) (hl : G.Live h.length) {y : ℝ} (hy : y ∈ Set.Icc 0 G.v)
    (hgt : G.value σ (y :: h) (other (proposer h.length)) < y) : σ.resp h y = true := by
  by_contra hrej
  have hrej' : σ.resp h y = false := by simpa using hrej
  have := (hσ.2 _ (setResp σ h y true) hσ.1 (setResp_isDeviation σ h y true) h hv hl).2 y hy
  rw [G.respValue_accept (by simp [setResp]), G.respValue_reject hrej', share_other,
    offerCost_other] at this
  simp only [sub_zero, neg_zero, WithBot.coe_zero, zero_add] at this
  exact absurd this (not_le.2 hgt)

/-- In an SPNE the responder rejects an offer below her continuation payoff. -/
theorem reject_of_lt {σ : BargainingProfile} (hσ : G.IsSPNE σ) {h : List ℝ}
    (hv : G.ValidHist h) (hl : G.Live h.length) {y : ℝ} (hy : y ∈ Set.Icc 0 G.v)
    (hlt : (y : WithBot ℝ) < G.value σ (y :: h) (other (proposer h.length))) :
    σ.resp h y = false := by
  by_contra hacc
  have hacc' : σ.resp h y = true := by simpa using hacc
  have := (hσ.2 _ (setResp σ h y false) hσ.1 (setResp_isDeviation σ h y false) h hv hl).2 y hy
  rw [G.respValue_reject (by simp [setResp]), G.setResp_value, G.respValue_accept hacc',
    share_other, offerCost_other] at this
  simp only [sub_zero, neg_zero, WithBot.coe_zero, zero_add] at this
  exact absurd this (not_le.2 hlt)

/-- In an SPNE the proposer does at least as well as with any other feasible offer. -/
theorem respValue_le_value {σ : BargainingProfile} (hσ : G.IsSPNE σ) {h : List ℝ}
    (hv : G.ValidHist h) (hl : G.Live h.length) {y : ℝ} (hy : y ∈ Set.Icc 0 G.v) :
    G.respValue σ h y (proposer h.length) ≤ G.value σ h (proposer h.length) := by
  have hf : G.Feasible (setProp σ h y) := by
    intro h'
    simp only [setProp]
    split_ifs
    · exact hy
    · exact hσ.1 h'
  have := (hσ.2 _ _ hf (setProp_isDeviation σ h y) h hv hl).1
  rw [G.value_eq_respValue _ hl] at this
  have hp : (setProp σ h y).prop h = y := by simp [setProp]
  rw [hp] at this
  unfold respValue at this ⊢
  rw [G.setProp_value] at this
  exact this

/-- The threshold profile: in period `n` the proposer offers `a n`; the responder accepts
exactly the offers `y ≥ a n`. -/
noncomputable def threshold (a : ℕ → ℝ) : BargainingProfile where
  prop h := a h.length
  resp h y := decide (a h.length ≤ y)

/-- Payoffs of a threshold profile from a live node: immediate agreement, the proposer gets
`v − c − a n` and the responder `a n`. -/
theorem value_threshold (a : ℕ → ℝ) {h : List ℝ} (hl : G.Live h.length) :
    G.value (threshold a) h (proposer h.length) = ((G.v - G.c - a h.length : ℝ) : WithBot ℝ) ∧
      G.value (threshold a) h (other (proposer h.length)) = ((a h.length : ℝ) : WithBot ℝ) := by
  have hacc : (threshold a).resp h ((threshold a).prop h) = true := by simp [threshold]
  rw [G.value_eq_respValue _ hl, G.value_eq_respValue _ hl, G.respValue_accept hacc,
    G.respValue_accept hacc, share_proposer, share_other, offerCost_proposer, offerCost_other]
  refine ⟨?_, ?_⟩
  · simp only [threshold]
    congr 1
    ring
  · simp [threshold]

/-- **Threshold profiles are SPNE** (MWG, pp. 302-303). If `a n ∈ [0, v]` for all `n`, and in
every live period `a n` is the responder's value as the next proposer (`a n = v − c − a (n + 1)`
if period `n + 1` is live, `a n = 0` in the last period), then `threshold a` is a subgame
perfect Nash equilibrium. -/
theorem threshold_isSPNE {a : ℕ → ℝ} (ha0 : ∀ n, a n ∈ Set.Icc 0 G.v)
    (ha1 : ∀ n, G.Live (n + 1) → a n = G.v - G.c - a (n + 1))
    (ha2 : ∀ n, G.Live n → ¬ G.Live (n + 1) → a n = 0) : G.IsSPNE (threshold a) := by
  classical
  refine ⟨fun h => ha0 h.length, fun i σ' hσ' hdev h hv hl => ?_⟩
  let bnd : List ℝ → ℝ := fun h => if G.Live h.length then
    (if proposer h.length = i then G.v - G.c - a h.length else a h.length) else 0
  have hbnd_val : ∀ h, G.value (threshold a) h i = bnd h := by
    intro h
    simp only [bnd]
    split_ifs with hl' hp
    · rw [← hp]; exact (G.value_threshold a hl').1
    · rcases eq_or_eq_other (proposer h.length) i with h1 | h1
      · exact absurd h1.symm hp
      · rw [h1]; exact (G.value_threshold a hl').2
    · rw [G.value_of_not_live hl']
      rfl
  -- the responder's continuation `bnd (y :: h)` as the next proposer is `a n`
  have hnext : ∀ h y, G.Live h.length → proposer h.length ≠ i → bnd (y :: h) = a h.length := by
    intro h y hl' hp
    have hi : proposer (y :: h).length = i := by
      rcases eq_or_eq_other (proposer h.length) i with h1 | h1
      · exact absurd h1.symm hp
      · rw [List.length_cons, proposer_succ, h1]
    simp only [bnd, hi, ↓reduceIte]
    split_ifs with hl2
    · exact (ha1 _ hl2).symm
    · exact (ha2 _ hl' hl2).symm
  have hnext' : ∀ h y, G.Live h.length → proposer h.length = i →
      bnd (y :: h) = if G.Live (h.length + 1) then a (h.length + 1) else 0 := by
    intro h y _ hp
    have hi : proposer (h.length + 1) ≠ i := by
      rw [proposer_succ, hp]
      exact other_ne i
    simp only [bnd, List.length_cons, hi, ↓reduceIte]
  have hbound : ∀ h, G.value σ' h i ≤ bnd h := by
    refine G.value_le_of_bound bnd (fun h hl' => by simp [bnd, hl']) (fun h' hl' hr => ?_)
      (fun h' hl' hr => ?_)
    · by_cases hp : proposer h'.length = i
      · have hr' := hdev.2 h' (σ'.prop h') hp
        rw [hr] at hr'
        have hle : a h'.length ≤ σ'.prop h' := by simpa [threshold] using hr'.symm
        subst hp
        rw [share_proposer, offerCost_proposer]
        simp only [bnd, hl', ↓reduceIte]
        linarith
      · have hpr := hdev.1 h' hp
        rcases eq_or_eq_other (proposer h'.length) i with h1 | h1
        · exact absurd h1.symm hp
        · subst h1
          rw [share_other, offerCost_other, hpr]
          simp only [bnd, hl', hp, ↓reduceIte, threshold]
          linarith
    · by_cases hp : proposer h'.length = i
      · rw [hnext' h' _ hl' hp]
        have hle := (ha0 h'.length).2
        subst hp
        rw [offerCost_proposer]
        simp only [bnd, hl', ↓reduceIte]
        have hc := G.c_pos
        split_ifs with hl2
        · rw [ha1 _ hl2]; linarith
        · linarith
      · rw [hnext h' _ hl' hp]
        rcases eq_or_eq_other (proposer h'.length) i with h1 | h1
        · exact absurd h1.symm hp
        · subst h1
          rw [offerCost_other]
          simp only [bnd, hl', hp, ↓reduceIte]
          linarith
  refine ⟨by rw [hbnd_val]; exact hbound h, fun y hy => ?_⟩
  by_cases hp : proposer h.length = i
  · have hr' := hdev.2 h y hp
    cases hry : (threshold a).resp h y with
    | true =>
      rw [G.respValue_accept hry, G.respValue_accept (hr'.trans hry)]
    | false =>
      rw [G.respValue_reject hry, G.respValue_reject (hr'.trans hry), hbnd_val]
      gcongr
      exact hbound _
  · have hB := hnext h y hl hp
    rcases eq_or_eq_other (proposer h.length) i with h1 | h1
    · exact absurd h1.symm hp
    · subst h1
      have hσ'v : G.value σ' (y :: h) (other (proposer h.length)) ≤ a h.length := by
        rw [← hB]; exact hbound _
      have hthr : (y : WithBot ℝ) ≤ G.respValue (threshold a) h y (other (proposer h.length)) ∧
          ((a h.length : ℝ) : WithBot ℝ) ≤
            G.respValue (threshold a) h y (other (proposer h.length)) := by
        cases hry : (threshold a).resp h y with
        | true =>
          rw [G.respValue_accept hry, share_other, offerCost_other, sub_zero]
          have : a h.length ≤ y := by simpa [threshold] using hry
          exact ⟨le_rfl, WithBot.coe_le_coe.2 this⟩
        | false =>
          rw [G.respValue_reject hry, offerCost_other, hbnd_val, hB, neg_zero, WithBot.coe_zero,
            zero_add]
          have : y < a h.length := by simpa [threshold] using hry
          exact ⟨WithBot.coe_le_coe.2 this.le, le_rfl⟩
      cases hry : σ'.resp h y with
      | true =>
        rw [G.respValue_accept hry, share_other, offerCost_other, sub_zero]
        exact hthr.1
      | false =>
        rw [G.respValue_reject hry, offerCost_other, neg_zero, WithBot.coe_zero, zero_add]
        exact hσ'v.trans hthr.2

/-- **SPNE strategies at a node are determined by the continuation values.** In an SPNE, if
after every feasible offer at the live node `h` the responder's continuation value (as the
next proposer) is `X ∈ [0, v]` and the proposer's is `Y ≥ 0`, with `X + Y < v`, then the
proposer offers exactly `X`, the responder accepts exactly the offers `y ≥ X` (indifference
included), and the payoffs from `h` are `v − c − X` and `X`. -/
theorem strategies_determined {σ : BargainingProfile} (hσ : G.IsSPNE σ) {h : List ℝ}
    (hv : G.ValidHist h) (hl : G.Live h.length) {X Y : ℝ} (hX : X ∈ Set.Icc 0 G.v)
    (hY : 0 ≤ Y) (hXY : X + Y < G.v)
    (hcr : ∀ y ∈ Set.Icc 0 G.v, G.value σ (y :: h) (other (proposer h.length)) = X)
    (hcp : ∀ y ∈ Set.Icc 0 G.v, G.value σ (y :: h) (proposer h.length) = Y) :
    σ.prop h = X ∧ (∀ y ∈ Set.Icc 0 G.v, σ.resp h y = decide (X ≤ y)) ∧
      G.value σ h (proposer h.length) = ((G.v - G.c - X : ℝ) : WithBot ℝ) ∧
      G.value σ h (other (proposer h.length)) = (X : WithBot ℝ) := by
  set p := proposer h.length
  set r := other p
  have hc := G.c_pos
  have hgt : ∀ y ∈ Set.Icc 0 G.v, X < y → σ.resp h y = true := fun y hy hxy =>
    G.accept_of_gt hσ hv hl hy (by rw [hcr y hy]; exact WithBot.coe_lt_coe.2 hxy)
  have hlt : ∀ y ∈ Set.Icc 0 G.v, y < X → σ.resp h y = false := fun y hy hxy =>
    G.reject_of_lt hσ hv hl hy (by rw [hcr y hy]; exact WithBot.coe_lt_coe.2 hxy)
  set y₀ := σ.prop h
  have hy₀ : y₀ ∈ Set.Icc 0 G.v := hσ.1 h
  -- the proposer's payoff is a real number `V`
  set V : ℝ := if σ.resp h y₀ = true then G.v - y₀ - G.c else Y - G.c with hVdef
  have hval : G.value σ h p = (V : WithBot ℝ) := by
    rw [G.value_eq_respValue σ hl]
    cases hr : σ.resp h y₀ with
    | true =>
      rw [G.respValue_accept hr, share_proposer, offerCost_proposer]
      simp only [hVdef, hr, ↓reduceIte]
    | false =>
      rw [G.respValue_reject hr, offerCost_proposer, hcp y₀ hy₀, ← WithBot.coe_add]
      simp only [hVdef, hr, Bool.false_eq_true, ↓reduceIte]
      congr 1
      ring
  have hdev : ∀ y ∈ Set.Icc 0 G.v, σ.resp h y = true → G.v - y - G.c ≤ V := by
    intro y hy hr
    have := G.respValue_le_value hσ hv hl hy
    rw [G.respValue_accept hr, share_proposer, offerCost_proposer, hval] at this
    exact WithBot.coe_le_coe.1 this
  have hVlow : X - G.v - G.c ≤ V := by
    simp only [hVdef]
    split_ifs <;> linarith [hX.1, hX.2, hy₀.1, hy₀.2]
  -- indifference: the responder accepts `X`
  have hXacc : σ.resp h X = true := by
    by_contra hrej
    have hrej' : σ.resp h X = false := by simpa using hrej
    have hVlt : V < G.v - G.c - X := by
      simp only [hVdef]
      split_ifs with hr
      · have hge : X ≤ y₀ := by
          by_contra hlt'
          rw [hlt y₀ hy₀ (not_le.1 hlt')] at hr
          exact Bool.noConfusion hr
        have hne : y₀ ≠ X := fun he => by rw [he, hrej'] at hr; exact Bool.noConfusion hr
        have := lt_of_le_of_ne hge (Ne.symm hne)
        linarith
      · linarith
    set y := X + (G.v - G.c - X - V) / 2
    have hy : y ∈ Set.Icc 0 G.v := ⟨by simp only [y]; linarith [hX.1],
      by simp only [y]; linarith [hX.2]⟩
    have := hdev y hy (hgt y hy (by simp only [y]; linarith))
    simp only [y] at this
    linarith
  have hXdev := hdev X hX hXacc
  have hprop : y₀ = X := by
    cases hr : σ.resp h y₀ with
    | true =>
      have hge : X ≤ y₀ := by
        by_contra hlt'
        rw [hlt y₀ hy₀ (not_le.1 hlt')] at hr
        exact Bool.noConfusion hr
      simp only [hVdef, hr, ↓reduceIte] at hXdev
      linarith
    | false =>
      simp only [hVdef, hr, Bool.false_eq_true, ↓reduceIte] at hXdev
      linarith
  refine ⟨hprop, fun y hy => ?_, ?_, ?_⟩
  · rcases lt_trichotomy y X with hyX | hyX | hyX
    · rw [hlt y hy hyX]; simp [not_le.2 hyX]
    · rw [hyX, hXacc]; simp
    · rw [hgt y hy hyX]; simp [hyX.le]
  · rw [G.value_eq_respValue σ hl, show σ.prop h = X from hprop, G.respValue_accept hXacc,
      share_proposer, offerCost_proposer]
    congr 1
    ring
  · rw [G.value_eq_respValue σ hl, show σ.prop h = X from hprop, G.respValue_accept hXacc,
      share_other, offerCost_other, sub_zero]

/-- The upper bounds on payoffs for any feasible profile: at most `v − c` for a player who
proposes at `h` and at most `v` for the responder. -/
theorem value_le_feasible {σ : BargainingProfile} (hσ : G.Feasible σ) (i : Fin 2)
    (h : List ℝ) : G.value σ h i ≤ ((if proposer h.length = i then G.v - G.c else G.v : ℝ) :
      WithBot ℝ) := by
  have hc := G.c_pos
  have hcv := G.c_lt_v
  refine G.value_le_of_bound (fun h => if proposer h.length = i then G.v - G.c else G.v)
    (fun h _ => by split_ifs <;> linarith) (fun h' _ _ => ?_) (fun h' _ _ => ?_) h
  · have hy := hσ h'
    by_cases hp : proposer h'.length = i
    · subst hp
      rw [share_proposer, offerCost_proposer]
      simp only [↓reduceIte]
      linarith [hy.1]
    · rcases eq_or_eq_other (proposer h'.length) i with h1 | h1
      · exact absurd h1.symm hp
      · subst h1
        rw [share_other, offerCost_other]
        simp only [hp, ↓reduceIte]
        linarith [hy.2]
  · by_cases hp : proposer h'.length = i
    · have hn : proposer (σ.prop h' :: h').length ≠ i := by
        rw [List.length_cons, proposer_succ, hp]; exact other_ne i
      subst hp
      rw [offerCost_proposer]
      simp only [hn, ↓reduceIte]
      linarith
    · have hn : proposer (σ.prop h' :: h').length = i := by
        rcases eq_or_eq_other (proposer h'.length) i with h1 | h1
        · exact absurd h1.symm hp
        · rw [List.length_cons, proposer_succ, h1]
      rcases eq_or_eq_other (proposer h'.length) i with h1 | h1
      · exact absurd h1.symm hp
      · rw [hn]
        subst h1
        rw [offerCost_other]
        simp only [hp, ↓reduceIte]
        linarith

theorem offerCost_add (n : ℕ) : G.offerCost 0 n + G.offerCost 1 n = G.c := by
  unfold offerCost
  rcases Fin.exists_fin_two.1 ⟨proposer n, rfl⟩ with h | h <;> simp [h]

theorem share_add (n : ℕ) (y : ℝ) : G.share 0 n y + G.share 1 n y = G.v := by
  unfold share
  rcases Fin.exists_fin_two.1 ⟨proposer n, rfl⟩ with h | h <;> simp [h]

/-- The two players' payoffs add up to at most `v − c`: an agreement divides `v`, and at least
one offer is made. -/
theorem value_add_le {σ : BargainingProfile} (h : List ℝ) :
    G.value σ h 0 + G.value σ h 1 ≤ ((G.v - G.c : ℝ) : WithBot ℝ) := by
  have hc := G.c_pos
  have hcv := G.c_lt_v
  unfold value
  rw [firstStop_add]
  refine firstStop_le (fun _ => G.v - G.c) (fun k _ => ?_) (fun k _ => ?_)
  · have := G.offerCost_add (h.length + k)
    linarith
  · split_ifs
    · rw [← WithBot.coe_add]
      refine WithBot.coe_le_coe.2 (le_of_eq ?_)
      have h1 := G.offerCost_add (h.length + k)
      have h2 := G.share_add (h.length + k) (σ.prop (path σ h k))
      linarith
    · simp only [add_zero]
      exact WithBot.coe_le_coe.2 (by linarith)

/-- **SPNE payoffs are nonnegative.** In an SPNE, at every live feasible node, the proposer's
and the responder's payoffs are real numbers `a, b ≥ 0` with `a + b ≤ v − c`. -/
theorem spne_bounds {σ : BargainingProfile} (hσ : G.IsSPNE σ) :
    ∀ h, G.ValidHist h → G.Live h.length → ∃ a b : ℝ,
      G.value σ h (proposer h.length) = a ∧ G.value σ h (other (proposer h.length)) = b ∧
        0 ≤ a ∧ 0 ≤ b ∧ a + b ≤ G.v - G.c := by
  have hc := G.c_pos
  have hcv := G.c_lt_v
  -- the proposer's payoff is at least `0`
  have hprop : ∀ h, G.ValidHist h → G.Live h.length →
      ∃ a : ℝ, G.value σ h (proposer h.length) = a ∧ 0 ≤ a := by
    intro h hv hl
    have hlow : ∀ y ∈ Set.Ioc (G.v - G.c) G.v,
        ((G.v - y - G.c : ℝ) : WithBot ℝ) ≤ G.value σ h (proposer h.length) := by
      intro y hy
      have hy' : y ∈ Set.Icc 0 G.v := ⟨by linarith [hy.1], hy.2⟩
      have hub := G.value_le_feasible hσ.1 (other (proposer h.length)) (y :: h)
      rw [List.length_cons, proposer_succ] at hub
      simp only [↓reduceIte] at hub
      have hacc := G.accept_of_gt hσ hv hl hy'
        (lt_of_le_of_lt hub (WithBot.coe_lt_coe.2 hy.1))
      have := G.respValue_le_value hσ hv hl hy'
      rw [G.respValue_accept hacc, share_proposer, offerCost_proposer] at this
      exact this
    have hne : G.value σ h (proposer h.length) ≠ ⊥ :=
      ne_bot_of_le_ne_bot (WithBot.coe_ne_bot) (hlow G.v ⟨by linarith, le_rfl⟩)
    obtain ⟨x, hx⟩ := WithBot.ne_bot_iff_exists.1 hne
    refine ⟨x, hx.symm, ?_⟩
    have hx1 := hlow G.v ⟨by linarith, le_rfl⟩
    rw [← hx] at hx1
    replace hx1 : G.v - G.v - G.c ≤ x := WithBot.coe_le_coe.1 hx1
    by_contra hneg
    push Not at hneg
    have := hlow (G.v - G.c - x / 2) ⟨by linarith, by linarith⟩
    rw [← hx] at this
    replace this : G.v - (G.v - G.c - x / 2) - G.c ≤ x := WithBot.coe_le_coe.1 this
    linarith
  intro h hv hl
  obtain ⟨a, ha, ha0⟩ := hprop h hv hl
  -- the responder's payoff is at least `0`
  have hresp : ∃ b : ℝ, G.value σ h (other (proposer h.length)) = b ∧ 0 ≤ b := by
    have hy₀ := hσ.1 h
    rw [G.value_eq_respValue σ hl]
    cases hr : σ.resp h (σ.prop h) with
    | true =>
      rw [G.respValue_accept hr, share_other, offerCost_other, sub_zero]
      exact ⟨_, rfl, hy₀.1⟩
    | false =>
      rw [G.respValue_reject hr, offerCost_other, neg_zero, WithBot.coe_zero, zero_add]
      by_cases hl2 : G.Live (σ.prop h :: h).length
      · obtain ⟨b, hb, hb0⟩ := hprop _ (G.validHist_cons hv hy₀) hl2
        rw [List.length_cons, proposer_succ] at hb
        exact ⟨b, hb, hb0⟩
      · exact ⟨0, G.value_of_not_live hl2 _, le_rfl⟩
  obtain ⟨b, hb, hb0⟩ := hresp
  refine ⟨a, b, ha, hb, ha0, hb0, ?_⟩
  have hsum := G.value_add_le (σ := σ) h
  rcases Fin.exists_fin_two.1 ⟨proposer h.length, rfl⟩ with hp | hp
  · have h1 : other (proposer h.length) = 1 := by rw [hp]; rfl
    rw [← hp, ha, ← h1, hb, ← WithBot.coe_add] at hsum
    exact WithBot.coe_le_coe.1 hsum
  · have h1 : other (proposer h.length) = 0 := by rw [hp]; rfl
    rw [← hp, ha, ← h1, hb, ← WithBot.coe_add, add_comm b a] at hsum
    · exact WithBot.coe_le_coe.1 hsum

/-- The proposer's SPNE payoff with `k` periods left in the finite game of Exercise 9.B.7:
`v − c` if `k` is odd and `0` if `k` is even. -/
def W (k : ℕ) : ℝ := if k % 2 = 1 then G.v - G.c else 0

theorem W_zero : G.W 0 = 0 := by simp [W]

theorem W_succ (k : ℕ) : G.W (k + 1) = G.v - G.c - G.W k := by
  unfold W
  rcases Nat.mod_two_eq_zero_or_one k with h | h
  · have : (k + 1) % 2 = 1 := by omega
    simp [h, this]
  · have : (k + 1) % 2 = 0 := by omega
    simp [h, this]

theorem W_mem (k : ℕ) : G.W k ∈ Set.Icc 0 G.v := by
  have hc := G.c_pos
  have hcv := G.c_lt_v
  unfold W
  split_ifs <;> constructor <;> linarith

theorem W_add_pred (k : ℕ) : G.W k + G.W (k - 1) ≤ G.v - G.c := by
  have hcv := G.c_lt_v
  cases k with
  | zero => rw [W_zero]; simp; linarith
  | succ k => rw [W_succ]; simp

theorem live_iff {N : ℕ} (hT : G.T = N) (n : ℕ) : G.Live n ↔ n < N := by
  simp [Live, hT]

/-- **Exercise 9.B.7: the SPNE payoffs** (MWG, p. 302). In every SPNE of the `N`-period game, at
every feasible node with `m` periods left, the proposer earns `W m` and the responder
`W (m − 1)`. -/
theorem exercise_9_B_7_values {N : ℕ} (hT : G.T = N) {σ : BargainingProfile}
    (hσ : G.IsSPNE σ) : ∀ m h, G.ValidHist h → h.length + m = N →
      G.value σ h (proposer h.length) = (G.W m : WithBot ℝ) ∧
        G.value σ h (other (proposer h.length)) = (G.W (m - 1) : WithBot ℝ) := by
  intro m
  induction m with
  | zero =>
    intro h _ hN
    have hl : ¬ G.Live h.length := by rw [G.live_iff hT]; omega
    rw [G.value_of_not_live hl, G.value_of_not_live hl, Nat.zero_sub, W_zero]
    simp
  | succ m ih =>
    intro h hv hN
    have hl : G.Live h.length := by rw [G.live_iff hT]; omega
    have hcont : ∀ y ∈ Set.Icc 0 G.v,
        G.value σ (y :: h) (other (proposer h.length)) = (G.W m : WithBot ℝ) ∧
          G.value σ (y :: h) (proposer h.length) = (G.W (m - 1) : WithBot ℝ) := by
      intro y hy
      have := ih (y :: h) (G.validHist_cons hv hy) (by simp; omega)
      rw [List.length_cons, proposer_succ, other_other] at this
      exact this
    have hcv := G.c_lt_v
    have hc := G.c_pos
    have hd := G.strategies_determined hσ hv hl (G.W_mem m) (G.W_mem (m - 1)).1
      (by linarith [G.W_add_pred m]) (fun y hy => (hcont y hy).1) (fun y hy => (hcont y hy).2)
    refine ⟨?_, ?_⟩
    · rw [hd.2.2.1, W_succ]
    · rw [hd.2.2.2, Nat.add_sub_cancel]

/-- **Exercise 9.B.7** (MWG, p. 302). The `N`-period alternating-offer game with offer cost
`c ∈ (0, v)` and no discounting has a unique SPNE: at every feasible node of period `n < N`
(so `m = N − n` periods are left) the proposer offers `W (m − 1)` and the responder accepts
exactly the offers `y ≥ W (m − 1)` (including at indifference), where `W k` is `v − c` for odd
`k` and `0` for even `k`. Agreement is immediate; player 1 (index `0`) earns `W N` and player
2 earns `W (N − 1)`. -/
theorem exercise_9_B_7 {N : ℕ} (hT : G.T = N) :
    G.IsSPNE (threshold (fun n => G.W (N - n - 1))) ∧
      ∀ σ, G.IsSPNE σ → (∀ h, G.ValidHist h → h.length < N →
        σ.prop h = G.W (N - h.length - 1) ∧
          ∀ y ∈ Set.Icc 0 G.v, σ.resp h y = decide (G.W (N - h.length - 1) ≤ y)) ∧
        G.value σ [] 0 = (G.W N : WithBot ℝ) ∧ G.value σ [] 1 = (G.W (N - 1) : WithBot ℝ) := by
  have hcv := G.c_lt_v
  refine ⟨G.threshold_isSPNE (fun n => G.W_mem _) (fun n hn => ?_) (fun n hn hn' => ?_),
    fun σ hσ => ⟨fun h hv hl => ?_, ?_⟩⟩
  · rw [G.live_iff hT] at hn
    rw [show N - n - 1 = (N - (n + 1) - 1) + 1 by omega, W_succ]
  · rw [G.live_iff hT] at hn hn'
    rw [show N - n - 1 = 0 by omega, W_zero]
  · have hl' : G.Live h.length := by rw [G.live_iff hT]; exact hl
    have hcont : ∀ y ∈ Set.Icc 0 G.v,
        G.value σ (y :: h) (other (proposer h.length)) = (G.W (N - h.length - 1) : WithBot ℝ) ∧
          G.value σ (y :: h) (proposer h.length) =
            (G.W (N - h.length - 1 - 1) : WithBot ℝ) := by
      intro y hy
      have := G.exercise_9_B_7_values hT hσ (N - h.length - 1) (y :: h)
        (G.validHist_cons hv hy) (by simp; omega)
      rw [List.length_cons, proposer_succ, other_other] at this
      exact this
    have hc := G.c_pos
    have hd := G.strategies_determined hσ hv hl' (G.W_mem _) (G.W_mem _).1
      (by linarith [G.W_add_pred (N - h.length - 1)]) (fun y hy => (hcont y hy).1)
      (fun y hy => (hcont y hy).2)
    exact ⟨hd.1, hd.2.1⟩
  · have := G.exercise_9_B_7_values hT hσ N [] (fun _ h => by simp at h) (by simp)
    exact this

/-- **Exercise 9.B.7: parity** (MWG, p. 302). With `N` periods, player 1's SPNE payoff is
`v − c` and player 2's is `0` if `N` is odd; if `N ≥ 2` is even they are `0` and `v − c`. -/
theorem exercise_9_B_7_parity {N : ℕ} (hT : G.T = N) {σ : BargainingProfile}
    (hσ : G.IsSPNE σ) :
    (N % 2 = 1 → G.value σ [] 0 = ((G.v - G.c : ℝ) : WithBot ℝ) ∧ G.value σ [] 1 = 0) ∧
      (N % 2 = 0 → 2 ≤ N →
        G.value σ [] 0 = 0 ∧ G.value σ [] 1 = ((G.v - G.c : ℝ) : WithBot ℝ)) := by
  have h := (G.exercise_9_B_7 hT).2 σ hσ
  refine ⟨fun hN => ?_, fun hN hN2 => ?_⟩
  · rw [h.2.1, h.2.2]
    have : (N - 1) % 2 = 0 := by omega
    simp [W, hN, this]
  · rw [h.2.1, h.2.2]
    have : (N - 1) % 2 = 1 := by omega
    simp [W, hN, this]

open Filter Topology in
/-- **Exercise 9.B.7: no limit as `T → ∞`** (MWG, p. 302). Player 1's SPNE payoff `W T`
alternates between `v − c` (odd `T`) and `0` (even `T`), so it has no limit. -/
theorem exercise_9_B_7_limit : ¬ ∃ L, Tendsto G.W atTop (𝓝 L) := by
  rintro ⟨L, hL⟩
  have hcv := G.c_lt_v
  have h2 : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨b, fun a ha => by omega⟩
  have h2' : Tendsto (fun n : ℕ => 2 * n + 1) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨b, fun a ha => by omega⟩
  have he : (G.W ∘ fun n : ℕ => 2 * n) = fun _ => 0 := by
    funext n; simp [W]
  have ho : (G.W ∘ fun n : ℕ => 2 * n + 1) = fun _ => G.v - G.c := by
    funext n; simp [W, Nat.add_mod]
  have l0 := hL.comp h2
  have l1 := hL.comp h2'
  rw [he] at l0
  rw [ho] at l1
  have := tendsto_nhds_unique (tendsto_const_nhds (x := (0 : ℝ))) l0
  have := tendsto_nhds_unique (tendsto_const_nhds (x := G.v - G.c)) l1
  linarith

theorem live_top (hT : G.T = ⊤) (n : ℕ) : G.Live n := by
  simp [Live, hT]

/-- The stationary split profile of the infinite game: player 1 (index `0`, proposing in even
periods) offers `v − c − a`, player 2 offers `a`; each accepts exactly the offers of at least
her own value as the next proposer. -/
noncomputable def splitProfile (a : ℝ) : BargainingProfile :=
  threshold (fun n => if n % 2 = 0 then G.v - G.c - a else a)

/-- **Exercise 9.B.13: every split is an SPNE outcome** (MWG, p. 303). In the infinite game,
for every `a ∈ [0, v − c]` the split profile is an SPNE with immediate agreement, giving
player 1 the payoff `a` and player 2 the payoff `v − c − a`. -/
theorem splitProfile_isSPNE (hT : G.T = ⊤) {a : ℝ} (ha : a ∈ Set.Icc 0 (G.v - G.c)) :
    G.IsSPNE (G.splitProfile a) ∧ G.value (G.splitProfile a) [] 0 = (a : WithBot ℝ) ∧
      G.value (G.splitProfile a) [] 1 = ((G.v - G.c - a : ℝ) : WithBot ℝ) ∧
      (G.splitProfile a).resp [] ((G.splitProfile a).prop []) = true := by
  have hc := G.c_pos
  refine ⟨G.threshold_isSPNE (fun n => ?_) (fun n _ => ?_) (fun n _ hn => absurd (G.live_top hT
    (n + 1)) hn), ?_, ?_, ?_⟩
  · split_ifs <;> constructor <;> linarith [ha.1, ha.2]
  · rcases Nat.mod_two_eq_zero_or_one n with h | h
    · have : (n + 1) % 2 = 1 := by omega
      simp [h, this]
    · have : (n + 1) % 2 = 0 := by omega
      simp [h, this]
  · have := (G.value_threshold (fun n => if n % 2 = 0 then G.v - G.c - a else a)
      (h := []) (G.live_top hT 0)).1
    simp only [List.length_nil, Nat.zero_mod, ↓reduceIte, sub_sub_cancel] at this
    exact this
  · exact (G.value_threshold (fun n => if n % 2 = 0 then G.v - G.c - a else a)
      (h := []) (G.live_top hT 0)).2
  · simp [splitProfile, threshold]

/-- **Exercise 9.B.13** (MWG, p. 303). The infinite horizon game with offer cost `c ∈ (0, v)`
and no discounting. (1) In every SPNE the payoffs `a` of player 1 and `b` of player 2 are real
numbers with `a, b ≥ 0` and `a + b ≤ v − c` (`spne_bounds`: the same holds in every subgame).
(2) Conversely, for every `a ∈ [0, v − c]` there is an SPNE with immediate agreement and payoffs
`(a, v − c − a)` (`splitProfile_isSPNE`). -/
theorem exercise_9_B_13 (hT : G.T = ⊤) :
    (∀ σ, G.IsSPNE σ → ∃ a b : ℝ, G.value σ [] 0 = a ∧ G.value σ [] 1 = b ∧ 0 ≤ a ∧ 0 ≤ b ∧
      a + b ≤ G.v - G.c) ∧
    ∀ a ∈ Set.Icc 0 (G.v - G.c), ∃ σ, G.IsSPNE σ ∧ G.value σ [] 0 = (a : WithBot ℝ) ∧
      G.value σ [] 1 = ((G.v - G.c - a : ℝ) : WithBot ℝ) ∧ σ.resp [] (σ.prop []) = true := by
  refine ⟨fun σ hσ => ?_, fun a ha => ⟨_, G.splitProfile_isSPNE hT ha⟩⟩
  exact G.spne_bounds hσ [] (fun _ h => by simp at h) (G.live_top hT 0)

/-- **Exercise 9.B.13: player 1's SPNE payoffs** (MWG, p. 303). In the infinite game the set of
player 1's SPNE payoffs is exactly `[0, v − c]`; so is player 2's. -/
theorem exercise_9_B_13_payoffs (hT : G.T = ⊤) :
    {x : ℝ | ∃ σ, G.IsSPNE σ ∧ G.value σ [] 0 = (x : WithBot ℝ)} = Set.Icc 0 (G.v - G.c) ∧
      {x : ℝ | ∃ σ, G.IsSPNE σ ∧ G.value σ [] 1 = (x : WithBot ℝ)} =
        Set.Icc 0 (G.v - G.c) := by
  refine ⟨Set.ext fun x => ⟨fun ⟨σ, hσ, hx⟩ => ?_, fun hx => ?_⟩,
    Set.ext fun x => ⟨fun ⟨σ, hσ, hx⟩ => ?_, fun hx => ?_⟩⟩
  · obtain ⟨a, b, ha, _, ha0, hb0, hab⟩ := (G.exercise_9_B_13 hT).1 σ hσ
    rw [ha] at hx
    have := WithBot.coe_injective hx
    subst this
    exact ⟨ha0, by linarith⟩
  · exact ⟨_, (G.splitProfile_isSPNE hT hx).1, (G.splitProfile_isSPNE hT hx).2.1⟩
  · obtain ⟨a, b, _, hb, ha0, hb0, hab⟩ := (G.exercise_9_B_13 hT).1 σ hσ
    rw [hb] at hx
    have := WithBot.coe_injective hx
    subst this
    exact ⟨hb0, by linarith⟩
  · have hx' : G.v - G.c - x ∈ Set.Icc 0 (G.v - G.c) := ⟨by linarith [hx.2], by linarith [hx.1]⟩
    refine ⟨_, (G.splitProfile_isSPNE hT hx').1, ?_⟩
    rw [(G.splitProfile_isSPNE hT hx').2.2.1]
    congr 1
    ring

/-- **Exercise 9.B.13: the SPNE is not unique** (MWG, p. 303): in the infinite game there are
SPNE giving player 1 the payoffs `0` and `v − c > 0`. -/
theorem exercise_9_B_13_not_unique (hT : G.T = ⊤) :
    ∃ σ₁ σ₂, G.IsSPNE σ₁ ∧ G.IsSPNE σ₂ ∧ G.value σ₁ [] 0 ≠ G.value σ₂ [] 0 := by
  have hcv := G.c_lt_v
  have h0 := G.splitProfile_isSPNE hT (a := 0) ⟨le_rfl, by linarith⟩
  have h1 := G.splitProfile_isSPNE hT (a := G.v - G.c) ⟨by linarith, le_rfl⟩
  refine ⟨_, _, h0.1, h1.1, ?_⟩
  rw [h0.2.1, h1.2.1]
  intro he
  have := WithBot.coe_injective he
  linarith

/-- **Exercise 9.B.13: immediate agreement when `v < 2c`** (MWG, p. 303). If `v < 2c`, then in
every SPNE (of any horizon) the offer made at every live feasible node is accepted: after a
rejection the two payoffs add up to at most `v − c`, so the first proposer would get at most
`v − 2c < 0`. -/
theorem spne_immediate {σ : BargainingProfile} (hσ : G.IsSPNE σ) {h : List ℝ}
    (hv : G.ValidHist h) (hl : G.Live h.length) (hc2 : G.v < 2 * G.c) :
    σ.resp h (σ.prop h) = true := by
  by_contra hr
  have hr' : σ.resp h (σ.prop h) = false := by simpa using hr
  have hc := G.c_pos
  obtain ⟨a, b, ha, _, ha0, _, _⟩ := G.spne_bounds hσ h hv hl
  have h1 := G.value_eq_respValue σ hl (proposer h.length)
  rw [G.respValue_reject hr', offerCost_proposer, ha] at h1
  have hy₀ := hσ.1 h
  by_cases hl2 : G.Live (σ.prop h :: h).length
  · obtain ⟨a', b', _, hb', ha0', _, hab'⟩ :=
      G.spne_bounds hσ _ (G.validHist_cons hv hy₀) hl2
    rw [List.length_cons, proposer_succ, other_other] at hb'
    rw [hb', ← WithBot.coe_add] at h1
    have := WithBot.coe_injective h1
    linarith
  · rw [G.value_of_not_live hl2, ← WithBot.coe_zero, ← WithBot.coe_add] at h1
    have := WithBot.coe_injective h1
    linarith

/-- **One-stage deviation principle with offer costs.** A feasible profile `σ` is an SPNE if
its payoffs are given by real numbers `Vf h i` and at every live node no one-stage deviation
pays: the proposer cannot gain by any offer (given the responses and `Vf` afterwards), and the
responder accepts only offers of at least her `Vf` after rejection and rejects only offers of
at most it. -/
theorem isSPNE_of_oneStage {σ : BargainingProfile} (hF : G.Feasible σ)
    (Vf : List ℝ → Fin 2 → ℝ) (hval : ∀ h i, G.value σ h i = (Vf h i : WithBot ℝ))
    (hP : ∀ h, G.Live h.length → ∀ y ∈ Set.Icc 0 G.v,
      (if σ.resp h y = true then G.v - y - G.c else -G.c + Vf (y :: h) (proposer h.length)) ≤
        Vf h (proposer h.length))
    (hRa : ∀ h, G.Live h.length → ∀ y ∈ Set.Icc 0 G.v, σ.resp h y = true →
      Vf (y :: h) (other (proposer h.length)) ≤ y)
    (hRr : ∀ h, G.Live h.length → ∀ y ∈ Set.Icc 0 G.v, σ.resp h y = false →
      y ≤ Vf (y :: h) (other (proposer h.length))) : G.IsSPNE σ := by
  refine ⟨hF, fun i σ' hσ' hdev h _ hl => ?_⟩
  -- the responder's `Vf` dominates both the offer and the continuation
  have hresp : ∀ h, G.Live h.length → ∀ y ∈ Set.Icc 0 G.v,
      y ≤ (G.respValue σ h y (other (proposer h.length))) ∧
      (Vf (y :: h) (other (proposer h.length)) : WithBot ℝ) ≤
        G.respValue σ h y (other (proposer h.length)) := by
    intro h hl y hy
    cases hr : σ.resp h y with
    | true =>
      rw [G.respValue_accept hr, share_other, offerCost_other, sub_zero]
      exact ⟨le_rfl, WithBot.coe_le_coe.2 (hRa h hl y hy hr)⟩
    | false =>
      rw [G.respValue_reject hr, offerCost_other, neg_zero, WithBot.coe_zero, zero_add, hval]
      exact ⟨WithBot.coe_le_coe.2 (hRr h hl y hy hr), le_rfl⟩
  have hVr' : ∀ h, G.Live h.length →
      σ.prop h ≤ Vf h (other (proposer h.length)) ∧
        Vf (σ.prop h :: h) (other (proposer h.length)) ≤ Vf h (other (proposer h.length)) := by
    intro h hl
    have := hresp h hl (σ.prop h) (hF h)
    rw [← G.value_eq_respValue σ hl, hval] at this
    exact ⟨WithBot.coe_le_coe.1 this.1, WithBot.coe_le_coe.1 this.2⟩
  have hbound : ∀ h, G.value σ' h i ≤ (Vf h i : WithBot ℝ) := by
    refine G.value_le_of_bound (fun h => Vf h i) (fun h hl' => ?_) (fun h' hl' hr => ?_)
      (fun h' hl' hr => ?_)
    · have := hval h i
      rw [G.value_of_not_live hl'] at this
      exact (WithBot.coe_eq_zero.1 this.symm).ge
    · by_cases hp : proposer h'.length = i
      · have hr' : σ.resp h' (σ'.prop h') = true := (hdev.2 h' _ hp).symm.trans hr
        have := hP h' hl' _ (hσ' h')
        rw [hr'] at this
        subst hp
        rw [share_proposer, offerCost_proposer]
        simpa using this
      · rcases eq_or_eq_other (proposer h'.length) i with h1 | h1
        · exact absurd h1.symm hp
        · subst h1
          rw [share_other, offerCost_other, sub_zero, hdev.1 h' hp]
          exact (hVr' h' hl').1
    · by_cases hp : proposer h'.length = i
      · have hr' : σ.resp h' (σ'.prop h') = false := (hdev.2 h' _ hp).symm.trans hr
        have := hP h' hl' _ (hσ' h')
        rw [hr'] at this
        subst hp
        rw [offerCost_proposer]
        simpa using this
      · rcases eq_or_eq_other (proposer h'.length) i with h1 | h1
        · exact absurd h1.symm hp
        · subst h1
          rw [offerCost_other, neg_zero, zero_add, hdev.1 h' hp]
          exact (hVr' h' hl').2
  refine ⟨by rw [hval]; exact hbound h, fun y hy => ?_⟩
  by_cases hp : proposer h.length = i
  · have hr' := hdev.2 h y hp
    cases hry : σ.resp h y with
    | true =>
      rw [G.respValue_accept hry, G.respValue_accept (hr'.trans hry)]
    | false =>
      rw [G.respValue_reject hry, G.respValue_reject (hr'.trans hry), hval]
      gcongr
      exact hbound _
  · rcases eq_or_eq_other (proposer h.length) i with h1 | h1
    · exact absurd h1.symm hp
    · subst h1
      have := hresp h hl y hy
      cases hry : σ'.resp h y with
      | true =>
        rw [G.respValue_accept hry, share_other, offerCost_other, sub_zero]
        exact this.1
      | false =>
        rw [G.respValue_reject hry, offerCost_other, neg_zero, WithBot.coe_zero, zero_add]
        exact (hbound _).trans this.2

/-- The regime of the delay equilibrium after the first rejection: player 1 gets `v − c` if
the first offer was `0`, and `0` otherwise. -/
noncomputable def delayReg (h : List ℝ) : ℝ := if h.getLast? = some 0 then G.v - G.c else 0

/-- Payoffs in the delay equilibrium: at the root `(v − 2c, 0)`; after the first offer `y`
player 1 gets `delayReg` and player 2 gets the rest of `v − c`. -/
noncomputable def delayV (h : List ℝ) (i : Fin 2) : ℝ :=
  if h = [] then (if i = 0 then G.v - 2 * G.c else 0)
  else (if i = 0 then G.delayReg h else G.v - G.c - G.delayReg h)

/-- **An SPNE with delay** (Exercise 9.B.13, MWG, p. 303). Player 1 offers `0` and player 2
rejects it; after that, a stationary split profile is played in which player 1 gets `v − c` if
the first offer was `0` and `0` otherwise (and player 2 accepts a first offer `y ≠ 0` exactly
when `y ≥ v − c`). -/
noncomputable def delayProfile : BargainingProfile where
  prop h := if h = [] then 0 else G.delayV h (other (proposer h.length))
  resp h y := if h = [] then decide (y ≠ 0 ∧ G.v - G.c ≤ y)
    else decide (G.delayV h (other (proposer h.length)) ≤ y)

theorem delayV_cons {h : List ℝ} (hh : h ≠ []) (y : ℝ) (i : Fin 2) :
    G.delayV (y :: h) i = G.delayV h i := by
  obtain ⟨b, l, rfl⟩ := List.exists_cons_of_ne_nil hh
  simp [delayV, delayReg, List.getLast?_cons_cons]

theorem delayV_add {h : List ℝ} (hh : h ≠ []) (i : Fin 2) :
    G.delayV h i + G.delayV h (other i) = G.v - G.c := by
  rcases Fin.exists_fin_two.1 ⟨i, rfl⟩ with rfl | rfl
  · simp only [delayV, hh, ↓reduceIte, show other 0 = 1 from rfl, one_ne_zero]
    ring
  · simp only [delayV, hh, ↓reduceIte, show other 1 = 0 from rfl, one_ne_zero]
    ring

theorem delayV_nil_one : G.delayV [] 1 = 0 := by simp [delayV]

theorem delayReg_mem (h : List ℝ) : G.delayReg h ∈ Set.Icc 0 (G.v - G.c) := by
  have := G.c_lt_v
  unfold delayReg
  split_ifs <;> constructor <;> linarith

/-- **Exercise 9.B.13: agreement need not be immediate** (MWG, p. 303). If `v ≥ 2c`, the
infinite game has an SPNE in which player 1's first offer is rejected; player 1 then gets
`v − 2c` and player 2 gets `0`. -/
theorem delayProfile_isSPNE (hT : G.T = ⊤) (hc2 : 2 * G.c ≤ G.v) :
    G.IsSPNE G.delayProfile ∧ G.delayProfile.resp [] (G.delayProfile.prop []) = false ∧
      G.value G.delayProfile [] 0 = ((G.v - 2 * G.c : ℝ) : WithBot ℝ) ∧
      G.value G.delayProfile [] 1 = ((0 : ℝ) : WithBot ℝ) := by
  have hc := G.c_pos
  have hl : ∀ n, G.Live n := G.live_top hT
  have hp0 : proposer ([] : List ℝ).length = 0 := rfl
  have ho0 : other (0 : Fin 2) = 1 := rfl
  have hreg := G.delayReg_mem
  have hres0 : ∀ y, G.delayProfile.resp [] y = decide (y ≠ 0 ∧ G.v - G.c ≤ y) := fun y => by
    simp only [delayProfile, ↓reduceIte]
  have hresc : ∀ h, h ≠ [] → ∀ y, G.delayProfile.resp h y =
      decide (G.delayV h (other (proposer h.length)) ≤ y) := fun h hh y => by
    simp only [delayProfile, hh, ↓reduceIte]
  have hprop0 : G.delayProfile.prop [] = 0 := by simp only [delayProfile, ↓reduceIte]
  have hpropc : ∀ h, h ≠ [] → G.delayProfile.prop h = G.delayV h (other (proposer h.length)) :=
    fun h hh => by simp only [delayProfile, hh, ↓reduceIte]
  have hreg0 : G.delayReg [0] = G.v - G.c := by simp [delayReg]
  have hregy : ∀ y, y ≠ 0 → G.delayReg [y] = 0 := fun y hy => by simp [delayReg, hy]
  have hV1 : ∀ y, G.delayV [y] 1 = G.v - G.c - G.delayReg [y] := fun y => by simp [delayV]
  have hV0 : ∀ y, G.delayV [y] 0 = G.delayReg [y] := fun y => by simp [delayV]
  -- values at nodes after the first offer: immediate agreement
  have hvalc : ∀ h, h ≠ [] → ∀ i, G.value G.delayProfile h i = (G.delayV h i : WithBot ℝ) := by
    intro h hh i
    have hacc : G.delayProfile.resp h (G.delayProfile.prop h) = true := by
      rw [hresc h hh, hpropc h hh]; simp
    rw [G.value_eq_respValue _ (hl _), G.respValue_accept hacc, hpropc h hh]
    rcases eq_or_eq_other (proposer h.length) i with h1 | h1
    · subst h1
      rw [share_proposer, offerCost_proposer]
      have := G.delayV_add hh (proposer h.length)
      congr 1
      linarith
    · subst h1
      rw [share_other, offerCost_other, sub_zero]
  have hrej0 : G.delayProfile.resp [] (G.delayProfile.prop []) = false := by
    rw [hres0, hprop0]; simp
  have hval : ∀ h i, G.value G.delayProfile h i = (G.delayV h i : WithBot ℝ) := by
    intro h i
    by_cases hh : h = []
    · subst hh
      rw [G.value_eq_respValue _ (hl _), G.respValue_reject hrej0, hprop0,
        hvalc _ (List.cons_ne_nil _ _), ← WithBot.coe_add]
      congr 1
      rcases Fin.exists_fin_two.1 ⟨i, rfl⟩ with rfl | rfl
      · rw [← hp0, offerCost_proposer, hp0, hV0, hreg0]
        simp only [delayV, ↓reduceIte]
        ring
      · rw [show (1 : Fin 2) = other (proposer ([] : List ℝ).length) from rfl, offerCost_other,
          ← show (1 : Fin 2) = other (proposer ([] : List ℝ).length) from rfl, hV1, hreg0,
          delayV_nil_one]
        ring
    · exact hvalc h hh i
  refine ⟨G.isSPNE_of_oneStage (fun h => ?_) G.delayV hval (fun h _ y hy => ?_)
    (fun h _ y hy hr => ?_) (fun h _ y hy hr => ?_), hrej0, ?_, ?_⟩
  · by_cases hh : h = []
    · subst hh
      rw [hprop0]
      exact ⟨le_rfl, by linarith⟩
    · rw [hpropc h hh]
      have h1 := hreg h
      rcases Fin.exists_fin_two.1 ⟨other (proposer h.length), rfl⟩ with h2 | h2 <;>
        rw [h2] <;> simp only [delayV, hh, ↓reduceIte, one_ne_zero] <;> constructor <;>
        linarith [h1.1, h1.2]
  · by_cases hh : h = []
    · subst hh
      rw [hp0, hV0]
      have hy1 := hreg [y]
      by_cases hr : G.delayProfile.resp [] y = true
      · simp only [hr, ↓reduceIte]
        rw [hres0] at hr
        have := (of_decide_eq_true hr).2
        simp only [delayV, ↓reduceIte]
        linarith
      · simp only [hr, Bool.false_eq_true, ↓reduceIte]
        simp only [delayV, ↓reduceIte]
        linarith [hy1.2]
    · rw [G.delayV_cons hh]
      have hs := G.delayV_add hh (proposer h.length)
      by_cases hr : G.delayProfile.resp h y = true
      · simp only [hr, ↓reduceIte]
        rw [hresc h hh] at hr
        have := of_decide_eq_true hr
        linarith
      · simp only [hr, Bool.false_eq_true, ↓reduceIte]
        linarith
  · by_cases hh : h = []
    · subst hh
      rw [hres0] at hr
      have := of_decide_eq_true hr
      rw [hp0, ho0, hV1, hregy y this.1]
      linarith [this.2]
    · rw [G.delayV_cons hh]
      rw [hresc h hh] at hr
      exact of_decide_eq_true hr
  · by_cases hh : h = []
    · subst hh
      rw [hres0] at hr
      have := of_decide_eq_false hr
      rw [hp0, ho0, hV1]
      by_cases hy0 : y = 0
      · subst hy0
        rw [hreg0]
        simp
      · rw [hregy y hy0]
        push Not at this
        linarith [this hy0]
    · rw [G.delayV_cons hh]
      rw [hresc h hh] at hr
      have := of_decide_eq_false hr
      linarith
  · rw [hval]
    simp [delayV]
  · rw [hval, delayV_nil_one]

/-- **Exercise 9.B.13: delay** (MWG, p. 303). In the infinite game, if `v < 2c` every SPNE has
immediate agreement at every feasible node; if `v ≥ 2c` some SPNE has the first offer
rejected. -/
theorem exercise_9_B_13_delay (hT : G.T = ⊤) :
    (G.v < 2 * G.c → ∀ σ, G.IsSPNE σ → ∀ h, G.ValidHist h → σ.resp h (σ.prop h) = true) ∧
      (2 * G.c ≤ G.v → ∃ σ, G.IsSPNE σ ∧ σ.resp [] (σ.prop []) = false) :=
  ⟨fun hc2 _ hσ _ hv => G.spne_immediate hσ hv (G.live_top hT _) hc2,
    fun hc2 => ⟨_, (G.delayProfile_isSPNE hT hc2).1, (G.delayProfile_isSPNE hT hc2).2.1⟩⟩

end OfferCostGame

/-- **Exercise 9.B.13: an instance** (MWG, p. 303): `v = 2`, `c = 1`, infinite horizon; the
split profiles with `a = 0` and `a = 1` are both SPNE. -/
theorem exercise_9_B_13_instance :
    ∃ G : OfferCostGame, G.T = ⊤ ∧ G.IsSPNE (G.splitProfile 0) ∧ G.IsSPNE (G.splitProfile 1) :=
  ⟨⟨2, 1, ⊤, by norm_num, by norm_num⟩, rfl,
    (OfferCostGame.splitProfile_isSPNE _ rfl ⟨le_rfl, by norm_num⟩).1,
    (OfferCostGame.splitProfile_isSPNE _ rfl ⟨by norm_num, by norm_num⟩).1⟩

/-- **Exercise 9.B.13: instances of the delay dichotomy** (MWG, p. 303): with `v = 2`, `c = 1`
(so `v ≥ 2c`) the delay profile is an SPNE with the first offer rejected; with `v = 3/2`,
`c = 1` (so `v < 2c`) every SPNE agrees at once, and an SPNE exists. -/
theorem exercise_9_B_13_delay_instance :
    (∃ G : OfferCostGame, G.T = ⊤ ∧ 2 * G.c ≤ G.v ∧ G.IsSPNE G.delayProfile ∧
      G.delayProfile.resp [] (G.delayProfile.prop []) = false) ∧
    ∃ G : OfferCostGame, G.T = ⊤ ∧ G.v < 2 * G.c ∧ G.IsSPNE (G.splitProfile 0) ∧
      ∀ σ, G.IsSPNE σ → ∀ h, G.ValidHist h → σ.resp h (σ.prop h) = true := by
  refine ⟨⟨⟨2, 1, ⊤, by norm_num, by norm_num⟩, rfl, by norm_num, ?_, ?_⟩,
    ⟨⟨3 / 2, 1, ⊤, by norm_num, by norm_num⟩, rfl, by norm_num, ?_, ?_⟩⟩
  · exact (OfferCostGame.delayProfile_isSPNE _ rfl (by norm_num)).1
  · exact (OfferCostGame.delayProfile_isSPNE _ rfl (by norm_num)).2.1
  · exact (OfferCostGame.splitProfile_isSPNE _ rfl ⟨le_rfl, by norm_num⟩).1
  · exact (OfferCostGame.exercise_9_B_13_delay _ rfl).1 (by norm_num)

/-- **Exercise 9.B.7: an instance** (MWG, p. 302): `v = 2`, `c = 1`, three periods; the unique
SPNE gives player 1 the payoff `v − c = 1`. -/
theorem exercise_9_B_7_instance :
    ∃ G : OfferCostGame, G.T = 3 ∧ G.IsSPNE (OfferCostGame.threshold (fun n => G.W (3 - n - 1))) ∧
      ∀ σ, G.IsSPNE σ → G.value σ [] 0 = ((1 : ℝ) : WithBot ℝ) := by
  refine ⟨⟨2, 1, 3, by norm_num, by norm_num⟩, rfl, ?_, fun σ hσ => ?_⟩
  · exact (OfferCostGame.exercise_9_B_7 _ (N := 3) rfl).1
  · rw [((OfferCostGame.exercise_9_B_7 _ (N := 3) rfl).2 σ hσ).2.1]
    norm_num [OfferCostGame.W]

end MWG.DynamicGames

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# A war of attrition in a declining market

MWG, Exercise 9.B.11 (p. 303). Two firms, A (index `0`) and B (index `1`), are in a market in
periods `t = 0, 1, 2, …`. At the start of each period each active firm stays in or exits
(simultaneously if both are active); exit is permanent. A firm earns the duopoly profit
`duo i t` in a period in which both firms are in, the monopoly profit `mono i t` in a period in
which it is alone, and `0` once out; payoffs are undiscounted sums.

The model is an infinite-horizon game. A firm's information at a decision node is the date
`t` and the rival's status: `none` (the rival is still in) or `some u` (the rival exited at
the start of period `u < t`); this is the whole history, since before an exit every move was
"stay". A profile (`AttritionProfile`) gives each firm's move at every such node, and
`IsSPNE` is subgame perfection at every node (`t`, both in) and (`t`, alone after the rival's
exit at `u`). A firm that never exits earns `⊥` (`−∞`): its profits eventually fall below
every negative bound in the exercise.

* `jointValue_eq`, `monoValue_eq`: the recursions of the payoffs.
* `monopoly_spne`: in an SPNE a monopolist with profits positive up to `L` and negative after
  stays exactly in the periods `t ≤ L` (the truncation: from `L + 1` on staying is
  dominated, then backward induction over finitely many periods).
* `exercise_9_B_11`: with MWG's profits `105 − 10t`, `10.5 − t` (duopoly) and `510 − 25t`,
  `51 − 2t` (monopoly) there is a unique SPNE. While both are in, A stays exactly in
  periods `t ≤ 10` and B exactly in periods `t ≤ 25`; as a monopolist A stays exactly for
  `t ≤ 20` and B for `t ≤ 25`. The outcome: both stay in periods `0, …, 10`, A exits at the
  start of period 11, B is a monopolist in periods `11, …, 25` and exits at the start of
  period 26. Payoffs: `605` for A and `285.5` for B.
-/

namespace MWG.DynamicGames

/-- A two-firm war of attrition: duopoly and monopoly profits in each period. -/
structure AttritionGame where
  /-- Firm `i`'s profit in period `t` when both firms are in. -/
  duo : Fin 2 → ℕ → ℝ
  /-- Firm `i`'s profit in period `t` when it is alone in the market. -/
  mono : Fin 2 → ℕ → ℝ

/-- A strategy profile of the war of attrition: `stay i t none` is firm `i`'s move (`true` =
stay in) at date `t` when both firms are in; `stay i t (some u)` its move at date `t` when the
rival exited at the start of period `u < t`. -/
structure AttritionProfile where
  /-- The moves. -/
  stay : Fin 2 → ℕ → Option ℕ → Bool

namespace AttritionGame

open BargainingGame (other other_ne ne_other)

variable (A : AttritionGame)

/-- Firm `i`'s payoff from the node at date `t` where it is alone in the market (the rival
exited at `u`): monopoly profits until it exits. -/
noncomputable def monoValue (s : AttritionProfile) (i : Fin 2) (t u : ℕ) : WithBot ℝ :=
  firstStop (fun k => s.stay i (t + k) (some u)) (fun k => A.mono i (t + k)) (fun _ => 0)

/-- Firm `i`'s payoff from the node at date `t` where both firms are in: duopoly profits until
the first exit; if then only the rival exits, monopoly profits from that period on. -/
noncomputable def jointValue (s : AttritionProfile) (i : Fin 2) (t : ℕ) : WithBot ℝ :=
  firstStop (fun k => s.stay 0 (t + k) none && s.stay 1 (t + k) none) (fun k => A.duo i (t + k))
    (fun k => if s.stay i (t + k) none = true then
      ((A.mono i (t + k) : ℝ) : WithBot ℝ) + A.monoValue s i (t + k + 1) (t + k) else 0)

theorem monoValue_eq (s : AttritionProfile) (i : Fin 2) (t u : ℕ) :
    A.monoValue s i t u = if s.stay i t (some u) = true then
      ((A.mono i t : ℝ) : WithBot ℝ) + A.monoValue s i (t + 1) u else 0 := by
  unfold monoValue
  rw [firstStop_eq]
  simp only [add_zero]
  congr 3
  · funext k
    rw [show t + (k + 1) = t + 1 + k by omega]
  · funext k
    rw [show t + (k + 1) = t + 1 + k by omega]

/-- Firm `i`'s payoff from staying in at the date-`t` node where both firms are in. -/
noncomputable def stayValue (s : AttritionProfile) (i : Fin 2) (t : ℕ) : WithBot ℝ :=
  if s.stay (other i) t none = true then ((A.duo i t : ℝ) : WithBot ℝ) + A.jointValue s i (t + 1)
  else ((A.mono i t : ℝ) : WithBot ℝ) + A.monoValue s i (t + 1) t

theorem jointValue_eq (s : AttritionProfile) (i : Fin 2) (t : ℕ) :
    A.jointValue s i t = if s.stay i t none = true then A.stayValue s i t else 0 := by
  unfold stayValue
  conv_lhs => unfold jointValue
  rw [firstStop_eq]
  simp only [add_zero]
  have hj : firstStop (fun k => s.stay 0 (t + (k + 1)) none && s.stay 1 (t + (k + 1)) none)
      (fun k => A.duo i (t + (k + 1))) (fun k => if s.stay i (t + (k + 1)) none = true then
        ((A.mono i (t + (k + 1)) : ℝ) : WithBot ℝ) +
          A.monoValue s i (t + (k + 1) + 1) (t + (k + 1)) else 0) = A.jointValue s i (t + 1) := by
    unfold jointValue
    congr 1
    · funext k
      rw [show t + (k + 1) = t + 1 + k by omega]
    · funext k
      rw [show t + (k + 1) = t + 1 + k by omega]
    · funext k
      rw [show t + (k + 1) = t + 1 + k by omega]
  rw [hj]
  fin_cases i <;> cases h0 : s.stay 0 t none <;> cases h1 : s.stay 1 t none <;>
    simp [h0, h1, other]

/-- **Definition 9.B.2 for the war of attrition** (MWG, pp. 275 and 303). A subgame perfect
Nash equilibrium: at every node where both firms are in (date `t`) and at every node where firm
`i` is alone (date `t`, rival out since `u < t`), no firm gains by changing its strategy. -/
def IsSPNE (s : AttritionProfile) : Prop :=
  ∀ i (s' : AttritionProfile), s'.stay (other i) = s.stay (other i) → ∀ t,
    A.jointValue s' i t ≤ A.jointValue s i t ∧ ∀ u < t, A.monoValue s' i t u ≤ A.monoValue s i t u

/-- Changing firm `i`'s move at the single node `(t₀, e₀)`. -/
def setStay (s : AttritionProfile) (i : Fin 2) (t₀ : ℕ) (e₀ : Option ℕ) (b : Bool) :
    AttritionProfile :=
  ⟨fun j t e => if j = i ∧ t = t₀ ∧ e = e₀ then b else s.stay j t e⟩

theorem setStay_other (s : AttritionProfile) (i : Fin 2) (t₀ : ℕ) (e₀ : Option ℕ) (b : Bool) :
    (setStay s i t₀ e₀ b).stay (other i) = s.stay (other i) := by
  funext t e
  simp [setStay, other_ne]

theorem setStay_self (s : AttritionProfile) (i : Fin 2) (t₀ : ℕ) (e₀ : Option ℕ) (b : Bool) :
    (setStay s i t₀ e₀ b).stay i t₀ e₀ = b := by
  simp [setStay]

theorem monoValue_setStay (s : AttritionProfile) (i : Fin 2) {t₀ : ℕ} {e₀ : Option ℕ}
    (b : Bool) {t u : ℕ} (h : t₀ < t ∨ e₀ ≠ some u) :
    A.monoValue (setStay s i t₀ e₀ b) i t u = A.monoValue s i t u := by
  have hk : ∀ k, (setStay s i t₀ e₀ b).stay i (t + k) (some u) = s.stay i (t + k) (some u) := by
    intro k
    simp only [setStay]
    split_ifs with hc
    · rcases h with h | h
      · omega
      · exact absurd hc.2.2.symm h
    · rfl
  simp only [monoValue, hk]

theorem jointValue_setStay (s : AttritionProfile) (i : Fin 2) {t₀ : ℕ} (b : Bool) {t : ℕ}
    (h : t₀ < t) : A.jointValue (setStay s i t₀ none b) i t = A.jointValue s i t := by
  have hk : ∀ j k, (setStay s i t₀ none b).stay j (t + k) none = s.stay j (t + k) none := by
    intro j k
    simp only [setStay]
    split_ifs with hc
    · omega
    · rfl
  have hm : ∀ r u, A.monoValue (setStay s i t₀ none b) i r u = A.monoValue s i r u :=
    fun r u => A.monoValue_setStay s i b (Or.inr (by simp))
  simp only [jointValue, hk, hm]

theorem stayValue_setStay (s : AttritionProfile) (i : Fin 2) (t : ℕ) (b : Bool) :
    A.stayValue (setStay s i t none b) i t = A.stayValue s i t := by
  unfold stayValue
  rw [setStay_other, A.jointValue_setStay s i b (Nat.lt_succ_self t),
    A.monoValue_setStay s i b (Or.inr (by simp))]

/-- In an SPNE a firm stays in when staying is strictly profitable (both firms in). -/
theorem stay_of_pos {s : AttritionProfile} (hs : A.IsSPNE s) {i : Fin 2} {t : ℕ}
    (h : 0 < A.stayValue s i t) : s.stay i t none = true := by
  by_contra hc
  have hc' : s.stay i t none = false := by simpa using hc
  have := (hs i (setStay s i t none true) (setStay_other s i t none true) t).1
  rw [A.jointValue_eq, A.jointValue_eq, setStay_self, hc', A.stayValue_setStay] at this
  simp only [↓reduceIte, Bool.false_eq_true] at this
  exact absurd this (not_le.2 h)

/-- In an SPNE a firm exits when staying is strictly unprofitable (both firms in). -/
theorem exit_of_neg {s : AttritionProfile} (hs : A.IsSPNE s) {i : Fin 2} {t : ℕ}
    (h : A.stayValue s i t < 0) : s.stay i t none = false := by
  by_contra hc
  have hc' : s.stay i t none = true := by simpa using hc
  have := (hs i (setStay s i t none false) (setStay_other s i t none false) t).1
  rw [A.jointValue_eq, A.jointValue_eq, setStay_self, hc'] at this
  simp only [↓reduceIte, Bool.false_eq_true] at this
  exact absurd this (not_le.2 h)

/-- In an SPNE a monopolist stays in when staying is strictly profitable. -/
theorem monoStay_of_pos {s : AttritionProfile} (hs : A.IsSPNE s) {i : Fin 2} {t u : ℕ}
    (hu : u < t) (h : 0 < ((A.mono i t : ℝ) : WithBot ℝ) + A.monoValue s i (t + 1) u) :
    s.stay i t (some u) = true := by
  by_contra hc
  have hc' : s.stay i t (some u) = false := by simpa using hc
  have := (hs i (setStay s i t (some u) true) (setStay_other s i t (some u) true) t).2 u hu
  rw [A.monoValue_eq (setStay s i t (some u) true) i t u, A.monoValue_eq s i t u, setStay_self,
    hc',
    A.monoValue_setStay s i true (Or.inl (Nat.lt_succ_self t))] at this
  simp only [↓reduceIte, Bool.false_eq_true] at this
  exact absurd this (not_le.2 h)

/-- In an SPNE a monopolist exits when staying is strictly unprofitable. -/
theorem monoExit_of_neg {s : AttritionProfile} (hs : A.IsSPNE s) {i : Fin 2} {t u : ℕ}
    (hu : u < t) (h : ((A.mono i t : ℝ) : WithBot ℝ) + A.monoValue s i (t + 1) u < 0) :
    s.stay i t (some u) = false := by
  by_contra hc
  have hc' : s.stay i t (some u) = true := by simpa using hc
  have := (hs i (setStay s i t (some u) false) (setStay_other s i t (some u) false) t).2 u hu
  rw [A.monoValue_eq (setStay s i t (some u) false) i t u, A.monoValue_eq s i t u, setStay_self,
    hc'] at this
  simp only [↓reduceIte, Bool.false_eq_true] at this
  exact absurd this (not_le.2 h)

/-- An upper bound on a monopolist's payoff by a one-stage condition. -/
theorem monoValue_le (s : AttritionProfile) (i : Fin 2) (t u : ℕ) (M : ℕ → ℝ)
    (hrec : ∀ r, A.mono i r + M (r + 1) ≤ M r) (h0 : ∀ r, 0 ≤ M r) :
    A.monoValue s i t u ≤ (M t : WithBot ℝ) := by
  have := firstStop_le (c := fun k => s.stay i (t + k) (some u)) (f := fun k => A.mono i (t + k))
    (g := fun _ => 0) (fun k => M (t + k)) (fun k _ => by rw [← add_assoc]; exact hrec _)
    (fun k _ => WithBot.coe_le_coe.2 (h0 _))
  unfold monoValue
  simpa using this

/-- **The monopolist's problem** (MWG, Exercise 9.B.11, p. 303). If firm `i`'s monopoly profit
is positive up to date `L` and negative afterwards, and `M` is its value of staying exactly up to
`L` (`M t = mono t + M (t + 1)` for `t ≤ L`, `M t = 0` after `L`), then in every SPNE a
monopolist `i` (rival out since `u`) stays exactly at the dates `t ≤ L` and earns `M t`. From
`L + 1` on, staying is dominated (all later profits are negative); before, backward induction
over the finitely many dates `t ≤ L` applies. -/
theorem monopoly_spne {s : AttritionProfile} (hs : A.IsSPNE s) (i : Fin 2) (L : ℕ)
    (M : ℕ → ℝ) (hpos : ∀ t ≤ L, 0 < A.mono i t) (hneg : ∀ t, L < t → A.mono i t < 0)
    (hM : ∀ t ≤ L, M t = A.mono i t + M (t + 1)) (hM0 : ∀ t, L < t → M t = 0)
    (hnn : ∀ t, 0 ≤ M t) :
    ∀ u t, u < t → s.stay i t (some u) = decide (t ≤ L) ∧ A.monoValue s i t u = (M t : ℝ) := by
  intro u
  have hrec : ∀ r, A.mono i r + M (r + 1) ≤ M r := by
    intro r
    by_cases hr : r ≤ L
    · rw [hM r hr]
    · rw [hM0 r (by omega), hM0 (r + 1) (by omega)]
      linarith [hneg r (by omega)]
  -- after `L`: exit
  have hlate : ∀ t, L < t → u < t →
      s.stay i t (some u) = decide (t ≤ L) ∧ A.monoValue s i t u = (M t : ℝ) := by
    intro t hLt hut
    have hle := A.monoValue_le s i (t + 1) u M hrec hnn
    rw [hM0 (t + 1) (by omega)] at hle
    have hex : s.stay i t (some u) = false := by
      refine A.monoExit_of_neg hs hut (lt_of_le_of_lt (add_le_add le_rfl hle) ?_)
      rw [← WithBot.coe_add, ← WithBot.coe_zero, WithBot.coe_lt_coe]
      linarith [hneg t hLt]
    refine ⟨by rw [hex]; simp [not_le.2 hLt], ?_⟩
    rw [A.monoValue_eq, hex, hM0 t hLt]
    simp
  -- up to `L`: stay, by backward induction
  have key : ∀ d t, t + d = L + 1 → u < t →
      s.stay i t (some u) = decide (t ≤ L) ∧ A.monoValue s i t u = (M t : ℝ) := by
    intro d
    induction d with
    | zero => intro t ht hut; exact hlate t (by omega) hut
    | succ d ih =>
      intro t ht hut
      have hn := (ih (t + 1) (by omega) (by omega)).2
      have htL : t ≤ L := by omega
      have hst : s.stay i t (some u) = true := by
        refine A.monoStay_of_pos hs hut ?_
        rw [hn, ← WithBot.coe_add, ← WithBot.coe_zero, WithBot.coe_lt_coe]
        linarith [hpos t htL, hnn (t + 1)]
      refine ⟨by rw [hst]; simp [htL], ?_⟩
      rw [A.monoValue_eq, hst, hn, hM t htL]
      simp
  intro t hut
  by_cases hLt : L < t
  · exact hlate t hLt hut
  · exact key (L + 1 - t) t (by omega) hut

/-- A monopolist who stays exactly at the dates `t ≤ L` earns `M t`. -/
theorem monoValue_cutoff (s : AttritionProfile) (i : Fin 2) (u L : ℕ) (M : ℕ → ℝ)
    (hstay : ∀ t, s.stay i t (some u) = decide (t ≤ L))
    (hM : ∀ t ≤ L, M t = A.mono i t + M (t + 1)) (hM0 : ∀ t, L < t → M t = 0) :
    ∀ t, A.monoValue s i t u = (M t : ℝ) := by
  have key : ∀ d t, t + d = L + 1 → A.monoValue s i t u = (M t : ℝ) := by
    intro d
    induction d with
    | zero =>
      intro t ht
      rw [A.monoValue_eq, hstay, hM0 t (by omega)]
      simp [show ¬ t ≤ L by omega]
    | succ d ih =>
      intro t ht
      rw [A.monoValue_eq, hstay, ih (t + 1) (by omega), hM t (by omega)]
      simp [show t ≤ L by omega]
  intro t
  by_cases hLt : L < t
  · rw [A.monoValue_eq, hstay, hM0 t hLt]
    simp [not_le.2 hLt]
  · exact key (L + 1 - t) t (by omega)

/-- An upper bound on a firm's payoff from a node where both firms are in, by a one-stage
condition from date `t` on. -/
theorem jointValue_le (s : AttritionProfile) (i : Fin 2) (t : ℕ) (V : ℕ → ℝ)
    (hc : ∀ r, t ≤ r → s.stay 0 r none = true → s.stay 1 r none = true →
      A.duo i r + V (r + 1) ≤ V r)
    (hg : ∀ r, t ≤ r → s.stay i r none = true → s.stay (other i) r none = false →
      ((A.mono i r : ℝ) : WithBot ℝ) + A.monoValue s i (r + 1) r ≤ (V r : WithBot ℝ))
    (h0 : ∀ r, t ≤ r → 0 ≤ V r) : A.jointValue s i t ≤ (V t : WithBot ℝ) := by
  have := firstStop_le (c := fun k => s.stay 0 (t + k) none && s.stay 1 (t + k) none)
    (f := fun k => A.duo i (t + k))
    (g := fun k => if s.stay i (t + k) none = true then
      ((A.mono i (t + k) : ℝ) : WithBot ℝ) + A.monoValue s i (t + k + 1) (t + k) else 0)
    (fun k => V (t + k)) (fun k hk => ?_) (fun k hk => ?_)
  · unfold jointValue
    simpa using this
  · simp only [Bool.and_eq_true] at hk
    rw [← add_assoc]
    exact hc _ (by omega) hk.1 hk.2
  · by_cases hi : s.stay i (t + k) none = true
    · have ho : s.stay (other i) (t + k) none = false := by
        fin_cases i
        · simp_all [other]
        · simp_all [other]
      simp only [hi, ↓reduceIte]
      exact hg _ (by omega) hi ho
    · simp only [hi, Bool.false_eq_true, ↓reduceIte]
      exact WithBot.coe_le_coe.2 (h0 _ (by omega))

end AttritionGame

open BargainingGame (other) in
/-- **The declining market of Exercise 9.B.11** (MWG, p. 303). Duopoly profits `105 − 10t`
(firm A, index `0`) and `10.5 − t` (firm B, index `1`); monopoly profits `510 − 25t` and
`51 − 2t`. -/
noncomputable def declining : AttritionGame where
  duo i t := if i = 0 then 105 - 10 * (t : ℝ) else 21 / 2 - t
  mono i t := if i = 0 then 510 - 25 * (t : ℝ) else 51 - 2 * t

/-- The last date at which monopoly profit is positive: `20` for A, `25` for B. -/
def decL (i : Fin 2) : ℕ := if i = 0 then 20 else 25

/-- A monopolist's value of staying exactly up to `decL i`. -/
noncomputable def decM (i : Fin 2) (t : ℕ) : ℝ :=
  if i = 0 then (if t ≤ 20 then (21 - t) * (520 - 25 * t) / 2 else 0)
  else (if t ≤ 25 then (26 - t) ^ 2 else 0)

/-- A's SPNE value when both firms are in at date `t`. -/
noncomputable def decVA (t : ℕ) : ℝ := if t ≤ 10 then 5 * (11 - t) ^ 2 else 0

/-- B's SPNE value when both firms are in at date `t`. -/
noncomputable def decVB (t : ℕ) : ℝ :=
  if t ≤ 10 then (11 - t) ^ 2 / 2 + 225 else if t ≤ 25 then (26 - t) ^ 2 else 0

/-- The SPNE of Exercise 9.B.11: while both are in, A stays iff `t ≤ 10` and B iff `t ≤ 25`;
alone, A stays iff `t ≤ 20` and B iff `t ≤ 25`. -/
def attritionSPNE : AttritionProfile :=
  ⟨fun i t e => match e with
    | none => decide (t ≤ if i = 0 then 10 else 25)
    | some _ => decide (t ≤ decL i)⟩

theorem decM_rec (i : Fin 2) (t : ℕ) (ht : t ≤ decL i) :
    decM i t = declining.mono i t + decM i (t + 1) := by
  fin_cases i
  · simp only [decL, Fin.zero_eta, Fin.isValue, ↓reduceIte] at ht
    rcases Nat.lt_or_ge t 20 with h | h
    · simp only [decM, declining, Fin.zero_eta, Fin.isValue, ↓reduceIte, ht,
        show t + 1 ≤ 20 by omega]
      push_cast
      ring
    · simp only [decM, declining, Fin.zero_eta, Fin.isValue, ↓reduceIte, show t = 20 by omega]
      norm_num
  · simp only [decL, Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte] at ht
    rcases Nat.lt_or_ge t 25 with h | h
    · simp only [decM, declining, Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte, ht,
        show t + 1 ≤ 25 by omega]
      push_cast
      ring
    · simp only [decM, declining, Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte,
        show t = 25 by omega]
      norm_num

theorem decM_late (i : Fin 2) (t : ℕ) (ht : decL i < t) : decM i t = 0 := by
  fin_cases i
  · simp only [decL, Fin.zero_eta, Fin.isValue, ↓reduceIte] at ht
    simp [decM, show ¬ t ≤ 20 by omega]
  · simp only [decL, Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte] at ht
    simp [decM, show ¬ t ≤ 25 by omega]

theorem decM_nonneg (i : Fin 2) (t : ℕ) : 0 ≤ decM i t := by
  fin_cases i
  · simp only [decM, Fin.zero_eta, Fin.isValue, ↓reduceIte]
    split_ifs with h
    · have : (t : ℝ) ≤ 20 := by exact_mod_cast h
      apply div_nonneg _ (by norm_num)
      apply mul_nonneg <;> linarith
    · exact le_rfl
  · simp only [decM, Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte]
    split_ifs
    · positivity
    · exact le_rfl

theorem decMono_pos (i : Fin 2) (t : ℕ) (ht : t ≤ decL i) : 0 < declining.mono i t := by
  fin_cases i
  · simp only [decL, Fin.zero_eta, Fin.isValue, ↓reduceIte] at ht
    have : (t : ℝ) ≤ 20 := by exact_mod_cast ht
    simp only [declining, Fin.zero_eta, Fin.isValue, ↓reduceIte]
    linarith
  · simp only [decL, Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte] at ht
    have : (t : ℝ) ≤ 25 := by exact_mod_cast ht
    simp only [declining, Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte]
    linarith

theorem decMono_neg (i : Fin 2) (t : ℕ) (ht : decL i < t) : declining.mono i t < 0 := by
  fin_cases i
  · simp only [decL, Fin.zero_eta, Fin.isValue, ↓reduceIte] at ht
    have : (21 : ℝ) ≤ t := by exact_mod_cast ht
    simp only [declining, Fin.zero_eta, Fin.isValue, ↓reduceIte]
    linarith
  · simp only [decL, Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte] at ht
    have : (26 : ℝ) ≤ t := by exact_mod_cast ht
    simp only [declining, Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte]
    linarith

theorem decM_hrec (i : Fin 2) (r : ℕ) : declining.mono i r + decM i (r + 1) ≤ decM i r := by
  by_cases hr : r ≤ decL i
  · rw [decM_rec i r hr]
  · rw [decM_late i r (by omega), decM_late i (r + 1) (by omega)]
    linarith [decMono_neg i r (by omega)]

/-- **Exercise 9.B.11: the monopoly subgames** (MWG, p. 303). In every SPNE, a firm alone in the
market stays exactly while its monopoly profit is positive (A for `t ≤ 20`, B for `t ≤ 25`). -/
theorem exercise_9_B_11_monopoly {s : AttritionProfile} (hs : declining.IsSPNE s) (i : Fin 2) :
    ∀ u t, u < t → s.stay i t (some u) = decide (t ≤ decL i) ∧
      declining.monoValue s i t u = (decM i t : ℝ) :=
  declining.monopoly_spne hs i (decL i) (decM i) (decMono_pos i) (decMono_neg i) (decM_rec i)
    (decM_late i) (decM_nonneg i)

theorem decVA_rec (t : ℕ) (ht : t ≤ 10) : decVA t = declining.duo 0 t + decVA (t + 1) := by
  rcases Nat.lt_or_ge t 10 with h | h
  · simp only [decVA, declining, ↓reduceIte, ht, show t + 1 ≤ 10 by omega]
    push_cast
    ring
  · simp only [decVA, declining, ↓reduceIte, show t = 10 by omega]
    norm_num

theorem decVB_rec (t : ℕ) (ht : t ≤ 10) : decVB t = declining.duo 1 t + decVB (t + 1) := by
  rcases Nat.lt_or_ge t 10 with h | h
  · simp only [decVB, declining, ↓reduceIte, ht, show t + 1 ≤ 10 by omega, one_ne_zero]
    push_cast
    ring
  · simp only [decVB, declining, ↓reduceIte, show t = 10 by omega, one_ne_zero]
    norm_num

theorem decVA_late (t : ℕ) (ht : 10 < t) : decVA t = 0 := by
  simp [decVA, show ¬ t ≤ 10 by omega]

theorem decVB_late (t : ℕ) (ht : 10 < t) : decVB t = decM 1 t := by
  simp [decVB, decM, show ¬ t ≤ 10 by omega]

theorem decVA_pos (t : ℕ) (ht : t ≤ 10) : 0 < decVA t := by
  have : (t : ℝ) ≤ 10 := by exact_mod_cast ht
  simp only [decVA, ht, ↓reduceIte]
  have : 0 < (11 - (t : ℝ)) := by linarith
  positivity

theorem decVB_pos (t : ℕ) (ht : t ≤ 10) : 0 < decVB t := by
  simp only [decVB, ht, ↓reduceIte]
  positivity

theorem decM1_pos (t : ℕ) (ht : t ≤ 25) : 0 < decM 1 t := by
  have : (t : ℝ) ≤ 25 := by exact_mod_cast ht
  simp only [decM, one_ne_zero, ↓reduceIte, ht]
  have : 0 < (26 - (t : ℝ)) := by linarith
  positivity

theorem attr_none (i : Fin 2) (t : ℕ) :
    attritionSPNE.stay i t none = decide (t ≤ if i = 0 then 10 else 25) := rfl

theorem attr_some (i : Fin 2) (t u : ℕ) :
    attritionSPNE.stay i t (some u) = decide (t ≤ decL i) := rfl

/-- The values at a date `t` when both firms use the SPNE moves at `t` and the continuation
values are the SPNE values. -/
theorem dec_jv_step (s : AttritionProfile) (t : ℕ) (h0 : s.stay 0 t none = decide (t ≤ 10))
    (h1 : s.stay 1 t none = decide (t ≤ 25))
    (hA : t ≤ 10 → declining.jointValue s 0 (t + 1) = (decVA (t + 1) : WithBot ℝ))
    (hB : t ≤ 10 → declining.jointValue s 1 (t + 1) = (decVB (t + 1) : WithBot ℝ))
    (hm : 10 < t → t ≤ 25 → declining.monoValue s 1 (t + 1) t = (decM 1 (t + 1) : WithBot ℝ)) :
    declining.jointValue s 0 t = (decVA t : WithBot ℝ) ∧
      declining.jointValue s 1 t = (decVB t : WithBot ℝ) := by
  rw [declining.jointValue_eq, declining.jointValue_eq]
  unfold AttritionGame.stayValue
  have o0 : BargainingGame.other 0 = 1 := rfl
  have o1 : BargainingGame.other 1 = 0 := rfl
  rw [o0, o1, h0, h1]
  by_cases ht10 : t ≤ 10
  · simp only [ht10, show t ≤ 25 by omega, decide_true, ↓reduceIte]
    rw [hA ht10, hB ht10, ← WithBot.coe_add, ← WithBot.coe_add, decVA_rec t ht10,
      decVB_rec t ht10]
    exact ⟨rfl, rfl⟩
  · by_cases ht25 : t ≤ 25
    · simp only [ht10, ht25, decide_true, decide_false, ↓reduceIte, Bool.false_eq_true]
      rw [hm (by omega) ht25, ← WithBot.coe_add, decVA_late t (by omega),
        decVB_late t (by omega), decM_rec 1 t (by simpa [decL] using ht25)]
      exact ⟨rfl, rfl⟩
    · simp only [ht10, ht25, decide_false, ↓reduceIte, Bool.false_eq_true]
      rw [decVA_late t (by omega), decVB_late t (by omega), decM_late 1 t
        (by simp [decL]; omega)]
      exact ⟨rfl, rfl⟩

theorem decDuo_neg (i : Fin 2) (t : ℕ) (ht : 11 ≤ t) : declining.duo i t < 0 := by
  have : (11 : ℝ) ≤ t := by exact_mod_cast ht
  fin_cases i
  · simp only [declining, Fin.zero_eta, Fin.isValue, ↓reduceIte]
    linarith
  · simp only [declining, Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte]
    linarith

theorem decB_mid (t : ℕ) (h11 : 11 ≤ t) (h20 : t ≤ 20) :
    0 < declining.duo 1 t + decVB (t + 1) := by
  rw [decVB_late _ (by omega)]
  have a : (11 : ℝ) ≤ t := by exact_mod_cast h11
  have b : (t : ℝ) ≤ 20 := by exact_mod_cast h20
  simp only [declining, decM, Fin.isValue, one_ne_zero, ↓reduceIte, show t + 1 ≤ 25 by omega]
  push_cast
  nlinarith

/-- The monopoly values in the SPNE profile. -/
theorem attritionSPNE_mono (i : Fin 2) (t u : ℕ) :
    declining.monoValue attritionSPNE i t u = (decM i t : WithBot ℝ) :=
  declining.monoValue_cutoff attritionSPNE i u (decL i) (decM i) (fun _ => rfl) (decM_rec i)
    (decM_late i) t

/-- The values in the SPNE profile at the nodes where both firms are in. -/
theorem attritionSPNE_values (t : ℕ) :
    declining.jointValue attritionSPNE 0 t = (decVA t : WithBot ℝ) ∧
      declining.jointValue attritionSPNE 1 t = (decVB t : WithBot ℝ) := by
  have h0 : ∀ t, attritionSPNE.stay 0 t none = decide (t ≤ 10) := fun t => by simp [attr_none]
  have h1 : ∀ t, attritionSPNE.stay 1 t none = decide (t ≤ 25) := fun t => by simp [attr_none]
  have key : ∀ d t, t + d = 26 → declining.jointValue attritionSPNE 0 t = (decVA t : WithBot ℝ) ∧
      declining.jointValue attritionSPNE 1 t = (decVB t : WithBot ℝ) := by
    intro d
    induction d with
    | zero =>
      intro t ht
      exact dec_jv_step _ t (h0 t) (h1 t) (fun h => by omega) (fun h => by omega)
        (fun _ h => by omega)
    | succ d ih =>
      intro t ht
      exact dec_jv_step _ t (h0 t) (h1 t) (fun _ => (ih (t + 1) (by omega)).1)
        (fun _ => (ih (t + 1) (by omega)).2) (fun _ _ => attritionSPNE_mono 1 (t + 1) t)
  by_cases ht : t ≤ 26
  · exact key (26 - t) t (by omega)
  · exact dec_jv_step _ t (h0 t) (h1 t) (fun h => by omega) (fun h => by omega)
      (fun _ h => by omega)

/-- **Exercise 9.B.11: the SPNE profile is an SPNE** (MWG, p. 303). -/
theorem attritionSPNE_isSPNE : declining.IsSPNE attritionSPNE := by
  intro i s' hs' t
  refine ⟨?_, fun u _ => ?_⟩
  · rcases Fin.exists_fin_two.1 ⟨i, rfl⟩ with rfl | rfl
    · rw [(attritionSPNE_values t).1]
      have ho : s'.stay 1 = attritionSPNE.stay 1 := hs'
      refine declining.jointValue_le s' 0 t decVA (fun r _ _ _ => ?_) (fun r _ _ hr => ?_)
        (fun r _ => ?_)
      · by_cases hr : r ≤ 10
        · rw [decVA_rec r hr]
        · rw [decVA_late r (by omega), decVA_late (r + 1) (by omega)]
          linarith [decDuo_neg 0 r (by omega)]
      · change s'.stay 1 r none = false at hr
        rw [ho, attr_none] at hr
        have hr26 : 25 < r := by simpa using hr
        have hle := declining.monoValue_le s' 0 (r + 1) r (decM 0) (decM_hrec 0)
          (decM_nonneg 0)
        refine (add_le_add le_rfl hle).trans ?_
        rw [← WithBot.coe_add, WithBot.coe_le_coe, decVA_late r (by omega),
          ← decM_late 0 r (by simp [decL]; omega)]
        exact decM_hrec 0 r
      · unfold decVA; split_ifs <;> positivity
    · rw [(attritionSPNE_values t).2]
      have ho : s'.stay 0 = attritionSPNE.stay 0 := hs'
      refine declining.jointValue_le s' 1 t decVB (fun r _ hr _ => ?_) (fun r _ _ hr => ?_)
        (fun r _ => ?_)
      · rw [ho, attr_none] at hr
        have hr10 : r ≤ 10 := by simpa using hr
        rw [decVB_rec r hr10]
      · change s'.stay 0 r none = false at hr
        rw [ho, attr_none] at hr
        have hr10 : 10 < r := by simpa using hr
        have hle := declining.monoValue_le s' 1 (r + 1) r (decM 1) (decM_hrec 1)
          (decM_nonneg 1)
        refine (add_le_add le_rfl hle).trans ?_
        rw [← WithBot.coe_add, WithBot.coe_le_coe, decVB_late r hr10]
        exact decM_hrec 1 r
      · unfold decVB; split_ifs <;> positivity
  · rw [attritionSPNE_mono]
    exact declining.monoValue_le s' i t u (decM i) (decM_hrec i) (decM_nonneg i)

/-- **Exercise 9.B.11: uniqueness** (MWG, p. 303). In every SPNE, while both firms are in, A
stays exactly at the dates `t ≤ 10` and B exactly at the dates `t ≤ 25`, and the payoffs from
date `t` are `decVA t` and `decVB t`. From date 26 on staying is dominated for both firms
(all profits are negative); backward induction over dates `25, …, 0` does the rest: at dates
21-25 staying is dominated for A, so B stays; at dates 11-20 staying is strictly better for B
whatever A does, so A exits; at dates `t ≤ 10` both strictly prefer to stay. -/
theorem exercise_9_B_11_unique {s : AttritionProfile} (hs : declining.IsSPNE s) (t : ℕ) :
    s.stay 0 t none = decide (t ≤ 10) ∧ s.stay 1 t none = decide (t ≤ 25) ∧
      declining.jointValue s 0 t = (decVA t : WithBot ℝ) ∧
      declining.jointValue s 1 t = (decVB t : WithBot ℝ) := by
  have hm : ∀ i t, declining.monoValue s i (t + 1) t = (decM i (t + 1) : WithBot ℝ) :=
    fun i t => (exercise_9_B_11_monopoly hs i t (t + 1) (Nat.lt_succ_self t)).2
  have o0 : BargainingGame.other 0 = 1 := rfl
  have o1 : BargainingGame.other 1 = 0 := rfl
  -- from date 26 on: both exit
  have hle0 : ∀ i r, 26 ≤ r → declining.jointValue s i r ≤ ((0 : ℝ) : WithBot ℝ) := by
    intro i r hr
    refine declining.jointValue_le s i r (fun _ => 0) (fun r' hr' _ _ => ?_)
      (fun r' hr' _ _ => ?_) (fun _ _ => le_rfl)
    · linarith [decDuo_neg i r' (by omega)]
    · have hle := declining.monoValue_le s i (r' + 1) r' (decM i) (decM_hrec i) (decM_nonneg i)
      refine (add_le_add le_rfl hle).trans ?_
      rw [← WithBot.coe_add, WithBot.coe_le_coe, ← decM_late i r' (by fin_cases i <;>
        simp [decL] <;> omega)]
      exact decM_hrec i r'
  have hlate : ∀ t, 26 ≤ t → s.stay 0 t none = decide (t ≤ 10) ∧
      s.stay 1 t none = decide (t ≤ 25) ∧
      declining.jointValue s 0 t = (decVA t : WithBot ℝ) ∧
      declining.jointValue s 1 t = (decVB t : WithBot ℝ) := by
    intro t ht
    have hex : ∀ i, s.stay i t none = false := by
      intro i
      refine declining.exit_of_neg hs ?_
      unfold AttritionGame.stayValue
      split_ifs
      · refine lt_of_le_of_lt (add_le_add le_rfl (hle0 i (t + 1) (by omega))) ?_
        rw [← WithBot.coe_add, ← WithBot.coe_zero, WithBot.coe_lt_coe]
        linarith [decDuo_neg i t (by omega)]
      · rw [hm, ← WithBot.coe_add, ← WithBot.coe_zero, WithBot.coe_lt_coe,
          decM_late i (t + 1) (by fin_cases i <;> simp [decL] <;> omega)]
        linarith [decMono_neg i t (by fin_cases i <;> simp [decL] <;> omega)]
    have e0 : s.stay 0 t none = decide (t ≤ 10) := by rw [hex 0]; simp; omega
    have e1 : s.stay 1 t none = decide (t ≤ 25) := by rw [hex 1]; simp; omega
    exact ⟨e0, e1, dec_jv_step s t e0 e1 (fun h => by omega) (fun h => by omega)
      (fun _ h => by omega)⟩
  -- dates `t ≤ 25`, by backward induction
  have step : ∀ t, t ≤ 25 → declining.jointValue s 0 (t + 1) = (decVA (t + 1) : WithBot ℝ) →
      declining.jointValue s 1 (t + 1) = (decVB (t + 1) : WithBot ℝ) →
      s.stay 0 t none = decide (t ≤ 10) ∧ s.stay 1 t none = decide (t ≤ 25) := by
    intro t ht hA hB
    have hS0 : declining.stayValue s 0 t = if s.stay 1 t none = true then
        ((declining.duo 0 t + decVA (t + 1) : ℝ) : WithBot ℝ)
        else ((declining.mono 0 t + decM 0 (t + 1) : ℝ) : WithBot ℝ) := by
      unfold AttritionGame.stayValue
      rw [o0, hA, hm, WithBot.coe_add, WithBot.coe_add]
    have hS1 : declining.stayValue s 1 t = if s.stay 0 t none = true then
        ((declining.duo 1 t + decVB (t + 1) : ℝ) : WithBot ℝ)
        else ((declining.mono 1 t + decM 1 (t + 1) : ℝ) : WithBot ℝ) := by
      unfold AttritionGame.stayValue
      rw [o1, hB, hm, WithBot.coe_add, WithBot.coe_add]
    have hBmono : 0 < declining.mono 1 t + decM 1 (t + 1) := by
      rw [← decM_rec 1 t (by simp [decL]; omega)]
      exact decM1_pos t ht
    by_cases h20 : 20 < t
    · -- dates 21-25: staying is dominated for A; then B stays
      have eA : s.stay 0 t none = false := by
        refine declining.exit_of_neg hs ?_
        rw [hS0, ← WithBot.coe_zero]
        split_ifs
        · rw [WithBot.coe_lt_coe, decVA_late (t + 1) (by omega)]
          linarith [decDuo_neg 0 t (by omega)]
        · rw [WithBot.coe_lt_coe, decM_late 0 (t + 1) (by simp [decL]; omega)]
          linarith [decMono_neg 0 t (by simp [decL]; omega)]
      have eB : s.stay 1 t none = true := by
        refine declining.stay_of_pos hs ?_
        rw [hS1, eA, ← WithBot.coe_zero]
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact WithBot.coe_lt_coe.2 hBmono
      rw [eA, eB]
      exact ⟨by simp; omega, by simp; omega⟩
    · -- dates up to 20: staying is strictly better for B whatever A does
      have eB : s.stay 1 t none = true := by
        refine declining.stay_of_pos hs ?_
        rw [hS1, ← WithBot.coe_zero]
        split_ifs
        · refine WithBot.coe_lt_coe.2 ?_
          by_cases h10 : t ≤ 10
          · rw [← decVB_rec t h10]; exact decVB_pos t h10
          · exact decB_mid t (by omega) (by omega)
        · exact WithBot.coe_lt_coe.2 hBmono
      by_cases h10 : t ≤ 10
      · have eA : s.stay 0 t none = true := by
          refine declining.stay_of_pos hs ?_
          rw [hS0, eB, ← WithBot.coe_zero]
          simp only [↓reduceIte]
          rw [WithBot.coe_lt_coe, ← decVA_rec t h10]
          exact decVA_pos t h10
        rw [eA, eB]
        exact ⟨by simp [h10], by simp; omega⟩
      · have eA : s.stay 0 t none = false := by
          refine declining.exit_of_neg hs ?_
          rw [hS0, eB, ← WithBot.coe_zero]
          simp only [↓reduceIte]
          rw [WithBot.coe_lt_coe, decVA_late (t + 1) (by omega)]
          linarith [decDuo_neg 0 t (by omega)]
        rw [eA, eB]
        exact ⟨by simp; omega, by simp; omega⟩
  have key : ∀ d t, t + d = 26 → s.stay 0 t none = decide (t ≤ 10) ∧
      s.stay 1 t none = decide (t ≤ 25) ∧
      declining.jointValue s 0 t = (decVA t : WithBot ℝ) ∧
      declining.jointValue s 1 t = (decVB t : WithBot ℝ) := by
    intro d
    induction d with
    | zero => intro t ht; exact hlate t (by omega)
    | succ d ih =>
      intro t ht
      have hn := ih (t + 1) (by omega)
      have hst := step t (by omega) hn.2.2.1 hn.2.2.2
      exact ⟨hst.1, hst.2, dec_jv_step s t hst.1 hst.2 (fun _ => hn.2.2.1)
        (fun _ => hn.2.2.2) (fun _ _ => hm 1 t)⟩
  by_cases ht : t ≤ 26
  · exact key (26 - t) t (by omega)
  · exact hlate t (by omega)

/-- **Exercise 9.B.11** (MWG, p. 303). The declining-market war of attrition has a unique SPNE,
`attritionSPNE`: while both firms are in, A stays exactly in periods `t ≤ 10` and B exactly in
periods `t ≤ 25`; a firm alone stays exactly while its monopoly profit is positive (A for
`t ≤ 20`, B for `t ≤ 25`), whatever the rival's exit date. The SPNE outcome: both firms stay in
periods `0, …, 10`, A exits at the start of period 11, and B is a monopolist in periods
`11, …, 25` and exits at the start of period 26. Payoffs: `605` for A and `285.5` for B. -/
theorem exercise_9_B_11 :
    declining.IsSPNE attritionSPNE ∧
      ∀ s, declining.IsSPNE s →
        (∀ i t e, (∀ u, e = some u → u < t) → s.stay i t e = attritionSPNE.stay i t e) ∧
        declining.jointValue s 0 0 = ((605 : ℝ) : WithBot ℝ) ∧
        declining.jointValue s 1 0 = ((571 / 2 : ℝ) : WithBot ℝ) := by
  refine ⟨attritionSPNE_isSPNE, fun s hs => ⟨fun i t e he => ?_, ?_, ?_⟩⟩
  · rcases e with _ | u
    · have := exercise_9_B_11_unique hs t
      rcases Fin.exists_fin_two.1 ⟨i, rfl⟩ with rfl | rfl
      · rw [this.1, attr_none]; simp
      · rw [this.2.1, attr_none]; simp
    · rw [(exercise_9_B_11_monopoly hs i u t (he u rfl)).1, attr_some]
  · rw [(exercise_9_B_11_unique hs 0).2.2.1]
    norm_num [decVA]
  · rw [(exercise_9_B_11_unique hs 0).2.2.2]
    norm_num [decVB]

end MWG.DynamicGames

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Bagwell's commitment game with observation noise

MWG, Exercise 9.C.7 and Figure 9.Ex.2 (pp. 304-305). Player 1 (`0`) chooses `B` (`0`) or `T`
(`1`); player 2 (`1`) chooses `D` (`0`) or `U` (`1`). Payoffs `(u₁, u₂)`: `(B, D) = (4, 2)`,
`(B, U) = (1, 1)`, `(T, D) = (5, 1)`, `(T, U) = (2, 2)`.

* (a) `bagA`, player 2 observing player 1's move: `exercise_9_C_7a`. The unique SPNE is
  `(B; D after B, U after T)`; the Nash equilibria (behaviour strategies) are exactly: player 1
  plays `B`, player 2 plays `D` after `B` and `D` after `T` with probability at most `2/3`; or
  player 1 plays `T`, player 2 plays `U` after `T` and `D` after `B` with probability at most
  `1/3` (so `(T; U, U)` is a further Nash equilibrium).
* (b) `bagB`, player 2 not observing: `exercise_9_C_7b`. `T` strictly dominates `B`, and the
  unique Nash equilibrium (mixed ones included) is `(T, U)`.
* (c) `bagC p`, player 2 observing a signal that is correct with probability `p ∈ (0, 1)`:
  nature moves after player 1 and chooses the signal; player 2 has two information sets
  (signal `B`, signal `T`). `exercise_9_C_7c`: `(T; U, U)` with beliefs on `T` is a weak PBE
  for every `p`, and it is the unique weak PBE in which player 1 plays a pure strategy
  (`exercise_9_C_7c_pure_unique`). The printed claim that the weak PBE is unique holds exactly
  when `1/3 < p < 2/3` (`exercise_9_C_7c_unique`); for `p ≥ 2/3` and for `p ≤ 1/3` there are
  further weak PBE in which player 1 mixes (`exercise_9_C_7c_mixed_high`,
  `exercise_9_C_7c_mixed_low`; docs/corrections.md).
-/

namespace MWG.DynamicGames

open MWG.NoncooperativeGames MWG.NoncooperativeGames.ExtensiveForm

/-- Payoffs `(u₁, u₂)` of Figure 9.Ex.2 when player 1 plays `a` (`0` = B, `1` = T) and player
2 plays `d` (`0` = D, `1` = U). -/
def bagPay (i : Fin 2) (d a : Fin 2) : ℝ :=
  if a = 0 then (if d = 0 then ![4, 2] i else ![1, 1] i)
  else (if d = 0 then ![5, 1] i else ![2, 2] i)

/-- Terminal payoffs of the games of Exercise 9.C.7(a)-(b): the node `[d, a]`. -/
def bagPayAB (i : Fin 2) (z : List (Fin 2)) : ℝ :=
  match z with
  | [d, a] => bagPay i d a
  | _ => 0

/-- **Exercise 9.C.7(a), Figure 9.Ex.2** (MWG, pp. 304-305). Player 2 observes player 1's
move: information sets `0` (player 1), `1` (player 2 after `B`), `2` (player 2 after `T`). -/
def bagA : ExtensiveForm (Fin 2) (Fin 2) (Fin 3) where
  nodes := {[], [0], [1], [0, 0], [1, 0], [0, 1], [1, 1]}
  nil_mem := by decide
  tail_mem := by decide
  info x := if x = [] then 0 else if x = [0] then 1 else 2
  avail _ := Finset.univ
  avail_spec := by decide
  info_surj := by decide
  player := ![some 0, some 1, some 1]
  natureProb _ _ := 0
  nature_nonneg := fun k hk => absurd hk (by fin_cases k <;> simp)
  nature_zero := fun k hk => absurd hk (by fin_cases k <;> simp)
  nature_sum := fun k hk => absurd hk (by fin_cases k <;> simp)
  payoff := bagPayAB

/-- **Exercise 9.C.7(b)** (MWG, p. 304). Player 2 does not observe player 1's move: one
information set `1 = {[0], [1]}` for player 2. -/
def bagB : ExtensiveForm (Fin 2) (Fin 2) (Fin 2) where
  nodes := {[], [0], [1], [0, 0], [1, 0], [0, 1], [1, 1]}
  nil_mem := by decide
  tail_mem := by decide
  info x := if x = [] then 0 else 1
  avail _ := Finset.univ
  avail_spec := by decide
  info_surj := by decide
  player := ![some 0, some 1]
  natureProb _ _ := 0
  nature_nonneg := fun k hk => absurd hk (by fin_cases k <;> simp)
  nature_zero := fun k hk => absurd hk (by fin_cases k <;> simp)
  nature_sum := fun k hk => absurd hk (by fin_cases k <;> simp)
  payoff := bagPayAB

/-- Continuation payoffs in `bagA`. -/
theorem bagA_cont (f : Fin 3 → Fin 2 → ℝ) (i : Fin 2) :
    cont bagA f [0, 0] i = bagPay i 0 0 ∧ cont bagA f [1, 0] i = bagPay i 1 0 ∧
    cont bagA f [0, 1] i = bagPay i 0 1 ∧ cont bagA f [1, 1] i = bagPay i 1 1 ∧
    cont bagA f [0] i = f 1 0 * bagPay i 0 0 + f 1 1 * bagPay i 1 0 ∧
    cont bagA f [1] i = f 2 0 * bagPay i 0 1 + f 2 1 * bagPay i 1 1 ∧
    cont bagA f [] i = f 0 0 * (f 1 0 * bagPay i 0 0 + f 1 1 * bagPay i 1 0) +
      f 0 1 * (f 2 0 * bagPay i 0 1 + f 2 1 * bagPay i 1 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [cont_unfold, bagA, bagPayAB, Fin.sum_univ_two]

/-- Continuation payoffs in `bagB`. -/
theorem bagB_cont (f : Fin 2 → Fin 2 → ℝ) (i : Fin 2) :
    cont bagB f [] i = f 0 0 * (f 1 0 * bagPay i 0 0 + f 1 1 * bagPay i 1 0) +
      f 0 1 * (f 1 0 * bagPay i 0 1 + f 1 1 * bagPay i 1 1) := by
  simp [cont_unfold, bagB, bagPayAB, Fin.sum_univ_two]

/-- The moves of a profile of `bagA`. -/
theorem bagA_assemble_eq (F : Fin 2 → Fin 3 → Fin 2 → ℝ) :
    bagA.assemble F = fun k => F (![0, 1, 1] k) k := by
  funext k
  rcases (by decide : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2) k with rfl | rfl | rfl <;>
    exact bagA.assemble_of_some _ rfl

/-- The moves of a profile of `bagB`. -/
theorem bagB_assemble_eq (F : Fin 2 → Fin 2 → Fin 2 → ℝ) :
    bagB.assemble F = fun k => F k k := by
  funext k
  rcases (by decide : ∀ k : Fin 2, k = 0 ∨ k = 1) k with rfl | rfl <;>
    exact bagB.assemble_of_some _ rfl

/-- Facts about a behaviour profile of `bagA`. -/
theorem bagA_behavior {F : Fin 2 → Fin 3 → Fin 2 → ℝ} (hF : IsBehaviorProfile bagA F) :
    (∀ a, 0 ≤ F 0 0 a) ∧ F 0 0 0 + F 0 0 1 = 1 ∧ (∀ a, 0 ≤ F 1 1 a) ∧ F 1 1 0 + F 1 1 1 = 1 ∧
      (∀ a, 0 ≤ F 1 2 a) ∧ F 1 2 0 + F 1 2 1 = 1 := by
  have h0 := hF 0 0 rfl
  have h1 := hF 1 1 rfl
  have h2 := hF 1 2 rfl
  exact ⟨h0.1, by simpa [bagA, Fin.sum_univ_two] using h0.2.2, h1.1,
    by simpa [bagA, Fin.sum_univ_two] using h1.2.2, h2.1,
    by simpa [bagA, Fin.sum_univ_two] using h2.2.2⟩

/-- A behaviour strategy of a player of `bagA` with an information set `k` of hers. -/
theorem bagA_beh {g : Fin 3 → Fin 2 → ℝ} {i : Fin 2} (hg : bagA.IsBehaviorStrategy i g)
    {k : Fin 3} (hk : bagA.player k = some i) : (∀ a, 0 ≤ g k a) ∧ g k 0 + g k 1 = 1 :=
  ⟨(hg k hk).1, by simpa [bagA, Fin.sum_univ_two] using (hg k hk).2.2⟩

/-- A behaviour strategy of a player of `bagB` with an information set `k` of hers. -/
theorem bagB_beh {g : Fin 2 → Fin 2 → ℝ} {i : Fin 2} (hg : bagB.IsBehaviorStrategy i g)
    {k : Fin 2} (hk : bagB.player k = some i) : (∀ a, 0 ≤ g k a) ∧ g k 0 + g k 1 = 1 :=
  ⟨(hg k hk).1, by simpa [bagB, Fin.sum_univ_two] using (hg k hk).2.2⟩

/-- Playing `a` at information set `k` and following `F i` elsewhere (in `bagA`). -/
theorem bagA_beh_update {F : Fin 2 → Fin 3 → Fin 2 → ℝ} (hF : IsBehaviorProfile bagA F)
    (i : Fin 2) (k : Fin 3) (a : Fin 2) :
    bagA.IsBehaviorStrategy i (Function.update (F i) k (dirac a)) := by
  intro k' hk'
  by_cases hkk : k' = k
  · subst hkk
    simp only [Function.update_self]
    refine ⟨fun b => by unfold dirac; split_ifs <;> norm_num,
      fun b hb => absurd (Finset.mem_univ b) hb, ?_⟩
    simp only [dirac]
    rw [Finset.sum_ite_eq']
    simp [bagA]
  · simp only [Function.update_of_ne hkk]
    exact hF i k' hk'

/-- Playing `a` at information set `k` and following `F i` elsewhere (in `bagB`). -/
theorem bagB_beh_update {F : Fin 2 → Fin 2 → Fin 2 → ℝ} (hF : IsBehaviorProfile bagB F)
    (i : Fin 2) (k : Fin 2) (a : Fin 2) :
    bagB.IsBehaviorStrategy i (Function.update (F i) k (dirac a)) := by
  intro k' hk'
  by_cases hkk : k' = k
  · subst hkk
    simp only [Function.update_self]
    refine ⟨fun b => by unfold dirac; split_ifs <;> norm_num,
      fun b hb => absurd (Finset.mem_univ b) hb, ?_⟩
    simp only [dirac]
    rw [Finset.sum_ite_eq']
    simp [bagB]
  · simp only [Function.update_of_ne hkk]
    exact hF i k' hk'

/-- Player 1's and player 2's expected payoffs in `bagA` under the moves of a profile. -/
theorem bagA_payoffs (F : Fin 2 → Fin 3 → Fin 2 → ℝ) :
    cont bagA (bagA.assemble F) [] 0 = F 0 0 0 * (F 1 1 0 * 4 + F 1 1 1 * 1) +
      F 0 0 1 * (F 1 2 0 * 5 + F 1 2 1 * 2) ∧
    cont bagA (bagA.assemble F) [] 1 = F 0 0 0 * (F 1 1 0 * 2 + F 1 1 1 * 1) +
      F 0 0 1 * (F 1 2 0 * 1 + F 1 2 1 * 2) := by
  rw [(bagA_cont _ 0).2.2.2.2.2.2, (bagA_cont _ 1).2.2.2.2.2.2, bagA_assemble_eq]
  simp [bagPay]

/-- Player 1's and player 2's expected payoffs in `bagB` under the moves of a profile. -/
theorem bagB_payoffs (F : Fin 2 → Fin 2 → Fin 2 → ℝ) :
    cont bagB (bagB.assemble F) [] 0 = F 0 0 0 * (F 1 1 0 * 4 + F 1 1 1 * 1) +
      F 0 0 1 * (F 1 1 0 * 5 + F 1 1 1 * 2) ∧
    cont bagB (bagB.assemble F) [] 1 = F 0 0 0 * (F 1 1 0 * 2 + F 1 1 1 * 1) +
      F 0 0 1 * (F 1 1 0 * 1 + F 1 1 1 * 2) := by
  rw [bagB_cont, bagB_cont, bagB_assemble_eq]
  simp [bagPay]

theorem bagA_perfectInformation : bagA.PerfectInformation := by
  unfold ExtensiveForm.PerfectInformation
  decide

/-- `(B; D after B, U after T)` is a subgame perfect Nash equilibrium of `bagA`. -/
theorem bagA_isSPNE : IsSPNE bagA (pureMoves ![0, 0, 1]) := by
  have hdec : bagA.decisionNodes = {[], [0], [1]} := by decide
  refine isSPNE_of_oneShotOptimal _ (isBehaviorProfile_pureMoves fun _ => Finset.mem_univ _)
    fun x hx j hj a _ => ?_
  have hx' := (mem_decisionNodes _).2 hx
  rw [hdec] at hx'
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
  have hc := bagA_cont (bagA.assemble (pureMoves (I := Fin 2) ![0, 0, 1])) j
  rw [bagA_assemble_eq] at hc
  rcases hx' with rfl | rfl | rfl
  · obtain rfl : j = 0 := (Option.some.inj (hj : some 0 = some j)).symm
    rw [bagA_assemble_eq]
    fin_cases a
    · change cont _ _ [0] 0 ≤ _
      rw [hc.2.2.2.2.1, hc.2.2.2.2.2.2]
      norm_num [pureMoves, dirac, bagPay]
    · change cont _ _ [1] 0 ≤ _
      rw [hc.2.2.2.2.2.1, hc.2.2.2.2.2.2]
      norm_num [pureMoves, dirac, bagPay]
  · obtain rfl : j = 1 := (Option.some.inj (hj : some 1 = some j)).symm
    rw [bagA_assemble_eq]
    fin_cases a
    · change cont _ _ [0, 0] 1 ≤ cont _ _ [0] 1
      rw [hc.1, hc.2.2.2.2.1]
      norm_num [pureMoves, dirac, bagPay]
    · change cont _ _ [1, 0] 1 ≤ cont _ _ [0] 1
      rw [hc.2.1, hc.2.2.2.2.1]
      norm_num [pureMoves, dirac, bagPay]
  · obtain rfl : j = 1 := (Option.some.inj (hj : some 1 = some j)).symm
    rw [bagA_assemble_eq]
    fin_cases a
    · change cont _ _ [0, 1] 1 ≤ cont _ _ [1] 1
      rw [hc.2.2.1, hc.2.2.2.2.2.1]
      norm_num [pureMoves, dirac, bagPay]
    · change cont _ _ [1, 1] 1 ≤ cont _ _ [1] 1
      rw [hc.2.2.2.1, hc.2.2.2.2.2.1]
      norm_num [pureMoves, dirac, bagPay]

/-- The case analysis behind the Nash equilibria of `bagA` (`x`: probability of `B`, `q`, `r`:
probabilities of `D` after `B` and after `T`). -/
theorem bagA_nash_cases {x x' q r : ℝ} (hx : 0 ≤ x) (hx' : 0 ≤ x') (hs : x + x' = 1)
    (hq1 : q ≤ 1) (hr : 0 ≤ r) (e1 : x * (1 - q) ≤ 0) (e2 : x' * r ≤ 0)
    (e3 : x' * (3 * q - 3 * r - 1) ≤ 0) (e4 : x * (3 * r + 1 - 3 * q) ≤ 0) :
    (x = 1 ∧ q = 1 ∧ r ≤ 2 / 3) ∨ (x' = 1 ∧ r = 0 ∧ q ≤ 1 / 3) := by
  rcases hx'.lt_or_eq with h | h
  · have hr0 : r = 0 := le_antisymm (nonpos_of_mul_nonpos_right (by linarith) h) hr
    subst hr0
    rcases hx.lt_or_eq with h' | h'
    · have : q = 1 := le_antisymm hq1 (by nlinarith)
      subst this
      nlinarith
    · right
      have hx'1 : x' = 1 := by linarith
      subst hx'1
      exact ⟨rfl, rfl, by linarith⟩
  · left
    have hx1 : x = 1 := by linarith
    subst hx1
    have : q = 1 := le_antisymm hq1 (by linarith)
    subst this
    exact ⟨rfl, rfl, by linarith⟩

/-- The Nash equilibria of `bagA` (behaviour strategies). -/
theorem bagA_isNashB_iff (F : Fin 2 → Fin 3 → Fin 2 → ℝ) :
    IsNashB bagA F ↔ IsBehaviorProfile bagA F ∧
      ((F 0 0 0 = 1 ∧ F 1 1 0 = 1 ∧ F 1 2 0 ≤ 2 / 3) ∨
        (F 0 0 1 = 1 ∧ F 1 2 1 = 1 ∧ F 1 1 0 ≤ 1 / 3)) := by
  constructor
  · rintro ⟨hF, hN⟩
    obtain ⟨hx0, hx1, hq0, hq1, hr0, hr1⟩ := bagA_behavior hF
    have hu := bagA_payoffs F
    have dev : ∀ (i : Fin 2) (k : Fin 3) (a : Fin 2),
        cont bagA (bagA.assemble (Function.update F i (Function.update (F i) k (dirac a))))
          [] i ≤ cont bagA (bagA.assemble F) [] i :=
      fun i k a => hN i _ (bagA_beh_update hF i k a)
    have dB := dev 0 0 0
    have dT := dev 0 0 1
    have dD := dev 1 1 0
    have dU := dev 1 2 1
    rw [(bagA_payoffs _).1, hu.1] at dB dT
    rw [(bagA_payoffs _).2, hu.2] at dD dU
    simp only [Fin.isValue, Function.update_self, dirac, ↓reduceIte, ne_eq, one_ne_zero,
      not_false_eq_true, Function.update_of_ne, mul_one, one_mul, zero_mul, add_zero,
      zero_ne_one, zero_add, Fin.reduceEq, add_le_add_iff_right, add_le_add_iff_left]
      at dB dT dD dU
    have P1 := congrArg (F 0 0 0 * ·) hq1
    have P2 := congrArg (F 0 0 1 * ·) hr1
    have P3 := congrArg (F 0 0 0 * ·) hr1
    have P4 := congrArg (F 0 0 1 * ·) hq1
    have P5 := congrArg (F 1 1 0 * ·) hx1
    have P6 := congrArg (F 1 2 0 * ·) hx1
    have P7 := congrArg (F 1 1 1 * ·) hx1
    have P8 := congrArg (F 1 2 1 * ·) hx1
    have e1 : F 0 0 0 * (1 - F 1 1 0) ≤ 0 := by linarith
    have e2 : F 0 0 1 * F 1 2 0 ≤ 0 := by linarith
    have e3 : F 0 0 1 * (3 * F 1 1 0 - 3 * F 1 2 0 - 1) ≤ 0 := by linarith
    have e4 : F 0 0 0 * (3 * F 1 2 0 + 1 - 3 * F 1 1 0) ≤ 0 := by linarith
    refine ⟨hF, ?_⟩
    rcases bagA_nash_cases (hx0 0) (hx0 1) hx1 (by linarith [hq0 1]) (hr0 0) e1 e2 e3 e4 with
      h | ⟨h1, h2, h3⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, by linarith, h3⟩
  · rintro ⟨hF, hc⟩
    obtain ⟨hx0, hx1, hq0, hq1, hr0, hr1⟩ := bagA_behavior hF
    refine ⟨hF, fun i g hg => ?_⟩
    rcases (by decide : ∀ i : Fin 2, i = 0 ∨ i = 1) i with rfl | rfl
    · obtain ⟨hg0, hg1⟩ := bagA_beh hg (k := 0) rfl
      rw [(bagA_payoffs _).1, (bagA_payoffs _).1, Function.update_self,
        Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide),
        show g 0 1 = 1 - g 0 0 by linarith]
      rcases hc with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      · rw [h1, h2, show F 0 0 1 = 0 by linarith, show F 1 1 1 = 0 by linarith,
          show F 1 2 1 = 1 - F 1 2 0 by linarith]
        nlinarith [mul_nonneg (by linarith [hg0 1] : 0 ≤ 1 - g 0 0)
          (by linarith : 0 ≤ 2 / 3 - F 1 2 0)]
      · rw [h1, h2, show F 0 0 0 = 0 by linarith, show F 1 2 0 = 0 by linarith,
          show F 1 1 1 = 1 - F 1 1 0 by linarith]
        nlinarith [mul_nonneg (hg0 0) (by linarith : 0 ≤ 1 / 3 - F 1 1 0)]
    · obtain ⟨hg0, hg1⟩ := bagA_beh hg (k := 1) rfl
      obtain ⟨hh0, hh1⟩ := bagA_beh hg (k := 2) rfl
      rw [(bagA_payoffs _).2, (bagA_payoffs _).2, Function.update_self,
        Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide)]
      rcases hc with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      · rw [h1, h2, show F 0 0 1 = 0 by linarith, show F 1 1 1 = 0 by linarith]
        linarith [hg0 1]
      · rw [h1, h2, show F 0 0 0 = 0 by linarith, show F 1 2 0 = 0 by linarith]
        linarith [hh0 0]

/-- Every SPNE of `bagA` is `(B; D after B, U after T)`. -/
theorem bagA_isSPNE_unique {F : Fin 2 → Fin 3 → Fin 2 → ℝ} (hF : IsSPNE bagA F) :
    F 0 0 0 = 1 ∧ F 1 1 0 = 1 ∧ F 1 2 1 = 1 := by
  obtain ⟨hx0, hx1, hq0, hq1, hr0, hr1⟩ := bagA_behavior hF.1
  have o0 := oneShotOptimal_of_isSPNE bagA bagA_perfectInformation hF
    (x := []) ⟨by decide, 0, by decide⟩ 0 rfl 0 (Finset.mem_univ _)
  have o1 := oneShotOptimal_of_isSPNE bagA bagA_perfectInformation hF
    (x := [0]) ⟨by decide, 0, by decide⟩ 1 rfl 0 (Finset.mem_univ _)
  have o2 := oneShotOptimal_of_isSPNE bagA bagA_perfectInformation hF
    (x := [1]) ⟨by decide, 0, by decide⟩ 1 rfl 1 (Finset.mem_univ _)
  have hc0 := bagA_cont (bagA.assemble F) 0
  have hc1 := bagA_cont (bagA.assemble F) 1
  change cont _ _ [0, 0] 1 ≤ cont _ _ [0] 1 at o1
  change cont _ _ [1, 1] 1 ≤ cont _ _ [1] 1 at o2
  change cont _ _ [0] 0 ≤ cont _ _ [] 0 at o0
  rw [hc1.1, hc1.2.2.2.2.1] at o1
  rw [hc1.2.2.2.1, hc1.2.2.2.2.2.1] at o2
  rw [hc0.2.2.2.2.1, hc0.2.2.2.2.2.2] at o0
  simp only [Fin.isValue, bagA_assemble_eq, Nat.succ_eq_add_one, Nat.reduceAdd,
    Matrix.cons_val_one, Matrix.cons_val_zero, bagPay, ↓reduceIte, one_ne_zero, mul_one,
    Matrix.cons_val, Matrix.cons_val_fin_one] at o0 o1 o2
  have hq : F 1 1 0 = 1 := by nlinarith [hq0 0, hq0 1]
  have hr : F 1 2 1 = 1 := by nlinarith [hr0 0, hr0 1]
  have P1 := congrArg (F 0 0 0 * ·) hq
  have P2 := congrArg (F 0 0 0 * ·) (show F 1 1 1 = 0 by linarith)
  have P3 := congrArg (F 0 0 1 * ·) hr
  have P4 := congrArg (F 0 0 1 * ·) (show F 1 2 0 = 0 by linarith)
  exact ⟨by linarith [hx0 0, hx0 1], hq, hr⟩

/-- **Exercise 9.C.7(a)** (MWG, p. 304). In the game of Figure 9.Ex.2, `(B; D after B, U after
T)` is a subgame perfect Nash equilibrium, and it is the unique one (behaviour strategies).
The Nash equilibria are exactly the profiles in which either player 1 plays `B`, player 2 plays
`D` after `B` and `D` after `T` with probability at most `2/3`, or player 1 plays `T`, player 2
plays `U` after `T` and `D` after `B` with probability at most `1/3`; in particular
`(T; U, U)` is a Nash equilibrium that is not subgame perfect. -/
theorem exercise_9_C_7a :
    IsSPNE bagA (pureMoves ![0, 0, 1]) ∧
    (∀ F, IsSPNE bagA F → F 0 0 0 = 1 ∧ F 1 1 0 = 1 ∧ F 1 2 1 = 1) ∧
    (∀ F, IsNashB bagA F ↔ IsBehaviorProfile bagA F ∧
      ((F 0 0 0 = 1 ∧ F 1 1 0 = 1 ∧ F 1 2 0 ≤ 2 / 3) ∨
        (F 0 0 1 = 1 ∧ F 1 2 1 = 1 ∧ F 1 1 0 ≤ 1 / 3))) ∧
    IsNashB bagA (pureMoves ![1, 1, 1]) ∧ ¬ IsSPNE bagA (pureMoves ![1, 1, 1]) := by
  refine ⟨bagA_isSPNE, fun F hF => bagA_isSPNE_unique hF, bagA_isNashB_iff, ?_, fun h => ?_⟩
  · refine (bagA_isNashB_iff _).2
      ⟨isBehaviorProfile_pureMoves fun _ => Finset.mem_univ _, Or.inr ?_⟩
    norm_num [pureMoves, dirac]
  · have := (bagA_isSPNE_unique h).1
    norm_num [pureMoves, dirac] at this

/-- **Exercise 9.C.7(b)** (MWG, p. 304). When player 2 cannot observe player 1's move
(`bagB`, one information set for player 2), `T` strictly dominates `B` for player 1 (`5 > 4`
and `2 > 1`), and the unique Nash equilibrium, mixed (behaviour) strategies included, is
`(T, U)`. -/
theorem exercise_9_C_7b (F : Fin 2 → Fin 2 → Fin 2 → ℝ) :
    IsNashB bagB F ↔ IsBehaviorProfile bagB F ∧ F 0 0 1 = 1 ∧ F 1 1 1 = 1 := by
  constructor
  · rintro ⟨hF, hN⟩
    obtain ⟨hx0, hx1⟩ := bagB_beh (hF 0) (k := 0) rfl
    obtain ⟨hq0, hq1⟩ := bagB_beh (hF 1) (k := 1) rfl
    have dT := hN 0 _ (bagB_beh_update hF 0 0 1)
    have dU := hN 1 _ (bagB_beh_update hF 1 1 1)
    rw [(bagB_payoffs _).1, (bagB_payoffs _).1] at dT
    rw [(bagB_payoffs _).2, (bagB_payoffs _).2] at dU
    simp only [Fin.isValue, Function.update_self, dirac, zero_ne_one, ↓reduceIte, ne_eq,
      one_ne_zero, not_false_eq_true, Function.update_of_ne, mul_one, zero_mul, one_mul,
      zero_add] at dT dU
    have P1 := congrArg (F 0 0 0 * ·) hq1
    have P2 := congrArg (F 0 0 1 * ·) hq1
    have hx : F 0 0 0 = 0 := le_antisymm (by nlinarith [hq0 0, hq0 1]) (hx0 0)
    have hx' : F 0 0 1 = 1 := by linarith
    have Q1 := congrArg (· * F 1 1 0) hx'
    have Q2 := congrArg (· * F 1 1 1) hx'
    have Q3 := congrArg (· * F 1 1 0) hx
    have Q4 := congrArg (· * F 1 1 1) hx
    refine ⟨hF, hx', by linarith [hq0 0]⟩
  · rintro ⟨hF, hx, hq⟩
    obtain ⟨hx0, hx1⟩ := bagB_beh (hF 0) (k := 0) rfl
    obtain ⟨hq0, hq1⟩ := bagB_beh (hF 1) (k := 1) rfl
    have hx0' : F 0 0 0 = 0 := by linarith
    have hq0' : F 1 1 0 = 0 := by linarith
    refine ⟨hF, fun i g hg => ?_⟩
    rcases (by decide : ∀ i : Fin 2, i = 0 ∨ i = 1) i with rfl | rfl
    · obtain ⟨hg0, hg1⟩ := bagB_beh hg (k := 0) rfl
      rw [(bagB_payoffs _).1, (bagB_payoffs _).1, Function.update_self,
        Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide), hx0', hx, hq0', hq]
      linarith [hg0 0]
    · obtain ⟨hg0, hg1⟩ := bagB_beh hg (k := 1) rfl
      rw [(bagB_payoffs _).2, (bagB_payoffs _).2, Function.update_self,
        Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), hx0', hx, hq0', hq]
      linarith [hg0 0]

/-- Terminal payoffs of the game of Exercise 9.C.7(c): the node `[d, s, a]` (player 1's move
`a`, the signal `s`, player 2's move `d`). -/
def bagPayC (i : Fin 2) (z : List (Fin 2)) : ℝ :=
  match z with
  | [d, _, a] => bagPay i d a
  | _ => 0

/-- Nature's probabilities in the game of Exercise 9.C.7(c): after `B` (information set `1`)
the signal is `B` (`0`) with probability `p`; after `T` (information set `2`) it is `T` (`1`)
with probability `p`. -/
def bagNature (p : ℝ) (k : Fin 5) (s : Fin 2) : ℝ :=
  if k = 1 then (if s = 0 then p else 1 - p) else if k = 2 then (if s = 1 then p else 1 - p)
  else 0

/-- The information sets of the game of Exercise 9.C.7(c): `0` player 1; `1`, `2` nature
after `B`, `T`; `3` player 2 after signal `B` (nodes `[0, 0]`, `[0, 1]`); `4` player 2 after
signal `T` (nodes `[1, 0]`, `[1, 1]`). -/
def bagInfoC (x : List (Fin 2)) : Fin 5 :=
  if x = [] then 0 else if x = [0] then 1 else if x = [1] then 2
  else if x = [0, 0] ∨ x = [0, 1] then 3 else 4

/-- The nodes of the game of Exercise 9.C.7(c). -/
def bagCNodes : Finset (List (Fin 2)) :=
  {[], [0], [1], [0, 0], [1, 0], [0, 1], [1, 1], [0, 0, 0], [1, 0, 0], [0, 1, 0], [1, 1, 0],
    [0, 0, 1], [1, 0, 1], [0, 1, 1], [1, 1, 1]}

/-- **Exercise 9.C.7(c)** (MWG, p. 305). Player 2 observes player 1's move correctly with
probability `p` and incorrectly with probability `1 − p`: nature chooses the signal after
player 1's move, and player 2 knows only the signal. -/
def bagC (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) : ExtensiveForm (Fin 2) (Fin 2) (Fin 5) where
  nodes := bagCNodes
  nil_mem := by decide
  tail_mem := by decide
  info := bagInfoC
  avail _ := Finset.univ
  avail_spec := by decide
  info_surj := by decide
  player := ![some 0, none, none, some 1, some 1]
  natureProb := bagNature p
  nature_nonneg := fun _ _ _ => by unfold bagNature; split_ifs <;> linarith [hp.1, hp.2]
  nature_zero := fun _ _ a ha => absurd (Finset.mem_univ a) ha
  nature_sum := fun k hk => by
    rcases (by decide : ∀ k : Fin 5, k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) k with
      rfl | rfl | rfl | rfl | rfl
    · simp at hk
    · simp [bagNature, Fin.sum_univ_two]
    · simp [bagNature, Fin.sum_univ_two]
    · simp at hk
    · simp at hk
  payoff := bagPayC

variable {p : ℝ} {hp : p ∈ Set.Icc (0 : ℝ) 1}

/-- Continuation payoffs in `bagC p` (`f` any move function). -/
theorem bagC_cont (f : Fin 5 → Fin 2 → ℝ) (i : Fin 2) :
    cont (bagC p hp) f [0, 0] i = f 3 0 * bagPay i 0 0 + f 3 1 * bagPay i 1 0 ∧
    cont (bagC p hp) f [0, 1] i = f 3 0 * bagPay i 0 1 + f 3 1 * bagPay i 1 1 ∧
    cont (bagC p hp) f [1, 0] i = f 4 0 * bagPay i 0 0 + f 4 1 * bagPay i 1 0 ∧
    cont (bagC p hp) f [1, 1] i = f 4 0 * bagPay i 0 1 + f 4 1 * bagPay i 1 1 ∧
    cont (bagC p hp) f [] i =
      f 0 0 * (f 1 0 * (f 3 0 * bagPay i 0 0 + f 3 1 * bagPay i 1 0) +
        f 1 1 * (f 4 0 * bagPay i 0 0 + f 4 1 * bagPay i 1 0)) +
      f 0 1 * (f 2 0 * (f 3 0 * bagPay i 0 1 + f 3 1 * bagPay i 1 1) +
        f 2 1 * (f 4 0 * bagPay i 0 1 + f 4 1 * bagPay i 1 1)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [cont_unfold, bagC, bagCNodes, bagPayC, bagInfoC, Fin.sum_univ_two]

theorem bagC_infoSet : (bagC p hp).infoSet 0 = {[]} ∧ (bagC p hp).infoSet 1 = {[0]} ∧
    (bagC p hp).infoSet 2 = {[1]} ∧ (bagC p hp).infoSet 3 = {[0, 0], [0, 1]} ∧
    (bagC p hp).infoSet 4 = {[1, 0], [1, 1]} := by
  have key : ∀ k, (bagC p hp).infoSet k =
      (bagCNodes.filter fun x => ∃ b, b :: x ∈ bagCNodes).filter fun x => bagInfoC x = k :=
    fun _ => rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [key] <;> decide

theorem bagC_assemble (F : Fin 2 → Fin 5 → Fin 2 → ℝ) :
    (bagC p hp).assemble F 0 = F 0 0 ∧ (bagC p hp).assemble F 1 = bagNature p 1 ∧
      (bagC p hp).assemble F 2 = bagNature p 2 ∧ (bagC p hp).assemble F 3 = F 1 3 ∧
      (bagC p hp).assemble F 4 = F 1 4 :=
  ⟨(bagC p hp).assemble_of_some _ rfl, (bagC p hp).assemble_of_none _ rfl,
    (bagC p hp).assemble_of_none _ rfl, (bagC p hp).assemble_of_some _ rfl,
    (bagC p hp).assemble_of_some _ rfl⟩

/-- Player 1's expected payoff in `bagC p` when she plays `B` with probability `x`, `T` with
probability `x'`, and player 2 plays `D` with probabilities `qB`, `qT` after the two signals. -/
theorem bagC_payoff0 (F : Fin 2 → Fin 5 → Fin 2 → ℝ) :
    cont (bagC p hp) ((bagC p hp).assemble F) [] 0 =
      F 0 0 0 * (p * (F 1 3 0 * 4 + F 1 3 1) + (1 - p) * (F 1 4 0 * 4 + F 1 4 1)) +
      F 0 0 1 * ((1 - p) * (F 1 3 0 * 5 + F 1 3 1 * 2) + p * (F 1 4 0 * 5 + F 1 4 1 * 2)) := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := bagC_assemble (p := p) (hp := hp) F
  rw [(bagC_cont _ 0).2.2.2.2, h0, h1, h2, h3, h4]
  simp [bagPay, bagNature]

/-- Expected payoffs at the information sets of `bagC p` given beliefs `μ`. -/
theorem bagC_condPayoff (f : Fin 5 → Fin 2 → ℝ) (μ : List (Fin 2) → ℝ) (i : Fin 2) :
    condPayoff (bagC p hp) f μ 0 i = μ [] * cont (bagC p hp) f [] i ∧
    condPayoff (bagC p hp) f μ 3 i = μ [0, 0] * cont (bagC p hp) f [0, 0] i +
      μ [0, 1] * cont (bagC p hp) f [0, 1] i ∧
    condPayoff (bagC p hp) f μ 4 i = μ [1, 0] * cont (bagC p hp) f [1, 0] i +
      μ [1, 1] * cont (bagC p hp) f [1, 1] i := by
  obtain ⟨h0, -, -, h3, h4⟩ := bagC_infoSet (p := p) (hp := hp)
  unfold condPayoff
  rw [h0, h3, h4]
  refine ⟨by simp, ?_, ?_⟩ <;> rw [Finset.sum_insert (by decide), Finset.sum_singleton]

theorem bagC_reach (f : Fin 5 → Fin 2 → ℝ) :
    probInfo (bagC p hp) f 0 = 1 ∧ probInfo (bagC p hp) f 1 = f 0 0 ∧
    probInfo (bagC p hp) f 2 = f 0 1 ∧
    probInfo (bagC p hp) f 3 = f 0 0 * f 1 0 + f 0 1 * f 2 0 ∧
    probInfo (bagC p hp) f 4 = f 0 0 * f 1 1 + f 0 1 * f 2 1 ∧
    (bagC p hp).reach f [] = 1 ∧ (bagC p hp).reach f [0] = f 0 0 ∧
    (bagC p hp).reach f [1] = f 0 1 ∧
    (bagC p hp).reach f [0, 0] = f 0 0 * f 1 0 ∧ (bagC p hp).reach f [0, 1] = f 0 1 * f 2 0 ∧
    (bagC p hp).reach f [1, 0] = f 0 0 * f 1 1 ∧ (bagC p hp).reach f [1, 1] = f 0 1 * f 2 1 := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := bagC_infoSet (p := p) (hp := hp)
  have r00 : (bagC p hp).reach f [0, 0] = f 0 0 * f 1 0 := by simp [bagC, bagInfoC]
  have r01 : (bagC p hp).reach f [0, 1] = f 0 1 * f 2 0 := by simp [bagC, bagInfoC]
  have r10 : (bagC p hp).reach f [1, 0] = f 0 0 * f 1 1 := by simp [bagC, bagInfoC]
  have r11 : (bagC p hp).reach f [1, 1] = f 0 1 * f 2 1 := by simp [bagC, bagInfoC]
  have r0 : (bagC p hp).reach f [0] = f 0 0 := by simp [bagC, bagInfoC]
  have r1 : (bagC p hp).reach f [1] = f 0 1 := by simp [bagC, bagInfoC]
  have rn : (bagC p hp).reach f [] = 1 := by simp
  unfold probInfo
  rw [h0, h1, h2, h3, h4, Finset.sum_insert (by decide), Finset.sum_singleton,
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [Finset.sum_singleton]
  exact ⟨rn, r0, r1, by rw [r00, r01], by rw [r10, r11], rn, r0, r1, r00, r01, r10, r11⟩

/-- A behaviour strategy of a player of `bagC p` at one of her information sets. -/
theorem bagC_beh {g : Fin 5 → Fin 2 → ℝ} {i : Fin 2} (hg : (bagC p hp).IsBehaviorStrategy i g)
    {k : Fin 5} (hk : (bagC p hp).player k = some i) : (∀ a, 0 ≤ g k a) ∧ g k 0 + g k 1 = 1 :=
  ⟨(hg k hk).1, by simpa [bagC, Fin.sum_univ_two] using (hg k hk).2.2⟩

/-- Playing `a` at information set `k` and following `F i` elsewhere (in `bagC p`). -/
theorem bagC_beh_update {F : Fin 2 → Fin 5 → Fin 2 → ℝ} (hF : IsBehaviorProfile (bagC p hp) F)
    (i : Fin 2) (k : Fin 5) (a : Fin 2) :
    (bagC p hp).IsBehaviorStrategy i (Function.update (F i) k (dirac a)) := by
  intro k' hk'
  by_cases hkk : k' = k
  · subst hkk
    simp only [Function.update_self]
    refine ⟨fun b => by unfold dirac; split_ifs <;> norm_num,
      fun b hb => absurd (Finset.mem_univ b) hb, ?_⟩
    simp only [dirac]
    rw [Finset.sum_ite_eq']
    simp [bagC]
  · simp only [Function.update_of_ne hkk]
    exact hF i k' hk'

/-- The probability of each of player 2's information sets in `bagC p` is positive. -/
theorem bagC_probInfo_pos (hp' : p ∈ Set.Ioo (0 : ℝ) 1) {x x' : ℝ} (hx : 0 ≤ x)
    (hx' : 0 ≤ x') (hs : x + x' = 1) : 0 < x * p + x' * (1 - p) ∧ 0 < x * (1 - p) + x' * p := by
  obtain ⟨h0, h1⟩ := hp'
  rcases le_total p (1 - p) with h | h
  · constructor
    · nlinarith [mul_le_mul_of_nonneg_left h hx']
    · nlinarith [mul_le_mul_of_nonneg_left h hx]
  · constructor
    · nlinarith [mul_le_mul_of_nonneg_left h hx]
    · nlinarith [mul_le_mul_of_nonneg_left h hx']

/-- The moves of a profile of `bagC p`. -/
theorem bagC_assemble_eq (F : Fin 2 → Fin 5 → Fin 2 → ℝ) :
    (bagC p hp).assemble F = fun k => if k = 1 then bagNature p 1 else if k = 2 then
      bagNature p 2 else F (![0, 0, 0, 1, 1] k) k := by
  funext k
  rcases (by decide : ∀ k : Fin 5, k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) k with
    rfl | rfl | rfl | rfl | rfl
  · exact (bagC p hp).assemble_of_some _ rfl
  · exact (bagC p hp).assemble_of_none _ rfl
  · exact (bagC p hp).assemble_of_none _ rfl
  · exact (bagC p hp).assemble_of_some _ rfl
  · exact (bagC p hp).assemble_of_some _ rfl

/-- Player 2's expected payoff at the information set of signal `B`. -/
theorem bagC_cond3 (f : Fin 5 → Fin 2 → ℝ) (μ : List (Fin 2) → ℝ) :
    condPayoff (bagC p hp) f μ 3 1 =
      μ [0, 0] * (f 3 0 * 2 + f 3 1) + μ [0, 1] * (f 3 0 + f 3 1 * 2) := by
  rw [(bagC_condPayoff f μ 1).2.1, (bagC_cont f 1).1, (bagC_cont f 1).2.1]
  simp [bagPay]

/-- Player 2's expected payoff at the information set of signal `T`. -/
theorem bagC_cond4 (f : Fin 5 → Fin 2 → ℝ) (μ : List (Fin 2) → ℝ) :
    condPayoff (bagC p hp) f μ 4 1 =
      μ [1, 0] * (f 4 0 * 2 + f 4 1) + μ [1, 1] * (f 4 0 + f 4 1 * 2) := by
  rw [(bagC_condPayoff f μ 1).2.2, (bagC_cont f 1).2.2.1, (bagC_cont f 1).2.2.2.1]
  simp [bagPay]

theorem dirac_fin2 : dirac (0 : Fin 2) 0 = 1 ∧ dirac (0 : Fin 2) 1 = 0 ∧
    dirac (1 : Fin 2) 0 = 0 ∧ dirac (1 : Fin 2) 1 = 1 := by
  simp [dirac]

/-- The conditions satisfied by a weak PBE of `bagC p` (`x`, `x'`: player 1's probabilities of
`B`, `T`; `qB`, `qT`: player 2's probabilities of `D` after the signals `B`, `T`): Bayes' rule
at both of player 2's information sets, player 2's sequential rationality (`D` only if the
belief on `B` is at least `1/2`, `U` only if it is at most `1/2`), and player 1's optimality
(`T` gains `1 + 3 (qT − qB)(2p − 1)` over `B`). -/
theorem bagC_weakPBE_facts (hp' : p ∈ Set.Ioo (0 : ℝ) 1) {F : Fin 2 → Fin 5 → Fin 2 → ℝ}
    {μ : List (Fin 2) → ℝ} (h : IsWeakPBE (bagC p hp) F μ) :
    F 0 0 0 * (1 + 3 * (F 1 4 0 - F 1 3 0) * (2 * p - 1)) ≤ 0 ∧
    0 ≤ F 0 0 1 * (1 + 3 * (F 1 4 0 - F 1 3 0) * (2 * p - 1)) ∧
    (1 - F 1 3 0) * (F 0 0 0 * p - F 0 0 1 * (1 - p)) ≤ 0 ∧
    F 1 3 0 * (F 0 0 1 * (1 - p) - F 0 0 0 * p) ≤ 0 ∧
    (1 - F 1 4 0) * (F 0 0 0 * (1 - p) - F 0 0 1 * p) ≤ 0 ∧
    F 1 4 0 * (F 0 0 1 * p - F 0 0 0 * (1 - p)) ≤ 0 ∧
    μ [0, 0] * (F 0 0 0 * p + F 0 0 1 * (1 - p)) = F 0 0 0 * p ∧
    μ [0, 1] * (F 0 0 0 * p + F 0 0 1 * (1 - p)) = F 0 0 1 * (1 - p) ∧
    μ [1, 0] * (F 0 0 0 * (1 - p) + F 0 0 1 * p) = F 0 0 0 * (1 - p) ∧
    μ [1, 1] * (F 0 0 0 * (1 - p) + F 0 0 1 * p) = F 0 0 1 * p := by
  obtain ⟨hF, -, hSR, hB⟩ := h
  obtain ⟨hx0, hx1⟩ := bagC_beh (hF 0) (k := 0) rfl
  obtain ⟨hq0, hq1⟩ := bagC_beh (hF 1) (k := 3) rfl
  obtain ⟨hr0, hr1⟩ := bagC_beh (hF 1) (k := 4) rfl
  obtain ⟨P3, P4⟩ := bagC_probInfo_pos hp' (hx0 0) (hx0 1) hx1
  obtain ⟨a0, a1, a2, a3, a4⟩ := bagC_assemble (p := p) (hp := hp) F
  obtain ⟨p0, -, -, p3, p4, rn, -, -, r00, r01, r10, r11⟩ :=
    bagC_reach (p := p) (hp := hp) ((bagC p hp).assemble F)
  obtain ⟨h0, -, -, h3, h4⟩ := bagC_infoSet (p := p) (hp := hp)
  have n10 : bagNature p 1 0 = p := by simp [bagNature]
  have n11 : bagNature p 1 1 = 1 - p := by simp [bagNature]
  have n20 : bagNature p 2 0 = 1 - p := by simp [bagNature]
  have n21 : bagNature p 2 1 = p := by simp [bagNature]
  simp only [a0, a1, a2, n10, n11, n20, n21] at p3 p4 r00 r01 r10 r11
  -- Bayes' rule
  have hpos3 : 0 < probInfo (bagC p hp) ((bagC p hp).assemble F) 3 := by rw [p3]; exact P3
  have hpos4 : 0 < probInfo (bagC p hp) ((bagC p hp).assemble F) 4 := by rw [p4]; exact P4
  have b00 := hB 3 hpos3 [0, 0] (by rw [h3]; simp)
  have b01 := hB 3 hpos3 [0, 1] (by rw [h3]; simp)
  have b10 := hB 4 hpos4 [1, 0] (by rw [h4]; simp)
  have b11 := hB 4 hpos4 [1, 1] (by rw [h4]; simp)
  rw [r00, p3] at b00
  rw [r01, p3] at b01
  rw [r10, p4] at b10
  rw [r11, p4] at b11
  have e00 : μ [0, 0] * (F 0 0 0 * p + F 0 0 1 * (1 - p)) = F 0 0 0 * p := by
    rw [b00, div_mul_cancel₀ _ P3.ne']
  have e01 : μ [0, 1] * (F 0 0 0 * p + F 0 0 1 * (1 - p)) = F 0 0 1 * (1 - p) := by
    rw [b01, div_mul_cancel₀ _ P3.ne']
  have e10 : μ [1, 0] * (F 0 0 0 * (1 - p) + F 0 0 1 * p) = F 0 0 0 * (1 - p) := by
    rw [b10, div_mul_cancel₀ _ P4.ne']
  have e11 : μ [1, 1] * (F 0 0 0 * (1 - p) + F 0 0 1 * p) = F 0 0 1 * p := by
    rw [b11, div_mul_cancel₀ _ P4.ne']
  have hμn : μ [] = 1 := by
    have := hB 0 (by rw [p0]; norm_num) [] (by rw [h0]; simp)
    rw [this, rn, p0]; norm_num
  -- sequential rationality
  have K3 : ∀ a : Fin 2, μ [0, 0] * (dirac a 0 * 2 + dirac a 1) +
      μ [0, 1] * (dirac a 0 + dirac a 1 * 2) ≤
      μ [0, 0] * (F 1 3 0 * 2 + F 1 3 1) + μ [0, 1] * (F 1 3 0 + F 1 3 1 * 2) := fun a => by
    have := hSR 3 1 rfl _ (bagC_beh_update hF 1 3 a)
    rw [bagC_cond3, bagC_cond3] at this
    simpa [bagC_assemble_eq] using this
  have K4 : ∀ a : Fin 2, μ [1, 0] * (dirac a 0 * 2 + dirac a 1) +
      μ [1, 1] * (dirac a 0 + dirac a 1 * 2) ≤
      μ [1, 0] * (F 1 4 0 * 2 + F 1 4 1) + μ [1, 1] * (F 1 4 0 + F 1 4 1 * 2) := fun a => by
    have := hSR 4 1 rfl _ (bagC_beh_update hF 1 4 a)
    rw [bagC_cond4, bagC_cond4] at this
    simpa [bagC_assemble_eq] using this
  have K0 : ∀ a : Fin 2,
      dirac a 0 * (p * (F 1 3 0 * 4 + F 1 3 1) + (1 - p) * (F 1 4 0 * 4 + F 1 4 1)) +
      dirac a 1 * ((1 - p) * (F 1 3 0 * 5 + F 1 3 1 * 2) + p * (F 1 4 0 * 5 + F 1 4 1 * 2)) ≤
      F 0 0 0 * (p * (F 1 3 0 * 4 + F 1 3 1) + (1 - p) * (F 1 4 0 * 4 + F 1 4 1)) +
      F 0 0 1 * ((1 - p) * (F 1 3 0 * 5 + F 1 3 1 * 2) + p * (F 1 4 0 * 5 + F 1 4 1 * 2)) :=
    fun a => by
    have := hSR 0 0 rfl _ (bagC_beh_update hF 0 0 a)
    rwa [(bagC_condPayoff _ _ _).1, (bagC_condPayoff _ _ _).1, hμn, one_mul, one_mul,
      bagC_payoff0, bagC_payoff0, Function.update_self,
      Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide), Function.update_self] at this
  have k30 := K3 0
  have k31 := K3 1
  have k40 := K4 0
  have k41 := K4 1
  have k00 := K0 0
  have k01 := K0 1
  obtain ⟨d00, d01, d10, d11⟩ := dirac_fin2
  have hqB : F 1 3 1 = 1 - F 1 3 0 := by linarith
  have hqT : F 1 4 1 = 1 - F 1 4 0 := by linarith
  have hx' : F 0 0 1 = 1 - F 0 0 0 := by linarith
  simp only [d00, d01, d10, d11, hqB, hqT] at k30 k31 k40 k41 k00 k01
  simp only [hx'] at k00 k01 e01 e11 e00 e10 P3 P4 ⊢
  have L3 : (1 - F 1 3 0) * (μ [0, 0] - μ [0, 1]) ≤ 0 := by linarith
  have L3' : F 1 3 0 * (μ [0, 1] - μ [0, 0]) ≤ 0 := by linarith
  have L4 : (1 - F 1 4 0) * (μ [1, 0] - μ [1, 1]) ≤ 0 := by linarith
  have L4' : F 1 4 0 * (μ [1, 1] - μ [1, 0]) ≤ 0 := by linarith
  refine ⟨by linarith, by linarith, ?_, ?_, ?_, ?_, e00, e01, e10, e11⟩
  · have : (1 - F 1 3 0) * (F 0 0 0 * p - (1 - F 0 0 0) * (1 - p)) =
        (1 - F 1 3 0) * (μ [0, 0] - μ [0, 1]) * (F 0 0 0 * p + (1 - F 0 0 0) * (1 - p)) := by
      linear_combination (1 - F 1 3 0) * (e01 - e00)
    rw [this]
    exact mul_nonpos_of_nonpos_of_nonneg L3 P3.le
  · have : F 1 3 0 * ((1 - F 0 0 0) * (1 - p) - F 0 0 0 * p) =
        F 1 3 0 * (μ [0, 1] - μ [0, 0]) * (F 0 0 0 * p + (1 - F 0 0 0) * (1 - p)) := by
      linear_combination F 1 3 0 * (e00 - e01)
    rw [this]
    exact mul_nonpos_of_nonpos_of_nonneg L3' P3.le
  · have : (1 - F 1 4 0) * (F 0 0 0 * (1 - p) - (1 - F 0 0 0) * p) =
        (1 - F 1 4 0) * (μ [1, 0] - μ [1, 1]) * (F 0 0 0 * (1 - p) + (1 - F 0 0 0) * p) := by
      linear_combination (1 - F 1 4 0) * (e11 - e10)
    rw [this]
    exact mul_nonpos_of_nonpos_of_nonneg L4 P4.le
  · have : F 1 4 0 * ((1 - F 0 0 0) * p - F 0 0 0 * (1 - p)) =
        F 1 4 0 * (μ [1, 1] - μ [1, 0]) * (F 0 0 0 * (1 - p) + (1 - F 0 0 0) * p) := by
      linear_combination F 1 4 0 * (e10 - e11)
    rw [this]
    exact mul_nonpos_of_nonpos_of_nonneg L4' P4.le

/-- A profile of `bagC p`: player 1 plays `B` with probability `x`; player 2 plays `D` with
probability `qB` after signal `B` and `qT` after signal `T`. -/
def bagProfile (x qB qT : ℝ) : Fin 2 → Fin 5 → Fin 2 → ℝ := fun _ k a =>
  if k = 0 then (if a = 0 then x else 1 - x) else if k = 3 then (if a = 0 then qB else 1 - qB)
  else (if a = 0 then qT else 1 - qT)

/-- Beliefs in `bagC p`: probability `m3` on `B` after signal `B`, `m4` on `B` after signal
`T` (and one on the nodes of the singleton information sets). -/
def bagBelief (m3 m4 : ℝ) (z : List (Fin 2)) : ℝ :=
  if z = [0, 0] then m3 else if z = [0, 1] then 1 - m3 else if z = [1, 0] then m4
  else if z = [1, 1] then 1 - m4 else 1

theorem bagProfile_values (x qB qT : ℝ) :
    bagProfile x qB qT 0 0 0 = x ∧ bagProfile x qB qT 0 0 1 = 1 - x ∧
    bagProfile x qB qT 1 3 0 = qB ∧ bagProfile x qB qT 1 3 1 = 1 - qB ∧
    bagProfile x qB qT 1 4 0 = qT ∧ bagProfile x qB qT 1 4 1 = 1 - qT := by
  simp [bagProfile]

theorem bagBelief_values (m3 m4 : ℝ) :
    bagBelief m3 m4 [0, 0] = m3 ∧ bagBelief m3 m4 [0, 1] = 1 - m3 ∧
    bagBelief m3 m4 [1, 0] = m4 ∧ bagBelief m3 m4 [1, 1] = 1 - m4 ∧
    bagBelief m3 m4 [0] = 1 ∧ bagBelief m3 m4 [1] = 1 ∧ bagBelief m3 m4 [] = 1 := by
  simp [bagBelief]

/-- Player 1's sequential rationality in `bagC p` when her moves match the sign of her gain
`1 + 3 (qT − qB)(2p − 1)` from `T` over `B`. -/
theorem bagC_seq0 {x qB qT m3 m4 : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (h1 : x * (1 + 3 * (qT - qB) * (2 * p - 1)) ≤ 0)
    (h1' : 0 ≤ (1 - x) * (1 + 3 * (qT - qB) * (2 * p - 1))) :
    SeqRationalAt (bagC p hp) (bagProfile x qB qT) (bagBelief m3 m4) 0 := by
  intro i hi g hg
  obtain rfl : i = 0 := (Option.some.inj (hi : some 0 = some i)).symm
  obtain ⟨hg0, hg1⟩ := bagC_beh hg (k := 0) rfl
  obtain ⟨Q00, Q01, Q30, Q31, Q40, Q41⟩ := bagProfile_values x qB qT
  obtain ⟨-, -, -, -, -, -, Vn⟩ := bagBelief_values m3 m4
  rw [(bagC_condPayoff _ _ _).1, (bagC_condPayoff _ _ _).1, bagC_payoff0, bagC_payoff0,
    Function.update_self, Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide),
    show g 0 1 = 1 - g 0 0 by linarith, Vn, Q00, Q01, Q30, Q31, Q40, Q41]
  rcases lt_trichotomy (1 + 3 * (qT - qB) * (2 * p - 1)) 0 with hD | hD | hD
  · have : x = 1 := le_antisymm hx.2 (by nlinarith)
    subst this
    nlinarith [mul_nonneg (by linarith [hg0 1] : (0 : ℝ) ≤ 1 - g 0 0)
      (by linarith : (0 : ℝ) ≤ -(1 + 3 * (qT - qB) * (2 * p - 1)))]
  · nlinarith [congrArg ((x - g 0 0) * ·) hD]
  · have : x = 0 := le_antisymm (by nlinarith) hx.1
    subst this
    nlinarith [mul_nonneg (hg0 0) hD.le]

/-- Player 2's sequential rationality after signal `B` when her move matches her belief. -/
theorem bagC_seq3 {x qB qT m3 m4 : ℝ} (hqB : qB ∈ Set.Icc (0 : ℝ) 1)
    (h3 : (1 - qB) * (2 * m3 - 1) ≤ 0) (h3' : qB * (1 - 2 * m3) ≤ 0) :
    SeqRationalAt (bagC p hp) (bagProfile x qB qT) (bagBelief m3 m4) 3 := by
  intro i hi g hg
  obtain rfl : i = 1 := (Option.some.inj (hi : some 1 = some i)).symm
  obtain ⟨hg0, hg1⟩ := bagC_beh hg (k := 3) rfl
  obtain ⟨-, -, Q30, Q31, -, -⟩ := bagProfile_values x qB qT
  obtain ⟨V00, V01, -⟩ := bagBelief_values m3 m4
  rw [bagC_cond3, bagC_cond3, (bagC_assemble _).2.2.2.1, (bagC_assemble _).2.2.2.1,
    Function.update_self, show g 3 1 = 1 - g 3 0 by linarith, V00, V01, Q30, Q31]
  rcases lt_trichotomy (2 * m3 - 1) 0 with hD | hD | hD
  · have : qB = 0 := le_antisymm (by nlinarith) hqB.1
    subst this
    nlinarith [mul_nonneg (hg0 0) (by linarith : (0 : ℝ) ≤ -(2 * m3 - 1))]
  · nlinarith [congrArg ((qB - g 3 0) * ·) hD]
  · have : qB = 1 := le_antisymm hqB.2 (by nlinarith)
    subst this
    nlinarith [mul_nonneg (by linarith [hg0 1] : (0 : ℝ) ≤ 1 - g 3 0) hD.le]

/-- Player 2's sequential rationality after signal `T` when her move matches her belief. -/
theorem bagC_seq4 {x qB qT m3 m4 : ℝ} (hqT : qT ∈ Set.Icc (0 : ℝ) 1)
    (h4 : (1 - qT) * (2 * m4 - 1) ≤ 0) (h4' : qT * (1 - 2 * m4) ≤ 0) :
    SeqRationalAt (bagC p hp) (bagProfile x qB qT) (bagBelief m3 m4) 4 := by
  intro i hi g hg
  obtain rfl : i = 1 := (Option.some.inj (hi : some 1 = some i)).symm
  obtain ⟨hg0, hg1⟩ := bagC_beh hg (k := 4) rfl
  obtain ⟨-, -, -, -, Q40, Q41⟩ := bagProfile_values x qB qT
  obtain ⟨-, -, V10, V11, -⟩ := bagBelief_values m3 m4
  rw [bagC_cond4, bagC_cond4, (bagC_assemble _).2.2.2.2, (bagC_assemble _).2.2.2.2,
    Function.update_self, show g 4 1 = 1 - g 4 0 by linarith, V10, V11, Q40, Q41]
  rcases lt_trichotomy (2 * m4 - 1) 0 with hD | hD | hD
  · have : qT = 0 := le_antisymm (by nlinarith) hqT.1
    subst this
    nlinarith [mul_nonneg (hg0 0) (by linarith : (0 : ℝ) ≤ -(2 * m4 - 1))]
  · nlinarith [congrArg ((qT - g 4 0) * ·) hD]
  · have : qT = 1 := le_antisymm hqT.2 (by nlinarith)
    subst this
    nlinarith [mul_nonneg (by linarith [hg0 1] : (0 : ℝ) ≤ 1 - g 4 0) hD.le]

/-- Bayes' rule for `(bagProfile x qB qT, bagBelief m3 m4)` in `bagC p`. -/
theorem bagC_bayes {x qB qT m3 m4 : ℝ} (hp' : p ∈ Set.Ioo (0 : ℝ) 1)
    (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hb3 : m3 * (x * p + (1 - x) * (1 - p)) = x * p)
    (hb4 : m4 * (x * (1 - p) + (1 - x) * p) = x * (1 - p)) :
    BayesConsistent (bagC p hp) (bagProfile x qB qT) (bagBelief m3 m4) := by
  intro k hk z hz
  obtain ⟨P3, P4⟩ := bagC_probInfo_pos hp' hx.1 (by linarith [hx.2]) (by ring : x + (1 - x) = 1)
  obtain ⟨h0, hI1, hI2, hI3, hI4⟩ := bagC_infoSet (p := p) (hp := hp)
  obtain ⟨V00, V01, V10, V11, V0, V1, Vn⟩ := bagBelief_values m3 m4
  obtain ⟨p0, p1, p2, p3, p4, rn, r0, r1, r00, r01, r10, r11⟩ :=
    bagC_reach (p := p) (hp := hp) ((bagC p hp).assemble (bagProfile x qB qT))
  have A00 : (bagC p hp).assemble (bagProfile x qB qT) 0 0 = x := by
    simp [bagC_assemble_eq, bagProfile]
  have A01 : (bagC p hp).assemble (bagProfile x qB qT) 0 1 = 1 - x := by
    simp [bagC_assemble_eq, bagProfile]
  have A10 : (bagC p hp).assemble (bagProfile x qB qT) 1 0 = p := by
    simp [bagC_assemble_eq, bagNature]
  have A11 : (bagC p hp).assemble (bagProfile x qB qT) 1 1 = 1 - p := by
    simp [bagC_assemble_eq, bagNature]
  have A20 : (bagC p hp).assemble (bagProfile x qB qT) 2 0 = 1 - p := by
    simp [bagC_assemble_eq, bagNature]
  have A21 : (bagC p hp).assemble (bagProfile x qB qT) 2 1 = p := by
    simp [bagC_assemble_eq, bagNature]
  rcases (by decide : ∀ k : Fin 5, k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) k with
    rfl | rfl | rfl | rfl | rfl
  · rw [h0, Finset.mem_singleton] at hz
    subst hz
    rw [rn, p0, Vn]
    norm_num
  · rw [hI1, Finset.mem_singleton] at hz
    subst hz
    rw [p1, A00] at hk
    rw [r0, p1, A00, V0, div_self hk.ne']
  · rw [hI2, Finset.mem_singleton] at hz
    subst hz
    rw [p2, A01] at hk
    rw [r1, p2, A01, V1, div_self hk.ne']
  · rw [hI3] at hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · rw [r00, p3, A00, A01, A10, A20, V00, eq_div_iff P3.ne']
      linarith
    · rw [r01, p3, A00, A01, A10, A20, V01, eq_div_iff P3.ne']
      linarith
  · rw [hI4] at hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · rw [r10, p4, A00, A01, A11, A21, V10, eq_div_iff P4.ne']
      linarith
    · rw [r11, p4, A00, A01, A11, A21, V11, eq_div_iff P4.ne']
      linarith

/-- A sufficient condition for `(bagProfile x qB qT, bagBelief m3 m4)` to be a weak PBE of
`bagC p`: probabilities in `[0, 1]`, Bayes' rule, player 2's moves matching her beliefs, and
player 1's moves matching the sign of her gain from `T`. -/
theorem bagC_isWeakPBE_of (hp' : p ∈ Set.Ioo (0 : ℝ) 1) {x qB qT m3 m4 : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hqB : qB ∈ Set.Icc (0 : ℝ) 1) (hqT : qT ∈ Set.Icc (0 : ℝ) 1)
    (hm3 : m3 ∈ Set.Icc (0 : ℝ) 1) (hm4 : m4 ∈ Set.Icc (0 : ℝ) 1)
    (h1 : x * (1 + 3 * (qT - qB) * (2 * p - 1)) ≤ 0)
    (h1' : 0 ≤ (1 - x) * (1 + 3 * (qT - qB) * (2 * p - 1)))
    (h3 : (1 - qB) * (2 * m3 - 1) ≤ 0) (h3' : qB * (1 - 2 * m3) ≤ 0)
    (h4 : (1 - qT) * (2 * m4 - 1) ≤ 0) (h4' : qT * (1 - 2 * m4) ≤ 0)
    (hb3 : m3 * (x * p + (1 - x) * (1 - p)) = x * p)
    (hb4 : m4 * (x * (1 - p) + (1 - x) * p) = x * (1 - p)) :
    IsWeakPBE (bagC p hp) (bagProfile x qB qT) (bagBelief m3 m4) := by
  obtain ⟨h0, hI1, hI2, hI3, hI4⟩ := bagC_infoSet (p := p) (hp := hp)
  have hk5 : ∀ k : Fin 5, k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by decide
  have hF : IsBehaviorProfile (bagC p hp) (bagProfile x qB qT) := by
    intro i k hk
    refine ⟨fun a => ?_, fun a ha => absurd (Finset.mem_univ a) ha, ?_⟩
    · unfold bagProfile
      split_ifs <;> linarith [hx.1, hx.2, hqB.1, hqB.2, hqT.1, hqT.2]
    · simp only [bagC, Fin.sum_univ_two, bagProfile]
      split_ifs <;> simp_all
  have hB : IsBeliefSystem (bagC p hp) (bagBelief m3 m4) := by
    refine ⟨fun z _ => ?_, fun k => ?_⟩
    · unfold bagBelief
      split_ifs <;> constructor <;> linarith [hm3.1, hm3.2, hm4.1, hm4.2]
    · rcases hk5 k with rfl | rfl | rfl | rfl | rfl
      · simp [h0, bagBelief]
      · simp [hI1, bagBelief]
      · simp [hI2, bagBelief]
      · rw [hI3, Finset.sum_insert (by decide), Finset.sum_singleton]
        simp [bagBelief]
      · rw [hI4, Finset.sum_insert (by decide), Finset.sum_singleton]
        simp [bagBelief]
  refine ⟨hF, hB, fun k => ?_, bagC_bayes hp' hx hb3 hb4⟩
  rcases hk5 k with rfl | rfl | rfl | rfl | rfl
  · exact bagC_seq0 hx h1 h1'
  · exact fun i hi => absurd hi (by simp [bagC])
  · exact fun i hi => absurd hi (by simp [bagC])
  · exact bagC_seq3 hqB h3 h3'
  · exact bagC_seq4 hqT h4 h4'

/-- **Exercise 9.C.7(c)** (MWG, p. 305). For every `p ∈ (0, 1)`, player 1 playing `T` and
player 2 playing `U` after both signals, with beliefs putting probability one on `T` at both
of player 2's information sets, is a weak perfect Bayesian equilibrium of the noisy game. -/
theorem exercise_9_C_7c (hp' : p ∈ Set.Ioo (0 : ℝ) 1) :
    IsWeakPBE (bagC p hp) (bagProfile 0 0 0) (bagBelief 0 0) := by
  refine bagC_isWeakPBE_of hp' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> norm_num

/-- In a weak PBE of `bagC p` in which player 1 never plays `B`, player 2 plays `U` after both
signals and believes `T` at both information sets. -/
theorem bagC_weakPBE_of_T (hp' : p ∈ Set.Ioo (0 : ℝ) 1) {F : Fin 2 → Fin 5 → Fin 2 → ℝ}
    {μ : List (Fin 2) → ℝ} (h : IsWeakPBE (bagC p hp) F μ) (hx : F 0 0 0 = 0) :
    F 0 0 1 = 1 ∧ F 1 3 1 = 1 ∧ F 1 4 1 = 1 ∧ μ [0, 1] = 1 ∧ μ [1, 1] = 1 := by
  obtain ⟨-, -, -, f4, -, f6, -, e01, -, e11⟩ := bagC_weakPBE_facts hp' h
  obtain ⟨hx0, hx1⟩ := bagC_beh (h.1 0) (k := 0) rfl
  obtain ⟨hq0, hq1⟩ := bagC_beh (h.1 1) (k := 3) rfl
  obtain ⟨hr0, hr1⟩ := bagC_beh (h.1 1) (k := 4) rfl
  have hx' : F 0 0 1 = 1 := by linarith
  rw [hx, hx'] at f4 f6 e01 e11
  obtain ⟨h0, h1⟩ := hp'
  have hqB : F 1 3 0 = 0 := le_antisymm (by nlinarith) (hq0 0)
  have hqT : F 1 4 0 = 0 := le_antisymm (by nlinarith) (hr0 0)
  refine ⟨hx', by linarith, by linarith, ?_, ?_⟩
  · have : μ [0, 1] * (1 - p) = 1 * (1 - p) := by linarith
    exact mul_right_cancel₀ (by linarith) this
  · have : μ [1, 1] * p = 1 * p := by linarith
    exact mul_right_cancel₀ (by linarith) this

/-- **Exercise 9.C.7(c), pure strategies** (MWG, p. 305). For every `p ∈ (0, 1)`, in every weak
PBE in which player 1 plays a pure strategy, she plays `T`, player 2 plays `U` after both
signals, and player 2's beliefs put probability one on `T`: the weak PBE of
`exercise_9_C_7c` is the unique pure-strategy weak PBE. -/
theorem exercise_9_C_7c_pure_unique (hp' : p ∈ Set.Ioo (0 : ℝ) 1)
    {F : Fin 2 → Fin 5 → Fin 2 → ℝ} {μ : List (Fin 2) → ℝ} (h : IsWeakPBE (bagC p hp) F μ)
    (hpure : F 0 0 0 = 0 ∨ F 0 0 0 = 1) :
    F 0 0 1 = 1 ∧ F 1 3 1 = 1 ∧ F 1 4 1 = 1 ∧ μ [0, 1] = 1 ∧ μ [1, 1] = 1 := by
  rcases hpure with hx | hx
  · exact bagC_weakPBE_of_T hp' h hx
  · exfalso
    obtain ⟨f1, -, f3, -, f5, -⟩ := bagC_weakPBE_facts hp' h
    obtain ⟨hx0, hx1⟩ := bagC_beh (h.1 0) (k := 0) rfl
    obtain ⟨hq0, hq1⟩ := bagC_beh (h.1 1) (k := 3) rfl
    obtain ⟨hr0, hr1⟩ := bagC_beh (h.1 1) (k := 4) rfl
    have hx' : F 0 0 1 = 0 := by linarith
    rw [hx, hx'] at f3 f5
    rw [hx] at f1
    obtain ⟨h0, h1⟩ := hp'
    have hqB : F 1 3 0 = 1 := le_antisymm (by linarith [hq0 1]) (by nlinarith)
    have hqT : F 1 4 0 = 1 := le_antisymm (by linarith [hr0 1]) (by nlinarith)
    rw [hqB, hqT] at f1
    linarith

/-- **Exercise 9.C.7(c), uniqueness** (MWG, p. 305). For `1/3 < p < 2/3` the weak PBE of
`exercise_9_C_7c` is the unique weak PBE (behaviour strategies, any beliefs): `T` is strictly
better than `B` against every strategy of player 2, since `|3 (2p − 1)| < 1`. -/
theorem exercise_9_C_7c_unique (hp1 : 1 / 3 < p) (hp2 : p < 2 / 3)
    {F : Fin 2 → Fin 5 → Fin 2 → ℝ} {μ : List (Fin 2) → ℝ} (h : IsWeakPBE (bagC p hp) F μ) :
    F 0 0 1 = 1 ∧ F 1 3 1 = 1 ∧ F 1 4 1 = 1 ∧ μ [0, 1] = 1 ∧ μ [1, 1] = 1 := by
  have hp' : p ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  obtain ⟨f1, -⟩ := bagC_weakPBE_facts hp' h
  obtain ⟨hx0, -⟩ := bagC_beh (h.1 0) (k := 0) rfl
  obtain ⟨hq0, hq1⟩ := bagC_beh (h.1 1) (k := 3) rfl
  obtain ⟨hr0, hr1⟩ := bagC_beh (h.1 1) (k := 4) rfl
  have hD : 0 < 1 + 3 * (F 1 4 0 - F 1 3 0) * (2 * p - 1) := by
    rcases le_total 0 (2 * p - 1) with hs | hs
    · nlinarith [mul_nonneg (by linarith [hr0 0, hq0 1] : (0 : ℝ) ≤ F 1 4 0 - F 1 3 0 + 1) hs]
    · nlinarith [mul_nonneg (by linarith [hr0 1, hq0 0] : (0 : ℝ) ≤ 1 - (F 1 4 0 - F 1 3 0))
        (by linarith : (0 : ℝ) ≤ -(2 * p - 1))]
  exact bagC_weakPBE_of_T hp' h (le_antisymm (nonpos_of_mul_nonpos_left f1 hD) (hx0 0))

/-- **Correction to Exercise 9.C.7(c)** (MWG, p. 305). For `2/3 ≤ p < 1` there is a further weak
PBE: player 1 plays `T` with probability `p`, player 2 plays `D` with probability
`1 / (3 (2p − 1))` after signal `B` (where she believes `B` with probability `1/2`) and `U` after
signal `T`; player 1 is indifferent. -/
theorem exercise_9_C_7c_mixed_high (hp2 : 2 / 3 ≤ p) (hp1 : p < 1) :
    IsWeakPBE (bagC p hp) (bagProfile (1 - p) (1 / (3 * (2 * p - 1))) 0)
      (bagBelief (1 / 2) ((1 - p) ^ 2 / ((1 - p) ^ 2 + p ^ 2))) ∧
    bagProfile (1 - p) (1 / (3 * (2 * p - 1))) 0 0 0 1 ≠ 1 := by
  have hp' : p ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith, hp1⟩
  have hc : 1 ≤ 3 * (2 * p - 1) := by linarith
  have hD : 0 < (1 - p) ^ 2 + p ^ 2 := by positivity
  have hm4 : (1 - p) ^ 2 / ((1 - p) ^ 2 + p ^ 2) ≤ 1 / 2 := by
    rw [div_le_iff₀ hD]; nlinarith
  refine ⟨bagC_isWeakPBE_of hp' ⟨by linarith, by linarith⟩
    ⟨by positivity, by rw [div_le_one (by linarith)]; exact hc⟩ ⟨le_rfl, zero_le_one⟩
    ⟨by norm_num, by norm_num⟩ ⟨by positivity, by linarith⟩ ?_ ?_ (by norm_num) (by norm_num)
    (by linarith) (by norm_num) (by ring) ?_, ?_⟩
  · have : 1 + 3 * (0 - 1 / (3 * (2 * p - 1))) * (2 * p - 1) = 0 := by
      field_simp [(by linarith : (0 : ℝ) < 2 * p - 1).ne']; ring
    rw [this, mul_zero]
  · have : 1 + 3 * (0 - 1 / (3 * (2 * p - 1))) * (2 * p - 1) = 0 := by
      field_simp [(by linarith : (0 : ℝ) < 2 * p - 1).ne']; ring
    rw [this, mul_zero]
  · rw [div_mul_eq_mul_div, div_eq_iff hD.ne']
    ring
  · simp only [bagProfile_values]
    linarith

/-- **Correction to Exercise 9.C.7(c)** (MWG, p. 305). For `0 < p ≤ 1/3` there is a further weak
PBE: player 1 plays `B` with probability `p`, player 2 plays `U` after signal `B` and `D` with
probability `1 / (3 (1 − 2p))` after signal `T` (where she believes `B` with probability `1/2`);
player 1 is indifferent. -/
theorem exercise_9_C_7c_mixed_low (hp0 : 0 < p) (hp1 : p ≤ 1 / 3) :
    IsWeakPBE (bagC p hp) (bagProfile p 0 (1 / (3 * (1 - 2 * p))))
      (bagBelief (p ^ 2 / (p ^ 2 + (1 - p) ^ 2)) (1 / 2)) ∧
    bagProfile p 0 (1 / (3 * (1 - 2 * p))) 0 0 1 ≠ 1 := by
  have hp' : p ∈ Set.Ioo (0 : ℝ) 1 := ⟨hp0, by linarith⟩
  have hc : 1 ≤ 3 * (1 - 2 * p) := by linarith
  have hD : 0 < p ^ 2 + (1 - p) ^ 2 := by positivity
  have hm3 : p ^ 2 / (p ^ 2 + (1 - p) ^ 2) ≤ 1 / 2 := by
    rw [div_le_iff₀ hD]; nlinarith
  refine ⟨bagC_isWeakPBE_of hp' ⟨hp0.le, by linarith⟩ ⟨le_rfl, zero_le_one⟩
    ⟨by positivity, by rw [div_le_one (by linarith)]; exact hc⟩
    ⟨by positivity, by linarith⟩ ⟨by norm_num, by norm_num⟩ ?_ ?_ (by linarith) (by norm_num)
    (by norm_num) (by norm_num) ?_ (by ring), ?_⟩
  · have : 1 + 3 * (1 / (3 * (1 - 2 * p)) - 0) * (2 * p - 1) = 0 := by
      field_simp [(by linarith : (0 : ℝ) < 1 - 2 * p).ne']; ring
    rw [this, mul_zero]
  · have : 1 + 3 * (1 / (3 * (1 - 2 * p)) - 0) * (2 * p - 1) = 0 := by
      field_simp [(by linarith : (0 : ℝ) < 1 - 2 * p).ne']; ring
    rw [this, mul_zero]
  · rw [div_mul_eq_mul_div, div_eq_iff hD.ne']
    ring
  · simp only [bagProfile_values]
    linarith

/-- **Exercise 9.C.7(c), corrected** (MWG, p. 305). The weak PBE of the noisy game is unique
(player 1 plays `T` for sure in every weak PBE) if and only if `1/3 < p < 2/3`. -/
theorem exercise_9_C_7c_unique_iff (hp' : p ∈ Set.Ioo (0 : ℝ) 1) :
    (∀ F μ, IsWeakPBE (bagC p hp) F μ → F 0 0 1 = 1) ↔ 1 / 3 < p ∧ p < 2 / 3 := by
  constructor
  · intro hU
    by_contra hn
    rcases not_and_or.1 hn with h | h
    · have h' := not_lt.1 h
      exact (exercise_9_C_7c_mixed_low (hp := hp) hp'.1 h').2 (hU _ _
        (exercise_9_C_7c_mixed_low (hp := hp) hp'.1 h').1)
    · have h' := not_lt.1 h
      exact (exercise_9_C_7c_mixed_high (hp := hp) h' hp'.2).2 (hU _ _
        (exercise_9_C_7c_mixed_high (hp := hp) h' hp'.2).1)
  · rintro ⟨h1, h2⟩ F μ h
    exact (exercise_9_C_7c_unique h1 h2 h).1

end MWG.DynamicGames

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Two-period bargaining with a privately informed buyer

MWG, Exercise 9.C.3 (p. 304) and Exercise 9.C.6 for it. The seller (value `0`) names a
price in each of two periods; the buyer, whose value `v ∈ {vL, vH}` (`0 < vL < vH`,
`Prob(vH) = λ ∈ (0, 1)`) only she knows, accepts or rejects; payoffs in period 2 are discounted
by `δ ∈ (0, 1)`; the buyer accepts when indifferent.

The model (a direct description of the extensive form's pure strategies and of a weak PBE,
Definition 9.C.3). `SBProfile`: the seller's first price `p1`, the buyer's period-1 acceptance
rule `acc b p` (type `b`, `true` = high, at every price `p`), the seller's second price
`p2 p` after each rejected `p`, and the seller's belief `μ p` that `v = vH` there. In period 2 the
buyer accepts `q` iff `q ≤ v` (the unique sequentially rational move given the tie rule,
`sb_period2`). `IsSBWeakPBE`: the buyer is sequentially rational at every price, the seller is
sequentially rational after every rejected price given her belief, the belief is Bayes'
posterior after the equilibrium price whenever someone rejects it, and the seller's first price
is optimal against every deviation of her whole strategy (price `p` now, price `q` after a
rejection of `p`) given the buyer's strategy and the prior.

* `exercise_9_C_3a`: with `p̂ = (1 − δ) vH + δ vL` (the highest price the high type accepts when
  she expects `vL` next), `A = vL`, `B = λ p̂ + (1 − λ) δ vL`, `C = δ λ vH`, every pure weak PBE has
  one of three outcomes: (i) `p1 = vL`, both types buy at once (needs `B, C ≤ A`); (ii)
  `p1 = p̂`, the high type buys at once, the low type in period 2 at `vL` (needs `A, C ≤ B`);
  (iii) `p1 > vH`, both types reject and the seller charges `vH` in period 2 (needs
  `A, B ≤ C`). Each outcome is a weak PBE outcome exactly under its condition, the seller's
  payoff is `max {A, B, C}`, and a weak PBE always exists. Along the way: the seller's period-2
  price is always `vL` or `vH` (`sb_p2_mem`), the buyer's period-1 choice has a cutoff
  structure (the high type accepts whenever the low type does, `sb_acc_mono`).
* Exercise 9.C.6 (two types). Definition 9.C.4 is stated for finite games, so it is read here
  through its implication for these games (structural consistency, recorded in
  docs/corrections.md): after every price that some type rejects, the seller's belief is Bayes'
  posterior given the buyer's strategy (`IsSBConsistent`; `sbPost_tendsto` shows this is what
  limits of Bayes beliefs from trembles converging to the profile give). Then:
  `exercise_9_C_6_two_types_none` (if `λ vH > vL` there is no pure-strategy sequential
  equilibrium: after prices between `p̂` and `vH` no pure continuation is consistent) and
  `exercise_9_C_6_two_types` (if `λ vH ≤ vL`, the pure sequential equilibria have exactly the
  outcomes (i)-(ii) above under the same conditions, and one exists).
* Exercise 9.C.3(b), values uniform on `[0, 1]` (`v̲ = 0`, normalised `v̄ = 1`; the case `v̲ > 0` is
  in `SellerBuyerGeneral.lean`). `exercise_9_C_3b_cutoff`: for every expected second price the
  buyer's period-1 choice is a cutoff rule. In a reduced model (`IsSBUWeakPBE`: first price, second
  price after each rejected price, cutoff buyers, uniform prior through its distribution function)
  `exercise_9_C_3b` proves that the linear-cutoff profile (cutoff `2p/(2 − δ)`, second price half
  the cutoff, first price `(2 − δ)²/(2 (4 − 3δ))`) is a weak PBE and the unique one with consistent
  beliefs (`IsSBUConsistent`); `exercise_9_C_3b_not_unique` exhibits another weak PBE first price
  (off-path beliefs after the seller's own deviations).
-/

namespace MWG.DynamicGames

/-- The buyer's value: `vH` for the high type (`true`), `vL` for the low type (`false`). -/
def sbVal (vL vH : ℝ) (b : Bool) : ℝ := if b then vH else vL

/-- The prior probability of a type: `λ` for the high type, `1 − λ` for the low type. -/
def sbPrior (lam : ℝ) (b : Bool) : ℝ := if b then lam else 1 - lam

/-- A buyer with value `v` who rejects in period 1 and faces the price `q` in period 2 accepts iff
`q ≤ v`, and gets `δ (v − q)` or `0`. -/
noncomputable def sbCont (δ v q : ℝ) : ℝ := if q ≤ v then δ * (v - q) else 0

/-- The seller's undiscounted period-2 expected revenue at price `q` when she believes the
buyer is of the high type with probability `m`. -/
noncomputable def sbRev (vL vH m q : ℝ) : ℝ :=
  m * (if q ≤ vH then q else 0) + (1 - m) * (if q ≤ vL then q else 0)

/-- A pure strategy profile with beliefs: the seller's first price `p1`, the buyer's period-1
acceptance rule `acc b p`, the seller's second price `p2 p` after a rejection of `p`, and her
belief `μ p` that the buyer is of the high type there. -/
structure SBProfile where
  /-- The seller's first-period price. -/
  p1 : ℝ
  /-- Whether type `b` accepts the first-period price `p`. -/
  acc : Bool → ℝ → Bool
  /-- The seller's second-period price after the first-period price `p` was rejected. -/
  p2 : ℝ → ℝ
  /-- The seller's belief that `v = vH` after the first-period price `p` was rejected. -/
  μ : ℝ → ℝ

/-- The seller's expected payoff when she charges `p` and, after a rejection, `q`, against the
buyer's acceptance rule `acc`. -/
noncomputable def sbPay (vL vH lam δ : ℝ) (acc : Bool → ℝ → Bool) (p q : ℝ) : ℝ :=
  lam * (if acc true p then p else δ * (if q ≤ vH then q else 0)) +
    (1 - lam) * (if acc false p then p else δ * (if q ≤ vL then q else 0))

/-- Bayes' posterior on the high type after the price `p` is rejected. -/
noncomputable def sbPost (lam : ℝ) (acc : Bool → ℝ → Bool) (p : ℝ) : ℝ :=
  (if acc true p then 0 else lam) /
    ((if acc true p then 0 else lam) + (if acc false p then 0 else 1 - lam))

/-- **Exercise 9.C.3** (MWG, p. 304). A pure-strategy weak perfect Bayesian equilibrium of the
two-type bargaining game (Definition 9.C.3). -/
def IsSBWeakPBE (vL vH lam δ : ℝ) (P : SBProfile) : Prop :=
  (∀ b p, P.acc b p = true ↔ sbCont δ (sbVal vL vH b) (P.p2 p) ≤ sbVal vL vH b - p) ∧
  (∀ p, 0 ≤ P.μ p ∧ P.μ p ≤ 1) ∧
  (∀ p q, δ * sbRev vL vH (P.μ p) q ≤ δ * sbRev vL vH (P.μ p) (P.p2 p)) ∧
  ((P.acc true P.p1 = false ∨ P.acc false P.p1 = false) → P.μ P.p1 = sbPost lam P.acc P.p1) ∧
  ∀ p q, sbPay vL vH lam δ P.acc p q ≤ sbPay vL vH lam δ P.acc P.p1 (P.p2 P.p1)

/-- **Exercise 9.C.6** (MWG, p. 304), structural consistency: after every price that some type
rejects (on or off the equilibrium path), the seller's belief is Bayes' posterior. -/
def IsSBConsistent (lam : ℝ) (P : SBProfile) : Prop :=
  ∀ p, (P.acc true p = false ∨ P.acc false p = false) → P.μ p = sbPost lam P.acc p

/-- In period 2 the buyer is sequentially rational exactly when she accepts iff `q ≤ v`
(accepting gives `δ (v − q)`, rejecting `0`, and she accepts when indifferent). -/
theorem sb_period2 {δ v q : ℝ} (hd : 0 < δ) : 0 ≤ δ * (v - q) ↔ q ≤ v := by
  constructor
  · intro h
    by_contra hn
    push Not at hn
    nlinarith
  · intro h
    exact mul_nonneg hd.le (by linarith)

variable {vL vH lam δ : ℝ}

theorem sbRev_vL (hLH : vL < vH) (m : ℝ) : sbRev vL vH m vL = vL := by
  simp only [sbRev, hLH.le, le_refl, ↓reduceIte]
  ring

theorem sbRev_vH (hLH : vL < vH) (m : ℝ) : sbRev vL vH m vH = m * vH := by
  simp only [sbRev, le_refl, ↓reduceIte, not_le.2 hLH]
  ring

/-- The seller's period-2 revenue never exceeds the larger of `vL` (price `vL`, both types
buy) and `m vH` (price `vH`, only the high type buys). -/
theorem sbRev_le (hL : 0 < vL) (hLH : vL < vH) {m : ℝ} (hm : 0 ≤ m ∧ m ≤ 1) (q : ℝ) :
    sbRev vL vH m q ≤ vL ∨ sbRev vL vH m q ≤ m * vH := by
  unfold sbRev
  by_cases h1 : q ≤ vL
  · left
    simp only [h1, le_trans h1 hLH.le, ↓reduceIte]
    nlinarith
  · by_cases h2 : q ≤ vH
    · right
      simp only [h1, h2, ↓reduceIte]
      nlinarith
    · left
      simp only [h1, h2, ↓reduceIte]
      linarith

/-- With `0 < vL < vH`, the seller's optimal period-2 price is `vL` or `vH`, whatever her
belief. -/
theorem sb_p2_mem (hL : 0 < vL) (hLH : vL < vH) {m q : ℝ} (hm : 0 ≤ m ∧ m ≤ 1)
    (hq : ∀ q', sbRev vL vH m q' ≤ sbRev vL vH m q) : q = vL ∨ q = vH := by
  have h1 := hq vL
  have h2 := hq vH
  rw [sbRev_vL hLH] at h1
  rw [sbRev_vH hLH] at h2
  unfold sbRev at h1 h2
  by_cases a : q ≤ vL
  · left
    simp only [a, le_trans a hLH.le, ↓reduceIte] at h1
    linarith
  · by_cases b : q ≤ vH
    · right
      simp only [a, b, ↓reduceIte] at h1 h2
      have hm0 : 0 < m := by
        by_contra hn
        have : m = 0 := le_antisymm (not_lt.1 hn) hm.1
        rw [this] at h1
        linarith
      have : vH ≤ q := le_of_mul_le_mul_left (by linarith) hm0
      linarith
    · simp only [a, b, ↓reduceIte] at h1
      linarith

/-- The seller's period-2 price when one of the two prices is strictly better. -/
theorem sb_p2_of_lt (hLH : vL < vH) {m q : ℝ} (hq : ∀ q', sbRev vL vH m q' ≤ sbRev vL vH m q)
    (hq2 : q = vL ∨ q = vH) : (m * vH < vL → q = vL) ∧ (vL < m * vH → q = vH) := by
  have h1 := hq vL
  have h2 := hq vH
  rw [sbRev_vL hLH] at h1
  rw [sbRev_vH hLH] at h2
  constructor
  · intro h
    rcases hq2 with rfl | rfl
    · rfl
    · rw [sbRev_vH hLH] at h1
      linarith
  · intro h
    rcases hq2 with rfl | rfl
    · rw [sbRev_vL hLH] at h2
      linarith
    · rfl

/-- The highest first-period price that the high type accepts when she expects the price `vL`
in period 2: `p̂ = (1 − δ) vH + δ vL`. -/
def sbHat (vL vH δ : ℝ) : ℝ := (1 - δ) * vH + δ * vL

/-- The buyer's period-1 decision when the period-2 price is `vL` or `vH`: the low type accepts
`p` iff `p ≤ vL`; the high type accepts iff `p ≤ p̂` (period-2 price `vL`) or `p ≤ vH` (period-2
price `vH`). -/
theorem sb_buyer {acc : Bool → ℝ → Bool} {p2 : ℝ → ℝ} (hLH : vL < vH)
    (hacc : ∀ b p, acc b p = true ↔ sbCont δ (sbVal vL vH b) (p2 p) ≤ sbVal vL vH b - p)
    {p : ℝ} (hp2 : p2 p = vL ∨ p2 p = vH) :
    (acc false p = true ↔ p ≤ vL) ∧ (p2 p = vL → (acc true p = true ↔ p ≤ sbHat vL vH δ)) ∧
      (p2 p = vH → (acc true p = true ↔ p ≤ vH)) := by
  have hl := hacc false p
  have hh := hacc true p
  simp only [sbVal, Bool.false_eq_true, ↓reduceIte] at hl hh
  refine ⟨?_, fun h => ?_, fun h => ?_⟩
  · rcases hp2 with h | h <;> rw [h] at hl <;> rw [hl] <;>
      simp [sbCont, not_le.2 hLH]
  · rw [h] at hh
    rw [hh]
    simp only [sbCont, hLH.le, ↓reduceIte, sbHat]
    constructor <;> intro <;> linarith
  · rw [h] at hh
    rw [hh]
    simp only [sbCont, le_refl, ↓reduceIte, sub_self, mul_zero]
    constructor <;> intro <;> linarith

theorem sbHat_mem (hLH : vL < vH) (hd0 : 0 < δ) (hd1 : δ < 1) :
    vL < sbHat vL vH δ ∧ sbHat vL vH δ < vH := by
  unfold sbHat
  constructor <;> nlinarith

/-- An upper bound on the seller's payoff from any deviation, when her period-2 price is `vL`
after every price except possibly prices above `vH` (where it may be `vH`): at most the
largest of `vL`, `λ p̂ + (1 − λ) δ vL` and `δ λ vH`. -/
theorem sbPay_le (hL : 0 < vL) (hLH : vL < vH) (hl0 : 0 < lam) (hl1 : lam < 1) (hd0 : 0 < δ)
    (hd1 : δ < 1) {acc : Bool → ℝ → Bool} {p2 : ℝ → ℝ}
    (hacc : ∀ b p, acc b p = true ↔ sbCont δ (sbVal vL vH b) (p2 p) ≤ sbVal vL vH b - p)
    (hp2 : ∀ p, p2 p = vL ∨ (p2 p = vH ∧ vH < p)) {M : ℝ} (hA : vL ≤ M)
    (hB : lam * sbHat vL vH δ + (1 - lam) * (δ * vL) ≤ M) (hC : δ * (lam * vH) ≤ M)
    (p q : ℝ) : sbPay vL vH lam δ acc p q ≤ M := by
  obtain ⟨hh1, hh2⟩ := sbHat_mem hLH hd0 hd1
  have hp2' : p2 p = vL ∨ p2 p = vH := by rcases hp2 p with h | h; exacts [Or.inl h, Or.inr h.1]
  obtain ⟨bl, bh1, bh2⟩ := sb_buyer hLH hacc hp2'
  have hqL : (if q ≤ vL then q else 0) ≤ vL := by split_ifs <;> linarith
  unfold sbPay
  by_cases h1 : p ≤ vL
  · have hH : acc true p = true := by
      rcases hp2 p with h | h
      · exact (bh1 h).2 (by linarith)
      · linarith [h.2]
    rw [hH, bl.2 h1]
    simp only [↓reduceIte]
    nlinarith
  · have hLo : acc false p = false := by
      cases h : acc false p
      · rfl
      · exact absurd (bl.1 h) h1
    by_cases h2 : p ≤ sbHat vL vH δ
    · have hH : acc true p = true := by
        rcases hp2 p with h | h
        · exact (bh1 h).2 h2
        · linarith [h.2]
      rw [hH, hLo]
      simp only [↓reduceIte, Bool.false_eq_true]
      nlinarith [mul_le_mul_of_nonneg_left h2 hl0.le, mul_le_mul_of_nonneg_left hqL hd0.le]
    · have hH : acc true p = false := by
        cases h : acc true p
        · rfl
        · rcases hp2 p with h' | h'
          · exact absurd ((bh1 h').1 h) h2
          · exact absurd ((bh2 h'.1).1 h) (not_le.2 h'.2)
      rw [hH, hLo]
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hR := sbRev_le hL hLH ⟨hl0.le, hl1.le⟩ q
      unfold sbRev at hR
      rcases hR with hR | hR <;> nlinarith

/-- In a weak PBE the seller's period-2 price after any rejected price is optimal for her belief,
and it is `vL` or `vH`. -/
theorem sb_weakPBE_p2 (hL : 0 < vL) (hLH : vL < vH) (hd0 : 0 < δ) {P : SBProfile}
    (h : IsSBWeakPBE vL vH lam δ P) (p : ℝ) :
    (∀ q, sbRev vL vH (P.μ p) q ≤ sbRev vL vH (P.μ p) (P.p2 p)) ∧
      (P.p2 p = vL ∨ P.p2 p = vH) := by
  have hq : ∀ q, sbRev vL vH (P.μ p) q ≤ sbRev vL vH (P.μ p) (P.p2 p) :=
    fun q => le_of_mul_le_mul_left (h.2.2.1 p q) hd0
  exact ⟨hq, sb_p2_mem hL hLH (h.2.1 p) hq⟩

/-- **Exercise 9.C.3(a), cutoff structure** (MWG, p. 304). In a weak PBE, at every first-period
price the high type accepts whenever the low type does. -/
theorem sb_acc_mono (hL : 0 < vL) (hLH : vL < vH) (hd0 : 0 < δ) (hd1 : δ < 1)
    {P : SBProfile} (h : IsSBWeakPBE vL vH lam δ P) (p : ℝ) (hp : P.acc false p = true) :
    P.acc true p = true := by
  obtain ⟨-, hp2⟩ := sb_weakPBE_p2 hL hLH hd0 h p
  obtain ⟨bl, bh1, bh2⟩ := sb_buyer hLH h.1 hp2
  obtain ⟨hh1, -⟩ := sbHat_mem hLH hd0 hd1
  have := bl.1 hp
  rcases hp2 with h2 | h2
  · exact (bh1 h2).2 (by linarith)
  · exact (bh2 h2).2 (by linarith)

/-- **Exercise 9.C.3(a)** (MWG, p. 304), necessity. Every pure-strategy weak PBE has one of three
outcomes: (i) `p1 = vL` and both types buy at once, possible only if `vL ≥ λ p̂ + (1 − λ) δ vL`
and `vL ≥ δ λ vH`; (ii) `p1 = p̂`, the high type buys at once and the low type buys at `vL` in
period 2, possible only if `λ p̂ + (1 − λ) δ vL` is the largest of the three numbers; (iii)
`p1 > vH`, nobody buys in period 1 and the seller charges `vH` in period 2, possible only if
`δ λ vH` is the largest. In each case the seller's payoff is the largest of the three. -/
theorem sb_weakPBE_outcome (hL : 0 < vL) (hLH : vL < vH) (hl0 : 0 < lam) (hl1 : lam < 1)
    (hd0 : 0 < δ) (hd1 : δ < 1) {P : SBProfile} (h : IsSBWeakPBE vL vH lam δ P) :
    (P.p1 = vL ∧ P.acc true P.p1 = true ∧ P.acc false P.p1 = true ∧
        lam * sbHat vL vH δ + (1 - lam) * (δ * vL) ≤ vL ∧ δ * (lam * vH) ≤ vL ∧
        sbPay vL vH lam δ P.acc P.p1 (P.p2 P.p1) = vL) ∨
    (P.p1 = sbHat vL vH δ ∧ P.acc true P.p1 = true ∧ P.acc false P.p1 = false ∧
        P.p2 P.p1 = vL ∧ vL ≤ lam * sbHat vL vH δ + (1 - lam) * (δ * vL) ∧
        δ * (lam * vH) ≤ lam * sbHat vL vH δ + (1 - lam) * (δ * vL) ∧
        sbPay vL vH lam δ P.acc P.p1 (P.p2 P.p1) = lam * sbHat vL vH δ + (1 - lam) * (δ * vL)) ∨
    (vH < P.p1 ∧ P.acc true P.p1 = false ∧ P.acc false P.p1 = false ∧ P.p2 P.p1 = vH ∧
        vL ≤ δ * (lam * vH) ∧ lam * sbHat vL vH δ + (1 - lam) * (δ * vL) ≤ δ * (lam * vH) ∧
        sbPay vL vH lam δ P.acc P.p1 (P.p2 P.p1) = δ * (lam * vH)) := by
  obtain ⟨hh1, hh2⟩ := sbHat_mem hLH hd0 hd1
  have hroot := h.2.2.2.2
  have hB2 := fun p => sb_buyer hLH h.1 (sb_weakPBE_p2 hL hLH hd0 h p).2
  have hp2 := fun p => (sb_weakPBE_p2 hL hLH hd0 h p).2
  set S := sbPay vL vH lam δ P.acc P.p1 (P.p2 P.p1) with hS
  -- the three deviations
  have dA : vL ≤ S := by
    have hLo : P.acc false vL = true := (hB2 vL).1.2 le_rfl
    have hH : P.acc true vL = true := sb_acc_mono hL hLH hd0 hd1 h vL hLo
    have := hroot vL 0
    rw [sbPay, hH, hLo] at this
    simp only [↓reduceIte] at this
    linarith
  have dB : lam * sbHat vL vH δ + (1 - lam) * (δ * vL) ≤ S := by
    have hLo : P.acc false (sbHat vL vH δ) = false := by
      cases hc : P.acc false (sbHat vL vH δ)
      · rfl
      · exact absurd ((hB2 _).1.1 hc) (not_le.2 hh1)
    have hH : P.acc true (sbHat vL vH δ) = true := by
      rcases hp2 (sbHat vL vH δ) with h2 | h2
      · exact ((hB2 _).2.1 h2).2 le_rfl
      · exact ((hB2 _).2.2 h2).2 hh2.le
    have := hroot (sbHat vL vH δ) vL
    rw [sbPay, hH, hLo] at this
    simp only [↓reduceIte, Bool.false_eq_true, le_refl] at this
    linarith
  have dC : δ * (lam * vH) ≤ S := by
    have hLo : P.acc false (vH + 1) = false := by
      cases hc : P.acc false (vH + 1)
      · rfl
      · have := (hB2 _).1.1 hc; linarith
    have hH : P.acc true (vH + 1) = false := by
      cases hc : P.acc true (vH + 1)
      · rfl
      · rcases hp2 (vH + 1) with h2 | h2
        · have := ((hB2 _).2.1 h2).1 hc; linarith
        · have := ((hB2 _).2.2 h2).1 hc; linarith
    have := hroot (vH + 1) vH
    rw [sbPay, hH, hLo] at this
    simp only [↓reduceIte, Bool.false_eq_true, le_refl, not_le.2 hLH] at this
    linarith
  -- the equilibrium
  cases hLo : P.acc false P.p1
  · cases hH : P.acc true P.p1
    · -- both reject: the posterior is `λ`
      have hμ : P.μ P.p1 = lam := by
        rw [h.2.2.2.1 (Or.inl hH), sbPost, hH, hLo]
        simp
      obtain ⟨hq, -⟩ := sb_weakPBE_p2 hL hLH hd0 h P.p1
      rw [hμ] at hq
      have hS' : S = δ * sbRev vL vH lam (P.p2 P.p1) := by
        rw [hS, sbPay, hH, hLo, sbRev]
        simp only [Bool.false_eq_true, ↓reduceIte]
        ring
      rcases hp2 P.p1 with h2 | h2
      · rw [hS', h2, sbRev_vL hLH] at dA
        nlinarith
      · rw [hS', h2, sbRev_vH hLH] at dA dB
        have hgt : vH < P.p1 := by
          by_contra hn
          have := ((hB2 _).2.2 h2).2 (not_lt.1 hn)
          rw [hH] at this
          exact Bool.false_ne_true this
        right; right
        refine ⟨hgt, rfl, rfl, h2, by linarith, by linarith, ?_⟩
        rw [hS', h2, sbRev_vH hLH]
    · -- only the low type rejects: the posterior is `0`
      have hμ : P.μ P.p1 = 0 := by
        rw [h.2.2.2.1 (Or.inr hLo), sbPost, hH, hLo]
        simp
      obtain ⟨hq, -⟩ := sb_weakPBE_p2 hL hLH hd0 h P.p1
      rw [hμ] at hq
      have h2 : P.p2 P.p1 = vL :=
        (sb_p2_of_lt hLH hq (hp2 P.p1)).1 (by linarith)
      have hle : P.p1 ≤ sbHat vL vH δ := ((hB2 _).2.1 h2).1 hH
      have hS' : S = lam * P.p1 + (1 - lam) * (δ * vL) := by
        rw [hS, sbPay, hH, hLo, h2]
        simp only [Bool.false_eq_true, ↓reduceIte, le_refl]
      have heq : P.p1 = sbHat vL vH δ := by
        rw [hS'] at dB
        exact le_antisymm hle (le_of_mul_le_mul_left (by linarith) hl0)
      right; left
      have hSv : S = lam * sbHat vL vH δ + (1 - lam) * (δ * vL) := by rw [hS', heq]
      refine ⟨heq, rfl, rfl, h2, by linarith, by linarith, hSv⟩
  · have hH := sb_acc_mono hL hLH hd0 hd1 h P.p1 hLo
    have hle := (hB2 P.p1).1.1 hLo
    have hS' : S = P.p1 := by
      rw [hS, sbPay, hH, hLo]
      simp only [↓reduceIte]
      ring
    have heq : P.p1 = vL := le_antisymm hle (by linarith)
    left
    exact ⟨heq, hH, rfl, by linarith, by linarith, by rw [hS', heq]⟩

/-- The profile with first price `p1`, period-2 prices `p2`, beliefs `μ`, and the buyer's
sequentially rational period-1 acceptance rule. -/
noncomputable def sbBuild (vL vH δ p1 : ℝ) (p2 μ : ℝ → ℝ) : SBProfile where
  p1 := p1
  acc b p := decide (sbCont δ (sbVal vL vH b) (p2 p) ≤ sbVal vL vH b - p)
  p2 := p2
  μ := μ

theorem sbBuild_acc (p1 : ℝ) (p2 μ : ℝ → ℝ) (b : Bool) (p : ℝ) :
    (sbBuild vL vH δ p1 p2 μ).acc b p = true ↔
      sbCont δ (sbVal vL vH b) ((sbBuild vL vH δ p1 p2 μ).p2 p) ≤ sbVal vL vH b - p := by
  simp [sbBuild]

/-- A sufficient condition for `sbBuild` to be a weak PBE: beliefs in `[0, 1]`, period-2 prices
optimal for the beliefs and equal to `vL` except possibly above `vH`, Bayes' rule at `p1`, and a
payoff at `p1` at least the three benchmark payoffs. -/
theorem sbBuild_isWeakPBE (hL : 0 < vL) (hLH : vL < vH) (hl0 : 0 < lam) (hl1 : lam < 1)
    (hd0 : 0 < δ) (hd1 : δ < 1) {p1 : ℝ} {p2 μ : ℝ → ℝ} (hμ : ∀ p, 0 ≤ μ p ∧ μ p ≤ 1)
    (hopt : ∀ p q, sbRev vL vH (μ p) q ≤ sbRev vL vH (μ p) (p2 p))
    (hp2 : ∀ p, p2 p = vL ∨ (p2 p = vH ∧ vH < p))
    (hbayes : ((sbBuild vL vH δ p1 p2 μ).acc true p1 = false ∨
      (sbBuild vL vH δ p1 p2 μ).acc false p1 = false) →
      μ p1 = sbPost lam (sbBuild vL vH δ p1 p2 μ).acc p1)
    (hA : vL ≤ sbPay vL vH lam δ (sbBuild vL vH δ p1 p2 μ).acc p1 (p2 p1))
    (hB : lam * sbHat vL vH δ + (1 - lam) * (δ * vL) ≤
      sbPay vL vH lam δ (sbBuild vL vH δ p1 p2 μ).acc p1 (p2 p1))
    (hC : δ * (lam * vH) ≤ sbPay vL vH lam δ (sbBuild vL vH δ p1 p2 μ).acc p1 (p2 p1)) :
    IsSBWeakPBE vL vH lam δ (sbBuild vL vH δ p1 p2 μ) :=
  ⟨sbBuild_acc p1 p2 μ, hμ, fun p q => mul_le_mul_of_nonneg_left (hopt p q) hd0.le, hbayes,
    fun p q => sbPay_le hL hLH hl0 hl1 hd0 hd1 (sbBuild_acc p1 p2 μ) hp2 hA hB hC p q⟩

/-- The buyer's choices in `sbBuild` when the period-2 price is `vL` after `p`. -/
theorem sbBuild_acc_vL (hLH : vL < vH) {p1 p : ℝ} {p2 μ : ℝ → ℝ} (h2 : p2 p = vL) :
    ((sbBuild vL vH δ p1 p2 μ).acc false p = true ↔ p ≤ vL) ∧
      ((sbBuild vL vH δ p1 p2 μ).acc true p = true ↔ p ≤ sbHat vL vH δ) :=
  have h := sb_buyer (δ := δ) hLH (sbBuild_acc p1 p2 μ) (Or.inl h2)
  ⟨h.1, h.2.1 h2⟩

/-- The period-2 revenue is at most `vL` at any belief `m` with `m vH ≤ vL`. -/
theorem sbRev_le_vL (hL : 0 < vL) (hLH : vL < vH) {m : ℝ} (hm : 0 ≤ m ∧ m ≤ 1)
    (hmv : m * vH ≤ vL) (q : ℝ) : sbRev vL vH m q ≤ vL := by
  rcases sbRev_le hL hLH hm q with h | h <;> linarith

theorem bool_false_of_not {b : Bool} (h : ¬ b = true) : b = false := by
  cases b
  · rfl
  · exact absurd rfl h

/-- **Exercise 9.C.3(a)** (MWG, p. 304). Write `p̂ = (1 − δ) vH + δ vL`, `A = vL`,
`B = λ p̂ + (1 − λ) δ vL`, `C = δ λ vH`. Every pure-strategy weak PBE has outcome (i) `p1 = vL`,
immediate sale to both types, (ii) `p1 = p̂`, immediate sale to the high type and sale to the low
type at `vL` in period 2, or (iii) `p1 > vH`, no sale in period 1 and sale to the high type at
`vH` in period 2 (`sb_weakPBE_outcome`, which also gives the necessary conditions and the
seller's payoff `max {A, B, C}`); conversely each outcome is that of a weak PBE whenever its
benchmark is the largest of `A`, `B`, `C`. -/
theorem exercise_9_C_3a (hL : 0 < vL) (hLH : vL < vH) (hl0 : 0 < lam) (hl1 : lam < 1)
    (hd0 : 0 < δ) (hd1 : δ < 1) :
    (lam * sbHat vL vH δ + (1 - lam) * (δ * vL) ≤ vL → δ * (lam * vH) ≤ vL →
      ∃ P, IsSBWeakPBE vL vH lam δ P ∧ P.p1 = vL ∧ P.acc true P.p1 = true ∧
        P.acc false P.p1 = true) ∧
    (vL ≤ lam * sbHat vL vH δ + (1 - lam) * (δ * vL) →
      δ * (lam * vH) ≤ lam * sbHat vL vH δ + (1 - lam) * (δ * vL) →
      ∃ P, IsSBWeakPBE vL vH lam δ P ∧ P.p1 = sbHat vL vH δ ∧ P.acc true P.p1 = true ∧
        P.acc false P.p1 = false ∧ P.p2 P.p1 = vL) ∧
    (vL ≤ δ * (lam * vH) → lam * sbHat vL vH δ + (1 - lam) * (δ * vL) ≤ δ * (lam * vH) →
      ∃ P, IsSBWeakPBE vL vH lam δ P ∧ vH < P.p1 ∧ P.acc true P.p1 = false ∧
        P.acc false P.p1 = false ∧ P.p2 P.p1 = vH) := by
  obtain ⟨hh1, hh2⟩ := sbHat_mem hLH hd0 hd1
  have hμ0 : ∀ p : ℝ, 0 ≤ (fun _ => (0 : ℝ)) p ∧ (fun _ => (0 : ℝ)) p ≤ 1 :=
    fun _ => ⟨le_rfl, zero_le_one⟩
  have hopt0 : ∀ p q : ℝ, sbRev vL vH ((fun _ => (0 : ℝ)) p) q ≤
      sbRev vL vH ((fun _ => (0 : ℝ)) p) ((fun _ => vL) p) := fun p q => by
    rw [sbRev_vL hLH]
    exact sbRev_le_vL hL hLH ⟨le_rfl, zero_le_one⟩ (by simp [hL.le]) q
  refine ⟨fun hB hC => ?_, fun hA hC => ?_, fun hA hB => ?_⟩
  · -- (i)
    obtain ⟨bl, bh⟩ := sbBuild_acc_vL (δ := δ) (p1 := vL) (μ := fun _ => 0) hLH
      (p2 := fun _ => vL) (p := vL) rfl
    have hLo := bl.2 le_rfl
    have hH := bh.2 hh1.le
    have hpay : sbPay vL vH lam δ (sbBuild vL vH δ vL (fun _ => vL) fun _ => 0).acc vL vL =
        vL := by
      rw [sbPay, hH, hLo]
      simp only [↓reduceIte]
      ring
    refine ⟨_, sbBuild_isWeakPBE hL hLH hl0 hl1 hd0 hd1 hμ0 hopt0 (fun _ => Or.inl rfl)
      (fun h => ?_) (by rw [hpay]) (by rw [hpay]; exact hB) (by rw [hpay]; exact hC),
      rfl, hH, hLo⟩
    rcases h with h | h
    · rw [hH] at h; exact absurd h (by decide)
    · rw [hLo] at h; exact absurd h (by decide)
  · -- (ii)
    set P := sbBuild vL vH δ (sbHat vL vH δ) (fun _ => vL) fun _ => 0 with hP
    obtain ⟨bl, bh⟩ := sbBuild_acc_vL (δ := δ) (p1 := sbHat vL vH δ) (μ := fun _ => 0) hLH
      (p2 := fun _ => vL) (p := sbHat vL vH δ) rfl
    have hH : P.acc true (sbHat vL vH δ) = true := bh.2 le_rfl
    have hLo : P.acc false (sbHat vL vH δ) = false :=
      bool_false_of_not fun h => absurd (bl.1 h) (not_le.2 hh1)
    have hpay : sbPay vL vH lam δ P.acc (sbHat vL vH δ) vL =
        lam * sbHat vL vH δ + (1 - lam) * (δ * vL) := by
      rw [sbPay, hH, hLo]
      simp only [↓reduceIte, Bool.false_eq_true, le_refl]
    refine ⟨P, sbBuild_isWeakPBE hL hLH hl0 hl1 hd0 hd1 hμ0 hopt0 (fun _ => Or.inl rfl)
      (fun _ => ?_) (by rw [hpay]; exact hA) (by rw [hpay]) (by rw [hpay]; exact hC),
      rfl, hH, hLo, rfl⟩
    rw [sbPost, hH, hLo]
    simp
  · -- (iii)
    have hlv : vL ≤ lam * vH := by nlinarith
    set p2 : ℝ → ℝ := fun p => if p = vH + 1 then vH else vL with hp2
    set μ : ℝ → ℝ := fun p => if p = vH + 1 then lam else 0 with hμ
    set P := sbBuild vL vH δ (vH + 1) p2 μ with hP
    have h2 : p2 (vH + 1) = vH := by simp [hp2]
    obtain ⟨bl, -, bh⟩ := sb_buyer (δ := δ) hLH (sbBuild_acc (vH + 1) p2 μ)
      (p := vH + 1) (Or.inr h2)
    have hH : P.acc true (vH + 1) = false :=
      bool_false_of_not fun h => by have := (bh h2).1 h; linarith
    have hLo : P.acc false (vH + 1) = false :=
      bool_false_of_not fun h => by have := bl.1 h; linarith
    have hpay : sbPay vL vH lam δ P.acc (vH + 1) (p2 (vH + 1)) = δ * (lam * vH) := by
      rw [sbPay, hH, hLo, h2]
      simp only [Bool.false_eq_true, ↓reduceIte, le_refl, not_le.2 hLH]
      ring
    have hμ' : ∀ p, 0 ≤ μ p ∧ μ p ≤ 1 := fun p => by
      simp only [hμ]; split_ifs <;> constructor <;> linarith
    have hopt : ∀ p q, sbRev vL vH (μ p) q ≤ sbRev vL vH (μ p) (p2 p) := fun p q => by
      by_cases hp : p = vH + 1
      · simp only [hμ, hp2, hp, ↓reduceIte]
        rw [sbRev_vH hLH]
        rcases sbRev_le hL hLH ⟨hl0.le, hl1.le⟩ q with h | h <;> linarith
      · simp only [hμ, hp2, hp, ↓reduceIte]
        rw [sbRev_vL hLH]
        exact sbRev_le_vL hL hLH ⟨le_rfl, zero_le_one⟩ (by simp [hL.le]) q
    have hp2' : ∀ p, p2 p = vL ∨ (p2 p = vH ∧ vH < p) := fun p => by
      by_cases hp : p = vH + 1
      · right; simp only [hp2, hp, ↓reduceIte]; exact ⟨trivial, by linarith⟩
      · left; simp [hp2, hp]
    refine ⟨P, sbBuild_isWeakPBE hL hLH hl0 hl1 hd0 hd1 hμ' hopt hp2' (fun _ => ?_)
      (by rw [hpay]; exact hA) (by rw [hpay]; exact hB) (by rw [hpay]), by simp [hP, sbBuild],
      hH, hLo, h2⟩
    rw [sbPost, hH, hLo]
    simp [hμ]

/-- A weak PBE always exists in the two-type game (one of the three benchmarks is largest). -/
theorem exercise_9_C_3a_exists (hL : 0 < vL) (hLH : vL < vH) (hl0 : 0 < lam) (hl1 : lam < 1)
    (hd0 : 0 < δ) (hd1 : δ < 1) : ∃ P, IsSBWeakPBE vL vH lam δ P := by
  obtain ⟨h1, h2, h3⟩ := exercise_9_C_3a hL hLH hl0 hl1 hd0 hd1
  rcases le_total (lam * sbHat vL vH δ + (1 - lam) * (δ * vL)) vL with hB | hB
  · rcases le_total (δ * (lam * vH)) vL with hC | hC
    · obtain ⟨P, hP, -⟩ := h1 hB hC; exact ⟨P, hP⟩
    · obtain ⟨P, hP, -⟩ := h3 hC (by linarith); exact ⟨P, hP⟩
  · rcases le_total (δ * (lam * vH)) (lam * sbHat vL vH δ + (1 - lam) * (δ * vL)) with hC | hC
    · obtain ⟨P, hP, -⟩ := h2 hB hC; exact ⟨P, hP⟩
    · obtain ⟨P, hP, -⟩ := h3 (by linarith) hC; exact ⟨P, hP⟩

/-- **Exercise 9.C.3(a), examples** (MWG, p. 304). Each of the three outcomes occurs: with
`vL = 1`, `vH = 2`, `δ = 1/2`, outcome (i) for `λ = 1/10` and outcome (ii) for `λ = 9/10`; with
`vL = 1`, `vH = 10`, `λ = δ = 9/10`, outcome (iii). -/
theorem exercise_9_C_3a_examples :
    (∃ P, IsSBWeakPBE 1 2 (1 / 10) (1 / 2) P ∧ P.p1 = 1) ∧
    (∃ P, IsSBWeakPBE 1 2 (9 / 10) (1 / 2) P ∧ P.p1 = 3 / 2) ∧
    (∃ P, IsSBWeakPBE 1 10 (9 / 10) (9 / 10) P ∧ 10 < P.p1) := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨P, hP, h1, -⟩ := (exercise_9_C_3a (vL := 1) (vH := 2) (lam := 1 / 10)
      (δ := 1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)).1 (by norm_num [sbHat]) (by norm_num)
    exact ⟨P, hP, h1⟩
  · obtain ⟨P, hP, h1, -⟩ := (exercise_9_C_3a (vL := 1) (vH := 2) (lam := 9 / 10)
      (δ := 1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)).2.1 (by norm_num [sbHat]) (by norm_num [sbHat])
    exact ⟨P, hP, by rw [h1]; norm_num [sbHat]⟩
  · obtain ⟨P, hP, h1, -⟩ := (exercise_9_C_3a (vL := 1) (vH := 10) (lam := 9 / 10)
      (δ := 9 / 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)).2.2 (by norm_num) (by norm_num [sbHat])
    exact ⟨P, hP, h1⟩

/-- Bayes' posterior as a function of the two types' rejection probabilities. -/
theorem sbPost_eq (lam : ℝ) (acc : Bool → ℝ → Bool) (p : ℝ) :
    sbPost lam acc p = lam * (if acc true p then 0 else 1) /
      (lam * (if acc true p then 0 else 1) + (1 - lam) * (if acc false p then 0 else 1)) := by
  unfold sbPost
  split_ifs <;> simp

open Filter Topology in
/-- **Exercise 9.C.6, the consistency reading** (MWG, pp. 290 and 304). Suppose trembles give the
two types rejection probabilities `rH n → aH` and `rL n → aL` (and the seller's own trembles do
not depend on the buyer's type, so they cancel). If some type rejects in the limit
(`aH + aL > 0`), the Bayes beliefs converge to Bayes' posterior for the limit strategies. So in
the limit of totally mixed profiles, the seller's belief after a price that some type rejects
is `sbPost`; this is what `IsSBConsistent` imposes. -/
theorem sbPost_tendsto (hl0 : 0 < lam) (hl1 : lam < 1) {rH rL : ℕ → ℝ} {aH aL : ℝ}
    (hH : Tendsto rH atTop (𝓝 aH)) (hL : Tendsto rL atTop (𝓝 aL)) (haH : 0 ≤ aH)
    (haL : 0 ≤ aL) (hpos : 0 < aH + aL) :
    Tendsto (fun n => lam * rH n / (lam * rH n + (1 - lam) * rL n)) atTop
      (𝓝 (lam * aH / (lam * aH + (1 - lam) * aL))) := by
  have hne : lam * aH + (1 - lam) * aL ≠ 0 := by
    rcases haH.lt_or_eq with h | h
    · have : 0 < lam * aH := mul_pos hl0 h
      have : 0 ≤ (1 - lam) * aL := mul_nonneg (by linarith) haL
      linarith
    · have : 0 < (1 - lam) * aL := mul_pos (by linarith) (by linarith)
      rw [← h]
      linarith
  exact (hH.const_mul lam).div ((hH.const_mul lam).add (hL.const_mul (1 - lam))) hne

/-- **Exercise 9.C.6, two types, `λ vH > vL`** (MWG, p. 304). There is no pure-strategy
sequential equilibrium (no pure-strategy weak PBE whose beliefs are consistent after every
rejected price): after a first price strictly between `p̂` and `vH`, if the seller is expected to
charge `vL` both types reject, so she believes `λ` and must charge `vH`; if she is expected to
charge `vH` only the low type rejects, so she believes `0` and must charge `vL`. -/
theorem exercise_9_C_6_two_types_none (hL : 0 < vL) (hLH : vL < vH) (hd0 : 0 < δ) (hd1 : δ < 1)
    (hgt : vL < lam * vH) :
    ¬ ∃ P, IsSBWeakPBE vL vH lam δ P ∧ IsSBConsistent lam P := by
  rintro ⟨P, h, hc⟩
  obtain ⟨hh1, hh2⟩ := sbHat_mem hLH hd0 hd1
  set p := (sbHat vL vH δ + vH) / 2 with hp
  obtain ⟨hq, hp2⟩ := sb_weakPBE_p2 hL hLH hd0 h p
  obtain ⟨bl, bh1, bh2⟩ := sb_buyer hLH h.1 hp2
  have hLo : P.acc false p = false := bool_false_of_not fun h' => by have := bl.1 h'; linarith
  rcases hp2 with h2 | h2
  · have hH : P.acc true p = false :=
      bool_false_of_not fun h' => by have := (bh1 h2).1 h'; linarith
    have hμ : P.μ p = lam := by
      rw [hc p (Or.inl hH), sbPost, hH, hLo]
      simp
    rw [hμ] at hq
    have := (sb_p2_of_lt hLH hq (Or.inl h2)).2 hgt
    linarith
  · have hH : P.acc true p = true := (bh2 h2).2 (by linarith)
    have hμ : P.μ p = 0 := by
      rw [hc p (Or.inr hLo), sbPost, hH, hLo]
      simp
    rw [hμ] at hq
    have := (sb_p2_of_lt hLH hq (Or.inr h2)).1 (by linarith)
    linarith

/-- **Exercise 9.C.6, two types, `λ vH ≤ vL`** (MWG, p. 304). The pure-strategy sequential
equilibria (weak PBE with consistent beliefs after every rejected price) have outcome (i)
(`p1 = vL`) or (ii) (`p1 = p̂`) of `exercise_9_C_3a`, never (iii); and each of (i), (ii) is the
outcome of one whenever its benchmark is the larger. -/
theorem exercise_9_C_6_two_types (hL : 0 < vL) (hLH : vL < vH) (hl0 : 0 < lam) (hl1 : lam < 1)
    (hd0 : 0 < δ) (hd1 : δ < 1) (hle : lam * vH ≤ vL) :
    (∀ P, IsSBWeakPBE vL vH lam δ P → IsSBConsistent lam P →
      P.p1 = vL ∨ P.p1 = sbHat vL vH δ) ∧
    (lam * sbHat vL vH δ + (1 - lam) * (δ * vL) ≤ vL →
      ∃ P, IsSBWeakPBE vL vH lam δ P ∧ IsSBConsistent lam P ∧ P.p1 = vL) ∧
    (vL ≤ lam * sbHat vL vH δ + (1 - lam) * (δ * vL) →
      ∃ P, IsSBWeakPBE vL vH lam δ P ∧ IsSBConsistent lam P ∧ P.p1 = sbHat vL vH δ) := by
  obtain ⟨hh1, hh2⟩ := sbHat_mem hLH hd0 hd1
  have hC : δ * (lam * vH) < vL := by nlinarith
  set p2 : ℝ → ℝ := fun _ => vL with hp2
  set μ : ℝ → ℝ := fun p => if sbHat vL vH δ < p then lam else 0 with hμ
  have hμ' : ∀ p, 0 ≤ μ p ∧ μ p ≤ 1 := fun p => by
    simp only [hμ]; split_ifs <;> constructor <;> linarith
  have hopt : ∀ p q, sbRev vL vH (μ p) q ≤ sbRev vL vH (μ p) (p2 p) := fun p q => by
    simp only [hp2]
    rw [sbRev_vL hLH]
    refine sbRev_le_vL hL hLH (hμ' p) ?_ q
    simp only [hμ]
    split_ifs
    · exact hle
    · simp [hL.le]
  have hcons : ∀ p1, IsSBConsistent lam (sbBuild vL vH δ p1 p2 μ) := by
    intro p1 p hp
    obtain ⟨bl, bh⟩ := sbBuild_acc_vL (δ := δ) (p1 := p1) (μ := μ) hLH (p2 := p2) (p := p) rfl
    change μ p = _
    have hLo : (sbBuild vL vH δ p1 p2 μ).acc false p = false := by
      rcases hp with hp | hp
      · exact bool_false_of_not fun h' => by
          have h1 := bl.1 h'
          rw [bh.2 (by linarith)] at hp
          exact absurd hp (by decide)
      · exact hp
    by_cases hgt : sbHat vL vH δ < p
    · have hH : (sbBuild vL vH δ p1 p2 μ).acc true p = false :=
        bool_false_of_not fun h' => absurd (bh.1 h') (not_le.2 hgt)
      rw [sbPost, hH, hLo]
      simp [hμ, hgt]
    · have hH : (sbBuild vL vH δ p1 p2 μ).acc true p = true := bh.2 (not_lt.1 hgt)
      rw [sbPost, hH, hLo]
      simp [hμ, hgt]
  refine ⟨fun P h _ => ?_, fun hB => ?_, fun hB => ?_⟩
  · rcases sb_weakPBE_outcome hL hLH hl0 hl1 hd0 hd1 h with h1 | h1 | h1
    · exact Or.inl h1.1
    · exact Or.inr h1.1
    · linarith [h1.2.2.2.2.1]
  · obtain ⟨bl, bh⟩ := sbBuild_acc_vL (δ := δ) (p1 := vL) (μ := μ) hLH (p2 := p2) (p := vL) rfl
    have hLo := bl.2 le_rfl
    have hH := bh.2 hh1.le
    have hpay : sbPay vL vH lam δ (sbBuild vL vH δ vL p2 μ).acc vL (p2 vL) = vL := by
      rw [sbPay, hH, hLo]
      simp only [↓reduceIte]
      ring
    refine ⟨_, sbBuild_isWeakPBE hL hLH hl0 hl1 hd0 hd1 hμ' hopt (fun _ => Or.inl rfl)
      (fun h => hcons vL vL h) (by rw [hpay]) (by rw [hpay]; exact hB)
      (by rw [hpay]; exact hC.le), hcons vL, rfl⟩
  · set P := sbBuild vL vH δ (sbHat vL vH δ) p2 μ
    obtain ⟨bl, bh⟩ := sbBuild_acc_vL (δ := δ) (p1 := sbHat vL vH δ) (μ := μ) hLH (p2 := p2)
      (p := sbHat vL vH δ) rfl
    have hH : P.acc true (sbHat vL vH δ) = true := bh.2 le_rfl
    have hLo : P.acc false (sbHat vL vH δ) = false :=
      bool_false_of_not fun h => absurd (bl.1 h) (not_le.2 hh1)
    have hpay : sbPay vL vH lam δ P.acc (sbHat vL vH δ) (p2 (sbHat vL vH δ)) =
        lam * sbHat vL vH δ + (1 - lam) * (δ * vL) := by
      rw [sbPay, hH, hLo]
      simp only [↓reduceIte, Bool.false_eq_true, le_refl, hp2]
    refine ⟨P, sbBuild_isWeakPBE hL hLH hl0 hl1 hd0 hd1 hμ' hopt (fun _ => Or.inl rfl)
      (fun h => hcons _ _ h) (by rw [hpay]; exact hB) (by rw [hpay])
      (by rw [hpay]; linarith), hcons _, rfl⟩

/-! ### Exercise 9.C.3(b): values uniform on `[0, 1]` -/

/-- The cutoff type at the first price `p` when the second price is `r`: the buyer with value
`v` accepts `p` iff `κ ≤ v` (`exercise_9_C_3b_cutoff`). -/
noncomputable def sbKappa (δ p r : ℝ) : ℝ := if r ≤ p then (p - δ * r) / (1 - δ) else p

/-- **Exercise 9.C.3(b), cutoff structure** (MWG, p. 304). Whatever second price `r` the buyer
expects after rejecting `p`, she accepts `p` iff her value is at least `κ(p, r)`: her gain from
accepting, `v − p − δ (v − r)⁺`, is strictly increasing in `v`. -/
theorem exercise_9_C_3b_cutoff (hd1 : δ < 1) (v p r : ℝ) :
    sbCont δ v r ≤ v - p ↔ sbKappa δ p r ≤ v := by
  unfold sbCont sbKappa
  have h1 : 0 < 1 - δ := by linarith
  by_cases hrv : r ≤ v
  · simp only [hrv, ↓reduceIte]
    split_ifs with hrp
    · rw [div_le_iff₀ h1]
      constructor <;> intro <;> nlinarith
    · constructor <;> intro <;> nlinarith
  · simp only [hrv, ↓reduceIte]
    split_ifs with hrp
    · rw [div_le_iff₀ h1]
      constructor <;> intro <;> nlinarith
    · constructor <;> intro <;> linarith

/-- The mass of buyers who reject `p` (values in `[0, k)`, `k = κ` clamped to `[0, 1]`). -/
noncomputable def sbCut (δ p r : ℝ) : ℝ := max 0 (min (sbKappa δ p r) 1)

/-- The seller's expected payoff (values uniform on `[0, 1]`) from first price `p` and second
price `q`, when the buyer expects the second price `r`: the types `[k, 1]` buy at `p`, the types
in `[max q 0, k)` buy at `q` in period 2. -/
noncomputable def sbUPay (δ p r q : ℝ) : ℝ :=
  p * (1 - sbCut δ p r) + δ * q * max 0 (sbCut δ p r - max q 0)

/-- The seller's period-2 revenue at price `q` when her belief is uniform on `[0, k)` (the Bayes
posterior after the types below `k` reject): `q · Prob(v ≥ q)`. -/
noncomputable def sbURev (k q : ℝ) : ℝ := q * (max 0 (k - max q 0) / k)

/-- **Exercise 9.C.3(b)** (MWG, p. 304). A pure-strategy weak PBE of the uniform case, in reduced
form: the first price `p1` and the second price `r p` after each rejected price `p`; the buyer
uses the cutoff rule of `exercise_9_C_3b_cutoff`. Each `r p` is in `[0, 1]` (any such price is
optimal for some belief, `sb_point_mass_opt`); after `p1`, if some types reject, `r p1` is
optimal for the Bayes posterior (uniform on the rejecting types); `p1` is optimal against every
deviation `(p, q)`. -/
def IsSBUWeakPBE (δ p1 : ℝ) (r : ℝ → ℝ) : Prop :=
  (∀ p, 0 ≤ r p ∧ r p ≤ 1) ∧
  (0 < sbCut δ p1 (r p1) → ∀ q, sbURev (sbCut δ p1 (r p1)) q ≤
    sbURev (sbCut δ p1 (r p1)) (r p1)) ∧
  ∀ p q, sbUPay δ p (r p) q ≤ sbUPay δ p1 (r p1) (r p1)

/-- **Exercise 9.C.6 for 9.C.3(b)** (MWG, p. 304). Structural consistency: after every price that
a positive mass of types rejects, the second price is optimal for the Bayes posterior. -/
def IsSBUConsistent (δ : ℝ) (r : ℝ → ℝ) : Prop :=
  ∀ p, 0 < sbCut δ p (r p) → ∀ q, sbURev (sbCut δ p (r p)) q ≤ sbURev (sbCut δ p (r p)) (r p)

/-- Any price `r ∈ [0, 1]` is an optimal period-2 price for the belief that puts probability
one on the value `r`. -/
theorem sb_point_mass_opt {r : ℝ} (hr : 0 ≤ r) (q : ℝ) :
    q * (if q ≤ r then 1 else 0) ≤ r * (if r ≤ r then 1 else 0) := by
  split_ifs <;> linarith

/-- `q (k − q)⁺ ≤ k²/4`. -/
theorem sb_rev_bound {k : ℝ} (hk : 0 ≤ k) (q : ℝ) : q * max 0 (k - max q 0) ≤ k ^ 2 / 4 := by
  rcases le_total q 0 with hq | hq
  · rw [max_eq_right hq, sub_zero, max_eq_right hk]
    nlinarith
  · rw [max_eq_left hq]
    rcases le_total (k - q) 0 with h | h
    · rw [max_eq_left h]; nlinarith
    · rw [max_eq_right h]; nlinarith [sq_nonneg (q - k / 2)]

/-- **Exercise 9.C.3(b), the second price** (MWG, p. 304). With the posterior uniform on
`[0, k)`, `k > 0`, the unique optimal second price is `k/2`. -/
theorem sbURev_opt_iff {k : ℝ} (hk : 0 < k) (r : ℝ) :
    (∀ q, sbURev k q ≤ sbURev k r) ↔ r = k / 2 := by
  have hval : sbURev k (k / 2) = k / 4 := by
    unfold sbURev
    rw [max_eq_left (by linarith : (0 : ℝ) ≤ k / 2), max_eq_right (by linarith)]
    field_simp
    ring
  have hle : ∀ q, sbURev k q ≤ k / 4 := fun q => by
    unfold sbURev
    rw [← mul_div_assoc, div_le_iff₀ hk]
    nlinarith [sb_rev_bound hk.le q]
  constructor
  · intro h
    have h1 := h (k / 2)
    rw [hval] at h1
    have h2 : sbURev k r * k = r * max 0 (k - max r 0) := by
      unfold sbURev; field_simp
    have h3 : k ^ 2 / 4 ≤ r * max 0 (k - max r 0) := by nlinarith
    rcases le_total r 0 with hq | hq
    · rw [max_eq_right hq, sub_zero, max_eq_right hk.le] at h3
      nlinarith
    · rw [max_eq_left hq] at h3
      rcases le_total (k - r) 0 with h4 | h4
      · rw [max_eq_left h4] at h3; nlinarith
      · rw [max_eq_right h4] at h3; nlinarith [sq_nonneg (r - k / 2)]
  · rintro rfl q
    rw [hval]
    exact hle q

/-- The second price after `p > 0` in the consistent profile: half the cutoff
`min (2p/(2 − δ), 1)`. -/
noncomputable def sbRStar (δ p : ℝ) : ℝ := if 0 < p then min (2 * p / (2 - δ)) 1 / 2 else 0

/-- The equilibrium first price `p* = (2 − δ)² / (2 (4 − 3δ))`. -/
noncomputable def sbPStar (δ : ℝ) : ℝ := (2 - δ) ^ 2 / (2 * (4 - 3 * δ))

/-- **Exercise 9.C.3(b), the linear cutoff** (MWG, p. 304). If the second price after `p > 0` is
optimal for the Bayes posterior, then the cutoff is `κ = 2p/(2 − δ)` (capped at `1`) and the
second price is `κ/2`. -/
theorem sb_consistent_r (hd0 : 0 < δ) (hd1 : δ < 1) {r : ℝ → ℝ} (hc : IsSBUConsistent δ r)
    {p : ℝ} (hp : 0 < p) :
    r p = sbRStar δ p ∧ sbCut δ p (r p) = min (2 * p / (2 - δ)) 1 := by
  have h1 : 0 < 1 - δ := by linarith
  have h2 : 0 < 2 - δ := by linarith
  set κ := sbKappa δ p (r p) with hκ
  have hκpos : 0 < κ := by
    rw [hκ, sbKappa]
    split_ifs with h
    · rw [lt_div_iff₀ h1]; nlinarith [mul_le_mul_of_nonneg_left h hd0.le]
    · exact hp
  have hk : 0 < sbCut δ p (r p) := by
    unfold sbCut
    rw [← hκ]
    exact lt_max_of_lt_right (lt_min hκpos one_pos)
  have hr2 := (sbURev_opt_iff hk (r p)).1 (hc p hk)
  have hcut : sbCut δ p (r p) = min κ 1 := by
    unfold sbCut; rw [← hκ]; exact max_eq_right (le_min hκpos.le zero_le_one)
  rw [hcut] at hr2 ⊢
  have hRS : sbRStar δ p = min (2 * p / (2 - δ)) 1 / 2 := by simp [sbRStar, hp]
  rw [hRS]
  by_cases hrp : r p ≤ p
  · have hκeq : κ * (1 - δ) = p - δ * r p := by
      rw [hκ, sbKappa]
      simp only [hrp, ↓reduceIte]
      field_simp
    rcases le_total κ 1 with hk1 | hk1
    · rw [min_eq_left hk1] at hr2
      have : κ = 2 * p / (2 - δ) := by
        rw [eq_div_iff h2.ne']
        rw [hr2] at hκeq
        linarith
      rw [← this, min_eq_left hk1]
      exact ⟨hr2, rfl⟩
    · rw [min_eq_right hk1] at hr2
      have : 1 ≤ 2 * p / (2 - δ) := by
        rw [le_div_iff₀ h2]
        rw [hr2] at hκeq
        nlinarith
      rw [min_eq_right this, min_eq_right hk1]
      exact ⟨hr2, rfl⟩
  · exfalso
    have hκp : κ = p := by
      rw [hκ, sbKappa]
      simp only [hrp, ↓reduceIte]
    rw [hκp] at hr2
    have : min p 1 ≤ p := min_le_left _ _
    have : p < r p := not_le.1 hrp
    linarith

/-- At a first price `p ≤ 0` every type buys at once, and the seller earns `p ≤ 0`. -/
theorem sbUPay_nonpos (hd0 : 0 < δ) (hd1 : δ < 1) {p r : ℝ} (hp : p ≤ 0) (hr : 0 ≤ r)
    (q : ℝ) : sbUPay δ p r q ≤ 0 := by
  have hκ : sbKappa δ p r ≤ 0 := by
    unfold sbKappa
    split_ifs
    · exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) (by linarith)
    · exact hp
  have hcut : sbCut δ p r = 0 := by
    unfold sbCut
    exact max_eq_left (le_trans (min_le_left _ _) hκ)
  unfold sbUPay
  rw [hcut]
  rcases le_total q 0 with hq | hq
  · rw [max_eq_right hq, sub_self, max_self, mul_zero, add_zero]; linarith
  · rw [max_eq_left hq, max_eq_left (by linarith : (0 : ℝ) - q ≤ 0)]; linarith

/-- The seller's payoff after `p > 0` when the cutoff is `k` and the second price is `k/2`: at
most `p (1 − k) + δ k²/4`, attained at `q = k/2`. -/
theorem sbUPay_value {p r k : ℝ} (hd0 : 0 < δ) (hk : 0 ≤ k) (hcut : sbCut δ p r = k)
    (q : ℝ) : sbUPay δ p r q ≤ p * (1 - k) + δ * k ^ 2 / 4 ∧
      sbUPay δ p r (k / 2) = p * (1 - k) + δ * k ^ 2 / 4 := by
  unfold sbUPay
  rw [hcut]
  constructor
  · nlinarith [sb_rev_bound hk q]
  · rw [max_eq_left (by linarith : (0 : ℝ) ≤ k / 2), max_eq_right (by linarith)]
    ring

/-- The seller's first-period problem: `p (1 − k) + δ k²/4` with `k = min (2p/(2 − δ), 1)` is at
most `(2 − δ)² / (4 (4 − 3δ))`, with equality only at `p* = (2 − δ)² / (2 (4 − 3δ))`. -/
theorem sbG_le (hd0 : 0 < δ) (hd1 : δ < 1) {p : ℝ} (hp : 0 < p) :
    p * (1 - min (2 * p / (2 - δ)) 1) + δ * (min (2 * p / (2 - δ)) 1) ^ 2 / 4 ≤
      (2 - δ) ^ 2 / (4 * (4 - 3 * δ)) ∧
    (p * (1 - min (2 * p / (2 - δ)) 1) + δ * (min (2 * p / (2 - δ)) 1) ^ 2 / 4 =
      (2 - δ) ^ 2 / (4 * (4 - 3 * δ)) → p = sbPStar δ) := by
  have h2 : 0 < 2 - δ := by linarith
  have h43 : 0 < 4 - 3 * δ := by linarith
  have h43' : 4 - 3 * δ ≠ 0 := h43.ne'
  have h2' : 2 - δ ≠ 0 := h2.ne'
  set k := 2 * p / (2 - δ) with hk
  have hpk : p = (2 - δ) * k / 2 := by rw [hk]; field_simp
  set c := (2 - δ) / (4 - 3 * δ) with hcdef
  have hc : c * (4 - 3 * δ) = 2 - δ := div_mul_cancel₀ _ h43'
  have hg : (2 - δ) ^ 2 / (4 * (4 - 3 * δ)) = c * (2 - δ) / 4 := by
    rw [hcdef]; field_simp
  have key : (2 - δ) ^ 2 / (4 * (4 - 3 * δ)) - (p * (1 - k) + δ * k ^ 2 / 4) =
      (4 - 3 * δ) / 4 * (k - c) ^ 2 := by
    rw [hg, hpk]
    linear_combination (k / 2 - c / 4) * hc
  rcases le_total k 1 with hk1 | hk1
  · rw [min_eq_left hk1]
    refine ⟨by nlinarith [sq_nonneg (k - c)], fun he => ?_⟩
    have hsq : (k - c) ^ 2 = 0 := by
      have : (4 - 3 * δ) / 4 * (k - c) ^ 2 = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h (by positivity)
      · exact h
    have hkk : k = c := sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 hsq)
    rw [hpk, hkk, hcdef, sbPStar]
    field_simp
  · rw [min_eq_right hk1]
    have hlt : δ * 1 ^ 2 / 4 < (2 - δ) ^ 2 / (4 * (4 - 3 * δ)) := by
      rw [lt_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (1 - δ), mul_pos hd0 h43]
    refine ⟨by nlinarith, fun he => ?_⟩
    exfalso
    have : p * (1 - 1) = 0 := by ring
    linarith

/-- The cutoff and second price of the consistent profile after `p > 0`. -/
theorem sbRStar_cut (hd0 : 0 < δ) (hd1 : δ < 1) {p : ℝ} (hp : 0 < p) :
    sbCut δ p (sbRStar δ p) = min (2 * p / (2 - δ)) 1 ∧
      sbRStar δ p = min (2 * p / (2 - δ)) 1 / 2 := by
  have h1 : 0 < 1 - δ := by linarith
  have h2 : 0 < 2 - δ := by linarith
  have hRS : sbRStar δ p = min (2 * p / (2 - δ)) 1 / 2 := by simp [sbRStar, hp]
  refine ⟨?_, hRS⟩
  set k := min (2 * p / (2 - δ)) 1 with hk
  have hkpos : 0 < k := lt_min (div_pos (by linarith) h2) one_pos
  have hkp : k / 2 ≤ p := by
    have : k ≤ 2 * p / (2 - δ) := min_le_left _ _
    rw [le_div_iff₀ h2] at this
    nlinarith
  unfold sbCut sbKappa
  rw [hRS]
  simp only [hkp, ↓reduceIte]
  rcases le_total (2 * p / (2 - δ)) 1 with hk1 | hk1
  · have hk' : k = 2 * p / (2 - δ) := min_eq_left hk1
    have : (p - δ * (k / 2)) / (1 - δ) = k := by
      rw [hk', div_eq_iff h1.ne']; field_simp; ring
    rw [this, min_eq_left (min_le_right _ _), max_eq_right hkpos.le]
  · have hk' : k = 1 := min_eq_right hk1
    have : 1 ≤ (p - δ * (k / 2)) / (1 - δ) := by
      rw [hk', le_div_iff₀ h1]
      rw [le_div_iff₀ h2] at hk1
      linarith
    rw [min_eq_right this, max_eq_right zero_le_one, hk']

/-- **Exercise 9.C.3(b)** (MWG, p. 304), values uniform on `[0, 1]`. The profile in which, after
every first price `p > 0`, the types with `v ≥ κ = 2p/(2 − δ)` (capped at `1`) buy at once and
the seller then charges `κ/2`, and the first price is `p* = (2 − δ)²/(2 (4 − 3δ))` (cutoff
`(2 − δ)/(4 − 3δ)`, second price `(2 − δ)/(2 (4 − 3δ))`), is a weak PBE with consistent beliefs;
and it is the only weak PBE whose beliefs are consistent after every rejected price
(the sequential-equilibrium reading of Exercise 9.C.6). -/
theorem exercise_9_C_3b (hd0 : 0 < δ) (hd1 : δ < 1) :
    IsSBUWeakPBE δ (sbPStar δ) (sbRStar δ) ∧ IsSBUConsistent δ (sbRStar δ) ∧
    sbCut δ (sbPStar δ) (sbRStar δ (sbPStar δ)) = (2 - δ) / (4 - 3 * δ) ∧
    sbRStar δ (sbPStar δ) = (2 - δ) / (2 * (4 - 3 * δ)) ∧
    ∀ p1 r, IsSBUWeakPBE δ p1 r → IsSBUConsistent δ r →
      p1 = sbPStar δ ∧ ∀ p, 0 < p → r p = sbRStar δ p := by
  have h2 : 0 < 2 - δ := by linarith
  have h43 : 0 < 4 - 3 * δ := by linarith
  have h43' : 4 - 3 * δ ≠ 0 := h43.ne'
  have h2' : 2 - δ ≠ 0 := h2.ne'
  have hps : 0 < sbPStar δ := by unfold sbPStar; positivity
  have hks : 2 * sbPStar δ / (2 - δ) = (2 - δ) / (4 - 3 * δ) := by
    unfold sbPStar; field_simp
  have hks1 : (2 - δ) / (4 - 3 * δ) ≤ 1 := by rw [div_le_one h43]; linarith
  obtain ⟨hc1, hc2⟩ := sbRStar_cut hd0 hd1 hps
  rw [hks, min_eq_left hks1] at hc1 hc2
  -- the value of the consistent profile
  have hval : ∀ p, 0 < p → ∀ q, sbUPay δ p (sbRStar δ p) q ≤
      (2 - δ) ^ 2 / (4 * (4 - 3 * δ)) := fun p hp q => by
    obtain ⟨c1, -⟩ := sbRStar_cut hd0 hd1 hp
    have := (sbUPay_value hd0 (le_min (div_pos (by linarith) h2).le zero_le_one) c1 q).1
    linarith [(sbG_le hd0 hd1 hp).1]
  have hstar : sbUPay δ (sbPStar δ) (sbRStar δ (sbPStar δ)) (sbRStar δ (sbPStar δ)) =
      (2 - δ) ^ 2 / (4 * (4 - 3 * δ)) := by
    have := (sbUPay_value hd0 (by positivity) hc1 0).2
    rw [hc2] at this ⊢
    rw [this]
    set c := (2 - δ) / (4 - 3 * δ) with hcdef
    have hc : c * (4 - 3 * δ) = 2 - δ := div_mul_cancel₀ _ h43'
    have hpc : sbPStar δ = (2 - δ) * c / 2 := by unfold sbPStar; rw [hcdef]; field_simp
    have hg : (2 - δ) ^ 2 / (4 * (4 - 3 * δ)) = c * (2 - δ) / 4 := by rw [hcdef]; field_simp
    rw [hpc, hg]
    linear_combination (-c / 4) * hc
  have hRnn : ∀ p, 0 ≤ sbRStar δ p ∧ sbRStar δ p ≤ 1 := fun p => by
    unfold sbRStar
    split_ifs with hp
    · constructor
      · exact div_nonneg (le_min (div_pos (by linarith) h2).le zero_le_one) zero_le_two
      · linarith [min_le_right (2 * p / (2 - δ)) 1]
    · exact ⟨le_rfl, zero_le_one⟩
  have hcons : IsSBUConsistent δ (sbRStar δ) := by
    intro p hpos q
    by_cases hp : 0 < p
    · obtain ⟨c1, c2⟩ := sbRStar_cut hd0 hd1 hp
      rw [c1] at hpos ⊢
      exact (sbURev_opt_iff hpos _).2 c2 q
    · exfalso
      have hκ : sbKappa δ p (sbRStar δ p) ≤ 0 := by
        have hr0 : sbRStar δ p = 0 := by simp [sbRStar, hp]
        rw [hr0, sbKappa]
        split_ifs
        · rw [mul_zero, sub_zero]
          exact div_nonpos_of_nonpos_of_nonneg (not_lt.1 hp) (by linarith)
        · exact not_lt.1 hp
      have : sbCut δ p (sbRStar δ p) = 0 := max_eq_left (le_trans (min_le_left _ _) hκ)
      linarith
  refine ⟨⟨hRnn, fun h => hcons _ h, fun p q => ?_⟩, hcons, hc1,
    by rw [hc2, div_div, mul_comm (4 - 3 * δ)], fun p1 r hW hC => ?_⟩
  · rw [hstar]
    by_cases hp : 0 < p
    · exact hval p hp q
    · exact le_trans (sbUPay_nonpos hd0 hd1 (not_lt.1 hp) (hRnn p).1 q) (by positivity)
  · obtain ⟨hr01, -, hroot⟩ := hW
    have hrs : ∀ p, 0 < p → r p = sbRStar δ p := fun p hp => (sb_consistent_r hd0 hd1 hC hp).1
    have hdev := hroot (sbPStar δ) (sbRStar δ (sbPStar δ))
    rw [hrs _ hps, hstar] at hdev
    have hp1 : 0 < p1 := by
      by_contra hn
      have := sbUPay_nonpos hd0 hd1 (not_lt.1 hn) (hr01 p1).1 (r p1)
      have : 0 < (2 - δ) ^ 2 / (4 * (4 - 3 * δ)) := by positivity
      linarith
    refine ⟨?_, hrs⟩
    obtain ⟨c1, c2⟩ := sb_consistent_r hd0 hd1 hC hp1
    obtain ⟨-, c3⟩ := sbRStar_cut hd0 hd1 hp1
    have hv := (sbUPay_value hd0 (le_min (div_pos (by linarith) h2).le zero_le_one) c2
      (r p1)).2
    rw [c1, c3] at hv
    rw [c1, c3, hv] at hdev
    exact (sbG_le hd0 hd1 hp1).2 (le_antisymm (sbG_le hd0 hd1 hp1).1 hdev)

/-- **Exercise 9.C.3(b): weak PBE are not unique** (MWG, p. 304). With `δ = 1/2` the
consistent price is `p* = 9/20`, but `p1 = 3/10` is also a weak PBE first price: after
`3/10` the cutoff is `2/5` and the seller charges `1/5`, earning `1/5`; after any other price
the seller (at an information set reached with probability zero, where any belief is allowed)
charges `0`, so the buyers' cutoff is `2p` and no deviation earns more than `1/6`. -/
theorem exercise_9_C_3b_not_unique :
    IsSBUWeakPBE (1 / 2) (3 / 10) (fun p => if p = 3 / 10 then 1 / 5 else 0) ∧
      (3 / 10 : ℝ) ≠ sbPStar (1 / 2) := by
  set r : ℝ → ℝ := fun p => if p = 3 / 10 then 1 / 5 else 0 with hr
  have hcut1 : sbCut (1 / 2) (3 / 10) (r (3 / 10)) = 2 / 5 := by
    simp only [hr, ↓reduceIte, sbCut, sbKappa]
    norm_num
  have hpay1 : sbUPay (1 / 2) (3 / 10) (r (3 / 10)) (r (3 / 10)) = 1 / 5 := by
    unfold sbUPay
    rw [hcut1]
    simp only [hr, ↓reduceIte]
    norm_num
  refine ⟨⟨fun p => ?_, fun _ q => ?_, fun p q => ?_⟩, by unfold sbPStar; norm_num⟩
  · simp only [hr]; split_ifs <;> norm_num
  · rw [hcut1]
    have : r (3 / 10) = 2 / 5 / 2 := by simp only [hr, ↓reduceIte]; norm_num
    rw [this]
    exact (sbURev_opt_iff (by norm_num) _).2 rfl q
  · rw [hpay1]
    by_cases hp : p = 3 / 10
    · subst hp
      unfold sbUPay
      rw [hcut1]
      nlinarith [sb_rev_bound (k := 2 / 5) (by norm_num) q]
    · have hr0 : r p = 0 := by simp [hr, hp]
      rw [hr0]
      by_cases hp0 : 0 < p
      · have hκ : sbKappa (1 / 2) p 0 = 2 * p := by
          simp only [sbKappa, hp0.le, ↓reduceIte]; ring
        unfold sbUPay sbCut
        rw [hκ]
        rcases le_total (2 * p) 1 with h1 | h1
        · rw [min_eq_left h1, max_eq_right (by linarith)]
          nlinarith [sb_rev_bound (k := 2 * p) (by linarith) q, sq_nonneg (p - 1 / 3)]
        · rw [min_eq_right h1, max_eq_right zero_le_one]
          nlinarith [sb_rev_bound (k := 1) zero_le_one q]
      · exact le_trans (sbUPay_nonpos (by norm_num) (by norm_num) (not_lt.1 hp0) le_rfl q)
          (by norm_num)

end MWG.DynamicGames

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Pretrial settlement with an informed defendant

MWG, Exercise 9.C.4 (p. 304). Ms. P sues Ms. D for damages `π > 0` (`dmg` here: `π` may not
be used as a name); D knows the probability `λ ∈ [0, 1]` that P wins, P only knows its prior
distribution `μ` (a probability measure on `ℝ` concentrated on `[0, 1]`); going to trial costs
`c_p, c_d > 0`. P makes a take-it-or-leave-it offer `s`; D accepts (pays `s`) or rejects (trial:
P gets `λπ − c_p`, D pays `λπ + c_d`).

(a) The weak PBE (`IsSetWeakPBE`). D's information sets are singletons and P moves once, so a
weak PBE is: D best responds at every `(λ, s)` (`SetBR`: accept only if `s ≤ λπ + c_d`, reject
only if `s ≥ λπ + c_d`), and P's offer maximises her expected payoff against D's strategy.
`exercise_9_C_4a`: when the prior has no atoms (in particular when it has a density, as in the
book), `(s, acc)` is a weak PBE iff D best responds and `s` maximises
`V(s) = E[s·1{λπ + c_d ≥ s} + (λπ − c_p)·1{λπ + c_d < s}]`; and (`setV_eq`) with
`t = (s − c_d)/π` (the type indifferent at `s`),
`V(s) = π E[min(λ, t)] + c_d − (c_p + c_d) Prob(λ < t)`; the equilibrium offer satisfies
`s ≥ c_d` (`setOffer_ge`), and trial happens with probability `Prob(λ < t)` (`setTrial_eq`).

(b) Comparative statics, without any assumption on the prior beyond no atoms
(`exercise_9_C_4b`): the equilibrium probability of trial is weakly decreasing in
`(c_p + c_d)/π`, hence weakly decreasing in `c_p` and in `c_d` and weakly increasing in `π`;
P's equilibrium payoff is weakly decreasing in `c_p` and weakly increasing in `c_d` and in `π`
(`exercise_9_C_4b_payoff`). Example: with the uniform prior and `c_p + c_d ≥ π`, P offers `c_d`
and every type settles (`exercise_9_C_4_uniform`).

(c) (the book says "Ms. D"; the agent whose offer was rejected is Ms. P, see
docs/corrections.md): after a rejection P chooses between trial and dropping the case. See
`exercise_9_C_4c_no_trial`, `exercise_9_C_4c_drop`, `exercise_9_C_4c_settle`.
-/

namespace MWG.DynamicGames

open MeasureTheory ProbabilityTheory

/-- **Exercise 9.C.4(a)** (MWG, p. 304). D's best responses: type `x` accepts the offer `s`
only if paying `s` is no worse than the expected trial payment `x π + c_d`, and rejects only if
it is no better. -/
def SetBR (dmg cd : ℝ) (acc : ℝ → ℝ → Bool) : Prop :=
  ∀ x s, (acc x s = true → s ≤ x * dmg + cd) ∧ (acc x s = false → x * dmg + cd ≤ s)

/-- P's expected payoff from the offer `s` against D's strategy `acc`. -/
noncomputable def setPay (μ : Measure ℝ) (dmg cp : ℝ) (acc : ℝ → ℝ → Bool) (s : ℝ) : ℝ :=
  ∫ x, (if acc x s then s else x * dmg - cp) ∂μ

/-- **Exercise 9.C.4(a)** (MWG, p. 304). A pure-strategy weak PBE: D best responds at each of
her (singleton) information sets, and P's offer is optimal given D's strategy and the prior. -/
def IsSetWeakPBE (μ : Measure ℝ) (dmg cp cd s : ℝ) (acc : ℝ → ℝ → Bool) : Prop :=
  SetBR dmg cd acc ∧ ∀ s', setPay μ dmg cp acc s' ≤ setPay μ dmg cp acc s

/-- P's expected payoff from the offer `s` when the types that weakly prefer settling accept. -/
noncomputable def setV (μ : Measure ℝ) (dmg cp cd s : ℝ) : ℝ :=
  ∫ x, (if s ≤ x * dmg + cd then s else x * dmg - cp) ∂μ

/-- `E[min(λ, t)]` under the prior. -/
noncomputable def setM (μ : Measure ℝ) (t : ℝ) : ℝ := ∫ x, min x t ∂μ

variable {μ : Measure ℝ}

/-- Against a best-responding D, P's payoff is `V(s)` when the prior has no atoms (only the
type indifferent at `s` may act otherwise, and it has probability zero). -/
theorem setPay_eq_setV [NullSingletonClass μ] {dmg cp cd : ℝ} (hdmg : 0 < dmg)
    {acc : ℝ → ℝ → Bool} (h : SetBR dmg cd acc) (s : ℝ) :
    setPay μ dmg cp acc s = setV μ dmg cp cd s := by
  refine integral_congr_ae ?_
  have hne : ∀ᵐ x ∂μ, x ≠ (s - cd) / dmg := by
    rw [ae_iff]
    simp
  filter_upwards [hne] with x hx
  have hx' : x * dmg + cd ≠ s := fun he => hx (by field_simp; linarith)
  cases hc : acc x s
  · have h1 := (h x s).2 hc
    have h2 : ¬ s ≤ x * dmg + cd := fun h3 => hx' (le_antisymm h1 h3)
    simp [h2]
  · simp [(h x s).1 hc]

/-- **Exercise 9.C.4(a)** (MWG, p. 304). With an atomless prior, `(s, acc)` is a weak PBE iff D
best responds and `s` maximises `V`. -/
theorem exercise_9_C_4a [NullSingletonClass μ] {dmg cp cd s : ℝ} (hdmg : 0 < dmg)
    {acc : ℝ → ℝ → Bool} :
    IsSetWeakPBE μ dmg cp cd s acc ↔ SetBR dmg cd acc ∧ ∀ s', setV μ dmg cp cd s' ≤
      setV μ dmg cp cd s := by
  constructor
  · rintro ⟨h, hopt⟩
    refine ⟨h, fun s' => ?_⟩
    rw [← setPay_eq_setV hdmg h, ← setPay_eq_setV hdmg h]
    exact hopt s'
  · rintro ⟨h, hopt⟩
    refine ⟨h, fun s' => ?_⟩
    rw [setPay_eq_setV hdmg h, setPay_eq_setV hdmg h]
    exact hopt s'

/-- `min λ t` is integrable for a probability measure concentrated on `[0, 1]`. -/
theorem integrable_min [IsProbabilityMeasure μ] (hsupp : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) 1)
    (t : ℝ) : Integrable (fun x => min x t) μ := by
  refine Integrable.of_bound (continuous_id.min continuous_const).aestronglyMeasurable
    (max 1 |t|) ?_
  filter_upwards [hsupp] with x hx
  rw [Real.norm_eq_abs]
  rcases le_total x t with h | h
  · rw [min_eq_left h, abs_of_nonneg hx.1]
    exact le_trans hx.2 (le_max_left _ _)
  · rw [min_eq_right h]
    exact le_max_right _ _

/-- **Exercise 9.C.4(a)**, the reduced form (MWG, p. 304). With `t = (s − c_d)/π`,
`V(s) = π E[min(λ, t)] + c_d − (c_p + c_d) Prob(λ < t)`. -/
theorem setV_eq [IsProbabilityMeasure μ] (hsupp : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) 1)
    {dmg cp cd : ℝ} (hdmg : 0 < dmg) (s : ℝ) :
    setV μ dmg cp cd s = dmg * setM μ ((s - cd) / dmg) + cd -
      (cp + cd) * μ.real (Set.Iio ((s - cd) / dmg)) := by
  set t := (s - cd) / dmg with ht
  have hs : s = cd + dmg * t := by rw [ht]; field_simp; ring
  have hpt : ∀ x, (if s ≤ x * dmg + cd then s else x * dmg - cp) =
      dmg * min x t + cd - (cp + cd) * (Set.Iio t).indicator 1 x := by
    intro x
    by_cases hx : t ≤ x
    · have : s ≤ x * dmg + cd := by rw [hs]; nlinarith
      rw [min_eq_right hx, Set.indicator_of_notMem (show x ∉ Set.Iio t from not_lt.2 hx)]
      simp only [this, ↓reduceIte]
      linarith
    · have hx' : x < t := not_le.1 hx
      have : ¬ s ≤ x * dmg + cd := by rw [hs]; nlinarith
      rw [min_eq_left hx'.le, Set.indicator_of_mem (show x ∈ Set.Iio t from hx'), Pi.one_apply]
      simp only [this, ↓reduceIte]
      ring
  unfold setV
  simp_rw [hpt]
  have hI1 : Integrable (fun x => dmg * min x t) μ := (integrable_min hsupp t).const_mul dmg
  have hI2 : Integrable (fun x => (cp + cd) * (Set.Iio t).indicator 1 x) μ :=
    ((integrable_const (1 : ℝ)).indicator measurableSet_Iio).const_mul _
  have hA : Integrable (fun x => dmg * min x t + cd) μ := hI1.add (integrable_const cd)
  rw [integral_sub hA hI2, integral_add hI1 (integrable_const cd),
    integral_const_mul, integral_const_mul, integral_indicator_one measurableSet_Iio,
    integral_const, probReal_univ, one_smul]
  rfl

/-- Against a best-responding D, the probability of trial is `Prob(λ < t)` (atomless prior). -/
theorem setTrial_eq [IsProbabilityMeasure μ] [NullSingletonClass μ] {dmg cd : ℝ} (hdmg : 0 < dmg)
    {acc : ℝ → ℝ → Bool} (h : SetBR dmg cd acc) (s : ℝ) :
    μ.real {x | acc x s = false} = μ.real (Set.Iio ((s - cd) / dmg)) := by
  set t := (s - cd) / dmg with ht
  have hs : s = cd + dmg * t := by rw [ht]; field_simp; ring
  have h1 : Set.Iio t ⊆ {x | acc x s = false} := by
    intro x hx
    change acc x s = false
    cases hc : acc x s
    · rfl
    · have := (h x s).1 hc
      rw [hs] at this
      have : t ≤ x := by nlinarith [Set.mem_Iio.1 hx]
      exact absurd hx (not_lt.2 this)
  have h2 : {x | acc x s = false} ⊆ Set.Iic t := by
    intro x hx
    have := (h x s).2 hx
    rw [hs] at this
    change x ≤ t
    nlinarith
  refine le_antisymm ?_ (measureReal_mono h1)
  calc μ.real {x | acc x s = false} ≤ μ.real (Set.Iic t) := measureReal_mono h2
    _ = μ.real (Set.Iio t) := by rw [measureReal_def, measureReal_def, measure_congr Iio_ae_eq_Iic]

/-- `E[min(λ, t)] = t` for `t ≤ 0`, and `E[min(λ, t)] ≥ 0` for `t ≥ 0`. -/
theorem setM_facts [IsProbabilityMeasure μ] (hsupp : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) 1) (t : ℝ) :
    (t ≤ 0 → setM μ t = t) ∧ (0 ≤ t → 0 ≤ setM μ t) := by
  constructor
  · intro h
    unfold setM
    rw [integral_congr_ae (g := fun _ => t) ?_, integral_const, probReal_univ, one_smul]
    filter_upwards [hsupp] with x hx
    exact min_eq_right (le_trans h hx.1)
  · intro h
    exact integral_nonneg_of_ae (by filter_upwards [hsupp] with x hx; exact le_min hx.1 h)

/-- `Prob(λ < t) = 0` for `t ≤ 0`. -/
theorem setG_zero [IsProbabilityMeasure μ] (hsupp : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) 1) {t : ℝ}
    (h : t ≤ 0) : μ.real (Set.Iio t) = 0 := by
  have h0 : μ {x | ¬ x ∈ Set.Icc (0 : ℝ) 1} = 0 := ae_iff.1 hsupp
  have hsub : Set.Iio t ⊆ {x | x ∉ Set.Icc (0 : ℝ) 1} := fun x hx hm =>
    absurd (lt_of_lt_of_le (Set.mem_Iio.1 hx) h) (not_lt.2 hm.1)
  rw [measureReal_def, measure_mono_null hsub h0, ENNReal.toReal_zero]

/-- `V` below `c_d`: an offer `s ≤ c_d` is accepted by every type and earns `s`. -/
theorem setV_of_le [IsProbabilityMeasure μ] (hsupp : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) 1)
    {dmg cp cd : ℝ} (hdmg : 0 < dmg) {s : ℝ} (hs : s ≤ cd) : setV μ dmg cp cd s = s := by
  have ht : (s - cd) / dmg ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hdmg.le
  rw [setV_eq hsupp hdmg, (setM_facts hsupp _).1 ht, setG_zero hsupp ht]
  field_simp
  ring

/-- **Exercise 9.C.4(a)** (MWG, p. 304). In every weak PBE the offer is at least `c_d` (lower
offers are accepted by all types and are beaten by `c_d`), so the indifferent type
`t = (s − c_d)/π` is nonnegative. -/
theorem setOffer_ge [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (hsupp : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) 1) {dmg cp cd s : ℝ} (hdmg : 0 < dmg)
    {acc : ℝ → ℝ → Bool} (h : IsSetWeakPBE μ dmg cp cd s acc) : cd ≤ s := by
  by_contra hn
  have hopt := ((exercise_9_C_4a hdmg).1 h).2 cd
  rw [setV_of_le hsupp hdmg le_rfl, setV_of_le hsupp hdmg (not_le.1 hn).le] at hopt
  exact hn hopt

/-- P's payoff from the offer that makes type `t` indifferent, in reduced form. -/
theorem setV_thr [IsProbabilityMeasure μ] (hsupp : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) 1)
    {dmg cp cd : ℝ} (hdmg : 0 < dmg) (t : ℝ) :
    setV μ dmg cp cd (cd + dmg * t) = dmg * setM μ t + cd - (cp + cd) * μ.real (Set.Iio t) := by
  rw [setV_eq hsupp hdmg]
  have : (cd + dmg * t - cd) / dmg = t := by field_simp; ring
  rw [this]

/-- **Exercise 9.C.4(b)** (MWG, p. 304), the key comparison. Let `(s₁, acc₁)` and `(s₂, acc₂)`
be weak PBE for parameters `(c_p, c_d, π)₁` and `(c_p, c_d, π)₂` (same prior, no atoms). If
`(c_p + c_d)/π` is smaller in the first, the probability of trial is weakly larger in the
first. -/
theorem setTrial_anti [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (hsupp : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) 1) {dmg₁ cp₁ cd₁ s₁ dmg₂ cp₂ cd₂ s₂ : ℝ}
    (hd₁ : 0 < dmg₁) (hd₂ : 0 < dmg₂) {acc₁ acc₂ : ℝ → ℝ → Bool}
    (h₁ : IsSetWeakPBE μ dmg₁ cp₁ cd₁ s₁ acc₁) (h₂ : IsSetWeakPBE μ dmg₂ cp₂ cd₂ s₂ acc₂)
    (hk : (cp₁ + cd₁) / dmg₁ < (cp₂ + cd₂) / dmg₂) :
    μ.real {x | acc₂ x s₂ = false} ≤ μ.real {x | acc₁ x s₁ = false} := by
  obtain ⟨b₁, o₁⟩ := (exercise_9_C_4a hd₁).1 h₁
  obtain ⟨b₂, o₂⟩ := (exercise_9_C_4a hd₂).1 h₂
  rw [setTrial_eq hd₁ b₁, setTrial_eq hd₂ b₂]
  set t₁ := (s₁ - cd₁) / dmg₁ with ht₁
  set t₂ := (s₂ - cd₂) / dmg₂ with ht₂
  have e₁ : s₁ = cd₁ + dmg₁ * t₁ := by rw [ht₁]; field_simp; ring
  have e₂ : s₂ = cd₂ + dmg₂ * t₂ := by rw [ht₂]; field_simp; ring
  have i₁ := o₁ (cd₁ + dmg₁ * t₂)
  have i₂ := o₂ (cd₂ + dmg₂ * t₁)
  rw [e₁, setV_thr hsupp hd₁, setV_thr hsupp hd₁] at i₁
  rw [e₂, setV_thr hsupp hd₂, setV_thr hsupp hd₂] at i₂
  set k₁ := (cp₁ + cd₁) / dmg₁
  set k₂ := (cp₂ + cd₂) / dmg₂
  have a₁ : cp₁ + cd₁ = k₁ * dmg₁ := by simp only [k₁]; field_simp
  have a₂ : cp₂ + cd₂ = k₂ * dmg₂ := by simp only [k₂]; field_simp
  rw [a₁] at i₁
  rw [a₂] at i₂
  set M₁ := setM μ t₁
  set M₂ := setM μ t₂
  set G₁ := μ.real (Set.Iio t₁)
  set G₂ := μ.real (Set.Iio t₂)
  have f₁ : 0 ≤ dmg₁ * (M₁ - M₂ - k₁ * (G₁ - G₂)) := by linarith
  have f₂ : 0 ≤ dmg₂ * (M₂ - M₁ - k₂ * (G₂ - G₁)) := by linarith
  have g₁ := (mul_nonneg_iff_of_pos_left hd₁).1 f₁
  have g₂ := (mul_nonneg_iff_of_pos_left hd₂).1 f₂
  by_contra hn
  nlinarith [mul_pos (sub_pos.2 hk) (sub_pos.2 (not_le.1 hn))]

/-- **Exercise 9.C.4(b)** (MWG, p. 304). Effects on the equilibrium probability of trial (any
atomless prior): it weakly falls when `c_p` rises, weakly falls when `c_d` rises, and weakly
rises when `π` rises. -/
theorem exercise_9_C_4b [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (hsupp : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) 1) {dmg cp cd : ℝ} (hdmg : 0 < dmg) (hcp : 0 < cp)
    (hcd : 0 < cd) {s₁ s₂ : ℝ} {acc₁ acc₂ : ℝ → ℝ → Bool} :
    (∀ cp', cp < cp' → IsSetWeakPBE μ dmg cp cd s₁ acc₁ → IsSetWeakPBE μ dmg cp' cd s₂ acc₂ →
      μ.real {x | acc₂ x s₂ = false} ≤ μ.real {x | acc₁ x s₁ = false}) ∧
    (∀ cd', cd < cd' → IsSetWeakPBE μ dmg cp cd s₁ acc₁ → IsSetWeakPBE μ dmg cp cd' s₂ acc₂ →
      μ.real {x | acc₂ x s₂ = false} ≤ μ.real {x | acc₁ x s₁ = false}) ∧
    (∀ dmg', dmg < dmg' → IsSetWeakPBE μ dmg cp cd s₁ acc₁ →
      IsSetWeakPBE μ dmg' cp cd s₂ acc₂ →
      μ.real {x | acc₁ x s₁ = false} ≤ μ.real {x | acc₂ x s₂ = false}) := by
  refine ⟨fun cp' hlt h₁ h₂ => setTrial_anti hsupp hdmg hdmg h₁ h₂ ?_,
    fun cd' hlt h₁ h₂ => setTrial_anti hsupp hdmg hdmg h₁ h₂ ?_,
    fun dmg' hlt h₁ h₂ => setTrial_anti hsupp (by linarith) hdmg h₂ h₁ ?_⟩
  · exact div_lt_div_of_pos_right (by linarith) hdmg
  · exact div_lt_div_of_pos_right (by linarith) hdmg
  · exact div_lt_div_of_pos_left (by linarith) hdmg hlt

/-- **Exercise 9.C.4(b)** (MWG, p. 304). Effects on P's equilibrium payoff (any atomless prior):
it weakly falls when `c_p` rises and weakly rises when `c_d` or `π` rises. -/
theorem exercise_9_C_4b_payoff [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (hsupp : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) 1) {dmg cp cd : ℝ} (hdmg : 0 < dmg)
    {s₁ s₂ : ℝ} {acc₁ acc₂ : ℝ → ℝ → Bool} :
    (∀ cp', cp ≤ cp' → IsSetWeakPBE μ dmg cp cd s₁ acc₁ → IsSetWeakPBE μ dmg cp' cd s₂ acc₂ →
      setPay μ dmg cp' acc₂ s₂ ≤ setPay μ dmg cp acc₁ s₁) ∧
    (∀ cd', cd ≤ cd' → IsSetWeakPBE μ dmg cp cd s₁ acc₁ → IsSetWeakPBE μ dmg cp cd' s₂ acc₂ →
      setPay μ dmg cp acc₁ s₁ ≤ setPay μ dmg cp acc₂ s₂) ∧
    (∀ dmg', dmg ≤ dmg' → IsSetWeakPBE μ dmg cp cd s₁ acc₁ →
      IsSetWeakPBE μ dmg' cp cd s₂ acc₂ →
      setPay μ dmg cp acc₁ s₁ ≤ setPay μ dmg' cp acc₂ s₂) := by
  have hG : ∀ t, 0 ≤ μ.real (Set.Iio t) ∧ μ.real (Set.Iio t) ≤ 1 :=
    fun t => ⟨measureReal_nonneg, measureReal_le_one⟩
  refine ⟨fun cp' hle h₁ h₂ => ?_, fun cd' hle h₁ h₂ => ?_, fun dmg' hle h₁ h₂ => ?_⟩
  · obtain ⟨b₁, o₁⟩ := (exercise_9_C_4a hdmg).1 h₁
    obtain ⟨b₂, -⟩ := (exercise_9_C_4a hdmg).1 h₂
    rw [setPay_eq_setV hdmg b₁, setPay_eq_setV hdmg b₂]
    refine le_trans ?_ (o₁ s₂)
    rw [setV_eq hsupp hdmg, setV_eq hsupp hdmg]
    nlinarith [(hG ((s₂ - cd) / dmg)).1]
  · obtain ⟨b₁, -⟩ := (exercise_9_C_4a hdmg).1 h₁
    obtain ⟨b₂, o₂⟩ := (exercise_9_C_4a hdmg).1 h₂
    rw [setPay_eq_setV hdmg b₁, setPay_eq_setV hdmg b₂]
    refine le_trans ?_ (o₂ (cd' + dmg * ((s₁ - cd) / dmg)))
    rw [setV_eq hsupp hdmg, setV_thr hsupp hdmg]
    nlinarith [(hG ((s₁ - cd) / dmg)).2]
  · have hd' : 0 < dmg' := by linarith
    obtain ⟨b₁, -⟩ := (exercise_9_C_4a hdmg).1 h₁
    obtain ⟨b₂, o₂⟩ := (exercise_9_C_4a hd').1 h₂
    rw [setPay_eq_setV hdmg b₁, setPay_eq_setV hd' b₂]
    refine le_trans ?_ (o₂ (cd + dmg' * ((s₁ - cd) / dmg)))
    rw [setV_eq hsupp hdmg, setV_thr hsupp hd']
    have ht : 0 ≤ (s₁ - cd) / dmg := div_nonneg (by linarith [setOffer_ge hsupp hdmg h₁]) hdmg.le
    nlinarith [(setM_facts hsupp _).2 ht]

/-- The uniform prior on `[0, 1]`. -/
noncomputable def unifPrior : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)

theorem unifPrior_isProbabilityMeasure : IsProbabilityMeasure unifPrior :=
  ⟨by simp [unifPrior, Real.volume_Icc]⟩

theorem unifPrior_supp : ∀ᵐ x ∂unifPrior, x ∈ Set.Icc (0 : ℝ) 1 :=
  ae_restrict_mem measurableSet_Icc

/-- D's best response (accepting when indifferent). -/
noncomputable def setAccBR (dmg cd : ℝ) (x s : ℝ) : Bool := decide (s ≤ x * dmg + cd)

theorem setAccBR_BR (dmg cd : ℝ) : SetBR dmg cd (setAccBR dmg cd) := by
  intro x s
  refine ⟨fun h => by simpa [setAccBR] using h, fun h => ?_⟩
  simp only [setAccBR, decide_eq_false_iff_not, not_le] at h
  exact h.le

/-- **Exercise 9.C.4(a), an example** (MWG, p. 304). With the uniform prior and
`c_p + c_d ≥ π`, offering `c_d` (accepted by every type) is a weak PBE: no trials occur. -/
theorem exercise_9_C_4_uniform {dmg cp cd : ℝ} (hdmg : 0 < dmg) (hk : dmg ≤ cp + cd) :
    IsSetWeakPBE unifPrior dmg cp cd cd (setAccBR dmg cd) ∧
      unifPrior.real {x | setAccBR dmg cd x cd = false} = 0 := by
  have hP := unifPrior_isProbabilityMeasure
  have hs := unifPrior_supp
  have hN : NullSingletonClass unifPrior := Measure.restrict.instNullSingletonClass _
  refine ⟨(exercise_9_C_4a hdmg).2 ⟨setAccBR_BR dmg cd, fun s' => ?_⟩, ?_⟩
  · rw [setV_of_le hs hdmg le_rfl, setV_eq hs hdmg]
    set t := (s' - cd) / dmg
    rcases le_total t 0 with ht | ht
    · rw [(setM_facts hs t).1 ht, setG_zero hs ht]
      nlinarith
    · -- `E[min(λ, t)] ≤ min(t, 1) ≤ Prob(λ < t)`
      set m := min t 1 with hm
      have hM : setM unifPrior t ≤ m := by
        have := integral_mono_ae (integrable_min hs t) (integrable_const m) (by
          filter_upwards [hs] with x hx
          exact le_min (min_le_right _ _) (le_trans (min_le_left _ _) hx.2))
        rwa [integral_const, probReal_univ, one_smul] at this
      have hG : m ≤ unifPrior.real (Set.Iio t) := by
        have h1 : unifPrior (Set.Ico 0 m) = ENNReal.ofReal m := by
          rw [unifPrior, Measure.restrict_apply measurableSet_Ico,
            Set.inter_eq_left.2 (Set.Ico_subset_Icc_self.trans
              (Set.Icc_subset_Icc le_rfl (min_le_right _ _))), Real.volume_Ico, sub_zero]
        have h2 : Set.Ico 0 m ⊆ Set.Iio t := fun x hx => lt_of_lt_of_le hx.2 (min_le_left _ _)
        calc m = unifPrior.real (Set.Ico 0 m) := by
              rw [measureReal_def, h1, ENNReal.toReal_ofReal (le_min ht zero_le_one)]
          _ ≤ unifPrior.real (Set.Iio t) := measureReal_mono h2
      have hG0 : 0 ≤ unifPrior.real (Set.Iio t) := measureReal_nonneg
      nlinarith
  · rw [measureReal_def, ENNReal.toReal_eq_zero_iff]
    left
    have hsub : {x | setAccBR dmg cd x cd = false} ⊆ {x | x ∉ Set.Icc (0 : ℝ) 1} := by
      intro x hx hm
      have hx' : x * dmg + cd < cd := by
        have := (setAccBR_BR dmg cd x cd).2 hx
        rcases this.lt_or_eq with h | h
        · exact h
        · have h2 : setAccBR dmg cd x cd = true := by simp [setAccBR, h]
          have hx2 : setAccBR dmg cd x cd = false := hx
          rw [h2] at hx2
          exact absurd hx2 (by decide)
      nlinarith [hm.1]
    exact measure_mono_null hsub (ae_iff.1 hs)

/-- The identity is integrable for a probability measure concentrated on `[0, 1]`. -/
theorem integrable_id_of_supp [IsProbabilityMeasure μ]
    (hsupp : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) 1) : Integrable (fun x : ℝ => x) μ := by
  refine Integrable.of_bound continuous_id.aestronglyMeasurable 1 ?_
  filter_upwards [hsupp] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
  exact hx.2

/-- `E[λ π − c_p] = E[λ] π − c_p`. -/
theorem integral_trial [IsProbabilityMeasure μ] (hsupp : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) 1)
    (dmg cp : ℝ) : ∫ x, (x * dmg - cp) ∂μ = (∫ x, x ∂μ) * dmg - cp := by
  rw [integral_sub ((integrable_id_of_supp hsupp).mul_const dmg) (integrable_const cp),
    integral_mul_const, integral_const, probReal_univ, one_smul]

/-- The mean of `λ` over a lower set `L` is at most its mean over all types:
`∫_L λ ≤ Prob(L) E[λ]` (the types that reject an offer are the low ones). -/
theorem setIntegral_lower_le [IsProbabilityMeasure μ] (hsupp : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) 1)
    {L : Set ℝ} (hL : MeasurableSet L) (hlow : ∀ x y, y ∈ L → x ≤ y → x ∈ L) :
    ∫ x in L, x ∂μ ≤ μ.real L * ∫ x, x ∂μ := by
  set m := ∫ x, x ∂μ with hm
  have hI := integrable_id_of_supp hsupp
  have hsub : ∫ x in L, (x - m) ∂μ = ∫ x in L, x ∂μ - μ.real L * m := by
    rw [integral_sub hI.integrableOn (integrable_const m).integrableOn, setIntegral_const,
      smul_eq_mul]
  suffices h : ∫ x in L, (x - m) ∂μ ≤ 0 by linarith
  by_cases hcase : ∀ y ∈ L, y ≤ m
  · exact setIntegral_nonpos hL fun x hx => by linarith [hcase x hx]
  · push Not at hcase
    obtain ⟨y, hyL, hym⟩ := hcase
    have hzero : ∫ x, (x - m) ∂μ = 0 := by
      rw [integral_sub hI (integrable_const m), integral_const, probReal_univ, one_smul, sub_self]
    have hsplit := integral_add_compl hL (hI.sub (integrable_const m))
    have hcomp : 0 ≤ ∫ x in Lᶜ, (x - m) ∂μ := by
      refine setIntegral_nonneg hL.compl fun x hx => ?_
      have : y < x := by
        by_contra hn
        exact hx (hlow x y hyL (not_lt.1 hn))
      linarith
    simp only [Pi.sub_apply] at hsplit
    linarith

/-- **Exercise 9.C.4(c)** (MWG, p. 304). A profile of the game in which, after a rejection of the
offer `s'`, P decides whether to go to court (`court s'`) holding the belief `ν s'` about `λ`. -/
structure SetCProfile where
  /-- P's offer. -/
  s : ℝ
  /-- Whether type `x` accepts the offer `s'`. -/
  acc : ℝ → ℝ → Bool
  /-- Whether P goes to court after the offer `s'` is rejected. -/
  court : ℝ → Bool
  /-- P's belief about `λ` after the offer `s'` is rejected. -/
  ν : ℝ → Measure ℝ

/-- P's expected payoff from the offer `s'` followed by court (`g' = true`) or dropping the case
after a rejection, against D's strategy `acc`. -/
noncomputable def setCPay (μ : Measure ℝ) (dmg cp : ℝ) (acc : ℝ → ℝ → Bool) (s' : ℝ)
    (g' : Bool) : ℝ :=
  ∫ x, (if acc x s' then s' else if g' then x * dmg - cp else 0) ∂μ

/-- **Exercise 9.C.4(c)** (MWG, p. 304). A pure-strategy weak PBE of the game with the option to
drop the case: D best responds to P's court decision at every offer; P's beliefs are
probability measures on `[0, 1]`; P's court decision is optimal for her belief after every
rejected offer; the belief after the equilibrium offer is Bayes' (the prior conditioned on the
rejecting types) when rejection has positive probability; P's offer and court decision are
optimal against D's strategy. -/
def IsSetCWeakPBE (μ : Measure ℝ) (dmg cp cd : ℝ) (P : SetCProfile) : Prop :=
  (∀ x s', (P.acc x s' = true → (if P.court s' then s' ≤ x * dmg + cd else s' ≤ 0)) ∧
    (P.acc x s' = false → (if P.court s' then x * dmg + cd ≤ s' else 0 ≤ s'))) ∧
  (∀ s', IsProbabilityMeasure (P.ν s') ∧ ∀ᵐ x ∂(P.ν s'), x ∈ Set.Icc (0 : ℝ) 1) ∧
  (∀ s', (P.court s' = true → 0 ≤ ∫ x, (x * dmg - cp) ∂(P.ν s')) ∧
    (P.court s' = false → ∫ x, (x * dmg - cp) ∂(P.ν s') ≤ 0)) ∧
  (0 < μ {x | P.acc x P.s = false} → P.ν P.s = μ[|{x | P.acc x P.s = false}]) ∧
  ∀ s' g', setCPay μ dmg cp P.acc s' g' ≤ setCPay μ dmg cp P.acc P.s (P.court P.s)

/-- **Exercise 9.C.4(c)** (MWG, p. 304). If `E[λ] π < c_p`, no weak PBE has trials: after the
equilibrium offer either P drops the case or rejection has probability zero. The rejecting
types are the low ones, so P's posterior mean after a rejection is at most `E[λ]`, and court is
not credible. -/
theorem exercise_9_C_4c_no_trial [IsProbabilityMeasure μ]
    (hsupp : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) 1) {dmg cp cd : ℝ} (hdmg : 0 < dmg)
    (hmean : (∫ x, x ∂μ) * dmg < cp) {P : SetCProfile} (h : IsSetCWeakPBE μ dmg cp cd P) :
    ¬ (P.court P.s = true ∧ 0 < μ {x | P.acc x P.s = false}) := by
  rintro ⟨hc, hpos⟩
  obtain ⟨hBR, -, hSR, hB, -⟩ := h
  set R := {x | P.acc x P.s = false} with hR
  set t := (P.s - cd) / dmg with ht
  have hs : P.s = cd + dmg * t := by rw [ht]; field_simp; ring
  have h1 : Set.Iio t ⊆ R := by
    intro x hx
    change P.acc x P.s = false
    cases hcx : P.acc x P.s
    · rfl
    · have := (hBR x P.s).1 hcx
      simp only [hc, ↓reduceIte] at this
      rw [hs] at this
      have : t ≤ x := by nlinarith [Set.mem_Iio.1 hx]
      exact absurd hx (not_lt.2 this)
  have h2 : R ⊆ Set.Iic t := by
    intro x hx
    have := (hBR x P.s).2 hx
    simp only [hc, ↓reduceIte] at this
    rw [hs] at this
    change x ≤ t
    nlinarith
  have hRm : MeasurableSet R ∧ ∀ x y, y ∈ R → x ≤ y → x ∈ R := by
    by_cases htR : t ∈ R
    · have : R = Set.Iic t := Set.Subset.antisymm h2 fun x hx => by
        rcases (Set.mem_Iic.1 hx).lt_or_eq with h' | h'
        · exact h1 h'
        · rw [h']; exact htR
      rw [this]
      exact ⟨measurableSet_Iic, fun x y hy hxy => le_trans hxy hy⟩
    · have : R = Set.Iio t := Set.Subset.antisymm (fun x hx => by
          rcases (Set.mem_Iic.1 (h2 hx)).lt_or_eq with h' | h'
          · exact h'
          · rw [h'] at hx; exact absurd hx htR) h1
      rw [this]
      exact ⟨measurableSet_Iio, fun x y hy hxy => lt_of_le_of_lt hxy hy⟩
  have hcourt := (hSR P.s).1 hc
  rw [hB hpos, ProbabilityTheory.cond, integral_smul_measure, smul_eq_mul] at hcourt
  have hRpos : 0 < μ.real R := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos hpos.ne' (measure_ne_top μ R)
  have hinv : 0 < (μ R)⁻¹.toReal := by
    rw [ENNReal.toReal_inv]
    exact inv_pos.2 hRpos
  have hint : 0 ≤ ∫ x in R, (x * dmg - cp) ∂μ := nonneg_of_mul_nonneg_right hcourt hinv
  have hI := integrable_id_of_supp hsupp
  rw [integral_sub (hI.mul_const dmg).integrableOn (integrable_const cp).integrableOn,
    integral_mul_const, setIntegral_const, smul_eq_mul] at hint
  have hlow := setIntegral_lower_le hsupp hRm.1 hRm.2
  nlinarith [mul_le_mul_of_nonneg_right hlow hdmg.le, mul_lt_mul_of_pos_left hmean hRpos]

/-- The no-settlement profile of Exercise 9.C.4(c): P offers `1`, D rejects every positive offer,
P drops the case after every rejection and keeps the prior as belief. -/
noncomputable def setDrop (μ : Measure ℝ) : SetCProfile where
  s := 1
  acc _ s' := decide (s' ≤ 0)
  court _ := false
  ν _ := μ

/-- **Exercise 9.C.4(c)** (MWG, p. 304). The profile in which P's offer is rejected and she
drops the case (payoffs `0`) is a weak PBE iff `E[λ] π ≤ c_p`. -/
theorem exercise_9_C_4c_drop [IsProbabilityMeasure μ]
    (hsupp : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) 1) {dmg cp cd : ℝ} :
    IsSetCWeakPBE μ dmg cp cd (setDrop μ) ↔ (∫ x, x ∂μ) * dmg ≤ cp := by
  have hE := integral_trial hsupp dmg cp
  constructor
  · rintro ⟨-, -, hSR, -, -⟩
    have := (hSR 1).2 rfl
    simp only [setDrop] at this
    linarith
  · intro hm
    have hR : {x | (setDrop μ).acc x (setDrop μ).s = false} = Set.univ := by
      ext x; simp [setDrop]
    refine ⟨fun x s' => ⟨fun h => ?_, fun h => ?_⟩,
      fun _ => ⟨show IsProbabilityMeasure μ from inferInstance, hsupp⟩,
      fun _ => ⟨fun h => absurd h (by simp [setDrop]), fun _ => by simp only [setDrop]; linarith⟩,
      fun _ => by rw [hR, cond_univ]; rfl, fun s' g' => ?_⟩
    · simpa [setDrop] using h
    · simp only [setDrop, decide_eq_false_iff_not, not_le] at h
      simp only [setDrop, Bool.false_eq_true, ↓reduceIte]
      exact h.le
    · have h0 : setCPay μ dmg cp (setDrop μ).acc (setDrop μ).s ((setDrop μ).court
          (setDrop μ).s) = 0 := by
        simp [setCPay, setDrop]
      rw [h0]
      unfold setCPay
      by_cases hs : s' ≤ 0
      · simp only [setDrop, hs, decide_true, ↓reduceIte, integral_const, probReal_univ,
          one_smul]
      · simp only [setDrop, hs, decide_false, Bool.false_eq_true, ↓reduceIte]
        cases g'
        · simp
        · simp only [↓reduceIte]
          linarith

/-- The all-settle profile of Exercise 9.C.4(c) at the offer `s`: P goes to court only after a
rejection of `s` (believing `λ = 1` there) and drops the case after any other rejected offer
(keeping the prior); D accepts `s` iff `s ≤ λπ + c_d`, and any other offer iff it is `≤ 0`. -/
noncomputable def setSettle (μ : Measure ℝ) (dmg cd s : ℝ) : SetCProfile where
  s := s
  acc x s' := if s' = s then decide (s' ≤ x * dmg + cd) else decide (s' ≤ 0)
  court s' := decide (s' = s)
  ν s' := if s' = s then Measure.dirac 1 else μ

/-- **Exercise 9.C.4(c)** (MWG, p. 304). When `E[λ] π ≤ c_p ≤ π`, for every `s ∈ (0, c_d]`
there is a weak PBE in which P offers `s`, every type settles, and P earns `s`: going to court
is credible after a rejection of `s` (an off-path event, where any belief is allowed), and
not after other offers. So the weak PBE of (c) are far from unique. -/
theorem exercise_9_C_4c_settle [IsProbabilityMeasure μ]
    (hsupp : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) 1) {dmg cp cd s : ℝ} (hdmg : 0 < dmg)
    (hcp : cp ≤ dmg) (hmean : (∫ x, x ∂μ) * dmg ≤ cp) (hs0 : 0 < s) (hs1 : s ≤ cd) :
    IsSetCWeakPBE μ dmg cp cd (setSettle μ dmg cd s) ∧
      μ {x | (setSettle μ dmg cd s).acc x s = false} = 0 ∧
      setCPay μ dmg cp (setSettle μ dmg cd s).acc s true = s := by
  have hE := integral_trial hsupp dmg cp
  have hacc : ∀ᵐ x ∂μ, (setSettle μ dmg cd s).acc x s = true := by
    filter_upwards [hsupp] with x hx
    simp only [setSettle, ↓reduceIte, decide_eq_true_eq]
    nlinarith [hx.1]
  have hnull : μ {x | (setSettle μ dmg cd s).acc x s = false} = 0 := by
    rw [← ae_iff.1 hacc]
    congr 1
    ext x
    simp
  have hpay : ∀ g', setCPay μ dmg cp (setSettle μ dmg cd s).acc s g' = s := by
    intro g'
    unfold setCPay
    rw [integral_congr_ae (g := fun _ => s) (by
      filter_upwards [hacc] with x hx
      simp [hx]), integral_const, probReal_univ, one_smul]
  refine ⟨⟨fun x s' => ⟨fun h => ?_, fun h => ?_⟩, fun s' => ?_, fun s' => ⟨fun h => ?_,
    fun h => ?_⟩, fun h => absurd h (by
    rw [show (setSettle μ dmg cd s).s = s from rfl, hnull]; exact lt_irrefl 0), fun s' g' => ?_⟩,
    hnull, hpay true⟩
  · by_cases hs : s' = s
    · simp only [setSettle, hs, ↓reduceIte, decide_true, decide_eq_true_eq] at h ⊢
      exact h
    · simp only [setSettle, hs, ↓reduceIte, decide_false, Bool.false_eq_true,
        decide_eq_true_eq] at h ⊢
      exact h
  · by_cases hs : s' = s
    · simp only [setSettle, hs, ↓reduceIte, decide_true, decide_eq_false_iff_not,
        not_le] at h ⊢
      exact h.le
    · simp only [setSettle, hs, ↓reduceIte, decide_false, Bool.false_eq_true,
        decide_eq_false_iff_not, not_le] at h ⊢
      exact h.le
  · by_cases hs : s' = s
    · simp only [setSettle, hs, ↓reduceIte]
      refine ⟨inferInstance, ?_⟩
      exact (ae_dirac_iff (p := fun x => x ∈ Set.Icc (0 : ℝ) 1) measurableSet_Icc).2
        ⟨zero_le_one, le_rfl⟩
    · simp only [setSettle, hs, ↓reduceIte]
      exact ⟨inferInstance, hsupp⟩
  · have hs : s' = s := by simpa [setSettle] using h
    simp only [setSettle, hs, ↓reduceIte]
    rw [integral_dirac]
    linarith
  · have hs : s' ≠ s := by simpa [setSettle] using h
    simp only [setSettle, hs, ↓reduceIte]
    linarith
  · rw [show (setSettle μ dmg cd s).s = s from rfl, hpay]
    by_cases hs : s' = s
    · rw [hs, hpay]
    · unfold setCPay
      by_cases h0 : s' ≤ 0
      · simp only [setSettle, hs, h0, ↓reduceIte, decide_true, integral_const, probReal_univ,
          one_smul]
        linarith
      · simp only [setSettle, hs, h0, ↓reduceIte, decide_false, Bool.false_eq_true]
        cases g'
        · simp only [Bool.false_eq_true, ↓reduceIte, integral_zero]
          exact hs0.le
        · simp only [↓reduceIte]
          linarith

end MWG.DynamicGames

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Pretrial settlement with an informed plaintiff

MWG, Exercise 9.C.5 (p. 304): Exercise 9.C.4 when it is Ms. P who knows `λ` (and makes the
offer), and the sequential-equilibrium reading of Exercise 9.C.6 for Exercises 9.C.4(c) and
9.C.5.

Model (`IsSet5WeakPBE`): P's offer is a function `σ` of her type `λ ∈ [0, 1]`; D accepts or
rejects each offer (`acc s`) holding a belief `ν s` (a probability measure on `[0, 1]`) about
`λ`; D accepts only if paying `s` is no worse than the expected trial payment `E_ν[λ] π + c_d`,
rejects only if it is no better; each type of P chooses an optimal offer; and D's belief after
an offer made with positive prior probability is Bayes' (the prior conditioned on the types
making it).

* `exercise_9_C_5`: in every weak PBE all settling types settle at the same amount, every type
  gets at least `max (c_d, λπ − c_p)`, and the types going to trial are the high ones (if `λ`
  goes to trial, so does every `λ' > λ`): high types do not settle because no offer above what
  the low types would accept is accepted.
* `exercise_9_C_5_semi`: for every prior there is a weak PBE in which the types with
  `λπ − c_p ≤ c_d` settle at `c_d` and the others go to trial.
* `exercise_9_C_5_pooling`: if `π − c_p ≤ E[λ] π + c_d`, every `s` with
  `max (c_d, π − c_p) ≤ s ≤ E[λ] π + c_d` is the offer of a pooling weak PBE in which every type
  settles at `s` (off-path offers above `c_d` are believed to come from `λ = 0`); with the
  prior as belief after every offer (`exercise_9_C_5_passive`) the pooling offer is
  `E[λ] π + c_d`.
* Exercise 9.C.6 for 9.C.4(c): `IsSetCConsistent` (structural consistency: after every offer
  rejected with positive probability, P's belief is the prior conditioned on the rejecting
  types). `exercise_9_C_6_settlement`: the multiple weak PBE of `exercise_9_C_4c_settle` and
  `exercise_9_C_4c_drop` are consistent, so the sequential equilibria are not unique either.
-/

namespace MWG.DynamicGames

open MeasureTheory ProbabilityTheory

/-- P's payoff in Exercise 9.C.5 when her type is `x`, she offers `s`, and D's strategy is
`acc`. -/
noncomputable def set5Pay (dmg cp : ℝ) (acc : ℝ → Bool) (x s : ℝ) : ℝ :=
  if acc s then s else x * dmg - cp

theorem set5Pay_acc {dmg cp : ℝ} {acc : ℝ → Bool} {s : ℝ} (h : acc s = true) (x : ℝ) :
    set5Pay dmg cp acc x s = s := by
  simp [set5Pay, h]

theorem set5Pay_rej {dmg cp : ℝ} {acc : ℝ → Bool} {s : ℝ} (h : acc s = false) (x : ℝ) :
    set5Pay dmg cp acc x s = x * dmg - cp := by
  simp [set5Pay, h]

/-- **Exercise 9.C.5** (MWG, p. 304). A profile: P's offer as a function of her type, D's
acceptance rule, and D's beliefs after each offer. -/
structure Set5Profile where
  /-- The offer of P's type `x`. -/
  σ : ℝ → ℝ
  /-- Whether D accepts the offer `s`. -/
  acc : ℝ → Bool
  /-- D's belief about `λ` after the offer `s`. -/
  ν : ℝ → Measure ℝ

/-- **Exercise 9.C.5** (MWG, p. 304). A pure-strategy weak PBE. -/
def IsSet5WeakPBE (μ : Measure ℝ) (dmg cp cd : ℝ) (P : Set5Profile) : Prop :=
  (∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ s', set5Pay dmg cp P.acc x s' ≤ set5Pay dmg cp P.acc x (P.σ x)) ∧
  (∀ s, IsProbabilityMeasure (P.ν s) ∧ ∀ᵐ x ∂(P.ν s), x ∈ Set.Icc (0 : ℝ) 1) ∧
  (∀ s, (P.acc s = true → s ≤ (∫ x, x ∂(P.ν s)) * dmg + cd) ∧
    (P.acc s = false → (∫ x, x ∂(P.ν s)) * dmg + cd ≤ s)) ∧
  ∀ s, 0 < μ (P.σ ⁻¹' {s}) → P.ν s = μ[|P.σ ⁻¹' {s}]

/-- The mean of a probability measure concentrated on `[0, 1]` lies in `[0, 1]`. -/
theorem mean_mem_Icc {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (h : ∀ᵐ x ∂ν, x ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ ∫ x, x ∂ν ∧ ∫ x, x ∂ν ≤ 1 := by
  refine ⟨integral_nonneg_of_ae (by filter_upwards [h] with x hx; exact hx.1), ?_⟩
  have := integral_mono_ae (integrable_id_of_supp h) (integrable_const (1 : ℝ))
    (by filter_upwards [h] with x hx; exact hx.2)
  rwa [integral_const, probReal_univ, one_smul] at this

/-- In a weak PBE of Exercise 9.C.5, D accepts every offer below `c_d` and rejects every offer
above `π + c_d`, whatever her belief. -/
theorem set5_acc_facts {μ : Measure ℝ} {dmg cp cd : ℝ} (hdmg : 0 < dmg) {P : Set5Profile}
    (h : IsSet5WeakPBE μ dmg cp cd P) :
    (∀ s, s < cd → P.acc s = true) ∧ (∀ s, dmg + cd < s → P.acc s = false) := by
  obtain ⟨-, hν, hD, -⟩ := h
  refine ⟨fun s hs => ?_, fun s hs => ?_⟩
  · have := (hν s).1
    obtain ⟨h0, -⟩ := mean_mem_Icc (hν s).2
    cases hc : P.acc s
    · have := (hD s).2 hc
      nlinarith
    · rfl
  · have := (hν s).1
    obtain ⟨-, h1⟩ := mean_mem_Icc (hν s).2
    cases hc : P.acc s
    · rfl
    · have := (hD s).1 hc
      nlinarith

/-- **Exercise 9.C.5** (MWG, p. 304). In every weak PBE: (i) all settling types make the same
offer; (ii) every type gets at least `c_d` and at least `λπ − c_p`; (iii) the types going to
trial are the high ones: if type `x` goes to trial, so does every type `y > x`. -/
theorem exercise_9_C_5 {μ : Measure ℝ} {dmg cp cd : ℝ} (hdmg : 0 < dmg) {P : Set5Profile}
    (h : IsSet5WeakPBE μ dmg cp cd P) :
    (∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, P.acc (P.σ x) = true →
      P.acc (P.σ y) = true → P.σ x = P.σ y) ∧
    (∀ x ∈ Set.Icc (0 : ℝ) 1, cd ≤ set5Pay dmg cp P.acc x (P.σ x) ∧
      x * dmg - cp ≤ set5Pay dmg cp P.acc x (P.σ x)) ∧
    (∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, x < y → P.acc (P.σ x) = false →
      P.acc (P.σ y) = false) := by
  obtain ⟨hacc, hrej⟩ := set5_acc_facts hdmg h
  have hopt := h.1
  refine ⟨fun x hx y hy hax hay => ?_, fun x hx => ⟨?_, ?_⟩, fun x hx y hy hxy hrx => ?_⟩
  · have h1 := hopt x hx (P.σ y)
    have h2 := hopt y hy (P.σ x)
    simp only [set5Pay, hax, hay, ↓reduceIte] at h1 h2
    linarith
  · by_contra hn
    push Not at hn
    set u := set5Pay dmg cp P.acc x (P.σ x)
    have := hopt x hx ((u + cd) / 2)
    rw [set5Pay_acc (hacc _ (by linarith))] at this
    linarith
  · have := hopt x hx (dmg + cd + 1)
    rwa [set5Pay_rej (hrej _ (by linarith))] at this
  · cases hay : P.acc (P.σ y)
    · rfl
    · have h1 := hopt x hx (P.σ y)
      have h2 := hopt y hy (dmg + cd + 1)
      rw [set5Pay_acc hay, set5Pay_rej hrx] at h1
      rw [set5Pay_rej (hrej _ (by linarith)), set5Pay_acc hay] at h2
      nlinarith [hx.1, hy.1]

/-- The pooling profile of Exercise 9.C.5 at the offer `s`: every type offers `s`; D accepts
`s` and every offer `≤ c_d`; D believes the prior after `s` and `λ = 0` after other offers. -/
noncomputable def set5Pool (μ : Measure ℝ) (cd s : ℝ) : Set5Profile where
  σ _ := s
  acc s' := decide (s' = s ∨ s' ≤ cd)
  ν s' := if s' = s then μ else Measure.dirac 0

/-- **Exercise 9.C.5** (MWG, p. 304). If `max (c_d, π − c_p) ≤ s ≤ E[λ] π + c_d`, every type of P
offering `s` and every type settling is a weak PBE. -/
theorem exercise_9_C_5_pooling {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hsupp : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) 1) {dmg cp cd s : ℝ} (hdmg : 0 < dmg)
    (hs1 : cd ≤ s) (hs2 : dmg - cp ≤ s) (hs3 : s ≤ (∫ x, x ∂μ) * dmg + cd) :
    IsSet5WeakPBE μ dmg cp cd (set5Pool μ cd s) ∧ ∀ x, (set5Pool μ cd s).acc
      ((set5Pool μ cd s).σ x) = true := by
  have hacc : (set5Pool μ cd s).acc s = true := by simp [set5Pool]
  refine ⟨⟨fun x hx s' => ?_, fun s' => ?_, fun s' => ⟨fun h => ?_, fun h => ?_⟩,
    fun s' hpos => ?_⟩, fun _ => hacc⟩
  · change _ ≤ set5Pay dmg cp _ x s
    rw [set5Pay_acc hacc]
    cases hc : (set5Pool μ cd s).acc s'
    · rw [set5Pay_rej hc]
      nlinarith [hx.2]
    · rw [set5Pay_acc hc]
      simp only [set5Pool, decide_eq_true_eq] at hc
      rcases hc with hc | hc <;> linarith
  · by_cases hs : s' = s
    · simp only [set5Pool, hs, ↓reduceIte]
      exact ⟨inferInstance, hsupp⟩
    · simp only [set5Pool, hs, ↓reduceIte]
      exact ⟨inferInstance,
        (ae_dirac_iff (p := fun x => x ∈ Set.Icc (0 : ℝ) 1) measurableSet_Icc).2
          ⟨le_rfl, zero_le_one⟩⟩
  · by_cases hs : s' = s
    · simp only [set5Pool, hs, ↓reduceIte]
      exact hs3
    · simp only [set5Pool, hs, ↓reduceIte, integral_dirac, zero_mul, zero_add]
      simp only [set5Pool, hs, false_or, decide_eq_true_eq] at h
      exact h
  · by_cases hs : s' = s
    · rw [hs, hacc] at h
      exact absurd h (by decide)
    · simp only [set5Pool, hs, ↓reduceIte, integral_dirac, zero_mul, zero_add]
      simp only [set5Pool, hs, false_or, decide_eq_false_iff_not, not_le] at h
      exact h.le
  · by_cases hs : s' = s
    · have : (set5Pool μ cd s).σ ⁻¹' {s'} = Set.univ := by
        ext x; simp [set5Pool, hs]
      rw [this, cond_univ]
      simp [set5Pool, hs]
    · have : (set5Pool μ cd s).σ ⁻¹' {s'} = ∅ := by
        ext x; simp [set5Pool, Ne.symm hs]
      rw [this, measure_empty] at hpos
      exact absurd hpos (lt_irrefl 0)

/-- The pooling profile with passive beliefs: every type offers `E[λ] π + c_d`, and D keeps the
prior as her belief after every offer. -/
noncomputable def set5Passive (μ : Measure ℝ) (dmg cd : ℝ) : Set5Profile where
  σ _ := (∫ x, x ∂μ) * dmg + cd
  acc s' := decide (s' ≤ (∫ x, x ∂μ) * dmg + cd)
  ν _ := μ

/-- **Exercise 9.C.5** (MWG, p. 304). If `π − c_p ≤ E[λ] π + c_d`, every type offering
`E[λ] π + c_d`, D accepting exactly the offers up to `E[λ] π + c_d` and keeping the prior as
her belief after every offer, is a weak PBE in which every type settles. (These beliefs are the
limits of the Bayes beliefs when every type trembles to every offer with the same probability,
so this is a sequential equilibrium in the reading of Exercise 9.C.6.) -/
theorem exercise_9_C_5_passive {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hsupp : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) 1) {dmg cp cd : ℝ} (hdmg : 0 < dmg)
    (hle : dmg - cp ≤ (∫ x, x ∂μ) * dmg + cd) :
    IsSet5WeakPBE μ dmg cp cd (set5Passive μ dmg cd) := by
  set m := (∫ x, x ∂μ) * dmg + cd with hm
  have hacc : (set5Passive μ dmg cd).acc m = true := by simp [set5Passive, hm]
  refine ⟨fun x hx s' => ?_, fun _ => ⟨show IsProbabilityMeasure μ from inferInstance, hsupp⟩,
    fun s' => ⟨fun h => ?_, fun h => ?_⟩, fun s' hpos => ?_⟩
  · change _ ≤ set5Pay dmg cp _ x m
    rw [set5Pay_acc hacc]
    cases hc : (set5Passive μ dmg cd).acc s'
    · rw [set5Pay_rej hc]
      nlinarith [hx.2]
    · rw [set5Pay_acc hc]
      simpa [set5Passive, hm] using hc
  · simpa [set5Passive] using h
  · simp only [set5Passive, decide_eq_false_iff_not, not_le] at h
    exact h.le
  · by_cases hs : s' = m
    · have : (set5Passive μ dmg cd).σ ⁻¹' {s'} = Set.univ := by
        ext x; simp [set5Passive, hs, hm]
      rw [this, cond_univ]
      rfl
    · have : (set5Passive μ dmg cd).σ ⁻¹' {s'} = ∅ := by
        ext x; simp only [set5Passive, Set.mem_preimage, Set.mem_singleton_iff,
          Set.mem_empty_iff_false, iff_false]; exact fun h => hs (by rw [← h])
      rw [this, measure_empty] at hpos
      exact absurd hpos (lt_irrefl 0)

/-- A belief: the prior conditioned on `S` if `S` has positive probability, `λ = 0` otherwise. -/
noncomputable def condOrZero (μ : Measure ℝ) (S : Set ℝ) : Measure ℝ :=
  if 0 < μ S then μ[|S] else Measure.dirac 0

theorem condOrZero_facts {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hsupp : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) 1) (S : Set ℝ) :
    IsProbabilityMeasure (condOrZero μ S) ∧
      ∀ᵐ x ∂(condOrZero μ S), x ∈ Set.Icc (0 : ℝ) 1 := by
  unfold condOrZero
  split_ifs with h
  · exact ⟨cond_isProbabilityMeasure h.ne', cond_absolutelyContinuous.ae_le hsupp⟩
  · exact ⟨inferInstance, (ae_dirac_iff (p := fun x => x ∈ Set.Icc (0 : ℝ) 1)
      measurableSet_Icc).2 ⟨le_rfl, zero_le_one⟩⟩

/-- The semi-pooling profile of Exercise 9.C.5: the types with `λπ − c_p ≤ c_d` offer `c_d`,
the others offer `π + c_d + 1` (rejected, so they go to trial); D accepts exactly the offers up
to `c_d`. -/
noncomputable def set5Semi (μ : Measure ℝ) (dmg cp cd : ℝ) : Set5Profile where
  σ x := if x ≤ (cd + cp) / dmg then cd else dmg + cd + 1
  acc s' := decide (s' ≤ cd)
  ν s' := if s' = cd then condOrZero μ (Set.Iic ((cd + cp) / dmg))
    else if s' = dmg + cd + 1 then condOrZero μ (Set.Ioi ((cd + cp) / dmg))
    else Measure.dirac 0

/-- **Exercise 9.C.5** (MWG, p. 304). For every prior, the types with `λπ − c_p ≤ c_d` settling
at `c_d` and the others going to trial is a weak PBE; in particular a weak PBE always exists.
-/
theorem exercise_9_C_5_semi {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hsupp : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) 1) {dmg cp cd : ℝ} (hdmg : 0 < dmg) :
    IsSet5WeakPBE μ dmg cp cd (set5Semi μ dmg cp cd) ∧
      ∀ x, ((set5Semi μ dmg cp cd).acc ((set5Semi μ dmg cp cd).σ x) = true ↔
        x * dmg - cp ≤ cd) := by
  set τ := (cd + cp) / dmg with hτ
  have hne : cd ≠ dmg + cd + 1 := by intro h; linarith
  have hτ' : ∀ x, x ≤ τ ↔ x * dmg - cp ≤ cd := fun x => by
    rw [hτ, le_div_iff₀ hdmg]; constructor <;> intro <;> linarith
  have hσacc : ∀ x, ((set5Semi μ dmg cp cd).acc ((set5Semi μ dmg cp cd).σ x) = true ↔
      x * dmg - cp ≤ cd) := by
    intro x
    by_cases hx : x ≤ τ
    · simp only [set5Semi, ← hτ, hx, ↓reduceIte, le_refl, decide_true, true_iff]
      exact (hτ' x).1 hx
    · simp only [set5Semi, ← hτ, hx, ↓reduceIte, decide_eq_true_eq]
      constructor
      · intro h; linarith
      · intro h; exact absurd ((hτ' x).2 h) hx
  have hbel : ∀ s', IsProbabilityMeasure ((set5Semi μ dmg cp cd).ν s') ∧
      ∀ᵐ x ∂((set5Semi μ dmg cp cd).ν s'), x ∈ Set.Icc (0 : ℝ) 1 := by
    intro s'
    simp only [set5Semi, ← hτ]
    split_ifs
    · exact condOrZero_facts hsupp _
    · exact condOrZero_facts hsupp _
    · exact ⟨inferInstance, (ae_dirac_iff (p := fun x => x ∈ Set.Icc (0 : ℝ) 1)
        measurableSet_Icc).2 ⟨le_rfl, zero_le_one⟩⟩
  refine ⟨⟨fun x hx s' => ?_, hbel, fun s' => ⟨fun h => ?_, fun h => ?_⟩,
    fun s' hpos => ?_⟩, hσacc⟩
  · by_cases hx' : x * dmg - cp ≤ cd
    · rw [set5Pay_acc ((hσacc x).2 hx')]
      have hc : (set5Semi μ dmg cp cd).σ x = cd := by
        simp [set5Semi, ← hτ, (hτ' x).2 hx']
      rw [hc]
      cases hs : (set5Semi μ dmg cp cd).acc s'
      · rw [set5Pay_rej hs]; exact hx'
      · rw [set5Pay_acc hs]; simpa [set5Semi] using hs
    · have hr : (set5Semi μ dmg cp cd).acc ((set5Semi μ dmg cp cd).σ x) = false := by
        cases hc : (set5Semi μ dmg cp cd).acc ((set5Semi μ dmg cp cd).σ x)
        · rfl
        · exact absurd ((hσacc x).1 hc) hx'
      rw [set5Pay_rej hr]
      cases hs : (set5Semi μ dmg cp cd).acc s'
      · rw [set5Pay_rej hs]
      · rw [set5Pay_acc hs]
        have : s' ≤ cd := by simpa [set5Semi] using hs
        linarith
  · have hs : s' ≤ cd := by simpa [set5Semi] using h
    have := (hbel s').1
    obtain ⟨h0, -⟩ := mean_mem_Icc (hbel s').2
    nlinarith
  · have hs : cd < s' := by simpa [set5Semi] using h
    by_cases h1 : s' = dmg + cd + 1
    · have := (hbel s').1
      obtain ⟨-, h1'⟩ := mean_mem_Icc (hbel s').2
      nlinarith
    · have hcd : s' ≠ cd := fun h' => by rw [h'] at hs; exact lt_irrefl _ hs
      simp only [set5Semi, hcd, h1, ↓reduceIte, integral_dirac, zero_mul, zero_add]
      exact hs.le
  · by_cases h1 : s' = cd
    · have hpre : (set5Semi μ dmg cp cd).σ ⁻¹' {s'} = Set.Iic τ := by
        ext x
        simp only [set5Semi, ← hτ, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_Iic, h1]
        split_ifs with hx
        · simp [hx]
        · simp only [hx, iff_false]; exact fun h => hne h.symm
      rw [hpre] at hpos ⊢
      simp only [set5Semi, ← hτ, h1, ↓reduceIte, condOrZero, hpos]
    · by_cases h2 : s' = dmg + cd + 1
      · have hpre : (set5Semi μ dmg cp cd).σ ⁻¹' {s'} = Set.Ioi τ := by
          ext x
          simp only [set5Semi, ← hτ, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_Ioi, h2]
          split_ifs with hx
          · simp only [hne, false_iff, not_lt]; exact hx
          · simp only [true_iff]; exact not_le.1 hx
        rw [hpre] at hpos ⊢
        simp only [set5Semi, ← hτ, h2, ↓reduceIte, condOrZero, hpos, Ne.symm hne]
      · have hpre : (set5Semi μ dmg cp cd).σ ⁻¹' {s'} = ∅ := by
          ext x
          simp only [set5Semi, Set.mem_preimage, Set.mem_singleton_iff,
            Set.mem_empty_iff_false, iff_false]
          split_ifs
          · exact fun h => h1 h.symm
          · exact fun h => h2 h.symm
        rw [hpre, measure_empty] at hpos
        exact absurd hpos (lt_irrefl 0)

/-- **Exercise 9.C.6** (MWG, p. 304), structural consistency for Exercise 9.C.4(c): after every
offer that is rejected with positive probability (on or off the equilibrium path), P's belief
is the prior conditioned on the rejecting types (P's own trembles do not depend on `λ`). -/
def IsSetCConsistent (μ : Measure ℝ) (P : SetCProfile) : Prop :=
  ∀ s', 0 < μ {x | P.acc x s' = false} → P.ν s' = μ[|{x | P.acc x s' = false}]

/-- **Exercise 9.C.6 for Exercise 9.C.4(c)** (MWG, p. 304). The weak PBE of
`exercise_9_C_4c_settle` (every type settles at any `s ∈ (0, c_d]`) and of
`exercise_9_C_4c_drop` (no settlement, P drops the case) have consistent beliefs, so they are
sequential equilibria in the reading of Exercise 9.C.6, which therefore does not remove the
multiplicity. -/
theorem exercise_9_C_6_settlement {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hsupp : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) 1) {dmg cd s : ℝ} (hdmg : 0 < dmg)
    (hs1 : s ≤ cd) :
    IsSetCConsistent μ (setSettle μ dmg cd s) ∧ IsSetCConsistent μ (setDrop μ) := by
  constructor
  · intro s' hpos
    by_cases hs : s' = s
    · exfalso
      subst hs
      have hnull : μ {x | (setSettle μ dmg cd s').acc x s' = false} = 0 := by
        have hsub : {x | (setSettle μ dmg cd s').acc x s' = false} ⊆
            {x | x ∉ Set.Icc (0 : ℝ) 1} := by
          intro x hx hm
          have hx' : s' > x * dmg + cd := by
            have hx2 : (setSettle μ dmg cd s').acc x s' = false := hx
            simpa [setSettle] using hx2
          nlinarith [hm.1]
        exact measure_mono_null hsub (ae_iff.1 hsupp)
      rw [hnull] at hpos
      exact lt_irrefl 0 hpos
    · by_cases h0 : s' ≤ 0
      · have : {x | (setSettle μ dmg cd s).acc x s' = false} = ∅ := by
          ext x; simp [setSettle, hs, h0]
        rw [this, measure_empty] at hpos
        exact absurd hpos (lt_irrefl 0)
      · have : {x | (setSettle μ dmg cd s).acc x s' = false} = Set.univ := by
          ext x; simp [setSettle, hs, h0]
        rw [this, cond_univ]
        simp [setSettle, hs]
  · intro s' hpos
    by_cases h0 : s' ≤ 0
    · have : {x | (setDrop μ).acc x s' = false} = ∅ := by
        ext x; simp [setDrop, h0]
      rw [this, measure_empty] at hpos
      exact absurd hpos (lt_irrefl 0)
    · have : {x | (setDrop μ).acc x s' = false} = Set.univ := by
        ext x; simp [setDrop, h0]
      rw [this, cond_univ]
      rfl

/-- **Exercises 9.C.4(c) and 9.C.5, examples** (MWG, p. 304), with the uniform prior and
`π = c_d = 1`: for `c_p = 2` the no-settlement profile is a weak PBE and trials never occur in
any weak PBE (`E[λ] π ≤ 1 < 2`); for `c_p = 1` every type settling at `1/2` is a weak PBE; and in
the informed-plaintiff game the semi-pooling profile is a weak PBE. -/
theorem exercise_9_C_4c_5_examples :
    IsSetCWeakPBE unifPrior 1 2 1 (setDrop unifPrior) ∧
    (∀ P, IsSetCWeakPBE unifPrior 1 2 1 P →
      ¬ (P.court P.s = true ∧ 0 < unifPrior {x | P.acc x P.s = false})) ∧
    IsSetCWeakPBE unifPrior 1 1 1 (setSettle unifPrior 1 1 (1 / 2)) ∧
    IsSet5WeakPBE unifPrior 1 1 1 (set5Semi unifPrior 1 1 1) := by
  have hP := unifPrior_isProbabilityMeasure
  have hs := unifPrior_supp
  have hE := (mean_mem_Icc hs).2
  refine ⟨(exercise_9_C_4c_drop hs).2 (by linarith), fun P h =>
    exercise_9_C_4c_no_trial hs one_pos (by linarith) h,
    (exercise_9_C_4c_settle hs one_pos le_rfl (by linarith) (by norm_num) (by norm_num)).1,
    (exercise_9_C_5_semi hs one_pos).1⟩

end MWG.DynamicGames

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Footnote 15: the forward induction examples are extensive form trembling-hand perfect

MWG, Section 9.D, footnote 15 (p. 292), with Appendix B (pp. 299-300).

* `isEFTHP_pureMoves_of`: a sufficient condition for extensive form trembling-hand perfection
  of a pure profile `c` (in a game without absent-mindedness): a sequence of totally mixed
  behaviour profiles converging to `c` against which, at every personal information set, the
  sure move `c k` is a best reply of the agent there. (The agent normal form profiles built from
  the sequence are totally mixed, converge to `c`, and `c` is a best response to each, so
  Proposition 8.F.1 applies; the limit is a Nash equilibrium of the agent normal form by
  continuity.)
* `footnote_15_D_1a_EFTHP`, `footnote_15_D_1b_EFTHP`, `footnote_15_D_2_EFTHP`: the weak PBE of
  Figures 9.D.1(a), 9.D.1(b) and 9.D.2 are extensive form trembling-hand perfect. Trembles: E
  plays the entry strategy that I's beliefs favour with probability `ε`, the other with `ε²`;
  each agent of I plays its other action with probability `ε`, where `ε = 1/(n + 5)`.
-/

namespace MWG.DynamicGames

open MWG.NoncooperativeGames MWG.NoncooperativeGames.ExtensiveForm MWG.SimultaneousMoveGames
  Filter Topology

variable {I A H : Type*} (G : ExtensiveForm I A H) [DecidableEq A] [Fintype A] [DecidableEq I]
  [DecidableEq H]

omit [DecidableEq I] in
/-- **Appendix B** (MWG, pp. 299-300). A sufficient condition for extensive form trembling-hand
perfection. In a game without absent-mindedness, the sure choice `c` is an extensive form
trembling-hand perfect Nash equilibrium if there are totally mixed behaviour profiles `Fsⁿ`
whose moves converge to those of `c` and against which, for every `n` and every personal
information set `k` of player `i`, playing `c k` for sure at `k` is at least as good for `i` as
playing any other available action `b` for sure at `k`. -/
theorem isEFTHP_pureMoves_of [Fintype H] (hNA : G.NoAbsentMindedness) {c : H → A}
    (hc : ∀ k, c k ∈ G.avail k) (Fs : ℕ → I → H → A → ℝ)
    (hTM : ∀ n, IsTotallyMixedB G (Fs n))
    (hlim : ∀ i k, G.player k = some i → ∀ a,
      Tendsto (fun n => Fs n i k a) atTop (𝓝 (dirac (c k) a)))
    (hbest : ∀ n i k, G.player k = some i → ∀ b ∈ G.avail k,
      cont G (Function.update (G.assemble (Fs n)) k (dirac b)) [] i ≤
        cont G (Function.update (G.assemble (Fs n)) k (dirac (c k))) [] i) :
    IsEFTHP G (pureMoves (I := I) c) := by
  set ρ : ℕ → (ag : Agent G) → (agentForm G).PureStrategy ag → ℝ :=
    fun n ag s => Fs n (owner G ag) ag.1 ((agentEquiv G ag).symm s).1 with hρ
  set σ : (ag : Agent G) → (agentForm G).PureStrategy ag → ℝ :=
    fun ag => pureMixed (agentPure G ag ⟨c ag.1, hc ag.1⟩) with hσ
  have hown : ∀ ag : Agent G, G.player ag.1 = some (owner G ag) := player_owner G
  -- the agent profiles assemble to the given behaviour profiles
  have hA : ∀ n, G.assemble (agentProfile G (ρ n)) = G.assemble (Fs n) := by
    intro n
    funext k a
    cases hk : G.player k with
    | none => rw [G.assemble_of_none _ hk, G.assemble_of_none _ hk]
    | some i =>
      have hne : G.player k ≠ none := by rw [hk]; simp
      have hi : owner G ⟨k, hne⟩ = i := by
        have := hown ⟨k, hne⟩
        rw [hk] at this
        exact (Option.some.inj this).symm
      have h1 := assemble_agentProfile_apply G (ρ n) ⟨k, hne⟩ a
      rw [h1, G.assemble_of_some _ hk]
      split_ifs with ha
      · simp only [hρ, hi]
        rfl
      · exact (((hTM n).1 i k hk).2.1 a ha).symm
  -- the agent profiles are totally mixed
  have hρpos : ∀ n ag s, 0 < ρ n ag s := fun n ag s =>
    (hTM n).2 _ _ (hown ag) _ ((agentEquiv G ag).symm s).2
  have hρsum : ∀ n ag, ∑ s, ρ n ag s = 1 := by
    intro n ag
    have h1 := ((hTM n).1 (owner G ag) ag.1 (hown ag)).2.2
    rw [← Finset.sum_coe_sort] at h1
    rw [← h1, ← Equiv.sum_comp (agentEquiv G ag)]
    rfl
  have hρmix : ∀ n ag, IsMixedStrategy (ρ n ag) := fun n ag =>
    ⟨fun s => (hρpos n ag s).le, hρsum n ag⟩
  -- the value of `σ` at the pure strategy of an action
  have hσval : ∀ ag (a : {a // a ∈ G.avail ag.1}),
      σ ag (agentEquiv G ag a) = dirac (c ag.1) a.1 := by
    intro ag a
    by_cases h : a.1 = c ag.1
    · have : a = ⟨c ag.1, hc ag.1⟩ := Subtype.ext h
      subst this
      change pureMixed _ (agentPure G ag _) = _
      simp [pureMixed, dirac]
    · have hne : agentEquiv G ag a ≠ agentPure G ag ⟨c ag.1, hc ag.1⟩ := fun he =>
        h (congrArg Subtype.val ((agentEquiv G ag).injective he))
      simp only [hσ, pureMixed, dirac, hne, h, ↓reduceIte]
  have hρlim : Tendsto ρ atTop (𝓝 σ) := by
    refine tendsto_pi_nhds.2 fun ag => tendsto_pi_nhds.2 fun s => ?_
    obtain ⟨a, rfl⟩ := (agentEquiv G ag).surjective s
    rw [hσval]
    exact hlim _ _ (hown ag) a.1
  -- `c` is a best reply of every agent against every `ρ n`
  have hpay : ∀ n ag (b : (agentForm G).PureStrategy ag),
      (agentNF G).mixedPayoff (Function.update (ρ n) ag (pureMixed b)) ag ≤
        (agentNF G).mixedPayoff (Function.update (ρ n) ag (σ ag)) ag := by
    intro n ag b
    obtain ⟨⟨b, hb⟩, rfl⟩ := (agentEquiv G ag).surjective b
    have hmixU : ∀ s, ∀ ag', IsMixedStrategy (Function.update (ρ n) ag (pureMixed s) ag') := by
      intro s ag'
      by_cases h : ag' = ag
      · subst h
        rw [Function.update_self]
        exact isMixedStrategy_pureMixed s
      · rw [Function.update_of_ne h]
        exact hρmix n ag'
    have e1 : agentEquiv G ag ⟨b, hb⟩ = agentPure G ag ⟨b, hb⟩ := rfl
    rw [e1, hσ, agentNF_mixedPayoff G hNA (hmixU _), agentNF_mixedPayoff G hNA (hmixU _),
      assemble_agentProfile_update G _ ag hb, assemble_agentProfile_update G _ ag (hc ag.1),
      hA n]
    exact hbest n _ _ (hown ag) b hb
  have hsupp : ∀ ag (a : (agentForm G).PureStrategy ag), 0 < σ ag a →
      pureMixed a = σ ag := by
    intro ag a ha
    simp only [hσ, pureMixed] at ha ⊢
    split_ifs at ha with h
    · rw [h]
    · exact absurd ha (lt_irrefl 0)
  have hbr : ∀ n ag, IsBestResponse (agentNF G) ag (σ ag) (ρ n) := by
    intro n ag
    refine (isBestResponse_iff_support _ ag (isMixedStrategy_pureMixed _) _).2
      fun a ha b => ?_
    rw [hsupp ag a ha]
    exact hpay n ag b
  -- the limit `σ` is a Nash equilibrium of the agent normal form
  have hσmix : IsMixedProfile σ := fun ag => isMixedStrategy_pureMixed _
  have hNash : IsMixedNash (agentNF G) σ := by
    refine (isMixedNash_iff_bestResponse _ σ).2 ⟨hσmix, fun ag => ?_⟩
    refine (isBestResponse_iff_support _ ag (hσmix ag) _).2 fun a ha b => ?_
    rw [hsupp ag a ha]
    exact le_of_tendsto_of_tendsto'
      (tendsto_mixedPayoff_update _ ag hρlim tendsto_const_nhds)
      (tendsto_mixedPayoff_update _ ag hρlim tendsto_const_nhds) fun n => hpay n ag b
  have hTHP : IsTHP (agentNF G) σ :=
    (proposition_8_F_1 _ hNash).2 ⟨ρ, fun n ag => ⟨hρmix n ag, hρpos n ag⟩, hρlim, hbr⟩
  refine ⟨isBehaviorProfile_pureMoves hc, σ, hTHP, fun k hk => ?_⟩
  obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.1 hk
  funext a
  rw [G.assemble_of_some _ hi]
  have h1 := assemble_agentProfile_apply G σ ⟨k, hk⟩ a
  rw [h1]
  split_ifs with ha
  · exact (hσval ⟨k, hk⟩ ⟨a, ha⟩).symm
  · have : a ≠ c k := fun h => ha (h ▸ hc k)
    simp [pureMoves, dirac, this]

/-- The trembles `ε n = 1/(n + 5)`. -/
noncomputable def fwdTremble (n : ℕ) : ℝ := 1 / ((n : ℝ) + 5)

theorem fwdTremble_pos (n : ℕ) : 0 < fwdTremble n := by
  unfold fwdTremble
  positivity

theorem fwdTremble_le (n : ℕ) : fwdTremble n ≤ 1 / 5 := by
  unfold fwdTremble
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]

theorem tendsto_fwdTremble : Tendsto fwdTremble atTop (𝓝 0) := by
  refine squeeze_zero (fun n => (fwdTremble_pos n).le) (fun n => ?_)
    tendsto_one_div_add_atTop_nhds_zero_nat
  unfold fwdTremble
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  linarith

/-- **Footnote 15** (MWG, p. 292). The weak PBE of Figure 9.D.1(a) (E out, I fights after
entry) is extensive form trembling-hand perfect. E trembles to In₁ with probability `ε` and to
In₂ with probability `ε²`, I accommodates with probability `ε`: fighting is then a best reply
of I (it is better at In₁, which is twice as likely as In₂ up to `ε ≤ 1/2`), and Out is a best
reply of E (In₁ gives `−3 + 4ε` and In₂ gives `−2 + 5ε`, both `≤ 0` for `ε ≤ 1/5`). -/
theorem footnote_15_D_1a_EFTHP : IsEFTHP fig9D1a (pureMoves ![0, 0]) := by
  set ε := fwdTremble
  have hε0 := fwdTremble_pos
  have hε1 := fwdTremble_le
  set Fs : ℕ → Fin 2 → Fin 2 → Fin 3 → ℝ := fun n _ k =>
    if k = 0 then ![1 - ε n - ε n ^ 2, ε n, ε n ^ 2] else ![1 - ε n, ε n, 0] with hFs
  have hc := entryTwo_cont ![0, 2] ![![![-3, -1], ![1, -2]], ![![-2, -1], ![3, 1]]]
  refine isEFTHP_pureMoves_of _ (entryTwo_noAbsentMindedness _ _)
    (fun k => by fin_cases k <;> simp [entryTwo]) Fs (fun n => ?_) ?_ ?_
  · have e0 := hε0 n
    have e1 := hε1 n
    refine ⟨fun i k hk => ?_, fun i k hk a ha => ?_⟩
    · obtain rfl : k = i := Option.some.inj hk
      fin_cases k
      · refine ⟨fun a => ?_, fun a ha => absurd (by simp [entryTwo]) ha, ?_⟩
        · fin_cases a <;> simp [hFs] <;> nlinarith
        · simp [hFs, entryTwo, Fin.sum_univ_three]
          ring
      · refine ⟨fun a => ?_, fun a ha => ?_, ?_⟩
        · fin_cases a <;> simp [hFs] <;> linarith
        · have : a = 2 := by
            fin_cases a <;> simp [entryTwo] at ha ⊢
          subst this
          simp [hFs]
        · simp [hFs, entryTwo]
    · obtain rfl : k = i := Option.some.inj hk
      fin_cases k
      · fin_cases a <;> simp [hFs] <;> nlinarith
      · fin_cases a <;> simp [hFs, entryTwo] at ha ⊢ <;> linarith
  · intro i k hk a
    obtain rfl : k = i := Option.some.inj hk
    have hsq : Tendsto (fun n => ε n ^ 2) atTop (𝓝 0) := by
      simpa using tendsto_fwdTremble.pow 2
    fin_cases k <;> fin_cases a
    · simpa [hFs, dirac] using
        ((tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_fwdTremble).sub hsq
    · simpa [hFs, dirac] using tendsto_fwdTremble
    · simpa [hFs, dirac] using hsq
    · simpa [hFs, dirac] using (tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_fwdTremble
    · simpa [hFs, dirac] using tendsto_fwdTremble
    · simp [hFs, dirac]
  · intro n i k hk b hb
    obtain rfl : k = i := Option.some.inj hk
    have e0 := hε0 n
    have e1 := hε1 n
    fin_cases k
    · rw [(hc _ _).2.2, (hc _ _).2.2]
      fin_cases b <;> simp [entryTwo_assemble, hFs, dirac] <;> nlinarith
    · rw [(hc _ _).2.2, (hc _ _).2.2]
      have : b = 0 ∨ b = 1 := by fin_cases b <;> simp [entryTwo] at hb ⊢
      rcases this with rfl | rfl
      · simp
      · simp [entryTwo_assemble, hFs, dirac]
        nlinarith

/-- **Footnote 15** (MWG, p. 292). The weak PBE of Figure 9.D.1(b) (E out, I targets the large
niche) is extensive form trembling-hand perfect. E trembles to the small niche with probability
`ε` and to the large niche with probability `ε²`, I targets the small niche with probability
`ε`: the large niche is then a best reply of I (`7ε − 2ε² ≥ 0`), and Out is a best reply of E
(the small niche gives `−1 − 5ε` and the large niche `−3 + 4ε`). -/
theorem footnote_15_D_1b_EFTHP : IsEFTHP fig9D1b (pureMoves ![0, 1]) := by
  set ε := fwdTremble
  have hε0 := fwdTremble_pos
  have hε1 := fwdTremble_le
  set Fs : ℕ → Fin 2 → Fin 2 → Fin 3 → ℝ := fun n _ k =>
    if k = 0 then ![1 - ε n - ε n ^ 2, ε n, ε n ^ 2] else ![ε n, 1 - ε n, 0] with hFs
  have hc := entryTwo_cont ![0, 2] ![![![-6, -6], ![-1, 1]], ![![1, -1], ![-3, -3]]]
  refine isEFTHP_pureMoves_of _ (entryTwo_noAbsentMindedness _ _)
    (fun k => by fin_cases k <;> simp [entryTwo]) Fs (fun n => ?_) ?_ ?_
  · have e0 := hε0 n
    have e1 := hε1 n
    refine ⟨fun i k hk => ?_, fun i k hk a ha => ?_⟩
    · obtain rfl : k = i := Option.some.inj hk
      fin_cases k
      · refine ⟨fun a => ?_, fun a ha => absurd (by simp [entryTwo]) ha, ?_⟩
        · fin_cases a <;> simp [hFs] <;> nlinarith
        · simp [hFs, entryTwo, Fin.sum_univ_three]
          ring
      · refine ⟨fun a => ?_, fun a ha => ?_, ?_⟩
        · fin_cases a <;> simp [hFs] <;> linarith
        · have : a = 2 := by
            fin_cases a <;> simp [entryTwo] at ha ⊢
          subst this
          simp [hFs]
        · simp [hFs, entryTwo]
    · obtain rfl : k = i := Option.some.inj hk
      fin_cases k
      · fin_cases a <;> simp [hFs] <;> nlinarith
      · fin_cases a <;> simp [hFs, entryTwo] at ha ⊢ <;> linarith
  · intro i k hk a
    obtain rfl : k = i := Option.some.inj hk
    have hsq : Tendsto (fun n => ε n ^ 2) atTop (𝓝 0) := by
      simpa using tendsto_fwdTremble.pow 2
    fin_cases k <;> fin_cases a
    · simpa [hFs, dirac] using
        ((tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_fwdTremble).sub hsq
    · simpa [hFs, dirac] using tendsto_fwdTremble
    · simpa [hFs, dirac] using hsq
    · simpa [hFs, dirac] using tendsto_fwdTremble
    · simpa [hFs, dirac] using (tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_fwdTremble
    · simp [hFs, dirac]
  · intro n i k hk b hb
    obtain rfl : k = i := Option.some.inj hk
    have e0 := hε0 n
    have e1 := hε1 n
    fin_cases k
    · rw [(hc _ _).2.2, (hc _ _).2.2]
      fin_cases b <;> simp [entryTwo_assemble, hFs, dirac] <;> nlinarith
    · rw [(hc _ _).2.2, (hc _ _).2.2]
      have : b = 0 ∨ b = 1 := by fin_cases b <;> simp [entryTwo] at hb ⊢
      rcases this with rfl | rfl
      · simp [entryTwo_assemble, hFs, dirac]
        nlinarith
      · simp

/-- **Footnote 15** (MWG, p. 292), for **Figure 9.D.2** (p. 294). The weak PBE of Figure 9.D.2
(E out, I plays `R` after "out" and the large niche after entry) is extensive form
trembling-hand perfect. E trembles to the small niche with probability `ε` and to the large
niche with probability `ε²`; each agent of I plays its other action with probability `ε`. Out
gives E `−10ε`, the small niche `−1 − 5ε` and the large niche `−3 + 4ε`, so Out is a best reply
for `ε ≤ 1/5`. -/
theorem footnote_15_D_2_EFTHP : IsEFTHP fig9D2 (pureMoves ![0, 1, 1]) := by
  set ε := fwdTremble
  have hε0 := fwdTremble_pos
  have hε1 := fwdTremble_le
  set Fs : ℕ → Fin 2 → Fin 3 → Fin 3 → ℝ := fun n _ k =>
    if k = 0 then ![1 - ε n - ε n ^ 2, ε n, ε n ^ 2] else ![ε n, 1 - ε n, 0] with hFs
  have hc := fig9D2_cont
  have hNA : fig9D2.NoAbsentMindedness := by
    unfold ExtensiveForm.NoAbsentMindedness
    decide
  refine isEFTHP_pureMoves_of _ hNA
    (fun k => by fin_cases k <;> simp [fig9D2]) Fs (fun n => ?_) ?_ ?_
  · have e0 := hε0 n
    have e1 := hε1 n
    refine ⟨fun i k hk => ?_, fun i k hk a ha => ?_⟩
    · fin_cases k
      · refine ⟨fun a => ?_, fun a ha => absurd (by simp [fig9D2]) ha, ?_⟩
        · fin_cases a <;> simp [hFs] <;> nlinarith
        · simp [hFs, fig9D2, Fin.sum_univ_three]
          ring
      all_goals
        refine ⟨fun a => ?_, fun a ha => ?_, ?_⟩
        · fin_cases a <;> simp [hFs] <;> linarith
        · have : a = 2 := by
            fin_cases a <;> simp [fig9D2] at ha ⊢
          subst this
          simp [hFs]
        · simp [hFs, fig9D2]
    · fin_cases k
      · fin_cases a <;> simp [hFs] <;> nlinarith
      all_goals fin_cases a <;> simp [hFs, fig9D2] at ha ⊢ <;> linarith
  · intro i k hk a
    have hsq : Tendsto (fun n => ε n ^ 2) atTop (𝓝 0) := by
      simpa using tendsto_fwdTremble.pow 2
    fin_cases k <;> fin_cases a
    · simpa [hFs, dirac] using
        ((tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_fwdTremble).sub hsq
    · simpa [hFs, dirac] using tendsto_fwdTremble
    · simpa [hFs, dirac] using hsq
    · simpa [hFs, dirac] using tendsto_fwdTremble
    · simpa [hFs, dirac] using (tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_fwdTremble
    · simp [hFs, dirac]
    · simpa [hFs, dirac] using tendsto_fwdTremble
    · simpa [hFs, dirac] using (tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_fwdTremble
    · simp [hFs, dirac]
  · intro n i k hk b hb
    have e0 := hε0 n
    have e1 := hε1 n
    fin_cases k
    · obtain rfl : i = 0 := (Option.some.inj (hk : some 0 = some i)).symm
      rw [(hc _ _).2.2.2, (hc _ _).2.2.2]
      fin_cases b <;> simp [fig9D2_assemble, hFs, dirac] <;> nlinarith
    all_goals
      obtain rfl : i = 1 := (Option.some.inj (hk : some 1 = some i)).symm
      rw [(hc _ _).2.2.2, (hc _ _).2.2.2]
      have : b = 0 ∨ b = 1 := by fin_cases b <;> simp [fig9D2] at hb ⊢
      rcases this with rfl | rfl
      · simp [fig9D2_assemble, hFs, dirac]
        nlinarith
      · simp

end MWG.DynamicGames

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercise 9.C.3(b) with a general lower bound `v̲ ≥ 0`

MWG, Exercise 9.C.3(b) (p. 304) and Exercise 9.C.6 for it: the buyer's value is uniform on
`[v̲, v̄]` with `0 ≤ v̲ < v̄` (written `vl`, `vh`), the discount factor is `δ ∈ (0, 1)`.

The reduced model is that of `SellerBuyer.lean` (where `v̲ = 0`, `v̄ = 1`), with the prior's
mass of `[k, v̄]` equal to `(v̄ − k)/(v̄ − v̲)`. The seller's payoffs are multiplied by
`v̄ − v̲ > 0` and her period-2 revenue for the posterior uniform on `[v̲, k)` by `k − v̲ > 0`;
this changes no comparison. `sbgCut` is the cutoff `κ` of `exercise_9_C_3b_cutoff` clamped to
`[v̲, v̄]`, `sbgPay` the seller's payoff, `sbgRev` the period-2 revenue, `IsSBGWeakPBE` and
`IsSBGConsistent` the weak PBE and consistency conditions (`isSBGWeakPBE_zero_one_iff`: for
`v̲ = 0`, `v̄ = 1` they are those of `SellerBuyer.lean`).

* `sbgRev_opt_iff`: for the posterior uniform on `[v̲, k)` the unique optimal second price is
  `max (v̲, k/2)`: the **corner** `v̲` when `k ≤ 2v̲`.
* `sbg_consistent`: with consistent beliefs, after every price `p > v̲` the cutoff is
  `K(p) = min ((p − δv̲)/(1 − δ), 2p/(2 − δ), v̄)` and the second price `max (v̲, K(p)/2)`.
* `exercise_9_C_3b_general`: the characterisation of the weak PBE with consistent beliefs.
  With `G_C = (1 − δ) v̄²/4 + δ v̲ v̄ − δ v̲²` (corner value) and `G_I = (2 − δ)² v̄²/(4 (4 − 3δ))`
  (interior value): (i) if `v̄ ≤ 2v̲` the first price is `v̲` and every type buys at once;
  (ii) if `2v̲ < v̄` and `G_C ≤ G_I` the first price is `(2 − δ)² v̄/(2 (4 − 3δ))`, the cutoff
  `k* = (2 − δ) v̄/(4 − 3δ)` and the second price `k*/2`; (iii) if `2v̲ < v̄` and `G_I ≤ G_C` the
  first price is `(1 − δ) v̄/2 + δ v̲`, the cutoff `v̄/2` and the second price is the corner
  `v̲`. `sbgGI_sub_sbgGC`: `G_I − G_C = δ (v̲² − v̲ v̄ + (3 − 2δ) v̄²/(4 (4 − 3δ)))`.
  `exercise_9_C_3b_general_outcomes`, `exercise_9_C_3b_general_exists`, and the instances
  `exercise_9_C_3b_general_examples` (one per case).
-/

namespace MWG.DynamicGames

/-- The cutoff clamped to `[v̲, v̄]`: the types in `[v̲, k)` reject the first price `p` when they
expect the second price `r`. -/
noncomputable def sbgCut (vl vh δ p r : ℝ) : ℝ := max vl (min (sbKappa δ p r) vh)

/-- The seller's payoff (times `v̄ − v̲`) from the first price `p` and second price `q` when the
buyer expects the second price `r`: the types `[k, v̄]` buy at `p`, the types in `[max q v̲, k)`
buy at `q` in period 2. -/
noncomputable def sbgPay (vl vh δ p r q : ℝ) : ℝ :=
  p * (vh - sbgCut vl vh δ p r) + δ * q * max 0 (sbgCut vl vh δ p r - max q vl)

/-- The seller's period-2 revenue at price `q` (times `k − v̲`) for the belief uniform on
`[v̲, k)`. -/
noncomputable def sbgRev (vl k q : ℝ) : ℝ := q * max 0 (k - max q vl)

/-- **Exercise 9.C.3(b)** (MWG, p. 304), values uniform on `[v̲, v̄]`. A pure-strategy weak PBE in
reduced form: second prices `r p ∈ [v̲, v̄]` after every rejected price (each optimal for the
belief concentrated on `v = r p`), optimal for the Bayes posterior after `p1` if some types
reject it, and `p1` optimal against every deviation `(p, q)`. -/
def IsSBGWeakPBE (vl vh δ p1 : ℝ) (r : ℝ → ℝ) : Prop :=
  (∀ p, vl ≤ r p ∧ r p ≤ vh) ∧
  (vl < sbgCut vl vh δ p1 (r p1) → ∀ q, sbgRev vl (sbgCut vl vh δ p1 (r p1)) q ≤
    sbgRev vl (sbgCut vl vh δ p1 (r p1)) (r p1)) ∧
  ∀ p q, sbgPay vl vh δ p (r p) q ≤ sbgPay vl vh δ p1 (r p1) (r p1)

/-- **Exercise 9.C.6 for 9.C.3(b)** (MWG, p. 304). Structural consistency: after every price that
a positive mass of types rejects, the second price is optimal for the Bayes posterior. -/
def IsSBGConsistent (vl vh δ : ℝ) (r : ℝ → ℝ) : Prop :=
  ∀ p, vl < sbgCut vl vh δ p (r p) → ∀ q, sbgRev vl (sbgCut vl vh δ p (r p)) q ≤
    sbgRev vl (sbgCut vl vh δ p (r p)) (r p)

/-- The consistent cutoff after the first price `p > v̲`. -/
noncomputable def sbgK (vl vh δ p : ℝ) : ℝ :=
  min (min ((p - δ * vl) / (1 - δ)) (2 * p / (2 - δ))) vh

/-- The consistent second price after the first price `p > v̲`. -/
noncomputable def sbgR (vl vh δ p : ℝ) : ℝ := max vl (sbgK vl vh δ p / 2)

/-- The first price whose consistent cutoff is `k` (the inverse of `sbgK` on `[v̲, v̄]`). -/
noncomputable def sbgPhi (vl δ k : ℝ) : ℝ := max ((1 - δ) * k + δ * vl) ((2 - δ) * k / 2)

/-- The seller's maximal period-2 revenue (times `k − v̲`) for the belief uniform on `[v̲, k)`. -/
noncomputable def sbgMaxRev (vl k : ℝ) : ℝ := if 2 * vl ≤ k then k ^ 2 / 4 else vl * (k - vl)

/-- The seller's payoff when the consistent cutoff is `k`. -/
noncomputable def sbgVal (vl vh δ k : ℝ) : ℝ := sbgPhi vl δ k * (vh - k) + δ * sbgMaxRev vl k

/-- The payoff for cutoff `k` when the second price is interior (`k ≥ 2v̲`). -/
noncomputable def sbgGIk (vh δ k : ℝ) : ℝ := (2 - δ) * vh * k / 2 - (4 - 3 * δ) * k ^ 2 / 4

/-- The payoff for cutoff `k` when the second price is the corner `v̲` (`k ≤ 2v̲`). -/
noncomputable def sbgGCk (vl vh δ k : ℝ) : ℝ :=
  ((1 - δ) * k + δ * vl) * (vh - k) + δ * vl * (k - vl)

/-- The interior cutoff `k* = (2 − δ) v̄/(4 − 3δ)`. -/
noncomputable def sbgKI (vh δ : ℝ) : ℝ := (2 - δ) * vh / (4 - 3 * δ)

/-- The interior value `G_I`. -/
noncomputable def sbgGI (vh δ : ℝ) : ℝ := sbgGIk vh δ (sbgKI vh δ)

/-- The corner value `G_C` (cutoff `v̄/2`). -/
noncomputable def sbgGC (vl vh δ : ℝ) : ℝ := sbgGCk vl vh δ (vh / 2)

/-- The interior first price `(2 − δ)² v̄/(2 (4 − 3δ))`. -/
noncomputable def sbgPI (vh δ : ℝ) : ℝ := (2 - δ) ^ 2 * vh / (2 * (4 - 3 * δ))

/-- The corner first price `(1 − δ) v̄/2 + δ v̲`. -/
noncomputable def sbgPC (vl vh δ : ℝ) : ℝ := (1 - δ) * vh / 2 + δ * vl

variable {vl vh δ : ℝ}

/-- The period-2 revenue is at most `sbgMaxRev`. -/
theorem sbgRev_le (hvl : 0 ≤ vl) {k : ℝ} (hk : vl ≤ k) (q : ℝ) :
    sbgRev vl k q ≤ sbgMaxRev vl k := by
  unfold sbgRev sbgMaxRev
  rcases le_total q vl with hq | hq
  · rw [max_eq_right hq, max_eq_right (by linarith : (0 : ℝ) ≤ k - vl)]
    have h1 := mul_nonneg (sub_nonneg.2 hq) (sub_nonneg.2 hk)
    split_ifs with h
    · nlinarith [sq_nonneg (k - 2 * vl)]
    · nlinarith
  · rw [max_eq_left hq]
    rcases le_total (k - q) 0 with h1 | h1
    · rw [max_eq_left h1, mul_zero]
      split_ifs
      · positivity
      · exact mul_nonneg hvl (by linarith)
    · rw [max_eq_right h1]
      split_ifs with h
      · nlinarith [sq_nonneg (q - k / 2)]
      · nlinarith [mul_nonneg (sub_nonneg.2 hq) (by linarith : (0 : ℝ) ≤ q + vl - k)]

/-- The revenue at `max (v̲, k/2)` is `sbgMaxRev`. -/
theorem sbgRev_opt_val (hvl : 0 ≤ vl) {k : ℝ} (hk : vl ≤ k) :
    sbgRev vl k (max vl (k / 2)) = sbgMaxRev vl k := by
  unfold sbgRev sbgMaxRev
  split_ifs with h
  · rw [max_eq_right (by linarith : vl ≤ k / 2), max_eq_left (by linarith : vl ≤ k / 2),
      max_eq_right (by linarith : (0 : ℝ) ≤ k - k / 2)]
    ring
  · rw [max_eq_left (by linarith : k / 2 ≤ vl), max_self, max_eq_right (by linarith)]

/-- **Exercise 9.C.3(b), the second price** (MWG, p. 304). For the belief uniform on `[v̲, k)`,
`v̲ < k`, the unique optimal second price is `max (v̲, k/2)`: the corner `v̲` when `k ≤ 2v̲`. -/
theorem sbgRev_opt_iff (hvl : 0 ≤ vl) {k : ℝ} (hk : vl < k) (r : ℝ) :
    (∀ q, sbgRev vl k q ≤ sbgRev vl k r) ↔ r = max vl (k / 2) := by
  constructor
  · intro h
    have h1 := h (max vl (k / 2))
    rw [sbgRev_opt_val hvl hk.le] at h1
    unfold sbgRev sbgMaxRev at h1
    split_ifs at h1 with h2
    · rw [max_eq_right (by linarith : vl ≤ k / 2)]
      rcases le_total r vl with hr | hr
      · rw [max_eq_right hr, max_eq_right (by linarith : (0 : ℝ) ≤ k - vl)] at h1
        have h3 : (k - 2 * vl) ^ 2 ≤ 0 := by
          nlinarith [mul_nonneg (sub_nonneg.2 hr) (sub_nonneg.2 hk.le)]
        have h4 : k = 2 * vl := by
          have := le_antisymm h3 (sq_nonneg _)
          have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
          linarith
        subst h4
        nlinarith
      · rw [max_eq_left hr] at h1
        rcases le_total (k - r) 0 with h5 | h5
        · rw [max_eq_left h5] at h1
          nlinarith
        · rw [max_eq_right h5] at h1
          have h6 : (r - k / 2) ^ 2 ≤ 0 := by nlinarith
          have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm h6 (sq_nonneg _))
          linarith
    · rw [max_eq_left (by linarith : k / 2 ≤ vl)]
      have hvl0 : 0 < vl := by linarith
      rcases le_total r vl with hr | hr
      · rw [max_eq_right hr, max_eq_right (by linarith : (0 : ℝ) ≤ k - vl)] at h1
        have : vl ≤ r := by nlinarith
        linarith
      · rcases hr.eq_or_lt with h6 | h6
        · exact h6.symm
        exfalso
        rw [max_eq_left hr] at h1
        rcases le_total (k - r) 0 with h5 | h5
        · rw [max_eq_left h5] at h1
          nlinarith
        · rw [max_eq_right h5] at h1
          nlinarith [mul_pos (sub_pos.2 h6) (by linarith : (0 : ℝ) < r + vl - k)]
  · rintro rfl q
    rw [sbgRev_opt_val hvl hk.le]
    exact sbgRev_le hvl hk.le q

/-- After a first price `p ≤ v̲`, if the expected second price is at least `v̲`, every type
buys at once. -/
theorem sbgCut_of_le (hd0 : 0 < δ) (hd1 : δ < 1) {p r : ℝ} (hp : p ≤ vl)
    (hr : vl ≤ r) : sbgCut vl vh δ p r = vl := by
  have hκ : sbKappa δ p r ≤ vl := by
    unfold sbKappa
    split_ifs
    · rw [div_le_iff₀ (by linarith)]
      nlinarith
    · exact hp
  unfold sbgCut
  exact max_eq_left ((min_le_left _ _).trans hκ)

/-- After a first price `p > v̲` some types reject, whatever second price they expect. -/
theorem sbgCut_gt (hlh : vl < vh) (hd0 : 0 < δ) (hd1 : δ < 1) {p : ℝ} (hp : vl < p)
    (r : ℝ) : vl < sbgCut vl vh δ p r := by
  have hκ : p ≤ sbKappa δ p r := by
    unfold sbKappa
    split_ifs
    · rw [le_div_iff₀ (by linarith)]
      nlinarith
    · exact le_rfl
  unfold sbgCut
  exact lt_max_of_lt_right (lt_min (hp.trans_le hκ) hlh)

/-- **Exercise 9.C.3(b), consistent continuation** (MWG, p. 304). With consistent beliefs, after
every first price `p > v̲` the second price is `sbgR p = max (v̲, K(p)/2)` and the cutoff is
`K(p) = min ((p − δv̲)/(1 − δ), 2p/(2 − δ), v̄)`. -/
theorem sbg_consistent (hvl : 0 ≤ vl) (hlh : vl < vh) (hd0 : 0 < δ) (hd1 : δ < 1)
    {r : ℝ → ℝ} (hc : IsSBGConsistent vl vh δ r) {p : ℝ} (hp : vl < p) :
    r p = sbgR vl vh δ p ∧ sbgCut vl vh δ p (r p) = sbgK vl vh δ p := by
  have h1 : 0 < 1 - δ := by linarith
  have h2 : 0 < 2 - δ := by linarith
  set k := sbgCut vl vh δ p (r p) with hkdef
  have hk := sbgCut_gt hlh hd0 hd1 hp (r p)
  rw [← hkdef] at hk
  have hr := (sbgRev_opt_iff hvl hk (r p)).1 (hc p hk)
  have hrvl : vl ≤ r p := hr ▸ le_max_left _ _
  have hrk : k / 2 ≤ r p := hr ▸ le_max_right _ _
  have hkle : k = min (sbKappa δ p (r p)) vh := by
    rw [hkdef, sbgCut]
    refine max_eq_right ?_
    by_contra hn
    have : sbgCut vl vh δ p (r p) = vl := max_eq_left (le_of_not_ge hn)
    rw [← hkdef] at this
    linarith
  have hrp : r p ≤ p := by
    by_contra hn
    have hκ : sbKappa δ p (r p) = p := by simp [sbKappa, hn]
    rw [hκ] at hkle
    have hkp : k ≤ p := hkle ▸ min_le_left _ _
    rcases max_choice vl (k / 2) with h | h
    · rw [h] at hr; linarith
    · rw [h] at hr; linarith
  have hκ : sbKappa δ p (r p) * (1 - δ) = p - δ * r p := by
    simp only [sbKappa, hrp, ↓reduceIte]
    field_simp
  have hKk : k = sbgK vl vh δ p := by
    refine le_antisymm ?_ ?_
    · have hkκ : k ≤ sbKappa δ p (r p) := hkle ▸ min_le_left _ _
      refine le_min (le_min ?_ ?_) (hkle ▸ min_le_right _ _)
      · rw [le_div_iff₀ h1]
        nlinarith
      · rw [le_div_iff₀ h2]
        nlinarith
    · rcases min_choice (sbKappa δ p (r p)) vh with h | h
      · rw [h] at hkle
        rcases max_choice vl (k / 2) with h' | h'
        · rw [h'] at hr
          refine (min_le_left _ _).trans ((min_le_left _ _).trans (le_of_eq ?_))
          rw [div_eq_iff h1.ne', hkle, hκ, hr]
        · rw [h'] at hr
          refine (min_le_left _ _).trans ((min_le_right _ _).trans (le_of_eq ?_))
          rw [div_eq_iff h2.ne']
          have e : sbKappa δ p (r p) * (1 - δ) = p - δ * (k / 2) := by rw [hκ, hr]
          rw [← hkle] at e
          linear_combination (-2) * e
      · rw [h] at hkle
        rw [hkle]
        exact min_le_right _ _
  exact ⟨by rw [hr, hKk, sbgR], hKk⟩

/-- The consistent cutoff after `p > v̲` lies in `(v̲, v̄]`. -/
theorem sbgK_mem (hvl : 0 ≤ vl) (hlh : vl < vh) (hd0 : 0 < δ) (hd1 : δ < 1) {p : ℝ}
    (hp : vl < p) : vl < sbgK vl vh δ p ∧ sbgK vl vh δ p ≤ vh := by
  have h1 : 0 < 1 - δ := by linarith
  have h2 : 0 < 2 - δ := by linarith
  refine ⟨lt_min (lt_min ?_ ?_) hlh, min_le_right _ _⟩
  · rw [lt_div_iff₀ h1]; nlinarith
  · rw [lt_div_iff₀ h2]; nlinarith

/-- The price `sbgPhi k` has consistent cutoff `k`. -/
theorem sbgK_phi (hd0 : 0 < δ) (hd1 : δ < 1) {k : ℝ} (hkh : k ≤ vh) :
    sbgK vl vh δ (sbgPhi vl δ k) = k := by
  have h1 : 0 < 1 - δ := by linarith
  have h2 : 0 < 2 - δ := by linarith
  unfold sbgK sbgPhi
  set m := max ((1 - δ) * k + δ * vl) ((2 - δ) * k / 2) with hm
  have hA : k ≤ (m - δ * vl) / (1 - δ) := by
    rw [le_div_iff₀ h1]; linarith [le_max_left ((1 - δ) * k + δ * vl) ((2 - δ) * k / 2)]
  have hB : k ≤ 2 * m / (2 - δ) := by
    rw [le_div_iff₀ h2]; linarith [le_max_right ((1 - δ) * k + δ * vl) ((2 - δ) * k / 2)]
  have hmin : min ((m - δ * vl) / (1 - δ)) (2 * m / (2 - δ)) = k := by
    refine le_antisymm ?_ (le_min hA hB)
    rcases max_choice ((1 - δ) * k + δ * vl) ((2 - δ) * k / 2) with h | h
    · refine (min_le_left _ _).trans (le_of_eq ?_)
      rw [hm, h, div_eq_iff h1.ne']
      ring
    · refine (min_le_right _ _).trans (le_of_eq ?_)
      rw [hm, h, div_eq_iff h2.ne']
      ring
  rw [hmin, min_eq_left hkh]

/-- When the consistent cutoff after `p` is below `v̄`, `p = sbgPhi (K(p))`. -/
theorem sbgPhi_K (hd0 : 0 < δ) (hd1 : δ < 1) {p : ℝ} (hK : sbgK vl vh δ p < vh) :
    sbgPhi vl δ (sbgK vl vh δ p) = p := by
  have h1 : 0 < 1 - δ := by linarith
  have h2 : 0 < 2 - δ := by linarith
  set A := (p - δ * vl) / (1 - δ) with hA
  set B := 2 * p / (2 - δ) with hB
  have hA' : A * (1 - δ) = p - δ * vl := by rw [hA]; field_simp
  have hB' : B * (2 - δ) = 2 * p := by rw [hB]; field_simp
  have hKe : sbgK vl vh δ p = min A B := by
    unfold sbgK at hK ⊢
    exact min_eq_left (le_of_lt (by
      rcases min_choice (min A B) vh with h | h
      · rw [h] at hK; exact hK
      · rw [h] at hK; exact absurd hK (lt_irrefl _)))
  rw [hKe]
  unfold sbgPhi
  have hle1 : (1 - δ) * min A B + δ * vl ≤ p := by
    nlinarith [mul_le_mul_of_nonneg_left (min_le_left A B) h1.le]
  have hle2 : (2 - δ) * min A B / 2 ≤ p := by
    nlinarith [mul_le_mul_of_nonneg_left (min_le_right A B) h2.le]
  refine le_antisymm (max_le hle1 hle2) ?_
  rcases min_choice A B with h | h
  · rw [h]; exact le_max_of_le_left (by linarith)
  · rw [h]; exact le_max_of_le_right (by linarith)

/-- The consistent second price yields the consistent cutoff. -/
theorem sbgCut_R (hvl : 0 ≤ vl) (hlh : vl < vh) (hd0 : 0 < δ) (hd1 : δ < 1) {p : ℝ}
    (hp : vl < p) : sbgCut vl vh δ p (sbgR vl vh δ p) = sbgK vl vh δ p := by
  have h1 : 0 < 1 - δ := by linarith
  have h2 : 0 < 2 - δ := by linarith
  obtain ⟨hK0, hK1⟩ := sbgK_mem hvl hlh hd0 hd1 hp
  set K := sbgK vl vh δ p with hKdef
  set A := (p - δ * vl) / (1 - δ) with hA
  set B := 2 * p / (2 - δ) with hB
  have hA' : A * (1 - δ) = p - δ * vl := by rw [hA]; field_simp
  have hB' : B * (2 - δ) = 2 * p := by rw [hB]; field_simp
  have hKAB : K = min (min A B) vh := rfl
  have hKB : K ≤ B := hKAB ▸ (min_le_left _ _).trans (min_le_right _ _)
  have hKA : K ≤ A := hKAB ▸ (min_le_left _ _).trans (min_le_left _ _)
  have hRp : sbgR vl vh δ p ≤ p := by
    unfold sbgR
    refine max_le hp.le ?_
    rw [← hKdef]
    nlinarith
  have hκ : sbKappa δ p (sbgR vl vh δ p) * (1 - δ) = p - δ * sbgR vl vh δ p := by
    simp only [sbKappa, hRp, ↓reduceIte]
    field_simp
  -- `κ = K` when `K < v̄`, `κ ≥ v̄` otherwise
  have hmain : min (sbKappa δ p (sbgR vl vh δ p)) vh = K := by
    rcases le_total (min A B) vh with hc | hc
    · have hKe : K = min A B := by rw [hKAB]; exact min_eq_left hc
      have hκK : sbKappa δ p (sbgR vl vh δ p) = K := by
        rcases min_choice A B with h | h
        · rw [h] at hKe
          -- `A ≤ B` gives `K ≤ 2 v̲`, so the second price is `v̲`
          have hAB : A ≤ B := h ▸ min_le_right A B
          have hK2 : K ≤ 2 * vl := by nlinarith
          have hR : sbgR vl vh δ p = vl := by
            unfold sbgR; rw [← hKdef]; exact max_eq_left (by linarith)
          refine mul_right_cancel₀ h1.ne' (hκ.trans ?_)
          rw [hR, hKe, hA']
        · rw [h] at hKe
          have hBA : B ≤ A := h ▸ min_le_left A B
          have hK2 : 2 * vl ≤ K := by nlinarith
          have hR : sbgR vl vh δ p = K / 2 := by
            unfold sbgR; rw [← hKdef]; exact max_eq_right (by linarith)
          refine mul_right_cancel₀ h1.ne' (hκ.trans ?_)
          rw [hR, hKe, hB]
          field_simp
          ring
      rw [hκK]
      exact min_eq_left hK1
    · have hKe : K = vh := by rw [hKAB]; exact min_eq_right hc
      have hAv : vh ≤ A := hc.trans (min_le_left _ _)
      have hBv : vh ≤ B := hc.trans (min_le_right _ _)
      rw [hKe]
      refine min_eq_right (le_of_mul_le_mul_right ?_ h1)
      rw [hκ]
      unfold sbgR
      rw [← hKdef, hKe]
      rcases max_choice vl (vh / 2) with h | h
      · rw [h]; nlinarith
      · rw [h]; nlinarith
  unfold sbgCut
  rw [hmain]
  exact max_eq_right hK0.le

/-- The seller's optimal value: `v̲ (v̄ − v̲)` if `v̄ ≤ 2v̲`, otherwise `max (G_I, G_C)`. -/
noncomputable def sbgOpt (vl vh δ : ℝ) : ℝ :=
  if vh ≤ 2 * vl then vl * (vh - vl) else max (sbgGI vh δ) (sbgGC vl vh δ)

/-- For `k ≤ 2v̲` the second price is the corner `v̲` and the payoff is `G_C(k)`. -/
theorem sbgVal_corner (hd0 : 0 < δ) {k : ℝ} (hk : k ≤ 2 * vl) :
    sbgVal vl vh δ k = sbgGCk vl vh δ k := by
  unfold sbgVal sbgPhi sbgMaxRev sbgGCk
  rw [max_eq_left (by nlinarith [mul_le_mul_of_nonneg_left hk hd0.le])]
  split_ifs with h
  · have : k = 2 * vl := le_antisymm hk h
    subst this
    ring
  · ring

/-- For `k ≥ 2v̲` the second price is `k/2` and the payoff is `G_I(k)`. -/
theorem sbgVal_interior (hd0 : 0 < δ) {k : ℝ} (hk : 2 * vl ≤ k) :
    sbgVal vl vh δ k = sbgGIk vh δ k := by
  unfold sbgVal sbgPhi sbgMaxRev sbgGIk
  rw [max_eq_right (by nlinarith [mul_le_mul_of_nonneg_left hk hd0.le])]
  simp only [hk, ↓reduceIte]
  ring

/-- `G_C − G_C(k) = (1 − δ) (k − v̄/2)²`. -/
theorem sbgGC_sub (k : ℝ) :
    sbgGC vl vh δ - sbgGCk vl vh δ k = (1 - δ) * (k - vh / 2) ^ 2 := by
  unfold sbgGC sbgGCk
  ring

/-- `G_I − G_I(k) = (4 − 3δ)/4 · (k − k*)²`. -/
theorem sbgGI_sub (hd1 : δ < 1) (k : ℝ) :
    sbgGI vh δ - sbgGIk vh δ k = (4 - 3 * δ) / 4 * (k - sbgKI vh δ) ^ 2 := by
  have h : (4 - 3 * δ) ≠ 0 := (by linarith : (0 : ℝ) < 4 - 3 * δ).ne'
  have hK : sbgKI vh δ * (4 - 3 * δ) = (2 - δ) * vh := div_mul_cancel₀ _ h
  unfold sbgGI sbgGIk
  linear_combination (-(sbgKI vh δ - k) / 2) * hK

/-- `G_I(k) − G_C(k) = δ (k/2 − v̲) (v̄ − k/2 − v̲)`. -/
theorem sbgGIk_sub_sbgGCk (k : ℝ) :
    sbgGIk vh δ k - sbgGCk vl vh δ k = δ * (k / 2 - vl) * (vh - k / 2 - vl) := by
  unfold sbgGIk sbgGCk
  ring

/-- **Exercise 9.C.3(b), the comparison** (MWG, p. 304).
`4 (4 − 3δ) (G_I − G_C) = δ (4 (4 − 3δ) (v̲² − v̲ v̄) + (3 − 2δ) v̄²)`: the interior solution is
better iff `v̲² − v̲ v̄ + (3 − 2δ) v̄²/(4 (4 − 3δ)) > 0`. -/
theorem sbgGI_sub_sbgGC (hd1 : δ < 1) :
    4 * (4 - 3 * δ) * (sbgGI vh δ - sbgGC vl vh δ) =
      δ * (4 * (4 - 3 * δ) * (vl ^ 2 - vl * vh) + (3 - 2 * δ) * vh ^ 2) := by
  have h : (4 - 3 * δ) ≠ 0 := (by linarith : (0 : ℝ) < 4 - 3 * δ).ne'
  have hK : sbgKI vh δ * (4 - 3 * δ) = (2 - δ) * vh := div_mul_cancel₀ _ h
  unfold sbgGI sbgGIk sbgGC sbgGCk
  linear_combination ((2 - δ) * vh - sbgKI vh δ * (4 - 3 * δ)) * hK

/-- Every consistent payoff is at most `sbgOpt`. -/
theorem sbgVal_le_opt (hd0 : 0 < δ) (hd1 : δ < 1) {k : ℝ} (hk0 : vl ≤ k)
    (hk1 : k ≤ vh) : sbgVal vl vh δ k ≤ sbgOpt vl vh δ := by
  have h1 : 0 < 1 - δ := by linarith
  unfold sbgOpt
  split_ifs with h
  · rw [sbgVal_corner hd0 (by linarith)]
    unfold sbgGCk
    nlinarith [mul_nonneg h1.le (mul_nonneg (sub_nonneg.2 hk0)
      (by linarith : (0 : ℝ) ≤ k + vl - vh))]
  · rcases le_total k (2 * vl) with hk | hk
    · rw [sbgVal_corner hd0 hk]
      have := sbgGC_sub (vl := vl) (vh := vh) (δ := δ) k
      exact le_max_of_le_right (by nlinarith [sq_nonneg (k - vh / 2)])
    · rw [sbgVal_interior hd0 hk]
      have := sbgGI_sub (vh := vh) hd1 k
      have h43 : 0 < 4 - 3 * δ := by linarith
      exact le_max_of_le_left (by nlinarith [mul_nonneg h43.le (sq_nonneg (k - sbgKI vh δ))])

/-- After a first price `p ≤ v̲` (and a second price `r ≥ v̲`) the seller earns `p (v̄ − v̲)`. -/
theorem sbgPay_low (hd0 : 0 < δ) (hd1 : δ < 1) {p r : ℝ} (hp : p ≤ vl) (hr : vl ≤ r)
    (q : ℝ) : sbgPay vl vh δ p r q = p * (vh - vl) := by
  unfold sbgPay
  rw [sbgCut_of_le hd0 hd1 hp hr, max_eq_left (by linarith [le_max_right q vl])]
  ring

/-- After a first price `p > v̲` with the consistent continuation, the seller earns at most
`sbgVal (K(p))`, with equality at the consistent second price. -/
theorem sbgPay_cons (hvl : 0 ≤ vl) (hlh : vl < vh) (hd0 : 0 < δ) (hd1 : δ < 1) {p : ℝ}
    (hp : vl < p) (q : ℝ) :
    sbgPay vl vh δ p (sbgR vl vh δ p) q ≤ sbgVal vl vh δ (sbgK vl vh δ p) ∧
      sbgPay vl vh δ p (sbgR vl vh δ p) (sbgR vl vh δ p) = sbgVal vl vh δ (sbgK vl vh δ p) := by
  obtain ⟨hK0, hK1⟩ := sbgK_mem hvl hlh hd0 hd1 hp
  have hcut := sbgCut_R hvl hlh hd0 hd1 hp
  set K := sbgK vl vh δ p with hK
  have hpk : p * (vh - K) = sbgPhi vl δ K * (vh - K) := by
    rcases hK1.lt_or_eq with h | h
    · rw [sbgPhi_K hd0 hd1 h]
    · rw [h, sub_self, mul_zero, mul_zero]
  have e : ∀ q, sbgPay vl vh δ p (sbgR vl vh δ p) q = p * (vh - K) + δ * sbgRev vl K q := by
    intro q
    unfold sbgPay sbgRev
    rw [hcut]
    ring
  have hR : sbgR vl vh δ p = max vl (K / 2) := rfl
  unfold sbgVal
  refine ⟨?_, ?_⟩
  · rw [e, hpk]
    nlinarith [sbgRev_le hvl hK0.le q]
  · rw [e, hpk, hR, sbgRev_opt_val hvl hK0.le]

/-- The candidate first prices: `sbgPI = sbgPhi k*` (if `2v̲ ≤ k*`) and `sbgPC = sbgPhi (v̄/2)`
(if `v̄/2 ≤ 2v̲`). -/
theorem sbgPhi_cand (hd0 : 0 < δ) (hd1 : δ < 1) :
    (2 * vl ≤ sbgKI vh δ → sbgPhi vl δ (sbgKI vh δ) = sbgPI vh δ) ∧
    (vh / 2 ≤ 2 * vl → sbgPhi vl δ (vh / 2) = sbgPC vl vh δ) := by
  have h43 : (4 - 3 * δ) ≠ 0 := (by linarith : (0 : ℝ) < 4 - 3 * δ).ne'
  refine ⟨fun h => ?_, fun h => ?_⟩
  · unfold sbgPhi
    rw [max_eq_right (by nlinarith [mul_le_mul_of_nonneg_left h hd0.le])]
    unfold sbgKI sbgPI
    field_simp
  · unfold sbgPhi
    rw [max_eq_left (by nlinarith [mul_le_mul_of_nonneg_left h hd0.le])]
    unfold sbgPC
    ring

/-- If `2v̲ < v̄` and `G_C ≤ G_I` the interior cutoff satisfies `2v̲ ≤ k*`; if `G_I ≤ G_C` the
corner cutoff satisfies `v̄/2 ≤ 2v̲`. -/
theorem sbg_cand_valid (hvl : 0 ≤ vl) (hd0 : 0 < δ) (hd1 : δ < 1) (h2 : 2 * vl < vh) :
    (sbgGC vl vh δ ≤ sbgGI vh δ → 2 * vl ≤ sbgKI vh δ) ∧
    (sbgGI vh δ ≤ sbgGC vl vh δ → vh / 2 ≤ 2 * vl) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · by_contra hn
    push Not at hn
    have e1 := sbgGIk_sub_sbgGCk (vl := vl) (vh := vh) (δ := δ) (sbgKI vh δ)
    have e2 := sbgGC_sub (vl := vl) (vh := vh) (δ := δ) (sbgKI vh δ)
    have : sbgGI vh δ = sbgGIk vh δ (sbgKI vh δ) := rfl
    nlinarith [mul_pos hd0 (mul_pos (by linarith : (0 : ℝ) < vl - sbgKI vh δ / 2)
      (by linarith : (0 : ℝ) < vh - sbgKI vh δ / 2 - vl)), sq_nonneg (sbgKI vh δ - vh / 2)]
  · by_contra hn
    push Not at hn
    have e1 := sbgGIk_sub_sbgGCk (vl := vl) (vh := vh) (δ := δ) (vh / 2)
    have e2 := sbgGI_sub (vh := vh) hd1 (vh / 2)
    have : sbgGC vl vh δ = sbgGCk vl vh δ (vh / 2) := rfl
    have h43 : 0 < 4 - 3 * δ := by linarith
    nlinarith [mul_pos hd0 (mul_pos (by linarith : (0 : ℝ) < vh / 4 - vl)
      (by linarith : (0 : ℝ) < vh - vh / 4 - vl)),
      mul_nonneg h43.le (sq_nonneg (vh / 2 - sbgKI vh δ))]

/-- The interior cutoff is below `v̄` (`δ > 0`) and positive. -/
theorem sbgKI_mem (hlh : vl < vh) (hvl : 0 ≤ vl) (hd0 : 0 < δ) (hd1 : δ < 1) :
    0 < sbgKI vh δ ∧ sbgKI vh δ < vh := by
  have h43 : 0 < 4 - 3 * δ := by linarith
  have hvh : 0 < vh := by linarith
  unfold sbgKI
  refine ⟨by apply div_pos <;> nlinarith, ?_⟩
  rw [div_lt_iff₀ h43]
  nlinarith

/-- **Exercise 9.C.3(b), uniform on `[v̲, v̄]`** (MWG, p. 304; with Exercise 9.C.6). Let
`0 ≤ v̲ < v̄` and `δ ∈ (0, 1)`. A first price `p1` and second prices `r` form a weak PBE with
consistent beliefs iff every `r p ∈ [v̲, v̄]`, after every `p > v̲` the second price is the
consistent one `sbgR p = max (v̲, K(p)/2)`, and either (i) `v̄ ≤ 2v̲` and `p1 = v̲` (every type
buys at once), or (ii) `2v̲ < v̄`, `G_C ≤ G_I` and `p1 = (2 − δ)² v̄/(2 (4 − 3δ))` (interior
second price), or (iii) `2v̲ < v̄`, `G_I ≤ G_C` and `p1 = (1 − δ) v̄/2 + δ v̲` (second price at
the corner `v̲`). -/
theorem exercise_9_C_3b_general (hvl : 0 ≤ vl) (hlh : vl < vh) (hd0 : 0 < δ) (hd1 : δ < 1)
    (p1 : ℝ) (r : ℝ → ℝ) :
    IsSBGWeakPBE vl vh δ p1 r ∧ IsSBGConsistent vl vh δ r ↔
      (∀ p, vl ≤ r p ∧ r p ≤ vh) ∧ (∀ p, vl < p → r p = sbgR vl vh δ p) ∧
      ((vh ≤ 2 * vl ∧ p1 = vl) ∨
        (2 * vl < vh ∧ sbgGC vl vh δ ≤ sbgGI vh δ ∧ p1 = sbgPI vh δ) ∨
        (2 * vl < vh ∧ sbgGI vh δ ≤ sbgGC vl vh δ ∧ p1 = sbgPC vl vh δ)) := by
  have h1 : 0 < 1 - δ := by linarith
  have h43 : 0 < 4 - 3 * δ := by linarith
  obtain ⟨hKI0, hKI1⟩ := sbgKI_mem hlh hvl hd0 hd1
  -- payoffs of a profile with the consistent continuation
  have hbound : ∀ r : ℝ → ℝ, (∀ p, vl ≤ r p) → (∀ p, vl < p → r p = sbgR vl vh δ p) →
      ∀ p q, sbgPay vl vh δ p (r p) q ≤ sbgOpt vl vh δ := by
    intro r hr hrs p q
    by_cases hp : vl < p
    · rw [hrs p hp]
      obtain ⟨hK0, hK1⟩ := sbgK_mem hvl hlh hd0 hd1 hp
      exact (sbgPay_cons hvl hlh hd0 hd1 hp q).1.trans (sbgVal_le_opt hd0 hd1 hK0.le hK1)
    · rw [sbgPay_low hd0 hd1 (not_lt.1 hp) (hr p)]
      have hv := sbgVal_le_opt (vh := vh) hd0 hd1 le_rfl hlh.le
      rw [sbgVal_corner hd0 (by linarith)] at hv
      unfold sbgGCk at hv
      nlinarith [mul_le_mul_of_nonneg_right (not_lt.1 hp) (by linarith : (0 : ℝ) ≤ vh - vl)]
  -- the value of each candidate
  have hcand : ∀ r : ℝ → ℝ, (∀ p, vl ≤ r p) → (∀ p, vl < p → r p = sbgR vl vh δ p) →
      ((vh ≤ 2 * vl → sbgPay vl vh δ vl (r vl) (r vl) = sbgOpt vl vh δ) ∧
      (2 * vl < vh → sbgGC vl vh δ ≤ sbgGI vh δ →
        sbgPay vl vh δ (sbgPI vh δ) (r (sbgPI vh δ)) (r (sbgPI vh δ)) = sbgOpt vl vh δ) ∧
      (2 * vl < vh → sbgGI vh δ ≤ sbgGC vl vh δ →
        sbgPay vl vh δ (sbgPC vl vh δ) (r (sbgPC vl vh δ)) (r (sbgPC vl vh δ)) =
          sbgOpt vl vh δ)) := by
    intro r hr hrs
    refine ⟨fun h => ?_, fun h hG => ?_, fun h hG => ?_⟩
    · rw [sbgPay_low hd0 hd1 le_rfl (hr vl)]
      simp only [sbgOpt, h, ↓reduceIte]
    · have hv := (sbg_cand_valid hvl hd0 hd1 h).1 hG
      have hphi := (sbgPhi_cand (vl := vl) (vh := vh) hd0 hd1).1 hv
      have hgt : vl < sbgPI vh δ := by
        rw [← hphi]; unfold sbgPhi
        exact lt_max_of_lt_left (by nlinarith)
      rw [hrs _ hgt, (sbgPay_cons hvl hlh hd0 hd1 hgt 0).2, ← hphi,
        sbgK_phi hd0 hd1 hKI1.le, sbgVal_interior hd0 hv]
      simp only [sbgOpt, not_le.2 h, ↓reduceIte]
      exact (max_eq_left hG).symm
    · have hv := (sbg_cand_valid hvl hd0 hd1 h).2 hG
      have hphi := (sbgPhi_cand (vl := vl) (vh := vh) hd0 hd1).2 hv
      have hgt : vl < sbgPC vl vh δ := by
        rw [← hphi]; unfold sbgPhi
        exact lt_max_of_lt_left (by nlinarith)
      rw [hrs _ hgt, (sbgPay_cons hvl hlh hd0 hd1 hgt 0).2, ← hphi,
        sbgK_phi hd0 hd1 (by linarith), sbgVal_corner hd0 hv]
      simp only [sbgOpt, not_le.2 h, ↓reduceIte]
      exact (max_eq_right hG).symm
  -- consistency of the consistent continuation
  have hcons : ∀ r : ℝ → ℝ, (∀ p, vl ≤ r p) → (∀ p, vl < p → r p = sbgR vl vh δ p) →
      IsSBGConsistent vl vh δ r := by
    intro r hr hrs p hpos q
    by_cases hp : vl < p
    · rw [hrs p hp] at hpos ⊢
      rw [sbgCut_R hvl hlh hd0 hd1 hp] at hpos ⊢
      exact (sbgRev_opt_iff hvl hpos _).2 rfl q
    · rw [sbgCut_of_le hd0 hd1 (not_lt.1 hp) (hr p)] at hpos
      exact absurd hpos (lt_irrefl _)
  constructor
  · rintro ⟨⟨hr01, -, hroot⟩, hC⟩
    have hrs : ∀ p, vl < p → r p = sbgR vl vh δ p := fun p hp =>
      (sbg_consistent hvl hlh hd0 hd1 hC hp).1
    have hr : ∀ p, vl ≤ r p := fun p => (hr01 p).1
    obtain ⟨cA, cB, cC⟩ := hcand r hr hrs
    refine ⟨hr01, hrs, ?_⟩
    -- the equilibrium payoff is at least `sbgOpt`
    have hopt : sbgOpt vl vh δ ≤ sbgPay vl vh δ p1 (r p1) (r p1) := by
      by_cases h : vh ≤ 2 * vl
      · rw [← cA h]; exact hroot _ _
      · push Not at h
        rcases le_total (sbgGC vl vh δ) (sbgGI vh δ) with hG | hG
        · rw [← cB h hG]; exact hroot _ _
        · rw [← cC h hG]; exact hroot _ _
    by_cases hp : vl < p1
    · rw [hrs p1 hp, (sbgPay_cons hvl hlh hd0 hd1 hp 0).2] at hopt
      obtain ⟨hK0, hK1⟩ := sbgK_mem hvl hlh hd0 hd1 hp
      set K := sbgK vl vh δ p1 with hK
      by_cases h : vh ≤ 2 * vl
      · exfalso
        simp only [sbgOpt, h, ↓reduceIte] at hopt
        rw [sbgVal_corner hd0 (by linarith)] at hopt
        unfold sbgGCk at hopt
        nlinarith [mul_pos h1 (mul_pos (sub_pos.2 hK0) (by linarith : (0 : ℝ) < K + vl - vh))]
      push Not at h
      simp only [sbgOpt, not_le.2 h, ↓reduceIte] at hopt
      rcases le_total K (2 * vl) with hk | hk
      · rw [sbgVal_corner hd0 hk] at hopt
        have e := sbgGC_sub (vl := vl) (vh := vh) (δ := δ) K
        have hGC := le_of_max_le_right hopt
        have hGI := le_of_max_le_left hopt
        have hsq : (K - vh / 2) ^ 2 = 0 := by
          have : (1 - δ) * (K - vh / 2) ^ 2 ≤ 0 := by linarith
          nlinarith [sq_nonneg (K - vh / 2)]
        have hKv : K = vh / 2 := by
          have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hsq
          linarith
        have hp1 : p1 = sbgPhi vl δ K := (sbgPhi_K hd0 hd1 (by rw [← hK, hKv]; linarith)).symm
        rw [hKv] at hp1 hk
        refine Or.inr (Or.inr ⟨h, ?_, ?_⟩)
        · have := sbgGC_sub (vl := vl) (vh := vh) (δ := δ) K
          nlinarith [sq_nonneg (K - vh / 2)]
        · rw [hp1, (sbgPhi_cand hd0 hd1).2 hk]
      · rw [sbgVal_interior hd0 hk] at hopt
        have e := sbgGI_sub (vh := vh) hd1 K
        have hGI := le_of_max_le_left hopt
        have hGC := le_of_max_le_right hopt
        have hsq : (K - sbgKI vh δ) ^ 2 = 0 := by
          have : (4 - 3 * δ) / 4 * (K - sbgKI vh δ) ^ 2 ≤ 0 := by linarith
          nlinarith [sq_nonneg (K - sbgKI vh δ)]
        have hKv : K = sbgKI vh δ := by
          have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hsq
          linarith
        have hp1 : p1 = sbgPhi vl δ K := (sbgPhi_K hd0 hd1 (by rw [← hK, hKv]; exact hKI1)).symm
        rw [hKv] at hp1 hk
        refine Or.inr (Or.inl ⟨h, ?_, ?_⟩)
        · have := sbgGI_sub (vh := vh) hd1 K
          nlinarith [sq_nonneg (K - sbgKI vh δ)]
        · rw [hp1, (sbgPhi_cand hd0 hd1).1 hk]
    · push Not at hp
      rw [sbgPay_low hd0 hd1 hp (hr p1)] at hopt
      by_cases h : vh ≤ 2 * vl
      · simp only [sbgOpt, h, ↓reduceIte] at hopt
        refine Or.inl ⟨h, le_antisymm hp ?_⟩
        nlinarith
      · exfalso
        push Not at h
        simp only [sbgOpt, not_le.2 h, ↓reduceIte] at hopt
        have e := sbgGC_sub (vl := vl) (vh := vh) (δ := δ) vl
        have hGC := le_of_max_le_right hopt
        unfold sbgGCk at e
        nlinarith [mul_pos h1 (sq_pos_of_pos (by linarith : (0 : ℝ) < vh / 2 - vl)),
          mul_le_mul_of_nonneg_right hp (by linarith : (0 : ℝ) ≤ vh - vl)]
  · rintro ⟨hr01, hrs, hcase⟩
    have hr : ∀ p, vl ≤ r p := fun p => (hr01 p).1
    obtain ⟨cA, cB, cC⟩ := hcand r hr hrs
    have hC := hcons r hr hrs
    have hval : sbgPay vl vh δ p1 (r p1) (r p1) = sbgOpt vl vh δ := by
      rcases hcase with ⟨h, rfl⟩ | ⟨h, hG, rfl⟩ | ⟨h, hG, rfl⟩
      · exact cA h
      · exact cB h hG
      · exact cC h hG
    exact ⟨⟨hr01, fun h => hC p1 h, fun p q => hval ▸ hbound r hr hrs p q⟩, hC⟩

/-- **Exercise 9.C.3(b), the equilibrium outcomes** (MWG, p. 304). (i) If `v̄ ≤ 2v̲`, at the first
price `v̲` every type buys at once (whatever second price is expected). (ii) If `2v̲ < v̄` and
`G_C ≤ G_I`, at `sbgPI` the cutoff is `k* = (2 − δ) v̄/(4 − 3δ)` and the second price `k*/2`.
(iii) If `2v̲ < v̄` and `G_I ≤ G_C`, at `sbgPC` the cutoff is `v̄/2` and the second price is the
corner `v̲`. -/
theorem exercise_9_C_3b_general_outcomes (hvl : 0 ≤ vl) (hlh : vl < vh) (hd0 : 0 < δ)
    (hd1 : δ < 1) :
    (∀ r, vl ≤ r → sbgCut vl vh δ vl r = vl) ∧
    (2 * vl < vh → sbgGC vl vh δ ≤ sbgGI vh δ →
      sbgCut vl vh δ (sbgPI vh δ) (sbgR vl vh δ (sbgPI vh δ)) = sbgKI vh δ ∧
      sbgR vl vh δ (sbgPI vh δ) = sbgKI vh δ / 2) ∧
    (2 * vl < vh → sbgGI vh δ ≤ sbgGC vl vh δ →
      sbgCut vl vh δ (sbgPC vl vh δ) (sbgR vl vh δ (sbgPC vl vh δ)) = vh / 2 ∧
      sbgR vl vh δ (sbgPC vl vh δ) = vl) := by
  obtain ⟨hKI0, hKI1⟩ := sbgKI_mem hlh hvl hd0 hd1
  refine ⟨fun r hr => sbgCut_of_le hd0 hd1 le_rfl hr, fun h hG => ?_, fun h hG => ?_⟩
  · have hv := (sbg_cand_valid hvl hd0 hd1 h).1 hG
    have hphi := (sbgPhi_cand (vl := vl) (vh := vh) hd0 hd1).1 hv
    have hgt : vl < sbgPI vh δ := by
      rw [← hphi]; unfold sbgPhi
      exact lt_max_of_lt_left (by nlinarith)
    have hK : sbgK vl vh δ (sbgPI vh δ) = sbgKI vh δ := by
      rw [← hphi, sbgK_phi hd0 hd1 hKI1.le]
    rw [sbgCut_R hvl hlh hd0 hd1 hgt, hK]
    refine ⟨rfl, ?_⟩
    unfold sbgR
    rw [hK]
    exact max_eq_right (by linarith)
  · have hv := (sbg_cand_valid hvl hd0 hd1 h).2 hG
    have hphi := (sbgPhi_cand (vl := vl) (vh := vh) hd0 hd1).2 hv
    have hgt : vl < sbgPC vl vh δ := by
      rw [← hphi]; unfold sbgPhi
      exact lt_max_of_lt_left (by nlinarith)
    have hK : sbgK vl vh δ (sbgPC vl vh δ) = vh / 2 := by
      rw [← hphi, sbgK_phi hd0 hd1 (by linarith)]
    rw [sbgCut_R hvl hlh hd0 hd1 hgt, hK]
    refine ⟨rfl, ?_⟩
    unfold sbgR
    rw [hK]
    exact max_eq_left (by linarith)

/-- **Exercise 9.C.3(b), existence** (MWG, p. 304). A weak PBE with consistent beliefs exists
for all `0 ≤ v̲ < v̄` and `δ ∈ (0, 1)`. -/
theorem exercise_9_C_3b_general_exists (hvl : 0 ≤ vl) (hlh : vl < vh) (hd0 : 0 < δ)
    (hd1 : δ < 1) : ∃ p1 r, IsSBGWeakPBE vl vh δ p1 r ∧ IsSBGConsistent vl vh δ r := by
  classical
  set r : ℝ → ℝ := fun p => if vl < p then sbgR vl vh δ p else vl with hr
  have hr01 : ∀ p, vl ≤ r p ∧ r p ≤ vh := by
    intro p
    simp only [hr]
    split_ifs with hp
    · obtain ⟨hK0, hK1⟩ := sbgK_mem hvl hlh hd0 hd1 hp
      exact ⟨le_max_left _ _, max_le hlh.le (by linarith)⟩
    · exact ⟨le_rfl, hlh.le⟩
  have hrs : ∀ p, vl < p → r p = sbgR vl vh δ p := fun p hp => by simp [hr, hp]
  by_cases h : vh ≤ 2 * vl
  · exact ⟨vl, r, (exercise_9_C_3b_general hvl hlh hd0 hd1 vl r).2
      ⟨hr01, hrs, Or.inl ⟨h, rfl⟩⟩⟩
  · push Not at h
    rcases le_total (sbgGC vl vh δ) (sbgGI vh δ) with hG | hG
    · exact ⟨_, r, (exercise_9_C_3b_general hvl hlh hd0 hd1 _ r).2
        ⟨hr01, hrs, Or.inr (Or.inl ⟨h, hG, rfl⟩)⟩⟩
    · exact ⟨_, r, (exercise_9_C_3b_general hvl hlh hd0 hd1 _ r).2
        ⟨hr01, hrs, Or.inr (Or.inr ⟨h, hG, rfl⟩)⟩⟩

/-- For `v̲ = 0`, `v̄ = 1` the weak PBE conditions are those of `IsSBUWeakPBE`
(`SellerBuyer.lean`): the period-2 revenues differ by the factor `1/k`. -/
theorem isSBGWeakPBE_zero_one_iff (δ p1 : ℝ) (r : ℝ → ℝ) :
    IsSBGWeakPBE 0 1 δ p1 r ↔ IsSBUWeakPBE δ p1 r := by
  have hiff : ∀ k : ℝ, 0 < k → ∀ x y, sbURev k x ≤ sbURev k y ↔ sbgRev 0 k x ≤ sbgRev 0 k y := by
    intro k hk x y
    have e : ∀ z, sbURev k z = sbgRev 0 k z / k := fun z => by
      unfold sbURev sbgRev
      ring
    rw [e, e]
    exact div_le_div_iff_of_pos_right hk
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, fun hk q => (hiff _ hk _ _).2 (h2 hk q), h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, fun hk q => (hiff _ hk _ _).1 (h2 hk q), h3⟩

/-- **Exercise 9.C.3(b), instances** (MWG, p. 304), `v̄ = 1`, `δ = 1/2`. (i) `v̲ = 0`: the unique
consistent weak PBE first price is the interior `9/20 = sbPStar (1/2)` (the `v̲ = 0` answer of
`exercise_9_C_3b`). (ii) `v̲ = 3/10`: it is the corner price `2/5`, with cutoff `1/2` and second
price `3/10 = v̲`. (iii) `v̲ = 3/5`: it is `3/5 = v̲` and every type buys at once. -/
theorem exercise_9_C_3b_general_examples :
    (∀ p1 r, IsSBGWeakPBE 0 1 (1 / 2) p1 r ∧ IsSBGConsistent 0 1 (1 / 2) r →
      p1 = 9 / 20 ∧ p1 = sbPStar (1 / 2)) ∧
    (∀ p1 r, IsSBGWeakPBE (3 / 10) 1 (1 / 2) p1 r ∧ IsSBGConsistent (3 / 10) 1 (1 / 2) r →
      p1 = 2 / 5 ∧ sbgCut (3 / 10) 1 (1 / 2) p1 (r p1) = 1 / 2 ∧ r p1 = 3 / 10) ∧
    (∀ p1 r, IsSBGWeakPBE (3 / 5) 1 (1 / 2) p1 r ∧ IsSBGConsistent (3 / 5) 1 (1 / 2) r →
      p1 = 3 / 5 ∧ sbgCut (3 / 5) 1 (1 / 2) p1 (r p1) = 3 / 5) := by
  have hGI : sbgGI 1 (1 / 2) = 9 / 40 := by
    norm_num [sbgGI, sbgGIk, sbgKI]
  refine ⟨fun p1 r h => ?_, fun p1 r h => ?_, fun p1 r h => ?_⟩
  · obtain ⟨-, -, hc⟩ := (exercise_9_C_3b_general (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) p1 r).1 h
    have hGC : sbgGC 0 1 (1 / 2) = 1 / 8 := by norm_num [sbgGC, sbgGCk]
    rcases hc with ⟨h1, -⟩ | ⟨-, -, rfl⟩ | ⟨-, h3, -⟩
    · norm_num at h1
    · norm_num [sbgPI, sbPStar]
    · rw [hGI, hGC] at h3; norm_num at h3
  · have hc := (exercise_9_C_3b_general (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) p1 r).1 h
    obtain ⟨-, hrs, hc⟩ := hc
    have hGC : sbgGC (3 / 10) 1 (1 / 2) = 23 / 100 := by norm_num [sbgGC, sbgGCk]
    have hlt : sbgGI 1 (1 / 2) ≤ sbgGC (3 / 10) 1 (1 / 2) := by rw [hGI, hGC]; norm_num
    rcases hc with ⟨h1, -⟩ | ⟨-, h2, -⟩ | ⟨h2, h3, rfl⟩
    · norm_num at h1
    · rw [hGI, hGC] at h2; norm_num at h2
    · obtain ⟨-, -, hout⟩ := exercise_9_C_3b_general_outcomes (vl := 3 / 10) (vh := 1)
        (δ := 1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      obtain ⟨o1, o2⟩ := hout h2 h3
      have hgt : (3 / 10 : ℝ) < sbgPC (3 / 10) 1 (1 / 2) := by norm_num [sbgPC]
      rw [hrs _ hgt, o1, o2]
      norm_num [sbgPC]
  · have hc := (exercise_9_C_3b_general (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) p1 r).1 h
    obtain ⟨hr01, -, hc⟩ := hc
    rcases hc with ⟨-, rfl⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
    · exact ⟨rfl, ((exercise_9_C_3b_general_outcomes (by norm_num) (by norm_num) (by norm_num)
        (by norm_num)).1 _ (hr01 _).1)⟩
    · norm_num at h1
    · norm_num at h1

end MWG.DynamicGames

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The one-shot deviation principle for infinite-horizon discounted games

MWG, Appendix A of Chapter 9 (pp. 296-299): the subgame perfection of the stationary profile
of the infinite horizon bargaining game is checked by one-stage deviations; this module states
and proves the principle behind that check in general.

A multi-stage game with observed actions: players `i ∈ I` choose actions `a_i ∈ A i`
simultaneously in every period `t = 0, 1, 2, …`; a history is the list of the action profiles
played so far (most recent first); a pure strategy of player `i` (`OSProfile`) maps histories
to actions. Player `i`'s per-period payoff `u i h x` may depend on the history `h` and the
current profile `x`; payoffs are bounded (`|u| ≤ M`) and discounted by `δ ∈ [0, 1)`.
`osValue u δ σ h i = ∑ₙ δⁿ u_i(hₙ, σ(hₙ))` is player `i`'s continuation payoff from history `h`.

* `osValue_succ`: the recursion `V(h) = u_i(h, σ(h)) + δ V(σ(h) :: h)`.
* `oneShot_deviation_principle_discounted`: if player `i` cannot gain at any history by a one-period
  deviation (deviating now and following `σ_i` afterwards), then no strategy of player `i`
  (deviating at finitely or infinitely many histories) gains at any history.
* `oneShot_deviation_principle_discounted_iff`: hence `σ` is subgame perfect (no player gains by any
  change of strategy at any history) iff there is no profitable one-shot deviation.
* Instance: the infinitely repeated prisoners' dilemma (`(C, C) ↦ 2`, `(D, C) ↦ 3`, `(C, D) ↦
  0`, `(D, D) ↦ 1`) with grim trigger strategies: subgame perfect iff `δ ≥ 1/2`
  (`grim_trigger_spe_iff`).
-/

namespace MWG.DynamicGames

variable {I : Type*} [DecidableEq I] {A : I → Type*}

/-- A history: the action profiles played so far, the most recent first. -/
abbrev OSHist (A : I → Type*) := List ((i : I) → A i)

/-- A pure strategy profile of the multi-stage game. -/
abbrev OSProfile (A : I → Type*) := (i : I) → OSHist A → A i

/-- The action profile played at history `h`. -/
def osPlay (σ : OSProfile A) (h : OSHist A) : (i : I) → A i := fun i => σ i h

/-- The history after `n` further periods of play according to `σ`. -/
def osPath (σ : OSProfile A) : OSHist A → ℕ → OSHist A
  | h, 0 => h
  | h, n + 1 => osPath σ (osPlay σ h :: h) n

/-- Player `i`'s discounted payoff from history `h` on when `σ` is played. -/
noncomputable def osValue (u : I → OSHist A → ((i : I) → A i) → ℝ) (δ : ℝ) (σ : OSProfile A)
    (h : OSHist A) (i : I) : ℝ :=
  ∑' n : ℕ, δ ^ n * u i (osPath σ h n) (osPlay σ (osPath σ h n))

omit [DecidableEq I] in
theorem osPath_length (σ : OSProfile A) (n : ℕ) (h : OSHist A) :
    (osPath σ h n).length = h.length + n := by
  induction n generalizing h with
  | zero => rfl
  | succ n ih =>
    simp only [osPath, ih, List.length_cons]
    omega

omit [DecidableEq I] in
/-- Bounded discounted payoffs are summable. -/
theorem osValue_summable {u : I → OSHist A → ((i : I) → A i) → ℝ} {δ M : ℝ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (hu : ∀ i h x, |u i h x| ≤ M) (σ : OSProfile A) (h : OSHist A) (i : I) :
    Summable fun n : ℕ => δ ^ n * u i (osPath σ h n) (osPlay σ (osPath σ h n)) := by
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hδ0 hδ1).mul_right M)
    fun n => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hδ0 n)]
  exact mul_le_mul_of_nonneg_left (hu _ _ _) (pow_nonneg hδ0 n)

omit [DecidableEq I] in
/-- The continuation payoff is bounded by `M/(1 − δ)`. -/
theorem osValue_abs_le {u : I → OSHist A → ((i : I) → A i) → ℝ} {δ M : ℝ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (hu : ∀ i h x, |u i h x| ≤ M) (σ : OSProfile A) (h : OSHist A) (i : I) :
    |osValue u δ σ h i| ≤ M / (1 - δ) := by
  have hs := osValue_summable hδ0 hδ1 hu σ h i
  have hg := (summable_geometric_of_lt_one hδ0 hδ1).mul_right M
  have hle : ∀ n : ℕ, |δ ^ n * u i (osPath σ h n) (osPlay σ (osPath σ h n))| ≤ δ ^ n * M := by
    intro n
    rw [abs_mul, abs_of_nonneg (pow_nonneg hδ0 n)]
    exact mul_le_mul_of_nonneg_left (hu _ _ _) (pow_nonneg hδ0 n)
  have h1 : |osValue u δ σ h i| ≤ ∑' n : ℕ, δ ^ n * M := by
    unfold osValue
    rw [abs_le]
    constructor
    · rw [← tsum_neg]
      exact hg.neg.tsum_le_tsum (fun n => neg_le_of_abs_le (hle n)) hs
    · exact hs.tsum_le_tsum (fun n => le_of_abs_le (hle n)) hg
  rw [tsum_mul_right, tsum_geometric_of_lt_one hδ0 hδ1] at h1
  rw [div_eq_inv_mul]
  exact h1

omit [DecidableEq I] in
/-- **The recursion** `V(h) = u_i(h, σ(h)) + δ V(σ(h) :: h)`. -/
theorem osValue_succ {u : I → OSHist A → ((i : I) → A i) → ℝ} {δ M : ℝ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (hu : ∀ i h x, |u i h x| ≤ M) (σ : OSProfile A) (h : OSHist A) (i : I) :
    osValue u δ σ h i = u i h (osPlay σ h) + δ * osValue u δ σ (osPlay σ h :: h) i := by
  unfold osValue
  rw [(osValue_summable hδ0 hδ1 hu σ h i).tsum_eq_zero_add, ← tsum_mul_left]
  simp only [pow_zero, one_mul, osPath, pow_succ]
  congr 1
  refine tsum_congr fun n => ?_
  ring

/-- Changing player `i`'s strategy changes only her action. -/
theorem osPlay_update (σ : OSProfile A) (i : I) (τ : OSHist A → A i) (h : OSHist A) :
    osPlay (Function.update σ i τ) h = Function.update (osPlay σ h) i (τ h) := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp [osPlay]
  · simp [osPlay, Function.update_of_ne hj]

omit [DecidableEq I] in
/-- Profiles that agree on all histories of length at least `L` give the same continuation
payoffs from such histories. -/
theorem osValue_congr {u : I → OSHist A → ((i : I) → A i) → ℝ} {δ : ℝ} {σ σ' : OSProfile A}
    {L : ℕ} (hag : ∀ h : OSHist A, L ≤ h.length → osPlay σ' h = osPlay σ h) {h : OSHist A}
    (hh : L ≤ h.length) (i : I) : osValue u δ σ' h i = osValue u δ σ h i := by
  have hpath : ∀ n (h : OSHist A), L ≤ h.length → osPath σ' h n = osPath σ h n := by
    intro n
    induction n with
    | zero => intro h _; rfl
    | succ n ih =>
      intro h hh
      simp only [osPath, hag h hh]
      exact ih _ (by simp only [List.length_cons]; omega)
  unfold osValue
  refine tsum_congr fun n => ?_
  rw [hpath n h hh, hag _ (by rw [osPath_length]; omega)]

/-- **The one-shot deviation principle** (MWG, Appendix A, pp. 296-299). In a multi-stage game
with observed actions, bounded per-period payoffs and discount factor `δ ∈ [0, 1)`: if player
`i` cannot gain at any history `h` by deviating to any action `a` for one period and then
following `σ_i`, then no strategy `τ` of player `i` gains at any history. -/
theorem oneShot_deviation_principle_discounted {u : I → OSHist A → ((i : I) → A i) → ℝ} {δ M : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hu : ∀ i h x, |u i h x| ≤ M) (σ : OSProfile A) (i : I)
    (hos : ∀ (h : OSHist A) (a : A i),
      u i h (Function.update (osPlay σ h) i a) +
        δ * osValue u δ σ (Function.update (osPlay σ h) i a :: h) i ≤ osValue u δ σ h i)
    (τ : OSHist A → A i) (h : OSHist A) :
    osValue u δ (Function.update σ i τ) h i ≤ osValue u δ σ h i := by
  set σ' := Function.update σ i τ with hσ'
  set C := 2 * (M / (1 - δ)) with hC
  have key : ∀ T : ℕ, ∀ h, osValue u δ σ' h i ≤ osValue u δ σ h i + δ ^ T * C := by
    intro T
    induction T with
    | zero =>
      intro h
      have h1 := osValue_abs_le hδ0 hδ1 hu σ' h i
      have h2 := osValue_abs_le hδ0 hδ1 hu σ h i
      rw [abs_le] at h1 h2
      rw [pow_zero, one_mul, hC]
      linarith
    | succ T ih =>
      intro h
      rw [osValue_succ hδ0 hδ1 hu σ' h i, hσ', osPlay_update σ i τ h, ← hσ']
      have h1 := ih (Function.update (osPlay σ h) i (τ h) :: h)
      have h2 := hos h (τ h)
      have h3 := mul_le_mul_of_nonneg_left h1 hδ0
      rw [pow_succ]
      nlinarith
  have hlim : Filter.Tendsto (fun T : ℕ => osValue u δ σ h i + δ ^ T * C) Filter.atTop
      (nhds (osValue u δ σ h i + 0 * C)) :=
    tendsto_const_nhds.add ((tendsto_pow_atTop_nhds_zero_of_lt_one hδ0 hδ1).mul_const C)
  rw [zero_mul, add_zero] at hlim
  exact ge_of_tendsto' hlim fun T => key T h

/-- **The one-shot deviation principle, characterisation** (MWG, Appendix A, pp. 296-299). With
bounded per-period payoffs and `δ ∈ [0, 1)`, a pure profile `σ` is subgame perfect (at every
history no player gains by any change of her strategy) iff no player has a profitable one-shot
deviation at any history. -/
theorem oneShot_deviation_principle_discounted_iff
    {u : I → OSHist A → ((i : I) → A i) → ℝ} {δ M : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hu : ∀ i h x, |u i h x| ≤ M) (σ : OSProfile A) :
    (∀ i (τ : OSHist A → A i) h, osValue u δ (Function.update σ i τ) h i ≤ osValue u δ σ h i) ↔
      ∀ i (h : OSHist A) (a : A i),
        u i h (Function.update (osPlay σ h) i a) +
          δ * osValue u δ σ (Function.update (osPlay σ h) i a :: h) i ≤ osValue u δ σ h i := by
  constructor
  · intro hspe i h a
    -- the strategy that plays `a` at histories of the length of `h` and follows `σ_i` otherwise
    set τ : OSHist A → A i := fun h' => if h'.length = h.length then a else σ i h' with hτ
    have hspe' := hspe i τ h
    rw [osValue_succ hδ0 hδ1 hu _ h i, osPlay_update σ i τ h] at hspe'
    have hτh : τ h = a := by simp [hτ]
    rw [hτh] at hspe'
    have hcong : osValue u δ (Function.update σ i τ) (Function.update (osPlay σ h) i a :: h) i =
        osValue u δ σ (Function.update (osPlay σ h) i a :: h) i := by
      refine osValue_congr (L := h.length + 1) (fun h' hh' => ?_) (by simp) i
      rw [osPlay_update]
      have : τ h' = σ i h' := by
        simp only [hτ]
        split_ifs with hl
        · omega
        · rfl
      rw [this]
      funext j
      by_cases hj : j = i
      · subst hj; simp [osPlay]
      · simp [Function.update_of_ne hj]
    rw [hcong] at hspe'
    exact hspe'
  · intro hos i τ h
    exact oneShot_deviation_principle_discounted hδ0 hδ1 hu σ i (hos i) τ h

/-! ### Instance: grim trigger in the infinitely repeated prisoners' dilemma -/

/-- The prisoners' dilemma stage payoffs (`true` = cooperate): `(C, C) ↦ 2`, `(D, C) ↦ 3` for
the defector, `(C, D) ↦ 0`, `(D, D) ↦ 1`. -/
def pdStage (i : Fin 2) (x : Fin 2 → Bool) : ℝ :=
  if x i then (if x (1 - i) then 2 else 0) else (if x (1 - i) then 3 else 1)

/-- A history in which both players always cooperated. -/
def pdClean (h : OSHist fun _ : Fin 2 => Bool) : Bool := h.all fun x => x 0 && x 1

/-- Grim trigger: cooperate iff both have always cooperated. -/
def grimTrigger : OSProfile fun _ : Fin 2 => Bool := fun _ h => pdClean h

/-- The repeated prisoners' dilemma payoff (history independent). -/
def pdU (i : Fin 2) (_ : OSHist fun _ : Fin 2 => Bool) (x : Fin 2 → Bool) : ℝ := pdStage i x

theorem pdU_bound (i : Fin 2) (h : OSHist fun _ : Fin 2 => Bool) (x : Fin 2 → Bool) :
    |pdU i h x| ≤ 3 := by
  unfold pdU pdStage
  split_ifs <;> norm_num

theorem grim_value_clean {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) {h : OSHist fun _ : Fin 2 => Bool}
    (hc : pdClean h = true) (i : Fin 2) : osValue pdU δ grimTrigger h i = 2 / (1 - δ) := by
  have hpath : ∀ n (h : OSHist fun _ : Fin 2 => Bool), pdClean h = true →
      pdClean (osPath grimTrigger h n) = true := by
    intro n
    induction n with
    | zero => intro h hc; exact hc
    | succ n ih =>
      intro h hc
      refine ih _ ?_
      simp only [pdClean, List.all_cons] at hc ⊢
      simp [osPlay, grimTrigger, pdClean, hc]
  have hterm : ∀ n, δ ^ n * pdU i (osPath grimTrigger h n)
      (osPlay grimTrigger (osPath grimTrigger h n)) = 2 * δ ^ n := by
    intro n
    have := hpath n h hc
    have hp : osPlay grimTrigger (osPath grimTrigger h n) = fun _ => true := by
      funext j
      simp [osPlay, grimTrigger, this]
    rw [hp]
    simp [pdU, pdStage]
    ring
  unfold osValue
  simp only [hterm]
  rw [tsum_mul_left, tsum_geometric_of_lt_one hδ0 hδ1, div_eq_mul_inv]

theorem grim_value_dirty {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) {h : OSHist fun _ : Fin 2 => Bool}
    (hc : pdClean h = false) (i : Fin 2) : osValue pdU δ grimTrigger h i = 1 / (1 - δ) := by
  have hpath : ∀ n (h : OSHist fun _ : Fin 2 => Bool), pdClean h = false →
      pdClean (osPath grimTrigger h n) = false := by
    intro n
    induction n with
    | zero => intro h hc; exact hc
    | succ n ih =>
      intro h hc
      refine ih _ ?_
      simp only [pdClean, List.all_cons] at hc ⊢
      simp [hc]
  have hterm : ∀ n, δ ^ n * pdU i (osPath grimTrigger h n)
      (osPlay grimTrigger (osPath grimTrigger h n)) = 1 * δ ^ n := by
    intro n
    have := hpath n h hc
    have hp : osPlay grimTrigger (osPath grimTrigger h n) = fun _ => false := by
      funext j
      simp [osPlay, grimTrigger, this]
    rw [hp]
    simp [pdU, pdStage]
  unfold osValue
  simp only [hterm]
  rw [tsum_mul_left, tsum_geometric_of_lt_one hδ0 hδ1, div_eq_mul_inv]

/-- **The one-shot deviation principle, an instance** (MWG, Appendix A). In the infinitely
repeated prisoners' dilemma with discount factor `δ ∈ [0, 1)`, grim trigger is subgame perfect
iff `δ ≥ 1/2`: by `oneShot_deviation_principle_discounted_iff` it suffices to check one-period
deviations, and the only one that can gain is defecting after a clean history, which gives
`3 + δ/(1 − δ)` against `2/(1 − δ)`. -/
theorem grim_trigger_spe_iff {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    (∀ i (τ : OSHist (fun _ : Fin 2 => Bool) → Bool) h,
      osValue pdU δ (Function.update grimTrigger i τ) h i ≤ osValue pdU δ grimTrigger h i) ↔
      1 / 2 ≤ δ := by
  have h1 : 0 < 1 - δ := by linarith
  rw [oneShot_deviation_principle_discounted_iff hδ0 hδ1 pdU_bound]
  constructor
  · intro hos
    have := hos 0 [] false
    have hc : pdClean ([] : OSHist fun _ : Fin 2 => Bool) = true := rfl
    rw [grim_value_clean hδ0 hδ1 hc] at this
    have hd : pdClean (Function.update (osPlay grimTrigger []) 0 false :: []) = false := by
      simp [pdClean]
    rw [grim_value_dirty hδ0 hδ1 hd] at this
    have hs : pdU 0 [] (Function.update (osPlay grimTrigger []) 0 false) = 3 := by
      simp [pdU, pdStage, osPlay, grimTrigger, pdClean]
    rw [hs] at this
    rw [div_eq_mul_inv, div_eq_mul_inv] at this
    have hinv : (1 - δ)⁻¹ * (1 - δ) = 1 := inv_mul_cancel₀ h1.ne'
    nlinarith [inv_pos.2 h1]
  · intro hδ i h a
    cases hc : pdClean h with
    | false =>
      have hd : pdClean (Function.update (osPlay grimTrigger h) i a :: h) = false := by
        simp only [pdClean, List.all_cons] at hc ⊢
        simp [hc]
      rw [grim_value_dirty hδ0 hδ1 hc, grim_value_dirty hδ0 hδ1 hd]
      have hs : pdU i h (Function.update (osPlay grimTrigger h) i a) ≤ 1 := by
        have hp : osPlay grimTrigger h = fun _ => false := by
          funext j; simp [osPlay, grimTrigger, hc]
        rw [hp]
        fin_cases i <;> cases a <;> simp [pdU, pdStage]
      have e1 : 1 / (1 - δ) * (1 - δ) = 1 := div_mul_cancel₀ 1 h1.ne'
      linarith
    | true =>
      have hp : osPlay grimTrigger h = fun _ => true := by
        funext j; simp [osPlay, grimTrigger, hc]
      cases a with
      | true =>
        have hu : Function.update (osPlay grimTrigger h) i true = fun _ => true := by
          rw [hp]; funext j; by_cases hj : j = i
          · subst hj; simp
          · simp [Function.update_of_ne hj]
        have hd : pdClean ((fun _ => true) :: h) = true := by
          simp only [pdClean, List.all_cons] at hc ⊢
          simp [hc]
        rw [hu, grim_value_clean hδ0 hδ1 hc, grim_value_clean hδ0 hδ1 hd]
        have hs : pdU i h (fun _ => true) = 2 := by simp [pdU, pdStage]
        rw [hs]
        have e2 : 2 / (1 - δ) * (1 - δ) = 2 := div_mul_cancel₀ 2 h1.ne'
        linarith
      | false =>
        have hd : pdClean (Function.update (osPlay grimTrigger h) i false :: h) = false := by
          rw [hp]
          fin_cases i <;> simp [pdClean]
        rw [grim_value_clean hδ0 hδ1 hc, grim_value_dirty hδ0 hδ1 hd]
        have hs : pdU i h (Function.update (osPlay grimTrigger h) i false) = 3 := by
          rw [hp]
          fin_cases i <;> simp [pdU, pdStage]
        rw [hs, div_eq_mul_inv, div_eq_mul_inv]
        have hinv : (1 - δ)⁻¹ * (1 - δ) = 1 := inv_mul_cancel₀ h1.ne'
        nlinarith [inv_pos.2 h1]

end MWG.DynamicGames

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Off-path beliefs after an informed player's move are unrestricted by consistency

MWG, Exercise 9.C.6 for Exercise 9.C.5 (p. 304), Definition 9.C.4 (p. 290). When a player
with finitely many types (prior `p`, full support) moves first and the move `m` is off the
equilibrium path, type-dependent trembles can generate any belief `q` after `m` as a limit of
Bayes posteriors (`signal_belief_consistent`): type `t` trembles to `m` with probability
`εₙ(t) = (q(t) + 1/(n+1)) / (p(t) (n+1))`. So consistency imposes nothing beyond Bayes' rule on
the path, and in a game in which the informed player moves once (as Ms. P in Exercise 9.C.5)
the sequential equilibria are the weak PBE. The model of Exercise 9.C.5 in `Informed.lean`
has a continuum of types, for which Definition 9.C.4 is not defined; this module proves the
finite-type statement.
-/

namespace MWG.DynamicGames

open Filter Topology

/-- **Exercise 9.C.6 for 9.C.5** (MWG, pp. 290 and 304). With finitely many types of full
prior support `p`, every belief `q` about the type after an off-path move is the limit of the
Bayes posteriors `p(t) εₙ(t) / ∑ₛ p(s) εₙ(s)` for some totally mixed trembles `εₙ → 0`. -/
theorem signal_belief_consistent {T : Type*} [Fintype T] (p q : T → ℝ) (hp : ∀ t, 0 < p t)
    (hq0 : ∀ t, 0 ≤ q t) (hq1 : ∑ t, q t = 1) :
    ∃ e : ℕ → T → ℝ, (∀ n t, 0 < e n t) ∧ (∀ t, Tendsto (fun n => e n t) atTop (𝓝 0)) ∧
      ∀ t, Tendsto (fun n => p t * e n t / ∑ s, p s * e n s) atTop (𝓝 (q t)) := by
  set c : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hc
  have hc0 : ∀ n, 0 < c n := fun n => by simp only [hc]; positivity
  have hclim : Tendsto c atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨fun n t => (q t + c n) * c n / p t, fun n t => ?_, fun t => ?_, fun t => ?_⟩
  · have := hq0 t
    have := hc0 n
    have := hp t
    positivity
  · have h := ((tendsto_const_nhds (x := q t)).add hclim).mul hclim
    rw [add_zero, mul_zero] at h
    simpa using h.div_const (p t)
  · have hterm : ∀ n s, p s * ((q s + c n) * c n / p s) = (q s + c n) * c n := fun n s => by
      field_simp [(hp s).ne']
    have hsum : ∀ n, ∑ s, p s * ((q s + c n) * c n / p s) =
        (1 + Fintype.card T * c n) * c n := by
      intro n
      simp only [hterm, ← Finset.sum_mul, Finset.sum_add_distrib, hq1, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
    have hratio : ∀ n, p t * ((q t + c n) * c n / p t) /
        ∑ s, p s * ((q s + c n) * c n / p s) = (q t + c n) / (1 + Fintype.card T * c n) := by
      intro n
      rw [hterm, hsum]
      have := hc0 n
      have : 0 < 1 + Fintype.card T * c n := by positivity
      field_simp
    simp only [hratio]
    have h : Tendsto (fun n => (q t + c n) / (1 + Fintype.card T * c n)) atTop
        (𝓝 ((q t + 0) / (1 + Fintype.card T * 0))) :=
      ((tendsto_const_nhds (x := q t)).add hclim).div
        ((tendsto_const_nhds (x := (1 : ℝ))).add (hclim.const_mul (Fintype.card T : ℝ)))
        (by norm_num)
    rwa [add_zero, mul_zero, add_zero, div_one] at h

/-- **Exercise 9.C.6 for 9.C.5, an instance** (MWG, p. 304): two types with prior `(1/2, 1/2)`;
the belief putting probability one on the first type is a limit of Bayes posteriors. -/
theorem signal_belief_consistent_instance :
    ∃ e : ℕ → Fin 2 → ℝ, (∀ n t, 0 < e n t) ∧ (∀ t, Tendsto (fun n => e n t) atTop (𝓝 0)) ∧
      ∀ t, Tendsto (fun n => (1 / 2 : ℝ) * e n t / ∑ s, (1 / 2 : ℝ) * e n s) atTop
        (𝓝 (![1, 0] t)) :=
  signal_belief_consistent (fun _ => 1 / 2) ![1, 0] (fun _ => by norm_num)
    (fun t => by fin_cases t <;> norm_num) (by simp [Fin.sum_univ_two])

end MWG.DynamicGames

set_option linter.style.longLine false
#print axioms MWG.DynamicGames.reachFrom
#print axioms MWG.DynamicGames.reachFrom_self
#print axioms MWG.DynamicGames.reachFrom_cons
#print axioms MWG.DynamicGames.reachFrom_cons_self
#print axioms MWG.DynamicGames.reachFrom_nil
#print axioms MWG.DynamicGames.reachFrom_trans
#print axioms MWG.DynamicGames.reach_eq_mul_reachFrom
#print axioms MWG.DynamicGames.reachFrom_nonneg
#print axioms MWG.DynamicGames.reachFrom_congr
#print axioms MWG.DynamicGames.cont
#print axioms MWG.DynamicGames.cont_terminal
#print axioms MWG.DynamicGames.cont_decision
#print axioms MWG.DynamicGames.cont_eq
#print axioms MWG.DynamicGames.cont_unfold
#print axioms MWG.DynamicGames.cont_nil
#print axioms MWG.DynamicGames.reach_mul_cont
#print axioms MWG.DynamicGames.cont_congr
#print axioms MWG.DynamicGames.sum_reachFrom_terminals
#print axioms MWG.DynamicGames.le_cont
#print axioms MWG.DynamicGames.sum_suffix_split
#print axioms MWG.DynamicGames.entryNodes
#print axioms MWG.DynamicGames.mem_entryNodes
#print axioms MWG.DynamicGames.cont_sub_eq_sum_entry
#print axioms MWG.DynamicGames.reachFrom_entry_congr
#print axioms MWG.DynamicGames.IsBehaviorProfile
#print axioms MWG.DynamicGames.assemble_nonneg
#print axioms MWG.DynamicGames.assemble_sum
#print axioms MWG.DynamicGames.isBehaviorProfile_update
#print axioms MWG.DynamicGames.IsNashB
#print axioms MWG.DynamicGames.toNormalForm_payoff_eq_cont
#print axioms MWG.DynamicGames.pureB
#print axioms MWG.DynamicGames.assemble_pureB
#print axioms MWG.DynamicGames.isBehaviorProfile_pureB
#print axioms MWG.DynamicGames.pureB_update
#print axioms MWG.DynamicGames.IsNashB.isNashEquilibrium_pure
#print axioms MWG.DynamicGames.IsSubgameRoot
#print axioms MWG.DynamicGames.InducesNashAt
#print axioms MWG.DynamicGames.IsSPNE
#print axioms MWG.DynamicGames.isSubgameRoot_nil
#print axioms MWG.DynamicGames.isNashB_of_isSPNE
#print axioms MWG.DynamicGames.exercise_9_B_2a
#print axioms MWG.DynamicGames.IsSubgameRootWithin
#print axioms MWG.DynamicGames.isSubgameRootWithin_iff
#print axioms MWG.DynamicGames.exercise_9_B_2b
#print axioms MWG.DynamicGames.OneShotOptimalAt
#print axioms MWG.DynamicGames.assemble_update_of_none
#print axioms MWG.DynamicGames.assemble_update_of_ne
#print axioms MWG.DynamicGames.assemble_update_self
#print axioms MWG.DynamicGames.oneShot_deviation_principle
#print axioms MWG.DynamicGames.isSPNE_of_oneShotOptimal
#print axioms MWG.DynamicGames.isSubgameRoot_of_perfectInformation
#print axioms MWG.DynamicGames.info_ne_of_perfectInformation
#print axioms MWG.DynamicGames.dirac
#print axioms MWG.DynamicGames.cont_dirac_update
#print axioms MWG.DynamicGames.oneShotOptimal_of_isSPNE
#print axioms MWG.DynamicGames.isSPNE_iff_oneShotOptimal
#print axioms MWG.DynamicGames.IsBackwardInduction
#print axioms MWG.DynamicGames.pureOfChoice
#print axioms MWG.DynamicGames.cont_pureOfChoice
#print axioms MWG.DynamicGames.exists_backwardInduction
#print axioms MWG.DynamicGames.oneShotOptimal_unique
#print axioms MWG.DynamicGames.pure_eq_of_assemble_eq
#print axioms MWG.DynamicGames.proposition_9_B_1
#print axioms MWG.DynamicGames.exists_pure_nash_of_perfectInformation
#print axioms MWG.DynamicGames.proposition_9_B_2
#print axioms MWG.DynamicGames.cont_zeroSum
#print axioms MWG.DynamicGames.exercise_9_B_4
#print axioms MWG.DynamicGames.InSub
#print axioms MWG.DynamicGames.splice
#print axioms MWG.DynamicGames.IsSPNEIn
#print axioms MWG.DynamicGames.isSPNEIn_of_isSPNE
#print axioms MWG.DynamicGames.IsSPNEReduced
#print axioms MWG.DynamicGames.inSub_of_suffix
#print axioms MWG.DynamicGames.assemble_splice
#print axioms MWG.DynamicGames.cont_splice_root
#print axioms MWG.DynamicGames.entryNodes_inSub
#print axioms MWG.DynamicGames.assemble_update_splice
#print axioms MWG.DynamicGames.proposition_9_B_3_ii
#print axioms MWG.DynamicGames.proposition_9_B_3_i
#print axioms MWG.DynamicGames.IsBeliefSystem
#print axioms MWG.DynamicGames.condPayoff
#print axioms MWG.DynamicGames.SeqRationalAt
#print axioms MWG.DynamicGames.SeqRational
#print axioms MWG.DynamicGames.probInfo
#print axioms MWG.DynamicGames.BayesConsistent
#print axioms MWG.DynamicGames.IsWeakPBE
#print axioms MWG.DynamicGames.mem_infoSet
#print axioms MWG.DynamicGames.recall_pred
#print axioms MWG.DynamicGames.eq_of_absentMinded
#print axioms MWG.DynamicGames.entry_closed
#print axioms MWG.DynamicGames.sum_eq_sum_infoSet
#print axioms MWG.DynamicGames.assemble_update_eq_off
#print axioms MWG.DynamicGames.reach_le_probInfo
#print axioms MWG.DynamicGames.nash_gap_eq
#print axioms MWG.DynamicGames.bayesOrUniform
#print axioms MWG.DynamicGames.bayesOrUniform_spec
#print axioms MWG.DynamicGames.proposition_9_C_1
#print axioms MWG.DynamicGames.isNashB_of_isWeakPBE
#print axioms MWG.DynamicGames.IsTotallyMixedB
#print axioms MWG.DynamicGames.bayesBelief
#print axioms MWG.DynamicGames.IsConsistent
#print axioms MWG.DynamicGames.IsSequentialEq
#print axioms MWG.DynamicGames.tendsto_assemble
#print axioms MWG.DynamicGames.tendsto_reachFrom
#print axioms MWG.DynamicGames.tendsto_reach
#print axioms MWG.DynamicGames.isWeakPBE_of_isSequentialEq
#print axioms MWG.DynamicGames.reachFrom_prop_of_consistent
#print axioms MWG.DynamicGames.proposition_9_C_2
#print axioms MWG.DynamicGames.isSequentialEq_strengthens
#print axioms MWG.DynamicGames.BargainingGame
#print axioms MWG.DynamicGames.BargainingGame.mk
#print axioms MWG.DynamicGames.BargainingGame.v
#print axioms MWG.DynamicGames.BargainingGame.δ
#print axioms MWG.DynamicGames.BargainingGame.T
#print axioms MWG.DynamicGames.BargainingGame.v_pos
#print axioms MWG.DynamicGames.BargainingGame.δ_pos
#print axioms MWG.DynamicGames.BargainingGame.δ_lt_one
#print axioms MWG.DynamicGames.BargainingProfile
#print axioms MWG.DynamicGames.BargainingProfile.mk
#print axioms MWG.DynamicGames.BargainingProfile.prop
#print axioms MWG.DynamicGames.BargainingProfile.resp
#print axioms MWG.DynamicGames.BargainingGame.proposer
#print axioms MWG.DynamicGames.BargainingGame.other
#print axioms MWG.DynamicGames.BargainingGame.other_ne
#print axioms MWG.DynamicGames.BargainingGame.ne_other
#print axioms MWG.DynamicGames.BargainingGame.other_other
#print axioms MWG.DynamicGames.BargainingGame.eq_or_eq_other
#print axioms MWG.DynamicGames.BargainingGame.proposer_succ
#print axioms MWG.DynamicGames.BargainingGame.share
#print axioms MWG.DynamicGames.BargainingGame.share_proposer
#print axioms MWG.DynamicGames.BargainingGame.share_other
#print axioms MWG.DynamicGames.BargainingGame.Live
#print axioms MWG.DynamicGames.BargainingGame.live_of_le
#print axioms MWG.DynamicGames.BargainingGame.path
#print axioms MWG.DynamicGames.BargainingGame.length_path
#print axioms MWG.DynamicGames.BargainingGame.path_succ
#print axioms MWG.DynamicGames.BargainingGame.Agrees
#print axioms MWG.DynamicGames.BargainingGame.value
#print axioms MWG.DynamicGames.BargainingGame.respValue
#print axioms MWG.DynamicGames.BargainingGame.value_of_exists
#print axioms MWG.DynamicGames.BargainingGame.value_of_not_exists
#print axioms MWG.DynamicGames.BargainingGame.respValue_accept
#print axioms MWG.DynamicGames.BargainingGame.respValue_reject
#print axioms MWG.DynamicGames.BargainingGame.value_of_not_live
#print axioms MWG.DynamicGames.BargainingGame.value_eq_respValue
#print axioms MWG.DynamicGames.BargainingGame.value_congr
#print axioms MWG.DynamicGames.BargainingGame.Feasible
#print axioms MWG.DynamicGames.BargainingGame.ValidHist
#print axioms MWG.DynamicGames.BargainingGame.validHist_cons
#print axioms MWG.DynamicGames.BargainingGame.share_mem
#print axioms MWG.DynamicGames.BargainingGame.share_add
#print axioms MWG.DynamicGames.BargainingGame.value_bounds
#print axioms MWG.DynamicGames.BargainingGame.IsDeviation
#print axioms MWG.DynamicGames.BargainingGame.IsSPNE
#print axioms MWG.DynamicGames.BargainingGame.setResp
#print axioms MWG.DynamicGames.BargainingGame.setProp
#print axioms MWG.DynamicGames.BargainingGame.setResp_value
#print axioms MWG.DynamicGames.BargainingGame.setProp_value
#print axioms MWG.DynamicGames.BargainingGame.setResp_isDeviation
#print axioms MWG.DynamicGames.BargainingGame.setProp_isDeviation
#print axioms MWG.DynamicGames.BargainingGame.setResp_feasible
#print axioms MWG.DynamicGames.BargainingGame.setProp_feasible
#print axioms MWG.DynamicGames.BargainingGame.accept_of_gt
#print axioms MWG.DynamicGames.BargainingGame.reject_of_lt
#print axioms MWG.DynamicGames.BargainingGame.respValue_le_value
#print axioms MWG.DynamicGames.BargainingGame.value_ge_of_isSPNE
#print axioms MWG.DynamicGames.BargainingGame.value_le_of_isSPNE
#print axioms MWG.DynamicGames.BargainingGame.value_le_of_bound
#print axioms MWG.DynamicGames.BargainingGame.strategies_determined
#print axioms MWG.DynamicGames.BargainingGame.threshold
#print axioms MWG.DynamicGames.BargainingGame.value_threshold
#print axioms MWG.DynamicGames.BargainingGame.threshold_isSPNE
#print axioms MWG.DynamicGames.BargainingGame.xstar
#print axioms MWG.DynamicGames.BargainingGame.one_sub_mul_pos
#print axioms MWG.DynamicGames.BargainingGame.xstar_add
#print axioms MWG.DynamicGames.BargainingGame.xstar_mem
#print axioms MWG.DynamicGames.BargainingGame.rubOffer
#print axioms MWG.DynamicGames.BargainingGame.rubOffer_mem
#print axioms MWG.DynamicGames.BargainingGame.live_of_top
#print axioms MWG.DynamicGames.BargainingGame.rubinstein_isSPNE
#print axioms MWG.DynamicGames.BargainingGame.spnePayoffs
#print axioms MWG.DynamicGames.BargainingGame.validHist_nil
#print axioms MWG.DynamicGames.BargainingGame.rubinstein_value
#print axioms MWG.DynamicGames.BargainingGame.exercise_9_B_12
#print axioms MWG.DynamicGames.BargainingGame.example_9_AA_2
#print axioms MWG.DynamicGames.BargainingGame.finP
#print axioms MWG.DynamicGames.BargainingGame.finP_mem
#print axioms MWG.DynamicGames.BargainingGame.finP_eq
#print axioms MWG.DynamicGames.BargainingGame.example_9_AA_1
#print axioms MWG.DynamicGames.BargainingGame.example_9_AA_1_odd
#print axioms MWG.DynamicGames.BargainingGame.example_9_AA_1_even
#print axioms MWG.DynamicGames.BargainingGame.example_9_AA_1_limit
#print axioms MWG.DynamicGames.Agent
#print axioms MWG.DynamicGames.owner
#print axioms MWG.DynamicGames.player_owner
#print axioms MWG.DynamicGames.agentForm
#print axioms MWG.DynamicGames.agentForm_player_none
#print axioms MWG.DynamicGames.agentForm_player_some
#print axioms MWG.DynamicGames.agentNF
#print axioms MWG.DynamicGames.agentPure
#print axioms MWG.DynamicGames.agentSelf
#print axioms MWG.DynamicGames.agentEquiv
#print axioms MWG.DynamicGames.agentBeh
#print axioms MWG.DynamicGames.agentProfile
#print axioms MWG.DynamicGames.assemble_agentProfile
#print axioms MWG.DynamicGames.assemble_agentProfile_apply
#print axioms MWG.DynamicGames.isBehaviorProfile_agentProfile
#print axioms MWG.DynamicGames.agentForm_noAbsentMindedness
#print axioms MWG.DynamicGames.reach_agentForm
#print axioms MWG.DynamicGames.agentNF_mixedPayoff
#print axioms MWG.DynamicGames.IsEFTHP
#print axioms MWG.DynamicGames.agent_nonempty
#print axioms MWG.DynamicGames.exists_isEFTHP
#print axioms MWG.DynamicGames.NatureFullSupport
#print axioms MWG.DynamicGames.reach_pos_of_totallyMixed
#print axioms MWG.DynamicGames.probInfo_pos
#print axioms MWG.DynamicGames.sum_bayesBelief
#print axioms MWG.DynamicGames.iEntry
#print axioms MWG.DynamicGames.entry_cons_unique
#print axioms MWG.DynamicGames.entry_cons_closed
#print axioms MWG.DynamicGames.propW
#print axioms MWG.DynamicGames.propagate_consistent
#print axioms MWG.DynamicGames.oneShot_consistent
#print axioms MWG.DynamicGames.tendsto_cont
#print axioms MWG.DynamicGames.entryNodes_single
#print axioms MWG.DynamicGames.cont_update_dirac
#print axioms MWG.DynamicGames.cont_update_dirac_sub
#print axioms MWG.DynamicGames.assemble_agentProfile_update
#print axioms MWG.DynamicGames.isSequentialEq_of_isEFTHP
#print axioms MWG.DynamicGames.exists_isSequentialEq
#print axioms MWG.DynamicGames.isSPNE_of_isEFTHP
#print axioms MWG.DynamicGames.exercise_9_B_8
#print axioms MWG.DynamicGames.pureMoves
#print axioms MWG.DynamicGames.isBehaviorProfile_pureMoves
#print axioms MWG.DynamicGames.entryPay
#print axioms MWG.DynamicGames.entryGame
#print axioms MWG.DynamicGames.entryGame_nodes
#print axioms MWG.DynamicGames.entryGame_info
#print axioms MWG.DynamicGames.entryGame_avail
#print axioms MWG.DynamicGames.entryGame_player
#print axioms MWG.DynamicGames.entryGame_payoff
#print axioms MWG.DynamicGames.entryGame_assemble
#print axioms MWG.DynamicGames.entryGame_cont
#print axioms MWG.DynamicGames.example_9_B_1_perfectInformation
#print axioms MWG.DynamicGames.example_9_B_1_nash
#print axioms MWG.DynamicGames.entryGame_decisionNodes
#print axioms MWG.DynamicGames.entryGame_terminals
#print axioms MWG.DynamicGames.example_9_B_1_subgames
#print axioms MWG.DynamicGames.example_9_B_1_not_spne
#print axioms MWG.DynamicGames.example_9_B_1_spne
#print axioms MWG.DynamicGames.entryTwoPay
#print axioms MWG.DynamicGames.entryTwo
#print axioms MWG.DynamicGames.entryTwo_assemble
#print axioms MWG.DynamicGames.entryTwo_cont
#print axioms MWG.DynamicGames.entryTwo_infoSet
#print axioms MWG.DynamicGames.entryTwo_condPayoff
#print axioms MWG.DynamicGames.entryTwo_reach
#print axioms MWG.DynamicGames.entryTwo_behavior
#print axioms MWG.DynamicGames.entryTwo_dirac_beh
#print axioms MWG.DynamicGames.fig9C1
#print axioms MWG.DynamicGames.entryTwo_beh0
#print axioms MWG.DynamicGames.entryTwo_beh1
#print axioms MWG.DynamicGames.entryTwo_subgames
#print axioms MWG.DynamicGames.example_9_C_1_nash
#print axioms MWG.DynamicGames.example_9_C_1_spne
#print axioms MWG.DynamicGames.leftBelief
#print axioms MWG.DynamicGames.example_9_C_1_weakPBE
#print axioms MWG.DynamicGames.entryTwo_weakPBE_facts
#print axioms MWG.DynamicGames.fig9C3
#print axioms MWG.DynamicGames.fig9C3_acc
#print axioms MWG.DynamicGames.fig9C3_fight
#print axioms MWG.DynamicGames.fig9C3_best
#print axioms MWG.DynamicGames.fig9C3_scalar
#print axioms MWG.DynamicGames.example_9_C_3_unique
#print axioms MWG.DynamicGames.entryTwo_weakPBE_of
#print axioms MWG.DynamicGames.fig9C3Profile
#print axioms MWG.DynamicGames.fig9C3Belief
#print axioms MWG.DynamicGames.example_9_C_3_exists
#print axioms MWG.DynamicGames.exercise_9_C_2
#print axioms MWG.DynamicGames.exercise_9_C_2_exists
#print axioms MWG.DynamicGames.fig9D1a
#print axioms MWG.DynamicGames.figure_9_D_1a
#print axioms MWG.DynamicGames.entrySimPay
#print axioms MWG.DynamicGames.entrySimInfo
#print axioms MWG.DynamicGames.entrySim
#print axioms MWG.DynamicGames.entrySim_assemble
#print axioms MWG.DynamicGames.entrySim_cont
#print axioms MWG.DynamicGames.entrySim_decisionNodes
#print axioms MWG.DynamicGames.entrySim_subgames
#print axioms MWG.DynamicGames.entrySim_beh
#print axioms MWG.DynamicGames.fig9B4
#print axioms MWG.DynamicGames.example_9_B_3_nash
#print axioms MWG.DynamicGames.example_9_B_3_spne
#print axioms MWG.DynamicGames.entrySim_infoSet
#print axioms MWG.DynamicGames.entrySim_reach
#print axioms MWG.DynamicGames.fin3_cases
#print axioms MWG.DynamicGames.entrySim_perfectRecall
#print axioms MWG.DynamicGames.fightBelief
#print axioms MWG.DynamicGames.example_9_C_5
#print axioms MWG.DynamicGames.nicheGame
#print axioms MWG.DynamicGames.example_9_B_4
#print axioms MWG.DynamicGames.nicheMixed
#print axioms MWG.DynamicGames.exercise_9_B_6
#print axioms MWG.DynamicGames.figure_9_D_3
#print axioms MWG.DynamicGames.threeInfo
#print axioms MWG.DynamicGames.threePayZ
#print axioms MWG.DynamicGames.threeGame
#print axioms MWG.DynamicGames.threeGame_nodes
#print axioms MWG.DynamicGames.threeGame_info
#print axioms MWG.DynamicGames.threeGame_avail
#print axioms MWG.DynamicGames.threeGame_payoff
#print axioms MWG.DynamicGames.threeOutcome
#print axioms MWG.DynamicGames.two_cases
#print axioms MWG.DynamicGames.threeGame_cont_pure
#print axioms MWG.DynamicGames.IsPureNash3
#print axioms MWG.DynamicGames.threeBI
#print axioms MWG.DynamicGames.exercise_9_B_3_nash
#print axioms MWG.DynamicGames.example_9_B_2
#print axioms MWG.DynamicGames.exercise_9_B_1
#print axioms MWG.DynamicGames.exercise_9_B_3
#print axioms MWG.DynamicGames.proposition_9_B_3_instance
#print axioms MWG.DynamicGames.example_9_C_1_bayes
#print axioms MWG.DynamicGames.fig9D1b
#print axioms MWG.DynamicGames.figure_9_D_1b
#print axioms MWG.DynamicGames.exercise_9_B_5b
#print axioms MWG.DynamicGames.exercise_9_B_4_instance
#print axioms MWG.DynamicGames.bargainHalf
#print axioms MWG.DynamicGames.example_9_AA_2_instance
#print axioms MWG.DynamicGames.example_9_AA_1_instance
#print axioms MWG.DynamicGames.assemble_pureB_pureOfChoice
#print axioms MWG.DynamicGames.naturePay
#print axioms MWG.DynamicGames.natureGame
#print axioms MWG.DynamicGames.natureGame_perfectInformation
#print axioms MWG.DynamicGames.natureGame_cont
#print axioms MWG.DynamicGames.natureGame_terminals
#print axioms MWG.DynamicGames.natureGame_decisionNodes
#print axioms MWG.DynamicGames.natureGame_payoff_injective
#print axioms MWG.DynamicGames.natureGame_oneShot
#print axioms MWG.DynamicGames.proposition_9_B_2_nature_counterexample
#print axioms MWG.DynamicGames.proposition_9_B_1_nature_counterexample
#print axioms MWG.DynamicGames.zeroSum3Pay
#print axioms MWG.DynamicGames.zeroSum3Game
#print axioms MWG.DynamicGames.zeroSum3Game_cont
#print axioms MWG.DynamicGames.exercise_9_B_4_three_player_counterexample
#print axioms MWG.DynamicGames.centMover
#print axioms MWG.DynamicGames.centPile
#print axioms MWG.DynamicGames.centPile_succ_mover
#print axioms MWG.DynamicGames.centPile_succ
#print axioms MWG.DynamicGames.centPile_even
#print axioms MWG.DynamicGames.centPile_odd
#print axioms MWG.DynamicGames.example_9_B_5_payoffs
#print axioms MWG.DynamicGames.centNodes
#print axioms MWG.DynamicGames.mem_centNodes
#print axioms MWG.DynamicGames.zero_cons_ne_replicate
#print axioms MWG.DynamicGames.cons_mem_centNodes
#print axioms MWG.DynamicGames.centipede
#print axioms MWG.DynamicGames.centipede_isDecision
#print axioms MWG.DynamicGames.centipede_info
#print axioms MWG.DynamicGames.centipede_isDecision_iff
#print axioms MWG.DynamicGames.centipede_cont_stop
#print axioms MWG.DynamicGames.centipede_cont_end
#print axioms MWG.DynamicGames.centipede_cont_decision
#print axioms MWG.DynamicGames.centipede_step
#print axioms MWG.DynamicGames.centipede_cont_stopAll
#print axioms MWG.DynamicGames.example_9_B_5
#print axioms MWG.DynamicGames.example_9_B_5_ties
#print axioms MWG.DynamicGames.jvPay
#print axioms MWG.DynamicGames.jvInfo
#print axioms MWG.DynamicGames.jvGame
#print axioms MWG.DynamicGames.jvGame_cont
#print axioms MWG.DynamicGames.jvGame_infoSet
#print axioms MWG.DynamicGames.jvGame_assemble
#print axioms MWG.DynamicGames.jvGame_assemble_eq
#print axioms MWG.DynamicGames.jvGame_condPayoff
#print axioms MWG.DynamicGames.jvGame_beh_update
#print axioms MWG.DynamicGames.jvGame_behavior
#print axioms MWG.DynamicGames.jvGame_reach
#print axioms MWG.DynamicGames.jvGame_probInfo
#print axioms MWG.DynamicGames.jvBelief
#print axioms MWG.DynamicGames.example_9_C_2_weakPBE
#print axioms MWG.DynamicGames.jvGame_subgames
#print axioms MWG.DynamicGames.example_9_C_2_spne
#print axioms MWG.DynamicGames.ncPay
#print axioms MWG.DynamicGames.ncGame
#print axioms MWG.DynamicGames.ncGame_assemble
#print axioms MWG.DynamicGames.ncGame_cont
#print axioms MWG.DynamicGames.ncGame_infoSet
#print axioms MWG.DynamicGames.ncGame_condPayoff
#print axioms MWG.DynamicGames.ncGame_reach
#print axioms MWG.DynamicGames.ncBelief
#print axioms MWG.DynamicGames.ncHalf
#print axioms MWG.DynamicGames.ncGame_beh
#print axioms MWG.DynamicGames.ncGame_k3
#print axioms MWG.DynamicGames.ncGame_beliefSystems
#print axioms MWG.DynamicGames.example_9_C_4_weakPBE
#print axioms MWG.DynamicGames.ncGame_bayes_half
#print axioms MWG.DynamicGames.example_9_C_4_consistent_beliefs
#print axioms MWG.DynamicGames.example_9_C_4_not_consistent
#print axioms MWG.DynamicGames.ncGame_beh_update
#print axioms MWG.DynamicGames.example_9_C_4_sequential
#print axioms MWG.DynamicGames.isEFTHP_eq_zero_of_worse
#print axioms MWG.DynamicGames.fig9BB2
#print axioms MWG.DynamicGames.entryTwo_noAbsentMindedness
#print axioms MWG.DynamicGames.entryTwo_consistent_leftBelief_zero
#print axioms MWG.DynamicGames.entryTwo_consistent_leftBelief_one
#print axioms MWG.DynamicGames.figure_9_BB_2
#print axioms MWG.DynamicGames.bb1Pay
#print axioms MWG.DynamicGames.bb1Game
#print axioms MWG.DynamicGames.bb1Game_assemble
#print axioms MWG.DynamicGames.bb1Game_cont
#print axioms MWG.DynamicGames.bb1Game_decisionNodes
#print axioms MWG.DynamicGames.bb1Game_subgames
#print axioms MWG.DynamicGames.bb1Game_perfectRecall
#print axioms MWG.DynamicGames.bb1Game_beh_update
#print axioms MWG.DynamicGames.figure_9_BB_1_spne
#print axioms MWG.DynamicGames.figure_9_BB_1_efthp
#print axioms MWG.DynamicGames.bb1U₁
#print axioms MWG.DynamicGames.bb1U₂
#print axioms MWG.DynamicGames.bb1Row
#print axioms MWG.DynamicGames.bb1_normalForm
#print axioms MWG.DynamicGames.bb1_row_two
#print axioms MWG.DynamicGames.figure_9_BB_1_normalTHP
#print axioms MWG.DynamicGames.footnote_15_D_1a
#print axioms MWG.DynamicGames.footnote_15_D_1b
#print axioms MWG.DynamicGames.fig9D2Pay
#print axioms MWG.DynamicGames.fig9D2
#print axioms MWG.DynamicGames.fig9D2_assemble
#print axioms MWG.DynamicGames.fig9D2_cont
#print axioms MWG.DynamicGames.fig9D2_infoSet
#print axioms MWG.DynamicGames.fig9D2_reach
#print axioms MWG.DynamicGames.fig9D2_condPayoff
#print axioms MWG.DynamicGames.figure_9_D_2
#print axioms MWG.DynamicGames.RHist
#print axioms MWG.DynamicGames.rsnoc
#print axioms MWG.DynamicGames.rval
#print axioms MWG.DynamicGames.IsRBehavior
#print axioms MWG.DynamicGames.IsRSPNE
#print axioms MWG.DynamicGames.rval_congr
#print axioms MWG.DynamicGames.rstage
#print axioms MWG.DynamicGames.rstage_update
#print axioms MWG.DynamicGames.rval_succ_of_const
#print axioms MWG.DynamicGames.isMixedNash_rstage_of_isRSPNE
#print axioms MWG.DynamicGames.proposition_9_B_4
#print axioms MWG.DynamicGames.pd_unique_nash
#print axioms MWG.DynamicGames.proposition_9_B_4_instance
#print axioms MWG.DynamicGames.IsMaskinSPNE
#print axioms MWG.DynamicGames.IsMaskinNash
#print axioms MWG.DynamicGames.IsMaskinSimNash
#print axioms MWG.DynamicGames.IsMaskinSPNE.isMaskinNash
#print axioms MWG.DynamicGames.exercise_9_B_5c
#print axioms MWG.DynamicGames.exercise_9_B_5d
#print axioms MWG.DynamicGames.maskinD₁
#print axioms MWG.DynamicGames.maskinD₂
#print axioms MWG.DynamicGames.maskinD₂_noTies
#print axioms MWG.DynamicGames.exercise_9_B_5d_instance
#print axioms MWG.DynamicGames.exercise_9_B_5d_nash
#print axioms MWG.DynamicGames.maskinTie₁
#print axioms MWG.DynamicGames.exercise_9_B_5e_ties
#print axioms MWG.DynamicGames.maskinMix₁
#print axioms MWG.DynamicGames.maskinMix₂
#print axioms MWG.DynamicGames.maskinMix_spne_iff
#print axioms MWG.DynamicGames.exercise_9_B_5c_instance
#print axioms MWG.DynamicGames.exercise_9_B_5e_mixed
#print axioms MWG.DynamicGames.rval_one
#print axioms MWG.DynamicGames.augGame
#print axioms MWG.DynamicGames.rval_two
#print axioms MWG.DynamicGames.isRSPNE_two_iff
#print axioms MWG.DynamicGames.rpure
#print axioms MWG.DynamicGames.isRSPNE_two_pure_iff
#print axioms MWG.DynamicGames.twU₁
#print axioms MWG.DynamicGames.twU₂
#print axioms MWG.DynamicGames.twS
#print axioms MWG.DynamicGames.tw_nash_iff
#print axioms MWG.DynamicGames.pp_inj
#print axioms MWG.DynamicGames.tw_nash_iff'
#print axioms MWG.DynamicGames.exercise_9_B_9
#print axioms MWG.DynamicGames.twProfile
#print axioms MWG.DynamicGames.rsnoc_zero
#print axioms MWG.DynamicGames.tw_payoff_cont
#print axioms MWG.DynamicGames.twProfile_isRSPNE
#print axioms MWG.DynamicGames.exercise_9_B_9_first
#print axioms MWG.DynamicGames.footnote_10
#print axioms MWG.DynamicGames.IsWDominatedIn
#print axioms MWG.DynamicGames.WDDeletionStep
#print axioms MWG.DynamicGames.OnPath
#print axioms MWG.DynamicGames.IsPureMoves
#print axioms MWG.DynamicGames.onPath_self
#print axioms MWG.DynamicGames.OnPath.mono
#print axioms MWG.DynamicGames.OnPath.cons
#print axioms MWG.DynamicGames.OnPath.trans
#print axioms MWG.DynamicGames.cont_step
#print axioms MWG.DynamicGames.cont_onPath
#print axioms MWG.DynamicGames.cont_agree
#print axioms MWG.DynamicGames.isPureMoves_pureProfile
#print axioms MWG.DynamicGames.Permits
#print axioms MWG.DynamicGames.biSets
#print axioms MWG.DynamicGames.pureProfile_eq_one_iff
#print axioms MWG.DynamicGames.permits_of_onPath
#print axioms MWG.DynamicGames.biSets_agree
#print axioms MWG.DynamicGames.cont_biSets
#print axioms MWG.DynamicGames.onPath_biSets_iff
#print axioms MWG.DynamicGames.inSub_iff_of_pi
#print axioms MWG.DynamicGames.towards
#print axioms MWG.DynamicGames.towards_on_path
#print axioms MWG.DynamicGames.towards_mem
#print axioms MWG.DynamicGames.bi_strict
#print axioms MWG.DynamicGames.biSets_mono
#print axioms MWG.DynamicGames.biSets_step
#print axioms MWG.DynamicGames.biSets_top
#print axioms MWG.DynamicGames.exercise_9_D_1
#print axioms MWG.DynamicGames.exercise_9_D_1_instance
#print axioms MWG.DynamicGames.assemble_pureMoves
#print axioms MWG.DynamicGames.IsSPNE.pure_dev
#print axioms MWG.DynamicGames.ecInfo
#print axioms MWG.DynamicGames.ecPay
#print axioms MWG.DynamicGames.ecGame
#print axioms MWG.DynamicGames.ec_noNature
#print axioms MWG.DynamicGames.ec_assemble
#print axioms MWG.DynamicGames.ec_cont
#print axioms MWG.DynamicGames.ec_cont3
#print axioms MWG.DynamicGames.ec_cont1
#print axioms MWG.DynamicGames.ec_cont0
#print axioms MWG.DynamicGames.ec_decisionNodes
#print axioms MWG.DynamicGames.ec_subgames
#print axioms MWG.DynamicGames.ec_beh
#print axioms MWG.DynamicGames.ec_spne_U
#print axioms MWG.DynamicGames.ec_spne_D
#print axioms MWG.DynamicGames.exercise_9_B_10_pure
#print axioms MWG.DynamicGames.exercise_9_B_10_neg
#print axioms MWG.DynamicGames.ecMixed
#print axioms MWG.DynamicGames.exercise_9_B_10_mixed
#print axioms MWG.DynamicGames.isPureMoves_dirac
#print axioms MWG.DynamicGames.bstep
#print axioms MWG.DynamicGames.cont_dirac_play
#print axioms MWG.DynamicGames.isSPNE_of_weak_bi
#print axioms MWG.DynamicGames.eq_dirac_of_strict_bi
#print axioms MWG.DynamicGames.dtNodesA
#print axioms MWG.DynamicGames.dtInfoA
#print axioms MWG.DynamicGames.dtPayA
#print axioms MWG.DynamicGames.deterA
#print axioms MWG.DynamicGames.dtStepA
#print axioms MWG.DynamicGames.dtA_decisionNodes
#print axioms MWG.DynamicGames.dtA_noNature
#print axioms MWG.DynamicGames.dtA_perfectInformation
#print axioms MWG.DynamicGames.dtA_cont
#print axioms MWG.DynamicGames.dtA_step
#print axioms MWG.DynamicGames.dtNodesB
#print axioms MWG.DynamicGames.dtInfoB
#print axioms MWG.DynamicGames.dtPayB
#print axioms MWG.DynamicGames.deterB
#print axioms MWG.DynamicGames.dtStepB
#print axioms MWG.DynamicGames.dtB_decisionNodes
#print axioms MWG.DynamicGames.dtB_noNature
#print axioms MWG.DynamicGames.dtB_perfectInformation
#print axioms MWG.DynamicGames.dtB_cont
#print axioms MWG.DynamicGames.dtB_step
#print axioms MWG.DynamicGames.cA
#print axioms MWG.DynamicGames.dtA_strict
#print axioms MWG.DynamicGames.cB
#print axioms MWG.DynamicGames.dtB_strict
#print axioms MWG.DynamicGames.dtB_root
#print axioms MWG.DynamicGames.dtB_after_root
#print axioms MWG.DynamicGames.exercise_9_B_14a
#print axioms MWG.DynamicGames.exercise_9_B_14b
#print axioms MWG.DynamicGames.exercise_9_B_14_instance
#print axioms MWG.DynamicGames.firstStop
#print axioms MWG.DynamicGames.firstStop_of_exists
#print axioms MWG.DynamicGames.firstStop_of_not_exists
#print axioms MWG.DynamicGames.firstStop_eq
#print axioms MWG.DynamicGames.firstStop_le
#print axioms MWG.DynamicGames.firstStop_add
#print axioms MWG.DynamicGames.OfferCostGame
#print axioms MWG.DynamicGames.OfferCostGame.mk
#print axioms MWG.DynamicGames.OfferCostGame.v
#print axioms MWG.DynamicGames.OfferCostGame.c
#print axioms MWG.DynamicGames.OfferCostGame.T
#print axioms MWG.DynamicGames.OfferCostGame.c_pos
#print axioms MWG.DynamicGames.OfferCostGame.c_lt_v
#print axioms MWG.DynamicGames.OfferCostGame.Live
#print axioms MWG.DynamicGames.OfferCostGame.share
#print axioms MWG.DynamicGames.OfferCostGame.offerCost
#print axioms MWG.DynamicGames.OfferCostGame.share_proposer
#print axioms MWG.DynamicGames.OfferCostGame.share_other
#print axioms MWG.DynamicGames.OfferCostGame.offerCost_proposer
#print axioms MWG.DynamicGames.OfferCostGame.offerCost_other
#print axioms MWG.DynamicGames.OfferCostGame.value
#print axioms MWG.DynamicGames.OfferCostGame.respValue
#print axioms MWG.DynamicGames.OfferCostGame.value_of_not_live
#print axioms MWG.DynamicGames.OfferCostGame.value_eq_respValue
#print axioms MWG.DynamicGames.OfferCostGame.respValue_accept
#print axioms MWG.DynamicGames.OfferCostGame.respValue_reject
#print axioms MWG.DynamicGames.OfferCostGame.value_congr
#print axioms MWG.DynamicGames.OfferCostGame.setResp_value
#print axioms MWG.DynamicGames.OfferCostGame.setProp_value
#print axioms MWG.DynamicGames.OfferCostGame.value_le_of_bound
#print axioms MWG.DynamicGames.OfferCostGame.Feasible
#print axioms MWG.DynamicGames.OfferCostGame.ValidHist
#print axioms MWG.DynamicGames.OfferCostGame.validHist_cons
#print axioms MWG.DynamicGames.OfferCostGame.IsSPNE
#print axioms MWG.DynamicGames.OfferCostGame.accept_of_gt
#print axioms MWG.DynamicGames.OfferCostGame.reject_of_lt
#print axioms MWG.DynamicGames.OfferCostGame.respValue_le_value
#print axioms MWG.DynamicGames.OfferCostGame.threshold
#print axioms MWG.DynamicGames.OfferCostGame.value_threshold
#print axioms MWG.DynamicGames.OfferCostGame.threshold_isSPNE
#print axioms MWG.DynamicGames.OfferCostGame.strategies_determined
#print axioms MWG.DynamicGames.OfferCostGame.value_le_feasible
#print axioms MWG.DynamicGames.OfferCostGame.offerCost_add
#print axioms MWG.DynamicGames.OfferCostGame.share_add
#print axioms MWG.DynamicGames.OfferCostGame.value_add_le
#print axioms MWG.DynamicGames.OfferCostGame.spne_bounds
#print axioms MWG.DynamicGames.OfferCostGame.W
#print axioms MWG.DynamicGames.OfferCostGame.W_zero
#print axioms MWG.DynamicGames.OfferCostGame.W_succ
#print axioms MWG.DynamicGames.OfferCostGame.W_mem
#print axioms MWG.DynamicGames.OfferCostGame.W_add_pred
#print axioms MWG.DynamicGames.OfferCostGame.live_iff
#print axioms MWG.DynamicGames.OfferCostGame.exercise_9_B_7_values
#print axioms MWG.DynamicGames.OfferCostGame.exercise_9_B_7
#print axioms MWG.DynamicGames.OfferCostGame.exercise_9_B_7_parity
#print axioms MWG.DynamicGames.OfferCostGame.exercise_9_B_7_limit
#print axioms MWG.DynamicGames.OfferCostGame.live_top
#print axioms MWG.DynamicGames.OfferCostGame.splitProfile
#print axioms MWG.DynamicGames.OfferCostGame.splitProfile_isSPNE
#print axioms MWG.DynamicGames.OfferCostGame.exercise_9_B_13
#print axioms MWG.DynamicGames.OfferCostGame.exercise_9_B_13_payoffs
#print axioms MWG.DynamicGames.OfferCostGame.exercise_9_B_13_not_unique
#print axioms MWG.DynamicGames.OfferCostGame.spne_immediate
#print axioms MWG.DynamicGames.OfferCostGame.isSPNE_of_oneStage
#print axioms MWG.DynamicGames.OfferCostGame.delayReg
#print axioms MWG.DynamicGames.OfferCostGame.delayV
#print axioms MWG.DynamicGames.OfferCostGame.delayProfile
#print axioms MWG.DynamicGames.OfferCostGame.delayV_cons
#print axioms MWG.DynamicGames.OfferCostGame.delayV_add
#print axioms MWG.DynamicGames.OfferCostGame.delayV_nil_one
#print axioms MWG.DynamicGames.OfferCostGame.delayReg_mem
#print axioms MWG.DynamicGames.OfferCostGame.delayProfile_isSPNE
#print axioms MWG.DynamicGames.OfferCostGame.exercise_9_B_13_delay
#print axioms MWG.DynamicGames.exercise_9_B_13_instance
#print axioms MWG.DynamicGames.exercise_9_B_13_delay_instance
#print axioms MWG.DynamicGames.exercise_9_B_7_instance
#print axioms MWG.DynamicGames.AttritionGame
#print axioms MWG.DynamicGames.AttritionGame.mk
#print axioms MWG.DynamicGames.AttritionGame.duo
#print axioms MWG.DynamicGames.AttritionGame.mono
#print axioms MWG.DynamicGames.AttritionProfile
#print axioms MWG.DynamicGames.AttritionProfile.mk
#print axioms MWG.DynamicGames.AttritionProfile.stay
#print axioms MWG.DynamicGames.AttritionGame.monoValue
#print axioms MWG.DynamicGames.AttritionGame.jointValue
#print axioms MWG.DynamicGames.AttritionGame.monoValue_eq
#print axioms MWG.DynamicGames.AttritionGame.stayValue
#print axioms MWG.DynamicGames.AttritionGame.jointValue_eq
#print axioms MWG.DynamicGames.AttritionGame.IsSPNE
#print axioms MWG.DynamicGames.AttritionGame.setStay
#print axioms MWG.DynamicGames.AttritionGame.setStay_other
#print axioms MWG.DynamicGames.AttritionGame.setStay_self
#print axioms MWG.DynamicGames.AttritionGame.monoValue_setStay
#print axioms MWG.DynamicGames.AttritionGame.jointValue_setStay
#print axioms MWG.DynamicGames.AttritionGame.stayValue_setStay
#print axioms MWG.DynamicGames.AttritionGame.stay_of_pos
#print axioms MWG.DynamicGames.AttritionGame.exit_of_neg
#print axioms MWG.DynamicGames.AttritionGame.monoStay_of_pos
#print axioms MWG.DynamicGames.AttritionGame.monoExit_of_neg
#print axioms MWG.DynamicGames.AttritionGame.monoValue_le
#print axioms MWG.DynamicGames.AttritionGame.monopoly_spne
#print axioms MWG.DynamicGames.AttritionGame.monoValue_cutoff
#print axioms MWG.DynamicGames.AttritionGame.jointValue_le
#print axioms MWG.DynamicGames.declining
#print axioms MWG.DynamicGames.decL
#print axioms MWG.DynamicGames.decM
#print axioms MWG.DynamicGames.decVA
#print axioms MWG.DynamicGames.decVB
#print axioms MWG.DynamicGames.attritionSPNE
#print axioms MWG.DynamicGames.decM_rec
#print axioms MWG.DynamicGames.decM_late
#print axioms MWG.DynamicGames.decM_nonneg
#print axioms MWG.DynamicGames.decMono_pos
#print axioms MWG.DynamicGames.decMono_neg
#print axioms MWG.DynamicGames.decM_hrec
#print axioms MWG.DynamicGames.exercise_9_B_11_monopoly
#print axioms MWG.DynamicGames.decVA_rec
#print axioms MWG.DynamicGames.decVB_rec
#print axioms MWG.DynamicGames.decVA_late
#print axioms MWG.DynamicGames.decVB_late
#print axioms MWG.DynamicGames.decVA_pos
#print axioms MWG.DynamicGames.decVB_pos
#print axioms MWG.DynamicGames.decM1_pos
#print axioms MWG.DynamicGames.attr_none
#print axioms MWG.DynamicGames.attr_some
#print axioms MWG.DynamicGames.dec_jv_step
#print axioms MWG.DynamicGames.decDuo_neg
#print axioms MWG.DynamicGames.decB_mid
#print axioms MWG.DynamicGames.attritionSPNE_mono
#print axioms MWG.DynamicGames.attritionSPNE_values
#print axioms MWG.DynamicGames.attritionSPNE_isSPNE
#print axioms MWG.DynamicGames.exercise_9_B_11_unique
#print axioms MWG.DynamicGames.exercise_9_B_11
#print axioms MWG.DynamicGames.bagPay
#print axioms MWG.DynamicGames.bagPayAB
#print axioms MWG.DynamicGames.bagA
#print axioms MWG.DynamicGames.bagB
#print axioms MWG.DynamicGames.bagA_cont
#print axioms MWG.DynamicGames.bagB_cont
#print axioms MWG.DynamicGames.bagA_assemble_eq
#print axioms MWG.DynamicGames.bagB_assemble_eq
#print axioms MWG.DynamicGames.bagA_behavior
#print axioms MWG.DynamicGames.bagA_beh
#print axioms MWG.DynamicGames.bagB_beh
#print axioms MWG.DynamicGames.bagA_beh_update
#print axioms MWG.DynamicGames.bagB_beh_update
#print axioms MWG.DynamicGames.bagA_payoffs
#print axioms MWG.DynamicGames.bagB_payoffs
#print axioms MWG.DynamicGames.bagA_perfectInformation
#print axioms MWG.DynamicGames.bagA_isSPNE
#print axioms MWG.DynamicGames.bagA_nash_cases
#print axioms MWG.DynamicGames.bagA_isNashB_iff
#print axioms MWG.DynamicGames.bagA_isSPNE_unique
#print axioms MWG.DynamicGames.exercise_9_C_7a
#print axioms MWG.DynamicGames.exercise_9_C_7b
#print axioms MWG.DynamicGames.bagPayC
#print axioms MWG.DynamicGames.bagNature
#print axioms MWG.DynamicGames.bagInfoC
#print axioms MWG.DynamicGames.bagCNodes
#print axioms MWG.DynamicGames.bagC
#print axioms MWG.DynamicGames.bagC_cont
#print axioms MWG.DynamicGames.bagC_infoSet
#print axioms MWG.DynamicGames.bagC_assemble
#print axioms MWG.DynamicGames.bagC_payoff0
#print axioms MWG.DynamicGames.bagC_condPayoff
#print axioms MWG.DynamicGames.bagC_reach
#print axioms MWG.DynamicGames.bagC_beh
#print axioms MWG.DynamicGames.bagC_beh_update
#print axioms MWG.DynamicGames.bagC_probInfo_pos
#print axioms MWG.DynamicGames.bagC_assemble_eq
#print axioms MWG.DynamicGames.bagC_cond3
#print axioms MWG.DynamicGames.bagC_cond4
#print axioms MWG.DynamicGames.dirac_fin2
#print axioms MWG.DynamicGames.bagC_weakPBE_facts
#print axioms MWG.DynamicGames.bagProfile
#print axioms MWG.DynamicGames.bagBelief
#print axioms MWG.DynamicGames.bagProfile_values
#print axioms MWG.DynamicGames.bagBelief_values
#print axioms MWG.DynamicGames.bagC_seq0
#print axioms MWG.DynamicGames.bagC_seq3
#print axioms MWG.DynamicGames.bagC_seq4
#print axioms MWG.DynamicGames.bagC_bayes
#print axioms MWG.DynamicGames.bagC_isWeakPBE_of
#print axioms MWG.DynamicGames.exercise_9_C_7c
#print axioms MWG.DynamicGames.bagC_weakPBE_of_T
#print axioms MWG.DynamicGames.exercise_9_C_7c_pure_unique
#print axioms MWG.DynamicGames.exercise_9_C_7c_unique
#print axioms MWG.DynamicGames.exercise_9_C_7c_mixed_high
#print axioms MWG.DynamicGames.exercise_9_C_7c_mixed_low
#print axioms MWG.DynamicGames.exercise_9_C_7c_unique_iff
#print axioms MWG.DynamicGames.sbVal
#print axioms MWG.DynamicGames.sbPrior
#print axioms MWG.DynamicGames.sbCont
#print axioms MWG.DynamicGames.sbRev
#print axioms MWG.DynamicGames.SBProfile
#print axioms MWG.DynamicGames.SBProfile.mk
#print axioms MWG.DynamicGames.SBProfile.p1
#print axioms MWG.DynamicGames.SBProfile.acc
#print axioms MWG.DynamicGames.SBProfile.p2
#print axioms MWG.DynamicGames.SBProfile.μ
#print axioms MWG.DynamicGames.sbPay
#print axioms MWG.DynamicGames.sbPost
#print axioms MWG.DynamicGames.IsSBWeakPBE
#print axioms MWG.DynamicGames.IsSBConsistent
#print axioms MWG.DynamicGames.sb_period2
#print axioms MWG.DynamicGames.sbRev_vL
#print axioms MWG.DynamicGames.sbRev_vH
#print axioms MWG.DynamicGames.sbRev_le
#print axioms MWG.DynamicGames.sb_p2_mem
#print axioms MWG.DynamicGames.sb_p2_of_lt
#print axioms MWG.DynamicGames.sbHat
#print axioms MWG.DynamicGames.sb_buyer
#print axioms MWG.DynamicGames.sbHat_mem
#print axioms MWG.DynamicGames.sbPay_le
#print axioms MWG.DynamicGames.sb_weakPBE_p2
#print axioms MWG.DynamicGames.sb_acc_mono
#print axioms MWG.DynamicGames.sb_weakPBE_outcome
#print axioms MWG.DynamicGames.sbBuild
#print axioms MWG.DynamicGames.sbBuild_acc
#print axioms MWG.DynamicGames.sbBuild_isWeakPBE
#print axioms MWG.DynamicGames.sbBuild_acc_vL
#print axioms MWG.DynamicGames.sbRev_le_vL
#print axioms MWG.DynamicGames.bool_false_of_not
#print axioms MWG.DynamicGames.exercise_9_C_3a
#print axioms MWG.DynamicGames.exercise_9_C_3a_exists
#print axioms MWG.DynamicGames.exercise_9_C_3a_examples
#print axioms MWG.DynamicGames.sbPost_eq
#print axioms MWG.DynamicGames.sbPost_tendsto
#print axioms MWG.DynamicGames.exercise_9_C_6_two_types_none
#print axioms MWG.DynamicGames.exercise_9_C_6_two_types
#print axioms MWG.DynamicGames.sbKappa
#print axioms MWG.DynamicGames.exercise_9_C_3b_cutoff
#print axioms MWG.DynamicGames.sbCut
#print axioms MWG.DynamicGames.sbUPay
#print axioms MWG.DynamicGames.sbURev
#print axioms MWG.DynamicGames.IsSBUWeakPBE
#print axioms MWG.DynamicGames.IsSBUConsistent
#print axioms MWG.DynamicGames.sb_point_mass_opt
#print axioms MWG.DynamicGames.sb_rev_bound
#print axioms MWG.DynamicGames.sbURev_opt_iff
#print axioms MWG.DynamicGames.sbRStar
#print axioms MWG.DynamicGames.sbPStar
#print axioms MWG.DynamicGames.sb_consistent_r
#print axioms MWG.DynamicGames.sbUPay_nonpos
#print axioms MWG.DynamicGames.sbUPay_value
#print axioms MWG.DynamicGames.sbG_le
#print axioms MWG.DynamicGames.sbRStar_cut
#print axioms MWG.DynamicGames.exercise_9_C_3b
#print axioms MWG.DynamicGames.exercise_9_C_3b_not_unique
#print axioms MWG.DynamicGames.SetBR
#print axioms MWG.DynamicGames.setPay
#print axioms MWG.DynamicGames.IsSetWeakPBE
#print axioms MWG.DynamicGames.setV
#print axioms MWG.DynamicGames.setM
#print axioms MWG.DynamicGames.setPay_eq_setV
#print axioms MWG.DynamicGames.exercise_9_C_4a
#print axioms MWG.DynamicGames.integrable_min
#print axioms MWG.DynamicGames.setV_eq
#print axioms MWG.DynamicGames.setTrial_eq
#print axioms MWG.DynamicGames.setM_facts
#print axioms MWG.DynamicGames.setG_zero
#print axioms MWG.DynamicGames.setV_of_le
#print axioms MWG.DynamicGames.setOffer_ge
#print axioms MWG.DynamicGames.setV_thr
#print axioms MWG.DynamicGames.setTrial_anti
#print axioms MWG.DynamicGames.exercise_9_C_4b
#print axioms MWG.DynamicGames.exercise_9_C_4b_payoff
#print axioms MWG.DynamicGames.unifPrior
#print axioms MWG.DynamicGames.unifPrior_isProbabilityMeasure
#print axioms MWG.DynamicGames.unifPrior_supp
#print axioms MWG.DynamicGames.setAccBR
#print axioms MWG.DynamicGames.setAccBR_BR
#print axioms MWG.DynamicGames.exercise_9_C_4_uniform
#print axioms MWG.DynamicGames.integrable_id_of_supp
#print axioms MWG.DynamicGames.integral_trial
#print axioms MWG.DynamicGames.setIntegral_lower_le
#print axioms MWG.DynamicGames.SetCProfile
#print axioms MWG.DynamicGames.SetCProfile.mk
#print axioms MWG.DynamicGames.SetCProfile.s
#print axioms MWG.DynamicGames.SetCProfile.acc
#print axioms MWG.DynamicGames.SetCProfile.court
#print axioms MWG.DynamicGames.SetCProfile.ν
#print axioms MWG.DynamicGames.setCPay
#print axioms MWG.DynamicGames.IsSetCWeakPBE
#print axioms MWG.DynamicGames.exercise_9_C_4c_no_trial
#print axioms MWG.DynamicGames.setDrop
#print axioms MWG.DynamicGames.exercise_9_C_4c_drop
#print axioms MWG.DynamicGames.setSettle
#print axioms MWG.DynamicGames.exercise_9_C_4c_settle
#print axioms MWG.DynamicGames.set5Pay
#print axioms MWG.DynamicGames.set5Pay_acc
#print axioms MWG.DynamicGames.set5Pay_rej
#print axioms MWG.DynamicGames.Set5Profile
#print axioms MWG.DynamicGames.Set5Profile.mk
#print axioms MWG.DynamicGames.Set5Profile.σ
#print axioms MWG.DynamicGames.Set5Profile.acc
#print axioms MWG.DynamicGames.Set5Profile.ν
#print axioms MWG.DynamicGames.IsSet5WeakPBE
#print axioms MWG.DynamicGames.mean_mem_Icc
#print axioms MWG.DynamicGames.set5_acc_facts
#print axioms MWG.DynamicGames.exercise_9_C_5
#print axioms MWG.DynamicGames.set5Pool
#print axioms MWG.DynamicGames.exercise_9_C_5_pooling
#print axioms MWG.DynamicGames.set5Passive
#print axioms MWG.DynamicGames.exercise_9_C_5_passive
#print axioms MWG.DynamicGames.condOrZero
#print axioms MWG.DynamicGames.condOrZero_facts
#print axioms MWG.DynamicGames.set5Semi
#print axioms MWG.DynamicGames.exercise_9_C_5_semi
#print axioms MWG.DynamicGames.IsSetCConsistent
#print axioms MWG.DynamicGames.exercise_9_C_6_settlement
#print axioms MWG.DynamicGames.exercise_9_C_4c_5_examples
#print axioms MWG.DynamicGames.isEFTHP_pureMoves_of
#print axioms MWG.DynamicGames.fwdTremble
#print axioms MWG.DynamicGames.fwdTremble_pos
#print axioms MWG.DynamicGames.fwdTremble_le
#print axioms MWG.DynamicGames.tendsto_fwdTremble
#print axioms MWG.DynamicGames.footnote_15_D_1a_EFTHP
#print axioms MWG.DynamicGames.footnote_15_D_1b_EFTHP
#print axioms MWG.DynamicGames.footnote_15_D_2_EFTHP
#print axioms MWG.DynamicGames.sbgCut
#print axioms MWG.DynamicGames.sbgPay
#print axioms MWG.DynamicGames.sbgRev
#print axioms MWG.DynamicGames.IsSBGWeakPBE
#print axioms MWG.DynamicGames.IsSBGConsistent
#print axioms MWG.DynamicGames.sbgK
#print axioms MWG.DynamicGames.sbgR
#print axioms MWG.DynamicGames.sbgPhi
#print axioms MWG.DynamicGames.sbgMaxRev
#print axioms MWG.DynamicGames.sbgVal
#print axioms MWG.DynamicGames.sbgGIk
#print axioms MWG.DynamicGames.sbgGCk
#print axioms MWG.DynamicGames.sbgKI
#print axioms MWG.DynamicGames.sbgGI
#print axioms MWG.DynamicGames.sbgGC
#print axioms MWG.DynamicGames.sbgPI
#print axioms MWG.DynamicGames.sbgPC
#print axioms MWG.DynamicGames.sbgRev_le
#print axioms MWG.DynamicGames.sbgRev_opt_val
#print axioms MWG.DynamicGames.sbgRev_opt_iff
#print axioms MWG.DynamicGames.sbgCut_of_le
#print axioms MWG.DynamicGames.sbgCut_gt
#print axioms MWG.DynamicGames.sbg_consistent
#print axioms MWG.DynamicGames.sbgK_mem
#print axioms MWG.DynamicGames.sbgK_phi
#print axioms MWG.DynamicGames.sbgPhi_K
#print axioms MWG.DynamicGames.sbgCut_R
#print axioms MWG.DynamicGames.sbgOpt
#print axioms MWG.DynamicGames.sbgVal_corner
#print axioms MWG.DynamicGames.sbgVal_interior
#print axioms MWG.DynamicGames.sbgGC_sub
#print axioms MWG.DynamicGames.sbgGI_sub
#print axioms MWG.DynamicGames.sbgGIk_sub_sbgGCk
#print axioms MWG.DynamicGames.sbgGI_sub_sbgGC
#print axioms MWG.DynamicGames.sbgVal_le_opt
#print axioms MWG.DynamicGames.sbgPay_low
#print axioms MWG.DynamicGames.sbgPay_cons
#print axioms MWG.DynamicGames.sbgPhi_cand
#print axioms MWG.DynamicGames.sbg_cand_valid
#print axioms MWG.DynamicGames.sbgKI_mem
#print axioms MWG.DynamicGames.exercise_9_C_3b_general
#print axioms MWG.DynamicGames.exercise_9_C_3b_general_outcomes
#print axioms MWG.DynamicGames.exercise_9_C_3b_general_exists
#print axioms MWG.DynamicGames.isSBGWeakPBE_zero_one_iff
#print axioms MWG.DynamicGames.exercise_9_C_3b_general_examples
#print axioms MWG.DynamicGames.OSHist
#print axioms MWG.DynamicGames.OSProfile
#print axioms MWG.DynamicGames.osPlay
#print axioms MWG.DynamicGames.osPath
#print axioms MWG.DynamicGames.osValue
#print axioms MWG.DynamicGames.osPath_length
#print axioms MWG.DynamicGames.osValue_summable
#print axioms MWG.DynamicGames.osValue_abs_le
#print axioms MWG.DynamicGames.osValue_succ
#print axioms MWG.DynamicGames.osPlay_update
#print axioms MWG.DynamicGames.osValue_congr
#print axioms MWG.DynamicGames.oneShot_deviation_principle_discounted
#print axioms MWG.DynamicGames.oneShot_deviation_principle_discounted_iff
#print axioms MWG.DynamicGames.pdStage
#print axioms MWG.DynamicGames.pdClean
#print axioms MWG.DynamicGames.grimTrigger
#print axioms MWG.DynamicGames.pdU
#print axioms MWG.DynamicGames.pdU_bound
#print axioms MWG.DynamicGames.grim_value_clean
#print axioms MWG.DynamicGames.grim_value_dirty
#print axioms MWG.DynamicGames.grim_trigger_spe_iff
#print axioms MWG.DynamicGames.signal_belief_consistent
#print axioms MWG.DynamicGames.signal_belief_consistent_instance
