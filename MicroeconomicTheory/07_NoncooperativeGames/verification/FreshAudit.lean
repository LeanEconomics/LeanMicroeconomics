import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Fintype.Option
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.OfFn
set_option autoImplicit false

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The extensive form representation of a game

MWG, Section 7.C, pp. 221-228. A finite game in extensive form

  `Γ_E = {𝒳, 𝒜, I, p(·), α(·), ℋ, H(·), ι(·), ρ(·), u}`

is represented here with its game tree given by **histories**: a node is the list of actions
that leads to it from the initial node, listed with the MOST RECENT action FIRST. So the
initial node `x₀` is `[]`, the immediate predecessor `p(x)` of a node `a :: x` is `x`, the
action `α(a :: x)` leading to it is `a`, and the immediate successors of `x` are the nodes
`a :: x`. The set of nodes is a finite set of histories that contains `[]` and is closed under
`List.tail`. The tree requirements in MWG item (ii) (a unique immediate predecessor, a unique
initial node, predecessors and successors disjoint) and item (iii) (distinct successors are
reached by distinct actions) then hold by construction; they are proved below
(`extensive_tree_disjoint`, `extensive_successor_actions_distinct`), and the module
`MWGNoncooperativeGames.GameTree` shows that MWG's abstract trees (items (i)-(iii) with an
arbitrary finite node set) are exactly these history trees up to relabelling.

Information sets are labels `k : H`; `info x` is the information set `H(x)` of a decision node
`x`. `avail k` is the choice set `C(k)`; the requirement of item (iv) that all nodes of one
information set have the same choices is the field `avail_spec`. `player k : Option I` is
`ι(k)`, with `none` standing for nature (MWG's player `0`), and `natureProb` is item (vi).
Payoffs `payoff i z` (item (vii)) are read at terminal nodes.

Main declarations: `ExtensiveForm`, `IsDecision`, `IsTerminal`, `IsPred`,
`PerfectInformation` (Definition 7.C.1), `NoAbsentMindedness`, `RecallFor`, `PerfectRecall`
(footnote 1, p. 224), and the partition of decision nodes into information sets
(`infoSet_partition`).
-/

namespace MWG.NoncooperativeGames

/-- **Section 7.C, items (i)-(vii)** (MWG, p. 227). A finite game in extensive form with
players `I`, actions `A` and information-set labels `H`. Nodes are histories (most recent
action first); `info`, `avail`, `player`, `natureProb` and `payoff` are `H(·)`, `C(·)`, `ι(·)`,
`ρ(·)` and `u`. Values of `info` off the decision nodes are irrelevant. -/
structure ExtensiveForm (I A H : Type*) where
  /-- The finite set of nodes `𝒳`, as histories. -/
  nodes : Finset (List A)
  /-- The initial node `x₀` is the empty history. -/
  nil_mem : [] ∈ nodes
  /-- The immediate predecessor of a node is a node. -/
  tail_mem : ∀ x ∈ nodes, x.tail ∈ nodes
  /-- The information set `H(x)` of a decision node. -/
  info : List A → H
  /-- The choices `C(k)` available at information set `k`. -/
  avail : H → Finset A
  /-- Item (iv): the choices at a decision node are those of its information set. -/
  avail_spec : ∀ x ∈ nodes, (∃ b, b :: x ∈ nodes) → ∀ a, a :: x ∈ nodes ↔ a ∈ avail (info x)
  /-- Every information set contains a decision node. -/
  info_surj : ∀ k, ∃ x ∈ nodes, (∃ b, b :: x ∈ nodes) ∧ info x = k
  /-- Item (v): the player moving at an information set (`none` is nature). -/
  player : H → Option I
  /-- Item (vi): nature's probabilities. -/
  natureProb : H → A → ℝ
  nature_nonneg : ∀ k, player k = none → ∀ a, 0 ≤ natureProb k a
  nature_zero : ∀ k, player k = none → ∀ a, a ∉ avail k → natureProb k a = 0
  nature_sum : ∀ k, player k = none → ∑ a ∈ avail k, natureProb k a = 1
  /-- Item (vii): the Bernoulli payoffs `u_i`, read at terminal nodes. -/
  payoff : I → List A → ℝ

namespace ExtensiveForm

variable {I A H : Type*} (G : ExtensiveForm I A H)

/-- A decision node: a node with at least one immediate successor (MWG, p. 227). -/
def IsDecision (x : List A) : Prop := x ∈ G.nodes ∧ ∃ b, b :: x ∈ G.nodes

/-- A terminal node: a node with no immediate successor, `s(x) = ∅` (MWG, p. 227). -/
def IsTerminal (x : List A) : Prop := x ∈ G.nodes ∧ ∀ b, b :: x ∉ G.nodes

/-- `y` is a (not necessarily immediate) strict predecessor of `x` (MWG, p. 227). -/
def IsPred (y x : List A) : Prop := y <:+ x ∧ y ≠ x

/-- The immediate predecessor of a node is a node. -/
theorem mem_of_cons_mem {a : A} {x : List A} (h : a :: x ∈ G.nodes) : x ∈ G.nodes :=
  G.tail_mem _ h

/-- Every predecessor of a node is a node. -/
theorem mem_of_suffix {y x : List A} (hyx : y <:+ x) (hx : x ∈ G.nodes) : y ∈ G.nodes := by
  obtain ⟨t, rfl⟩ := hyx
  induction t with
  | nil => simpa using hx
  | cons b t ih => exact ih (G.mem_of_cons_mem hx)

/-- A node with a successor is a decision node. -/
theorem isDecision_of_cons_mem {a : A} {x : List A} (h : a :: x ∈ G.nodes) :
    G.IsDecision x :=
  ⟨G.mem_of_cons_mem h, a, h⟩

/-- Every node is either a decision node or a terminal node, and not both. -/
theorem isDecision_or_isTerminal {x : List A} (hx : x ∈ G.nodes) :
    (G.IsDecision x ∨ G.IsTerminal x) ∧ ¬ (G.IsDecision x ∧ G.IsTerminal x) := by
  refine ⟨?_, fun ⟨⟨_, b, hb⟩, _, ht⟩ => ht b hb⟩
  by_cases h : ∃ b, b :: x ∈ G.nodes
  · exact Or.inl ⟨hx, h⟩
  · exact Or.inr ⟨hx, fun b hb => h ⟨b, hb⟩⟩

/-- The action leading to a successor is available at the information set of its
predecessor. -/
theorem mem_avail_of_cons_mem {a : A} {x : List A} (h : a :: x ∈ G.nodes) :
    a ∈ G.avail (G.info x) :=
  (G.avail_spec x (G.mem_of_cons_mem h) ⟨a, h⟩ a).1 h

/-- At a decision node every available action leads to a node. -/
theorem cons_mem_of_mem_avail {a : A} {x : List A} (hx : G.IsDecision x)
    (ha : a ∈ G.avail (G.info x)) : a :: x ∈ G.nodes :=
  (G.avail_spec x hx.1 hx.2 a).2 ha

/-- Every information set has a nonempty choice set. -/
theorem avail_nonempty (k : H) : (G.avail k).Nonempty := by
  obtain ⟨x, hx, ⟨b, hb⟩, rfl⟩ := G.info_surj k
  exact ⟨b, G.mem_avail_of_cons_mem hb⟩

/-- **Section 7.C, item (iv)** (MWG, p. 227). Decision nodes in one information set have the
same choices: `c(x) = c(x')` whenever `H(x) = H(x')`. -/
theorem choices_eq_of_info_eq {x x' : List A} (hx : G.IsDecision x) (hx' : G.IsDecision x')
    (h : G.info x = G.info x') (a : A) : a :: x ∈ G.nodes ↔ a :: x' ∈ G.nodes := by
  rw [G.avail_spec x hx.1 hx.2, G.avail_spec x' hx'.1 hx'.2, h]

/-- **Section 7.C, item (ii)** (MWG, p. 227). The tree property: no node is both a strict
predecessor and a strict successor of another node. -/
theorem extensive_tree_disjoint (x y : List A) : ¬ (IsPred y x ∧ IsPred x y) := by
  rintro ⟨⟨h1, h2⟩, h3, -⟩
  exact h2 (List.IsSuffix.eq_of_length h1 (le_antisymm h1.length_le h3.length_le))

/-- **Section 7.C, item (ii)** (MWG, p. 227). The initial node is the only node without an
immediate predecessor, and it is a predecessor of every node. -/
theorem extensive_initial_node (x : List A) : ([] : List A) <:+ x :=
  List.nil_suffix

/-- **Section 7.C, item (iii)** (MWG, p. 227). Distinct immediate successors of a node are
reached by distinct actions. -/
theorem extensive_successor_actions_distinct {x : List A} {a b : A} (h : a :: x ≠ b :: x) :
    a ≠ b := fun hab => h (by rw [hab])

/-- Two predecessors of the same node with equal length coincide (the path from the initial
node to a node is unique, MWG Example 7.C.1, p. 222). -/
theorem suffix_unique {y y' x : List A} (h : y <:+ x) (h' : y' <:+ x)
    (hl : y.length = y'.length) : y = y' :=
  List.IsSuffix.eq_of_length (List.suffix_of_suffix_length_le h h' hl.le) hl

/-- A strict predecessor `y` of `x` is followed on the path to `x` by some action `b`, i.e.
`b :: y` is a predecessor of `x`. -/
theorem exists_cons_suffix {y x : List A} (h : y <:+ x) (hne : y ≠ x) :
    ∃ b, b :: y <:+ x := by
  obtain ⟨t, rfl⟩ := h
  have ht : t ≠ [] := by
    rintro rfl
    exact hne rfl
  refine ⟨t.getLast ht, t.dropLast, ?_⟩
  conv_rhs => rw [← List.dropLast_append_getLast ht]
  simp

/-- **Definition 7.C.1** (MWG, p. 226). A game of perfect information: every information set
contains a single decision node. -/
def PerfectInformation : Prop :=
  ∀ x ∈ G.nodes, ∀ x' ∈ G.nodes, (∃ b, b :: x ∈ G.nodes) → (∃ b, b :: x' ∈ G.nodes) →
    G.info x = G.info x' → x = x'

/-- **Footnote 1, condition (i)** (MWG, p. 224). If `H(x) = H(x')` then `x` is not a strict
predecessor of `x'` (no information set is crossed twice on a path). -/
def NoAbsentMindedness : Prop :=
  ∀ x ∈ G.nodes, ∀ x' ∈ G.nodes, (∃ b, b :: x ∈ G.nodes) → (∃ b, b :: x' ∈ G.nodes) →
    G.info x = G.info x' → ¬ (x <:+ x' ∧ x ≠ x')

/-- **Footnote 1, condition (ii)** (MWG, p. 224), for player `i`. If `x, x'` are decision nodes
of player `i` with `H(x) = H(x')`, and `y` is a predecessor of `x` in one of player `i`'s
information sets, with `a` the action taken at `y` on the path to `x`, then some predecessor
`y'` of `x'` lies in `H(y)` and the action taken there on the path to `x'` is also `a`. -/
def RecallFor (i : I) : Prop :=
  ∀ x ∈ G.nodes, ∀ x' ∈ G.nodes, (∃ b, b :: x ∈ G.nodes) → (∃ b, b :: x' ∈ G.nodes) →
    G.player (G.info x) = some i → G.info x = G.info x' →
    ∀ y ∈ G.nodes, ∀ a, a :: y <:+ x → G.player (G.info y) = some i →
      ∃ y' ∈ G.nodes, a :: y' <:+ x' ∧ G.info y' = G.info y

/-- **Footnote 1** (MWG, p. 224). Perfect recall: conditions (i) and (ii) (the latter for
every player). -/
def PerfectRecall : Prop := G.NoAbsentMindedness ∧ ∀ i, G.RecallFor i

/-- Under condition (i), a predecessor of a decision node `x` never lies in `H(x)`. -/
theorem info_ne_of_cons_suffix (hG : G.NoAbsentMindedness) {x y : List A} {a : A}
    (hx : G.IsDecision x) (hy : a :: y <:+ x) : G.info y ≠ G.info x := by
  intro he
  have hyx : y <:+ x := (List.suffix_cons a y).trans hy
  have hyn : y ≠ x := by
    rintro rfl
    have := hy.length_le
    simp at this
  exact hG y (G.mem_of_suffix hyx hx.1) x hx.1 ⟨a, G.mem_of_suffix hy hx.1⟩ hx.2 he
    ⟨hyx, hyn⟩

/-- Perfect information implies perfect recall condition (i). -/
theorem noAbsentMindedness_of_perfectInformation (hG : G.PerfectInformation) :
    G.NoAbsentMindedness := fun x hx x' hx' hb hb' he h => h.2 (hG x hx x' hx' hb hb' he)

/-- Perfect information implies perfect recall condition (ii): the node `x'` is `x` itself. -/
theorem recallFor_of_perfectInformation (hG : G.PerfectInformation) (i : I) :
    G.RecallFor i := by
  intro x hx x' hx' hb hb' _ he y hy a hya _
  obtain rfl := hG x hx x' hx' hb hb' he
  exact ⟨y, hy, hya, rfl⟩

/-- Games of perfect information have perfect recall. -/
theorem perfectRecall_of_perfectInformation (hG : G.PerfectInformation) :
    G.PerfectRecall :=
  ⟨G.noAbsentMindedness_of_perfectInformation hG, G.recallFor_of_perfectInformation hG⟩

variable [DecidableEq A] [Fintype A] [DecidableEq H]

/-- The decision nodes of `G`, `𝒳 \ T`. -/
def decisionNodes : Finset (List A) := G.nodes.filter fun x => ∃ b, b :: x ∈ G.nodes

/-- The terminal nodes `T = {x ∈ 𝒳 : s(x) = ∅}` (MWG, p. 227). -/
def terminals : Finset (List A) := G.nodes.filter fun x => ∀ b, b :: x ∉ G.nodes

/-- The immediate successors `s(x) = p⁻¹(x)` of a node (MWG, p. 227). -/
def successors (x : List A) : Finset (List A) := G.nodes.filter fun y => y.tail = x ∧ y ≠ []

/-- The information set labelled `k`, as a set of decision nodes. -/
def infoSet (k : H) : Finset (List A) := G.decisionNodes.filter fun x => G.info x = k

omit [DecidableEq H] in
theorem mem_terminals {z : List A} : z ∈ G.terminals ↔ G.IsTerminal z := by
  simp [terminals, IsTerminal]

omit [DecidableEq H] in
theorem mem_decisionNodes {x : List A} : x ∈ G.decisionNodes ↔ G.IsDecision x := by
  simp [decisionNodes, IsDecision]

omit [Fintype A] [DecidableEq H] in
/-- The immediate successors of `x` are exactly the nodes `a :: x`. -/
theorem mem_successors {x y : List A} :
    y ∈ G.successors x ↔ ∃ a, y = a :: x ∧ a :: x ∈ G.nodes := by
  simp only [successors, Finset.mem_filter]
  constructor
  · rintro ⟨hy, ht, hne⟩
    cases y with
    | nil => exact absurd rfl hne
    | cons a y => exact ⟨a, by simp_all⟩
  · rintro ⟨a, rfl, h⟩
    exact ⟨h, rfl, List.cons_ne_nil a x⟩

/-- **Section 7.C, item (iv)** (MWG, p. 227). The information sets form a partition of the
decision nodes: each is nonempty, each decision node lies in exactly one of them. -/
theorem infoSet_partition :
    (∀ k, (G.infoSet k).Nonempty) ∧
    ∀ x, G.IsDecision x → ∃! k, x ∈ G.infoSet k := by
  refine ⟨fun k => ?_, fun x hx => ⟨G.info x, ?_, fun k hk => ?_⟩⟩
  · obtain ⟨x, hx, hb, rfl⟩ := G.info_surj k
    exact ⟨x, by simp [infoSet, decisionNodes, hx, hb]⟩
  · simp [infoSet, decisionNodes, hx.1, hx.2]
  · simp only [infoSet, Finset.mem_filter] at hk
    exact hk.2.symm

end ExtensiveForm

end MWG.NoncooperativeGames

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# MWG's abstract game trees are history trees

MWG, Section 7.C, items (i)-(iii), p. 227. MWG define a game tree on an abstract finite set
of nodes `𝒳` by an immediate-predecessor function `p : 𝒳 → 𝒳 ∪ {∅}`, empty only at the
initial node `x₀`, such that no node is its own (iterated) predecessor, and an action function
`α` on non-initial nodes with distinct actions leading to distinct immediate successors of the
same node. `GameTree X A` records exactly these data (`act` is defined on all of `X`; its value
at `x₀` plays no role).

`ExtensiveForm` represents a tree by histories instead. This module shows the two are
interchangeable:

* `ExtensiveForm.toGameTree`: the nodes of a history tree, with `p = tail` and `α = head`,
  form a `GameTree` (`gameTree_of_history`).
* `GameTree.hist`: for every finite `GameTree`, the history of a node (actions on the path from
  `x₀`, most recent first) satisfies `hist x₀ = []` and `hist x = α(x) :: hist (p x)`
  (`hist_root`, `hist_of_pred`), is injective (`hist_injective`), and its image is a set of
  histories closed under `tail` whose successor histories correspond exactly to immediate
  successors (`historyNodes_tail_mem`, `cons_mem_historyNodes_iff`). Every MWG tree is thus a
  history tree up to relabelling its nodes.

The proof that every node is reached from `x₀` uses MWG's acyclicity and the finiteness of
`𝒳` (a pigeonhole argument, `exists_iterate_eq_root`).
-/

namespace MWG.NoncooperativeGames

/-- **Section 7.C, items (i)-(iii)** (MWG, p. 227). An abstract game tree: nodes `X`, the
initial node `root`, immediate predecessors `pred` (`none` only at the initial node), no
node is its own iterated predecessor, and actions `act` leading to the nodes, distinct for
distinct immediate successors of the same node. -/
structure GameTree (X A : Type*) where
  /-- The initial node `x₀`. -/
  root : X
  /-- The immediate predecessor `p(x)` (`none` stands for `∅`). -/
  pred : X → Option X
  pred_root : pred root = none
  pred_ne_none : ∀ x, x ≠ root → pred x ≠ none
  /-- Predecessors and successors are disjoint: no node is its own iterated predecessor. -/
  acyclic : ∀ x (n : ℕ), (fun o : Option X => o.bind pred)^[n + 1] (some x) ≠ some x
  /-- The action `α(x)` leading to `x` from `p(x)` (irrelevant at `x₀`). -/
  act : X → A
  act_inj : ∀ x x', x ≠ x' → pred x = pred x' → pred x ≠ none → act x ≠ act x'

namespace GameTree

variable {X A : Type*} (T : GameTree X A)

/-- One step up the tree, on `Option X`. -/
def up : Option X → Option X := fun o => o.bind T.pred

theorem up_iterate_none (n : ℕ) : T.up^[n] none = none :=
  Function.iterate_fixed rfl n

theorem up_iterate_root_succ (n : ℕ) : T.up^[n + 1] (some T.root) = none := by
  rw [Function.iterate_succ_apply]
  have : T.up (some T.root) = none := by simp [up, T.pred_root]
  rw [this, up_iterate_none]

/-- Iterating `p` from any node reaches the initial node (MWG's tree property, using
finiteness of `𝒳`). -/
theorem exists_iterate_eq_root [Finite X] (x : X) : ∃ n, T.up^[n] (some x) = some T.root := by
  by_contra hno
  push Not at hno
  have hsome : ∀ n, T.up^[n] (some x) ≠ none := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.1 ih
      rw [Function.iterate_succ_apply', hy]
      have hyr : y ≠ T.root := fun h => hno n (by rw [hy, h])
      simpa [up] using T.pred_ne_none y hyr
  obtain ⟨m, n, hmn, he⟩ := Finite.exists_ne_map_eq_of_infinite (fun n => T.up^[n] (some x))
  have key : ∀ m n, m < n → T.up^[m] (some x) = T.up^[n] (some x) → False := by
    intro m n hlt he
    obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.1 (hsome m)
    obtain ⟨k, rfl⟩ : ∃ k, n = (k + 1) + m := ⟨n - m - 1, by omega⟩
    rw [Function.iterate_add_apply, hy] at he
    exact T.acyclic y k he.symm
  rcases lt_or_gt_of_ne hmn with h | h
  · exact key m n h he
  · exact key n m h he.symm

/-- The time at which iterating `p` from `x` reaches `x₀` is unique. -/
theorem iterate_eq_root_unique {x : X} {m n : ℕ} (hm : T.up^[m] (some x) = some T.root)
    (hn : T.up^[n] (some x) = some T.root) : m = n := by
  by_contra hne
  have key : ∀ m n, m < n → T.up^[m] (some x) = some T.root →
      T.up^[n] (some x) = some T.root → False := by
    intro m n hlt hm hn
    obtain ⟨k, rfl⟩ : ∃ k, n = (k + 1) + m := ⟨n - m - 1, by omega⟩
    rw [Function.iterate_add_apply, hm, up_iterate_root_succ] at hn
    simp at hn
  rcases lt_or_gt_of_ne hne with h | h
  · exact key m n h hm hn
  · exact key n m h hn hm

/-- Histories with fuel: the last `n` actions on the path to `x`, most recent first. -/
def histN : ℕ → X → List A
  | 0, _ => []
  | n + 1, x =>
    match T.pred x with
    | none => []
    | some y => T.act x :: histN n y

variable [Finite X]

/-- The depth of a node: the number of steps from `x` up to `x₀`. -/
noncomputable def depth (x : X) : ℕ := (T.exists_iterate_eq_root x).choose

theorem depth_spec (x : X) : T.up^[T.depth x] (some x) = some T.root :=
  (T.exists_iterate_eq_root x).choose_spec

/-- The history of a node: the actions on the path from `x₀` to `x`, most recent first. -/
noncomputable def hist (x : X) : List A := T.histN (T.depth x) x

theorem depth_root : T.depth T.root = 0 :=
  T.iterate_eq_root_unique (T.depth_spec T.root) (by simp)

theorem depth_of_pred {x y : X} (h : T.pred x = some y) : T.depth x = T.depth y + 1 := by
  refine T.iterate_eq_root_unique (T.depth_spec x) ?_
  rw [Function.iterate_succ_apply]
  have : T.up (some x) = some y := by simp [up, h]
  rw [this, T.depth_spec]

/-- The history of the initial node is empty. -/
theorem hist_root : T.hist T.root = [] := by
  simp [hist, depth_root, histN]

/-- The history of a node is the action leading to it followed by the history of its
immediate predecessor. -/
theorem hist_of_pred {x y : X} (h : T.pred x = some y) : T.hist x = T.act x :: T.hist y := by
  simp [hist, T.depth_of_pred h, histN, h]

theorem eq_root_of_depth_zero {x : X} (h : T.depth x = 0) : x = T.root := by
  have := T.depth_spec x
  rw [h] at this
  simpa using this

theorem hist_eq_nil_iff (x : X) : T.hist x = [] ↔ x = T.root := by
  constructor
  · intro h
    by_contra hx
    obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.1 (T.pred_ne_none x hx)
    rw [T.hist_of_pred hy] at h
    exact List.cons_ne_nil _ _ h
  · rintro rfl
    exact T.hist_root

/-- **Section 7.C** (MWG, pp. 222 and 227). Distinct nodes have distinct histories: each node
is identified by the unique path from the initial node to it. -/
theorem hist_injective : Function.Injective T.hist := by
  suffices h : ∀ n, ∀ x x', T.depth x = n → T.hist x = T.hist x' → x = x' from
    fun x x' he => h _ x x' rfl he
  intro n
  induction n with
  | zero =>
    intro x x' hd he
    have hx := T.eq_root_of_depth_zero hd
    subst hx
    rw [T.hist_root, eq_comm, T.hist_eq_nil_iff] at he
    exact he.symm
  | succ n ih =>
    intro x x' hd he
    have hx : x ≠ T.root := by
      rintro rfl
      rw [depth_root] at hd
      exact Nat.noConfusion hd
    have hx' : x' ≠ T.root := by
      rintro rfl
      rw [T.hist_root, T.hist_eq_nil_iff] at he
      exact hx he
    obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.1 (T.pred_ne_none x hx)
    obtain ⟨y', hy'⟩ := Option.ne_none_iff_exists'.1 (T.pred_ne_none x' hx')
    rw [T.hist_of_pred hy, T.hist_of_pred hy'] at he
    obtain ⟨ha, hh⟩ := List.cons.inj he
    have hyy : y = y' := ih y y' (by rw [T.depth_of_pred hy] at hd; omega) hh
    subst hyy
    by_contra hne
    exact T.act_inj x x' hne (by rw [hy, hy']) (by rw [hy]; exact Option.some_ne_none y) ha

variable [Fintype X]

/-- The histories of the nodes of a finite MWG tree. -/
noncomputable def historyNodes [DecidableEq A] : Finset (List A) := Finset.univ.image T.hist

/-- The history set contains the empty history. -/
theorem nil_mem_historyNodes [DecidableEq A] : [] ∈ T.historyNodes :=
  Finset.mem_image.2 ⟨T.root, Finset.mem_univ _, T.hist_root⟩

/-- The history set is closed under taking the immediate predecessor. -/
theorem historyNodes_tail_mem [DecidableEq A] :
    ∀ h ∈ T.historyNodes, h.tail ∈ T.historyNodes := by
  intro h hh
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hh
  by_cases hx : x = T.root
  · subst hx
    rw [T.hist_root]
    exact T.nil_mem_historyNodes
  · obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.1 (T.pred_ne_none x hx)
    rw [T.hist_of_pred hy]
    exact Finset.mem_image.2 ⟨y, Finset.mem_univ _, rfl⟩

/-- **Section 7.C, items (ii)-(iii)** (MWG, p. 227). The history `a :: hist y` is a node of the
history tree exactly when some immediate successor of `y` is reached by action `a`. -/
theorem cons_mem_historyNodes_iff [DecidableEq A] (a : A) (y : X) :
    a :: T.hist y ∈ T.historyNodes ↔ ∃ x, T.pred x = some y ∧ T.act x = a := by
  constructor
  · intro h
    obtain ⟨x, -, hx⟩ := Finset.mem_image.1 h
    have hxr : x ≠ T.root := by
      rintro rfl
      rw [T.hist_root] at hx
      simp at hx
    obtain ⟨y', hy'⟩ := Option.ne_none_iff_exists'.1 (T.pred_ne_none x hxr)
    rw [T.hist_of_pred hy'] at hx
    obtain ⟨ha, hh⟩ := List.cons.inj hx
    exact ⟨x, by rw [hy', T.hist_injective hh], ha⟩
  · rintro ⟨x, hx, rfl⟩
    exact Finset.mem_image.2 ⟨x, Finset.mem_univ _, T.hist_of_pred hx⟩

end GameTree

namespace ExtensiveForm

variable {I A H : Type*} (G : ExtensiveForm I A H)

/-- The immediate predecessor of a node of a history tree. -/
def treePred (x : {x // x ∈ G.nodes}) : Option {x // x ∈ G.nodes} :=
  if x.1 = [] then none else some ⟨x.1.tail, G.tail_mem _ x.2⟩

theorem up_iterate_treePred (x : {x // x ∈ G.nodes}) (n : ℕ) :
    (fun o : Option {x // x ∈ G.nodes} => o.bind G.treePred)^[n] (some x) =
      if n ≤ x.1.length then some ⟨x.1.drop n, G.mem_of_suffix (List.drop_suffix n x.1) x.2⟩
      else none := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    by_cases hn : n + 1 ≤ x.1.length
    · rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega)), ite_eq_left_of_eq_true _ _ (eq_true hn)]
      have hne : x.1.drop n ≠ [] := by simp; omega
      simp [treePred, hne, List.tail_drop]
    · by_cases hn' : n ≤ x.1.length
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hn'), ite_eq_right_of_eq_false _ _ (eq_false hn)]
        have he : x.1.drop n = [] := by simp; omega
        simp [treePred, he]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hn'),
          ite_eq_right_of_eq_false _ _ (eq_false hn)]
        rfl

/-- **Section 7.C, items (ii)-(iii)** (MWG, p. 227). The nodes of a history tree with
`p = tail` and `α = head` form an MWG game tree (`a` is any action, used as the irrelevant
value of `α` at the initial node). -/
def toGameTree (a₀ : A) : GameTree {x // x ∈ G.nodes} A where
  root := ⟨[], G.nil_mem⟩
  pred := G.treePred
  pred_root := by simp [treePred]
  pred_ne_none := fun x hx => by
    have : x.1 ≠ [] := fun h => hx (Subtype.ext h)
    simp [treePred, this]
  acyclic := fun x n h => by
    rw [G.up_iterate_treePred] at h
    split_ifs at h with hn
    · have := congrArg (fun y => y.map (fun z => z.1.length)) h
      simp at this
      omega
  act := fun x => x.1.headD a₀
  act_inj := fun x x' hne hp hpn => by
    intro ha
    apply hne
    have hx : x.1 ≠ [] := fun h => hpn (by simp [treePred, h])
    have hx' : x'.1 ≠ [] := fun h => hpn (by rw [hp]; simp [treePred, h])
    simp only [treePred, hx, hx', ite_false, Option.some.injEq, Subtype.mk.injEq] at hp
    apply Subtype.ext
    obtain ⟨y, hy⟩ := x
    obtain ⟨y', hy'⟩ := x'
    cases y with
    | nil => exact absurd rfl hx
    | cons b t =>
      cases y' with
      | nil => exact absurd rfl hx'
      | cons b' t' =>
        simp only [List.headD_cons] at ha
        simp only [List.tail_cons] at hp
        change b :: t = b' :: t'
        rw [ha, hp]

/-- **Section 7.C** (MWG, p. 227). History trees are MWG game trees, with root `[]`,
predecessor `tail` and action `head`. -/
theorem gameTree_of_history (a₀ : A) (x : {x // x ∈ G.nodes}) (a : A) (t : List A)
    (hx : x.1 = a :: t) :
    (G.toGameTree a₀).root.1 = [] ∧
      (G.toGameTree a₀).pred x =
        some ⟨t, by have := G.tail_mem _ x.2; rw [hx] at this; exact this⟩ ∧
      (G.toGameTree a₀).act x = a := by
  refine ⟨rfl, ?_, ?_⟩
  · simp [toGameTree, treePred, hx]
  · simp [toGameTree, hx]

end ExtensiveForm

end MWG.NoncooperativeGames

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

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

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

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

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Mixed strategies as plans contingent on a private uniform signal

MWG, Section 7.E, small type on p. 232: a player can form a mixed strategy by observing a
private signal `θ` uniformly distributed on `[0, 1]` and choosing a pure strategy `s(θ)` for
each realization. `mixedStrategy_signal` proves that every mixed strategy `σ` on a finite set
`S` arises this way: `[0, 1)` (which has full measure in `[0, 1]`) splits into pairwise
disjoint measurable sets `A s`, the plan plays `s` on `A s`, and `A s` has Lebesgue measure
`σ(s)`. The sets are consecutive intervals of lengths `σ(s)`.
-/

namespace MWG.NoncooperativeGames

open MeasureTheory

/-- Partial sums `c n = ∑_{j < n} σ j` of a probability vector on `Fin M`. -/
noncomputable def signalCut {M : ℕ} (σ : Fin M → ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin M => j.val < n), σ j

theorem signalCut_zero {M : ℕ} (σ : Fin M → ℝ) : signalCut σ 0 = 0 := by
  simp [signalCut]

theorem signalCut_mono {M : ℕ} {σ : Fin M → ℝ} (hσ : ∀ j, 0 ≤ σ j) {n n' : ℕ}
    (h : n ≤ n') : signalCut σ n ≤ signalCut σ n' := by
  unfold signalCut
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun j _ _ => hσ j
  intro j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  omega

theorem signalCut_full {M : ℕ} (σ : Fin M → ℝ) : signalCut σ M = ∑ j, σ j := by
  unfold signalCut
  congr 1
  ext j
  simp

theorem signalCut_succ {M : ℕ} (σ : Fin M → ℝ) (j : Fin M) :
    signalCut σ (j.val + 1) = signalCut σ j.val + σ j := by
  unfold signalCut
  simp only [Finset.sum_filter]
  have hj : σ j = ∑ i, if i = j then σ i else 0 := by simp
  rw [hj, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : i = j
  · subst h
    simp
  · have : i.val ≠ j.val := fun he => h (Fin.ext he)
    by_cases hi : i.val < j.val
    · simp [hi, h, show i.val < j.val + 1 by omega]
    · simp [hi, h, show ¬ i.val < j.val + 1 by omega]

/-- **Section 7.E, small type** (MWG, p. 232). Every mixed strategy `σ` over a finite set `S`
can be generated from a private signal uniformly distributed on `[0, 1]`: there are pairwise
disjoint measurable sets `A s` covering `[0, 1)` with Lebesgue measure `σ(s)`, and the plan
"play `s` when `θ ∈ A s`" selects each `s` with probability `σ(s)`. -/
theorem mixedStrategy_signal {S : Type*} [Fintype S] {σ : S → ℝ} (hσ : IsMixedStrategy σ) :
    ∃ A : S → Set ℝ, (∀ s, MeasurableSet (A s)) ∧ (∀ s s', s ≠ s' → Disjoint (A s) (A s')) ∧
      (⋃ s, A s) = Set.Ico 0 1 ∧ ∀ s, volume (A s) = ENNReal.ofReal (σ s) := by
  set e := Fintype.equivFin S
  set M := Fintype.card S
  let τ : Fin M → ℝ := fun j => σ (e.symm j)
  have hτ : ∀ j, 0 ≤ τ j := fun j => hσ.1 _
  have hsum : ∑ j, τ j = 1 := by
    rw [← hσ.2]
    exact Fintype.sum_equiv e.symm _ _ fun _ => rfl
  let c := signalCut τ
  refine ⟨fun s => Set.Ico (c (e s).val) (c ((e s).val + 1)), fun s => measurableSet_Ico,
    fun s s' hne => ?_, ?_, fun s => ?_⟩
  · have hne' : (e s).val ≠ (e s').val := fun h => hne (e.injective (Fin.ext h))
    rw [Set.disjoint_left]
    rintro θ ⟨h1, h2⟩ ⟨h3, h4⟩
    rcases lt_or_gt_of_ne hne' with h | h
    · have := signalCut_mono hτ (show (e s).val + 1 ≤ (e s').val by omega)
      linarith
    · have := signalCut_mono hτ (show (e s').val + 1 ≤ (e s).val by omega)
      linarith
  · ext θ
    simp only [Set.mem_iUnion, Set.mem_Ico]
    constructor
    · rintro ⟨s, h1, h2⟩
      have h0 := signalCut_mono hτ (Nat.zero_le (e s).val)
      have hM := signalCut_mono hτ (show (e s).val + 1 ≤ M from (e s).isLt)
      rw [signalCut_zero] at h0
      rw [signalCut_full, hsum] at hM
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨h0, h1⟩
      have hex : ∃ n, θ < c (n + 1) := ⟨M, by
        have := signalCut_mono hτ (show M ≤ M + 1 by omega)
        rw [signalCut_full, hsum] at this
        linarith⟩
      let m := Nat.find hex
      have hm : θ < c (m + 1) := Nat.find_spec hex
      have hM1 : 0 < M := by
        refine Fintype.card_pos_iff.2 ?_
        by_contra hne
        rw [not_nonempty_iff] at hne
        have := hσ.2
        simp at this
      have hθM : θ < c ((M - 1) + 1) := by
        rw [Nat.sub_add_cancel hM1]
        change θ < signalCut τ M
        rw [signalCut_full, hsum]
        exact h1
      have hmM : m < M := by
        have : m ≤ M - 1 := Nat.find_min' hex hθM
        omega
      have hcm : c m ≤ θ := by
        rcases Nat.eq_zero_or_pos m with h | h
        · rw [h]
          change signalCut τ 0 ≤ θ
          rw [signalCut_zero]
          exact h0
        · have := Nat.find_min hex (show m - 1 < m by omega)
          rw [show m - 1 + 1 = m by omega] at this
          exact not_lt.1 this
      refine ⟨e.symm ⟨m, hmM⟩, ?_, ?_⟩ <;> simp only [Equiv.apply_symm_apply] <;> assumption
  · rw [Real.volume_Ico]
    congr 1
    change signalCut τ ((e s).val + 1) - signalCut τ (e s).val = σ s
    rw [signalCut_succ]
    simp [τ]

/-- A concrete instance: the degenerate mixed strategy on heads (`0 : Fin 2`) is generated by
a uniform signal. -/
theorem mixedStrategy_signal_pure :
    ∃ A : Fin 2 → Set ℝ, (∀ s, MeasurableSet (A s)) ∧
      (∀ s s', s ≠ s' → Disjoint (A s) (A s')) ∧ (⋃ s, A s) = Set.Ico 0 1 ∧
      ∀ s, volume (A s) = ENNReal.ofReal (pureMixed (0 : Fin 2) s) :=
  mixedStrategy_signal (isMixedStrategy_pureMixed 0)

end MWG.NoncooperativeGames

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Kuhn's theorem: mixed and behaviour strategies under perfect recall

MWG, Section 7.E, p. 233 (the result of Kuhn (1953) cited there) and Exercise 7.E.1.

Two randomized strategies of player `i`, a mixed strategy `σ` and a behaviour strategy `β`,
are **realization equivalent** (`RealizationEquivalent`) if they generate the same probability
distribution over the terminal nodes whatever the other players (and nature) do. The rivals'
play is given as arbitrary move probabilities at their information sets, which covers pure and
behaviour strategies; `realizationEquivalent_mixed_rivals` covers mixed strategies of the
rivals.

* `kuhn_behavior_to_mixed`: if no information set is crossed twice on a path (condition (i)
  of perfect recall), every behaviour strategy has a realization-equivalent mixed strategy,
  namely `mixedOfBehavior β`, `σ(s) = ∏_{H ∈ ℋ_i} β(H, s(H))`.
* `kuhn_mixed_to_behavior`: if player `i` satisfies condition (ii) of perfect recall, every
  mixed strategy has a realization-equivalent behaviour strategy, namely `behaviorOfMixed σ`,
  the conditional probability of each action given that `σ` is consistent with reaching the
  information set.
* `kuhn_theorem`: both directions in games of perfect recall (the statement on p. 233).

Both constructions are proved node by node: `mixedWeight σ x = weight β x` for every node `x`
(`mixedWeight_mixedOfBehavior`, `mixedWeight_eq_weight_behaviorOfMixed`), and the
factorisation of `MWGNoncooperativeGames.Mixed` turns this into realization equivalence.
-/

namespace MWG.NoncooperativeGames

namespace ExtensiveForm

variable {I A H : Type*} (G : ExtensiveForm I A H)

/-- A chosen decision node in information set `k`. -/
noncomputable def rep (k : H) : List A := (G.info_surj k).choose

theorem rep_isDecision (k : H) : G.IsDecision (G.rep k) :=
  ⟨(G.info_surj k).choose_spec.1, (G.info_surj k).choose_spec.2.1⟩

theorem info_rep (k : H) : G.info (G.rep k) = k := (G.info_surj k).choose_spec.2.2

variable [DecidableEq I]

theorem weight_cons_of_ne (j : Option I) (f : H → A → ℝ) {a : A} {x : List A}
    (h : G.player (G.info x) ≠ j) : G.weight j f (a :: x) = G.weight j f x := by
  simp [weight_cons, h]

theorem weight_cons_of_eq (j : Option I) (f : H → A → ℝ) {a : A} {x : List A}
    (h : G.player (G.info x) = j) : G.weight j f (a :: x) = G.weight j f x * f (G.info x) a := by
  simp [weight_cons, h]

variable [DecidableEq A]

/-- The weight of a pure strategy is nonnegative. -/
theorem weight_pureBeh_nonneg {i : I} (s : G.PureStrategy i) (x : List A) :
    0 ≤ G.weight (some i) (G.pureBeh s) x := by
  by_cases h : G.Consistent s x
  · rw [G.weight_pureBeh_of_consistent s h]; norm_num
  · rw [G.weight_pureBeh_of_not_consistent s h]

omit [DecidableEq I] [DecidableEq A] in
/-- Under condition (ii) of perfect recall, a pure strategy of `i` is consistent with the path
to `x` iff it is consistent with the path to any `x'` in the same information set of `i`. -/
theorem consistent_iff_of_recall {i : I} (hR : G.RecallFor i) {x x' : List A}
    (hx : G.IsDecision x) (hx' : G.IsDecision x') (hown : G.player (G.info x) = some i)
    (he : G.info x = G.info x') (s : G.PureStrategy i) :
    G.Consistent s x ↔ G.Consistent s x' := by
  have key : ∀ x x', G.IsDecision x → G.IsDecision x' → G.player (G.info x) = some i →
      G.info x = G.info x' → G.Consistent s x' → G.Consistent s x := by
    intro x x' hx hx' hown he hc y b hy hb
    have hown' : G.player (G.info x') = some i := he ▸ hown
    obtain ⟨y', -, hb', hyy⟩ := hR x hx.1 x' hx'.1 hx.2 hx'.2 hown he y
      (G.mem_of_suffix ((List.suffix_cons b y).trans hb) hx.1) b hb hy
    have hy' : G.player (G.info y') = some i := hyy ▸ hy
    have h1 := hc y' b hy' hb'
    have e : (⟨G.info y', hy'⟩ : G.InfoSetOf i) = ⟨G.info y, hy⟩ := Subtype.ext hyy
    rw [e] at h1
    exact h1
  exact ⟨key x' x hx' hx (he ▸ hown) he.symm, key x x' hx hx' hown he⟩

/-- Under condition (ii), pure strategies have equal weights at nodes of one information set
of player `i`. -/
theorem weight_pureBeh_eq_of_recall {i : I} (hR : G.RecallFor i) {x x' : List A}
    (hx : G.IsDecision x) (hx' : G.IsDecision x') (hown : G.player (G.info x) = some i)
    (he : G.info x = G.info x') (s : G.PureStrategy i) :
    G.weight (some i) (G.pureBeh s) x = G.weight (some i) (G.pureBeh s) x' := by
  by_cases hc : G.Consistent s x
  · rw [G.weight_pureBeh_of_consistent s hc, G.weight_pureBeh_of_consistent s
      ((G.consistent_iff_of_recall hR hx hx' hown he s).1 hc)]
  · rw [G.weight_pureBeh_of_not_consistent s hc, G.weight_pureBeh_of_not_consistent s
      (fun h => hc ((G.consistent_iff_of_recall hR hx hx' hown he s).2 h))]

variable [Fintype A] [Fintype H] [DecidableEq H]

omit [Fintype A] in
theorem mixedWeight_nil {i : I} {σ : G.PureStrategy i → ℝ} (hσ : ∑ s, σ s = 1) :
    G.mixedWeight σ [] = 1 := by
  simp [mixedWeight, hσ]

omit [Fintype A] in
theorem mixedWeight_cons_of_ne {i : I} (σ : G.PureStrategy i → ℝ) {a : A} {x : List A}
    (h : G.player (G.info x) ≠ some i) : G.mixedWeight σ (a :: x) = G.mixedWeight σ x := by
  simp only [mixedWeight, G.weight_cons_of_ne _ _ h]

omit [Fintype A] in
theorem mixedWeight_cons_of_eq {i : I} (σ : G.PureStrategy i → ℝ) {a : A} {x : List A}
    (h : G.player (G.info x) = some i) :
    G.mixedWeight σ (a :: x) = ∑ s, σ s * G.weight (some i) (G.pureBeh s) x *
      (if (s ⟨G.info x, h⟩).1 = a then 1 else 0) := by
  simp only [mixedWeight, G.weight_cons_of_eq _ _ h, G.pureBeh_of_mem _ h, mul_assoc]

omit [Fintype A] in
theorem mixedWeight_nonneg {i : I} {σ : G.PureStrategy i → ℝ} (hσ : ∀ s, 0 ≤ σ s)
    (x : List A) : 0 ≤ G.mixedWeight σ x :=
  Finset.sum_nonneg fun s _ => mul_nonneg (hσ s) (G.weight_pureBeh_nonneg s x)

omit [Fintype A] in
theorem mixedWeight_cons_le {i : I} {σ : G.PureStrategy i → ℝ} (hσ : ∀ s, 0 ≤ σ s)
    (a : A) (x : List A) : G.mixedWeight σ (a :: x) ≤ G.mixedWeight σ x := by
  by_cases h : G.player (G.info x) = some i
  · rw [G.mixedWeight_cons_of_eq σ h, mixedWeight]
    refine Finset.sum_le_sum fun s _ => ?_
    have h0 := mul_nonneg (hσ s) (G.weight_pureBeh_nonneg s x)
    split_ifs <;> linarith
  · rw [G.mixedWeight_cons_of_ne σ h]

omit [Fintype A] in
theorem mixedWeight_cons_eq_zero {i : I} {σ : G.PureStrategy i → ℝ} (hσ : ∀ s, 0 ≤ σ s)
    {a : A} {x : List A} (h0 : G.mixedWeight σ x = 0) : G.mixedWeight σ (a :: x) = 0 :=
  le_antisymm (h0 ▸ G.mixedWeight_cons_le hσ a x) (G.mixedWeight_nonneg hσ _)

omit [Fintype A] in
theorem sum_mixedWeight_cons {i : I} (σ : G.PureStrategy i → ℝ) {x : List A}
    (h : G.player (G.info x) = some i) :
    ∑ a ∈ G.avail (G.info x), G.mixedWeight σ (a :: x) = G.mixedWeight σ x := by
  simp_rw [G.mixedWeight_cons_of_eq σ h]
  rw [Finset.sum_comm, mixedWeight]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← Finset.mul_sum, Finset.sum_ite_eq]
  simp [(s ⟨G.info x, h⟩).2]

omit [Fintype A] in
theorem mixedWeight_cons_of_not_mem {i : I} (σ : G.PureStrategy i → ℝ) {a : A} {x : List A}
    (h : G.player (G.info x) = some i) (ha : a ∉ G.avail (G.info x)) :
    G.mixedWeight σ (a :: x) = 0 := by
  rw [G.mixedWeight_cons_of_eq σ h]
  refine Finset.sum_eq_zero fun s _ => ?_
  have : (s ⟨G.info x, h⟩).1 ≠ a := by
    rintro rfl
    exact ha (s ⟨G.info x, h⟩).2
  simp [this]

omit [Fintype A] in
/-- Under condition (ii), mixed weights agree at nodes of one information set of `i`, before
and after any action. -/
theorem mixedWeight_eq_of_recall {i : I} (hR : G.RecallFor i) (σ : G.PureStrategy i → ℝ)
    {x x' : List A} (hx : G.IsDecision x) (hx' : G.IsDecision x')
    (hown : G.player (G.info x) = some i) (he : G.info x = G.info x') (a : A) :
    G.mixedWeight σ x = G.mixedWeight σ x' ∧
      G.mixedWeight σ (a :: x) = G.mixedWeight σ (a :: x') := by
  have hown' : G.player (G.info x') = some i := he ▸ hown
  have hw := G.weight_pureBeh_eq_of_recall hR hx hx' hown he
  refine ⟨Finset.sum_congr rfl fun s _ => by rw [hw s], ?_⟩
  rw [G.mixedWeight_cons_of_eq σ hown, G.mixedWeight_cons_of_eq σ hown']
  have e : (⟨G.info x, hown⟩ : G.InfoSetOf i) = ⟨G.info x', hown'⟩ := Subtype.ext he
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [hw s, e]

/-- The behaviour strategy induced by a mixed strategy `σ`: at information set `k`, the
probability of action `a` conditional on `σ` being consistent with reaching `k` (uniform on
`C(k)` when `σ` never reaches `k`). -/
noncomputable def behaviorOfMixed {i : I} (σ : G.PureStrategy i → ℝ) : H → A → ℝ :=
  fun k a => if G.mixedWeight σ (G.rep k) = 0 then
      (if a ∈ G.avail k then ((G.avail k).card : ℝ)⁻¹ else 0)
    else G.mixedWeight σ (a :: G.rep k) / G.mixedWeight σ (G.rep k)

omit [Fintype A] in
/-- The conditional probabilities of a mixed strategy form a behaviour strategy. -/
theorem isBehaviorStrategy_behaviorOfMixed {i : I} {σ : G.PureStrategy i → ℝ}
    (hσ : IsMixedStrategy σ) : G.IsBehaviorStrategy i (G.behaviorOfMixed σ) := by
  intro k hk
  have hr := G.info_rep k
  have hown : G.player (G.info (G.rep k)) = some i := by rw [hr]; exact hk
  refine ⟨fun a => ?_, fun a ha => ?_, ?_⟩
  · unfold behaviorOfMixed
    split_ifs
    · positivity
    · norm_num
    · exact div_nonneg (G.mixedWeight_nonneg hσ.1 _) (G.mixedWeight_nonneg hσ.1 _)
  · unfold behaviorOfMixed
    have ha' : a ∉ G.avail (G.info (G.rep k)) := by rw [hr]; exact ha
    split_ifs
    · rfl
    · rw [G.mixedWeight_cons_of_not_mem σ hown ha', zero_div]
  · unfold behaviorOfMixed
    split_ifs with h0
    · rw [Finset.sum_const, nsmul_eq_mul]
      have : ((G.avail k).card : ℝ) ≠ 0 := by
        exact_mod_cast (G.avail_nonempty k).card_pos.ne'
      field_simp
    · have hs := G.sum_mixedWeight_cons σ hown
      rw [hr] at hs
      rw [← Finset.sum_div, hs, div_self h0]

omit [Fintype A] in
/-- **Kuhn's theorem, mixed to behaviour** (MWG, p. 233), node by node: under condition (ii) of
perfect recall for player `i`, `behaviorOfMixed σ` reaches every node with the same
`i`-weight as `σ`. -/
theorem mixedWeight_eq_weight_behaviorOfMixed {i : I} (hR : G.RecallFor i)
    {σ : G.PureStrategy i → ℝ} (hσ : IsMixedStrategy σ) :
    ∀ x ∈ G.nodes, G.mixedWeight σ x = G.weight (some i) (G.behaviorOfMixed σ) x := by
  intro x
  induction x with
  | nil => intro _; rw [G.mixedWeight_nil hσ.2]; rfl
  | cons a x ih =>
    intro hax
    have hx := G.mem_of_cons_mem hax
    by_cases hown : G.player (G.info x) = some i
    · rw [G.weight_cons_of_eq _ _ hown, ← ih hx]
      have hxd : G.IsDecision x := G.isDecision_of_cons_mem hax
      obtain ⟨e1, e2⟩ := G.mixedWeight_eq_of_recall hR σ hxd (G.rep_isDecision (G.info x))
        hown (G.info_rep _).symm a
      rw [e1, e2]
      by_cases h0 : G.mixedWeight σ (G.rep (G.info x)) = 0
      · rw [h0, zero_mul]
        exact G.mixedWeight_cons_eq_zero hσ.1 h0
      · have hb : G.behaviorOfMixed σ (G.info x) a =
            G.mixedWeight σ (a :: G.rep (G.info x)) / G.mixedWeight σ (G.rep (G.info x)) := by
          simp [behaviorOfMixed, h0]
        rw [hb]
        field_simp
    · rw [G.mixedWeight_cons_of_ne σ hown, G.weight_cons_of_ne _ _ hown]
      exact ih hx

/-- The mixed strategy induced by a behaviour strategy `β`: pure strategies drawn by
independent randomizations at the information sets, `σ(s) = ∏_{H ∈ ℋ_i} β(H, s(H))`. -/
noncomputable def mixedOfBehavior {i : I} (β : H → A → ℝ) : G.PureStrategy i → ℝ :=
  fun s => ∏ k, β k.1 (s k).1

omit [DecidableEq A] [Fintype A] in
/-- The product of a behaviour strategy over the information sets is a mixed strategy. -/
theorem isMixedStrategy_mixedOfBehavior {i : I} {β : H → A → ℝ}
    (hβ : G.IsBehaviorStrategy i β) : IsMixedStrategy (G.mixedOfBehavior (i := i) β) := by
  refine ⟨fun s => Finset.prod_nonneg fun k _ => (hβ k.1 k.2).1 _, ?_⟩
  have h := Fintype.prod_sum
    (fun (k : G.InfoSetOf i) (b : {a // a ∈ G.avail k.1}) => β k.1 b.1)
  unfold mixedOfBehavior
  rw [← h]
  refine Finset.prod_eq_one fun k _ => ?_
  rw [Finset.sum_coe_sort (G.avail k.1) (β k.1)]
  exact (hβ k.1 k.2).2.2

/-- The path to `x` allows action `b` at player `i`'s information set `k`: whenever the path
crosses `k`, it takes `b` there. -/
def PathAllows {i : I} (x : List A) (k : G.InfoSetOf i) (b : A) : Prop :=
  ∀ y a, a :: y <:+ x → G.info y = k.1 → b = a

open Classical in
/-- The indicator of `PathAllows`. -/
noncomputable def pathFactor {i : I} (x : List A) (k : G.InfoSetOf i) (b : A) : ℝ :=
  if G.PathAllows x k b then 1 else 0

omit [DecidableEq I] [DecidableEq A] [Fintype A] [Fintype H] [DecidableEq H] in
theorem pathFactor_of {i : I} {x : List A} {k : G.InfoSetOf i} {b : A}
    (h : G.PathAllows x k b) : G.pathFactor x k b = 1 := by
  unfold pathFactor
  split_ifs
  rfl

omit [DecidableEq I] [DecidableEq A] [Fintype A] [Fintype H] [DecidableEq H] in
theorem pathFactor_of_not {i : I} {x : List A} {k : G.InfoSetOf i} {b : A}
    (h : ¬ G.PathAllows x k b) : G.pathFactor x k b = 0 := by
  unfold pathFactor
  split_ifs
  rfl

omit [Fintype A] [Fintype H] [DecidableEq H] [DecidableEq I] [DecidableEq A] in
theorem consistent_iff_pathAllows {i : I} (s : G.PureStrategy i) (x : List A) :
    G.Consistent s x ↔ ∀ k, G.PathAllows x k (s k).1 := by
  constructor
  · intro h k y a hya hyk
    have hy : G.player (G.info y) = some i := hyk ▸ k.2
    have h1 := h y a hy hya
    have e : (⟨G.info y, hy⟩ : G.InfoSetOf i) = k := Subtype.ext hyk
    rw [e] at h1
    exact h1
  · intro h y a hy hya
    exact h ⟨G.info y, hy⟩ y a hya rfl

omit [Fintype A] [DecidableEq H] in
/-- The weight of a pure strategy factorises over the information sets. -/
theorem weight_pureBeh_eq_prod {i : I} (s : G.PureStrategy i) (x : List A) :
    G.weight (some i) (G.pureBeh s) x = ∏ k, G.pathFactor x k (s k).1 := by
  by_cases hc : G.Consistent s x
  · rw [G.weight_pureBeh_of_consistent s hc]
    exact (Finset.prod_eq_one fun k _ =>
      G.pathFactor_of ((G.consistent_iff_pathAllows s x).1 hc k)).symm
  · rw [G.weight_pureBeh_of_not_consistent s hc]
    rw [G.consistent_iff_pathAllows] at hc
    push Not at hc
    obtain ⟨k, hk⟩ := hc
    exact (Finset.prod_eq_zero (Finset.mem_univ k) (G.pathFactor_of_not hk)).symm

omit [DecidableEq I] [DecidableEq A] [Fintype A] [Fintype H] [DecidableEq H] in
theorem pathAllows_nil {i : I} (k : G.InfoSetOf i) (b : A) : G.PathAllows [] k b := by
  intro y a h
  have := h.length_le
  simp at this

omit [DecidableEq I] [DecidableEq A] [Fintype A] [Fintype H] [DecidableEq H] in
theorem pathAllows_cons {i : I} (a : A) (x : List A) (k : G.InfoSetOf i) (b : A) :
    G.PathAllows (a :: x) k b ↔ (G.info x = k.1 → b = a) ∧ G.PathAllows x k b := by
  constructor
  · intro h
    exact ⟨fun he => h x a (List.suffix_refl _) he,
      fun y c hy he => h y c (hy.trans (List.suffix_cons a x)) he⟩
  · rintro ⟨h1, h2⟩ y c hy he
    rcases List.suffix_cons_iff.1 hy with heq | hy'
    · simp only [List.cons.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      exact h1 he
    · exact h2 y c hy' he

omit [DecidableEq I] [DecidableEq A] [Fintype A] [Fintype H] [DecidableEq H] in
theorem pathFactor_cons_of_ne {i : I} {a : A} {x : List A} {k : G.InfoSetOf i} {b : A}
    (hne : G.info x ≠ k.1) : G.pathFactor (a :: x) k b = G.pathFactor x k b := by
  have h : G.PathAllows (a :: x) k b ↔ G.PathAllows x k b := by
    rw [G.pathAllows_cons]
    simp [hne]
  by_cases hp : G.PathAllows x k b
  · rw [G.pathFactor_of hp, G.pathFactor_of (h.2 hp)]
  · rw [G.pathFactor_of_not hp, G.pathFactor_of_not (fun h' => hp (h.1 h'))]

omit [Fintype A] in
/-- **Kuhn's theorem, behaviour to mixed** (MWG, p. 233), node by node: if no information set
is crossed twice on a path, the product mixed strategy `mixedOfBehavior β` reaches every node
with the same `i`-weight as `β`. -/
theorem mixedWeight_mixedOfBehavior (hNA : G.NoAbsentMindedness) {i : I} {β : H → A → ℝ}
    (hβ : G.IsBehaviorStrategy i β) :
    ∀ x ∈ G.nodes, G.mixedWeight (G.mixedOfBehavior (i := i) β) x = G.weight (some i) β x := by
  have hprod : ∀ x, G.mixedWeight (G.mixedOfBehavior (i := i) β) x =
      ∏ k : G.InfoSetOf i, ∑ b ∈ G.avail k.1, β k.1 b * G.pathFactor x k b := by
    intro x
    have h := Fintype.prod_sum (fun (k : G.InfoSetOf i) (b : {a // a ∈ G.avail k.1}) =>
      β k.1 b.1 * G.pathFactor x k b.1)
    have h2 : ∀ k : G.InfoSetOf i,
        ∑ b : {a // a ∈ G.avail k.1}, β k.1 b.1 * G.pathFactor x k b.1 =
          ∑ b ∈ G.avail k.1, β k.1 b * G.pathFactor x k b := fun k =>
      Finset.sum_coe_sort (G.avail k.1) (fun b => β k.1 b * G.pathFactor x k b)
    rw [Finset.prod_congr rfl fun k _ => (h2 k).symm, h, mixedWeight]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [mixedOfBehavior, G.weight_pureBeh_eq_prod, ← Finset.prod_mul_distrib]
  intro x
  rw [hprod]
  induction x with
  | nil =>
    intro _
    refine Finset.prod_eq_one fun k _ => ?_
    have h1 : ∀ b, G.pathFactor [] k b = 1 := fun b => G.pathFactor_of (G.pathAllows_nil k b)
    simp_rw [h1, mul_one]
    exact (hβ k.1 k.2).2.2
  | cons a x ih =>
    intro hax
    have hx := G.mem_of_cons_mem hax
    by_cases hown : G.player (G.info x) = some i
    · rw [G.weight_cons_of_eq _ _ hown, ← ih hx]
      have hxd : G.IsDecision x := G.isDecision_of_cons_mem hax
      have hav : a ∈ G.avail (G.info x) := G.mem_avail_of_cons_mem hax
      obtain ⟨k₀, hk₀⟩ : ∃ k₀ : G.InfoSetOf i, k₀ = ⟨G.info x, hown⟩ := ⟨_, rfl⟩
      have hk1 : k₀.1 = G.info x := by rw [hk₀]
      have hstep : ∀ k : G.InfoSetOf i,
          ∑ b ∈ G.avail k.1, β k.1 b * G.pathFactor (a :: x) k b =
            (∑ b ∈ G.avail k.1, β k.1 b * G.pathFactor x k b) *
              if k = k₀ then β (G.info x) a else 1 := by
        intro k
        by_cases hk : k = k₀
        · subst hk
          have hall : ∀ b, G.pathFactor x k b = 1 := by
            intro b
            refine G.pathFactor_of fun y c hyc hye => ?_
            exact absurd (hye.trans hk1) (G.info_ne_of_cons_suffix hNA hxd hyc)
          have hpf : ∀ b, G.pathFactor (a :: x) k b = if b = a then 1 else 0 := by
            intro b
            by_cases hb : b = a
            · rw [ite_eq_left_of_eq_true _ _ (eq_true hb)]
              refine G.pathFactor_of ((G.pathAllows_cons a x k b).2 ⟨fun _ => hb, ?_⟩)
              intro y c hyc hye
              exact absurd (hye.trans hk1) (G.info_ne_of_cons_suffix hNA hxd hyc)
            · rw [ite_eq_right_of_eq_false _ _ (eq_false hb)]
              exact G.pathFactor_of_not fun h =>
                hb (((G.pathAllows_cons a x k b).1 h).1 hk1.symm)
          rw [ite_eq_left_of_eq_true _ _ (eq_self k)]
          simp_rw [hpf, hall, mul_one, mul_ite, mul_one, mul_zero]
          rw [(hβ k.1 k.2).2.2, one_mul, Finset.sum_ite_eq']
          simp [hk1, hav]
        · have hne : G.info x ≠ k.1 := fun he => hk (by rw [hk₀]; exact Subtype.ext he.symm)
          rw [ite_eq_right_of_eq_false _ _ (eq_false hk), mul_one]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [G.pathFactor_cons_of_ne hne]
      rw [Finset.prod_congr rfl fun k _ => hstep k, Finset.prod_mul_distrib, Finset.prod_ite_eq']
      simp [hk₀]
    · rw [G.weight_cons_of_ne _ _ hown, ← ih hx]
      refine Finset.prod_congr rfl fun k _ => Finset.sum_congr rfl fun b _ => ?_
      have hne : G.info x ≠ k.1 := fun he => hown (he ▸ k.2)
      rw [G.pathFactor_cons_of_ne hne]

variable [Fintype I]

/-- **Section 7.E** (MWG, p. 233; Exercise 7.E.1(b)). A mixed strategy `σ` and a behaviour
strategy `β` of player `i` are realization equivalent: whatever the move probabilities `F j`
of the other players (pure or behaviour strategies), they induce the same probability of every
terminal node. -/
def RealizationEquivalent (i : I) (σ : G.PureStrategy i → ℝ) (β : H → A → ℝ) : Prop :=
  ∀ F : I → H → A → ℝ, ∀ z ∈ G.terminals,
    ∑ s, σ s * G.reach (G.assemble (Function.update F i (G.pureBeh s))) z =
      G.reach (G.assemble (Function.update F i β)) z

omit [DecidableEq A] [Fintype A] [Fintype H] [DecidableEq H] in
/-- Isolating player `i`'s weight in a reach probability. -/
theorem reach_update_factor (i : I) (F : I → H → A → ℝ) (g : H → A → ℝ) (x : List A) :
    G.reach (G.assemble (Function.update F i g)) x =
      G.weight (some i) g x * (G.weight none G.natureProb x *
        ∏ j, if j = i then 1 else G.weight (some j) (F j) x) := by
  rw [reach_assemble_factor]
  have : ∀ j, G.weight (some j) (Function.update F i g j) x =
      (if j = i then G.weight (some i) g x else 1) *
        (if j = i then 1 else G.weight (some j) (F j) x) := by
    intro j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [hj]
  simp_rw [this]
  rw [Finset.prod_mul_distrib, Finset.prod_ite_eq']
  simp only [Finset.mem_univ, ite_true]
  ring

omit [Fintype I] in
/-- Equal `i`-weights at the terminal nodes give realization equivalence. -/
theorem realizationEquivalent_of_weight [Finite I] {i : I} {σ : G.PureStrategy i → ℝ}
    {β : H → A → ℝ} (h : ∀ z ∈ G.terminals, G.mixedWeight σ z = G.weight (some i) β z) :
    G.RealizationEquivalent i σ β := by
  have := Fintype.ofFinite I
  intro F z hz
  simp_rw [G.reach_update_factor i F]
  rw [← h z hz, mixedWeight, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  ring

omit [Fintype I] in
/-- **Kuhn's theorem** (Kuhn 1953, cited on MWG p. 233; Exercise 7.E.1(b)). If no information
set is crossed twice on a path (perfect recall condition (i)), every behaviour strategy of
player `i` has a realization-equivalent mixed strategy. -/
theorem kuhn_behavior_to_mixed [Finite I] (hNA : G.NoAbsentMindedness) {i : I} {β : H → A → ℝ}
    (hβ : G.IsBehaviorStrategy i β) :
    ∃ σ : G.PureStrategy i → ℝ, IsMixedStrategy σ ∧ G.RealizationEquivalent i σ β :=
  ⟨G.mixedOfBehavior β, G.isMixedStrategy_mixedOfBehavior hβ,
    G.realizationEquivalent_of_weight fun z hz =>
      G.mixedWeight_mixedOfBehavior hNA hβ z ((G.mem_terminals).1 hz).1⟩

omit [Fintype I] in
/-- **Kuhn's theorem** (Kuhn 1953, cited on MWG p. 233; Exercise 7.E.1(c)). If player `i`
satisfies perfect recall condition (ii), every mixed strategy of player `i` has a
realization-equivalent behaviour strategy. -/
theorem kuhn_mixed_to_behavior [Finite I] {i : I} (hR : G.RecallFor i) {σ : G.PureStrategy i → ℝ}
    (hσ : IsMixedStrategy σ) :
    ∃ β : H → A → ℝ, G.IsBehaviorStrategy i β ∧ G.RealizationEquivalent i σ β :=
  ⟨G.behaviorOfMixed σ, G.isBehaviorStrategy_behaviorOfMixed hσ,
    G.realizationEquivalent_of_weight fun z hz =>
      G.mixedWeight_eq_weight_behaviorOfMixed hR hσ z ((G.mem_terminals).1 hz).1⟩

omit [Fintype I] in
/-- **Kuhn's theorem** (Kuhn 1953; MWG, Section 7.E, p. 233). In a game of perfect recall, for
any behaviour strategy of player `i` there is a realization-equivalent mixed strategy, and
for any mixed strategy there is a realization-equivalent behaviour strategy. -/
theorem kuhn_theorem [Finite I] (hPR : G.PerfectRecall) (i : I) :
    (∀ β : H → A → ℝ, G.IsBehaviorStrategy i β →
      ∃ σ : G.PureStrategy i → ℝ, IsMixedStrategy σ ∧ G.RealizationEquivalent i σ β) ∧
    (∀ σ : G.PureStrategy i → ℝ, IsMixedStrategy σ →
      ∃ β : H → A → ℝ, G.IsBehaviorStrategy i β ∧ G.RealizationEquivalent i σ β) :=
  ⟨fun _ hβ => G.kuhn_behavior_to_mixed hPR.1 hβ,
    fun _ hσ => G.kuhn_mixed_to_behavior (hPR.2 i) hσ⟩

/-- **Section 7.E** (MWG, p. 233). Realization equivalence also holds against MIXED strategies
of the rivals: if `σ i` and `β` give player `i` the same weights at the terminal nodes, then
the mixed profile `σ` induces the same distribution over terminal nodes as the profile where
`i` plays `β` and the rivals randomize independently according to `σ` (the `i`-th coordinate
of the drawn pure profile is then irrelevant). -/
theorem realizationEquivalent_mixed_rivals {i : I} (σ : (j : I) → G.PureStrategy j → ℝ)
    (hσi : ∑ s, σ i s = 1) {β : H → A → ℝ}
    (h : ∀ z ∈ G.terminals, G.mixedWeight (σ i) z = G.weight (some i) β z) :
    ∀ z ∈ G.terminals, G.mixedOutcome σ z =
      ∑ s : (j : I) → G.PureStrategy j, (∏ j, σ j (s j)) *
        G.reach (G.assemble (Function.update (fun j => G.pureBeh (s j)) i β)) z := by
  intro z hz
  rw [mixedOutcome_factor]
  let c : (j : I) → G.PureStrategy j → ℝ := fun j t =>
    if j = i then G.weight (some i) β z else G.weight (some j) (G.pureBeh t) z
  have hc : ∀ s : (j : I) → G.PureStrategy j,
      G.reach (G.assemble (Function.update (fun j => G.pureBeh (s j)) i β)) z =
        G.weight none G.natureProb z * ∏ j, c j (s j) := by
    intro s
    rw [reach_assemble_factor]
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    by_cases hj : j = i
    · subst hj
      simp [c]
    · simp [c, hj]
  simp_rw [hc]
  have : ∀ s : (j : I) → G.PureStrategy j, (∏ j, σ j (s j)) *
      (G.weight none G.natureProb z * ∏ j, c j (s j)) =
        G.weight none G.natureProb z * ∏ j, σ j (s j) * c j (s j) := by
    intro s
    rw [Finset.prod_mul_distrib]
    ring
  simp_rw [this]
  have hps := Fintype.prod_sum (fun j (t : G.PureStrategy j) => σ j t * c j t)
  rw [← Finset.mul_sum, ← hps]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  by_cases hj : j = i
  · subst hj
    simp only [c, ite_true]
    rw [← Finset.sum_mul, hσi, one_mul, h z hz]
  · simp only [c, hj, ite_false, mixedWeight]

/-- **Kuhn's theorem against mixed rivals** (MWG, p. 233). Under condition (ii) of perfect
recall for player `i`, replacing her mixed strategy `σ i` by `behaviorOfMixed (σ i)` leaves
the distribution over terminal nodes unchanged when the rivals play mixed strategies. -/
theorem kuhn_mixed_rivals {i : I} (hR : G.RecallFor i) (σ : (j : I) → G.PureStrategy j → ℝ)
    (hσ : IsMixedStrategy (σ i)) :
    ∀ z ∈ G.terminals, G.mixedOutcome σ z =
      ∑ s : (j : I) → G.PureStrategy j, (∏ j, σ j (s j)) *
        G.reach (G.assemble
          (Function.update (fun j => G.pureBeh (s j)) i (G.behaviorOfMixed (σ i)))) z :=
  G.realizationEquivalent_mixed_rivals σ hσ.2 fun z hz =>
    G.mixedWeight_eq_weight_behaviorOfMixed hR hσ z ((G.mem_terminals).1 hz).1

end ExtensiveForm

end MWG.NoncooperativeGames

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Matching Pennies and its variants

MWG, Examples 7.B.1, 7.C.1, 7.C.3, 7.C.4, 7.C.5, 7.D.1, 7.D.2, 7.D.3, Exercise 7.D.2,
Figures 7.C.1, 7.C.3, 7.C.5, 7.D.1 and 7.D.2 (pp. 220-231).

Encoding. Players `Fin 2`: `0` is player 1 and `1` is player 2. Actions `Fin 2`: `0` is
heads (H) and `1` is tails (T). Histories list the most recent action first, so in a
two-move game the terminal node `[b, a]` means that the first mover chose `a` and the second
mover chose `b`. Player 1's payoff is `mpPay a b = -1` if the pennies match and `+1`
otherwise; player 2's payoff is its negative.

* `matchingPennies`: the normal form of Example 7.B.1; it is zero-sum and each player's best
  action depends on the opponent's (`example_7_B_1_zero_sum`, `example_7_B_1_best_action`).
* `matchingPenniesB` (Figure 7.C.1): perfect information. Its strategies (Example 7.D.1:
  two for player 1, four for player 2) and its normal form (Example 7.D.3, Figure 7.D.1).
* `matchingPenniesC` (Figure 7.C.3, Example 7.C.3) is also the extensive form of standard
  Matching Pennies (Example 7.C.4); `matchingPenniesReversed` is the tree with the order of
  the players reversed. Both have the normal form of Example 7.B.1 (Exercise 7.D.2).
* `matchingPenniesD` (Figure 7.C.5, Example 7.C.5): a move of nature decides who moves first.
* `figure_7_D_2`: an extensive form of imperfect information whose normal form is that of
  Figure 7.D.1 (MWG, pp. 230-231).
-/

namespace MWG.NoncooperativeGames

open ExtensiveForm

/-- Player 1's payoff in Matching Pennies when she plays `a` and player 2 plays `b`: she pays
one dollar if the pennies match and receives one dollar otherwise. -/
def mpPay (a b : Fin 2) : ℝ := if a = b then -1 else 1

/-- **Example 7.B.1** (MWG, p. 220). Matching Pennies in normal form: each player has the
actions H (`0`) and T (`1`); player 1 pays player 2 a dollar if the pennies match. -/
def matchingPennies : NormalForm (Fin 2) (fun _ => Fin 2) where
  payoff i s := if i = 0 then mpPay (s 0) (s 1) else -mpPay (s 0) (s 1)

/-- **Example 7.B.1** (MWG, p. 221). Matching Pennies is zero-sum: what one player wins, the
other loses. -/
theorem example_7_B_1_zero_sum (s : (i : Fin 2) → Fin 2) :
    matchingPennies.payoff 0 s + matchingPennies.payoff 1 s = 0 := by
  simp [matchingPennies]

/-- **Section 7.B** (MWG, p. 221). A zero-sum game: at every strategy profile the players'
payoffs sum to zero (what one player wins, the others lose). -/
def NormalForm.IsZeroSum {I : Type*} [Fintype I] {S : I → Type*} (N : NormalForm I S) : Prop :=
  ∀ s, ∑ i, N.payoff i s = 0

/-- **Example 7.B.1** (MWG, p. 221). Matching Pennies is a zero-sum game. -/
theorem example_7_B_1_isZeroSum : matchingPennies.IsZeroSum := fun s => by
  rw [Fin.sum_univ_two]
  exact example_7_B_1_zero_sum s

/-- **Example 7.B.1** (MWG, p. 221). The action that maximizes player 1's payoff depends on
what player 2 does: against H the unique best action is T, against T it is H. -/
theorem example_7_B_1_best_action :
    (∀ a : Fin 2, a ≠ 1 →
      matchingPennies.payoff 0 (![a, 0]) < matchingPennies.payoff 0 (![1, 0])) ∧
    (∀ a : Fin 2, a ≠ 0 →
      matchingPennies.payoff 0 (![a, 1]) < matchingPennies.payoff 0 (![0, 1])) := by
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩ <;> fin_cases a <;> simp_all [matchingPennies, mpPay]

/-- Player 1's payoff at a terminal node `b :: a :: _` of a two-move Matching Pennies tree
where player 1's action is `a` and player 2's is `b`. -/
def mpTermPay (z : List (Fin 2)) : ℝ :=
  match z with
  | b :: a :: _ => mpPay a b
  | _ => 0

/-- The nodes of the two-move Matching Pennies trees (Figures 7.C.1 and 7.C.3). -/
def mpNodes : Finset (List (Fin 2)) := {[], [0], [1], [0, 0], [1, 0], [0, 1], [1, 1]}

/-- The information sets of Figure 7.C.1: the initial node (`0`), after H (`1`), after T
(`2`). -/
def mpBInfo (x : List (Fin 2)) : Fin 3 := if x = [] then 0 else if x = [0] then 1 else 2

/-- **Example 7.C.1, Figure 7.C.1** (MWG, pp. 221-222). Matching Pennies Version B: player 1
moves first, player 2 sees her move and then moves. -/
def matchingPenniesB : ExtensiveForm (Fin 2) (Fin 2) (Fin 3) where
  nodes := mpNodes
  nil_mem := by decide
  tail_mem := by decide
  info := mpBInfo
  avail := fun _ => Finset.univ
  avail_spec := by decide
  info_surj := by decide
  player := fun k => if k = 0 then some 0 else some 1
  natureProb := fun _ _ => 0
  nature_nonneg := fun k hk => absurd hk (by fin_cases k <;> decide)
  nature_zero := fun k hk => absurd hk (by fin_cases k <;> decide)
  nature_sum := fun k hk => absurd hk (by fin_cases k <;> decide)
  payoff := fun i z => if i = 0 then mpTermPay z else -mpTermPay z

/-- **Example 7.C.1** (MWG, p. 222). Version B is a game of perfect information (every
information set is a singleton), hence of perfect recall. -/
theorem example_7_C_1 :
    matchingPenniesB.PerfectInformation ∧ matchingPenniesB.PerfectRecall := by
  have h : matchingPenniesB.PerfectInformation := by
    unfold ExtensiveForm.PerfectInformation; decide
  exact ⟨h, perfectRecall_of_perfectInformation _ h⟩

/-- **Example 7.C.1** (MWG, p. 222). The terminal nodes of Version B. -/
theorem matchingPenniesB_terminals :
    matchingPenniesB.terminals = {[0, 0], [1, 0], [0, 1], [1, 1]} := by decide

/-- **Example 7.D.1** (MWG, p. 229). In Version B player 1 has two pure strategies and
player 2 has four. -/
theorem example_7_D_1 :
    Fintype.card (matchingPenniesB.PureStrategy 0) = 2 ∧
      Fintype.card (matchingPenniesB.PureStrategy 1) = 4 := by
  rw [card_pureStrategy, card_pureStrategy]
  decide

/-- Player 2's four strategies in Version B (Example 7.D.1): `s₁` (`m = 0`) plays H after H
and after T, `s₂` plays H after H and T after T, `s₃` plays T after H and H after T, `s₄`
plays T after both. -/
def mpBResponse (m : Fin 4) (k : Fin 3) : Fin 2 :=
  if k = 1 then (if m.val < 2 then 0 else 1) else (if m.val % 2 = 0 then 0 else 1)

/-- The pure strategy profile of Version B in which player 1 plays `a` and player 2 plays
strategy `s_{m+1}`. -/
def mpBProfile (a : Fin 2) (m : Fin 4) : (i : Fin 2) → matchingPenniesB.PureStrategy i :=
  fun i => matchingPenniesB.pureOfFun i (fun k => if i = 0 then a else mpBResponse m k)
    (fun _ _ => Finset.mem_univ _)

theorem matchingPenniesB_info : matchingPenniesB.info = mpBInfo := rfl

theorem matchingPenniesB_payoff_def (i : Fin 2) (z : List (Fin 2)) :
    matchingPenniesB.payoff i z = if i = 0 then mpTermPay z else -mpTermPay z := rfl

theorem matchingPenniesB_no_nature : ∀ k, matchingPenniesB.player k ≠ none := by decide

theorem matchingPenniesB_root_player :
    matchingPenniesB.player (matchingPenniesB.info []) = some 0 := by
  decide

theorem matchingPenniesB_second_player (a : Fin 2) :
    matchingPenniesB.player (matchingPenniesB.info [a]) = some 1 := by
  revert a; decide

/-- **Section 7.D** (MWG, p. 230). The normal form of Version B in closed form: if player 1
plays `a` and player 2 answers `b` to `a`, payoffs are those at the terminal node `[b, a]`. -/
theorem matchingPenniesB_payoff (s : (i : Fin 2) → matchingPenniesB.PureStrategy i) (i : Fin 2) :
    matchingPenniesB.toNormalForm.payoff i s =
      matchingPenniesB.payoff i
        [(s 1 ⟨matchingPenniesB.info [(s 0 ⟨_, matchingPenniesB_root_player⟩).1],
            matchingPenniesB_second_player _⟩).1,
          (s 0 ⟨_, matchingPenniesB_root_player⟩).1] := by
  refine matchingPenniesB.toNormalForm_payoff_of_reach matchingPenniesB_no_nature s ?_ ?_ i
  · rw [matchingPenniesB_terminals]
    generalize (s 0 ⟨_, matchingPenniesB_root_player⟩).1 = a
    generalize (s 1 _).1 = b
    revert a b; decide
  · rw [reach_cons, reach_cons, reach_nil, pureProfile_apply _ s matchingPenniesB_root_player,
      pureProfile_apply _ s (matchingPenniesB_second_player _)]
    simp

/-- **Example 7.D.3, Figure 7.D.1** (MWG, p. 230). The normal form of Matching Pennies
Version B: `u₁(s₁, s₂) = +1` if `(s₁, s₂)` is (H, strategy 3 or 4) or (T, strategy 1 or 3),
`u₁ = -1` otherwise, and `u₂ = -u₁`. -/
theorem example_7_D_3 (a : Fin 2) (m : Fin 4) :
    matchingPenniesB.toNormalForm.payoff 0 (mpBProfile a m) =
      (if (a = 0 ∧ (m = 2 ∨ m = 3)) ∨ (a = 1 ∧ (m = 0 ∨ m = 2)) then 1 else -1) ∧
    matchingPenniesB.toNormalForm.payoff 1 (mpBProfile a m) =
      -matchingPenniesB.toNormalForm.payoff 0 (mpBProfile a m) := by
  rw [matchingPenniesB_payoff, matchingPenniesB_payoff]
  fin_cases a <;> fin_cases m <;>
    simp [mpBProfile, pureOfFun, matchingPenniesB_info, matchingPenniesB_payoff_def, mpBInfo,
      mpBResponse, mpTermPay, mpPay]

/-- The information sets of Figure 7.C.3: the initial node (`0`) and player 2's two nodes
(`1`). -/
def mpCInfo (x : List (Fin 2)) : Fin 2 := if x = [] then 0 else 1

/-- **Example 7.C.3, Figure 7.C.3** (MWG, pp. 223-224). Matching Pennies Version C: player 2
moves without seeing player 1's covered penny; her two nodes form one information set. By
Example 7.C.4 (MWG, p. 225) this is also the extensive form of standard Matching Pennies. -/
def matchingPenniesC : ExtensiveForm (Fin 2) (Fin 2) (Fin 2) where
  nodes := mpNodes
  nil_mem := by decide
  tail_mem := by decide
  info := mpCInfo
  avail := fun _ => Finset.univ
  avail_spec := by decide
  info_surj := by decide
  player := fun k => some k
  natureProb := fun _ _ => 0
  nature_nonneg := fun k hk => absurd hk (by fin_cases k <;> decide)
  nature_zero := fun k hk => absurd hk (by fin_cases k <;> decide)
  nature_sum := fun k hk => absurd hk (by fin_cases k <;> decide)
  payoff := fun i z => if i = 0 then mpTermPay z else -mpTermPay z

/-- **Example 7.C.3** (MWG, pp. 223-224). Version C has imperfect information, satisfies
perfect recall, and player 2 has the same actions at both nodes of her information set. -/
theorem example_7_C_3 :
    ¬ matchingPenniesC.PerfectInformation ∧ matchingPenniesC.PerfectRecall ∧
      ∀ a, a :: [0] ∈ matchingPenniesC.nodes ↔ a :: [1] ∈ matchingPenniesC.nodes := by
  refine ⟨by unfold ExtensiveForm.PerfectInformation; decide, ⟨?_, fun i => ?_⟩, by decide⟩
  · unfold ExtensiveForm.NoAbsentMindedness; decide
  · unfold ExtensiveForm.RecallFor; fin_cases i <;> decide

/-- **Example 7.D.2** (MWG, p. 229). In Version C each player has exactly two pure
strategies. -/
theorem example_7_D_2 :
    Fintype.card (matchingPenniesC.PureStrategy 0) = 2 ∧
      Fintype.card (matchingPenniesC.PureStrategy 1) = 2 := by
  rw [card_pureStrategy, card_pureStrategy]
  decide

theorem matchingPenniesC_terminals :
    matchingPenniesC.terminals = {[0, 0], [1, 0], [0, 1], [1, 1]} := by decide

theorem matchingPenniesC_no_nature : ∀ k, matchingPenniesC.player k ≠ none := by decide

/-- **Exercise 7.D.2** (MWG, p. 230). The normal form of Matching Pennies Version C (and so
of standard Matching Pennies, whose extensive form it is by Example 7.C.4) is the game of
Example 7.B.1, each player's strategy being her action at her single information set. -/
theorem exercise_7_D_2 (s : (i : Fin 2) → matchingPenniesC.PureStrategy i) (i : Fin 2) :
    matchingPenniesC.toNormalForm.payoff i s =
      matchingPennies.payoff i (fun j => (s j ⟨j, rfl⟩).1) := by
  have hz : [(s 1 ⟨1, rfl⟩).1, (s 0 ⟨0, rfl⟩).1] ∈ matchingPenniesC.terminals := by
    rw [matchingPenniesC_terminals]
    generalize (s 1 ⟨1, rfl⟩).1 = b
    generalize (s 0 ⟨0, rfl⟩).1 = a
    revert a b; decide
  rw [matchingPenniesC.toNormalForm_payoff_of_reach matchingPenniesC_no_nature s hz]
  · simp [matchingPenniesC, matchingPennies, mpTermPay]
  · rw [reach_cons, reach_cons, reach_nil,
      show matchingPenniesC.info [] = 0 from rfl,
      show matchingPenniesC.info [(s 0 ⟨0, rfl⟩).1] = 1 from rfl,
      pureProfile_apply _ s (k := 0) (j := 0) rfl, pureProfile_apply _ s (k := 1) (j := 1) rfl]
    simp

/-- **Example 7.C.4** (MWG, p. 225). Standard Matching Pennies can equally be drawn with the
order of the decision nodes reversed: player 2 at the initial node, player 1 at an
information set containing both successor nodes. -/
def matchingPenniesReversed : ExtensiveForm (Fin 2) (Fin 2) (Fin 2) where
  nodes := mpNodes
  nil_mem := by decide
  tail_mem := by decide
  info := mpCInfo
  avail := fun _ => Finset.univ
  avail_spec := by decide
  info_surj := by decide
  player := fun k => some (1 - k)
  natureProb := fun _ _ => 0
  nature_nonneg := fun k hk => absurd hk (by fin_cases k <;> decide)
  nature_zero := fun k hk => absurd hk (by fin_cases k <;> decide)
  nature_sum := fun k hk => absurd hk (by fin_cases k <;> decide)
  payoff := fun i z => if i = 0 then mpTermPay z.reverse else -mpTermPay z.reverse

theorem matchingPenniesReversed_terminals :
    matchingPenniesReversed.terminals = {[0, 0], [1, 0], [0, 1], [1, 1]} := by decide

/-- **Example 7.C.4** (MWG, p. 225). The reversed tree also has the normal form of Matching
Pennies: the timing of unobserved moves is irrelevant. -/
theorem example_7_C_4 (s : (i : Fin 2) → matchingPenniesReversed.PureStrategy i)
    (i : Fin 2) :
    matchingPenniesReversed.toNormalForm.payoff i s =
      matchingPennies.payoff i (fun j => (s j ⟨1 - j, by fin_cases j <;> rfl⟩).1) := by
  have hz : [(s 0 ⟨1, rfl⟩).1, (s 1 ⟨0, rfl⟩).1] ∈ matchingPenniesReversed.terminals := by
    rw [matchingPenniesReversed_terminals]
    generalize (s 0 ⟨1, rfl⟩).1 = b
    generalize (s 1 ⟨0, rfl⟩).1 = a
    revert a b; decide
  rw [matchingPenniesReversed.toNormalForm_payoff_of_reach (by decide) s hz]
  · fin_cases i <;> simp [matchingPenniesReversed, matchingPennies, mpTermPay]
  · rw [reach_cons, reach_cons, reach_nil,
      show matchingPenniesReversed.info [] = 0 from rfl,
      show matchingPenniesReversed.info [(s 1 ⟨0, rfl⟩).1] = 1 from rfl,
      pureProfile_apply _ s (k := 0) (j := 1) rfl, pureProfile_apply _ s (k := 1) (j := 0) rfl]
    simp

/-- Nature's information set and the players' singletons in Figure 7.C.5. -/
def mpDInfo (x : List (Fin 4)) : Fin 7 :=
  if x = [] then 0 else if x = [2] then 1 else if x = [3] then 2 else if x = [0, 2] then 3
  else if x = [1, 2] then 4 else if x = [0, 3] then 5 else 6

/-- The nodes of Figure 7.C.5. Actions: `0` = H, `1` = T, `2` = "player 1 moves first",
`3` = "player 2 moves first". -/
def mpDNodes : Finset (List (Fin 4)) :=
  {[], [2], [3], [0, 2], [1, 2], [0, 3], [1, 3],
    [0, 0, 2], [1, 0, 2], [0, 1, 2], [1, 1, 2], [0, 0, 3], [1, 0, 3], [0, 1, 3], [1, 1, 3]}

/-- Player 1's payoff at a terminal node of Figure 7.C.5: `-1` if the two pennies match. -/
def mpDPay (z : List (Fin 4)) : ℝ :=
  match z with
  | b :: a :: _ => if a = b then -1 else 1
  | _ => 0

/-- **Example 7.C.5, Figure 7.C.5** (MWG, p. 226). Matching Pennies Version D: a fair coin
(a move of nature with probabilities `1/2`) decides who moves first; the second mover sees
the first mover's penny. -/
noncomputable def matchingPenniesD : ExtensiveForm (Fin 2) (Fin 4) (Fin 7) where
  nodes := mpDNodes
  nil_mem := by decide
  tail_mem := by decide
  info := mpDInfo
  avail := fun k => if k = 0 then {2, 3} else {0, 1}
  avail_spec := by decide
  info_surj := by decide
  player := ![none, some 0, some 1, some 1, some 1, some 0, some 0]
  natureProb := fun k a => if k = 0 ∧ (a = 2 ∨ a = 3) then 1 / 2 else 0
  nature_nonneg := fun k _ a => by split_ifs <;> norm_num
  nature_zero := fun k hk a ha => by
    fin_cases k <;> simp_all
  nature_sum := fun k hk => by
    fin_cases k <;> simp_all
    norm_num
  payoff := fun i z => if i = 0 then mpDPay z else -mpDPay z

theorem matchingPenniesD_info : matchingPenniesD.info = mpDInfo := rfl

theorem matchingPenniesD_player :
    matchingPenniesD.player = ![none, some 0, some 1, some 1, some 1, some 0, some 0] := rfl

theorem matchingPenniesD_natureProb (k : Fin 7) (a : Fin 4) :
    matchingPenniesD.natureProb k a = if k = 0 ∧ (a = 2 ∨ a = 3) then 1 / 2 else 0 := rfl

theorem matchingPenniesD_payoff (i : Fin 2) (z : List (Fin 4)) :
    matchingPenniesD.payoff i z = if i = 0 then mpDPay z else -mpDPay z := rfl

/-- **Example 7.C.5** (MWG, p. 226). Version D is a game of perfect information whose initial
node is a move of nature with two branches of probability `1/2`. -/
theorem example_7_C_5 :
    matchingPenniesD.PerfectInformation ∧
      matchingPenniesD.player (matchingPenniesD.info []) = none ∧
      matchingPenniesD.natureProb 0 2 = 1 / 2 ∧ matchingPenniesD.natureProb 0 3 = 1 / 2 := by
  refine ⟨by unfold ExtensiveForm.PerfectInformation; decide, by decide, ?_, ?_⟩ <;>
    simp [matchingPenniesD]

/-- **Example 7.C.5** (MWG, p. 226). With a move of nature, pure strategies induce a random
outcome: if both players always play H, the two terminal nodes `(H, H)` after either coin
outcome are each reached with probability `1/2`. -/
theorem example_7_C_5_random_outcome :
    let s : (i : Fin 2) → matchingPenniesD.PureStrategy i := fun i =>
      matchingPenniesD.pureOfFun i (fun _ => 0) (fun k hk => by
        fin_cases k <;> simp_all [matchingPenniesD])
    matchingPenniesD.reach (matchingPenniesD.pureProfile s) [0, 0, 2] = 1 / 2 ∧
      matchingPenniesD.reach (matchingPenniesD.pureProfile s) [0, 0, 3] = 1 / 2 ∧
      matchingPenniesD.toNormalForm.payoff 0 s = -1 := by
  intro s
  have h2 : matchingPenniesD.reach (matchingPenniesD.pureProfile s) [0, 0, 2] = 1 / 2 := by
    simp [reach_cons, pureProfile, assemble, pureBeh, s, pureOfFun, matchingPenniesD_info,
      matchingPenniesD_player, matchingPenniesD_natureProb, mpDInfo]
  have h3 : matchingPenniesD.reach (matchingPenniesD.pureProfile s) [0, 0, 3] = 1 / 2 := by
    simp [reach_cons, pureProfile, assemble, pureBeh, s, pureOfFun, matchingPenniesD_info,
      matchingPenniesD_player, matchingPenniesD_natureProb, mpDInfo]
  refine ⟨h2, h3, ?_⟩
  have hT : matchingPenniesD.terminals = {[0, 0, 2], [1, 0, 2], [0, 1, 2], [1, 1, 2],
      [0, 0, 3], [1, 0, 3], [0, 1, 3], [1, 1, 3]} := by decide
  simp only [toNormalForm, hT]
  simp [reach_cons, pureProfile, assemble, pureBeh, s, pureOfFun, matchingPenniesD_info,
    matchingPenniesD_player, matchingPenniesD_natureProb, matchingPenniesD_payoff, mpDInfo, mpDPay]
  norm_num

/-- The nodes of Figure 7.D.2. Actions: `0` = L, `1` = R (player 1), and `2, 3, 4, 5` =
`a, b, c, d` (player 2). -/
def fig7D2Nodes : Finset (List (Fin 6)) :=
  {[], [2], [3], [4], [5], [0, 2], [1, 2], [0, 3], [1, 3], [0, 4], [1, 4], [0, 5], [1, 5]}

/-- Player 1's payoffs in Figure 7.D.2: after player 2's `a` (`c`), L gives `-1` (`+1`) and R
gives `+1` (`+1`); after `b`, both give `-1`; after `d`, L gives `+1` and R gives `-1`. -/
def fig7D2Pay (z : List (Fin 6)) : ℝ :=
  match z with
  | [l, c] =>
    if c = 2 then (if l = 0 then -1 else 1) else if c = 3 then -1 else if c = 4 then 1
    else (if l = 0 then 1 else -1)
  | _ => 0

/-- **Figure 7.D.2** (MWG, p. 231). An extensive form in which player 2 moves first, choosing
among `a, b, c, d`, and player 1 then chooses L or R without observing player 2's choice. -/
def figure_7_D_2 : ExtensiveForm (Fin 2) (Fin 6) (Fin 2) where
  nodes := fig7D2Nodes
  nil_mem := by decide
  tail_mem := by decide
  info := fun x => if x = [] then 0 else 1
  avail := fun k => if k = 0 then {2, 3, 4, 5} else {0, 1}
  avail_spec := by decide
  info_surj := by decide
  player := fun k => some (1 - k)
  natureProb := fun _ _ => 0
  nature_nonneg := fun k hk => absurd hk (by fin_cases k <;> decide)
  nature_zero := fun k hk => absurd hk (by fin_cases k <;> decide)
  nature_sum := fun k hk => absurd hk (by fin_cases k <;> decide)
  payoff := fun i z => if i = 0 then fig7D2Pay z else -fig7D2Pay z

theorem figure_7_D_2_terminals : figure_7_D_2.terminals =
    {[0, 2], [1, 2], [0, 3], [1, 3], [0, 4], [1, 4], [0, 5], [1, 5]} := by decide

/-- The profile of Figure 7.D.2 where player 1 plays `L` (`a = 0`) or `R` (`a = 1`) and
player 2 plays the `m`-th of `a, b, c, d`. -/
def fig7D2Profile (a : Fin 2) (m : Fin 4) : (i : Fin 2) → figure_7_D_2.PureStrategy i :=
  fun i => figure_7_D_2.pureOfFun i
    (fun k => if i = 0 then (if a = 0 then 0 else 1) else
      (if m = 0 then 2 else if m = 1 then 3 else if m = 2 then 4 else 5))
    (fun k hk => by fin_cases i <;> fin_cases k <;> fin_cases m <;> fin_cases a <;>
      simp_all [figure_7_D_2])

theorem figure_7_D_2_payoff_def (i : Fin 2) (z : List (Fin 6)) :
    figure_7_D_2.payoff i z = if i = 0 then fig7D2Pay z else -fig7D2Pay z := rfl

/-- The normal form of Figure 7.D.2: payoffs at the terminal node `[l, c]`, where player 2
chooses `c` at the initial node and player 1 chooses `l` at her information set. -/
theorem figure_7_D_2_payoff (s : (i : Fin 2) → figure_7_D_2.PureStrategy i) (i : Fin 2) :
    figure_7_D_2.toNormalForm.payoff i s =
      figure_7_D_2.payoff i [(s 0 ⟨1, rfl⟩).1, (s 1 ⟨0, rfl⟩).1] := by
  have hz : [(s 0 ⟨1, rfl⟩).1, (s 1 ⟨0, rfl⟩).1] ∈ figure_7_D_2.terminals := by
    have h0 := (s 0 ⟨1, rfl⟩).2
    have h1 := (s 1 ⟨0, rfl⟩).2
    rw [figure_7_D_2_terminals]
    generalize (s 0 ⟨1, rfl⟩).1 = l at h0 ⊢
    generalize (s 1 ⟨0, rfl⟩).1 = c at h1 ⊢
    revert l c; decide
  refine figure_7_D_2.toNormalForm_payoff_of_reach (by decide) s hz ?_ i
  rw [reach_cons, reach_cons, reach_nil,
    show figure_7_D_2.info [] = 0 from rfl,
    show figure_7_D_2.info [(s 1 ⟨0, rfl⟩).1] = 1 from rfl,
    pureProfile_apply _ s (k := 0) (j := 1) rfl, pureProfile_apply _ s (k := 1) (j := 0) rfl]
  simp

/-- **Section 7.D, small type** (MWG, pp. 230-231). Figure 7.D.2 has the normal form of
Figure 7.D.1: relabelling player 1's L, R as H, T and player 2's `a, b, c, d` as strategies
`s₁, …, s₄`, payoffs coincide with those of Version B. Yet Version B has perfect information
and Figure 7.D.2 does not: different extensive forms can have the same normal form. -/
theorem figure_7_D_2_same_normal_form :
    (∀ (a : Fin 2) (m : Fin 4) (i : Fin 2),
      figure_7_D_2.toNormalForm.payoff i (fig7D2Profile a m) =
        matchingPenniesB.toNormalForm.payoff i (mpBProfile a m)) ∧
    Fintype.card (figure_7_D_2.PureStrategy 0) = Fintype.card (matchingPenniesB.PureStrategy 0) ∧
    Fintype.card (figure_7_D_2.PureStrategy 1) = Fintype.card (matchingPenniesB.PureStrategy 1) ∧
    matchingPenniesB.PerfectInformation ∧ ¬ figure_7_D_2.PerfectInformation := by
  refine ⟨fun a m i => ?_, ?_, ?_, example_7_C_1.1,
    by unfold ExtensiveForm.PerfectInformation; decide⟩
  · rw [matchingPenniesB_payoff, figure_7_D_2_payoff]
    fin_cases a <;> fin_cases m <;> fin_cases i <;>
      simp [fig7D2Profile, pureOfFun, figure_7_D_2_payoff_def, fig7D2Pay, mpBProfile,
        matchingPenniesB_info, matchingPenniesB_payoff_def, mpBInfo, mpBResponse, mpTermPay, mpPay]
  · rw [card_pureStrategy, card_pureStrategy]; decide
  · rw [card_pureStrategy, card_pureStrategy]; decide

end MWG.NoncooperativeGames

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Meeting in New York, Exercise 7.C.1, and two games without perfect recall

MWG, Example 7.B.3 (p. 221), Exercise 7.C.1 (p. 233) and Figure 7.C.4 (pp. 224-225).

* `meetingNY P`: the normal form of Meeting in New York with a set `P` of meeting places;
  payoffs are 100 dollars to each if they meet and 0 otherwise. The players' interests are
  completely aligned (`example_7_B_3_aligned`), yet each player's optimal choice depends on
  where he thinks the other will go (`example_7_B_3_best_reply`).
* `exercise7C1`: the game tree of Exercise 7.C.1 with the two places Grand Central Station
  (`0`) and the Empire State Building (`1`); the players choose simultaneously, which is
  drawn as Mr. Schelling not observing Mr. Thomas's choice. Its normal form is
  `meetingNY (Fin 2)` (`exercise_7_C_1`).
* `figure7C4a`, `figure7C4b`: the two games of Figure 7.C.4. In (a) player 2 forgets player
  1's first move, in (b) player 1 forgets her own first move; both violate condition (ii) of
  perfect recall for that player, while condition (i) holds.
-/

namespace MWG.NoncooperativeGames

open ExtensiveForm

/-- **Example 7.B.3** (MWG, p. 221). Meeting in New York: Mr. Thomas (`0`) and Mr. Schelling
(`1`) each choose a place in `P`; each gets 100 dollars if they choose the same place and
0 otherwise. -/
def meetingNY (P : Type*) [DecidableEq P] : NormalForm (Fin 2) (fun _ => P) where
  payoff _ s := if s 0 = s 1 then 100 else 0

/-- **Example 7.B.3** (MWG, p. 221). The players' interests are completely aligned: their
payoffs coincide at every strategy profile. -/
theorem example_7_B_3_aligned (P : Type*) [DecidableEq P] (s : (i : Fin 2) → P) :
    (meetingNY P).payoff 0 s = (meetingNY P).payoff 1 s := rfl

/-- **Example 7.B.3** (MWG, p. 221). Each player's optimal action depends on what he thinks
the other will do: against a place `p`, going to `p` is strictly better than going anywhere
else. Hence with two or more places, different beliefs call for different actions. -/
theorem example_7_B_3_best_reply (P : Type*) [DecidableEq P] (p q : P) (hq : q ≠ p) :
    (meetingNY P).payoff 0 (![q, p]) < (meetingNY P).payoff 0 (![p, p]) ∧
      (meetingNY P).payoff 1 (![p, q]) < (meetingNY P).payoff 1 (![p, p]) := by
  simp [meetingNY, hq, Ne.symm hq]

/-- **Example 7.B.3** (MWG, p. 221). Unlike Matching Pennies, Meeting in New York is not a
situation of pure conflict: it is not zero-sum. -/
theorem example_7_B_3_not_zeroSum : ¬ (meetingNY (Fin 2)).IsZeroSum := by
  intro h
  have := h (fun _ => 0)
  rw [Fin.sum_univ_two] at this
  norm_num [meetingNY] at this

/-- **Example 7.B.3** (MWG, p. 221). With the two places of Exercise 7.C.1, Mr. Thomas's best
reply to Grand Central (`0`) is Grand Central and to the Empire State Building (`1`) is the
Empire State Building. -/
theorem example_7_B_3_two_places :
    (meetingNY (Fin 2)).payoff 0 (![1, 0]) < (meetingNY (Fin 2)).payoff 0 (![0, 0]) ∧
      (meetingNY (Fin 2)).payoff 0 (![0, 1]) < (meetingNY (Fin 2)).payoff 0 (![1, 1]) :=
  ⟨(example_7_B_3_best_reply (Fin 2) 0 1 (by decide)).1,
    (example_7_B_3_best_reply (Fin 2) 1 0 (by decide)).1⟩

/-- Payoff of each player at a terminal node of the Exercise 7.C.1 tree. -/
def nyTermPay (z : List (Fin 2)) : ℝ :=
  match z with
  | b :: a :: _ => if a = b then 100 else 0
  | _ => 0

/-- **Exercise 7.C.1** (MWG, p. 233). The extensive form of Meeting in New York with two
places, Grand Central Station (`0`) and the Empire State Building (`1`): Mr. Thomas chooses
first, Mr. Schelling chooses without observing that choice (one information set). -/
def exercise7C1 : ExtensiveForm (Fin 2) (Fin 2) (Fin 2) where
  nodes := {[], [0], [1], [0, 0], [1, 0], [0, 1], [1, 1]}
  nil_mem := by decide
  tail_mem := by decide
  info := fun x => if x = [] then 0 else 1
  avail := fun _ => Finset.univ
  avail_spec := by decide
  info_surj := by decide
  player := fun k => some k
  natureProb := fun _ _ => 0
  nature_nonneg := fun k hk => absurd hk (by fin_cases k <;> decide)
  nature_zero := fun k hk => absurd hk (by fin_cases k <;> decide)
  nature_sum := fun k hk => absurd hk (by fin_cases k <;> decide)
  payoff := fun _ z => nyTermPay z

theorem exercise7C1_terminals :
    exercise7C1.terminals = {[0, 0], [1, 0], [0, 1], [1, 1]} := by decide

/-- **Exercise 7.C.1** (MWG, p. 233). The tree has imperfect information and perfect recall,
and its normal form is Meeting in New York with the two places. -/
theorem exercise_7_C_1 :
    ¬ exercise7C1.PerfectInformation ∧ exercise7C1.PerfectRecall ∧
    ∀ (s : (i : Fin 2) → exercise7C1.PureStrategy i) (i : Fin 2),
      exercise7C1.toNormalForm.payoff i s = (meetingNY (Fin 2)).payoff i
        (fun j => (s j ⟨j, rfl⟩).1) := by
  refine ⟨by unfold ExtensiveForm.PerfectInformation; decide,
    ⟨by unfold ExtensiveForm.NoAbsentMindedness; decide, fun i => ?_⟩, fun s i => ?_⟩
  · unfold ExtensiveForm.RecallFor; fin_cases i <;> decide
  have hz : [(s 1 ⟨1, rfl⟩).1, (s 0 ⟨0, rfl⟩).1] ∈ exercise7C1.terminals := by
    rw [exercise7C1_terminals]
    generalize (s 1 ⟨1, rfl⟩).1 = b
    generalize (s 0 ⟨0, rfl⟩).1 = a
    revert a b; decide
  rw [exercise7C1.toNormalForm_payoff_of_reach (by decide) s hz]
  · simp [exercise7C1, meetingNY, nyTermPay]
  · rw [reach_cons, reach_cons, reach_nil,
      show exercise7C1.info [] = 0 from rfl,
      show exercise7C1.info [(s 0 ⟨0, rfl⟩).1] = 1 from rfl,
      pureProfile_apply _ s (k := 0) (j := 0) rfl, pureProfile_apply _ s (k := 1) (j := 1) rfl]
    simp

/-- The information sets of Figure 7.C.4(a). Actions: `0, 1` = `ℓ, r`; `2, 3` = L, R;
`4, 5` = `x, y`; `6, 7` = `a, b`. -/
def fig7C4aInfo (x : List (Fin 8)) : Fin 6 :=
  if x = [] then 0 else if x = [0] then 1 else if x = [1] then 2 else if x = [3, 0] then 3
  else if x = [2, 1] then 4 else 5

/-- **Figure 7.C.4(a)** (MWG, p. 225). Player 1 chooses `ℓ` or `r`; player 2, seeing it,
chooses L or R; after (`ℓ`, R) and after (`r`, L) player 1 chooses `x` or `y`; after `x`
player 2 moves again (`a` or `b`) at one information set containing both nodes, so she no
longer knows whether player 1 chose `ℓ` or `r`. Payoffs are not given and set to `0`. -/
def figure7C4a : ExtensiveForm (Fin 2) (Fin 8) (Fin 6) where
  nodes := {[], [0], [1], [2, 0], [3, 0], [2, 1], [3, 1], [4, 3, 0], [5, 3, 0], [4, 2, 1],
    [5, 2, 1], [6, 4, 3, 0], [7, 4, 3, 0], [6, 4, 2, 1], [7, 4, 2, 1]}
  nil_mem := by decide
  tail_mem := by decide
  info := fig7C4aInfo
  avail := ![{0, 1}, {2, 3}, {2, 3}, {4, 5}, {4, 5}, {6, 7}]
  avail_spec := by decide
  info_surj := by decide
  player := ![some 0, some 1, some 1, some 0, some 0, some 1]
  natureProb := fun _ _ => 0
  nature_nonneg := fun k hk => absurd hk (by fin_cases k <;> decide)
  nature_zero := fun k hk => absurd hk (by fin_cases k <;> decide)
  nature_sum := fun k hk => absurd hk (by fin_cases k <;> decide)
  payoff := fun _ _ => 0

/-- **Figure 7.C.4(a)** (MWG, pp. 224-225). Player 2 forgets a move of player 1 that she once
knew: condition (ii) of perfect recall fails for player 2 (it holds for player 1, and
condition (i) holds), so the game does not have perfect recall. -/
theorem figure_7_C_4a :
    ¬ figure7C4a.PerfectRecall ∧ ¬ figure7C4a.RecallFor 1 ∧ figure7C4a.RecallFor 0 ∧
      figure7C4a.NoAbsentMindedness := by
  have h1 : ¬ figure7C4a.RecallFor 1 := by unfold ExtensiveForm.RecallFor; decide
  exact ⟨fun h => h1 (h.2 1), h1, by unfold ExtensiveForm.RecallFor; decide,
    by unfold ExtensiveForm.NoAbsentMindedness; decide⟩

/-- The information sets of Figure 7.C.4(b). Actions: `0, 1` = `ℓ, r`; `2, 3` = L, R;
`4, 5` = `x, y`. -/
def fig7C4bInfo (x : List (Fin 6)) : Fin 4 :=
  if x = [] then 0 else if x = [0] then 1 else if x = [1] then 2 else 3

/-- **Figure 7.C.4(b)** (MWG, p. 225). Player 1 chooses `ℓ` or `r`, player 2 sees it and
chooses L or R, and player 1 then chooses `x` or `y` at one information set containing all
four nodes: she forgets her own first move. Payoffs are not given and set to `0`. -/
def figure7C4b : ExtensiveForm (Fin 2) (Fin 6) (Fin 4) where
  nodes := {[], [0], [1], [2, 0], [3, 0], [2, 1], [3, 1], [4, 2, 0], [5, 2, 0], [4, 3, 0],
    [5, 3, 0], [4, 2, 1], [5, 2, 1], [4, 3, 1], [5, 3, 1]}
  nil_mem := by decide
  tail_mem := by decide
  info := fig7C4bInfo
  avail := ![{0, 1}, {2, 3}, {2, 3}, {4, 5}]
  avail_spec := by decide
  info_surj := by decide
  player := ![some 0, some 1, some 1, some 0]
  natureProb := fun _ _ => 0
  nature_nonneg := fun k hk => absurd hk (by fin_cases k <;> decide)
  nature_zero := fun k hk => absurd hk (by fin_cases k <;> decide)
  nature_sum := fun k hk => absurd hk (by fin_cases k <;> decide)
  payoff := fun _ _ => 0

/-- **Figure 7.C.4(b)** (MWG, pp. 224-225). Player 1 forgets her own previous move:
condition (ii) of perfect recall fails for player 1 (it holds for player 2, and condition (i)
holds), so the game does not have perfect recall. -/
theorem figure_7_C_4b :
    ¬ figure7C4b.PerfectRecall ∧ ¬ figure7C4b.RecallFor 0 ∧ figure7C4b.RecallFor 1 ∧
      figure7C4b.NoAbsentMindedness := by
  have h0 : ¬ figure7C4b.RecallFor 0 := by unfold ExtensiveForm.RecallFor; decide
  exact ⟨fun h => h0 (h.2 0), h0, by unfold ExtensiveForm.RecallFor; decide,
    by unfold ExtensiveForm.NoAbsentMindedness; decide⟩

end MWG.NoncooperativeGames

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Tick-Tack-Toe

MWG, Example 7.B.2 (p. 220), Figure 7.B.1, and Example 7.C.2 with Figure 7.C.2 (pp. 222-223).

The board's squares are `Fin 9` (square `3r + c` in row `r`, column `c`). A node is the
sequence of squares marked so far, most recent first; X (player `0`) marks at even times and
O (player `1`) at odd times. A sequence is a node when its squares are distinct and no
earlier position already had three marks of one player in a row (the game stops at the first
three-in-a-row). Every decision node is its own information set.

* `tickTackToe`: the extensive form (the full tree that Figure 7.C.2 draws in part).
* `example_7_C_2_perfectInformation`: it is a game of perfect information (MWG, p. 222).
* `example_7_B_2_zero_sum`: payoffs (`+1` to the winner, `-1` to the loser, `0` for a tie) sum
  to zero at every node, because at most one player can have three in a row.
* `example_7_C_2_paths`: the position with X in the two left corners and O in the two right
  corners is reached by different move sequences, which are different nodes of the tree
  (MWG, p. 222: nodes record how a position was reached).
-/

namespace MWG.NoncooperativeGames

/-- The eight lines of the board: rows, columns and diagonals. -/
def tttLines : List (List (Fin 9)) :=
  [[0, 1, 2], [3, 4, 5], [6, 7, 8], [0, 3, 6], [1, 4, 7], [2, 5, 8], [0, 4, 8], [2, 4, 6]]

/-- The squares marked by player `p` (`0` = X, `1` = O) in a history (most recent first); the
mark `a` in `a :: t` was made at time `t.length`, by X if it is even. -/
def tttMarks (p : ℕ) : List (Fin 9) → List (Fin 9)
  | [] => []
  | a :: t => if t.length % 2 = p then a :: tttMarks p t else tttMarks p t

/-- Player `p` has three marks in a row. -/
abbrev tttWins (p : ℕ) (x : List (Fin 9)) : Prop := ∃ l ∈ tttLines, ∀ q ∈ l, q ∈ tttMarks p x

/-- Somebody has three in a row. -/
abbrev tttWon (x : List (Fin 9)) : Prop := tttWins 0 x ∨ tttWins 1 x

/-- No strictly earlier position was already won. -/
abbrev tttNoEarlyWin (x : List (Fin 9)) : Prop :=
  ∀ k ∈ Finset.range x.length, ¬ tttWon (x.drop (k + 1))

/-- A legal history: distinct squares, and play stopped at the first three-in-a-row. -/
abbrev tttValid (x : List (Fin 9)) : Prop := x.length ≤ 9 ∧ x.Nodup ∧ tttNoEarlyWin x

/-- The nodes of Tick-Tack-Toe. -/
def tttNodes : Finset (List (Fin 9)) :=
  ((Finset.range 10).biUnion fun n =>
    (Finset.univ : Finset (Fin n → Fin 9)).image fun f => List.ofFn f).filter tttValid

theorem mem_tttNodes {x : List (Fin 9)} : x ∈ tttNodes ↔ tttValid x := by
  simp only [tttNodes, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_range,
    Finset.mem_image, Finset.mem_univ, true_and, and_iff_right_iff_imp]
  intro h
  exact ⟨x.length, by have := h.1; omega, x.get, List.ofFn_get x⟩

theorem tttNoEarlyWin_cons (a : Fin 9) (x : List (Fin 9)) :
    tttNoEarlyWin (a :: x) ↔ ¬ tttWon x ∧ tttNoEarlyWin x := by
  simp only [tttNoEarlyWin, Finset.mem_range, List.length_cons]
  constructor
  · intro h
    refine ⟨by simpa using h 0 (by omega), fun k hk => ?_⟩
    simpa using h (k + 1) (by omega)
  · rintro ⟨h0, h⟩ k hk
    cases k with
    | zero => simpa using h0
    | succ k => simpa using h k (by omega)

theorem length_lt_of_nodup_cons {a : Fin 9} {x : List (Fin 9)} (h : (a :: x).Nodup) :
    x.length < 9 := by
  have := h.length_le_card
  simp at this
  omega

/-- A non-full history with distinct squares leaves a free square. -/
theorem exists_not_mem {x : List (Fin 9)} (hn : x.Nodup) (hl : x.length < 9) :
    ∃ b, b ∉ x := by
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset (Fin 9)) ⊆ x.toFinset := fun b _ => List.mem_toFinset.2 (h b)
  have := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hn] at this
  simp at this
  omega

/-- The decision nodes: legal, not yet won, and not full. -/
def tttDecision : Finset (List (Fin 9)) :=
  tttNodes.filter fun x => ¬ tttWon x ∧ x.length < 9

theorem tttMarks_nil (p : ℕ) : tttMarks p [] = [] := rfl

theorem tttLines_ne_nil : ∀ l ∈ tttLines, l ≠ [] := by decide

theorem not_tttWins_nil (p : ℕ) : ¬ tttWins p [] := by
  rintro ⟨l, hl, h⟩
  obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil l (tttLines_ne_nil l hl)
  simpa [tttMarks_nil] using h q hq

theorem nil_mem_tttDecision : [] ∈ tttDecision := by
  simp only [tttDecision, Finset.mem_filter, mem_tttNodes]
  refine ⟨⟨by simp, List.nodup_nil, fun k hk => by simp at hk⟩, ?_, by simp⟩
  rintro (h | h) <;> exact not_tttWins_nil _ h

open Classical in
/-- The information set of a node: the node itself (perfect information). -/
noncomputable def tttInfo (x : List (Fin 9)) : {x // x ∈ tttDecision} :=
  if h : x ∈ tttDecision then ⟨x, h⟩ else ⟨[], nil_mem_tttDecision⟩

theorem cons_mem_tttNodes_iff {a : Fin 9} {x : List (Fin 9)} :
    a :: x ∈ tttNodes ↔ a ∉ x ∧ x ∈ tttNodes ∧ ¬ tttWon x := by
  simp only [mem_tttNodes, tttValid, List.nodup_cons, tttNoEarlyWin_cons]
  constructor
  · rintro ⟨-, ⟨ha, hn⟩, hw, he⟩
    exact ⟨ha, ⟨(length_lt_of_nodup_cons (List.nodup_cons.2 ⟨ha, hn⟩)).le, hn, he⟩, hw⟩
  · rintro ⟨ha, ⟨-, hn, he⟩, hw⟩
    have := length_lt_of_nodup_cons (List.nodup_cons.2 ⟨ha, hn⟩)
    simp only [List.length_cons]
    exact ⟨by omega, ⟨ha, hn⟩, hw, he⟩

theorem mem_tttDecision_of_cons {b : Fin 9} {x : List (Fin 9)} (h : b :: x ∈ tttNodes) :
    x ∈ tttDecision := by
  obtain ⟨hb, hx, hw⟩ := cons_mem_tttNodes_iff.1 h
  have hn := (mem_tttNodes.1 h).2.1
  exact Finset.mem_filter.2 ⟨hx, hw, length_lt_of_nodup_cons hn⟩

/-- Player X (`0`) moves when an even number of squares is marked, player O (`1`) when it is
odd. -/
def tttPlayer (k : {x // x ∈ tttDecision}) : Fin 2 := ⟨k.1.length % 2, Nat.mod_lt _ two_pos⟩

/-- Payoff of player `i`: `+1` for three in a row, `-1` if the opponent has three in a row,
`0` otherwise. -/
def tttPayoff (i : Fin 2) (z : List (Fin 9)) : ℝ :=
  if tttWins i z then 1 else if tttWins (1 - i : Fin 2) z then -1 else 0

/-- **Examples 7.B.2 and 7.C.2, Figures 7.B.1 and 7.C.2** (MWG, pp. 220-223). Tick-Tack-Toe
in extensive form. -/
noncomputable def tickTackToe : ExtensiveForm (Fin 2) (Fin 9) {x // x ∈ tttDecision} where
  nodes := tttNodes
  nil_mem := (Finset.mem_filter.1 nil_mem_tttDecision).1
  tail_mem := fun x hx => by
    cases x with
    | nil => exact hx
    | cons a t => exact (cons_mem_tttNodes_iff.1 hx).2.1
  info := tttInfo
  avail := fun k => Finset.univ.filter fun a => a ∉ k.1
  avail_spec := fun x _ ⟨b, hb⟩ a => by
    have hd := mem_tttDecision_of_cons hb
    have hw := (cons_mem_tttNodes_iff.1 hb).2
    simp only [tttInfo, hd, dite_true, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [cons_mem_tttNodes_iff]
    exact ⟨fun h => h.1, fun h => ⟨h, hw⟩⟩
  info_surj := fun k => by
    obtain ⟨x, hx⟩ := k
    obtain ⟨hxn, hw, hl⟩ := Finset.mem_filter.1 hx
    obtain ⟨b, hb⟩ := exists_not_mem (mem_tttNodes.1 hxn).2.1 hl
    exact ⟨x, hxn, ⟨b, cons_mem_tttNodes_iff.2 ⟨hb, hxn, hw⟩⟩, by simp [tttInfo, hx]⟩
  player := fun k => some (tttPlayer k)
  natureProb := fun _ _ => 0
  nature_nonneg := fun _ hk => absurd hk (Option.some_ne_none _)
  nature_zero := fun _ hk => absurd hk (Option.some_ne_none _)
  nature_sum := fun _ hk => absurd hk (Option.some_ne_none _)
  payoff := tttPayoff

theorem tickTackToe_info : tickTackToe.info = tttInfo := by
  simp only [tickTackToe]

theorem tickTackToe_player (k : {x // x ∈ tttDecision}) :
    tickTackToe.player k = some (tttPlayer k) := rfl

theorem tickTackToe_payoff : tickTackToe.payoff = tttPayoff := rfl

/-- **Example 7.C.2** (MWG, p. 222). Tick-Tack-Toe is a game of perfect information: each
player observes all previous moves. -/
theorem example_7_C_2_perfectInformation : tickTackToe.PerfectInformation := by
  intro x _ x' _ ⟨b, hb⟩ ⟨b', hb'⟩ he
  have hd := mem_tttDecision_of_cons hb
  have hd' := mem_tttDecision_of_cons hb'
  rw [tickTackToe_info] at he
  simp only [tttInfo, hd, hd', dite_true, Subtype.mk.injEq] at he
  exact he

/-- **Example 7.B.2** (MWG, p. 220). X moves first and the players alternate. -/
theorem example_7_B_2_alternate (x : List (Fin 9)) (hx : x ∈ tttDecision) :
    tickTackToe.player (tickTackToe.info x) = some ⟨x.length % 2, Nat.mod_lt _ two_pos⟩ := by
  rw [tickTackToe_info, tickTackToe_player]
  simp [tttInfo, hx, tttPlayer]

theorem tttMarks_cons_other (a : Fin 9) (t : List (Fin 9)) (p : ℕ) (hp : t.length % 2 ≠ p) :
    tttMarks p (a :: t) = tttMarks p t := by
  simp [tttMarks, hp]

/-- At most one player has three in a row at any node: only the last mover can have just
completed a line, and the other player had not won before. -/
theorem ttt_not_both_win {z : List (Fin 9)} (hz : z ∈ tttNodes) (p q : ℕ) (hp : p < 2)
    (hq : q < 2) (hpq : p ≠ q) : ¬ (tttWins p z ∧ tttWins q z) := by
  rintro ⟨hwp, hwq⟩
  cases z with
  | nil => exact not_tttWins_nil p hwp
  | cons a t =>
    have hw := (cons_mem_tttNodes_iff.1 hz).2.2
    -- the player who did not make the last mark
    have key : ∀ r, r < 2 → t.length % 2 ≠ r → tttWins r (a :: t) → tttWon t := by
      intro r hr hne ⟨l, hl, h⟩
      rw [tttMarks_cons_other a t r hne] at h
      have : r = 0 ∨ r = 1 := by omega
      rcases this with rfl | rfl
      · exact Or.inl ⟨l, hl, h⟩
      · exact Or.inr ⟨l, hl, h⟩
    by_cases h : t.length % 2 = p
    · exact hw (key q hq (by omega) hwq)
    · exact hw (key p hp h hwp)

/-- **Example 7.B.2** (MWG, pp. 220-221). Tick-Tack-Toe is zero-sum: at every node the
players' payoffs sum to zero. -/
theorem example_7_B_2_zero_sum (z : List (Fin 9)) (hz : z ∈ tickTackToe.nodes) :
    tickTackToe.payoff 0 z + tickTackToe.payoff 1 z = 0 := by
  have h01 := ttt_not_both_win hz 0 1 (by norm_num) (by norm_num) (by norm_num)
  have e0 : ((0 : Fin 2) : ℕ) = 0 := rfl
  have e1 : ((1 : Fin 2) : ℕ) = 1 := rfl
  have e10 : (1 - 0 : Fin 2) = 1 := rfl
  have e11 : (1 - 1 : Fin 2) = 0 := rfl
  rw [tickTackToe_payoff]
  by_cases h0 : tttWins 0 z <;> by_cases h1 : tttWins 1 z
  · exact absurd ⟨h0, h1⟩ h01
  all_goals
    simp only [tttPayoff, e0, e1, e10, e11, h0, h1, ite_true, ite_false]
    norm_num

/-- **Example 7.C.2** (MWG, p. 222). The position with X in the two left corners (squares 0
and 6) and O in the two right corners (squares 2 and 8) is reached by two different move
sequences; these are two different nodes of the game tree with the same marks. -/
theorem example_7_C_2_paths :
    [8, 6, 2, 0] ∈ tickTackToe.nodes ∧ [8, 0, 2, 6] ∈ tickTackToe.nodes ∧
      ([8, 6, 2, 0] : List (Fin 9)) ≠ [8, 0, 2, 6] ∧
      (tttMarks 0 [8, 6, 2, 0]).toFinset = (tttMarks 0 [8, 0, 2, 6]).toFinset ∧
      (tttMarks 1 [8, 6, 2, 0]).toFinset = (tttMarks 1 [8, 0, 2, 6]).toFinset := by
  refine ⟨mem_tttNodes.2 ?_, mem_tttNodes.2 ?_, by decide, by decide, by decide⟩ <;>
    unfold tttValid tttNoEarlyWin tttWon tttWins <;> decide

end MWG.NoncooperativeGames

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercise 7.E.1: realization equivalence in the game of Figure 7.Ex.1

MWG, Exercise 7.E.1 and Figure 7.Ex.1, pp. 233-234.

Figure 7.Ex.1: player 1 chooses L, M or R at the initial node; L ends the game (`T₀`). After
M or R, player 2 chooses `ℓ` or `r` without observing which (one information set). Player 1
then chooses `x` or `y`, knowing whether she played M or R but not player 2's move: her two
nodes after M form one information set, her two nodes after R another. The terminal nodes are
`T₁, …, T₈`.

Encoding. Players `Fin 2` (`0` = player 1). Actions `Fin 7`: `0, 1, 2` = L, M, R; `3, 4` =
`ℓ, r`; `5, 6` = `x, y`. Information sets `Fin 4`: `0` the initial node, `1` player 2's,
`2` player 1's after M, `3` player 1's after R. In the game of part (d), `exercise7E1Merged`,
player 1's last two information sets are merged into `2` (labels `Fin 3`).
Payoffs are not specified by the exercise and are set to `0`.

* (a) `exercise_7_E_1a`: player 1 has `3 · 2 · 2 = 12` pure strategies, player 2 has `2`.
* (b) `exercise_7_E_1b`: every behaviour strategy of player 1 has a realization-equivalent
  mixed strategy (an instance of `kuhn_behavior_to_mixed`; the game has perfect recall).
* (c) `exercise_7_E_1c`: every mixed strategy of player 1 has a realization-equivalent
  behaviour strategy (an instance of `kuhn_mixed_to_behavior`).
* (d) `exercise_7_E_1d`: after merging, the game violates perfect recall (player 1 forgets
  whether she played M or R), the result of (b) still holds (no information set is crossed
  twice), and the result of (c) fails: the mixed strategy `½ (M, x) + ½ (R, y)` has no
  realization-equivalent behaviour strategy.
-/

namespace MWG.NoncooperativeGames

open ExtensiveForm

/-- The nodes of Figure 7.Ex.1 (most recent action first). -/
def ex7E1Nodes : Finset (List (Fin 7)) :=
  {[], [0], [1], [2], [3, 1], [4, 1], [3, 2], [4, 2],
    [5, 3, 1], [6, 3, 1], [5, 4, 1], [6, 4, 1], [5, 3, 2], [6, 3, 2], [5, 4, 2], [6, 4, 2]}

/-- The information sets of Figure 7.Ex.1. -/
def ex7E1Info (x : List (Fin 7)) : Fin 4 :=
  if x = [] then 0 else if x.length = 1 then 1 else if x.getLast? = some 1 then 2 else 3

/-- **Exercise 7.E.1, Figure 7.Ex.1** (MWG, pp. 233-234). The game of Figure 7.Ex.1. -/
def exercise7E1 : ExtensiveForm (Fin 2) (Fin 7) (Fin 4) where
  nodes := ex7E1Nodes
  nil_mem := by decide
  tail_mem := by decide
  info := ex7E1Info
  avail := ![{0, 1, 2}, {3, 4}, {5, 6}, {5, 6}]
  avail_spec := by decide
  info_surj := by decide
  player := ![some 0, some 1, some 0, some 0]
  natureProb := fun _ _ => 0
  nature_nonneg := fun k hk => absurd hk (by fin_cases k <;> decide)
  nature_zero := fun k hk => absurd hk (by fin_cases k <;> decide)
  nature_sum := fun k hk => absurd hk (by fin_cases k <;> decide)
  payoff := fun _ _ => 0

/-- **Exercise 7.E.1(a)** (MWG, p. 233). Player 1's pure strategies choose one of L, M, R
and one of `x, y` at each of her two later information sets: `3 · 2 · 2 = 12` of them. Player
2 has the two strategies `ℓ` and `r`. -/
theorem exercise_7_E_1a :
    Fintype.card (exercise7E1.PureStrategy 0) = 12 ∧
      Fintype.card (exercise7E1.PureStrategy 1) = 2 := by
  rw [card_pureStrategy, card_pureStrategy]
  decide

/-- The game of Figure 7.Ex.1 has perfect recall. -/
theorem exercise7E1_perfectRecall : exercise7E1.PerfectRecall := by
  refine ⟨by unfold ExtensiveForm.NoAbsentMindedness; decide, fun i => ?_⟩
  unfold ExtensiveForm.RecallFor
  fin_cases i <;> decide

/-- **Exercise 7.E.1(b)** (MWG, p. 233). For any behaviour strategy of player 1 there is a
realization-equivalent mixed strategy. -/
theorem exercise_7_E_1b (β : Fin 4 → Fin 7 → ℝ) (hβ : exercise7E1.IsBehaviorStrategy 0 β) :
    ∃ σ : exercise7E1.PureStrategy 0 → ℝ,
      IsMixedStrategy σ ∧ exercise7E1.RealizationEquivalent 0 σ β :=
  exercise7E1.kuhn_behavior_to_mixed exercise7E1_perfectRecall.1 hβ

/-- **Exercise 7.E.1(c)** (MWG, p. 234). For any mixed strategy of player 1 there is a
realization-equivalent behaviour strategy. -/
theorem exercise_7_E_1c (σ : exercise7E1.PureStrategy 0 → ℝ) (hσ : IsMixedStrategy σ) :
    ∃ β : Fin 4 → Fin 7 → ℝ,
      exercise7E1.IsBehaviorStrategy 0 β ∧ exercise7E1.RealizationEquivalent 0 σ β :=
  exercise7E1.kuhn_mixed_to_behavior (exercise7E1_perfectRecall.2 0) hσ

/-- A pure strategy of each player in Figure 7.Ex.1 (L, `ℓ`, `x`, `x`). -/
def ex7E1Pure (j : Fin 2) : exercise7E1.PureStrategy j :=
  exercise7E1.pureOfFun j ![0, 3, 5, 5] (by revert j; decide)

/-- **Exercise 7.E.1(c)** (MWG, p. 234), against mixed rivals: an instance of
`kuhn_mixed_rivals` with player 1's induced behaviour strategy. -/
theorem exercise_7_E_1c_mixed_rivals :
    ∀ z ∈ exercise7E1.terminals,
      exercise7E1.mixedOutcome (fun j => pureMixed (ex7E1Pure j)) z =
        ∑ s : (j : Fin 2) → exercise7E1.PureStrategy j,
          (∏ j, pureMixed (ex7E1Pure j) (s j)) *
            exercise7E1.reach (exercise7E1.assemble (Function.update
              (fun j => exercise7E1.pureBeh (s j)) 0
              (exercise7E1.behaviorOfMixed (pureMixed (ex7E1Pure 0))))) z :=
  exercise7E1.kuhn_mixed_rivals (exercise7E1_perfectRecall.2 0) _
    (isMixedStrategy_pureMixed _)

/-- The information sets of the merged game of Exercise 7.E.1(d). -/
def ex7E1MergedInfo (x : List (Fin 7)) : Fin 3 :=
  if x = [] then 0 else if x.length = 1 then 1 else 2

/-- **Exercise 7.E.1(d)** (MWG, p. 234). Figure 7.Ex.1 with player 1's second-round
information sets merged into one. -/
def exercise7E1Merged : ExtensiveForm (Fin 2) (Fin 7) (Fin 3) where
  nodes := ex7E1Nodes
  nil_mem := by decide
  tail_mem := by decide
  info := ex7E1MergedInfo
  avail := ![{0, 1, 2}, {3, 4}, {5, 6}]
  avail_spec := by decide
  info_surj := by decide
  player := ![some 0, some 1, some 0]
  natureProb := fun _ _ => 0
  nature_nonneg := fun k hk => absurd hk (by fin_cases k <;> decide)
  nature_zero := fun k hk => absurd hk (by fin_cases k <;> decide)
  nature_sum := fun k hk => absurd hk (by fin_cases k <;> decide)
  payoff := fun _ _ => 0

theorem exercise7E1Merged_info : exercise7E1Merged.info = ex7E1MergedInfo := rfl

theorem exercise7E1Merged_player :
    exercise7E1Merged.player = ![some 0, some 1, some 0] := rfl

/-- Player 1's pure strategy "M, then `x`" in the merged game. -/
def ex7E1MX : exercise7E1Merged.PureStrategy 0 :=
  exercise7E1Merged.pureOfFun 0 (fun k => if k = 0 then 1 else 5) (by decide)

/-- Player 1's pure strategy "R, then `y`" in the merged game. -/
def ex7E1RY : exercise7E1Merged.PureStrategy 0 :=
  exercise7E1Merged.pureOfFun 0 (fun k => if k = 0 then 2 else 6) (by decide)

/-- The mixed strategy `½ (M, x) + ½ (R, y)` of Exercise 7.E.1(d). -/
noncomputable def ex7E1Sigma : exercise7E1Merged.PureStrategy 0 → ℝ :=
  fun s => (1 / 2) * pureMixed ex7E1MX s + (1 / 2) * pureMixed ex7E1RY s

theorem ex7E1MX_ne_RY : ex7E1MX ≠ ex7E1RY := by
  intro h
  have := congrArg (fun s => (s ⟨0, rfl⟩).1) h
  simp [ex7E1MX, ex7E1RY, pureOfFun] at this

theorem isMixedStrategy_ex7E1Sigma : IsMixedStrategy ex7E1Sigma := by
  refine ⟨fun s => ?_, ?_⟩
  · unfold ex7E1Sigma pureMixed
    split_ifs <;> norm_num
  · simp [ex7E1Sigma, pureMixed, Finset.sum_add_distrib]
    norm_num

/-- **Exercise 7.E.1(d)** (MWG, p. 234). After merging player 1's second-round information
sets: (i) perfect recall fails, because player 1 forgets whether she played M or R
(condition (ii) fails for player 1) although no information set is crossed twice;
(ii) the result of (b) still holds; (iii) the result of (c) fails: the mixed strategy
`½ (M, x) + ½ (R, y)` has no realization-equivalent behaviour strategy. -/
theorem exercise_7_E_1d :
    ¬ exercise7E1Merged.PerfectRecall ∧ ¬ exercise7E1Merged.RecallFor 0 ∧
    exercise7E1Merged.NoAbsentMindedness ∧
    (∀ β : Fin 3 → Fin 7 → ℝ, exercise7E1Merged.IsBehaviorStrategy 0 β →
      ∃ σ : exercise7E1Merged.PureStrategy 0 → ℝ,
        IsMixedStrategy σ ∧ exercise7E1Merged.RealizationEquivalent 0 σ β) ∧
    IsMixedStrategy ex7E1Sigma ∧
    ¬ ∃ β : Fin 3 → Fin 7 → ℝ, exercise7E1Merged.IsBehaviorStrategy 0 β ∧
        exercise7E1Merged.RealizationEquivalent 0 ex7E1Sigma β := by
  have hNR : ¬ exercise7E1Merged.RecallFor 0 := by
    unfold ExtensiveForm.RecallFor; decide
  have hNA : exercise7E1Merged.NoAbsentMindedness := by
    unfold ExtensiveForm.NoAbsentMindedness; decide
  refine ⟨fun h => hNR (h.2 0), hNR, hNA, fun β hβ => exercise7E1Merged.kuhn_behavior_to_mixed
    hNA hβ, isMixedStrategy_ex7E1Sigma, ?_⟩
  rintro ⟨β, -, hRE⟩
  -- player 2 plays `ℓ`
  let F : Fin 2 → Fin 3 → Fin 7 → ℝ := fun _ _ a => if a = 3 then 1 else 0
  have key : ∀ z ∈ exercise7E1Merged.terminals,
      ((1 / 2) * exercise7E1Merged.weight (some 0) (exercise7E1Merged.pureBeh ex7E1MX) z +
        (1 / 2) * exercise7E1Merged.weight (some 0) (exercise7E1Merged.pureBeh ex7E1RY) z) *
          (exercise7E1Merged.weight none exercise7E1Merged.natureProb z *
            ∏ j, if j = 0 then 1 else exercise7E1Merged.weight (some j) (F j) z) =
        exercise7E1Merged.weight (some 0) β z *
          (exercise7E1Merged.weight none exercise7E1Merged.natureProb z *
            ∏ j, if j = 0 then 1 else exercise7E1Merged.weight (some j) (F j) z) := by
    intro z hz
    have h := hRE F z hz
    simp_rw [exercise7E1Merged.reach_update_factor 0 F] at h
    rw [← h]
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul]
    congr 1
    simp only [ex7E1Sigma, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
    simp [pureMixed]
  have h1 := key [5, 3, 1] (by decide)
  have h2 := key [6, 3, 1] (by decide)
  have h6 := key [6, 3, 2] (by decide)
  have h1' : (2 : ℝ)⁻¹ = β 0 1 * β 2 5 := by
    simpa [weight_cons, F, ex7E1MX, ex7E1RY, pureBeh, pureOfFun, exercise7E1Merged_info,
      exercise7E1Merged_player, ex7E1MergedInfo, Fin.prod_univ_two] using h1
  have h2' : β 0 1 = 0 ∨ β 2 6 = 0 := by
    simpa [weight_cons, F, ex7E1MX, ex7E1RY, pureBeh, pureOfFun, exercise7E1Merged_info,
      exercise7E1Merged_player, ex7E1MergedInfo, Fin.prod_univ_two] using h2
  have h6' : (2 : ℝ)⁻¹ = β 0 2 * β 2 6 := by
    simpa [weight_cons, F, ex7E1MX, ex7E1RY, pureBeh, pureOfFun, exercise7E1Merged_info,
      exercise7E1Merged_player, ex7E1MergedInfo, Fin.prod_univ_two] using h6
  rcases h2' with h | h
  · rw [h, zero_mul] at h1'
    norm_num at h1'
  · rw [h, mul_zero] at h6'
    norm_num at h6'

end MWG.NoncooperativeGames

set_option linter.style.longLine false
#print axioms MWG.NoncooperativeGames.ExtensiveForm
#print axioms MWG.NoncooperativeGames.ExtensiveForm.mk
#print axioms MWG.NoncooperativeGames.ExtensiveForm.nodes
#print axioms MWG.NoncooperativeGames.ExtensiveForm.nil_mem
#print axioms MWG.NoncooperativeGames.ExtensiveForm.tail_mem
#print axioms MWG.NoncooperativeGames.ExtensiveForm.info
#print axioms MWG.NoncooperativeGames.ExtensiveForm.avail
#print axioms MWG.NoncooperativeGames.ExtensiveForm.avail_spec
#print axioms MWG.NoncooperativeGames.ExtensiveForm.info_surj
#print axioms MWG.NoncooperativeGames.ExtensiveForm.player
#print axioms MWG.NoncooperativeGames.ExtensiveForm.natureProb
#print axioms MWG.NoncooperativeGames.ExtensiveForm.nature_nonneg
#print axioms MWG.NoncooperativeGames.ExtensiveForm.nature_zero
#print axioms MWG.NoncooperativeGames.ExtensiveForm.nature_sum
#print axioms MWG.NoncooperativeGames.ExtensiveForm.payoff
#print axioms MWG.NoncooperativeGames.ExtensiveForm.IsDecision
#print axioms MWG.NoncooperativeGames.ExtensiveForm.IsTerminal
#print axioms MWG.NoncooperativeGames.ExtensiveForm.IsPred
#print axioms MWG.NoncooperativeGames.ExtensiveForm.mem_of_cons_mem
#print axioms MWG.NoncooperativeGames.ExtensiveForm.mem_of_suffix
#print axioms MWG.NoncooperativeGames.ExtensiveForm.isDecision_of_cons_mem
#print axioms MWG.NoncooperativeGames.ExtensiveForm.isDecision_or_isTerminal
#print axioms MWG.NoncooperativeGames.ExtensiveForm.mem_avail_of_cons_mem
#print axioms MWG.NoncooperativeGames.ExtensiveForm.cons_mem_of_mem_avail
#print axioms MWG.NoncooperativeGames.ExtensiveForm.avail_nonempty
#print axioms MWG.NoncooperativeGames.ExtensiveForm.choices_eq_of_info_eq
#print axioms MWG.NoncooperativeGames.ExtensiveForm.extensive_tree_disjoint
#print axioms MWG.NoncooperativeGames.ExtensiveForm.extensive_initial_node
#print axioms MWG.NoncooperativeGames.ExtensiveForm.extensive_successor_actions_distinct
#print axioms MWG.NoncooperativeGames.ExtensiveForm.suffix_unique
#print axioms MWG.NoncooperativeGames.ExtensiveForm.exists_cons_suffix
#print axioms MWG.NoncooperativeGames.ExtensiveForm.PerfectInformation
#print axioms MWG.NoncooperativeGames.ExtensiveForm.NoAbsentMindedness
#print axioms MWG.NoncooperativeGames.ExtensiveForm.RecallFor
#print axioms MWG.NoncooperativeGames.ExtensiveForm.PerfectRecall
#print axioms MWG.NoncooperativeGames.ExtensiveForm.info_ne_of_cons_suffix
#print axioms MWG.NoncooperativeGames.ExtensiveForm.noAbsentMindedness_of_perfectInformation
#print axioms MWG.NoncooperativeGames.ExtensiveForm.recallFor_of_perfectInformation
#print axioms MWG.NoncooperativeGames.ExtensiveForm.perfectRecall_of_perfectInformation
#print axioms MWG.NoncooperativeGames.ExtensiveForm.decisionNodes
#print axioms MWG.NoncooperativeGames.ExtensiveForm.terminals
#print axioms MWG.NoncooperativeGames.ExtensiveForm.successors
#print axioms MWG.NoncooperativeGames.ExtensiveForm.infoSet
#print axioms MWG.NoncooperativeGames.ExtensiveForm.mem_terminals
#print axioms MWG.NoncooperativeGames.ExtensiveForm.mem_decisionNodes
#print axioms MWG.NoncooperativeGames.ExtensiveForm.mem_successors
#print axioms MWG.NoncooperativeGames.ExtensiveForm.infoSet_partition
#print axioms MWG.NoncooperativeGames.GameTree
#print axioms MWG.NoncooperativeGames.GameTree.mk
#print axioms MWG.NoncooperativeGames.GameTree.root
#print axioms MWG.NoncooperativeGames.GameTree.pred
#print axioms MWG.NoncooperativeGames.GameTree.pred_root
#print axioms MWG.NoncooperativeGames.GameTree.pred_ne_none
#print axioms MWG.NoncooperativeGames.GameTree.acyclic
#print axioms MWG.NoncooperativeGames.GameTree.act
#print axioms MWG.NoncooperativeGames.GameTree.act_inj
#print axioms MWG.NoncooperativeGames.GameTree.up
#print axioms MWG.NoncooperativeGames.GameTree.up_iterate_none
#print axioms MWG.NoncooperativeGames.GameTree.up_iterate_root_succ
#print axioms MWG.NoncooperativeGames.GameTree.exists_iterate_eq_root
#print axioms MWG.NoncooperativeGames.GameTree.iterate_eq_root_unique
#print axioms MWG.NoncooperativeGames.GameTree.histN
#print axioms MWG.NoncooperativeGames.GameTree.depth
#print axioms MWG.NoncooperativeGames.GameTree.depth_spec
#print axioms MWG.NoncooperativeGames.GameTree.hist
#print axioms MWG.NoncooperativeGames.GameTree.depth_root
#print axioms MWG.NoncooperativeGames.GameTree.depth_of_pred
#print axioms MWG.NoncooperativeGames.GameTree.hist_root
#print axioms MWG.NoncooperativeGames.GameTree.hist_of_pred
#print axioms MWG.NoncooperativeGames.GameTree.eq_root_of_depth_zero
#print axioms MWG.NoncooperativeGames.GameTree.hist_eq_nil_iff
#print axioms MWG.NoncooperativeGames.GameTree.hist_injective
#print axioms MWG.NoncooperativeGames.GameTree.historyNodes
#print axioms MWG.NoncooperativeGames.GameTree.nil_mem_historyNodes
#print axioms MWG.NoncooperativeGames.GameTree.historyNodes_tail_mem
#print axioms MWG.NoncooperativeGames.GameTree.cons_mem_historyNodes_iff
#print axioms MWG.NoncooperativeGames.ExtensiveForm.treePred
#print axioms MWG.NoncooperativeGames.ExtensiveForm.up_iterate_treePred
#print axioms MWG.NoncooperativeGames.ExtensiveForm.toGameTree
#print axioms MWG.NoncooperativeGames.ExtensiveForm.gameTree_of_history
#print axioms MWG.NoncooperativeGames.NormalForm
#print axioms MWG.NoncooperativeGames.NormalForm.mk
#print axioms MWG.NoncooperativeGames.NormalForm.payoff
#print axioms MWG.NoncooperativeGames.ExtensiveForm.InfoSetOf
#print axioms MWG.NoncooperativeGames.ExtensiveForm.PureStrategy
#print axioms MWG.NoncooperativeGames.ExtensiveForm.pureOfFun
#print axioms MWG.NoncooperativeGames.ExtensiveForm.pureOfFun_apply
#print axioms MWG.NoncooperativeGames.ExtensiveForm.reach
#print axioms MWG.NoncooperativeGames.ExtensiveForm.reach_nil
#print axioms MWG.NoncooperativeGames.ExtensiveForm.reach_cons
#print axioms MWG.NoncooperativeGames.ExtensiveForm.assemble
#print axioms MWG.NoncooperativeGames.ExtensiveForm.assemble_of_none
#print axioms MWG.NoncooperativeGames.ExtensiveForm.assemble_of_some
#print axioms MWG.NoncooperativeGames.ExtensiveForm.reach_nonneg
#print axioms MWG.NoncooperativeGames.ExtensiveForm.pureBeh
#print axioms MWG.NoncooperativeGames.ExtensiveForm.pureBeh_of_mem
#print axioms MWG.NoncooperativeGames.ExtensiveForm.pureProfile
#print axioms MWG.NoncooperativeGames.ExtensiveForm.sum_pureBeh
#print axioms MWG.NoncooperativeGames.ExtensiveForm.sum_pureProfile
#print axioms MWG.NoncooperativeGames.ExtensiveForm.pureProfile_nonneg
#print axioms MWG.NoncooperativeGames.ExtensiveForm.eq_of_terminal_suffix
#print axioms MWG.NoncooperativeGames.ExtensiveForm.sum_terminals_below_decision
#print axioms MWG.NoncooperativeGames.ExtensiveForm.length_le_sup
#print axioms MWG.NoncooperativeGames.ExtensiveForm.sum_reach_terminals_below
#print axioms MWG.NoncooperativeGames.ExtensiveForm.sum_reach_terminals
#print axioms MWG.NoncooperativeGames.ExtensiveForm.pureProfile_outcome_distribution
#print axioms MWG.NoncooperativeGames.ExtensiveForm.reach_pureProfile_zero_or_one
#print axioms MWG.NoncooperativeGames.ExtensiveForm.pureProfile_outcome_degenerate
#print axioms MWG.NoncooperativeGames.ExtensiveForm.pureProfile_apply
#print axioms MWG.NoncooperativeGames.ExtensiveForm.toNormalForm_payoff_eq_of_reach
#print axioms MWG.NoncooperativeGames.ExtensiveForm.card_pureStrategy
#print axioms MWG.NoncooperativeGames.ExtensiveForm.exercise_7_D_1
#print axioms MWG.NoncooperativeGames.ExtensiveForm.toNormalForm
#print axioms MWG.NoncooperativeGames.ExtensiveForm.toNormalForm_payoff_of_reach
#print axioms MWG.NoncooperativeGames.IsMixedStrategy
#print axioms MWG.NoncooperativeGames.mixedExtension
#print axioms MWG.NoncooperativeGames.mixedExtension_fin
#print axioms MWG.NoncooperativeGames.pureMixed
#print axioms MWG.NoncooperativeGames.isMixedStrategy_pureMixed
#print axioms MWG.NoncooperativeGames.NormalForm.mixedPayoff
#print axioms MWG.NoncooperativeGames.NormalForm.sum_prod_mixed
#print axioms MWG.NoncooperativeGames.NormalForm.mixedPayoff_pure
#print axioms MWG.NoncooperativeGames.NormalForm.mixedExtensionGame
#print axioms MWG.NoncooperativeGames.NormalForm.mixedExtensionGame_pure
#print axioms MWG.NoncooperativeGames.ExtensiveForm.IsBehaviorStrategy
#print axioms MWG.NoncooperativeGames.ExtensiveForm.weight
#print axioms MWG.NoncooperativeGames.ExtensiveForm.weight_nil
#print axioms MWG.NoncooperativeGames.ExtensiveForm.weight_cons
#print axioms MWG.NoncooperativeGames.ExtensiveForm.weight_congr
#print axioms MWG.NoncooperativeGames.ExtensiveForm.reach_assemble_factor
#print axioms MWG.NoncooperativeGames.ExtensiveForm.Consistent
#print axioms MWG.NoncooperativeGames.ExtensiveForm.weight_pureBeh_of_consistent
#print axioms MWG.NoncooperativeGames.ExtensiveForm.weight_pureBeh_of_not_consistent
#print axioms MWG.NoncooperativeGames.ExtensiveForm.isBehaviorStrategy_pureBeh
#print axioms MWG.NoncooperativeGames.ExtensiveForm.mixedWeight
#print axioms MWG.NoncooperativeGames.ExtensiveForm.mixedOutcome
#print axioms MWG.NoncooperativeGames.ExtensiveForm.mixedOutcome_factor
#print axioms MWG.NoncooperativeGames.ExtensiveForm.mixedOutcome_distribution
#print axioms MWG.NoncooperativeGames.ExtensiveForm.mixedPayoff_toNormalForm
#print axioms MWG.NoncooperativeGames.signalCut
#print axioms MWG.NoncooperativeGames.signalCut_zero
#print axioms MWG.NoncooperativeGames.signalCut_mono
#print axioms MWG.NoncooperativeGames.signalCut_full
#print axioms MWG.NoncooperativeGames.signalCut_succ
#print axioms MWG.NoncooperativeGames.mixedStrategy_signal
#print axioms MWG.NoncooperativeGames.mixedStrategy_signal_pure
#print axioms MWG.NoncooperativeGames.ExtensiveForm.rep
#print axioms MWG.NoncooperativeGames.ExtensiveForm.rep_isDecision
#print axioms MWG.NoncooperativeGames.ExtensiveForm.info_rep
#print axioms MWG.NoncooperativeGames.ExtensiveForm.weight_cons_of_ne
#print axioms MWG.NoncooperativeGames.ExtensiveForm.weight_cons_of_eq
#print axioms MWG.NoncooperativeGames.ExtensiveForm.weight_pureBeh_nonneg
#print axioms MWG.NoncooperativeGames.ExtensiveForm.consistent_iff_of_recall
#print axioms MWG.NoncooperativeGames.ExtensiveForm.weight_pureBeh_eq_of_recall
#print axioms MWG.NoncooperativeGames.ExtensiveForm.mixedWeight_nil
#print axioms MWG.NoncooperativeGames.ExtensiveForm.mixedWeight_cons_of_ne
#print axioms MWG.NoncooperativeGames.ExtensiveForm.mixedWeight_cons_of_eq
#print axioms MWG.NoncooperativeGames.ExtensiveForm.mixedWeight_nonneg
#print axioms MWG.NoncooperativeGames.ExtensiveForm.mixedWeight_cons_le
#print axioms MWG.NoncooperativeGames.ExtensiveForm.mixedWeight_cons_eq_zero
#print axioms MWG.NoncooperativeGames.ExtensiveForm.sum_mixedWeight_cons
#print axioms MWG.NoncooperativeGames.ExtensiveForm.mixedWeight_cons_of_not_mem
#print axioms MWG.NoncooperativeGames.ExtensiveForm.mixedWeight_eq_of_recall
#print axioms MWG.NoncooperativeGames.ExtensiveForm.behaviorOfMixed
#print axioms MWG.NoncooperativeGames.ExtensiveForm.isBehaviorStrategy_behaviorOfMixed
#print axioms MWG.NoncooperativeGames.ExtensiveForm.mixedWeight_eq_weight_behaviorOfMixed
#print axioms MWG.NoncooperativeGames.ExtensiveForm.mixedOfBehavior
#print axioms MWG.NoncooperativeGames.ExtensiveForm.isMixedStrategy_mixedOfBehavior
#print axioms MWG.NoncooperativeGames.ExtensiveForm.PathAllows
#print axioms MWG.NoncooperativeGames.ExtensiveForm.pathFactor
#print axioms MWG.NoncooperativeGames.ExtensiveForm.pathFactor_of
#print axioms MWG.NoncooperativeGames.ExtensiveForm.pathFactor_of_not
#print axioms MWG.NoncooperativeGames.ExtensiveForm.consistent_iff_pathAllows
#print axioms MWG.NoncooperativeGames.ExtensiveForm.weight_pureBeh_eq_prod
#print axioms MWG.NoncooperativeGames.ExtensiveForm.pathAllows_nil
#print axioms MWG.NoncooperativeGames.ExtensiveForm.pathAllows_cons
#print axioms MWG.NoncooperativeGames.ExtensiveForm.pathFactor_cons_of_ne
#print axioms MWG.NoncooperativeGames.ExtensiveForm.mixedWeight_mixedOfBehavior
#print axioms MWG.NoncooperativeGames.ExtensiveForm.RealizationEquivalent
#print axioms MWG.NoncooperativeGames.ExtensiveForm.reach_update_factor
#print axioms MWG.NoncooperativeGames.ExtensiveForm.realizationEquivalent_of_weight
#print axioms MWG.NoncooperativeGames.ExtensiveForm.kuhn_behavior_to_mixed
#print axioms MWG.NoncooperativeGames.ExtensiveForm.kuhn_mixed_to_behavior
#print axioms MWG.NoncooperativeGames.ExtensiveForm.kuhn_theorem
#print axioms MWG.NoncooperativeGames.ExtensiveForm.realizationEquivalent_mixed_rivals
#print axioms MWG.NoncooperativeGames.ExtensiveForm.kuhn_mixed_rivals
#print axioms MWG.NoncooperativeGames.mpPay
#print axioms MWG.NoncooperativeGames.matchingPennies
#print axioms MWG.NoncooperativeGames.example_7_B_1_zero_sum
#print axioms MWG.NoncooperativeGames.NormalForm.IsZeroSum
#print axioms MWG.NoncooperativeGames.example_7_B_1_isZeroSum
#print axioms MWG.NoncooperativeGames.example_7_B_1_best_action
#print axioms MWG.NoncooperativeGames.mpTermPay
#print axioms MWG.NoncooperativeGames.mpNodes
#print axioms MWG.NoncooperativeGames.mpBInfo
#print axioms MWG.NoncooperativeGames.matchingPenniesB
#print axioms MWG.NoncooperativeGames.example_7_C_1
#print axioms MWG.NoncooperativeGames.matchingPenniesB_terminals
#print axioms MWG.NoncooperativeGames.example_7_D_1
#print axioms MWG.NoncooperativeGames.mpBResponse
#print axioms MWG.NoncooperativeGames.mpBProfile
#print axioms MWG.NoncooperativeGames.matchingPenniesB_info
#print axioms MWG.NoncooperativeGames.matchingPenniesB_payoff_def
#print axioms MWG.NoncooperativeGames.matchingPenniesB_no_nature
#print axioms MWG.NoncooperativeGames.matchingPenniesB_root_player
#print axioms MWG.NoncooperativeGames.matchingPenniesB_second_player
#print axioms MWG.NoncooperativeGames.matchingPenniesB_payoff
#print axioms MWG.NoncooperativeGames.example_7_D_3
#print axioms MWG.NoncooperativeGames.mpCInfo
#print axioms MWG.NoncooperativeGames.matchingPenniesC
#print axioms MWG.NoncooperativeGames.example_7_C_3
#print axioms MWG.NoncooperativeGames.example_7_D_2
#print axioms MWG.NoncooperativeGames.matchingPenniesC_terminals
#print axioms MWG.NoncooperativeGames.matchingPenniesC_no_nature
#print axioms MWG.NoncooperativeGames.exercise_7_D_2
#print axioms MWG.NoncooperativeGames.matchingPenniesReversed
#print axioms MWG.NoncooperativeGames.matchingPenniesReversed_terminals
#print axioms MWG.NoncooperativeGames.example_7_C_4
#print axioms MWG.NoncooperativeGames.mpDInfo
#print axioms MWG.NoncooperativeGames.mpDNodes
#print axioms MWG.NoncooperativeGames.mpDPay
#print axioms MWG.NoncooperativeGames.matchingPenniesD
#print axioms MWG.NoncooperativeGames.matchingPenniesD_info
#print axioms MWG.NoncooperativeGames.matchingPenniesD_player
#print axioms MWG.NoncooperativeGames.matchingPenniesD_natureProb
#print axioms MWG.NoncooperativeGames.matchingPenniesD_payoff
#print axioms MWG.NoncooperativeGames.example_7_C_5
#print axioms MWG.NoncooperativeGames.example_7_C_5_random_outcome
#print axioms MWG.NoncooperativeGames.fig7D2Nodes
#print axioms MWG.NoncooperativeGames.fig7D2Pay
#print axioms MWG.NoncooperativeGames.figure_7_D_2
#print axioms MWG.NoncooperativeGames.figure_7_D_2_terminals
#print axioms MWG.NoncooperativeGames.fig7D2Profile
#print axioms MWG.NoncooperativeGames.figure_7_D_2_payoff_def
#print axioms MWG.NoncooperativeGames.figure_7_D_2_payoff
#print axioms MWG.NoncooperativeGames.figure_7_D_2_same_normal_form
#print axioms MWG.NoncooperativeGames.meetingNY
#print axioms MWG.NoncooperativeGames.example_7_B_3_aligned
#print axioms MWG.NoncooperativeGames.example_7_B_3_best_reply
#print axioms MWG.NoncooperativeGames.example_7_B_3_not_zeroSum
#print axioms MWG.NoncooperativeGames.example_7_B_3_two_places
#print axioms MWG.NoncooperativeGames.nyTermPay
#print axioms MWG.NoncooperativeGames.exercise7C1
#print axioms MWG.NoncooperativeGames.exercise7C1_terminals
#print axioms MWG.NoncooperativeGames.exercise_7_C_1
#print axioms MWG.NoncooperativeGames.fig7C4aInfo
#print axioms MWG.NoncooperativeGames.figure7C4a
#print axioms MWG.NoncooperativeGames.figure_7_C_4a
#print axioms MWG.NoncooperativeGames.fig7C4bInfo
#print axioms MWG.NoncooperativeGames.figure7C4b
#print axioms MWG.NoncooperativeGames.figure_7_C_4b
#print axioms MWG.NoncooperativeGames.tttLines
#print axioms MWG.NoncooperativeGames.tttMarks
#print axioms MWG.NoncooperativeGames.tttWins
#print axioms MWG.NoncooperativeGames.tttWon
#print axioms MWG.NoncooperativeGames.tttNoEarlyWin
#print axioms MWG.NoncooperativeGames.tttValid
#print axioms MWG.NoncooperativeGames.tttNodes
#print axioms MWG.NoncooperativeGames.mem_tttNodes
#print axioms MWG.NoncooperativeGames.tttNoEarlyWin_cons
#print axioms MWG.NoncooperativeGames.length_lt_of_nodup_cons
#print axioms MWG.NoncooperativeGames.exists_not_mem
#print axioms MWG.NoncooperativeGames.tttDecision
#print axioms MWG.NoncooperativeGames.tttMarks_nil
#print axioms MWG.NoncooperativeGames.tttLines_ne_nil
#print axioms MWG.NoncooperativeGames.not_tttWins_nil
#print axioms MWG.NoncooperativeGames.nil_mem_tttDecision
#print axioms MWG.NoncooperativeGames.tttInfo
#print axioms MWG.NoncooperativeGames.cons_mem_tttNodes_iff
#print axioms MWG.NoncooperativeGames.mem_tttDecision_of_cons
#print axioms MWG.NoncooperativeGames.tttPlayer
#print axioms MWG.NoncooperativeGames.tttPayoff
#print axioms MWG.NoncooperativeGames.tickTackToe
#print axioms MWG.NoncooperativeGames.tickTackToe_info
#print axioms MWG.NoncooperativeGames.tickTackToe_player
#print axioms MWG.NoncooperativeGames.tickTackToe_payoff
#print axioms MWG.NoncooperativeGames.example_7_C_2_perfectInformation
#print axioms MWG.NoncooperativeGames.example_7_B_2_alternate
#print axioms MWG.NoncooperativeGames.tttMarks_cons_other
#print axioms MWG.NoncooperativeGames.ttt_not_both_win
#print axioms MWG.NoncooperativeGames.example_7_B_2_zero_sum
#print axioms MWG.NoncooperativeGames.example_7_C_2_paths
#print axioms MWG.NoncooperativeGames.ex7E1Nodes
#print axioms MWG.NoncooperativeGames.ex7E1Info
#print axioms MWG.NoncooperativeGames.exercise7E1
#print axioms MWG.NoncooperativeGames.exercise_7_E_1a
#print axioms MWG.NoncooperativeGames.exercise7E1_perfectRecall
#print axioms MWG.NoncooperativeGames.exercise_7_E_1b
#print axioms MWG.NoncooperativeGames.exercise_7_E_1c
#print axioms MWG.NoncooperativeGames.ex7E1Pure
#print axioms MWG.NoncooperativeGames.exercise_7_E_1c_mixed_rivals
#print axioms MWG.NoncooperativeGames.ex7E1MergedInfo
#print axioms MWG.NoncooperativeGames.exercise7E1Merged
#print axioms MWG.NoncooperativeGames.exercise7E1Merged_info
#print axioms MWG.NoncooperativeGames.exercise7E1Merged_player
#print axioms MWG.NoncooperativeGames.ex7E1MX
#print axioms MWG.NoncooperativeGames.ex7E1RY
#print axioms MWG.NoncooperativeGames.ex7E1Sigma
#print axioms MWG.NoncooperativeGames.ex7E1MX_ne_RY
#print axioms MWG.NoncooperativeGames.isMixedStrategy_ex7E1Sigma
#print axioms MWG.NoncooperativeGames.exercise_7_E_1d
