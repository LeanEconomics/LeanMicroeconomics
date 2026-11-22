/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Basic.Real.Basic

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
