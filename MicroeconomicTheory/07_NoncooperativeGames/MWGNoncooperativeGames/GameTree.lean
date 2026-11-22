/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGNoncooperativeGames.ExtensiveForm
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Fintype.Option

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
