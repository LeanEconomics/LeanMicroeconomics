/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGNoncooperativeGames.Kuhn
import MWGSimultaneousMoveGames.Dominance

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
