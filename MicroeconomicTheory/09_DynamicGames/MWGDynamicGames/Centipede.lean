/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGDynamicGames.Entry

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
