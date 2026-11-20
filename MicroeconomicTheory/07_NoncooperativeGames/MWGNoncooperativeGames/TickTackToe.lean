/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGNoncooperativeGames.ExtensiveForm
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.OfFn

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
