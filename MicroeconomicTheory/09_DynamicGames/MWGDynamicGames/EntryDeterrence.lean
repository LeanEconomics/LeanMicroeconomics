/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGDynamicGames.StrictBI

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
