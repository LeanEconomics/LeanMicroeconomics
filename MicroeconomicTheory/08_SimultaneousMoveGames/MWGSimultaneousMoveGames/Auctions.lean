/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGSimultaneousMoveGames.ExercisesBD
import Mathlib.Basic.NNReal.Basic

/-!
# Exercises 8.B.3 and 8.D.3: second-price and first-price auctions

MWG, Exercises 8.B.3 and 8.D.3, pp. 262-263.

**Exercise 8.B.3 (Vickrey auction).** `I` bidders bid nonnegative amounts (`ℝ≥0`); bidder `i`
values the object at `v_i ≥ 0`. If `b_i` is at least the highest rival bid `m_i = max_{j ≠ i} b_j`
then `i` is among the highest bidders, wins with probability `1 / (1 + #{j ≠ i : b_j = b_i})` and
pays the second-highest bid, which is `m_i` (with a tie at the top it equals the highest bid).
So `u_i(b) = (v_i - m_i) / (1 + #{j ≠ i : b_j = b_i})` if `m_i ≤ b_i` and `0` otherwise
(`vickrey`). Bidding `v_i` is a weakly dominant strategy and the only one
(`exercise_8_B_3`) as soon as there are two bidders; with a single bidder every bid pays `v_i`
and nothing is weakly dominant (`exercise_8_B_3_one_bidder`, correction 10).

**Exercise 8.D.3 (first-price auction with dollar bids).** Two bidders with integer values
`v_i ∈ ℕ` bid `b_i ∈ ℕ`; the higher bid wins and pays its bid, ties split the object.
* (a) No strategy is strictly dominated (`exercise_8_D_3a`): against a rival bid above both
  bids, both lose.
* (b) Bid `b` of bidder `i` is weakly dominated iff `b ≥ max(v_i, 1)` (dominated by
  `max(v_i - 1, 0)`), or `b = 0` and `v_i ≥ 2` (dominated by `1`) (`exercise_8_D_3b`).
* (c) The pure Nash equilibria are: a tie `b_1 = b_2 = b` with `b ≤ v_i ≤ b + 2` for both
  bidders, or the higher-value bidder winning with a bid one dollar above the loser's, at
  least the loser's value and at most his own value minus one (`exercise_8_D_3c`). An
  equilibrium always exists (`exercise_8_D_3c_exists`) and is not unique in general
  (`exercise_8_D_3c_not_unique`: with `v = (1, 1)` both `(0, 0)` and `(1, 1)` are equilibria).
-/

namespace MWG.SimultaneousMoveGames

open MWG.NoncooperativeGames Function Finset NNReal

/-! ### Exercise 8.B.3: the Vickrey auction -/

/-- **Exercise 8.B.3** (MWG, p. 262). The second-price sealed-bid auction with `I` bidders and
valuations `v_i ≥ 0`: bids are nonnegative; with `m_i = max_{j ≠ i} b_j`, bidder `i` gets
`(v_i - m_i) / (1 + #{j ≠ i : b_j = b_i})` if `m_i ≤ b_i` and `0` otherwise. -/
noncomputable def vickrey {I : Type*} [Fintype I] [DecidableEq I] (v : I → ℝ≥0) :
    NormalForm I (fun _ => ℝ≥0) where
  payoff i b := if (univ.erase i).sup b ≤ b i then
    ((v i : ℝ) - ((univ.erase i).sup b : ℝ≥0)) /
      (1 + ((univ.erase i).filter fun j => b j = b i).card)
    else 0

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Bidder `i`'s payoff from the bid `x` depends on the rivals' bids only. -/
theorem vickrey_update (v : I → ℝ≥0) (i : I) (r : I → ℝ≥0) (x : ℝ≥0) :
    (vickrey v).payoff i (update r i x) = if (univ.erase i).sup r ≤ x then
      ((v i : ℝ) - ((univ.erase i).sup r : ℝ≥0)) /
        (1 + ((univ.erase i).filter fun j => r j = x).card) else 0 := by
  have hsup : (univ.erase i).sup (update r i x) = (univ.erase i).sup r :=
    Finset.sup_congr rfl fun j hj => update_of_ne (ne_of_mem_erase hj) _ _
  have hfil : ((univ.erase i).filter fun j => update r i x j = x) =
      (univ.erase i).filter fun j => r j = x :=
    Finset.filter_congr fun j hj => by rw [update_of_ne (ne_of_mem_erase hj)]
  simp only [vickrey, hsup, update_self, hfil]

/-- Truthful bidding gets `max(v_i - m_i, 0)`. -/
theorem vickrey_truthful (v : I → ℝ≥0) (i : I) (r : I → ℝ≥0) :
    (vickrey v).payoff i (update r i (v i)) = max ((v i : ℝ) - ((univ.erase i).sup r : ℝ≥0)) 0 := by
  rw [vickrey_update]
  set M := (univ.erase i).sup r with hM
  split_ifs with h
  · rcases h.lt_or_eq with hlt | heq
    · have hk : ((univ.erase i).filter fun j => r j = v i).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro j hj hrj
        have := Finset.le_sup (f := r) hj
        rw [hrj, ← hM] at this
        exact absurd hlt (not_lt.2 this)
      rw [hk]
      have : (M : ℝ) < v i := by exact_mod_cast hlt
      simp [max_eq_left (by linarith : (0 : ℝ) ≤ (v i : ℝ) - M)]
    · rw [heq]; simp
  · have : (v i : ℝ) < M := by exact_mod_cast not_le.1 h
    rw [max_eq_right (by linarith)]

/-- Against any rival bids, truthful bidding is at least as good as any bid `x`. -/
theorem vickrey_le_truthful (v : I → ℝ≥0) (i : I) (r : I → ℝ≥0) (x : ℝ≥0) :
    (vickrey v).payoff i (update r i x) ≤ (vickrey v).payoff i (update r i (v i)) := by
  rw [vickrey_truthful, vickrey_update]
  split_ifs
  · set k := (((univ.erase i).filter fun j => r j = x).card : ℝ)
    have hk : (1 : ℝ) ≤ 1 + k := by simp [k]
    rcases le_or_gt 0 ((v i : ℝ) - ((univ.erase i).sup r : ℝ≥0)) with h0 | h0
    · exact (div_le_self h0 hk).trans (le_max_left _ _)
    · exact (div_neg_of_neg_of_pos h0 (by linarith)).le.trans (le_max_right _ _)
  · exact le_max_right _ _

/-- With all rivals bidding `z`, the highest rival bid is `z`. -/
theorem vickrey_sup_const (i j : I) (hj : j ≠ i) (z : ℝ≥0) :
    (univ.erase i).sup (fun _ => z) = z :=
  Finset.sup_const ⟨j, mem_erase.2 ⟨hj, mem_univ _⟩⟩ z

/-- **Exercise 8.B.3** (MWG, p. 262). With at least two bidders, bidding one's valuation `v_i` is
a weakly dominant strategy in the Vickrey auction, and it is bidder `i`'s unique weakly dominant
strategy. -/
theorem exercise_8_B_3 (v : I → ℝ≥0) (i : I) (hI : ∃ j, j ≠ i) :
    WeaklyDominant (vickrey v) i (v i) ∧ ∀ x, WeaklyDominant (vickrey v) i x → x = v i := by
  obtain ⟨j, hj⟩ := hI
  have hdom : WeaklyDominant (vickrey v) i (v i) := by
    intro x hx
    refine ⟨fun r => vickrey_le_truthful v i r x, ?_⟩
    -- all rivals bid strictly between `x` and `v_i`
    set z : ℝ≥0 := ⟨((x : ℝ) + v i) / 2, by positivity⟩ with hz
    have hzr : (z : ℝ) = ((x : ℝ) + v i) / 2 := rfl
    refine ⟨fun _ => z, ?_⟩
    rw [vickrey_truthful, vickrey_update, vickrey_sup_const i j hj]
    rcases lt_or_gt_of_ne hx with hlt | hgt
    · have hlt' : (x : ℝ) < v i := by exact_mod_cast hlt
      have hxz : ¬ z ≤ x := by
        rw [← NNReal.coe_le_coe, hzr]; linarith
      simp only [hxz, ↓reduceIte]
      rw [hzr, max_eq_left (by linarith)]
      linarith
    · have hgt' : (v i : ℝ) < x := by exact_mod_cast hgt
      have hxz : z ≤ x := by
        rw [← NNReal.coe_le_coe, hzr]; linarith
      simp only [hxz, ↓reduceIte]
      rw [hzr, max_eq_right (by linarith)]
      refine div_neg_of_neg_of_pos (by linarith) ?_
      positivity
  exact ⟨hdom, fun x hx =>
    @weaklyDominant_unique I (fun _ => ℝ≥0) _ (vickrey v) i x (v i) hx hdom⟩

/-- **Exercise 8.B.3 with one bidder** (correction 10). With a single bidder every bid pays
`v_1`, so truthful bidding is not weakly dominant (it does not weakly dominate the bid
`v_1 + 1`). -/
theorem exercise_8_B_3_one_bidder (v : Unit → ℝ≥0) :
    ¬ WeaklyDominant (vickrey v) () (v ()) := by
  intro h
  obtain ⟨-, r, hr⟩ := h (v () + 1) (by simp)
  rw [vickrey_update, vickrey_update] at hr
  simp at hr

/-- A concrete instance of Exercise 8.B.3: two bidders who value the object at `1`. -/
theorem exercise_8_B_3_instance : WeaklyDominant (vickrey (fun _ : Fin 2 => (1 : ℝ≥0))) 0 1 :=
  (exercise_8_B_3 _ 0 ⟨1, by decide⟩).1

/-! ### Exercise 8.D.3: the first-price auction with dollar bids -/

/-- Twice the payoff, an integer: bidding `x` against the rival bid `y` with value `v` gives
`2(v - x)` when winning, `v - x` when tying and `0` when losing. -/
def fpInt (v x y : ℕ) : ℤ :=
  if y < x then 2 * ((v : ℤ) - x) else if x = y then (v : ℤ) - x else 0

/-- **Exercise 8.D.3** (MWG, p. 263). The payoff of a bidder with value `v` who bids `x` against
the rival bid `y` in the first-price auction: `v - x` if `x > y`, `(v - x)/2` if `x = y`, `0`
otherwise. -/
noncomputable def fpPay (v x y : ℕ) : ℝ :=
  if y < x then (v : ℝ) - x else if x = y then ((v : ℝ) - x) / 2 else 0

theorem fpPay_eq (v x y : ℕ) : fpPay v x y = (fpInt v x y : ℝ) / 2 := by
  unfold fpPay fpInt
  split_ifs <;> push_cast <;> ring

theorem fpPay_le_iff (v x y v' x' y' : ℕ) :
    fpPay v x y ≤ fpPay v' x' y' ↔ fpInt v x y ≤ fpInt v' x' y' := by
  rw [fpPay_eq, fpPay_eq, div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)]
  exact_mod_cast Iff.rfl

theorem fpPay_lt_iff (v x y v' x' y' : ℕ) :
    fpPay v x y < fpPay v' x' y' ↔ fpInt v x y < fpInt v' x' y' := by
  rw [fpPay_eq, fpPay_eq, div_lt_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)]
  exact_mod_cast Iff.rfl

/-- **Exercise 8.D.3** (MWG, p. 263). The first-price sealed-bid auction with two bidders,
integer valuations `v_i` and bids in whole dollars. -/
noncomputable def firstPrice (v : Fin 2 → ℕ) : NormalForm (Fin 2) (fun _ => ℕ) where
  payoff i b := fpPay (v i) (b i) (b (1 - i))

theorem one_sub_ne (i : Fin 2) : 1 - i ≠ i := by
  fin_cases i <;> decide

theorem firstPrice_update (v : Fin 2 → ℕ) (i : Fin 2) (r : Fin 2 → ℕ) (x : ℕ) :
    (firstPrice v).payoff i (update r i x) = fpPay (v i) x (r (1 - i)) := by
  simp only [firstPrice, update_self, update_of_ne (one_sub_ne i)]

/-- Weak domination in the first-price auction, in terms of the rival's bid. -/
theorem firstPrice_weaklyDominates_iff (v : Fin 2 → ℕ) (i : Fin 2) (x' x : ℕ) :
    WeaklyDominates (firstPrice v) i x' x ↔
      (∀ y, fpInt (v i) x y ≤ fpInt (v i) x' y) ∧ ∃ y, fpInt (v i) x y < fpInt (v i) x' y := by
  constructor
  · rintro ⟨hle, r, hr⟩
    refine ⟨fun y => ?_, r (1 - i), ?_⟩
    · have := hle (fun _ => y)
      rwa [firstPrice_update, firstPrice_update, fpPay_le_iff] at this
    · rwa [firstPrice_update, firstPrice_update, fpPay_lt_iff] at hr
  · rintro ⟨hle, y, hy⟩
    refine ⟨fun r => ?_, fun _ => y, ?_⟩
    · rw [firstPrice_update, firstPrice_update, fpPay_le_iff]; exact hle _
    · rw [firstPrice_update, firstPrice_update, fpPay_lt_iff]; exact hy

/-- **Exercise 8.D.3(a)** (MWG, p. 263). No strategy is strictly dominated: against a rival bid
above both bids, both bids lose. -/
theorem exercise_8_D_3a (v : Fin 2 → ℕ) (i : Fin 2) (x : ℕ) :
    ¬ StrictlyDominated (firstPrice v) i x := by
  rintro ⟨x', hx'⟩
  have := hx' (fun _ => max x x' + 1)
  rw [firstPrice_update, firstPrice_update, fpPay_lt_iff] at this
  unfold fpInt at this
  split_ifs at this <;> omega

/-- **Exercise 8.D.3(b)** (MWG, p. 263). Bidder `i`'s bid `x` is weakly dominated iff
`x ≥ max(v_i, 1)` or (`x = 0` and `v_i ≥ 2`). -/
theorem exercise_8_D_3b (v : Fin 2 → ℕ) (i : Fin 2) (x : ℕ) :
    WeaklyDominated (firstPrice v) i x ↔ (v i ≤ x ∧ 1 ≤ x) ∨ (x = 0 ∧ 2 ≤ v i) := by
  set w := v i with hw
  constructor
  · rintro ⟨x', hdom⟩
    rw [firstPrice_weaklyDominates_iff] at hdom
    obtain ⟨hle, y, hy⟩ := hdom
    by_contra hcond
    have hxx' : x' ≠ x := by rintro rfl; exact lt_irrefl _ hy
    rw [← hw] at hle hy
    -- a rival bid against which `x` does strictly better than `x'`
    rcases Nat.eq_zero_or_pos x with hx0 | hxpos
    · subst hx0
      have h1 := hle 0
      unfold fpInt at h1
      split_ifs at h1 <;> omega
    · rcases lt_or_gt_of_ne hxx' with hlt | hgt
      · have h1 := hle x
        unfold fpInt at h1
        split_ifs at h1 <;> omega
      · have h1 := hle (x - 1)
        unfold fpInt at h1
        split_ifs at h1 <;> omega
  · rintro (⟨hvx, hx1⟩ | ⟨rfl, hv2⟩)
    · refine ⟨w - 1, (firstPrice_weaklyDominates_iff v i _ _).2 ⟨fun y => ?_, ?_⟩⟩
      · rw [← hw]; unfold fpInt; split_ifs <;> omega
      · rcases Nat.eq_zero_or_pos w with hw0 | hwpos
        · refine ⟨0, ?_⟩
          rw [← hw]; unfold fpInt; split_ifs <;> omega
        · refine ⟨w - 1, ?_⟩
          rw [← hw]; unfold fpInt; split_ifs <;> omega
    · refine ⟨1, (firstPrice_weaklyDominates_iff v i _ _).2 ⟨fun y => ?_, 1, ?_⟩⟩
      · rw [← hw]; unfold fpInt; split_ifs <;> omega
      · rw [← hw]; unfold fpInt; simp; omega

/-- The best payoff against the rival bid `y`: `(∀ x, 2u(x, y) ≤ W)` iff `W` is at least the
payoff of losing (when possible), of tying and of winning by one dollar. -/
theorem fpInt_bound_iff (w y : ℕ) (W : ℤ) :
    (∀ x, fpInt w x y ≤ W) ↔
      ((1 ≤ y → 0 ≤ W) ∧ (w : ℤ) - y ≤ W ∧ 2 * ((w : ℤ) - (y + 1)) ≤ W) := by
  constructor
  · intro h
    refine ⟨fun hy => ?_, ?_, ?_⟩
    · have := h 0
      unfold fpInt at this
      split_ifs at this <;> omega
    · have := h y
      unfold fpInt at this
      split_ifs at this <;> omega
    · have := h (y + 1)
      unfold fpInt at this
      split_ifs at this <;> push_cast at this <;> omega
  · rintro ⟨h0, h1, h2⟩ x
    unfold fpInt
    split_ifs <;> omega

/-- Nash equilibrium in the first-price auction: each bid is a best reply to the other. -/
theorem firstPrice_isNash_iff (v : Fin 2 → ℕ) (b : Fin 2 → ℕ) :
    IsNashEquilibrium (firstPrice v) b ↔
      (∀ x, fpInt (v 0) x (b 1) ≤ fpInt (v 0) (b 0) (b 1)) ∧
        ∀ x, fpInt (v 1) x (b 0) ≤ fpInt (v 1) (b 1) (b 0) := by
  have h0 : ∀ x, (firstPrice v).payoff 0 (update b 0 x) = fpPay (v 0) x (b 1) :=
    fun x => firstPrice_update v 0 b x
  have h1 : ∀ x, (firstPrice v).payoff 1 (update b 1 x) = fpPay (v 1) x (b 0) :=
    fun x => firstPrice_update v 1 b x
  have e0 : (firstPrice v).payoff 0 b = fpPay (v 0) (b 0) (b 1) := by
    rw [← h0, update_eq_self]
  have e1 : (firstPrice v).payoff 1 b = fpPay (v 1) (b 1) (b 0) := by
    rw [← h1, update_eq_self]
  constructor
  · intro h
    refine ⟨fun x => ?_, fun x => ?_⟩
    · have := h 0 x; rwa [h0, e0, fpPay_le_iff] at this
    · have := h 1 x; rwa [h1, e1, fpPay_le_iff] at this
  · rintro ⟨ha, hb⟩ i x
    fin_cases i
    · change (firstPrice v).payoff 0 (update b 0 x) ≤ (firstPrice v).payoff 0 b
      rw [h0, e0, fpPay_le_iff]; exact ha x
    · change (firstPrice v).payoff 1 (update b 1 x) ≤ (firstPrice v).payoff 1 b
      rw [h1, e1, fpPay_le_iff]; exact hb x

/-- **Exercise 8.D.3(c)** (MWG, p. 263). The pure strategy Nash equilibria of the first-price
auction with dollar bids: either both bid the same `b` with `b ≤ v_i ≤ b + 2` for both bidders, or
one bidder wins with a bid one dollar above the other's, at least the loser's value and at most
the winner's value minus one. -/
theorem exercise_8_D_3c (v : Fin 2 → ℕ) (b : Fin 2 → ℕ) :
    IsNashEquilibrium (firstPrice v) b ↔
      (b 0 = b 1 ∧ b 0 ≤ v 0 ∧ b 0 ≤ v 1 ∧ v 0 ≤ b 0 + 2 ∧ v 1 ≤ b 0 + 2) ∨
        (b 0 = b 1 + 1 ∧ v 1 ≤ b 0 ∧ b 0 + 1 ≤ v 0) ∨
          (b 1 = b 0 + 1 ∧ v 0 ≤ b 1 ∧ b 1 + 1 ≤ v 1) := by
  rw [firstPrice_isNash_iff, fpInt_bound_iff, fpInt_bound_iff]
  unfold fpInt
  split_ifs <;> omega

/-- **Exercise 8.D.3(c)** (MWG, p. 263). A pure strategy Nash equilibrium always exists: a tie at
the lower value when the values differ by at most two, and otherwise the higher-value bidder bids
one dollar above the other's value, which the other bids. -/
theorem exercise_8_D_3c_exists (v : Fin 2 → ℕ) : ∃ b, IsNashEquilibrium (firstPrice v) b := by
  by_cases h : v 0 ≤ v 1 + 2 ∧ v 1 ≤ v 0 + 2
  · rcases le_total (v 0) (v 1) with h01 | h10
    · exact ⟨fun _ => v 0, (exercise_8_D_3c v _).2 (Or.inl (by omega))⟩
    · exact ⟨fun _ => v 1, (exercise_8_D_3c v _).2 (Or.inl (by omega))⟩
  · rcases not_and_or.1 h with h1 | h1
    · refine ⟨fun k => if k = 0 then v 1 + 1 else v 1,
        (exercise_8_D_3c v _).2 (Or.inr (Or.inl ?_))⟩
      have h10 : (1 : Fin 2) ≠ 0 := by decide
      simp only [h10, ↓reduceIte, true_and]
      omega
    · refine ⟨fun k => if k = 0 then v 0 else v 0 + 1,
        (exercise_8_D_3c v _).2 (Or.inr (Or.inr ?_))⟩
      have h10 : (1 : Fin 2) ≠ 0 := by decide
      simp only [h10, ↓reduceIte, true_and]
      omega

/-- **Exercise 8.D.3(c)** (MWG, p. 263). The equilibrium need not be unique: with `v = (1, 1)`
both `(0, 0)` and `(1, 1)` are Nash equilibria. -/
theorem exercise_8_D_3c_not_unique :
    IsNashEquilibrium (firstPrice ![1, 1]) ![0, 0] ∧
      IsNashEquilibrium (firstPrice ![1, 1]) ![1, 1] := by
  refine ⟨(exercise_8_D_3c _ _).2 (Or.inl ?_), (exercise_8_D_3c _ _).2 (Or.inl ?_)⟩ <;>
    simp

end MWG.SimultaneousMoveGames
