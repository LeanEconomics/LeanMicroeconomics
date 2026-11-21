/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGSimultaneousMoveGames.Bayesian
import Mathlib.Basic.NNReal.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Exercise 8.B.5: iterated dominance in the Cournot model

MWG, Exercise 8.B.5, p. 262.

Firms `i ∈ I` choose quantities `q_i ≥ 0`; the price is `P = a - b ∑_j q_j` and unit cost is `c`,
so with `A = a - c` and rivals' total `X`, firm `i` earns `q_i (A - bX - b q_i)` (`cournot`).
Its best response to `X` is `r(X) = (A - bX)/(2b)` when `A ≥ bX`.

The deletion process needs infinitely many rounds, so it is formalized as the *maximal*
process: at each round every strategy that is strictly dominated (by a remaining strategy,
against the remaining rival strategies) is removed (`sdRound`, which is a deletion step of
Section 8.B, `sdStep_sdRound`); `sdIter N n` is what survives `n` rounds and the prediction is
the limit `⋂ₙ sdIter N n i`.

* `cournot_round`: if each firm's remaining set is `[L, U]` and the rivals' total ranges over
  `[kL, kU]` (`k` rivals), one round leaves `[r(kU), r(kL)]` (under the invariant that keeps the
  intervals nested); the first round leaves `[0, A/(2b)]` (`cournot_round_zero`).
* **Exercise 8.B.5(a)** (`exercise_8_B_5a`): with two firms the surviving sets are the intervals
  `[L_n, U_n]` of `cournotBounds`, whose width halves each round; every finite round leaves a
  continuum of strategies, and the limit is the single quantity `q* = (a - c)/(3b)`.
* **Exercise 8.B.5(b)** (`exercise_8_B_5b`): with three firms the process stops after one round
  at `[0, (a - c)/(2b)]` for every firm (nothing there is dominated: two rivals can total any
  amount in `[0, (a - c)/b]`), so there is no unique prediction.
-/

namespace MWG.SimultaneousMoveGames

open MWG.NoncooperativeGames Function Finset NNReal Filter Topology

/-! ### The maximal deletion process -/

variable {I : Type*} {S : I → Type*} [DecidableEq I]

/-- **Section 8.B** (MWG, pp. 238-240). One round of the maximal deletion process: remove every
remaining strategy that is strictly dominated in the remaining game. -/
def sdRound (N : NormalForm I S) (T : (i : I) → Set (S i)) : (i : I) → Set (S i) :=
  fun i => {s | s ∈ T i ∧ ¬ SDominatedIn N T i s}

/-- The strategies surviving `n` rounds of the maximal deletion process. -/
def sdIter (N : NormalForm I S) : ℕ → (i : I) → Set (S i)
  | 0 => fullSets S
  | n + 1 => sdRound N (sdIter N n)

/-- A round of the maximal process is a deletion step (Section 8.B). -/
theorem sdStep_sdRound (N : NormalForm I S) (T : (i : I) → Set (S i)) :
    SDStep N T (sdRound N T) :=
  ⟨fun _ _ hs => hs.1, fun i s hs hs' => by
    by_contra hnd
    exact hs' ⟨hs, hnd⟩⟩

/-- Every stage of the maximal process is reached by a deletion process from the full game. -/
theorem sdIter_chain (N : NormalForm I S) :
    ∀ n, Relation.ReflTransGen (SDStep N) (fullSets S) (sdIter N n)
  | 0 => Relation.ReflTransGen.refl
  | n + 1 => (sdIter_chain N n).tail (sdStep_sdRound N _)

/-! ### The Cournot game -/

/-- **Exercise 8.B.5** (MWG, p. 262). The Cournot game with firms `I`, inverse demand
`P = a - b ∑_j q_j` and unit cost `c`: `u_i(q) = (a - b ∑_j q_j) q_i - c q_i`. -/
def cournot (I : Type*) [Fintype I] (a b c : ℝ) : NormalForm I (fun _ => ℝ≥0) where
  payoff i q := (a - b * ∑ j, (q j : ℝ)) * q i - c * q i

/-- The rivals' total output `X = ∑_{j ≠ i} q_j`. -/
def rivalsTotal [Fintype I] (r : I → ℝ≥0) (i : I) : ℝ := ∑ j ∈ univ.erase i, (r j : ℝ)

/-- The interval `{q ≥ 0 : L ≤ q ≤ U}` of quantities. -/
def qIval (L U : ℝ) : Set ℝ≥0 := {q | L ≤ (q : ℝ) ∧ (q : ℝ) ≤ U}

/-- The best response `r(X) = (A - bX)/(2b)`. -/
noncomputable def cbr (A b X : ℝ) : ℝ := (A - b * X) / (2 * b)

variable [Fintype I]

/-- Firm `i`'s profit from `s` against the rivals' outputs: `s (A - bX - bs)`, `A = a - c`. -/
theorem cournot_update (a b c : ℝ) (i : I) (r : I → ℝ≥0) (s : ℝ≥0) :
    (cournot I a b c).payoff i (update r i s) =
      (s : ℝ) * ((a - c) - b * rivalsTotal r i - b * s) := by
  have hsum : ∑ j, ((update r i s j : ℝ≥0) : ℝ) = s + rivalsTotal r i := by
    rw [← Finset.add_sum_erase _ _ (mem_univ i), update_self]
    congr 1
    exact Finset.sum_congr rfl fun j hj => by rw [update_of_ne (ne_of_mem_erase hj)]
  simp only [cournot, hsum, update_self]
  ring

/-- With every rival producing `x`, the rivals' total is `k x`, `k = |I| - 1`. -/
theorem rivalsTotal_const (i : I) (x : ℝ≥0) :
    rivalsTotal (fun _ => x) i = ((Fintype.card I - 1 : ℕ) : ℝ) * x := by
  simp [rivalsTotal, Finset.card_erase_of_mem]

/-- If every rival's output lies in `[L, U]`, the rivals' total lies in `[kL, kU]`. -/
theorem rivalsTotal_mem {L U : ℝ} (i : I) {r : I → ℝ≥0}
    (hr : ∀ j, j ≠ i → r j ∈ qIval L U) :
    ((Fintype.card I - 1 : ℕ) : ℝ) * L ≤ rivalsTotal r i ∧
      rivalsTotal r i ≤ ((Fintype.card I - 1 : ℕ) : ℝ) * U := by
  have hcard : (univ.erase i).card = Fintype.card I - 1 := by
    rw [Finset.card_erase_of_mem (mem_univ i), Finset.card_univ]
  constructor
  · have := Finset.card_nsmul_le_sum (univ.erase i) (fun j => (r j : ℝ)) L
      fun j hj => (hr j (ne_of_mem_erase hj)).1
    rwa [hcard, nsmul_eq_mul] at this
  · have := Finset.sum_le_card_nsmul (univ.erase i) (fun j => (r j : ℝ)) U
      fun j hj => (hr j (ne_of_mem_erase hj)).2
    rwa [hcard, nsmul_eq_mul] at this

/-- The profit gap between `s'` and `s` against the rivals' total `X`. -/
theorem cournot_gap (A b X s s' : ℝ) :
    s' * (A - b * X - b * s') - s * (A - b * X - b * s) =
      (s' - s) * (A - b * X - b * (s + s')) := by
  ring

/-- A best response is never strictly dominated: if some admissible rivals' profile has
`bX = A - 2bs`, then `s` is not strictly dominated. -/
theorem cournot_not_dominated {a b c : ℝ} (hb : 0 < b) {T : I → Set ℝ≥0} {i : I} {s : ℝ≥0}
    {r : I → ℝ≥0} (hr : ∀ j, j ≠ i → r j ∈ T j)
    (hX : b * rivalsTotal r i = (a - c) - 2 * b * s) :
    ¬ SDominatedIn (cournot I a b c) T i s := by
  rintro ⟨s', -, hdom⟩
  have h := hdom r hr
  rw [cournot_update a b c i r s, cournot_update a b c i r, hX] at h
  nlinarith [sq_nonneg ((s : ℝ) - s')]

/-- **Exercise 8.B.5**, one round of deletion. Each firm's remaining quantities are `[L, U]` and
there are `k = |I| - 1 ≥ 1` rivals. Under the invariant `0 ≤ L ≤ U`, `L ≤ r(kU)`, `r(kL) ≤ U`,
`bkU ≤ A`, one round leaves `[r(kU), r(kL)]`. -/
theorem cournot_round {a b c : ℝ} (hb : 0 < b) (i : I) (hk : 1 ≤ Fintype.card I - 1)
    {L U : ℝ} (hL : 0 ≤ L) (hLU : L ≤ U)
    (h1 : L ≤ cbr (a - c) b ((Fintype.card I - 1 : ℕ) * U))
    (h2 : cbr (a - c) b ((Fintype.card I - 1 : ℕ) * L) ≤ U)
    (h3 : b * ((Fintype.card I - 1 : ℕ) * U) ≤ a - c) :
    sdRound (cournot I a b c) (fun _ => qIval L U) i =
      qIval (cbr (a - c) b ((Fintype.card I - 1 : ℕ) * U))
        (cbr (a - c) b ((Fintype.card I - 1 : ℕ) * L)) := by
  set k : ℝ := ((Fintype.card I - 1 : ℕ) : ℝ) with hkdef
  have hk1 : (1 : ℝ) ≤ k := by rw [hkdef]; exact_mod_cast hk
  set rU := cbr (a - c) b (k * U) with hrU
  set rL := cbr (a - c) b (k * L) with hrL
  have hrUrL : rU ≤ rL := by
    simp only [hrU, hrL, cbr]
    gcongr
  have hrU0 : 0 ≤ rU := by
    simp only [hrU, cbr]; exact div_nonneg (by linarith) (by linarith)
  have h2b : rU * (2 * b) = (a - c) - b * (k * U) := by
    simp only [hrU, cbr]; field_simp
  have h2b' : rL * (2 * b) = (a - c) - b * (k * L) := by
    simp only [hrL, cbr]; field_simp
  ext s
  constructor
  · rintro ⟨hsT, hnd⟩
    constructor
    · by_contra hlt
      push Not at hlt
      apply hnd
      set s' : ℝ≥0 := ⟨rU, hrU0⟩ with hs'
      have hs'v : (s' : ℝ) = rU := rfl
      refine ⟨s', ⟨h1, hrUrL.trans h2⟩, fun r hr => ?_⟩
      have hX := (rivalsTotal_mem i hr).2
      rw [← hkdef] at hX
      rw [cournot_update a b c i r s, cournot_update a b c i r s', hs'v]
      have hgap := cournot_gap (a - c) b (rivalsTotal r i) s rU
      have hpos : 0 < (rU - s) * ((a - c) - b * rivalsTotal r i - b * (s + rU)) := by
        apply mul_pos (by linarith)
        nlinarith
      linarith
    · by_contra hlt
      push Not at hlt
      apply hnd
      set s' : ℝ≥0 := ⟨rL, hrU0.trans hrUrL⟩ with hs'
      have hs'v : (s' : ℝ) = rL := rfl
      refine ⟨s', ⟨h1.trans hrUrL, h2⟩, fun r hr => ?_⟩
      have hX := (rivalsTotal_mem i hr).1
      rw [← hkdef] at hX
      rw [cournot_update a b c i r s, cournot_update a b c i r s', hs'v]
      have hgap := cournot_gap (a - c) b (rivalsTotal r i) s rL
      have hneg : (rL - s) * ((a - c) - b * rivalsTotal r i - b * (s + rL)) > 0 := by
        apply mul_pos_of_neg_of_neg (by linarith)
        nlinarith
      linarith
  · rintro ⟨hlo, hhi⟩
    refine ⟨⟨h1.trans hlo, hhi.trans h2⟩, ?_⟩
    -- the rivals' total `X* = (A - 2bs)/b`, split equally
    set Xs : ℝ := ((a - c) - 2 * b * s) / b with hXs
    have hXs0 : 0 ≤ Xs / k := by
      apply div_nonneg _ (by linarith)
      rw [hXs]; apply div_nonneg _ hb.le
      nlinarith [mul_le_mul_of_nonneg_left hhi (by linarith : (0 : ℝ) ≤ 2 * b),
        mul_nonneg hb.le (mul_nonneg (by linarith : (0 : ℝ) ≤ k) hL)]
    set x : ℝ≥0 := ⟨Xs / k, hXs0⟩ with hx
    have hxv : (x : ℝ) = Xs / k := rfl
    refine cournot_not_dominated hb (r := fun _ => x) (fun j _ => ⟨?_, ?_⟩) ?_
    · show L ≤ (x : ℝ)
      rw [hxv, le_div_iff₀ (by linarith), hXs, le_div_iff₀ hb]
      nlinarith [mul_le_mul_of_nonneg_left hhi (by linarith : (0 : ℝ) ≤ 2 * b)]
    · show (x : ℝ) ≤ U
      rw [hxv, div_le_iff₀ (by linarith), hXs, div_le_iff₀ hb]
      nlinarith [mul_le_mul_of_nonneg_left hlo (by linarith : (0 : ℝ) ≤ 2 * b)]
    · rw [rivalsTotal_const, ← hkdef, hxv, mul_div_cancel₀ _ (by linarith), hXs,
        mul_div_cancel₀ _ hb.ne']

/-- **Exercise 8.B.5**, the first round: from the full game, one round leaves `[0, A/(2b)]`
(quantities above the monopoly output are dominated by it). -/
theorem cournot_round_zero {a b c : ℝ} (hb : 0 < b) (hA : 0 < a - c) (i : I)
    (hk : 1 ≤ Fintype.card I - 1) :
    sdRound (cournot I a b c) (fullSets _) i = qIval 0 ((a - c) / (2 * b)) := by
  set k : ℝ := ((Fintype.card I - 1 : ℕ) : ℝ) with hkdef
  have hk1 : (1 : ℝ) ≤ k := by rw [hkdef]; exact_mod_cast hk
  set m := (a - c) / (2 * b) with hm
  have hm0 : 0 ≤ m := by rw [hm]; positivity
  have h2m : m * (2 * b) = a - c := by rw [hm]; field_simp
  ext s
  constructor
  · rintro ⟨-, hnd⟩
    refine ⟨s.2, ?_⟩
    by_contra hlt
    push Not at hlt
    apply hnd
    set s' : ℝ≥0 := ⟨m, hm0⟩ with hs'
    have hs'v : (s' : ℝ) = m := rfl
    refine ⟨s', Set.mem_univ _, fun r _ => ?_⟩
    have hX : 0 ≤ rivalsTotal r i := Finset.sum_nonneg fun j _ => (r j).2
    rw [cournot_update a b c i r s, cournot_update a b c i r s', hs'v]
    have hgap := cournot_gap (a - c) b (rivalsTotal r i) s m
    have hneg : (m - s) * ((a - c) - b * rivalsTotal r i - b * (s + m)) > 0 := by
      apply mul_pos_of_neg_of_neg (by linarith)
      nlinarith
    linarith
  · rintro ⟨-, hhi⟩
    refine ⟨Set.mem_univ _, ?_⟩
    set Xs : ℝ := ((a - c) - 2 * b * s) / b with hXs
    have hXs0 : 0 ≤ Xs / k := by
      apply div_nonneg _ (by linarith)
      rw [hXs]; apply div_nonneg _ hb.le
      nlinarith [mul_le_mul_of_nonneg_left hhi (by linarith : (0 : ℝ) ≤ 2 * b)]
    set x : ℝ≥0 := ⟨Xs / k, hXs0⟩ with hx
    have hxv : (x : ℝ) = Xs / k := rfl
    refine cournot_not_dominated hb (r := fun _ => x) (fun j _ => Set.mem_univ _) ?_
    rw [rivalsTotal_const, ← hkdef, hxv, mul_div_cancel₀ _ (by linarith), hXs,
      mul_div_cancel₀ _ hb.ne']

/-! ### Exercise 8.B.5(a): two firms -/

/-- The bounds `(L_n, U_n)` of the quantities surviving `n + 1` rounds with two firms:
`(L_0, U_0) = (0, A/(2b))` and `(L_{n+1}, U_{n+1}) = (r(U_n), r(L_n))`. -/
noncomputable def cournotBounds (A b : ℝ) : ℕ → ℝ × ℝ
  | 0 => (0, A / (2 * b))
  | n + 1 => (cbr A b (cournotBounds A b n).2, cbr A b (cournotBounds A b n).1)

/-- The invariant of the two-firm process, and the halving of the width. -/
theorem cournotBounds_inv {A b : ℝ} (hb : 0 < b) (hA : 0 < A) (n : ℕ) :
    0 ≤ (cournotBounds A b n).1 ∧ (cournotBounds A b n).1 ≤ (cournotBounds A b n).2 ∧
      (cournotBounds A b n).1 ≤ cbr A b (cournotBounds A b n).2 ∧
      cbr A b (cournotBounds A b n).1 ≤ (cournotBounds A b n).2 ∧
      b * (cournotBounds A b n).2 ≤ A ∧
      (cournotBounds A b n).1 ≤ A / (3 * b) ∧ A / (3 * b) ≤ (cournotBounds A b n).2 ∧
      (cournotBounds A b n).2 - (cournotBounds A b n).1 = A / (2 * b) / 2 ^ n := by
  induction n with
  | zero =>
    simp only [cournotBounds, cbr, pow_zero, div_one, sub_zero]
    refine ⟨le_rfl, by positivity, ?_, ?_, ?_, by positivity, ?_, trivial⟩
    · apply div_nonneg _ (by linarith)
      rw [mul_div_assoc', mul_comm b A, mul_div_mul_right _ _ hb.ne']
      linarith
    · simp
    · rw [mul_div_assoc', mul_comm b A, mul_div_mul_right _ _ hb.ne']
      linarith
    · gcongr; norm_num
  | succ n ih =>
    obtain ⟨hL, hLU, h1, h2, h3, hq1, hq2, hw⟩ := ih
    set L := (cournotBounds A b n).1
    set U := (cournotBounds A b n).2
    have e1 : (cournotBounds A b (n + 1)).1 = cbr A b U := rfl
    have e2 : (cournotBounds A b (n + 1)).2 = cbr A b L := rfl
    rw [e1, e2]
    have hcbr : ∀ x, cbr A b x * (2 * b) = A - b * x := fun x => by
      simp only [cbr]; field_simp
    have hmono : ∀ x y, x ≤ y → cbr A b y ≤ cbr A b x := fun x y hxy => by
      simp only [cbr]; gcongr
    have hq : cbr A b (A / (3 * b)) = A / (3 * b) := by
      simp only [cbr]; field_simp; ring
    refine ⟨?_, hmono _ _ hLU, hmono _ _ h2, hmono _ _ h1, ?_, ?_, ?_, ?_⟩
    · have := hcbr U
      nlinarith
    · have := hcbr L
      nlinarith
    · rw [← hq]; exact hmono _ _ hq2
    · rw [← hq]; exact hmono _ _ hq1
    · rw [pow_succ, show A / (2 * b) / (2 ^ n * 2) = (U - L) / 2 by rw [hw]; ring]
      simp only [cbr]
      field_simp
      ring

/-- With two firms, `n + 1` rounds leave `[L_n, U_n]` for each firm. -/
theorem cournot_two_sdIter {a b c : ℝ} (hb : 0 < b) (hA : 0 < a - c) (n : ℕ) :
    sdIter (cournot (Fin 2) a b c) (n + 1) =
      fun _ => qIval (cournotBounds (a - c) b n).1 (cournotBounds (a - c) b n).2 := by
  have hk : 1 ≤ Fintype.card (Fin 2) - 1 := by simp
  have hk' : ((Fintype.card (Fin 2) - 1 : ℕ) : ℝ) = 1 := by simp
  induction n with
  | zero =>
    funext i
    exact cournot_round_zero hb hA i hk
  | succ n ih =>
    obtain ⟨hL, hLU, h1, h2, h3, -, -, -⟩ := cournotBounds_inv hb hA n
    funext i
    change sdRound _ (sdIter _ (n + 1)) i = _
    rw [ih]
    have := cournot_round (a := a) (c := c) hb i hk hL hLU (by rwa [hk', one_mul])
      (by rwa [hk', one_mul]) (by rwa [hk', one_mul])
    rw [this, hk', one_mul, one_mul]
    rfl

/-- The Cournot quantity `q* = (a - c)/(3b)`. -/
noncomputable def cournotStar (a b c : ℝ) (hb : 0 < b) (hA : 0 < a - c) : ℝ≥0 :=
  ⟨(a - c) / (3 * b), by positivity⟩

/-- **Exercise 8.B.5(a)** (MWG, p. 262). With two firms (`a > c`, `b > 0`), iterated deletion of
strictly dominated strategies yields a unique prediction, but only in the limit: every finite
round of the maximal process leaves at least two quantities for each firm, and the strategies
surviving all rounds are exactly `q* = (a - c)/(3b)`. -/
theorem exercise_8_B_5a {a b c : ℝ} (hb : 0 < b) (hA : 0 < a - c) :
    (∀ i, ⋂ n, sdIter (cournot (Fin 2) a b c) n i = {cournotStar a b c hb hA}) ∧
      ∀ n i, (sdIter (cournot (Fin 2) a b c) n i).Nontrivial := by
  have hw0 : 0 < (a - c) / (2 * b) := by positivity
  constructor
  · intro i
    ext s
    simp only [Set.mem_iInter, Set.mem_singleton_iff]
    constructor
    · intro hs
      by_contra hne
      have hd : 0 < |(s : ℝ) - (a - c) / (3 * b)| := by
        rw [abs_pos, sub_ne_zero]
        intro h
        exact hne (NNReal.eq h)
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hd hw0) (by norm_num : (1 / 2 : ℝ) < 1)
      have hsn := hs (n + 1)
      rw [cournot_two_sdIter hb hA] at hsn
      obtain ⟨-, -, -, -, -, hq1, hq2, hw⟩ := cournotBounds_inv hb hA n
      have hlt : (a - c) / (2 * b) / 2 ^ n < |(s : ℝ) - (a - c) / (3 * b)| := by
        have h := (lt_div_iff₀ hw0).1 hn
        rw [one_div_pow] at h
        calc (a - c) / (2 * b) / 2 ^ n = 1 / 2 ^ n * ((a - c) / (2 * b)) := by ring
          _ < _ := h
      rw [← hw] at hlt
      have := hsn.1
      have := hsn.2
      rcases lt_or_ge ((s : ℝ) - (a - c) / (3 * b)) 0 with hneg | hnn
      · rw [abs_of_neg hneg] at hlt; linarith
      · rw [abs_of_nonneg hnn] at hlt; linarith
    · rintro rfl n
      rcases n with _ | n
      · exact Set.mem_univ _
      · rw [cournot_two_sdIter hb hA]
        obtain ⟨-, -, -, -, -, hq1, hq2, -⟩ := cournotBounds_inv hb hA n
        exact ⟨hq1, hq2⟩
  · intro n i
    rcases n with _ | n
    · exact ⟨0, Set.mem_univ _, 1, Set.mem_univ _, zero_ne_one⟩
    · rw [cournot_two_sdIter hb hA]
      obtain ⟨hL, hLU, -, -, -, -, -, hw⟩ := cournotBounds_inv hb hA n
      have hpos : 0 < (cournotBounds (a - c) b n).2 - (cournotBounds (a - c) b n).1 := by
        rw [hw]; positivity
      refine ⟨⟨_, hL⟩, ⟨le_rfl, hLU⟩, ⟨_, hL.trans hLU⟩, ⟨hLU, le_rfl⟩, fun h => ?_⟩
      have := congrArg NNReal.toReal h
      change (cournotBounds (a - c) b n).1 = (cournotBounds (a - c) b n).2 at this
      linarith

/-! ### Exercise 8.B.5(b): three firms -/

/-- **Exercise 8.B.5(b)** (MWG, p. 262). With three firms the answer is no: after the first round
every firm keeps `[0, (a - c)/(2b)]`, nothing there is strictly dominated (two rivals can total
any amount in `[0, (a - c)/b]`), so the process stops at a continuum of quantities. -/
theorem exercise_8_B_5b {a b c : ℝ} (hb : 0 < b) (hA : 0 < a - c) :
    (∀ n i, sdIter (cournot (Fin 3) a b c) (n + 1) i = qIval 0 ((a - c) / (2 * b))) ∧
      SDTerminal (cournot (Fin 3) a b c) (fun _ => qIval 0 ((a - c) / (2 * b))) ∧
      ∀ i, (⋂ n, sdIter (cournot (Fin 3) a b c) n i).Nontrivial := by
  have hk : 1 ≤ Fintype.card (Fin 3) - 1 := by simp
  have hk' : ((Fintype.card (Fin 3) - 1 : ℕ) : ℝ) = 2 := by norm_num [Fintype.card_fin]
  set m := (a - c) / (2 * b) with hm
  have hm0 : 0 ≤ m := by rw [hm]; positivity
  have hcbr0 : cbr (a - c) b (2 * m) = 0 := by
    simp only [cbr, hm]; field_simp; ring
  have hcbrm : cbr (a - c) b (2 * 0) = m := by simp [cbr, hm]
  have hround : ∀ i, sdRound (cournot (Fin 3) a b c) (fun _ => qIval 0 m) i = qIval 0 m := by
    intro i
    have := cournot_round (a := a) (c := c) hb i hk le_rfl hm0
      (by rw [hk', hcbr0]) (by rw [hk', hcbrm]) (by rw [hk', hm]; field_simp; linarith)
    rw [this, hk', hcbr0, hcbrm]
  have hiter : ∀ n i, sdIter (cournot (Fin 3) a b c) (n + 1) i = qIval 0 m := by
    intro n
    induction n with
    | zero => exact fun i => cournot_round_zero hb hA i hk
    | succ n ih =>
      intro i
      change sdRound _ (sdIter _ (n + 1)) i = _
      have : sdIter (cournot (Fin 3) a b c) (n + 1) = fun _ => qIval 0 m := funext ih
      rw [this, hround]
  refine ⟨hiter, fun i s hs => ?_, fun i => ?_⟩
  · have : s ∈ sdRound (cournot (Fin 3) a b c) (fun _ => qIval 0 m) i := by rw [hround]; exact hs
    exact this.2
  · have hm0' : 0 < m := by rw [hm]; positivity
    refine ⟨0, ?_, ⟨m, hm0⟩, ?_, fun h => ?_⟩
    · refine Set.mem_iInter.2 fun n => ?_
      rcases n with _ | n
      · exact Set.mem_univ _
      · rw [hiter]; exact ⟨le_rfl, hm0⟩
    · refine Set.mem_iInter.2 fun n => ?_
      rcases n with _ | n
      · exact Set.mem_univ _
      · rw [hiter]; exact ⟨hm0, le_rfl⟩
    · have := congrArg NNReal.toReal h
      change (0 : ℝ) = m at this
      linarith

/-! ### Exercise 8.E.3: Cournot with privately known costs -/

/-- The probability of a firm's cost type: type `0` (cost `c_L`) has probability `μ`, type `1`
(cost `c_H`) probability `1 - μ`. -/
def typeP (μ : ℝ) (t : Fin 2) : ℝ := if t = 0 then μ else 1 - μ

/-- The unit cost of type `t`. -/
def tcost (cL cH : ℝ) (t : Fin 2) : ℝ := if t = 0 then cL else cH

/-- **Exercise 8.E.3** (MWG, p. 265). The linear Cournot duopoly of Exercise 8.B.5 in which each
firm's unit cost is `c_L` with probability `μ` and `c_H` with probability `1 - μ`, independently
across firms, and known only to the firm. -/
noncomputable def bayesCournot (a b μ cL cH : ℝ) :
    BayesianGame (Fin 2) (fun _ => ℝ≥0) (fun _ => Fin 2) where
  prior θ := typeP μ (θ 0) * typeP μ (θ 1)
  payoff i q θ := (a - b * ((q 0 : ℝ) + q 1) - tcost cL cH (θ i)) * q i

/-- The rival's expected output `μ s_j(c_L) + (1 - μ) s_j(c_H)`. -/
def expQ (μ : ℝ) (sj : Fin 2 → ℝ≥0) : ℝ := μ * sj 0 + (1 - μ) * sj 1

/-- A sum over the four type profiles. -/
theorem sum_fin2_fin2 (f : (Fin 2 → Fin 2) → ℝ) :
    ∑ θ, f θ = f ![0, 0] + f ![0, 1] + f ![1, 0] + f ![1, 1] := by
  have e : ∀ p q : Fin 2, (piFinTwoEquiv fun _ => Fin 2).symm (p, q) = ![p, q] := by
    intro p q
    funext k
    fin_cases k <;> rfl
  rw [← (piFinTwoEquiv fun _ => Fin 2).symm.sum_comp, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, e]
  ring

theorem bayesCournot_isPrior {a b μ cL cH : ℝ} (h0 : 0 ≤ μ) (h1 : μ ≤ 1) :
    (bayesCournot a b μ cL cH).IsPrior := by
  have hp : ∀ t, 0 ≤ typeP μ t := fun t => by
    unfold typeP; split_ifs <;> linarith
  refine ⟨fun θ => mul_nonneg (hp _) (hp _), ?_⟩
  simp only [bayesCournot]
  rw [sum_fin2_fin2]
  simp [typeP]
  ring

/-- The probability of each type. -/
theorem bayesCournot_typeProb (a b μ cL cH : ℝ) (i t : Fin 2) :
    (bayesCournot a b μ cL cH).typeProb i t = typeP μ t := by
  unfold BayesianGame.typeProb
  rw [Finset.sum_filter, sum_fin2_fin2]
  fin_cases i <;> fin_cases t <;> simp [bayesCournot, typeP] <;> ring

/-- The gain of type `t` of firm `i` from the output `x`: `Prob(t) x (a - c_t - bx - b E[q_j])`. -/
theorem bayesCournot_typeGain (a b μ cL cH : ℝ) (s : (i : Fin 2) → Fin 2 → ℝ≥0) (i t : Fin 2)
    (x : ℝ≥0) :
    (bayesCournot a b μ cL cH).typeGain s i t x =
      typeP μ t * ((x : ℝ) * (a - tcost cL cH t - b * x - b * expQ μ (s (1 - i)))) := by
  unfold BayesianGame.typeGain
  rw [Finset.sum_filter, sum_fin2_fin2]
  fin_cases i <;> fin_cases t <;>
    simp [bayesCournot, typeP, tcost, expQ, BayesianGame.play, Function.update] <;> ring

/-- Maximizing `x (K - bx)` over `x ≥ 0`: the maximizer is `max(K/(2b), 0)`. -/
theorem quad_argmax {b : ℝ} (hb : 0 < b) (K : ℝ) (y : ℝ≥0) :
    (∀ x : ℝ≥0, (x : ℝ) * (K - b * x) ≤ y * (K - b * y)) ↔ (y : ℝ) = max (K / (2 * b)) 0 := by
  have hy0 := NNReal.coe_nonneg y
  constructor
  · intro h
    rcases le_or_gt 0 K with hK | hK
    · have hK' : 0 ≤ K / (2 * b) := by positivity
      rw [max_eq_left hK']
      have := h ⟨K / (2 * b), hK'⟩
      change K / (2 * b) * (K - b * (K / (2 * b))) ≤ (y : ℝ) * (K - b * y) at this
      have h2 : (y - K / (2 * b)) ^ 2 * b ≤ 0 := by
        have e : (y - K / (2 * b)) ^ 2 * b =
            K / (2 * b) * (K - b * (K / (2 * b))) - y * (K - b * y) := by
          field_simp; ring
        linarith
      have h3 : (y - K / (2 * b)) ^ 2 = 0 := by
        have := mul_nonpos_iff.1 h2
        rcases this with ⟨_, h⟩ | ⟨h, _⟩
        · linarith
        · exact le_antisymm h (sq_nonneg _)
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h3
      linarith
    · have hK' : K / (2 * b) < 0 := div_neg_of_neg_of_pos hK (by linarith)
      rw [max_eq_right hK'.le]
      have h0 := h 0
      simp only [NNReal.coe_zero, zero_mul] at h0
      by_contra hne
      have hy' : 0 < (y : ℝ) := lt_of_le_of_ne hy0 (fun h' => hne (by rw [← h']))
      have : (y : ℝ) * (K - b * y) < 0 := mul_neg_of_pos_of_neg hy' (by nlinarith)
      linarith
  · intro hy x
    have hx0 := NNReal.coe_nonneg x
    rcases le_or_gt 0 K with hK | hK
    · rw [max_eq_left (by positivity)] at hy
      rw [hy]
      have e : K / (2 * b) * (K - b * (K / (2 * b))) - x * (K - b * x) =
          ((x : ℝ) - K / (2 * b)) ^ 2 * b := by
        field_simp; ring
      nlinarith [sq_nonneg ((x : ℝ) - K / (2 * b))]
    · rw [max_eq_right (div_neg_of_neg_of_pos hK (by linarith)).le] at hy
      rw [hy]
      have e : (x : ℝ) * (K - b * x) = x * K - b * (x * x) := by ring
      have := mul_nonpos_of_nonneg_of_nonpos hx0 hK.le
      have := mul_nonneg hb.le (mul_nonneg hx0 hx0)
      rw [e]
      linarith

/-- Proposition 8.E.1 for the Bayesian Cournot game: a profile is a Bayesian Nash equilibrium iff
each type of each firm produces `max((a - c_t - b E[q_j])/(2b), 0)`. -/
theorem bayesCournot_isBNE_iff {a b μ cL cH : ℝ} (hb : 0 < b) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (s : (i : Fin 2) → Fin 2 → ℝ≥0) :
    (bayesCournot a b μ cL cH).IsBNE s ↔ ∀ i t,
      (s i t : ℝ) = max ((a - tcost cL cH t - b * expQ μ (s (1 - i))) / (2 * b)) 0 := by
  rw [BayesianGame.proposition_8_E_1 _ (bayesCournot_isPrior hμ0.le hμ1.le)]
  have hpos : ∀ t, 0 < typeP μ t := fun t => by
    unfold typeP; split_ifs <;> linarith
  refine forall_congr' fun i => forall_congr' fun t => ?_
  rw [bayesCournot_typeProb]
  simp only [hpos t, true_implies, BayesianGame.condPayoff, bayesCournot_typeProb,
    bayesCournot_typeGain, mul_div_cancel_left₀ _ (hpos t).ne']
  rw [← quad_argmax hb]
  refine forall_congr' fun x => ?_
  constructor <;> intro h <;> linarith

/-- The Bayesian Nash equilibrium outputs `q_t = (2a - 3c_t + c̄)/(6b)`, `c̄ = μ c_L + (1 - μ) c_H`.
-/
noncomputable def bcq (a b μ cL cH : ℝ) (t : Fin 2) : ℝ :=
  (2 * a - 3 * tcost cL cH t + (μ * cL + (1 - μ) * cH)) / (6 * b)

/-- **Exercise 8.E.3** (MWG, p. 265). In the Bayesian Cournot duopoly (`b > 0`, `0 < μ < 1`,
`c_L < c_H`, and `3c_H ≤ 2a + c̄` so that the high-cost output is nonnegative), the unique Bayesian
Nash equilibrium has each firm produce `q_L = (2a - 3c_L + c̄)/(6b)` when its cost is `c_L` and
`q_H = (2a - 3c_H + c̄)/(6b)` when its cost is `c_H`, where `c̄ = μ c_L + (1 - μ) c_H`. -/
theorem exercise_8_E_3 {a b μ cL cH : ℝ} (hb : 0 < b) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : cL < cH) (hint : 3 * cH ≤ 2 * a + (μ * cL + (1 - μ) * cH))
    (s : (i : Fin 2) → Fin 2 → ℝ≥0) :
    (bayesCournot a b μ cL cH).IsBNE s ↔ ∀ i t, (s i t : ℝ) = bcq a b μ cL cH t := by
  rw [bayesCournot_isBNE_iff hb hμ0 hμ1]
  set cbar := μ * cL + (1 - μ) * cH with hcbar
  set Qb := (a - cbar) / (3 * b) with hQb
  have hq0 : ∀ t, 0 ≤ bcq a b μ cL cH t := by
    intro t
    unfold bcq tcost
    split_ifs
    · apply div_nonneg _ (by linarith)
      nlinarith
    · exact div_nonneg (by linarith) (by linarith)
  -- `g(Q, t)`, the best reply of type `t` to the rival's expected output `Q`
  set g : ℝ → Fin 2 → ℝ := fun Q t => max ((a - tcost cL cH t - b * Q) / (2 * b)) 0 with hg
  have hgQb : ∀ t, g Qb t = bcq a b μ cL cH t := by
    intro t
    simp only [hg]
    have : (a - tcost cL cH t - b * Qb) / (2 * b) = bcq a b μ cL cH t := by
      simp only [hQb, bcq, hcbar]; field_simp; ring
    rw [this, max_eq_left (hq0 t)]
  have hexpQb : ∀ q : Fin 2 → ℝ≥0, (∀ t, (q t : ℝ) = bcq a b μ cL cH t) → expQ μ q = Qb := by
    intro q hq
    simp only [expQ, hq, bcq, tcost, hQb, hcbar]
    simp
    field_simp
    ring
  have hlip : ∀ Q Q' t, |g Q t - g Q' t| ≤ |Q - Q'| / 2 := by
    intro Q Q' t
    refine (abs_max_sub_max_le_abs _ _ _).trans (le_of_eq ?_)
    rw [show (a - tcost cL cH t - b * Q) / (2 * b) - (a - tcost cL cH t - b * Q') / (2 * b) =
      -(Q - Q') / 2 by field_simp; ring, abs_div, abs_neg]
    norm_num
  constructor
  · intro h
    -- the expected outputs are a fixed point of a contraction
    have hE : ∀ i, expQ μ (s i) = μ * g (expQ μ (s (1 - i))) 0 +
        (1 - μ) * g (expQ μ (s (1 - i))) 1 := by
      intro i
      simp only [expQ, h i 0, h i 1, hg]
    have hF : ∀ Q, |μ * g Q 0 + (1 - μ) * g Q 1 - Qb| ≤ |Q - Qb| / 2 := by
      intro Q
      have hQb' : Qb = μ * g Qb 0 + (1 - μ) * g Qb 1 := by
        rw [hgQb, hgQb]
        have := hexpQb (fun t => ⟨bcq a b μ cL cH t, hq0 t⟩) (fun t => rfl)
        rw [← this]
        rfl
      conv_lhs => rw [hQb']
      have e : μ * g Q 0 + (1 - μ) * g Q 1 - (μ * g Qb 0 + (1 - μ) * g Qb 1) =
          μ * (g Q 0 - g Qb 0) + (1 - μ) * (g Q 1 - g Qb 1) := by ring
      rw [e]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_of_pos hμ0, abs_of_pos (by linarith : 0 < 1 - μ)]
      have h0 := hlip Q Qb 0
      have h1 := hlip Q Qb 1
      nlinarith
    have h10 : (1 : Fin 2) - 1 = 0 := by decide
    have h01 : (1 : Fin 2) - 0 = 1 := by decide
    have e0 := hE 0
    have e1 := hE 1
    rw [h01] at e0
    rw [h10] at e1
    have a0 : |expQ μ (s 0) - Qb| ≤ |expQ μ (s 1) - Qb| / 2 := by rw [e0]; exact hF _
    have a1 : |expQ μ (s 1) - Qb| ≤ |expQ μ (s 0) - Qb| / 2 := by rw [e1]; exact hF _
    have z0 : expQ μ (s 0) = Qb := by
      have := abs_nonneg (expQ μ (s 0) - Qb)
      have := abs_nonneg (expQ μ (s 1) - Qb)
      have : |expQ μ (s 0) - Qb| = 0 := by linarith
      exact sub_eq_zero.1 (abs_eq_zero.1 this)
    have z1 : expQ μ (s 1) = Qb := by
      have := abs_nonneg (expQ μ (s 1) - Qb)
      have : |expQ μ (s 1) - Qb| = 0 := by rw [z0, sub_self, abs_zero] at a1; linarith
      exact sub_eq_zero.1 (abs_eq_zero.1 this)
    intro i t
    rw [h i t, ← hgQb]
    rcases (show i = 0 ∨ i = 1 by fin_cases i <;> simp) with rfl | rfl
    · simp only [hg, h01, z1]
    · simp only [hg, h10, z0]
  · intro h i t
    rw [h i t, hexpQb _ (h (1 - i)), ← hgQb]

/-- A concrete instance of Exercise 8.E.3 (`a = 10`, `b = 1`, `μ = 1/2`, `c_L = 1`, `c_H = 2`):
the profile `q_L = 37/12`, `q_H = 31/12` for both firms is a Bayesian Nash equilibrium. -/
theorem exercise_8_E_3_instance :
    (bayesCournot 10 1 (1 / 2) 1 2).IsBNE
      (fun _ t => if t = 0 then ⟨37 / 12, by norm_num⟩ else ⟨31 / 12, by norm_num⟩) := by
  refine (exercise_8_E_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    _).2 fun i t => ?_
  fin_cases t <;> simp [bcq, tcost] <;> norm_num <;> rfl

end MWG.SimultaneousMoveGames
