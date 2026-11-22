/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGCoreFoundations.Basic

/-!
# The market for shoes (MWG Section 18.B, Exercise 18.B.5, p. 685)

`2I + 1` consumers `i : Fin (2I + 1)`; consumers `i < I` own one right shoe each, the other
`I + 1` own one left shoe each. Shoes are indivisible (quantities in `ℕ`) and every consumer has
utility `min {R, L}`. Allocations are feasible with free disposal (`∑ Rᵢ ≤ I`, `∑ Lᵢ ≤ I + 1`), as
with `Y = -ℝ²₊` in Section 18.B.

* (a) `shoe_paretoOptimal_iff`: an allocation is Pareto optimal iff it forms `I` pairs in total,
  `∑ᵢ min {Rᵢ, Lᵢ} = I`. A matched allocation (`Rᵢ = Lᵢ` for all `i`) that uses all right shoes is
  Pareto optimal (`exercise_18_B_5a`). Departures: a matched allocation that throws pairs away
  is not Pareto optimal (`shoe_matched_not_paretoOptimal`), and the converse holds only up to the
  disposal of unusable left shoes: a Pareto optimum has `Rᵢ ≤ Lᵢ` and `∑ Rᵢ = I`, and discarding
  the extra left shoes gives a matched Pareto optimum with the same utilities
  (`exercise_18_B_5a_converse`), but need not itself be matched (`shoe_paretoOptimal_not_matched`).
* (b) With blocking by weak dominance, the core consists exactly of the feasible allocations in
  which every owner of a right shoe gets one pair and the owners of left shoes get nothing
  (`exercise_18_B_5b`).
* (c) Walrasian equilibria (`shoeWalras`; prices `p ≥ 0`, a good may be disposed of only at price
  `0`, as profit maximization on `-ℝ²₊` requires): `p_R > 0` in every equilibrium
  (`shoeWalras_pR_pos`); with `p_L = 0` the owners of right shoes get one pair each and the others
  nothing; with `p_L > 0` nobody can afford a pair and every utility is `0`
  (`exercise_18_B_5c`); both kinds exist (`shoeWalras_pairs`, `shoeWalras_endowment`).
* (d) `exercise_18_B_5d`: the core is exactly the set of Walrasian allocations with `p_L = 0`: the
  single extra left shoe drives the price of left shoes to zero and gives the owners of right
  shoes all the surplus, even with few consumers. Because of indivisibility (no local
  nonsatiation) there are also Walrasian equilibria with `p_L > 0` (no trade) which are neither
  Pareto optimal nor in the core.
-/

namespace MWG.CoreFoundations

variable {I : ℕ}

/-- **Exercise 18.B.5** (MWG, p. 685). The utility `min {Rᵢ, Lᵢ}` of consumer `i` at the
allocation `a` (`a i = (Rᵢ, Lᵢ)`). -/
def shoeU (a : Fin (2 * I + 1) → ℕ × ℕ) (i : Fin (2 * I + 1)) : ℕ := min (a i).1 (a i).2

/-- **Exercise 18.B.5** (MWG, p. 685). Feasibility with free disposal: at most `I` right shoes and
`I + 1` left shoes are consumed. -/
def shoeFeasible (I : ℕ) (a : Fin (2 * I + 1) → ℕ × ℕ) : Prop :=
  ∑ i, (a i).1 ≤ I ∧ ∑ i, (a i).2 ≤ I + 1

/-- **Exercise 18.B.5(a)** (MWG, p. 685). Pareto optimality. -/
def shoeParetoOptimal (I : ℕ) (a : Fin (2 * I + 1) → ℕ × ℕ) : Prop :=
  shoeFeasible I a ∧ ¬ ∃ a', shoeFeasible I a' ∧ (∀ i, shoeU a i ≤ shoeU a' i) ∧
    ∃ i, shoeU a i < shoeU a' i

/-- **Exercise 18.B.5(a)** (MWG, p. 685). A matched allocation: every consumer gets as many right
as left shoes. -/
def shoeMatched (a : Fin (2 * I + 1) → ℕ × ℕ) : Prop := ∀ i, (a i).1 = (a i).2

/-- **Exercise 18.B.5(b)** (MWG, p. 685). Blocking with weak dominance: with its own shoes (the
right shoes of its members `i < I` and the left shoes of the others) the coalition `S` can make
every member at least as well off and some member strictly better off. -/
def shoeBlocks (I : ℕ) (S : Finset (Fin (2 * I + 1))) (a : Fin (2 * I + 1) → ℕ × ℕ) : Prop :=
  ∃ a' : Fin (2 * I + 1) → ℕ × ℕ,
    ∑ i ∈ S, (a' i).1 ≤ (S.filter fun i : Fin (2 * I + 1) => (i : ℕ) < I).card ∧
    ∑ i ∈ S, (a' i).2 ≤ (S.filter fun i : Fin (2 * I + 1) => ¬ (i : ℕ) < I).card ∧
    (∀ i ∈ S, shoeU a i ≤ shoeU a' i) ∧ ∃ i ∈ S, shoeU a i < shoeU a' i

/-- **Exercise 18.B.5(b)** (MWG, p. 685). The core (with weak-dominance blocking). -/
def shoeCore (I : ℕ) : Set (Fin (2 * I + 1) → ℕ × ℕ) :=
  {a | shoeFeasible I a ∧ ∀ S, ¬ shoeBlocks I S a}

/-- The wealth of consumer `i` at prices `(p_R, p_L)`: the value of her shoe. -/
noncomputable def shoeWealth (I : ℕ) (pR pL : ℝ) (i : Fin (2 * I + 1)) : ℝ :=
  if (i : ℕ) < I then pR else pL

/-- **Exercise 18.B.5(c)** (MWG, p. 685). A Walrasian equilibrium with prices `(p_R, p_L)`:
`p ≥ 0`, feasibility, a good with positive price is not disposed of (profit maximization on the
free disposal technology), and every consumer's bundle is affordable and maximizes `min {R, L}`
over the affordable bundles of `ℕ²`. -/
def shoeWalras (I : ℕ) (pR pL : ℝ) (a : Fin (2 * I + 1) → ℕ × ℕ) : Prop :=
  0 ≤ pR ∧ 0 ≤ pL ∧ shoeFeasible I a ∧ (0 < pR → ∑ i, (a i).1 = I) ∧
    (0 < pL → ∑ i, (a i).2 = I + 1) ∧
    ∀ i, pR * (a i).1 + pL * (a i).2 ≤ shoeWealth I pR pL i ∧
      ∀ r l : ℕ, pR * r + pL * l ≤ shoeWealth I pR pL i → min r l ≤ shoeU a i

/-- `I` consumers own right shoes. -/
theorem shoe_card_right (I : ℕ) :
    (Finset.univ.filter fun i : Fin (2 * I + 1) => (i : ℕ) < I).card = I := by
  rw [Fin.card_filter_val_lt]
  omega

/-- `I + 1` consumers own left shoes. -/
theorem shoe_card_left (I : ℕ) :
    (Finset.univ.filter fun i : Fin (2 * I + 1) => ¬ (i : ℕ) < I).card = I + 1 := by
  have := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (p := fun i : Fin (2 * I + 1) => (i : ℕ) < I)
  rw [shoe_card_right, Finset.card_univ, Fintype.card_fin] at this
  omega

/-- Utilities sum to at most the number of right shoes used. -/
theorem shoe_sum_u_le {a : Fin (2 * I + 1) → ℕ × ℕ} (S : Finset (Fin (2 * I + 1))) :
    ∑ i ∈ S, shoeU a i ≤ ∑ i ∈ S, (a i).1 :=
  Finset.sum_le_sum fun _ _ => min_le_left _ _

/-- If `fᵢ ≥ 1` on `s` and `∑_s f ≤ #s`, then `f = 1` on `s`. -/
theorem shoe_eq_one_of_sum_le {s : Finset (Fin (2 * I + 1))} {f : Fin (2 * I + 1) → ℕ}
    (h1 : ∀ i ∈ s, 1 ≤ f i) (hs : ∑ i ∈ s, f i ≤ s.card) : ∀ i ∈ s, f i = 1 := by
  have hc : s.card = ∑ i ∈ s, 1 := by simp
  have heq : ∑ i ∈ s, 1 = ∑ i ∈ s, f i := le_antisymm (Finset.sum_le_sum h1) (hc ▸ hs)
  intro i hi
  exact ((Finset.sum_eq_sum_iff_of_le h1).mp heq i hi).symm

/-- **Exercise 18.B.5(a)** (MWG, p. 685). A feasible allocation is Pareto optimal iff it forms `I`
pairs: `∑ᵢ min {Rᵢ, Lᵢ} = I`. -/
theorem shoe_paretoOptimal_iff (a : Fin (2 * I + 1) → ℕ × ℕ) :
    shoeParetoOptimal I a ↔ shoeFeasible I a ∧ ∑ i, shoeU a i = I := by
  classical
  constructor
  · rintro ⟨hfe, hpo⟩
    refine ⟨hfe, le_antisymm ((shoe_sum_u_le _).trans hfe.1) ?_⟩
    by_contra hlt
    push Not at hlt
    -- give the unused pairs to consumer `0`
    set k := I - ∑ i, shoeU a i with hk
    set a' : Fin (2 * I + 1) → ℕ × ℕ := fun i =>
      (shoeU a i + if i = 0 then k else 0, shoeU a i + if i = 0 then k else 0) with ha'
    have hu' : ∀ i, shoeU a' i = shoeU a i + if i = 0 then k else 0 := fun i => by
      simp [shoeU, ha']
    have hsum : ∑ i, (shoeU a i + if i = 0 then k else 0) = I := by
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ (0 : Fin (2 * I + 1))]
      simp only [Finset.mem_univ, ↓reduceIte]
      omega
    apply hpo
    refine ⟨a', ⟨?_, ?_⟩, fun i => ?_, 0, ?_⟩
    · simp only [ha']; omega
    · simp only [ha']; omega
    · rw [hu']; omega
    · rw [hu']; simp only [↓reduceIte]; omega
  · rintro ⟨hfe, hsum⟩
    refine ⟨hfe, ?_⟩
    rintro ⟨a', hfe', hle, i, hi⟩
    have := Finset.sum_lt_sum (fun j _ => hle j) ⟨i, Finset.mem_univ i, hi⟩
    have := (shoe_sum_u_le (a := a') Finset.univ).trans hfe'.1
    omega

/-- **Exercise 18.B.5(a)** (MWG, p. 685). A matched allocation that uses all `I` right shoes is
Pareto optimal. -/
theorem exercise_18_B_5a (a : Fin (2 * I + 1) → ℕ × ℕ) (hfe : shoeFeasible I a)
    (hm : shoeMatched a) (hall : ∑ i, (a i).1 = I) : shoeParetoOptimal I a := by
  refine (shoe_paretoOptimal_iff a).2 ⟨hfe, ?_⟩
  exact (Finset.sum_congr rfl fun i _ => by simp [shoeU, hm i]).trans hall

/-- **Exercise 18.B.5(a)** (MWG, p. 685): a matched allocation that discards pairs (here,
nobody gets any shoe) is not Pareto optimal when `I ≥ 1`. -/
theorem shoe_matched_not_paretoOptimal (hI : 1 ≤ I) :
    shoeMatched (fun _ : Fin (2 * I + 1) => ((0 : ℕ), (0 : ℕ))) ∧
      shoeFeasible I (fun _ => (0, 0)) ∧ ¬ shoeParetoOptimal I (fun _ => (0, 0)) := by
  refine ⟨fun _ => rfl, ⟨by simp, by simp⟩, fun h => ?_⟩
  have := ((shoe_paretoOptimal_iff _).1 h).2
  simp [shoeU] at this
  omega

/-- **Exercise 18.B.5(a)** (MWG, p. 685), the converse up to disposal: a Pareto optimum uses all
right shoes, gives no one more right than left shoes, and discarding the unusable left shoes
(`Lᵢ ↦ Rᵢ`) gives a matched Pareto optimum with the same utilities. -/
theorem exercise_18_B_5a_converse {a : Fin (2 * I + 1) → ℕ × ℕ} (h : shoeParetoOptimal I a) :
    (∀ i, (a i).1 ≤ (a i).2) ∧ ∑ i, (a i).1 = I ∧
      shoeMatched (fun i => ((a i).1, (a i).1)) ∧
      shoeParetoOptimal I (fun i => ((a i).1, (a i).1)) ∧
      ∀ i, shoeU (fun i => ((a i).1, (a i).1)) i = shoeU a i := by
  obtain ⟨hfe, hsum⟩ := (shoe_paretoOptimal_iff a).1 h
  have hR : ∑ i, (a i).1 = I := by
    have := shoe_sum_u_le (a := a) Finset.univ
    have := hfe.1
    omega
  have heq : ∀ i, shoeU a i = (a i).1 := by
    have : ∑ i, shoeU a i = ∑ i, (a i).1 := by rw [hsum, hR]
    intro i
    exact (Finset.sum_eq_sum_iff_of_le fun j _ => min_le_left _ _).mp this i (Finset.mem_univ i)
  have hle : ∀ i, (a i).1 ≤ (a i).2 := fun i => by
    have := heq i
    simp only [shoeU] at this
    omega
  have hu : ∀ i, shoeU (fun i => ((a i).1, (a i).1)) i = shoeU a i := fun i => by
    simp only [shoeU, min_self]
    exact (min_eq_left (hle i)).symm
  refine ⟨hle, hR, fun _ => rfl, (shoe_paretoOptimal_iff _).2 ⟨⟨?_, ?_⟩, ?_⟩, hu⟩
  · simpa using hfe.1
  · simp only
    omega
  · simp only [hu]
    exact hsum

/-- With `I = 1`: consumer 1 holds one right and two left shoes, the others nothing. -/
def shoeExample : Fin (2 * 1 + 1) → ℕ × ℕ := ![(1, 2), (0, 0), (0, 0)]

/-- **Exercise 18.B.5(a)** (MWG, p. 685): a Pareto optimum need not be matched. With `I = 1`,
consumer 1 holding one right and two left shoes is Pareto optimal. -/
theorem shoe_paretoOptimal_not_matched :
    shoeParetoOptimal 1 shoeExample ∧ ¬ shoeMatched shoeExample := by
  refine ⟨(shoe_paretoOptimal_iff _).2 ⟨⟨by decide, by decide⟩, by decide⟩, fun h => ?_⟩
  have := h 0
  simp [shoeExample] at this

/-- **Exercise 18.B.5(b)** (MWG, p. 685). With blocking by weak dominance, the core consists of
the feasible allocations in which every owner of a right shoe gets exactly one pair (utility `1`)
and every owner of a left shoe gets utility `0`. -/
theorem exercise_18_B_5b (a : Fin (2 * I + 1) → ℕ × ℕ) :
    a ∈ shoeCore I ↔
      shoeFeasible I a ∧ ∀ i : Fin (2 * I + 1), shoeU a i = if (i : ℕ) < I then 1 else 0 := by
  classical
  set R := Finset.univ.filter fun i : Fin (2 * I + 1) => (i : ℕ) < I with hRdef
  set Lf := Finset.univ.filter fun i : Fin (2 * I + 1) => ¬ (i : ℕ) < I with hLdef
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun i : Fin (2 * I + 1) => (i : ℕ) < I) (shoeU a)
  constructor
  · rintro ⟨hfe, hcore⟩
    -- the core is Pareto optimal (the grand coalition blocks by weak dominance)
    have hpo : shoeParetoOptimal I a := by
      refine ⟨hfe, fun ⟨a', hfe', hle, i, hi⟩ => hcore Finset.univ ⟨a', ?_, ?_, fun j _ => hle j,
        i, Finset.mem_univ i, hi⟩⟩
      · rw [shoe_card_right]; exact hfe'.1
      · rw [shoe_card_left]; exact hfe'.2
    have hsum := ((shoe_paretoOptimal_iff a).1 hpo).2
    -- every owner of a right shoe has a pair
    have hright : ∀ i ∈ R, 1 ≤ shoeU a i := by
      intro i hi
      by_contra h0
      have hi0 : shoeU a i = 0 := by omega
      have hiR : (i : ℕ) < I := (Finset.mem_filter.mp hi).2
      obtain ⟨j, hj, hj0⟩ : ∃ j ∈ Lf, shoeU a j = 0 := by
        by_contra hall
        push Not at hall
        have h1 : ∑ j ∈ Lf, 1 ≤ ∑ j ∈ Lf, shoeU a j :=
          Finset.sum_le_sum fun j hj => Nat.one_le_iff_ne_zero.mpr (hall j hj)
        rw [Finset.sum_const, smul_eq_mul, mul_one, hLdef, shoe_card_left] at h1
        omega
      have hjL : ¬ (j : ℕ) < I := (Finset.mem_filter.mp hj).2
      have hij : i ≠ j := fun h => hjL (h ▸ hiR)
      refine hcore {i, j} ⟨fun k => if k = i then (1, 1) else (0, 0), ?_, ?_, fun k hk => ?_,
        i, Finset.mem_insert_self i {j}, ?_⟩
      · rw [Finset.sum_pair hij, Finset.filter_insert, Finset.filter_singleton]
        simp [hiR, hjL, hij.symm]
      · rw [Finset.sum_pair hij, Finset.filter_insert, Finset.filter_singleton]
        simp [hiR, hjL, hij.symm]
      · rcases Finset.mem_insert.mp hk with rfl | hk
        · rw [hi0]; exact Nat.zero_le _
        · rw [Finset.mem_singleton] at hk
          subst hk
          rw [hj0]; exact Nat.zero_le _
      · rw [hi0]; simp [shoeU]
    have hRsum : ∑ i ∈ R, shoeU a i ≤ R.card := by
      rw [hRdef, shoe_card_right]
      omega
    have hone := shoe_eq_one_of_sum_le hright hRsum
    have hRI : ∑ i ∈ R, shoeU a i = I := by
      rw [Finset.sum_congr rfl hone, Finset.sum_const, smul_eq_mul, mul_one, hRdef,
        shoe_card_right]
    have hL0 : ∑ i ∈ Lf, shoeU a i = 0 := by
      simp only [← hRdef, ← hLdef] at hsplit
      omega
    refine ⟨hfe, fun i => ?_⟩
    by_cases hi : (i : ℕ) < I
    · simp only [hi, ↓reduceIte]
      exact hone i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
    · simp only [hi, ↓reduceIte]
      exact (Finset.sum_eq_zero_iff.mp hL0) i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
  · rintro ⟨hfe, hu⟩
    refine ⟨hfe, fun S ⟨a', hR', _, hle, i, hiS, hi⟩ => ?_⟩
    have hlt := Finset.sum_lt_sum hle ⟨i, hiS, hi⟩
    have hSu : ∑ j ∈ S, shoeU a j = (S.filter fun j : Fin (2 * I + 1) => (j : ℕ) < I).card := by
      rw [Finset.card_filter]
      exact Finset.sum_congr rfl fun j _ => hu j
    have := (shoe_sum_u_le (a := a') S).trans hR'
    omega

/-- **Exercise 18.B.5(c)** (MWG, p. 685). In every Walrasian equilibrium `p_R > 0`: if right
shoes were free, each of the `I + 1` owners of left shoes could afford a pair, and only `I` right
shoes exist. -/
theorem shoeWalras_pR_pos {pR pL : ℝ} {a : Fin (2 * I + 1) → ℕ × ℕ} (h : shoeWalras I pR pL a) :
    0 < pR := by
  classical
  obtain ⟨hpR, hpL, hfe, -, -, hopt⟩ := h
  rcases hpR.lt_or_eq with hlt | heq
  · exact hlt
  exfalso
  have hone : ∀ j ∈ Finset.univ.filter fun i : Fin (2 * I + 1) => ¬ (i : ℕ) < I,
      1 ≤ (a j).1 := by
    intro j hj
    have hjL := (Finset.mem_filter.mp hj).2
    have := (hopt j).2 1 1 (by simp [shoeWealth, hjL, ← heq])
    simp only [shoeU] at this
    omega
  have h1 := Finset.sum_le_sum hone
  rw [Finset.sum_const, smul_eq_mul, mul_one, shoe_card_left] at h1
  have h2 := Finset.sum_le_sum_of_subset (f := fun i => (a i).1)
    (Finset.filter_subset (fun i : Fin (2 * I + 1) => ¬ (i : ℕ) < I) Finset.univ)
  have := hfe.1
  omega

/-- **Exercise 18.B.5(c)** (MWG, p. 685). The Walrasian equilibria: either `p_L = 0` and every
owner of a right shoe gets one pair while the owners of left shoes get nothing, or `p_L > 0` and
nobody can afford a pair (every utility is `0`). In both cases `p_R > 0`. -/
theorem exercise_18_B_5c {pR pL : ℝ} {a : Fin (2 * I + 1) → ℕ × ℕ} (h : shoeWalras I pR pL a) :
    0 < pR ∧ ((pL = 0 ∧ ∀ i : Fin (2 * I + 1), shoeU a i = if (i : ℕ) < I then 1 else 0) ∨
      (0 < pL ∧ ∀ i : Fin (2 * I + 1), shoeU a i = 0)) := by
  classical
  have hpR := shoeWalras_pR_pos h
  obtain ⟨-, hpL, hfe, -, -, hopt⟩ := h
  refine ⟨hpR, ?_⟩
  rcases hpL.lt_or_eq with hlt | heq
  · -- a pair costs `p_R + p_L`, more than anyone's wealth
    refine Or.inr ⟨hlt, fun i => ?_⟩
    by_contra hne
    have h1 : 1 ≤ (a i).1 := by simp only [shoeU] at hne; omega
    have h2 : 1 ≤ (a i).2 := by simp only [shoeU] at hne; omega
    have hb := (hopt i).1
    have h1' : (1 : ℝ) ≤ (a i).1 := by exact_mod_cast h1
    have h2' : (1 : ℝ) ≤ (a i).2 := by exact_mod_cast h2
    unfold shoeWealth at hb
    split_ifs at hb <;> nlinarith
  · refine Or.inl ⟨heq.symm, ?_⟩
    have hleft : ∀ i : Fin (2 * I + 1), ¬ (i : ℕ) < I → shoeU a i = 0 := by
      intro i hi
      have hb := (hopt i).1
      simp only [shoeWealth, hi, ↓reduceIte, ← heq, zero_mul, add_zero] at hb
      have : (a i).1 = 0 := by
        by_contra h0
        have : (1 : ℝ) ≤ (a i).1 := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0
        nlinarith
      simp [shoeU, this]
    have hright : ∀ i ∈ Finset.univ.filter fun i : Fin (2 * I + 1) => (i : ℕ) < I,
        1 ≤ shoeU a i := by
      intro i hi
      have hiR := (Finset.mem_filter.mp hi).2
      exact (hopt i).2 1 1 (by simp [shoeWealth, hiR, ← heq])
    have hRsum : ∑ i ∈ Finset.univ.filter fun i : Fin (2 * I + 1) => (i : ℕ) < I, shoeU a i ≤
        (Finset.univ.filter fun i : Fin (2 * I + 1) => (i : ℕ) < I).card := by
      rw [shoe_card_right]
      exact le_trans (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _))
        ((shoe_sum_u_le _).trans hfe.1)
    have hone := shoe_eq_one_of_sum_le hright hRsum
    intro i
    by_cases hi : (i : ℕ) < I
    · simp only [hi, ↓reduceIte]
      exact hone i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
    · simp only [hi, ↓reduceIte]
      exact hleft i hi

/-- The allocation in which every owner of a right shoe gets one pair. -/
def shoePairs (I : ℕ) : Fin (2 * I + 1) → ℕ × ℕ := fun i => if (i : ℕ) < I then (1, 1) else (0, 0)

/-- The endowment allocation (no trade). -/
def shoeEndow (I : ℕ) : Fin (2 * I + 1) → ℕ × ℕ := fun i => if (i : ℕ) < I then (1, 0) else (0, 1)

/-- `∑ᵢ [i < I] = I` on `Fin (2I + 1)`. -/
theorem shoe_sum_ite_right (I : ℕ) :
    ∑ i : Fin (2 * I + 1), (if (i : ℕ) < I then 1 else 0) = I := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_one,
    shoe_card_right]

/-- `∑ᵢ [i ≥ I] = I + 1` on `Fin (2I + 1)`. -/
theorem shoe_sum_ite_left (I : ℕ) :
    ∑ i : Fin (2 * I + 1), (if (i : ℕ) < I then 0 else 1) = I + 1 := by
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul, mul_one,
    shoe_card_left]

/-- **Exercise 18.B.5(c)** (MWG, p. 685). For every `p_R > 0`, the prices `(p_R, 0)` with one pair
for every owner of a right shoe form a Walrasian equilibrium. -/
theorem shoeWalras_pairs {pR : ℝ} (hpR : 0 < pR) : shoeWalras I pR 0 (shoePairs I) := by
  have hR : ∑ i, (shoePairs I i).1 = I := by
    refine (Finset.sum_congr rfl fun i _ => ?_).trans (shoe_sum_ite_right I)
    unfold shoePairs
    split_ifs <;> rfl
  have hL : ∑ i, (shoePairs I i).2 = I := by
    refine (Finset.sum_congr rfl fun i _ => ?_).trans (shoe_sum_ite_right I)
    unfold shoePairs
    split_ifs <;> rfl
  refine ⟨hpR.le, le_rfl, ⟨hR.le, by omega⟩, fun _ => hR, fun h => absurd h (lt_irrefl 0),
    fun i => ⟨?_, fun r l hb => ?_⟩⟩
  · unfold shoePairs shoeWealth
    split_ifs <;> simp
  · unfold shoeWealth at hb
    unfold shoeU shoePairs
    split_ifs at hb ⊢ with hi
    · simp only [zero_mul, add_zero] at hb
      have : (r : ℝ) ≤ 1 := by nlinarith
      have : r ≤ 1 := by exact_mod_cast this
      simp only
      omega
    · simp only [zero_mul, add_zero] at hb
      have : (r : ℝ) ≤ 0 := by nlinarith
      have : r = 0 := by exact_mod_cast le_antisymm this (Nat.cast_nonneg r)
      simp [this]

/-- **Exercise 18.B.5(c)** (MWG, p. 685). For all `p_R, p_L > 0` no consumer can afford a pair, and
the endowment allocation (no trade) is a Walrasian equilibrium. -/
theorem shoeWalras_endowment {pR pL : ℝ} (hpR : 0 < pR) (hpL : 0 < pL) :
    shoeWalras I pR pL (shoeEndow I) := by
  have hR : ∑ i, (shoeEndow I i).1 = I := by
    refine (Finset.sum_congr rfl fun i _ => ?_).trans (shoe_sum_ite_right I)
    unfold shoeEndow
    split_ifs <;> rfl
  have hL : ∑ i, (shoeEndow I i).2 = I + 1 := by
    refine (Finset.sum_congr rfl fun i _ => ?_).trans (shoe_sum_ite_left I)
    unfold shoeEndow
    split_ifs <;> rfl
  refine ⟨hpR.le, hpL.le, ⟨hR.le, hL.le⟩, fun _ => hR, fun _ => hL, fun i => ⟨?_, fun r l hb => ?_⟩⟩
  · unfold shoeEndow shoeWealth
    split_ifs <;> simp
  · by_contra hne
    have h1 : 1 ≤ r := by omega
    have h2 : 1 ≤ l := by omega
    have h1' : (1 : ℝ) ≤ r := by exact_mod_cast h1
    have h2' : (1 : ℝ) ≤ l := by exact_mod_cast h2
    unfold shoeWealth at hb
    split_ifs at hb <;> nlinarith

/-- **Exercise 18.B.5(d)** (MWG, p. 685). The core (weak-dominance blocking) is exactly the set of
Walrasian equilibrium allocations with `p_L = 0` (`p_R > 0`): the owners of right shoes, the
short side of the market, get all the surplus. With `I ≥ 1` there are also Walrasian equilibria
with `p_L > 0` (no trade) that are neither Pareto optimal nor in the core (indivisibility: local
nonsatiation fails). -/
theorem exercise_18_B_5d :
    shoeCore I = {a | ∃ pR : ℝ, 0 < pR ∧ shoeWalras I pR 0 a} ∧
      (1 ≤ I → shoeWalras I 1 1 (shoeEndow I) ∧ shoeEndow I ∉ shoeCore I ∧
        ¬ shoeParetoOptimal I (shoeEndow I)) := by
  classical
  refine ⟨Set.ext fun a => ⟨fun ha => ?_, fun ⟨pR, hpR, h⟩ => ?_⟩, fun hI => ?_⟩
  · -- a core allocation: every owner of a right shoe has exactly one right shoe
    obtain ⟨hfe, hu⟩ := (exercise_18_B_5b a).1 ha
    have hR1 : ∀ i ∈ Finset.univ.filter fun i : Fin (2 * I + 1) => (i : ℕ) < I,
        1 ≤ (a i).1 := by
      intro i hi
      have := hu i
      simp only [(Finset.mem_filter.mp hi).2, ↓reduceIte, shoeU] at this
      omega
    have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun i : Fin (2 * I + 1) => (i : ℕ) < I) (fun i => (a i).1)
    have hge := Finset.sum_le_sum hR1
    rw [Finset.sum_const, smul_eq_mul, mul_one, shoe_card_right] at hge
    have hRle : ∑ i ∈ Finset.univ.filter fun i : Fin (2 * I + 1) => (i : ℕ) < I, (a i).1 ≤
        (Finset.univ.filter fun i : Fin (2 * I + 1) => (i : ℕ) < I).card := by
      rw [shoe_card_right]; have := hfe.1; omega
    have hone := shoe_eq_one_of_sum_le hR1 hRle
    have hL0 : ∑ i ∈ Finset.univ.filter fun i : Fin (2 * I + 1) => ¬ (i : ℕ) < I, (a i).1 = 0 := by
      have := hfe.1; omega
    refine ⟨1, one_pos, le_of_lt one_pos, le_rfl, hfe, fun _ => by have := hfe.1; omega,
      fun h => absurd h (lt_irrefl 0), fun i => ⟨?_, fun r l hb => ?_⟩⟩
    · unfold shoeWealth
      by_cases hi : (i : ℕ) < I
      · simp only [hi, ↓reduceIte, zero_mul, add_zero, one_mul]
        exact_mod_cast (hone i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)).le
      · simp only [hi, ↓reduceIte, zero_mul, add_zero, one_mul]
        have := (Finset.sum_eq_zero_iff.mp hL0) i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
        simp [this]
    · rw [hu i]
      unfold shoeWealth at hb
      simp only [zero_mul, add_zero, one_mul] at hb
      split_ifs at hb ⊢
      · have : r ≤ 1 := by exact_mod_cast hb
        omega
      · have : r = 0 := by exact_mod_cast le_antisymm hb (Nat.cast_nonneg r)
        simp [this]
  · obtain ⟨-, hc⟩ := exercise_18_B_5c h
    rcases hc with ⟨-, hu⟩ | ⟨hlt, -⟩
    · exact (exercise_18_B_5b a).2 ⟨h.2.2.1, hu⟩
    · exact absurd hlt (lt_irrefl 0)
  · have hw := shoeWalras_endowment (I := I) one_pos one_pos
    have h0 : shoeU (shoeEndow I) ⟨0, by omega⟩ = 0 := by
      simp [shoeU, shoeEndow, show (0 : ℕ) < I by omega]
    refine ⟨hw, fun hc => ?_, fun hpo => ?_⟩
    · have := ((exercise_18_B_5b _).1 hc).2 ⟨0, by omega⟩
      rw [h0] at this
      simp [show (0 : ℕ) < I by omega] at this
    · have hsum := ((shoe_paretoOptimal_iff _).1 hpo).2
      have : ∀ i, shoeU (shoeEndow I) i = 0 := fun i => by
        unfold shoeU shoeEndow; split_ifs <;> simp
      simp only [this, Finset.sum_const_zero] at hsum
      omega

end MWG.CoreFoundations
