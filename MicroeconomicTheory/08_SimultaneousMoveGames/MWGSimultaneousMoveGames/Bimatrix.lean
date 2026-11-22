/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGSimultaneousMoveGames.TremblingHand
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

/-!
# Two-player games given by payoff tables

MWG's two-player examples are payoff tables: player 1 (`i = 0`) chooses a row among `m`, player 2
(`i = 1`) a column among `n`. `bimatrix u₁ u₂` is the Chapter 7 normal form with strategy sets
`Fin m` and `Fin n` (`S2 m n`), and `pp a b` is the pure profile (row `a`, column `b`).

This module translates the chapter's notions for such games into statements about the table:
pure payoffs after a deviation (`bimatrix_update_zero`, `bimatrix_update_one`), Nash
equilibrium (`bimatrix_isNash_iff`), domination (`bimatrix_strictlyDominates_zero_iff`, …), and
mixed payoffs (`mixedPayoff_fin_two`, `bimatrix_mixedPayoff_zero`, …).
-/

namespace MWG.SimultaneousMoveGames

open MWG.NoncooperativeGames Function Finset

/-- The strategy sets `S_1 = Fin m` (rows) and `S_2 = Fin n` (columns). -/
abbrev S2 (m n : ℕ) : Fin 2 → Type := fun i => Fin (![m, n] i)

/-- The two-player game with payoff tables `u₁` (player 1, rows) and `u₂` (player 2). -/
def bimatrix {m n : ℕ} (u₁ u₂ : Fin m → Fin n → ℝ) : NormalForm (Fin 2) (S2 m n) where
  payoff i s := if i = 0 then u₁ (s 0) (s 1) else u₂ (s 0) (s 1)

/-- The pure profile (row `a`, column `b`). -/
def pp {m n : ℕ} (a : Fin m) (b : Fin n) : (i : Fin 2) → S2 m n i :=
  Fin.cons a (Fin.cons b finZeroElim)

@[simp] theorem pp_zero {m n : ℕ} (a : Fin m) (b : Fin n) : pp a b 0 = a := rfl

@[simp] theorem pp_one {m n : ℕ} (a : Fin m) (b : Fin n) : pp a b 1 = b := rfl

theorem eq_pp {m n : ℕ} (s : (i : Fin 2) → S2 m n i) : s = pp (s 0) (s 1) := by
  funext i
  fin_cases i <;> rfl

variable {m n : ℕ} (u₁ u₂ : Fin m → Fin n → ℝ)

@[simp] theorem bimatrix_payoff_zero (s : (i : Fin 2) → S2 m n i) :
    (bimatrix u₁ u₂).payoff 0 s = u₁ (s 0) (s 1) := rfl

@[simp] theorem bimatrix_payoff_one (s : (i : Fin 2) → S2 m n i) :
    (bimatrix u₁ u₂).payoff 1 s = u₂ (s 0) (s 1) := rfl

/-- Player 1 deviates to row `a`. -/
@[simp] theorem bimatrix_update_zero (s : (i : Fin 2) → S2 m n i) (a : Fin m) (k : Fin 2) :
    (bimatrix u₁ u₂).payoff k (update s 0 a) = if k = 0 then u₁ a (s 1) else u₂ a (s 1) := by
  simp [bimatrix, Function.update]

/-- Player 2 deviates to column `b`. -/
@[simp] theorem bimatrix_update_one (s : (i : Fin 2) → S2 m n i) (b : Fin n) (k : Fin 2) :
    (bimatrix u₁ u₂).payoff k (update s 1 b) = if k = 0 then u₁ (s 0) b else u₂ (s 0) b := by
  simp [bimatrix, Function.update]

/-- Nash equilibrium (Definition 8.D.1) in a two-player table. -/
theorem bimatrix_isNash_iff (a : Fin m) (b : Fin n) :
    IsNashEquilibrium (bimatrix u₁ u₂) (pp a b) ↔
      (∀ a', u₁ a' b ≤ u₁ a b) ∧ ∀ b', u₂ a b' ≤ u₂ a b := by
  constructor
  · intro h
    refine ⟨fun a' => ?_, fun b' => ?_⟩
    · simpa using h 0 a'
    · simpa using h 1 b'
  · rintro ⟨h1, h2⟩ i t
    fin_cases i
    · simpa using h1 t
    · simpa using h2 t

/-- Strict domination (Definition 8.B.2) for player 1. -/
theorem bimatrix_strictlyDominates_zero_iff (a' a : Fin m) :
    StrictlyDominates (bimatrix u₁ u₂) 0 a' a ↔ ∀ b, u₁ a b < u₁ a' b := by
  constructor
  · intro h b
    simpa using h (pp a b)
  · intro h r
    simpa using h (r 1)

/-- Strict domination (Definition 8.B.2) for player 2. -/
theorem bimatrix_strictlyDominates_one_iff (b' b : Fin n) :
    StrictlyDominates (bimatrix u₁ u₂) 1 b' b ↔ ∀ a, u₂ a b < u₂ a b' := by
  constructor
  · intro h a
    simpa using h (pp a b)
  · intro h r
    simpa using h (r 0)

/-- Weak domination (Definition 8.B.3) for player 1. -/
theorem bimatrix_weaklyDominates_zero_iff (a' a : Fin m) :
    WeaklyDominates (bimatrix u₁ u₂) 0 a' a ↔
      (∀ b, u₁ a b ≤ u₁ a' b) ∧ ∃ b, u₁ a b < u₁ a' b := by
  constructor
  · rintro ⟨h1, r, hr⟩
    exact ⟨fun b => by simpa using h1 (pp a b), r 1, by simpa using hr⟩
  · rintro ⟨h1, b, hb⟩
    exact ⟨fun r => by simpa using h1 (r 1), pp a b, by simpa using hb⟩

/-- Weak domination (Definition 8.B.3) for player 2. -/
theorem bimatrix_weaklyDominates_one_iff (b' b : Fin n) :
    WeaklyDominates (bimatrix u₁ u₂) 1 b' b ↔
      (∀ a, u₂ a b ≤ u₂ a b') ∧ ∃ a, u₂ a b < u₂ a b' := by
  constructor
  · rintro ⟨h1, r, hr⟩
    exact ⟨fun a => by simpa using h1 (pp a b), r 0, by simpa using hr⟩
  · rintro ⟨h1, a, ha⟩
    exact ⟨fun r => by simpa using h1 (r 0), pp a b, by simpa using ha⟩

/-- A strictly dominant strategy (Definition 8.B.1) for player 1. -/
theorem bimatrix_strictlyDominant_zero_iff (a : Fin m) :
    StrictlyDominant (bimatrix u₁ u₂) 0 a ↔ ∀ a', a' ≠ a → ∀ b, u₁ a' b < u₁ a b := by
  exact (strictlyDominant_iff_dominates (bimatrix u₁ u₂) 0 a).trans
    (forall_congr' fun a' => imp_congr_right fun _ =>
      bimatrix_strictlyDominates_zero_iff u₁ u₂ a a')

/-- A strictly dominant strategy (Definition 8.B.1) for player 2. -/
theorem bimatrix_strictlyDominant_one_iff (b : Fin n) :
    StrictlyDominant (bimatrix u₁ u₂) 1 b ↔ ∀ b', b' ≠ b → ∀ a, u₂ a b' < u₂ a b := by
  exact (strictlyDominant_iff_dominates (bimatrix u₁ u₂) 1 b).trans
    (forall_congr' fun b' => imp_congr_right fun _ =>
      bimatrix_strictlyDominates_one_iff u₁ u₂ b b')

/-- Remaining strategy sets `A` (rows) and `B` (columns). -/
def ps {m n : ℕ} (A : Set (Fin m)) (B : Set (Fin n)) : (i : Fin 2) → Set (S2 m n i) :=
  Fin.cons A (Fin.cons B finZeroElim)

@[simp] theorem ps_zero {m n : ℕ} (A : Set (Fin m)) (B : Set (Fin n)) : ps A B 0 = A := rfl

@[simp] theorem ps_one {m n : ℕ} (A : Set (Fin m)) (B : Set (Fin n)) : ps A B 1 = B := rfl

/-- Strict domination within remaining sets, for player 1. -/
theorem bimatrix_sdominatedIn_zero_iff (A : Set (Fin m)) (B : Set (Fin n)) (a : Fin m) :
    SDominatedIn (bimatrix u₁ u₂) (ps A B) 0 a ↔ ∃ a' ∈ A, ∀ b ∈ B, u₁ a b < u₁ a' b := by
  constructor
  · rintro ⟨a', ha', h⟩
    refine ⟨a', ha', fun b hb => ?_⟩
    have := h (pp a b) fun j hj => by
      fin_cases j
      · exact absurd rfl hj
      · exact hb
    simpa using this
  · rintro ⟨a', ha', h⟩
    refine ⟨a', ha', fun r hr => ?_⟩
    simpa using h (r 1) (hr 1 (by decide))

/-- Strict domination within remaining sets, for player 2. -/
theorem bimatrix_sdominatedIn_one_iff (A : Set (Fin m)) (B : Set (Fin n)) (b : Fin n) :
    SDominatedIn (bimatrix u₁ u₂) (ps A B) 1 b ↔ ∃ b' ∈ B, ∀ a ∈ A, u₂ a b < u₂ a b' := by
  constructor
  · rintro ⟨b', hb', h⟩
    refine ⟨b', hb', fun a ha => ?_⟩
    have := h (pp a b) fun j hj => by
      fin_cases j
      · exact ha
      · exact absurd rfl hj
    simpa using this
  · rintro ⟨b', hb', h⟩
    refine ⟨b', hb', fun r hr => ?_⟩
    simpa using h (r 0) (hr 0 (by decide))

/-- A deletion step in a two-player table. -/
theorem bimatrix_sdStep_iff (A A' : Set (Fin m)) (B B' : Set (Fin n)) :
    SDStep (bimatrix u₁ u₂) (ps A B) (ps A' B') ↔
      (A' ⊆ A ∧ B' ⊆ B) ∧ (∀ a ∈ A, a ∉ A' → ∃ a' ∈ A, ∀ b ∈ B, u₁ a b < u₁ a' b) ∧
        ∀ b ∈ B, b ∉ B' → ∃ b' ∈ B, ∀ a ∈ A, u₂ a b < u₂ a b' := by
  unfold SDStep
  rw [Fin.forall_fin_two, Fin.forall_fin_two]
  exact and_congr Iff.rfl (and_congr
    (forall₂_congr fun a _ => imp_congr_right fun _ => bimatrix_sdominatedIn_zero_iff u₁ u₂ A B a)
    (forall₂_congr fun b _ => imp_congr_right fun _ => bimatrix_sdominatedIn_one_iff u₁ u₂ A B b))

/-- Completeness of a deletion process in a two-player table. -/
theorem bimatrix_sdTerminal_iff (A : Set (Fin m)) (B : Set (Fin n)) :
    SDTerminal (bimatrix u₁ u₂) (ps A B) ↔
      (∀ a ∈ A, ¬ ∃ a' ∈ A, ∀ b ∈ B, u₁ a b < u₁ a' b) ∧
        ∀ b ∈ B, ¬ ∃ b' ∈ B, ∀ a ∈ A, u₂ a b < u₂ a b' := by
  unfold SDTerminal
  rw [Fin.forall_fin_two]
  exact and_congr
    (forall₂_congr fun a _ => not_congr (bimatrix_sdominatedIn_zero_iff u₁ u₂ A B a))
    (forall₂_congr fun b _ => not_congr (bimatrix_sdominatedIn_one_iff u₁ u₂ A B b))

theorem fullSets_eq_ps : fullSets (S2 m n) = ps Set.univ Set.univ := by
  funext i
  fin_cases i <;> rfl

omit u₁ u₂ in
/-- **Section 7.E/8.D** for two players: `u_k(σ) = ∑_{a,b} σ₁(a) σ₂(b) u_k(a, b)`. -/
theorem mixedPayoff_fin_two {S : Fin 2 → Type*} [∀ i, Fintype (S i)] (N : NormalForm (Fin 2) S)
    (σ : (i : Fin 2) → S i → ℝ) (k : Fin 2) :
    N.mixedPayoff σ k = ∑ a : S 0, ∑ b : S 1, σ 0 a * σ 1 b *
      N.payoff k (Fin.cons a (Fin.cons b finZeroElim)) := by
  unfold NormalForm.mixedPayoff
  rw [← (piFinTwoEquiv S).symm.sum_comp, Fintype.sum_prod_type]
  simp [Fin.prod_univ_two, piFinTwoEquiv]

/-- Mixed payoffs in a two-player table. -/
theorem bimatrix_mixedPayoff (σ : (i : Fin 2) → S2 m n i → ℝ) :
    (bimatrix u₁ u₂).mixedPayoff σ 0 = ∑ a : Fin m, ∑ b : Fin n, σ 0 a * σ 1 b * u₁ a b ∧
      (bimatrix u₁ u₂).mixedPayoff σ 1 = ∑ a : Fin m, ∑ b : Fin n, σ 0 a * σ 1 b * u₂ a b := by
  rw [mixedPayoff_fin_two, mixedPayoff_fin_two]
  exact ⟨rfl, rfl⟩

/-- Player 1's payoff from row `a` against player 2's mixed strategy. -/
theorem bimatrix_mixedPayoff_row (σ : (i : Fin 2) → S2 m n i → ℝ) (a : Fin m) :
    (bimatrix u₁ u₂).mixedPayoff (update σ 0 (pureMixed a)) 0 = ∑ b : Fin n, σ 1 b * u₁ a b := by
  rw [(bimatrix_mixedPayoff u₁ u₂ _).1]
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  have hrow : (update σ 0 (pureMixed a) : (i : Fin 2) → S2 m n i → ℝ) 0 =
      fun a' : Fin m => if a' = a then (1 : ℝ) else 0 := by
    rw [update_self]; rfl
  rw [hrow, update_of_ne h10]
  simp [ite_mul]

/-- Player 2's payoff from column `b` against player 1's mixed strategy. -/
theorem bimatrix_mixedPayoff_col (σ : (i : Fin 2) → S2 m n i → ℝ) (b : Fin n) :
    (bimatrix u₁ u₂).mixedPayoff (update σ 1 (pureMixed b)) 1 = ∑ a : Fin m, σ 0 a * u₂ a b := by
  rw [(bimatrix_mixedPayoff u₁ u₂ _).2]
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have hcol : (update σ 1 (pureMixed b) : (i : Fin 2) → S2 m n i → ℝ) 1 =
      fun b' : Fin n => if b' = b then (1 : ℝ) else 0 := by
    rw [update_self]; rfl
  rw [hcol, update_of_ne h01]
  simp [ite_mul, mul_ite]

/-- A profile of mixed strategies in a two-player table from the two players' vectors. -/
def mp {m n : ℕ} (x : Fin m → ℝ) (y : Fin n → ℝ) : (i : Fin 2) → S2 m n i → ℝ :=
  Fin.cons x (Fin.cons y finZeroElim)

@[simp] theorem mp_zero {m n : ℕ} (x : Fin m → ℝ) (y : Fin n → ℝ) : mp x y 0 = x := rfl

@[simp] theorem mp_one {m n : ℕ} (x : Fin m → ℝ) (y : Fin n → ℝ) : mp x y 1 = y := rfl

theorem isMixedProfile_mp {x : Fin m → ℝ} {y : Fin n → ℝ} (hx : IsMixedStrategy x)
    (hy : IsMixedStrategy y) : IsMixedProfile (mp x y) := by
  intro i
  fin_cases i
  · exact hx
  · exact hy

/-- Mixed Nash equilibrium (Definition 8.D.2) in a two-player table: no profitable pure
deviation. -/
theorem bimatrix_isMixedNash_iff {x : Fin m → ℝ} {y : Fin n → ℝ} (hx : IsMixedStrategy x)
    (hy : IsMixedStrategy y) :
    IsMixedNash (bimatrix u₁ u₂) (mp x y) ↔
      (∀ a', ∑ b, y b * u₁ a' b ≤ ∑ a, ∑ b, x a * y b * u₁ a b) ∧
      ∀ b', ∑ a, x a * u₂ a b' ≤ ∑ a, ∑ b, x a * y b * u₂ a b := by
  rw [isMixedNash_iff_pure_deviations _ (isMixedProfile_mp hx hy)]
  constructor
  · intro h
    refine ⟨fun a' => ?_, fun b' => ?_⟩
    · have := h 0 a'
      rwa [bimatrix_mixedPayoff_row, (bimatrix_mixedPayoff u₁ u₂ _).1] at this
    · have := h 1 b'
      rwa [bimatrix_mixedPayoff_col, (bimatrix_mixedPayoff u₁ u₂ _).2] at this
  · rintro ⟨h1, h2⟩
    rw [Fin.forall_fin_two]
    refine ⟨fun a => ?_, fun b => ?_⟩
    · exact (bimatrix_mixedPayoff_row u₁ u₂ (mp x y) a).trans_le
        ((h1 a).trans_eq (bimatrix_mixedPayoff u₁ u₂ (mp x y)).1.symm)
    · exact (bimatrix_mixedPayoff_col u₁ u₂ (mp x y) b).trans_le
        ((h2 b).trans_eq (bimatrix_mixedPayoff u₁ u₂ (mp x y)).2.symm)

/-- Player 1's mixed strategy `τ` against player 2's pure strategy `b`. -/
theorem bimatrix_mixed_vs_pure_zero (τ : S2 m n 0 → ℝ) (s : (i : Fin 2) → S2 m n i) :
    (bimatrix u₁ u₂).mixedPayoff (update (pureProfile s) 0 τ) 0 =
      ∑ a : Fin m, τ a * u₁ a (s 1) := by
  rw [mixedPayoff_pureProfile_update_mixed]
  exact Finset.sum_congr rfl fun a _ => by simp [bimatrix, Function.update]

/-- Player 2's mixed strategy `τ` against player 1's pure strategy `a`. -/
theorem bimatrix_mixed_vs_pure_one (τ : S2 m n 1 → ℝ) (s : (i : Fin 2) → S2 m n i) :
    (bimatrix u₁ u₂).mixedPayoff (update (pureProfile s) 1 τ) 1 =
      ∑ b : Fin n, τ b * u₂ (s 0) b := by
  rw [mixedPayoff_pureProfile_update_mixed]
  exact Finset.sum_congr rfl fun b _ => by simp [bimatrix, Function.update]

/-- Strict domination of mixed strategies (Definition 8.B.4) for player 1, tested against the
columns. -/
theorem bimatrix_mixedStrictlyDominates_zero_iff [NeZero m] (τ' τ : Fin m → ℝ) :
    MixedStrictlyDominates (bimatrix u₁ u₂) 0 τ' τ ↔
      ∀ b, ∑ a, τ a * u₁ a b < ∑ a, τ' a * u₁ a b := by
  refine (mixedStrictlyDominates_iff_pure _ _ _ _).trans ⟨fun h b => ?_, fun h s => ?_⟩
  · have h1 := h (pp (0 : Fin m) b)
    have e1 := bimatrix_mixed_vs_pure_zero u₁ u₂ τ (pp (0 : Fin m) b)
    have e2 := bimatrix_mixed_vs_pure_zero u₁ u₂ τ' (pp (0 : Fin m) b)
    simp only [pp_one] at e1 e2
    linarith
  · have e1 := bimatrix_mixed_vs_pure_zero u₁ u₂ τ s
    have e2 := bimatrix_mixed_vs_pure_zero u₁ u₂ τ' s
    have := h (s 1)
    linarith

/-- Strict domination of mixed strategies (Definition 8.B.4) for player 2, tested against the
rows. -/
theorem bimatrix_mixedStrictlyDominates_one_iff [NeZero n] (τ' τ : Fin n → ℝ) :
    MixedStrictlyDominates (bimatrix u₁ u₂) 1 τ' τ ↔
      ∀ a, ∑ b, τ b * u₂ a b < ∑ b, τ' b * u₂ a b := by
  refine (mixedStrictlyDominates_iff_pure _ _ _ _).trans ⟨fun h a => ?_, fun h s => ?_⟩
  · have h1 := h (pp a (0 : Fin n))
    have e1 := bimatrix_mixed_vs_pure_one u₁ u₂ τ (pp a (0 : Fin n))
    have e2 := bimatrix_mixed_vs_pure_one u₁ u₂ τ' (pp a (0 : Fin n))
    simp only [pp_zero] at e1 e2
    linarith
  · have e1 := bimatrix_mixed_vs_pure_one u₁ u₂ τ s
    have e2 := bimatrix_mixed_vs_pure_one u₁ u₂ τ' s
    have := h (s 0)
    linarith

/-- A row is a best response (Definition 8.C.1) to player 2's mixed strategy if no row does
better against it. -/
theorem bimatrix_isBestResponse_row (σ : (i : Fin 2) → S2 m n i → ℝ) (a : Fin m)
    (h : ∀ a', ∑ b : Fin n, σ 1 b * u₁ a' b ≤ ∑ b : Fin n, σ 1 b * u₁ a b) :
    IsBestResponse (bimatrix u₁ u₂) 0 (pureMixed a) σ := by
  refine isBestResponse_pureMixed_of_max _ 0 σ fun a' => ?_
  have e1 := bimatrix_mixedPayoff_row u₁ u₂ σ a
  have e2 := bimatrix_mixedPayoff_row u₁ u₂ σ a'
  have := h a'
  linarith

/-- A column is a best response (Definition 8.C.1) to player 1's mixed strategy if no column does
better against it. -/
theorem bimatrix_isBestResponse_col (σ : (i : Fin 2) → S2 m n i → ℝ) (b : Fin n)
    (h : ∀ b', ∑ a : Fin m, σ 0 a * u₂ a b' ≤ ∑ a : Fin m, σ 0 a * u₂ a b) :
    IsBestResponse (bimatrix u₁ u₂) 1 (pureMixed b) σ := by
  refine isBestResponse_pureMixed_of_max _ 1 σ fun b' => ?_
  have e1 := bimatrix_mixedPayoff_col u₁ u₂ σ b
  have e2 := bimatrix_mixedPayoff_col u₁ u₂ σ b'
  have := h b'
  linarith

/-- A mixed Nash equilibrium of a two-player table (Proposition 8.D.1): every row played with
positive probability is a best row against `y`, and every column played with positive probability
is a best column against `x`. -/
theorem bimatrix_isMixedNash_support {x : Fin m → ℝ} {y : Fin n → ℝ} (hx : IsMixedStrategy x)
    (hy : IsMixedStrategy y) :
    IsMixedNash (bimatrix u₁ u₂) (mp x y) ↔
      (∀ a, 0 < x a → ∀ a', ∑ b, y b * u₁ a' b ≤ ∑ b, y b * u₁ a b) ∧
      ∀ b, 0 < y b → ∀ b', ∑ a, x a * u₂ a b' ≤ ∑ a, x a * u₂ a b := by
  rw [isMixedNash_iff_bestResponse]
  simp only [isMixedProfile_mp hx hy, true_and]
  rw [Fin.forall_fin_two]
  refine and_congr ?_ ?_
  · refine (isBestResponse_iff_support _ 0 hx (mp x y)).trans (forall_congr' fun a =>
      imp_congr_right fun _ => forall_congr' fun a' => ?_)
    have e1 := bimatrix_mixedPayoff_row u₁ u₂ (mp x y) a
    have e2 := bimatrix_mixedPayoff_row u₁ u₂ (mp x y) a'
    constructor <;> intro h <;> simp only [mp_one] at e1 e2 <;> linarith
  · refine (isBestResponse_iff_support _ 1 hy (mp x y)).trans (forall_congr' fun b =>
      imp_congr_right fun _ => forall_congr' fun b' => ?_)
    have e1 := bimatrix_mixedPayoff_col u₁ u₂ (mp x y) b
    have e2 := bimatrix_mixedPayoff_col u₁ u₂ (mp x y) b'
    constructor <;> intro h <;> simp only [mp_zero] at e1 e2 <;> linarith

omit u₁ u₂ in
/-- Payoff of a row against a pure column, as a sum. -/
theorem sum_pureMixed_mul {k : ℕ} (b₀ : Fin k) (f : Fin k → ℝ) :
    ∑ b, pureMixed b₀ b * f b = f b₀ := by
  simp [pureMixed]

/-- Every mixed profile of a two-player table is `mp (σ 0) (σ 1)`. -/
theorem eq_mp (σ : (i : Fin 2) → S2 m n i → ℝ) : σ = mp (σ 0) (σ 1) := by
  funext i
  fin_cases i <;> rfl

end MWG.SimultaneousMoveGames
