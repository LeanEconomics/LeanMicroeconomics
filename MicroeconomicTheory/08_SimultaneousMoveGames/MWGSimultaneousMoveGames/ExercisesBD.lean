/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGSimultaneousMoveGames.Zigger
import Mathlib.Analysis.Convex.Jensen

/-!
# Exercises 8.B.1, 8.B.2, 8.D.6, 8.D.7 and 8.D.8

MWG, pp. 262-264.

* **Exercise 8.B.1** (lobbying): with payoff `α ∑ h_j + β ∏ h_j - w_i h_i²` and efforts `h_i ≥ 0`,
  each firm's strictly dominant strategy when `β = 0` is `h_i = max(α, 0) / (2 w_i)`
  (`exercise_8_B_1_dominant`); with `α > 0` and at least two firms, a strictly dominant strategy
  exists only if `β = 0` (`exercise_8_B_1_only_if`). The printed "only if" fails with one firm
  (`exercise_8_B_1_one_firm`) and when `α ≤ 0 > β` (`exercise_8_B_1_nonpositive`) (correction 5).
* **Exercise 8.B.2**: under Definition 8.B.3 a player has at most one weakly dominant strategy
  (`weaklyDominant_unique`), so (a) holds vacuously and (b) has no example; with the weaker
  notion "at least as good as every other strategy" (`AtLeastAsGoodAsAll`) two such strategies
  give equal payoffs (`exercise_8_B_2a`) and the opponent may prefer one of them
  (`exercise_8_B_2b`) (correction 6).
* **Exercise 8.D.6**: every `2 × 2` game has a mixed strategy Nash equilibrium.
* **Exercise 8.D.7** (the minimax theorem): `v_i ≥ w_i` in any game; in a zero-sum game every Nash
  equilibrium gives `u_i* = v_i = w_i`; equilibria are interchangeable.
* **Exercise 8.D.8**: as printed (strictly quasiconvex payoffs) the claim is false
  (`exercise_8_D_8_counterexample`); with payoffs strictly concave in the player's own strategy
  a best-response finite mixture is degenerate (`exercise_8_D_8`) (correction 7).
-/

namespace MWG.SimultaneousMoveGames

open MWG.NoncooperativeGames Function Finset

/-! ### Exercise 8.B.1 -/

/-- Nonnegative effort levels `h ≥ 0`. -/
abbrev Effort := {h : ℝ // 0 ≤ h}

/-- **Exercise 8.B.1** (MWG, p. 262). The lobbying game: firm `i` chooses hours `h_i ≥ 0`, and its
payoff is the subsidy `α ∑_j h_j + β ∏_j h_j` minus its cost `w_i h_i²`. -/
def lobbyGame {I : Type*} [Fintype I] (α β : ℝ) (w : I → ℝ) : NormalForm I (fun _ => Effort) where
  payoff i h := α * ∑ j, (h j : ℝ) + β * ∏ j, (h j : ℝ) - w i * (h i : ℝ) ^ 2

/-- The maximizer of `A y - w y²` over `y ≥ 0`. -/
theorem quad_max {A w y : ℝ} (hw : 0 < w) (hy : 0 ≤ y) :
    A * y - w * y ^ 2 ≤ A * (max A 0 / (2 * w)) - w * (max A 0 / (2 * w)) ^ 2 ∧
      (y ≠ max A 0 / (2 * w) →
        A * y - w * y ^ 2 < A * (max A 0 / (2 * w)) - w * (max A 0 / (2 * w)) ^ 2) := by
  rcases le_total 0 A with hA | hA
  · rw [max_eq_left hA]
    have key : A * (A / (2 * w)) - w * (A / (2 * w)) ^ 2 - (A * y - w * y ^ 2) =
        w * (y - A / (2 * w)) ^ 2 := by field_simp; ring
    refine ⟨by nlinarith [sq_nonneg (y - A / (2 * w))], fun hne => ?_⟩
    have : 0 < (y - A / (2 * w)) ^ 2 := by positivity
    nlinarith
  · rw [max_eq_right hA]
    simp only [zero_div, mul_zero, ne_eq, sq, sub_zero]
    have h1 : y * A ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hy hA
    refine ⟨by nlinarith [mul_nonneg hw.le (mul_nonneg hy hy)], fun hne => ?_⟩
    have : 0 < y := lt_of_le_of_ne hy (Ne.symm hne)
    have h2 : 0 < w * (y * y) := by positivity
    linarith [mul_comm A y]

/-- The payoff of firm `i` after it changes its effort to `y`. -/
theorem lobbyGame_update {I : Type*} [Fintype I] [DecidableEq I] (α β : ℝ) (w : I → ℝ)
    (r : I → Effort) (i : I) (y : Effort) :
    (lobbyGame α β w).payoff i (update r i y) =
      (α + β * ∏ j ∈ univ.erase i, (r j : ℝ)) * y - w i * (y : ℝ) ^ 2 +
        α * ∑ j ∈ univ.erase i, (r j : ℝ) := by
  have hs : ∑ j, ((update r i y j : Effort) : ℝ) = y + ∑ j ∈ univ.erase i, (r j : ℝ) := by
    rw [← Finset.add_sum_erase _ _ (mem_univ i), update_self]
    congr 1
    exact Finset.sum_congr rfl fun j hj => by rw [update_of_ne (ne_of_mem_erase hj)]
  have hp : ∏ j, ((update r i y j : Effort) : ℝ) = y * ∏ j ∈ univ.erase i, (r j : ℝ) := by
    rw [← Finset.mul_prod_erase _ _ (mem_univ i), update_self]
    congr 1
    exact Finset.prod_congr rfl fun j hj => by rw [update_of_ne (ne_of_mem_erase hj)]
  simp only [lobbyGame, hs, hp, update_self]
  ring

/-- **Exercise 8.B.1** (MWG, p. 262). If `β = 0`, firm `i`'s strictly dominant strategy is
`h_i = max(α, 0) / (2 w_i)` (`α / (2 w_i)` when `α > 0`). -/
theorem exercise_8_B_1_dominant {I : Type*} [Fintype I] [DecidableEq I] (α : ℝ) (w : I → ℝ)
    (hw : ∀ i, 0 < w i) (i : I) :
    StrictlyDominant (lobbyGame α 0 w) i
      ⟨max α 0 / (2 * w i), div_nonneg (le_max_right _ _) (by linarith [hw i])⟩ := by
  intro y hy r
  rw [lobbyGame_update, lobbyGame_update]
  simp only [zero_mul, add_zero]
  have hne : (y : ℝ) ≠ max α 0 / (2 * w i) := fun h => hy (Subtype.ext h)
  have := (quad_max (A := α) (hw i) y.2).2 hne
  linarith

/-- If `x` is strictly dominant for firm `i` and `y` maximizes firm `i`'s payoff against the
rivals' profile `r`, then `x = y`. -/
theorem eq_of_strictlyDominant_of_max {I : Type*} [DecidableEq I] {S : I → Type*}
    {N : NormalForm I S} {i : I} {x : S i} (hx : StrictlyDominant N i x) (r : (j : I) → S j)
    {y : S i} (hy : ∀ z, N.payoff i (update r i z) ≤ N.payoff i (update r i y)) : x = y := by
  by_contra hne
  exact absurd (hy x) (not_le.2 (hx y (Ne.symm hne) r))

/-- **Exercise 8.B.1** (MWG, p. 262). With `α > 0` and at least two firms, if firm `i` has a
strictly dominant strategy then `β = 0`. -/
theorem exercise_8_B_1_only_if {I : Type*} [Fintype I] [DecidableEq I] (α β : ℝ) (w : I → ℝ)
    (hw : ∀ i, 0 < w i) (hα : 0 < α) (i j : I) (hij : j ≠ i) {x : Effort}
    (hx : StrictlyDominant (lobbyGame α β w) i x) : β = 0 := by
  by_contra hβ
  have hwi := hw i
  -- the best reply when the rivals choose `0`, and when they choose `1`
  have hbest : ∀ (r : I → Effort), ∀ z : Effort,
      (lobbyGame α β w).payoff i (update r i z) ≤ (lobbyGame α β w).payoff i (update r i
        ⟨max (α + β * ∏ j ∈ univ.erase i, (r j : ℝ)) 0 / (2 * w i),
          div_nonneg (le_max_right _ _) (by linarith)⟩) := by
    intro r z
    rw [lobbyGame_update, lobbyGame_update]
    have := (quad_max (A := α + β * ∏ j ∈ univ.erase i, (r j : ℝ)) hwi z.2).1
    linarith
  have h0 := congrArg Subtype.val (eq_of_strictlyDominant_of_max hx _ (hbest fun _ => ⟨0, le_rfl⟩))
  have h1 := congrArg Subtype.val
    (eq_of_strictlyDominant_of_max hx _ (hbest fun _ => ⟨1, zero_le_one⟩))
  have hz : ∏ j ∈ univ.erase i, ((⟨0, le_rfl⟩ : Effort) : ℝ) = 0 :=
    Finset.prod_eq_zero (mem_erase.2 ⟨hij, mem_univ j⟩) rfl
  have ho : ∏ j ∈ univ.erase i, ((⟨1, zero_le_one⟩ : Effort) : ℝ) = 1 := by simp
  simp only [hz, ho, mul_zero, add_zero, mul_one] at h0 h1
  rw [h0, max_eq_left hα.le] at h1
  have h2 : α = max (α + β) 0 := by
    field_simp at h1
    linarith
  rcases le_total (α + β) 0 with h | h
  · rw [max_eq_right h] at h2; linarith
  · rw [max_eq_left h] at h2; exact hβ (by linarith)

/-- **Exercise 8.B.1 needs two firms** (correction 5). With a single firm `β ≠ 0` does not prevent a
strictly dominant strategy: the payoff `(α + β) h - w h²` has the unique maximizer
`max(α + β, 0) / (2w)` whatever (the empty) rivals do. -/
theorem exercise_8_B_1_one_firm (α β w : ℝ) (hw : 0 < w) :
    StrictlyDominant (lobbyGame (I := Unit) α β fun _ => w) ()
      ⟨max (α + β) 0 / (2 * w), div_nonneg (le_max_right _ _) (by linarith)⟩ := by
  intro y hy r
  rw [lobbyGame_update, lobbyGame_update]
  simp only [Finset.univ_unique, Finset.erase_singleton, Finset.prod_empty, mul_one,
    Finset.sum_empty, mul_zero, add_zero]
  have hne : (y : ℝ) ≠ max (α + β) 0 / (2 * w) := fun h => hy (Subtype.ext h)
  have := (quad_max (A := α + β) hw y.2).2 hne
  linarith

/-- **Exercise 8.B.1 with `α ≤ 0` and `β < 0`** (correction 5). Then `h_i = 0` is strictly dominant
for every firm although `β ≠ 0`. -/
theorem exercise_8_B_1_nonpositive {I : Type*} [Fintype I] [DecidableEq I] (α β : ℝ)
    (w : I → ℝ) (hw : ∀ i, 0 < w i) (hα : α ≤ 0) (hβ : β < 0) (i : I) :
    StrictlyDominant (lobbyGame α β w) i ⟨0, le_rfl⟩ := by
  intro y hy r
  rw [lobbyGame_update, lobbyGame_update]
  have hP : 0 ≤ ∏ j ∈ univ.erase i, (r j : ℝ) := Finset.prod_nonneg fun j _ => (r j).2
  have hy0 : 0 < (y : ℝ) := lt_of_le_of_ne y.2 fun h => hy (Subtype.ext h.symm)
  have hA : α + β * ∏ j ∈ univ.erase i, (r j : ℝ) ≤ 0 := by nlinarith
  have := hw i
  have h1 := mul_le_mul_of_nonneg_right hA hy0.le
  have h2 : 0 < w i * (y : ℝ) ^ 2 := by positivity
  simp only [zero_mul, mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    sub_zero, zero_add] at h1 ⊢
  linarith

/-! ### Exercise 8.B.2 -/

/-- **Exercise 8.B.2 under Definition 8.B.3** (correction 6). A player has at most one weakly
dominant strategy: two would have to weakly dominate each other, which requires a strict
inequality in both directions. -/
theorem weaklyDominant_unique {I : Type*} {S : I → Type*} [DecidableEq I] {N : NormalForm I S}
    {i : I} {s s' : S i} (h : WeaklyDominant N i s) (h' : WeaklyDominant N i s') : s = s' := by
  by_contra hne
  obtain ⟨-, r, hr⟩ := h s' (Ne.symm hne)
  have := (h' s hne).1 r
  linarith

/-- The weaker notion: `s_i` does at least as well as every other strategy against every
`s_{-i}`. -/
def AtLeastAsGoodAsAll {I : Type*} {S : I → Type*} [DecidableEq I] (N : NormalForm I S) (i : I)
    (s : S i) : Prop :=
  ∀ s' (r : (j : I) → S j), N.payoff i (update r i s') ≤ N.payoff i (update r i s)

/-- **Exercise 8.B.2(a)** (MWG, p. 262), for the weaker notion: if two strategies are each at least
as good as every other, they yield equal payoffs against every strategy choice of the
opponents. -/
theorem exercise_8_B_2a {I : Type*} {S : I → Type*} [DecidableEq I] {N : NormalForm I S}
    {i : I} {s s' : S i} (h : AtLeastAsGoodAsAll N i s) (h' : AtLeastAsGoodAsAll N i s')
    (r : (j : I) → S j) : N.payoff i (update r i s) = N.payoff i (update r i s') :=
  le_antisymm (h' s r) (h s' r)

/-- **Exercise 8.B.2(b)** (MWG, p. 262), for the weaker notion: in the `2 × 2` game below both rows
are at least as good as every other row for player 1, but player 2 strictly prefers that player 1
play the first. -/
theorem exercise_8_B_2b :
    let u₁ : Fin 2 → Fin 2 → ℝ := fun _ _ => 1
    let u₂ : Fin 2 → Fin 2 → ℝ := ![![1, 1], ![0, 0]]
    AtLeastAsGoodAsAll (bimatrix u₁ u₂) 0 (0 : Fin 2) ∧
      AtLeastAsGoodAsAll (bimatrix u₁ u₂) 0 (1 : Fin 2) ∧ ∀ b : Fin 2, u₂ 1 b < u₂ 0 b := by
  intro u₁ u₂
  refine ⟨fun s' r => by simp [u₁], fun s' r => by simp [u₁], fun b => ?_⟩
  fin_cases b <;> simp [u₂]

/-! ### Exercise 8.D.6 -/

/-- **Exercise 8.D.6** (MWG, p. 264). Every two-player game with two strategies for each player has
a mixed strategy Nash equilibrium. -/
theorem exercise_8_D_6 (u₁ u₂ : Fin 2 → Fin 2 → ℝ) :
    ∃ x y : Fin 2 → ℝ, IsMixedStrategy x ∧ IsMixedStrategy y ∧
      IsMixedNash (bimatrix u₁ u₂) (mp x y) := by
  have hne : ∀ i, Nonempty (S2 2 2 i) := fun i => by fin_cases i <;> exact ⟨(0 : Fin 2)⟩
  obtain ⟨σ, hσ⟩ := proposition_8_D_2 (bimatrix u₁ u₂)
  exact ⟨σ 0, σ 1, hσ.1 0, hσ.1 1, Eq.mp (congrArg (IsMixedNash (bimatrix u₁ u₂)) (eq_mp σ)) hσ⟩

/-- **Exercise 8.D.6** (MWG, p. 264), the hint's parametrization: a mixed strategy over two pure
strategies is given by the probability `p ∈ [0, 1]` of the first. -/
theorem exercise_8_D_6_param (x : Fin 2 → ℝ) :
    IsMixedStrategy x ↔ ∃ p ∈ Set.Icc (0 : ℝ) 1, x = ![p, 1 - p] := by
  constructor
  · rintro ⟨h0, h1⟩
    rw [Fin.sum_univ_two] at h1
    refine ⟨x 0, ⟨h0 0, by linarith [h0 1]⟩, funext fun a => ?_⟩
    fin_cases a
    · rfl
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      linarith
  · rintro ⟨p, ⟨h0, h1⟩, rfl⟩
    refine ⟨fun a => ?_, by simp [Fin.sum_univ_two]⟩
    fin_cases a <;> simp <;> linarith

/-! ### Exercise 8.D.7: the minimax theorem -/

/-- `⨆ x ⨅ y f(x, y) ≤ ⨅ y ⨆ x f(x, y)` for a bounded function on nonempty sets. -/
theorem iSup_iInf_le_iInf_iSup_of_bdd {X Y : Type*} [Nonempty X] [Nonempty Y] (f : X → Y → ℝ)
    {B : ℝ} (hB : ∀ x y, |f x y| ≤ B) : ⨆ x, ⨅ y, f x y ≤ ⨅ y, ⨆ x, f x y := by
  have hbb : ∀ x, BddBelow (Set.range fun y => f x y) :=
    fun x => ⟨-B, by rintro _ ⟨y, rfl⟩; linarith [(abs_le.1 (hB x y)).1]⟩
  have hba : ∀ y, BddAbove (Set.range fun x => f x y) :=
    fun y => ⟨B, by rintro _ ⟨x, rfl⟩; linarith [(abs_le.1 (hB x y)).2]⟩
  refine ciSup_le fun x => le_ciInf fun y => ?_
  exact (ciInf_le (hbb x) y).trans (le_ciSup (hba y) x)

variable {S : Fin 2 → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

/-- A two-player mixed profile from the players' mixed strategies. -/
def mprof (x : S 0 → ℝ) (y : S 1 → ℝ) : (i : Fin 2) → S i → ℝ :=
  Fin.cons x (Fin.cons y finZeroElim)

/-- Player 1's mixed strategies. -/
abbrev Δ₁ (S : Fin 2 → Type*) [∀ i, Fintype (S i)] := {x : S 0 → ℝ // IsMixedStrategy x}

/-- Player 2's mixed strategies. -/
abbrev Δ₂ (S : Fin 2 → Type*) [∀ i, Fintype (S i)] := {y : S 1 → ℝ // IsMixedStrategy y}

/-- Player `k`'s payoff from the mixed profile `(x, y)`. -/
def pay2 (N : NormalForm (Fin 2) S) (k : Fin 2) (x : Δ₁ S) (y : Δ₂ S) : ℝ :=
  N.mixedPayoff (mprof x.1 y.1) k

omit [∀ i, DecidableEq (S i)] in
theorem isMixedProfile_mprof (x : Δ₁ S) (y : Δ₂ S) : IsMixedProfile (mprof x.1 y.1) := by
  intro i
  fin_cases i
  · exact x.2
  · exact y.2

omit [∀ i, DecidableEq (S i)] in
theorem abs_pay2_le (N : NormalForm (Fin 2) S) (k : Fin 2) (x : Δ₁ S) (y : Δ₂ S) :
    |pay2 N k x y| ≤ ∑ s, |N.payoff k s| :=
  abs_mixedPayoff_le N (isMixedProfile_mprof x y) k

/-- **Exercise 8.D.7** (MWG, p. 264). Player `i`'s maximin level `w_i = max_{σ_i} min_{σ_{-i}}
u_i(σ_i, σ_{-i})`, for player 1. -/
noncomputable def maximin₁ (N : NormalForm (Fin 2) S) : ℝ := ⨆ x : Δ₁ S, ⨅ y : Δ₂ S, pay2 N 0 x y

/-- Player 1's minimax level `v_1 = min_{σ_2} max_{σ_1} u_1(σ_1, σ_2)`. -/
noncomputable def minimax₁ (N : NormalForm (Fin 2) S) : ℝ := ⨅ y : Δ₂ S, ⨆ x : Δ₁ S, pay2 N 0 x y

/-- Player 2's maximin level `w_2 = max_{σ_2} min_{σ_1} u_2(σ_1, σ_2)`. -/
noncomputable def maximin₂ (N : NormalForm (Fin 2) S) : ℝ := ⨆ y : Δ₂ S, ⨅ x : Δ₁ S, pay2 N 1 x y

/-- Player 2's minimax level `v_2 = min_{σ_1} max_{σ_2} u_2(σ_1, σ_2)`. -/
noncomputable def minimax₂ (N : NormalForm (Fin 2) S) : ℝ := ⨅ x : Δ₁ S, ⨆ y : Δ₂ S, pay2 N 1 x y

omit [∀ i, DecidableEq (S i)] in
/-- **Exercise 8.D.7(a)** (MWG, p. 264). `v_i ≥ w_i` in any (finite, two-player) game. -/
theorem exercise_8_D_7a [∀ i, Nonempty (S i)] (N : NormalForm (Fin 2) S) :
    maximin₁ N ≤ minimax₁ N ∧ maximin₂ N ≤ minimax₂ N := by
  have h1 : Nonempty (Δ₁ S) := ⟨⟨_, isMixedStrategy_uniformMixed (S 0)⟩⟩
  have h2 : Nonempty (Δ₂ S) := ⟨⟨_, isMixedStrategy_uniformMixed (S 1)⟩⟩
  exact ⟨iSup_iInf_le_iInf_iSup_of_bdd (pay2 N 0) (abs_pay2_le N 0),
    iSup_iInf_le_iInf_iSup_of_bdd (fun y x => pay2 N 1 x y) (fun y x => abs_pay2_le N 1 x y)⟩

/-- A two-player game is zero-sum: `u_2(s) = -u_1(s)`. -/
def IsZeroSum2 (N : NormalForm (Fin 2) S) : Prop := ∀ s, N.payoff 1 s = -N.payoff 0 s

omit [∀ i, DecidableEq (S i)] in
theorem pay2_zeroSum {N : NormalForm (Fin 2) S} (hz : IsZeroSum2 N) (x : Δ₁ S) (y : Δ₂ S) :
    pay2 N 1 x y = -pay2 N 0 x y := by
  simp only [pay2, NormalForm.mixedPayoff]
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun s _ => by rw [hz s]; ring

omit [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] in
theorem update_mprof_zero (x x' : S 0 → ℝ) (y : S 1 → ℝ) :
    update (mprof x y) 0 x' = mprof x' y := by
  funext i
  fin_cases i <;> rfl

omit [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] in
theorem update_mprof_one (x : S 0 → ℝ) (y y' : S 1 → ℝ) :
    update (mprof x y) 1 y' = mprof x y' := by
  funext i
  fin_cases i <;> rfl

omit [∀ i, DecidableEq (S i)] in
/-- A mixed Nash equilibrium `(x*, y*)` of a two-player game in terms of `pay2`. -/
theorem isMixedNash_mprof_iff (N : NormalForm (Fin 2) S) (x : Δ₁ S) (y : Δ₂ S) :
    IsMixedNash N (mprof x.1 y.1) ↔
      (∀ x' : Δ₁ S, pay2 N 0 x' y ≤ pay2 N 0 x y) ∧ ∀ y' : Δ₂ S, pay2 N 1 x y' ≤ pay2 N 1 x y := by
  classical
  constructor
  · rintro ⟨-, h⟩
    refine ⟨fun x' => ?_, fun y' => ?_⟩
    · have := h 0 x'.1 x'.2
      rwa [update_mprof_zero] at this
    · have := h 1 y'.1 y'.2
      rwa [update_mprof_one] at this
  · rintro ⟨h1, h2⟩
    refine ⟨isMixedProfile_mprof x y, fun i τ hτ => ?_⟩
    fin_cases i
    · have := h1 ⟨τ, hτ⟩
      simp only [pay2] at this
      rwa [← update_mprof_zero x.1 τ y.1] at this
    · have := h2 ⟨τ, hτ⟩
      simp only [pay2] at this
      rwa [← update_mprof_one x.1 y.1 τ] at this

omit [∀ i, DecidableEq (S i)] in
/-- **Exercise 8.D.7(b)** (MWG, p. 264). In any mixed strategy Nash equilibrium `(x*, y*)` of a
zero-sum game, each player's expected utility equals his minimax and his maximin levels:
`u_i* = v_i = w_i`. -/
theorem exercise_8_D_7b [∀ i, Nonempty (S i)] {N : NormalForm (Fin 2) S} (hz : IsZeroSum2 N)
    (x : Δ₁ S) (y : Δ₂ S) (h : IsMixedNash N (mprof x.1 y.1)) :
    pay2 N 0 x y = minimax₁ N ∧ pay2 N 0 x y = maximin₁ N ∧
      pay2 N 1 x y = minimax₂ N ∧ pay2 N 1 x y = maximin₂ N := by
  classical
  obtain ⟨h1, h2⟩ := (isMixedNash_mprof_iff N x y).1 h
  have hn1 : Nonempty (Δ₁ S) := ⟨x⟩
  have hn2 : Nonempty (Δ₂ S) := ⟨y⟩
  have hab := exercise_8_D_7a N
  set B0 := ∑ s, |N.payoff 0 s|
  set B1 := ∑ s, |N.payoff 1 s|
  have hbb : ∀ (k : Fin 2) (x' : Δ₁ S), BddBelow (Set.range fun y' : Δ₂ S => pay2 N k x' y') :=
    fun k x' => ⟨-∑ s, |N.payoff k s|, by
      rintro _ ⟨y', rfl⟩; linarith [(abs_le.1 (abs_pay2_le N k x' y')).1]⟩
  have hba : ∀ (k : Fin 2) (y' : Δ₂ S), BddAbove (Set.range fun x' : Δ₁ S => pay2 N k x' y') :=
    fun k y' => ⟨∑ s, |N.payoff k s|, by
      rintro _ ⟨x', rfl⟩; linarith [(abs_le.1 (abs_pay2_le N k x' y')).2]⟩
  have hbb' : ∀ (k : Fin 2) (y' : Δ₂ S), BddBelow (Set.range fun x' : Δ₁ S => pay2 N k x' y') :=
    fun k y' => ⟨-∑ s, |N.payoff k s|, by
      rintro _ ⟨x', rfl⟩; linarith [(abs_le.1 (abs_pay2_le N k x' y')).1]⟩
  have hba' : ∀ (k : Fin 2) (x' : Δ₁ S), BddAbove (Set.range fun y' : Δ₂ S => pay2 N k x' y') :=
    fun k x' => ⟨∑ s, |N.payoff k s|, by
      rintro _ ⟨y', rfl⟩; linarith [(abs_le.1 (abs_pay2_le N k x' y')).2]⟩
  -- player 1: `v_1 ≤ u_1* ≤ w_1`
  have hv1 : minimax₁ N ≤ pay2 N 0 x y := by
    refine (ciInf_le (f := fun y' : Δ₂ S => ⨆ x' : Δ₁ S, pay2 N 0 x' y') ⟨-B0, ?_⟩ y).trans
      (ciSup_le h1)
    rintro _ ⟨y', rfl⟩
    exact (le_ciSup (hba 0 y') x).trans' (by linarith [(abs_le.1 (abs_pay2_le N 0 x y')).1])
  have hw1 : pay2 N 0 x y ≤ maximin₁ N := by
    refine (le_ciInf fun y' => ?_).trans
      (le_ciSup (f := fun x' : Δ₁ S => ⨅ y' : Δ₂ S, pay2 N 0 x' y') ⟨B0, ?_⟩ x)
    · have := h2 y'
      rw [pay2_zeroSum hz, pay2_zeroSum hz] at this
      linarith
    · rintro _ ⟨x', rfl⟩
      exact (ciInf_le (hbb 0 x') y).trans (by linarith [(abs_le.1 (abs_pay2_le N 0 x' y)).2])
  -- player 2: `v_2 ≤ u_2* ≤ w_2`
  have hv2 : minimax₂ N ≤ pay2 N 1 x y := by
    refine (ciInf_le (f := fun x' : Δ₁ S => ⨆ y' : Δ₂ S, pay2 N 1 x' y') ⟨-B1, ?_⟩ x).trans
      (ciSup_le h2)
    rintro _ ⟨x', rfl⟩
    exact (le_ciSup (hba' 1 x') y).trans' (by linarith [(abs_le.1 (abs_pay2_le N 1 x' y)).1])
  have hw2 : pay2 N 1 x y ≤ maximin₂ N := by
    refine (le_ciInf fun x' => ?_).trans
      (le_ciSup (f := fun y' : Δ₂ S => ⨅ x' : Δ₁ S, pay2 N 1 x' y') ⟨B1, ?_⟩ y)
    · have := h1 x'
      rw [pay2_zeroSum hz, pay2_zeroSum hz]
      linarith
    · rintro _ ⟨y', rfl⟩
      exact (ciInf_le (hbb' 1 y') x).trans (by linarith [(abs_le.1 (abs_pay2_le N 1 x y')).2])
  exact ⟨le_antisymm (by linarith [hab.1]) hv1, le_antisymm hw1 (by linarith [hab.1]),
    le_antisymm (by linarith [hab.2]) hv2, le_antisymm hw2 (by linarith [hab.2])⟩

omit [∀ i, DecidableEq (S i)] in
/-- **Exercise 8.D.7(c)** (MWG, p. 264). In a zero-sum game, if `(x', y')` and `(x'', y'')` are
Nash equilibria, so are `(x', y'')` and `(x'', y')`. -/
theorem exercise_8_D_7c [∀ i, Nonempty (S i)] {N : NormalForm (Fin 2) S} (hz : IsZeroSum2 N)
    {x' x'' : Δ₁ S} {y' y'' : Δ₂ S} (h' : IsMixedNash N (mprof x'.1 y'.1))
    (h'' : IsMixedNash N (mprof x''.1 y''.1)) :
    IsMixedNash N (mprof x'.1 y''.1) ∧ IsMixedNash N (mprof x''.1 y'.1) := by
  classical
  obtain ⟨a1, a2⟩ := (isMixedNash_mprof_iff N x' y').1 h'
  obtain ⟨b1, b2⟩ := (isMixedNash_mprof_iff N x'' y'').1 h''
  obtain ⟨e1, -, -, -⟩ := exercise_8_D_7b hz x' y' h'
  obtain ⟨e2, -, -, -⟩ := exercise_8_D_7b hz x'' y'' h''
  -- `x'` guarantees the value against every `y`, and `y''` holds player 1 to it
  have gx : ∀ (x : Δ₁ S) (y : Δ₂ S) , IsMixedNash N (mprof x.1 y.1) → ∀ y₀ : Δ₂ S,
      pay2 N 0 x y ≤ pay2 N 0 x y₀ := by
    intro x y h y₀
    have := ((isMixedNash_mprof_iff N x y).1 h).2 y₀
    rw [pay2_zeroSum hz, pay2_zeroSum hz] at this
    linarith
  have c1 := gx x' y' h' y''
  have c2 := b1 x'
  have c3 := gx x'' y'' h'' y'
  have c4 := a1 x''
  have hval : pay2 N 0 x' y'' = pay2 N 0 x' y' := by linarith
  have hval' : pay2 N 0 x'' y' = pay2 N 0 x' y' := by linarith
  refine ⟨(isMixedNash_mprof_iff N x' y'').2 ⟨fun x₀ => ?_, fun y₀ => ?_⟩,
    (isMixedNash_mprof_iff N x'' y').2 ⟨fun x₀ => ?_, fun y₀ => ?_⟩⟩
  · linarith [b1 x₀]
  · rw [pay2_zeroSum hz, pay2_zeroSum hz]; linarith [gx x' y' h' y₀]
  · linarith [a1 x₀]
  · rw [pay2_zeroSum hz, pay2_zeroSum hz]; linarith [gx x'' y'' h'' y₀]

/-! ### Exercise 8.D.8 -/

/-- **Exercise 8.D.8 as printed is false** (correction 7). One player with the convex strategy set
`[-1, 1]` and the strictly convex (hence strictly quasiconvex) payoff `u(s) = s²`: the mixture of
`-1` and `1` with probability `½` each gives expected payoff `1`, at least as much as any finite
mixture, yet it is not degenerate. -/
theorem exercise_8_D_8_counterexample :
    StrictConvexOn ℝ (Set.Icc (-1 : ℝ) 1) (fun s => s ^ 2) ∧
      (∀ x y : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → y ∈ Set.Icc (-1 : ℝ) 1 → x ≠ y →
        ∀ t ∈ Set.Ioo (0 : ℝ) 1, (t * x + (1 - t) * y) ^ 2 < max (x ^ 2) (y ^ 2)) ∧
      ∀ (n : ℕ) (w x : Fin n → ℝ), (∀ k, 0 ≤ w k) → ∑ k, w k = 1 →
        (∀ k, x k ∈ Set.Icc (-1 : ℝ) 1) →
        ∑ k, w k * x k ^ 2 ≤ (1 / 2) * (-1 : ℝ) ^ 2 + (1 / 2) * (1 : ℝ) ^ 2 := by
  have hsc : StrictConvexOn ℝ (Set.Icc (-1 : ℝ) 1) (fun s => s ^ 2) := by
    refine ⟨convex_Icc _ _, fun x _ y _ hxy a b ha hb hab => ?_⟩
    simp only [smul_eq_mul]
    have hd : 0 < (x - y) ^ 2 := by
      have : x - y ≠ 0 := sub_ne_zero.2 hxy
      positivity
    have hb' : b = 1 - a := by linarith
    subst hb'
    nlinarith [mul_pos ha hb]
  refine ⟨hsc, fun x y hx hy hxy t ht => ?_, fun n w x hw hs hx => ?_⟩
  · have := hsc.2 hx hy hxy ht.1 (by linarith [ht.2] : (0 : ℝ) < 1 - t) (by ring)
    simp only [smul_eq_mul] at this
    have h1 : t * x ^ 2 + (1 - t) * y ^ 2 ≤ max (x ^ 2) (y ^ 2) := by
      have := le_max_left (x ^ 2) (y ^ 2)
      have := le_max_right (x ^ 2) (y ^ 2)
      nlinarith [ht.1, ht.2]
    linarith
  · have hle : ∀ k, w k * x k ^ 2 ≤ w k := fun k => by
      have := hx k
      have : x k ^ 2 ≤ 1 := by nlinarith [this.1, this.2]
      nlinarith [hw k]
    calc ∑ k, w k * x k ^ 2 ≤ ∑ k, w k := Finset.sum_le_sum fun k _ => hle k
      _ = (1 / 2) * (-1 : ℝ) ^ 2 + (1 / 2) * (1 : ℝ) ^ 2 := by rw [hs]; norm_num

/-- **Exercise 8.D.8, corrected** (correction 7). If a player's expected payoff `U` (given the
others' play) is strictly concave on his convex strategy set, every finite mixture that is a best
response — at least as good as every pure strategy — is degenerate: all the points it plays with
positive probability coincide. -/
theorem exercise_8_D_8 {E : Type*} [AddCommGroup E] [Module ℝ E] {C : Set E} {U : E → ℝ}
    (hU : StrictConcaveOn ℝ C U) {n : ℕ} {w : Fin n → ℝ} {x : Fin n → E}
    (hw : ∀ k, 0 < w k) (hs : ∑ k, w k = 1) (hx : ∀ k, x k ∈ C)
    (hbest : ∀ z ∈ C, U z ≤ ∑ k, w k * U (x k)) : ∀ j k, x j = x k := by
  by_contra hne
  push Not at hne
  obtain ⟨j, k, hjk⟩ := hne
  have hlt := hU.lt_map_sum (t := univ) (fun i _ => hw i) hs (fun i _ => hx i)
    ⟨j, mem_univ _, k, mem_univ _, hjk⟩
  have hmem : ∑ i, w i • x i ∈ C :=
    hU.1.sum_mem (fun i _ => (hw i).le) hs fun i _ => hx i
  have := hbest _ hmem
  simp only [smul_eq_mul] at hlt
  linarith

end MWG.SimultaneousMoveGames
