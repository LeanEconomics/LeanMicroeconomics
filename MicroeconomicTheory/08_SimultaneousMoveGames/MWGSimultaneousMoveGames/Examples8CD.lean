/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGSimultaneousMoveGames.Examples8B
import MWGNoncooperativeGames.MatchingPennies

/-!
# The examples of Sections 8.C and 8.D

MWG, pp. 244-252, and Exercise 8.D.1 (p. 263). Rows and columns are numbered from `0`.

* **Example 8.C.1** (Figure 8.C.1, Bernheim's game): `a₁, a₂, a₃` and `b₁, b₂, b₃` are
  rationalizable (each is a best response to one of the others), `b₄` is strictly dominated by
  `½b₁ + ½b₃`, `a₄` is strictly dominated by `a₂` once `b₄` is deleted, and neither `a₄` nor `b₄`
  is rationalizable.
* Figure 8.C.2 (p. 245): when `M` in Figure 8.B.5 pays `6` against both columns it is a best
  response to `σ₂(R) = ½`.
* **Example 8.D.1** (Figure 8.D.1): `(M, m)` is the only pure Nash equilibrium.
* **Example 8.D.2**: `(a₂, b₂)` is the only pure Nash equilibrium of Figure 8.C.1, and
  **Exercise 8.D.1**: it is the only mixed one.
* **Example 8.D.3** (Meeting in New York): two pure equilibria; with Grand Central paying
  `1000` (the focal-point discussion, p. 248) both remain equilibria. **Example 8.D.5**: going to
  Grand Central with probability `1/11` is a mixed equilibrium, and `1/11` is the only
  probability that makes a player indifferent.
* The correlated-equilibrium remark (p. 252): following a public signal to `(Empire State, Empire
  State)` or `(Grand Central, Grand Central)` is self-enforcing.
* **Example 8.D.4** (Figure 8.D.3, Chapter 7's `matchingPennies`): no pure equilibrium; each
  player mixing `½`-`½` is a mixed equilibrium.
-/

namespace MWG.SimultaneousMoveGames

open MWG.NoncooperativeGames Function

/-! ### Example 8.C.1 (Figure 8.C.1) -/

/-- Player 1's payoffs in Figure 8.C.1 (rows `a₁, …, a₄`, columns `b₁, …, b₄`). -/
def fig8C1U₁ : Fin 4 → Fin 4 → ℝ :=
  ![![0, 2, 7, 0], ![5, 3, 5, 0], ![7, 2, 0, 0], ![0, 0, 0, 10]]

/-- Player 2's payoffs in Figure 8.C.1. -/
def fig8C1U₂ : Fin 4 → Fin 4 → ℝ :=
  ![![7, 5, 0, 1], ![2, 3, 2, 1], ![0, 5, 7, 1], ![0, -2, 0, -1]]

/-- The game of Figure 8.C.1. -/
abbrev bernheim : NormalForm (Fin 2) (S2 4 4) := bimatrix fig8C1U₁ fig8C1U₂

/-- The randomized strategy `½b₁ + ½b₃`. -/
noncomputable def halfB13 : Fin 4 → ℝ := ![1 / 2, 0, 1 / 2, 0]

theorem isMixedStrategy_halfB13 : IsMixedStrategy halfB13 := by
  refine ⟨fun a => by fin_cases a <;> norm_num [halfB13], ?_⟩
  simp [halfB13, Fin.sum_univ_four]
  norm_num

/-- **Example 8.C.1** (MWG, p. 244). `b₄` is strictly dominated by `½b₁ + ½b₃`; once `b₄` is
deleted, `a₄` is strictly dominated by `a₂`. -/
theorem example_8_C_1_dominance :
    MixedStrictlyDominates bernheim 1 halfB13 (pureMixed (3 : Fin 4)) ∧
      ∀ b : Fin 4, b ≠ 3 → fig8C1U₁ 3 b < fig8C1U₁ 1 b := by
  refine ⟨(bimatrix_mixedStrictlyDominates_one_iff fig8C1U₁ fig8C1U₂ halfB13
    (pureMixed (3 : Fin 4))).2 fun a => ?_, fun b hb => ?_⟩
  · fin_cases a <;> simp [Fin.sum_univ_four, halfB13, pureMixed, fig8C1U₂] <;> norm_num
  · fin_cases b <;> simp_all [fig8C1U₁]

/-- The pure strategies of Figure 8.C.1 claimed rationalizable: `a₁, a₂, a₃` and `b₁, b₂, b₃`. -/
def bernheimSet : (i : Fin 2) → Set (S2 4 4 i → ℝ) :=
  Fin.cons {pureMixed (0 : Fin 4), pureMixed (1 : Fin 4), pureMixed (2 : Fin 4)}
    (Fin.cons {pureMixed (0 : Fin 4), pureMixed (1 : Fin 4), pureMixed (2 : Fin 4)} finZeroElim)

/-- **Example 8.C.1** (MWG, p. 244). `a₁, a₂, a₃` are rationalizable for player 1 and `b₁, b₂, b₃`
for player 2: `a₁` is a best response to `b₃`, `a₂` to `b₂`, `a₃` to `b₁`, and `b₁, b₂, b₃` are
best responses to `a₁, a₂, a₃`. -/
theorem example_8_C_1_rationalizable (k : Fin 3) :
    Rationalizable bernheim 0 (pureMixed (k.castSucc : Fin 4)) ∧
      Rationalizable bernheim 1 (pureMixed (k.castSucc : Fin 4)) := by
  have hΔ : ∀ i, bernheimSet i ⊆ mixedExtension (S2 4 4 i) := by
    intro i τ hτ
    fin_cases i <;>
    · simp only [bernheimSet] at hτ
      rcases hτ with rfl | rfl | rfl <;> exact isMixedStrategy_pureMixed _
  -- player 1's rows against a pure column, and player 2's columns against a pure row
  have hBR : ∀ i, ∀ τ ∈ bernheimSet i, BRToSome bernheim bernheimSet i τ := by
    intro i
    fin_cases i
    · intro τ hτ
      simp only [bernheimSet] at hτ
      -- `a₁` against `b₃`, `a₂` against `b₂`, `a₃` against `b₁`
      obtain ⟨a, b, rfl, hab⟩ : ∃ a b : Fin 4, τ = pureMixed a ∧ b ≠ 3 ∧
          ∀ a', fig8C1U₁ a' b ≤ fig8C1U₁ a b := by
        rcases hτ with rfl | rfl | rfl
        · exact ⟨0, 2, rfl, by decide, fun a' => by fin_cases a' <;> norm_num [fig8C1U₁]⟩
        · exact ⟨1, 1, rfl, by decide, fun a' => by fin_cases a' <;> norm_num [fig8C1U₁]⟩
        · exact ⟨2, 0, rfl, by decide, fun a' => by fin_cases a' <;> norm_num [fig8C1U₁]⟩
      refine ⟨mp (pureMixed a) (pureMixed b), isMixedProfile_mp (isMixedStrategy_pureMixed _)
        (isMixedStrategy_pureMixed _), fun j hj => ?_, ?_⟩
      · have : j = 1 := by fin_cases j <;> simp_all
        subst this
        simp only [bernheimSet, mp_one]
        change pureMixed b ∈ ({pureMixed 0, pureMixed 1, pureMixed 2} : Set (Fin 4 → ℝ))
        have hb := hab.1
        fin_cases b <;> simp_all
      · refine bimatrix_isBestResponse_row _ _ _ a fun a' => ?_
        simp only [mp_one, sum_pureMixed_mul]
        exact hab.2 a'
    · intro τ hτ
      simp only [bernheimSet] at hτ
      obtain ⟨b, a, rfl, hab⟩ : ∃ b a : Fin 4, τ = pureMixed b ∧ a ≠ 3 ∧
          ∀ b', fig8C1U₂ a b' ≤ fig8C1U₂ a b := by
        rcases hτ with rfl | rfl | rfl
        · exact ⟨0, 0, rfl, by decide, fun b' => by fin_cases b' <;> norm_num [fig8C1U₂]⟩
        · exact ⟨1, 1, rfl, by decide, fun b' => by fin_cases b' <;> norm_num [fig8C1U₂]⟩
        · exact ⟨2, 2, rfl, by decide, fun b' => by fin_cases b' <;> norm_num [fig8C1U₂]⟩
      refine ⟨mp (pureMixed a) (pureMixed b), isMixedProfile_mp (isMixedStrategy_pureMixed _)
        (isMixedStrategy_pureMixed _), fun j hj => ?_, ?_⟩
      · have : j = 0 := by fin_cases j <;> simp_all
        subst this
        simp only [bernheimSet, mp_zero]
        change pureMixed a ∈ ({pureMixed 0, pureMixed 1, pureMixed 2} : Set (Fin 4 → ℝ))
        have ha := hab.1
        fin_cases a <;> simp_all
      · refine bimatrix_isBestResponse_col _ _ _ b fun b' => ?_
        simp only [mp_zero, sum_pureMixed_mul]
        exact hab.2 b'
  have hmem : pureMixed (k.castSucc : Fin 4) ∈
      ({pureMixed 0, pureMixed 1, pureMixed 2} : Set (Fin 4 → ℝ)) := by
    fin_cases k <;> simp
  exact ⟨rationalizable_of_bestResponseSet (i := 0) hΔ hBR hmem,
    rationalizable_of_bestResponseSet (i := 1) hΔ hBR hmem⟩

/-- In Figure 8.C.1, every best response of player 2 puts zero weight on `b₄`. -/
theorem bernheim_bestResponse_b4 {σ : (i : Fin 2) → S2 4 4 i → ℝ} (hσ : IsMixedProfile σ)
    {τ : Fin 4 → ℝ} (hτ : IsBestResponse bernheim 1 τ σ) : τ 3 = 0 := by
  have hτm : IsMixedStrategy τ := hτ.1
  by_contra hne
  have hpos : 0 < τ 3 := lt_of_le_of_ne (hτm.1 3) (Ne.symm hne)
  have hsupp := (isBestResponse_iff_support bernheim 1 hτ.1 σ).1 hτ (3 : Fin 4) hpos
  -- `b₄` does strictly worse than `½b₁ + ½b₃` against `σ₁`
  have hlt := example_8_C_1_dominance.1 σ hσ
  have hle := mixedPayoff_le_of_pure_le bernheim σ 1 isMixedStrategy_halfB13 1 hsupp
  linarith

/-- **Example 8.C.1** (MWG, p. 244). `b₄` and `a₄` are not rationalizable: `b₄` is never a best
response, and `a₄` is not a best response to any of player 2's strategies that survive the first
round. -/
theorem example_8_C_1_not_rationalizable :
    ¬ Rationalizable bernheim 1 (pureMixed (3 : Fin 4)) ∧
      ¬ Rationalizable bernheim 0 (pureMixed (3 : Fin 4)) := by
  constructor
  · intro h
    obtain ⟨-, σ, hσ, -, hbr⟩ := h 1
    have : (pureMixed (3 : Fin 4) : Fin 4 → ℝ) 3 = 0 := bernheim_bestResponse_b4 hσ hbr
    simp [pureMixed] at this
  · intro h
    obtain ⟨-, σ, hσ, hσT, hbr⟩ := h 2
    obtain ⟨-, ρ, hρ, -, hbr₂⟩ := hσT 1 (by decide)
    have h3 := bernheim_bestResponse_b4 hρ hbr₂
    -- `a₂` does better than `a₄` against `σ₂`
    have hle := hbr.2 _ (isMixedStrategy_pureMixed (1 : Fin 4))
    have e1 := bimatrix_mixedPayoff_row fig8C1U₁ fig8C1U₂ σ (1 : Fin 4)
    have e2 := bimatrix_mixedPayoff_row fig8C1U₁ fig8C1U₂ σ (3 : Fin 4)
    have hm : IsMixedStrategy (σ 1 : Fin 4 → ℝ) := hσ 1
    set τ : Fin 4 → ℝ := σ 1 with hτdef
    have hs : ∑ b : Fin 4, τ b = 1 := hm.2
    have hm0 : ∀ b : Fin 4, 0 ≤ τ b := hm.1
    rw [Fin.sum_univ_four] at hs
    have E1 : ∑ b : Fin 4, τ b * fig8C1U₁ 1 b = 5 * τ 0 + 3 * τ 1 + 5 * τ 2 := by
      simp [Fin.sum_univ_four, fig8C1U₁]
      ring
    have E2 : ∑ b : Fin 4, τ b * fig8C1U₁ 3 b = 10 * τ 3 := by
      simp [Fin.sum_univ_four, fig8C1U₁, mul_comm]
    have key : ∑ b : Fin 4, τ b * fig8C1U₁ 1 b ≤ ∑ b : Fin 4, τ b * fig8C1U₁ 3 b :=
      e1.symm.trans_le (hle.trans_eq e2)
    linarith [hm0 0, hm0 1, hm0 2]

/-! ### Figure 8.C.2 -/

/-- **Figure 8.C.2** (MWG, p. 245). If `M` pays `6` against both columns in Figure 8.B.5, it is not
strictly dominated and is a best response to `σ₂(R) = ½`. -/
theorem figure_8_C_2 :
    IsBestResponse (bimatrix fig8B5U₁' fig8B5U₂) 0 (pureMixed (1 : Fin 3))
      (mp halfUD ![1 / 2, 1 / 2]) := by
  refine bimatrix_isBestResponse_row _ _ _ 1 fun a' => ?_
  simp only [mp_one]
  fin_cases a' <;> simp [Fin.sum_univ_two, fig8B5U₁'] <;> norm_num

/-! ### Example 8.D.1 (Figure 8.D.1) -/

/-- Player 1's payoffs in Figure 8.D.1 (rows `U, M, D`, columns `ℓ, m, r`). -/
def fig8D1U₁ : Fin 3 → Fin 3 → ℝ := ![![5, 0, 3], ![4, 5, 4], ![3, 0, 5]]

/-- Player 2's payoffs in Figure 8.D.1. -/
def fig8D1U₂ : Fin 3 → Fin 3 → ℝ := ![![3, 4, 5], ![0, 5, 0], ![5, 4, 3]]

/-- **Example 8.D.1** (MWG, p. 246). `(M, m)` is the only pure strategy Nash equilibrium of the
game in Figure 8.D.1. -/
theorem example_8_D_1 (a b : Fin 3) :
    IsNashEquilibrium (bimatrix fig8D1U₁ fig8D1U₂) (pp a b) ↔ a = 1 ∧ b = 1 := by
  rw [bimatrix_isNash_iff]
  fin_cases a <;> fin_cases b <;> simp [Fin.forall_fin_succ, fig8D1U₁, fig8D1U₂] <;> norm_num

/-- **Example 8.D.2** (MWG, p. 246). `(a₂, b₂)` is the only pure strategy Nash equilibrium of the
game in Figure 8.C.1. -/
theorem example_8_D_2 (a b : Fin 4) :
    IsNashEquilibrium bernheim (pp a b) ↔ a = 1 ∧ b = 1 := by
  rw [bimatrix_isNash_iff]
  fin_cases a <;> fin_cases b <;> simp [Fin.forall_fin_succ, fig8C1U₁, fig8C1U₂] <;> norm_num

/-- **Exercise 8.D.1** (MWG, p. 263). `(a₂, b₂)` played with certainty is the unique mixed strategy
Nash equilibrium of the game in Figure 8.C.1. -/
theorem exercise_8_D_1 {x y : Fin 4 → ℝ} (hx : IsMixedStrategy x) (hy : IsMixedStrategy y) :
    IsMixedNash bernheim (mp x y) ↔ x = pureMixed 1 ∧ y = pureMixed 1 := by
  rw [bimatrix_isMixedNash_support _ _ hx hy]
  have hx0 := hx.1
  have hy0 := hy.1
  have hxs : x 0 + x 1 + x 2 + x 3 = 1 := by simpa [Fin.sum_univ_four] using hx.2
  have hys : y 0 + y 1 + y 2 + y 3 = 1 := by simpa [Fin.sum_univ_four] using hy.2
  -- the payoffs of the rows against `y` and of the columns against `x`
  have hrow : ∀ a', ∑ b, y b * fig8C1U₁ a' b =
      ![2 * y 1 + 7 * y 2, 5 * y 0 + 3 * y 1 + 5 * y 2, 7 * y 0 + 2 * y 1, 10 * y 3] a' := by
    intro a'
    fin_cases a' <;> simp [Fin.sum_univ_four, fig8C1U₁] <;> ring
  have hcol : ∀ b', ∑ a, x a * fig8C1U₂ a b' =
      ![7 * x 0 + 2 * x 1, 5 * x 0 + 3 * x 1 + 5 * x 2 - 2 * x 3, 2 * x 1 + 7 * x 2,
        x 0 + x 1 + x 2 - x 3] b' := by
    intro b'
    fin_cases b' <;> simp [Fin.sum_univ_four, fig8C1U₂] <;> ring
  simp only [hrow, hcol]
  constructor
  · rintro ⟨h1, h2⟩
    have nx : ∀ a, x a ≤ 0 ∨ 0 < x a := fun a => le_or_gt _ _
    have ny : ∀ b, y b ≤ 0 ∨ 0 < y b := fun b => le_or_gt _ _
    -- `b₄` is never used, then `a₄` is never used
    have y3 : y 3 = 0 := by
      rcases ny 3 with h | h
      · exact le_antisymm h (hy0 3)
      · have c0 := h2 3 h 0
        have c2 := h2 3 h 2
        simp at c0 c2
        linarith [hx0 0, hx0 1, hx0 2, hx0 3]
    have x3 : x 3 = 0 := by
      rcases nx 3 with h | h
      · exact le_antisymm h (hx0 3)
      · have r1 := h1 3 h 1
        simp at r1
        linarith [hy0 0, hy0 1, hy0 2, hy0 3]
    -- `a₁` is never used
    have x0 : x 0 = 0 := by
      rcases nx 0 with h | h
      · exact le_antisymm h (hx0 0)
      · have r1 := h1 0 h 1
        have r2 := h1 0 h 2
        simp at r1 r2
        have hy2 : 0 < y 2 := by
          by_contra hle
          push Not at hle
          linarith [hy0 0, hy0 1]
        have c1 := h2 2 hy2 1
        simp at c1
        have hx2 : 0 < x 2 := by linarith [hx0 1]
        have r0 := h1 2 hx2 0
        simp at r0
        linarith [hy0 0, hy0 1, hy0 2]
    -- `a₃` is never used
    have x2 : x 2 = 0 := by
      rcases nx 2 with h | h
      · exact le_antisymm h (hx0 2)
      · have r1 := h1 2 h 1
        simp at r1
        have hy0' : 0 < y 0 := by linarith [hy0 1, hy0 2]
        have c1 := h2 0 hy0' 1
        simp at c1
        linarith [hx0 1]
    have x1 : x 1 = 1 := by linarith
    have hy' : ∀ b, b ≠ 1 → y b = 0 := by
      intro b hb
      rcases ny b with h | h
      · exact le_antisymm h (hy0 b)
      · have c := h2 b h 1
        fin_cases b
        · simp at c; linarith
        · exact absurd rfl hb
        · simp at c; linarith
        · exact y3
    have y0 := hy' 0 (by decide)
    have y2 := hy' 2 (by decide)
    have y1 : y 1 = 1 := by linarith
    refine ⟨funext fun a => ?_, funext fun b => ?_⟩
    · fin_cases a <;> simp [pureMixed, x0, x1, x2, x3]
    · fin_cases b <;> simp [pureMixed, y0, y1, y2, y3]
  · rintro ⟨rfl, rfl⟩
    refine ⟨fun a ha a' => ?_, fun b hb b' => ?_⟩
    · have : a = 1 := by by_contra h; simp [pureMixed, h] at ha
      subst this
      fin_cases a' <;> simp [pureMixed] <;> norm_num
    · have : b = 1 := by by_contra h; simp [pureMixed, h] at hb
      subst this
      fin_cases b' <;> simp [pureMixed] <;> norm_num

/-! ### Examples 8.D.3 and 8.D.5: Meeting in New York (`0` = Empire State, `1` = Grand Central) -/

/-- The Meeting in New York payoffs with values `v₀` at Empire State and `v₁` at Grand Central. -/
def meetNY (v₀ v₁ : ℝ) : Fin 2 → Fin 2 → ℝ := ![![v₀, 0], ![0, v₁]]

/-- **Example 8.D.3** (MWG, p. 247). In the Meeting in New York game (Figure 8.D.2, payoffs `100`)
the pure Nash equilibria are exactly (Empire State, Empire State) and (Grand Central, Grand
Central); with the focal payoff `1000` at Grand Central (p. 248) the same two profiles are the
pure equilibria. -/
theorem example_8_D_3 {v₀ v₁ : ℝ} (h₀ : 0 < v₀) (h₁ : 0 < v₁) (a b : Fin 2) :
    IsNashEquilibrium (bimatrix (meetNY v₀ v₁) (meetNY v₀ v₁)) (pp a b) ↔ a = b := by
  rw [bimatrix_isNash_iff]
  constructor
  · rintro ⟨h1, h2⟩
    fin_cases a <;> fin_cases b
    · rfl
    · have := h1 1; simp [meetNY] at this; linarith
    · have := h1 0; simp [meetNY] at this; linarith
    · rfl
  · rintro rfl
    refine ⟨fun a' => ?_, fun b' => ?_⟩ <;> fin_cases a <;>
      first | (fin_cases a' <;> simp [meetNY, h₀.le, h₁.le])
            | (fin_cases b' <;> simp [meetNY, h₀.le, h₁.le])

/-- **Example 8.D.3** (MWG, p. 247), the instance of Figure 8.D.2 (`100` at both places). -/
theorem example_8_D_3_figure (a b : Fin 2) :
    IsNashEquilibrium (bimatrix (meetNY 100 100) (meetNY 100 100)) (pp a b) ↔ a = b :=
  example_8_D_3 (by norm_num) (by norm_num) a b

/-- **Example 8.D.5** (MWG, p. 251). With payoffs `100` at Empire State and `1000` at Grand Central,
Mr. Thomas is indifferent between the two places exactly when Mr. Schelling goes to Grand Central
with probability `1/11`. -/
theorem example_8_D_5_indifference (σ : ℝ) :
    1000 * σ + 0 * (1 - σ) = 100 * (1 - σ) + 0 * σ ↔ σ = 1 / 11 := by
  constructor <;> intro h <;> linarith

/-- **Example 8.D.5** (MWG, p. 251). Each player going to Grand Central with probability `1/11` is a
mixed strategy Nash equilibrium of the Meeting in New York game with Grand Central paying
`1000`. -/
theorem example_8_D_5 :
    IsMixedNash (bimatrix (meetNY 100 1000) (meetNY 100 1000))
      (mp ![10 / 11, 1 / 11] ![10 / 11, 1 / 11]) := by
  have hm : IsMixedStrategy (![10 / 11, 1 / 11] : Fin 2 → ℝ) := by
    refine ⟨fun a => by fin_cases a <;> norm_num, ?_⟩
    simp [Fin.sum_univ_two]
    norm_num
  rw [bimatrix_isMixedNash_iff _ _ hm hm]
  refine ⟨fun a' => ?_, fun b' => ?_⟩ <;>
  · first | fin_cases a' | fin_cases b'
    all_goals simp [Fin.sum_univ_two, meetNY]; norm_num

/-- **Section 8.D** (MWG, p. 252, small type). With a public signal telling both players to go to
the same place (each place with probability `½`), following the signal is optimal for each player
whatever he is told: a correlated equilibrium in which the players always meet. -/
theorem meetNY_correlated (a a' : Fin 2) :
    meetNY 100 100 a' a ≤ meetNY 100 100 a a ∧
      (∑ b : Fin 2, (1 / 2 : ℝ) * meetNY 100 100 b b) = 100 := by
  constructor
  · fin_cases a <;> fin_cases a' <;> norm_num [meetNY]
  · simp [Fin.sum_univ_two, meetNY]
    norm_num

/-! ### Example 8.D.4: Matching Pennies (Chapter 7's `matchingPennies`, Figure 8.D.3) -/

/-- **Example 8.D.4** (MWG, p. 250). Matching Pennies has no pure strategy Nash equilibrium. -/
theorem example_8_D_4_no_pure (s : (i : Fin 2) → Fin 2) :
    ¬ IsNashEquilibrium matchingPennies s := by
  intro h
  have h0 := h 0
  have h1 := h 1
  have hs : s = ![s 0, s 1] := by funext i; fin_cases i <;> rfl
  rw [hs] at h0 h1
  generalize s 0 = a at h0 h1
  generalize s 1 = b at h0 h1
  fin_cases a <;> fin_cases b
  · have := h0 1; simp [matchingPennies, mpPay, Function.update] at this; norm_num at this
  · have := h1 0; simp [matchingPennies, mpPay, Function.update] at this; norm_num at this
  · have := h1 1; simp [matchingPennies, mpPay, Function.update] at this; norm_num at this
  · have := h0 0; simp [matchingPennies, mpPay, Function.update] at this; norm_num at this

/-- **Example 8.D.4** (MWG, p. 250). Each player choosing heads and tails with equal probability is
a mixed strategy Nash equilibrium of Matching Pennies. -/
theorem example_8_D_4 : IsMixedNash matchingPennies (fun _ _ => 1 / 2) := by
  have hm : IsMixedProfile (fun (_ : Fin 2) (_ : Fin 2) => (1 / 2 : ℝ)) := fun _ =>
    ⟨fun _ => by norm_num, by norm_num [Fin.sum_univ_two]⟩
  rw [isMixedNash_iff_pure_deviations _ hm]
  intro i b
  rw [mixedPayoff_fin_two, mixedPayoff_fin_two]
  fin_cases i <;> fin_cases b <;>
    norm_num [Fin.sum_univ_two, matchingPennies, mpPay, pureMixed, Function.update]

end MWG.SimultaneousMoveGames
