/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGSimultaneousMoveGames.Bimatrix

/-!
# Exercise 8.D.9: Kreps's game

MWG, Exercise 8.D.9, pp. 264-265 (after Kreps 1990). Player 1 chooses `U` or `D`, player 2
chooses `LL`, `L`, `M` or `R` (rows and columns numbered from `0` in this order):

|     | `LL`      | `L`       | `M`  | `R`        |
|-----|-----------|-----------|------|------------|
| `U` | 100, 2    | -100, 1   | 0, 0 | -100, -100 |
| `D` | -100, -100| 100, -49  | 1, 0 | 100, 2     |

* (a) is a question about intuition. Its mathematical content: `M` is player 2's safe strategy.
  It guarantees `0`; every other pure strategy risks `-49` or worse; and `M` is the only mixed
  strategy that guarantees `0` (`exercise_8_D_9a`).
* (b) The Nash equilibria are `(U, LL)`, `(D, R)` and the mixed equilibrium in which player 1
  plays `U` with probability `51/52` and player 2 mixes `LL` and `L` equally
  (`exercise_8_D_9b`).
* (c) `M` is played in no Nash equilibrium (`exercise_8_D_9c_not_nash`). It is rationalizable
  (`exercise_8_D_9c_rationalizable`): it is a best response to `½U + ½D`, which is a best
  response to `½LL + ½L`, which is a best response to `(51/52)U + (1/52)D`, which is a best
  response to `½LL + ½L`.
* (d) is a question about preplay communication. Its mathematical content: in both pure
  equilibria the payoffs are `(100, 2)`, so both players strictly prefer either of them to any
  outcome in which player 2 plays `M` (player 2 gets `0` there) (`exercise_8_D_9d`).
-/

namespace MWG.SimultaneousMoveGames

open MWG.NoncooperativeGames Function Finset

/-- Player 1's payoffs in Kreps's game. -/
def krepsU₁ : Fin 2 → Fin 4 → ℝ := ![![100, -100, 0, -100], ![-100, 100, 1, 100]]

/-- Player 2's payoffs in Kreps's game. -/
def krepsU₂ : Fin 2 → Fin 4 → ℝ := ![![2, 1, 0, -100], ![-100, -49, 0, 2]]

/-- **Exercise 8.D.9** (MWG, p. 264). Kreps's game. -/
def kreps : NormalForm (Fin 2) (S2 2 4) := bimatrix krepsU₁ krepsU₂

/-- Player 1's payoffs against player 2's mixed strategy `y`. -/
theorem kreps_rows (y : Fin 4 → ℝ) (a : Fin 2) :
    ∑ b, y b * krepsU₁ a b =
      ![100 * y 0 - 100 * y 1 - 100 * y 3, -100 * y 0 + 100 * y 1 + y 2 + 100 * y 3] a := by
  fin_cases a <;> simp [Fin.sum_univ_four, krepsU₁] <;> ring

/-- Player 2's payoffs against player 1's mixed strategy `x`. -/
theorem kreps_cols (x : Fin 2 → ℝ) (b : Fin 4) :
    ∑ a, x a * krepsU₂ a b =
      ![2 * x 0 - 100 * x 1, x 0 - 49 * x 1, 0, -100 * x 0 + 2 * x 1] b := by
  fin_cases b <;> simp [Fin.sum_univ_two, krepsU₂] <;> ring

/-- **Exercise 8.D.9(a)** (MWG, p. 265), its mathematical content. `M` guarantees player 2 the
payoff `0`, each other pure strategy risks at most `-49`, and `M` is the only mixed strategy of
player 2 that guarantees `0` against both of player 1's strategies. -/
theorem exercise_8_D_9a :
    (∀ a, krepsU₂ a 2 = 0) ∧ (∀ b, b ≠ 2 → ∃ a, krepsU₂ a b ≤ -49) ∧
      ∀ y : Fin 4 → ℝ, IsMixedStrategy y →
        ((∀ a, 0 ≤ ∑ b, y b * krepsU₂ a b) ↔ y = pureMixed 2) := by
  refine ⟨fun a => by fin_cases a <;> rfl, fun b hb => ?_, fun y hy => ?_⟩
  · fin_cases b
    · exact ⟨1, by norm_num [krepsU₂]⟩
    · exact ⟨1, by norm_num [krepsU₂]⟩
    · exact absurd rfl hb
    · exact ⟨0, by norm_num [krepsU₂]⟩
  · have h0 := hy.1
    have hs : y 0 + y 1 + y 2 + y 3 = 1 := by simpa [Fin.sum_univ_four] using hy.2
    constructor
    · intro h
      have hU := h 0
      have hD := h 1
      simp [Fin.sum_univ_four, krepsU₂] at hU hD
      have y0 : y 0 = 0 := by linarith [h0 0, h0 1, h0 3]
      have y1 : y 1 = 0 := by linarith [h0 0, h0 1, h0 3]
      have y3 : y 3 = 0 := by linarith [h0 0, h0 1, h0 3]
      have y2 : y 2 = 1 := by linarith
      funext b
      fin_cases b
      · simp [pureMixed, y0]
      · simp [pureMixed, y1]
      · simp [pureMixed, y2]
      · simp [pureMixed, y3]
    · rintro rfl a
      fin_cases a <;> simp [krepsU₂, pureMixed]

/-- The mixed equilibrium strategy of player 1. -/
noncomputable def krepsX : Fin 2 → ℝ := ![51 / 52, 1 / 52]

/-- The mixed equilibrium strategy of player 2: `½LL + ½L`. -/
noncomputable def krepsY : Fin 4 → ℝ := ![1 / 2, 1 / 2, 0, 0]

/-- **Exercise 8.D.9(b)** (MWG, p. 265). The Nash equilibria (pure and mixed) of Kreps's game are
`(U, LL)`, `(D, R)` and `((51/52) U + (1/52) D, ½ LL + ½ L)`. -/
theorem exercise_8_D_9b {x : Fin 2 → ℝ} {y : Fin 4 → ℝ} (hx : IsMixedStrategy x)
    (hy : IsMixedStrategy y) :
    IsMixedNash kreps (mp x y) ↔ (x = pureMixed 0 ∧ y = pureMixed 0) ∨
      (x = pureMixed 1 ∧ y = pureMixed 3) ∨ (x = krepsX ∧ y = krepsY) := by
  rw [kreps, bimatrix_isMixedNash_support _ _ hx hy]
  simp only [kreps_rows, kreps_cols]
  have hx0 := hx.1
  have hy0 := hy.1
  have hxs : x 0 + x 1 = 1 := by simpa [Fin.sum_univ_two] using hx.2
  have hys : y 0 + y 1 + y 2 + y 3 = 1 := by simpa [Fin.sum_univ_four] using hy.2
  constructor
  · rintro ⟨hr, hc⟩
    -- the column conditions, one by one
    have c : ∀ b, 0 < y b → ∀ b', ![2 * x 0 - 100 * x 1, x 0 - 49 * x 1, 0,
        -100 * x 0 + 2 * x 1] b' ≤ ![2 * x 0 - 100 * x 1, x 0 - 49 * x 1, 0,
        -100 * x 0 + 2 * x 1] b := hc
    rcases (hx0 0).eq_or_lt with hx0z | hx0p
    · -- `x = D`: only `R` is a best reply
      have hx1 : x 1 = 1 := by linarith
      have hyz : ∀ b, b ≠ 3 → y b = 0 := by
        intro b hb
        rcases (hy0 b).eq_or_lt with h | h
        · exact h.symm
        · have := c b h 3
          fin_cases b <;> simp at this hb <;> linarith
      right; left
      refine ⟨?_, ?_⟩
      · funext a; fin_cases a <;> simp [pureMixed] <;> linarith
      · have y3 : y 3 = 1 := by linarith [hyz 0 (by decide), hyz 1 (by decide), hyz 2 (by decide)]
        funext b
        by_cases hb : b = 3
        · subst hb; simp [pureMixed, y3]
        · rw [hyz b hb]; simp [pureMixed, hb]
    rcases (hx0 1).eq_or_lt with hx1z | hx1p
    · -- `x = U`: only `LL` is a best reply
      have hx0' : x 0 = 1 := by linarith
      have hyz : ∀ b, b ≠ 0 → y b = 0 := by
        intro b hb
        rcases (hy0 b).eq_or_lt with h | h
        · exact h.symm
        · have := c b h 0
          fin_cases b <;> simp at this hb <;> linarith
      left
      refine ⟨?_, ?_⟩
      · funext a; fin_cases a <;> simp [pureMixed] <;> linarith
      · have y0 : y 0 = 1 := by linarith [hyz 1 (by decide), hyz 2 (by decide), hyz 3 (by decide)]
        funext b
        by_cases hb : b = 0
        · subst hb; simp [pureMixed, y0]
        · rw [hyz b hb]; simp [pureMixed, hb]
    -- both rows are played: player 1 is indifferent
    have hUD := hr 0 hx0p 1
    have hDU := hr 1 hx1p 0
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hUD hDU
    have hind : 200 * y 0 - 200 * y 1 - 200 * y 3 = y 2 := by linarith
    have y2 : y 2 = 0 := by
      rcases (hy0 2).eq_or_lt with h | h
      · exact h.symm
      · exfalso
        have hy0p : 0 < y 0 := by linarith [hy0 1, hy0 3]
        have m0 := c 2 h 0
        have m1 := c 2 h 1
        have l1 := c 0 hy0p 1
        simp at m0 m1 l1
        linarith
    have y3 : y 3 = 0 := by
      rcases (hy0 3).eq_or_lt with h | h
      · exact h.symm
      · exfalso
        have hy0p : 0 < y 0 := by linarith [hy0 1]
        have r0 := c 3 h 0
        have r2 := c 3 h 2
        have l3 := c 0 hy0p 3
        simp at r0 r2 l3
        linarith
    have y0 : y 0 = 1 / 2 := by linarith
    have y1 : y 1 = 1 / 2 := by linarith
    have l1 := c 0 (by linarith) 1
    have l0 := c 1 (by linarith) 0
    simp at l1 l0
    have x1 : x 1 = 1 / 52 := by linarith
    have x0 : x 0 = 51 / 52 := by linarith
    right; right
    refine ⟨?_, ?_⟩
    · funext a; fin_cases a <;> simp [krepsX, x0, x1]
    · funext b; fin_cases b <;> simp [krepsY, y0, y1, y2, y3]
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · refine ⟨fun a ha a' => ?_, fun b hb b' => ?_⟩
      · fin_cases a <;> fin_cases a' <;> simp [pureMixed] at ha ⊢
      · fin_cases b <;> fin_cases b' <;> simp [pureMixed] at hb ⊢
        norm_num
    · refine ⟨fun a ha a' => ?_, fun b hb b' => ?_⟩
      · fin_cases a <;> fin_cases a' <;> simp [pureMixed] at ha ⊢
      · fin_cases b <;> fin_cases b' <;> simp [pureMixed] at hb ⊢ <;> norm_num
    · refine ⟨fun a ha a' => ?_, fun b hb b' => ?_⟩
      · fin_cases a <;> fin_cases a' <;> simp [krepsY] at ha ⊢
      · fin_cases b <;> fin_cases b' <;> simp [krepsY, krepsX] at hb ⊢ <;> norm_num

/-- **Exercise 8.D.9(c)** (MWG, p. 265). `M` is not played in any Nash equilibrium. -/
theorem exercise_8_D_9c_not_nash {x : Fin 2 → ℝ} {y : Fin 4 → ℝ} (hx : IsMixedStrategy x)
    (hy : IsMixedStrategy y) (h : IsMixedNash kreps (mp x y)) : y 2 = 0 := by
  rcases (exercise_8_D_9b hx hy).1 h with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
    simp [pureMixed, krepsY]

/-- **Exercise 8.D.9(c)** (MWG, p. 265). `M` is a rationalizable strategy (Definition 8.C.2): the
sets `{½U + ½D, (51/52)U + (1/52)D}` and `{M, ½LL + ½L}` are best responses to each other. -/
theorem exercise_8_D_9c_rationalizable : Rationalizable kreps 1 (pureMixed (2 : Fin 4)) := by
  set xh : Fin 2 → ℝ := ![1 / 2, 1 / 2] with hxh
  have hmx : IsMixedStrategy xh :=
    ⟨fun a => by fin_cases a <;> norm_num [xh], by norm_num [xh, Fin.sum_univ_two]⟩
  have hmX : IsMixedStrategy krepsX :=
    ⟨fun a => by fin_cases a <;> norm_num [krepsX], by norm_num [krepsX, Fin.sum_univ_two]⟩
  have hmY : IsMixedStrategy krepsY :=
    ⟨fun b => by fin_cases b <;> norm_num [krepsY], by norm_num [krepsY, Fin.sum_univ_four]⟩
  have hmM : IsMixedStrategy (pureMixed (2 : Fin 4)) := isMixedStrategy_pureMixed _
  set T : (i : Fin 2) → Set (S2 2 4 i → ℝ) :=
    Fin.cons ({xh, krepsX} : Set (Fin 2 → ℝ))
      (Fin.cons ({pureMixed 2, krepsY} : Set (Fin 4 → ℝ)) finZeroElim) with hT
  -- player 1's mixtures are best responses to `½LL + ½L` (both rows give `0`)
  have br1 : ∀ x : Fin 2 → ℝ, IsMixedStrategy x → IsBestResponse kreps 0 x (mp xh krepsY) := by
    intro x hx
    refine (isBestResponse_iff_support kreps 0 (τ := x) hx _).2 ?_
    intro a _ a'
    refine (bimatrix_mixedPayoff_row _ _ _ a').trans_le
      (le_of_le_of_eq ?_ (bimatrix_mixedPayoff_row _ _ _ a).symm)
    simp only [mp_one]
    fin_cases a <;> fin_cases a' <;> simp [Fin.sum_univ_four, krepsU₁, krepsY]
  -- player 2's best replies
  have br2M : IsBestResponse kreps 1 (pureMixed (2 : Fin 4)) (mp xh krepsY) := by
    refine bimatrix_isBestResponse_col _ _ _ (2 : Fin 4) fun b' => ?_
    simp only [mp_zero, kreps_cols]
    fin_cases b' <;> simp [xh] <;> norm_num
  have br2Y : IsBestResponse kreps 1 krepsY (mp krepsX krepsY) := by
    refine (isBestResponse_iff_support kreps 1 (τ := krepsY) hmY _).2 ?_
    intro b hb b'
    refine (bimatrix_mixedPayoff_col _ _ _ b').trans_le
      (le_of_le_of_eq ?_ (bimatrix_mixedPayoff_col _ _ _ b).symm)
    simp only [mp_zero]
    fin_cases b <;> fin_cases b' <;> simp [Fin.sum_univ_two, krepsU₂, krepsY, krepsX] at hb ⊢ <;>
      norm_num
  refine rationalizable_of_bestResponseSet (T := T) (fun i τ hτ => ?_) (fun i τ hτ => ?_) ?_
  · fin_cases i
    · rcases hτ with rfl | rfl
      · exact hmx
      · exact hmX
    · rcases hτ with rfl | rfl
      · exact hmM
      · exact hmY
  · fin_cases i
    · refine ⟨mp xh krepsY, isMixedProfile_mp hmx hmY, fun j hj => ?_, ?_⟩
      · fin_cases j
        · exact absurd rfl hj
        · exact Or.inr rfl
      · rcases hτ with rfl | rfl
        · exact br1 _ hmx
        · exact br1 _ hmX
    · rcases hτ with rfl | rfl
      · refine ⟨mp xh krepsY, isMixedProfile_mp hmx hmY, fun j hj => ?_, br2M⟩
        fin_cases j
        · exact Or.inl rfl
        · exact absurd rfl hj
      · refine ⟨mp krepsX krepsY, isMixedProfile_mp hmX hmY, fun j hj => ?_, br2Y⟩
        fin_cases j
        · exact Or.inr rfl
        · exact absurd rfl hj
  · exact Or.inl rfl

/-- **Exercise 8.D.9(d)** (MWG, p. 265), its mathematical content. Both pure strategy equilibria
give the payoffs `(100, 2)`, while player 2 gets `0` whenever he plays `M`: an agreement on either
pure equilibrium is strictly better for both players than any outcome with `M`. -/
theorem exercise_8_D_9d :
    krepsU₁ 0 0 = 100 ∧ krepsU₂ 0 0 = 2 ∧ krepsU₁ 1 3 = 100 ∧ krepsU₂ 1 3 = 2 ∧
      (∀ a, krepsU₁ a 2 < 100 ∧ krepsU₂ a 2 < 2) := by
  refine ⟨rfl, rfl, rfl, rfl, fun a => ?_⟩
  fin_cases a <;> norm_num [krepsU₁, krepsU₂]

end MWG.SimultaneousMoveGames
