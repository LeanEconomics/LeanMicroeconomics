/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGSimultaneousMoveGames.ExercisesBD

/-!
# Figure 8.F.1 and Exercises 8.C.4 and 8.F.2

MWG, pp. 258-259 and 263-265.

* Figure 8.F.1: `(D, R)` is a Nash equilibrium in which both players play weakly dominated
  strategies, so by Proposition 8.F.2 it is not trembling-hand perfect.
* **Exercise 8.F.2** (van Damme's three-player game): `(D, L, B₁)` and `(U, L, B₁)` are pure Nash
  equilibria, none of `D`, `L`, `B₁` is weakly dominated, yet `(D, L, B₁)` is not
  trembling-hand perfect: against any totally mixed profile near it, `U` does strictly better
  than `D`. So the converse of Proposition 8.F.2 fails with three players.
* **Exercise 8.C.4**: player 1's payoffs in a three-player game. As printed, the entry at
  `(D, ℓ)` for `L` is `η + 4ε`, and then `M` *is* a best response to the pure profile `(D, ℓ)`
  when `π ≥ η/2 + 4ε` (`exercise_8_C_4a_printed_false`); with the entry `π + 4ε` (the symmetric
  table) `M` is never a best response to independent randomizations (`exercise_8_C_4a`) (correction
  8). In both versions `M` is not strictly dominated (`exercise_8_C_4b`) and is a best response to
  a correlated belief (`exercise_8_C_4c`).
-/

namespace MWG.SimultaneousMoveGames

open MWG.NoncooperativeGames Function Finset Filter Topology

/-- A pure strategy weakly dominated by another pure strategy (Definition 8.B.3) is weakly
dominated in the mixed extension. -/
theorem mixedWeaklyDominates_pureMixed {I : Type*} {S : I → Type*} [Fintype I] [DecidableEq I]
    [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] {N : NormalForm I S} {i : I} {a' a : S i}
    (h : WeaklyDominates N i a' a) : MixedWeaklyDominates N i (pureMixed a') (pureMixed a) := by
  rw [mixedWeaklyDominates_iff_pure]
  simp only [mixedPayoff_pureProfile_update]
  obtain ⟨hle, r, hr⟩ := h
  exact ⟨fun s => hle s, r, hr⟩

/-! ### Figure 8.F.1 -/

/-- Player 1's payoffs in Figure 8.F.1 (rows `U, D`, columns `L, R`). -/
def fig8F1U₁ : Fin 2 → Fin 2 → ℝ := ![![1, 0], ![-3, 0]]

/-- Player 2's payoffs in Figure 8.F.1. -/
def fig8F1U₂ : Fin 2 → Fin 2 → ℝ := ![![1, -3], ![0, 0]]

/-- **Figure 8.F.1** (MWG, pp. 258-259). `(D, R)` is a Nash equilibrium in which both players play
weakly dominated strategies (`D` by `U`, `R` by `L`); hence it is not trembling-hand perfect
(Proposition 8.F.2). -/
theorem figure_8_F_1 :
    IsNashEquilibrium (bimatrix fig8F1U₁ fig8F1U₂) (pp (1 : Fin 2) (1 : Fin 2)) ∧
      WeaklyDominates (bimatrix fig8F1U₁ fig8F1U₂) 0 (0 : Fin 2) (1 : Fin 2) ∧
      WeaklyDominates (bimatrix fig8F1U₁ fig8F1U₂) 1 (0 : Fin 2) (1 : Fin 2) ∧
      ¬ IsTHP (bimatrix fig8F1U₁ fig8F1U₂) (pureProfile (pp (1 : Fin 2) (1 : Fin 2))) := by
  have hw0 : WeaklyDominates (bimatrix fig8F1U₁ fig8F1U₂) 0 (0 : Fin 2) (1 : Fin 2) :=
    (bimatrix_weaklyDominates_zero_iff _ _ _ _).2
      ⟨fun b => by fin_cases b <;> norm_num [fig8F1U₁], 0, by norm_num [fig8F1U₁]⟩
  have hw1 : WeaklyDominates (bimatrix fig8F1U₁ fig8F1U₂) 1 (0 : Fin 2) (1 : Fin 2) :=
    (bimatrix_weaklyDominates_one_iff _ _ _ _).2
      ⟨fun a => by fin_cases a <;> norm_num [fig8F1U₂], 0, by norm_num [fig8F1U₂]⟩
  refine ⟨(bimatrix_isNash_iff _ _ _ _).2 ⟨fun a => ?_, fun b => ?_⟩, hw0, hw1, fun h => ?_⟩
  · fin_cases a <;> norm_num [fig8F1U₁]
  · fin_cases b <;> norm_num [fig8F1U₂]
  · exact proposition_8_F_2 _ h 0 ⟨_, isMixedStrategy_pureMixed _,
      mixedWeaklyDominates_pureMixed hw0⟩

/-! ### Exercise 8.F.2 -/

/-- Player 1's payoffs in Exercise 8.F.2, indexed (row, column, box): rows `U, D`, columns
`L, R`, boxes `B₁, B₂`. -/
def vdU₁ : Fin 2 → Fin 2 → Fin 2 → ℝ := ![![![1, 1], ![1, 0]], ![![1, 0], ![0, 1]]]

/-- **Exercise 8.F.2** (MWG, p. 265). Van Damme's three-player game: player 2 gets `1` from `L`,
player 3 gets `1` from `B₁`, and player 1's payoffs are `vdU₁`. -/
def vanDamme : NormalForm (Fin 3) (fun _ => Fin 2) where
  payoff i s := if i = 0 then vdU₁ (s 0) (s 1) (s 2) else if i = 1 then
    (if s 1 = 0 then 1 else 0) else (if s 2 = 0 then 1 else 0)

/-- The pure profile `(a, b, c)`. -/
def p3 (a b c : Fin 2) : Fin 3 → Fin 2 := ![a, b, c]

/-- In a three-player game with two strategies each, the payoff to the pure strategy `a` of
player 1 against the independent mixtures `ρ₂, ρ₃` of the others. -/
theorem mixedPayoff_three (N : NormalForm (Fin 3) (fun _ => Fin 2)) (ρ : (i : Fin 3) → Fin 2 → ℝ)
    (a : Fin 2) (k : Fin 3) :
    N.mixedPayoff (update ρ 0 (pureMixed a)) k =
      ∑ b, ∑ c, ρ 1 b * ρ 2 c * N.payoff k (p3 a b c) := by
  have h10 : (1 : Fin 3) ≠ 0 := by decide
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  conv_lhs => rw [← update_eq_self (1 : Fin 3) (update ρ 0 (pureMixed a)),
    mixedPayoff_update_eq_sum_pure]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [update_of_ne h10]
  set σ := update (update ρ 0 (pureMixed a)) 1 (pureMixed b) with hσ
  have hσ2 : σ 2 = ρ 2 := by rw [hσ, update_of_ne h21, update_of_ne h20]
  conv_lhs => rw [← update_eq_self (2 : Fin 3) σ, mixedPayoff_update_eq_sum_pure]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hpure : update σ 2 (pureMixed c) = pureProfile (p3 a b c) := by
    funext i
    fin_cases i <;> simp [hσ, pureProfile, p3, Function.update]
  rw [hpure, hσ2, mixedPayoff_pureProfile]
  ring

/-- The two pure Nash equilibria of Exercise 8.F.2. -/
theorem exercise_8_F_2_nash :
    IsNashEquilibrium vanDamme (p3 1 0 0) ∧ IsNashEquilibrium vanDamme (p3 0 0 0) := by
  constructor <;> intro i t <;> fin_cases i <;> fin_cases t <;>
    simp [vanDamme, p3, vdU₁, Function.update]

/-- **Exercise 8.F.2** (MWG, p. 265). None of `D` (player 1), `L` (player 2), `B₁` (player 3) is
weakly dominated in the mixed extension. -/
theorem exercise_8_F_2_undominated :
    ¬ MixedWeaklyDominated vanDamme 0 (pureMixed (1 : Fin 2)) ∧
      ¬ MixedWeaklyDominated vanDamme 1 (pureMixed (0 : Fin 2)) ∧
      ¬ MixedWeaklyDominated vanDamme 2 (pureMixed (0 : Fin 2)) := by
  refine ⟨?_, ?_, ?_⟩ <;> rintro ⟨τ, hτ, hdom⟩ <;>
    obtain ⟨hle, s, hs⟩ := (mixedWeaklyDominates_iff_pure _ _ _ _).1 hdom <;>
    simp only [mixedPayoff_pureProfile_update_mixed, Fin.sum_univ_two] at hle hs <;>
    have h2 := hτ.2 <;> rw [Fin.sum_univ_two] at h2
  · -- against `(R, B₂)`, `D` earns `1` and `τ` earns `τ(D)`
    have h := hle (p3 0 1 1)
    simp [vanDamme, p3, vdU₁, pureMixed, Function.update] at h
    have hτD : τ 1 = 1 := by linarith [hτ.1 0]
    have hτU : τ 0 = 0 := by linarith
    have hs' : s = p3 (s 0) (s 1) (s 2) := by funext i; fin_cases i <;> rfl
    rw [hs'] at hs
    generalize s 0 = x at hs
    generalize s 1 = y at hs
    generalize s 2 = z at hs
    fin_cases x <;> fin_cases y <;> fin_cases z <;>
      simp [vanDamme, p3, vdU₁, pureMixed, Function.update, hτD, hτU] at hs
  · simp [vanDamme, pureMixed, Function.update] at hs
    linarith [hτ.1 1]
  · simp [vanDamme, pureMixed, Function.update] at hs
    linarith [hτ.1 1]

/-- **Exercise 8.F.2** (MWG, p. 265). `(D, L, B₁)` is not (normal form) trembling-hand perfect,
although none of its strategies is weakly dominated: against totally mixed profiles near it,
`U` earns `1 - rβ` and `D` earns `(1 - r)(1 - β) + rβ`, where `r = ρ₂(R)`, `β = ρ₃(B₂)`, and
the difference `r + β - 3rβ` is positive once `r, β < 1/3`. -/
theorem exercise_8_F_2 : ¬ IsTHP vanDamme (pureProfile (p3 1 0 0)) := by
  intro h
  obtain ⟨ρ, hρ, hlim, hbr⟩ := (proposition_8_F_1 vanDamme h.1).1 h
  have hr : Tendsto (fun k => ρ k 1 1) atTop (𝓝 0) := by
    have := tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hlim 1) 1
    simpa [pureProfile, p3, pureMixed] using this
  have hβ : Tendsto (fun k => ρ k 2 1) atTop (𝓝 0) := by
    have := tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hlim 2) 1
    simpa [pureProfile, p3, pureMixed] using this
  obtain ⟨k, hk1, hk2⟩ := ((hr.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 3))).and
    (hβ.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 3)))).exists
  have hbrk := (hbr k 0).2 (pureMixed (0 : Fin 2)) (isMixedStrategy_pureMixed _)
  have hσ0 : (pureProfile (p3 1 0 0)) 0 = pureMixed (1 : Fin 2) := rfl
  rw [hσ0, mixedPayoff_three, mixedPayoff_three] at hbrk
  simp only [Fin.sum_univ_two, vanDamme, p3, vdU₁] at hbrk
  simp at hbrk
  have hs1 := (hρ k 1).1.2
  have hs2 := (hρ k 2).1.2
  rw [Fin.sum_univ_two] at hs1 hs2
  have hp1 := (hρ k 1).2 1
  have hp2 := (hρ k 2).2 1
  nlinarith [mul_pos hp1 hp2]

/-! ### Exercise 8.C.4 -/

/-- **Exercise 8.C.4** (MWG, p. 263). Player 1's payoffs `u(a, b, c)` for his strategy
`a ∈ {L, M, R}` (`0, 1, 2`), player 2's `b ∈ {U, D}` and player 3's `c ∈ {ℓ, r}`; the entry for
`L` at `(D, ℓ)` is the parameter `x` (printed `η + 4ε`; `π + 4ε` makes the table symmetric). -/
noncomputable def c4U (π ε η x : ℝ) : Fin 3 → Fin 2 → Fin 2 → ℝ :=
  ![![![π + 4 * ε, π - 4 * ε], ![x, π - 4 * ε]],
    ![![π - η, π + η / 2], ![π + η / 2, π - η]],
    ![![π - 4 * ε, π + 4 * ε], ![π - 4 * ε, π + 4 * ε]]]

/-- Player 1's expected payoff from `a` when player 2 plays `U` with probability `p` and player 3
plays `ℓ` with probability `r`, independently. -/
def c4E (u : Fin 3 → Fin 2 → Fin 2 → ℝ) (p r : ℝ) (a : Fin 3) : ℝ :=
  p * r * u a 0 0 + p * (1 - r) * u a 0 1 + (1 - p) * r * u a 1 0 + (1 - p) * (1 - r) * u a 1 1

/-- **Exercise 8.C.4(a)** (MWG, p. 263), with the symmetric entry `π + 4ε`. If `π, ε, η > 0` and
`η < 4ε`, then `M` is never a best response to independent randomizations of players 2 and 3:
against every pair of mixtures, `L` or `R` does strictly better. -/
theorem exercise_8_C_4a {π ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) (hηε : η < 4 * ε) {p r : ℝ}
    (hp : p ∈ Set.Icc (0 : ℝ) 1) (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    c4E (c4U π ε η (π + 4 * ε)) p r 1 < c4E (c4U π ε η (π + 4 * ε)) p r 0 ∨
      c4E (c4U π ε η (π + 4 * ε)) p r 1 < c4E (c4U π ε η (π + 4 * ε)) p r 2 := by
  simp only [c4E, c4U, Fin.isValue, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.cons_val]
  by_contra hno
  push Not at hno
  obtain ⟨h1, h2⟩ := hno
  obtain ⟨hp0, hp1⟩ := hp
  obtain ⟨hr0, hr1⟩ := hr
  -- `x = pr + (1 - p)(1 - r)` lies between `r` and `1 - r`
  have hx1 : r ≤ 1 / 2 → r ≤ p * r + (1 - p) * (1 - r) := fun h => by nlinarith
  have hx2 : 1 / 2 ≤ r → 1 - r ≤ p * r + (1 - p) * (1 - r) := fun h => by nlinarith
  rcases le_total r (1 / 2) with h | h
  · have := hx1 h
    nlinarith
  · have := hx2 h
    nlinarith

/-- **Exercise 8.C.4(a) as printed is false** (correction 8). With the printed entry `η + 4ε`, e.g.
`π = 10`, `ε = 1`, `η = 1`, the pure strategy `M` is a best response to `(D, ℓ)` (`p = 0`, `r = 1`),
a degenerate independent randomization. -/
theorem exercise_8_C_4a_printed_false :
    ∀ a : Fin 3, c4E (c4U 10 1 1 (1 + 4 * 1)) 0 1 a ≤ c4E (c4U 10 1 1 (1 + 4 * 1)) 0 1 1 := by
  intro a
  fin_cases a <;> simp [c4E, c4U] <;> norm_num

/-- **Exercise 8.C.4(b)** (MWG, p. 263). `M` is not strictly dominated (Proposition 8.B.1): for
every mixed strategy `τ` of player 1, `M` does at least as well as `τ` against `(U, r)` or against
`(D, ℓ)`. This holds for any entry `x ≤ π + 4ε + η`, so for the printed and the symmetric
table. -/
theorem exercise_8_C_4b {π ε η x : ℝ} (hη : 0 ≤ η) (hx : x ≤ π + 4 * ε + η) {τ : Fin 3 → ℝ}
    (hτ : IsMixedStrategy τ) :
    (∑ a, τ a * c4U π ε η x a 0 1 ≤ c4U π ε η x 1 0 1) ∨
      ∑ a, τ a * c4U π ε η x a 1 0 ≤ c4U π ε η x 1 1 0 := by
  have hs : τ 0 + τ 1 + τ 2 = 1 := by simpa [Fin.sum_univ_three] using hτ.2
  simp only [Fin.sum_univ_three, c4U, Fin.isValue, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.cons_val]
  by_contra hno
  push Not at hno
  obtain ⟨h1, h2⟩ := hno
  have h3 := mul_le_mul_of_nonneg_left hx (hτ.1 0)
  have h4 := mul_nonneg (hτ.1 2) hη
  have h5 : τ 0 * (π - 4 * ε) + τ 0 * x ≤ τ 0 * (2 * π + η) := by nlinarith
  have h6 : (τ 0 + τ 1 + τ 2) * (2 * π + η) = 2 * π + η := by rw [hs]; ring
  linarith

/-- **Exercise 8.C.4(c)** (MWG, p. 263). `M` is a best response if players 2 and 3 correlate:
against the belief `½(U, r) + ½(D, ℓ)` it earns `π + η/2`, at least as much as `L` and `R`. -/
theorem exercise_8_C_4c {π ε η x : ℝ} (hη : 0 < η) (hx : x ≤ π + 4 * ε + η) (a : Fin 3) :
    (1 / 2) * c4U π ε η x a 0 1 + (1 / 2) * c4U π ε η x a 1 0 ≤
      (1 / 2) * c4U π ε η x 1 0 1 + (1 / 2) * c4U π ε η x 1 1 0 := by
  fin_cases a <;> simp [c4U] <;> linarith

end MWG.SimultaneousMoveGames
