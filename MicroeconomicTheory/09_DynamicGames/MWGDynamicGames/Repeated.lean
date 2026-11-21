/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGSimultaneousMoveGames.MixedStrategies
import MWGSimultaneousMoveGames.Bimatrix
import MWGSimultaneousMoveGames.Examples8B
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Successive play of simultaneous-move games

MWG, Proposition 9.B.4 (pp. 279-280).

The game `Γ_E` in which the simultaneous-move games `Γᵗ_N = [I, {Δ(Sᵗᵢ)}, {uᵗᵢ}]`,
`t = 0, …, T − 1`, are played in succession, with the pure strategies played in each game
observed before the next, and payoffs summed. A **history** of length `n` is the list of pure
profiles played in periods `0, …, n − 1` (`RHist S n`); a (behaviour) strategy of player `i`
assigns to every history of length `n` a mixed strategy of `Γⁿ_N`. Every history starts a
subgame, and `rval N F i k n h` is player `i`'s expected payoff in the `k` periods following the
history `h` of length `n`. `IsRSPNE` is subgame perfection: at every history of length `n < T`
no player gains by switching to another behaviour strategy.

* `proposition_9_B_4`: if every `Γᵗ_N` has a unique (mixed) Nash equilibrium `σᵗ`, then playing
  `σᵗ` in period `t` regardless of history is an SPNE, and it is the unique SPNE: every SPNE plays
  `σⁿ` after every history of length `n < T`, and gives the payoff `∑_{t ≥ n} uᵗᵢ(σᵗ)`.
* `pd_unique_nash`, `proposition_9_B_4_instance`: the Prisoner's Dilemma (Chapter 8) has the
  unique mixed Nash equilibrium (confess, confess), so in its `T`-fold repetition the unique SPNE
  confesses after every history.

Departure: the model is the direct history-based description of `Γ_E` (subgames are the
histories), not Chapter 7's `ExtensiveForm` tree; no bridge to the tree is built.
-/

namespace MWG.DynamicGames

open MWG.NoncooperativeGames MWG.SimultaneousMoveGames

variable {I : Type*} [Fintype I] [DecidableEq I] {S : ℕ → I → Type*}
  [∀ t i, Fintype (S t i)] [∀ t i, DecidableEq (S t i)]

/-- A history of length `n`: the pure strategy profiles played in periods `0, …, n − 1`. -/
abbrev RHist (S : ℕ → I → Type*) (n : ℕ) := (t : Fin n) → (i : I) → S t i

/-- The history `h` followed by the profile `s` played in period `n`. -/
def rsnoc {n : ℕ} (h : RHist S n) (s : (i : I) → S n i) : RHist S (n + 1) :=
  Fin.snoc (α := fun t : Fin (n + 1) => (i : I) → S t i) h s

/-- **Proposition 9.B.4** (MWG, p. 279). Player `i`'s expected payoff over the `k` periods
following the history `h` of length `n`, when after each history `h'` of length `n'` player `j`
plays the mixed strategy `F j n' h'` of `Γ^{n'}_N`. -/
def rval (N : (t : ℕ) → NormalForm I (S t)) (F : (i : I) → (n : ℕ) → RHist S n → S n i → ℝ)
    (i : I) : ℕ → (n : ℕ) → RHist S n → ℝ
  | 0, _, _ => 0
  | k + 1, n, h => ∑ s : (j : I) → S n j,
      (∏ j, F j n h (s j)) * ((N n).payoff i s + rval N F i k (n + 1) (rsnoc h s))

/-- A behaviour strategy profile of the `T`-period game: a mixed strategy of `Γⁿ_N` after every
history of length `n < T`. -/
def IsRBehavior (T : ℕ) (F : (i : I) → (n : ℕ) → RHist S n → S n i → ℝ) : Prop :=
  ∀ i, ∀ n < T, ∀ h : RHist S n, IsMixedStrategy (F i n h)

/-- **Definition 9.B.2 for successive simultaneous-move games** (MWG, pp. 275 and 279). Every
history of length `n < T` starts a subgame; `F` is subgame perfect if in each of them no player
gains by switching to another behaviour strategy. -/
def IsRSPNE (N : (t : ℕ) → NormalForm I (S t)) (T : ℕ)
    (F : (i : I) → (n : ℕ) → RHist S n → S n i → ℝ) : Prop :=
  IsRBehavior T F ∧ ∀ n < T, ∀ h : RHist S n, ∀ i (g : (n : ℕ) → RHist S n → S n i → ℝ),
    (∀ n' < T, ∀ h', IsMixedStrategy (g n' h')) →
      rval N (Function.update F i g) i (T - n) n h ≤ rval N F i (T - n) n h

omit [∀ t i, DecidableEq (S t i)] in
/-- The payoff in the `k` periods after a history of length `m` depends only on play from
period `m` on. -/
theorem rval_congr (N : (t : ℕ) → NormalForm I (S t))
    {F F' : (i : I) → (n : ℕ) → RHist S n → S n i → ℝ} {m : ℕ}
    (hFF : ∀ j, ∀ n, m ≤ n → F j n = F' j n) (i : I) (k : ℕ) (h : RHist S m) :
    rval N F i k m h = rval N F' i k m h := by
  induction k generalizing m with
  | zero => rfl
  | succ k ih =>
    simp only [rval]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [ih (fun j n hn => hFF j n (by omega)) (rsnoc h s)]
    congr 1
    exact Finset.prod_congr rfl fun j _ => by rw [hFF j m le_rfl]

/-- The mixed profile played after the history `h` of length `n`. -/
def rstage (F : (i : I) → (n : ℕ) → RHist S n → S n i → ℝ) (n : ℕ) (h : RHist S n) :
    (j : I) → S n j → ℝ := fun j => F j n h

omit [Fintype I] [∀ t i, Fintype (S t i)] [∀ t i, DecidableEq (S t i)] in
theorem rstage_update (F : (i : I) → (n : ℕ) → RHist S n → S n i → ℝ) (i : I)
    (g : (n : ℕ) → RHist S n → S n i → ℝ) (n : ℕ) (h : RHist S n) :
    rstage (Function.update F i g) n h = Function.update (rstage F n h) i (g n h) := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp [rstage]
  · simp [rstage, Function.update_of_ne hj]

omit [∀ t i, DecidableEq (S t i)] in
/-- If the continuation payoff after every profile of period `n` is `c`, the payoff from a
history of length `n` is the period-`n` expected payoff plus `c`. -/
theorem rval_succ_of_const (N : (t : ℕ) → NormalForm I (S t))
    (F : (i : I) → (n : ℕ) → RHist S n → S n i → ℝ) (i : I) (k n : ℕ) (h : RHist S n) {c : ℝ}
    (hsum : ∀ j, ∑ a, F j n h a = 1)
    (hc : ∀ s, rval N F i k (n + 1) (rsnoc h s) = c) :
    rval N F i (k + 1) n h = (N n).mixedPayoff (rstage F n h) i + c := by
  simp only [rval, hc, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
    sum_prod_mixed_eq_one hsum, one_mul]
  rfl

omit [∀ t i, DecidableEq (S t i)] in
/-- The step of backward induction: if play after every profile of period `n` gives each
player a fixed continuation payoff, an SPNE plays a Nash equilibrium of `Γⁿ_N` after every
history of length `n`. -/
theorem isMixedNash_rstage_of_isRSPNE {N : (t : ℕ) → NormalForm I (S t)} {T : ℕ}
    {F : (i : I) → (n : ℕ) → RHist S n → S n i → ℝ} (hF : IsRSPNE N T F) {n : ℕ} (hn : n < T)
    (h : RHist S n) {c : I → ℝ}
    (hc : ∀ i s, rval N F i (T - n - 1) (n + 1) (rsnoc h s) = c i) :
    IsMixedNash (N n) (rstage F n h) := by
  refine ⟨fun j => hF.1 j n hn h, fun i τ hτ => ?_⟩
  set g : (n' : ℕ) → RHist S n' → S n' i → ℝ := Function.update (F i) n (fun _ => τ)
  have hg : ∀ n' < T, ∀ h', IsMixedStrategy (g n' h') := by
    intro n' hn' h'
    by_cases hnn : n' = n
    · subst hnn
      simp only [g, Function.update_self]
      exact hτ
    · simp only [g, Function.update_of_ne hnn]
      exact hF.1 i n' hn' h'
  have hdev := hF.2 n hn h i g hg
  have hk : T - n = T - n - 1 + 1 := by omega
  rw [hk] at hdev
  have hlater : ∀ j n', n + 1 ≤ n' → Function.update F i g j n' = F j n' := by
    intro j n' hn'
    by_cases hj : j = i
    · subst hj
      simp only [Function.update_self, g]
      exact Function.update_of_ne (by omega) _ _
    · exact congrFun (Function.update_of_ne hj g F) n'
  have hsum : ∀ (P : (i : I) → (n : ℕ) → RHist S n → S n i → ℝ), IsRBehavior T P →
      ∀ j, ∑ a, P j n h a = 1 := fun P hP j => (hP j n hn h).2
  have hupd : IsRBehavior T (Function.update F i g) := by
    intro j n' hn' h'
    by_cases hj : j = i
    · subst hj
      simp only [Function.update_self]
      exact hg n' hn' h'
    · simp only [Function.update_of_ne hj]
      exact hF.1 j n' hn' h'
  rw [rval_succ_of_const N _ i _ n h (hsum _ hupd) (c := c i) fun s => by
      rw [rval_congr N hlater i _ (rsnoc h s), hc],
    rval_succ_of_const N _ i _ n h (hsum _ hF.1) (c := c i) fun s => hc i s,
    rstage_update] at hdev
  have : g n h = τ := by simp [g]
  rw [this] at hdev
  linarith

omit [∀ t i, DecidableEq (S t i)] in
/-- **Proposition 9.B.4** (MWG, pp. 279-280). Suppose each simultaneous-move game `Γᵗ_N`,
`t < T`, has a unique (mixed) Nash equilibrium `σᵗ`. Then playing `σᵗ` in game `t` regardless of
what has happened previously is a subgame perfect Nash equilibrium of `Γ_E`, and it is the
unique one: every SPNE plays `σⁿ` after every history of length `n < T`, and gives every player
`i` the payoff `∑_{n ≤ t < T} uᵗᵢ(σᵗ)` from every history of length `n`. -/
theorem proposition_9_B_4 (N : (t : ℕ) → NormalForm I (S t)) (T : ℕ)
    (σ : (t : ℕ) → (i : I) → S t i → ℝ)
    (hσ : ∀ t < T, IsMixedNash (N t) (σ t) ∧ ∀ τ, IsMixedNash (N t) τ → τ = σ t) :
    IsRSPNE N T (fun i n _ => σ n i) ∧
    ∀ F, IsRSPNE N T F → (∀ n < T, ∀ h : RHist S n, rstage F n h = σ n) ∧
      ∀ n ≤ T, ∀ (h : RHist S n) i,
        rval N F i (T - n) n h = ∑ t ∈ Finset.Ico n T, (N t).mixedPayoff (σ t) i := by
  have hsplit : ∀ n, n < T → ∀ i, ∑ t ∈ Finset.Ico n T, (N t).mixedPayoff (σ t) i =
      (N n).mixedPayoff (σ n) i + ∑ t ∈ Finset.Ico (n + 1) T, (N t).mixedPayoff (σ t) i :=
    fun n hn i => Finset.sum_eq_sum_Ico_succ_bot hn _
  -- uniqueness
  have huniq : ∀ F, IsRSPNE N T F → (∀ n < T, ∀ h : RHist S n, rstage F n h = σ n) ∧
      ∀ n ≤ T, ∀ (h : RHist S n) i,
        rval N F i (T - n) n h = ∑ t ∈ Finset.Ico n T, (N t).mixedPayoff (σ t) i := by
    intro F hF
    have hval : ∀ k n, n + k = T → ∀ (h : RHist S n) i,
        rval N F i k n h = ∑ t ∈ Finset.Ico n T, (N t).mixedPayoff (σ t) i := by
      intro k
      induction k with
      | zero =>
        intro n hn h i
        obtain rfl : n = T := by omega
        simp [rval]
      | succ k ih =>
        intro n hn h i
        have hnT : n < T := by omega
        have hk : T - n - 1 = k := by omega
        have hc : ∀ i s, rval N F i (T - n - 1) (n + 1) (rsnoc h s) =
            ∑ t ∈ Finset.Ico (n + 1) T, (N t).mixedPayoff (σ t) i := fun i s => by
          rw [hk]; exact ih (n + 1) (by omega) _ i
        have hNE := isMixedNash_rstage_of_isRSPNE hF hnT h hc
        have heq := (hσ n hnT).2 _ hNE
        rw [rval_succ_of_const N F i k n h (fun j => (hF.1 j n hnT h).2) (fun s => by
          rw [← hk]; exact hc i s), heq, hsplit n hnT]
    refine ⟨fun n hn h => ?_, fun n hn h i => hval (T - n) n (by omega) h i⟩
    exact (hσ n hn).2 _ (isMixedNash_rstage_of_isRSPNE hF hn h fun i s =>
      hval (T - n - 1) (n + 1) (by omega) _ i)
  refine ⟨⟨fun i n hn _ => (hσ n hn).1.1 i, fun n hn h i g hg => ?_⟩, huniq⟩
  -- existence: no deviation gains, by induction on the number of remaining periods
  set F : (i : I) → (n : ℕ) → RHist S n → S n i → ℝ := fun i n _ => σ n i
  have key : ∀ k n, n + k ≤ T → ∀ h : RHist S n,
      rval N (Function.update F i g) i k n h ≤
        ∑ t ∈ Finset.Ico n (n + k), (N t).mixedPayoff (σ t) i ∧
      rval N F i k n h = ∑ t ∈ Finset.Ico n (n + k), (N t).mixedPayoff (σ t) i := by
    intro k
    induction k with
    | zero => intro n _ h; simp [rval]
    | succ k ih =>
      intro n hn h
      have hnT : n < T := by omega
      have hs : ∑ t ∈ Finset.Ico n (n + (k + 1)), (N t).mixedPayoff (σ t) i =
          (N n).mixedPayoff (σ n) i + ∑ t ∈ Finset.Ico (n + 1) (n + 1 + k),
            (N t).mixedPayoff (σ t) i := by
        rw [show n + 1 + k = n + (k + 1) by ring]
        exact Finset.sum_eq_sum_Ico_succ_bot (by omega) _
      rw [hs]
      have hsumU : ∀ j, ∑ a, Function.update F i g j n h a = 1 := by
        intro j
        by_cases hj : j = i
        · subst hj; simp only [Function.update_self]; exact (hg n hnT h).2
        · simp only [Function.update_of_ne hj, F]; exact ((hσ n hnT).1.1 j).2
      constructor
      · -- the deviation earns at most the equilibrium payoff in period `n` and after
        have hle : rval N (Function.update F i g) i (k + 1) n h ≤
            (N n).mixedPayoff (rstage (Function.update F i g) n h) i +
              ∑ t ∈ Finset.Ico (n + 1) (n + 1 + k), (N t).mixedPayoff (σ t) i := by
          simp only [rval]
          have hP : ∀ s : (j : I) → S n j, 0 ≤ ∏ j, Function.update F i g j n h (s j) := by
            intro s
            refine Finset.prod_nonneg fun j _ => ?_
            by_cases hj : j = i
            · subst hj; simp only [Function.update_self]; exact (hg n hnT h).1 _
            · simp only [Function.update_of_ne hj, F]; exact ((hσ n hnT).1.1 j).1 _
          calc ∑ s : (j : I) → S n j, (∏ j, Function.update F i g j n h (s j)) *
                ((N n).payoff i s + rval N (Function.update F i g) i k (n + 1) (rsnoc h s))
              ≤ ∑ s : (j : I) → S n j, (∏ j, Function.update F i g j n h (s j)) *
                ((N n).payoff i s + ∑ t ∈ Finset.Ico (n + 1) (n + 1 + k),
                  (N t).mixedPayoff (σ t) i) :=
                Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left
                  (add_le_add le_rfl (ih (n + 1) (by omega) _).1) (hP s)
            _ = _ := by
                simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
                  sum_prod_mixed_eq_one hsumU, one_mul]
                rfl
        refine hle.trans (add_le_add ?_ le_rfl)
        rw [rstage_update]
        have : rstage F n h = σ n := rfl
        rw [this]
        exact (hσ n hnT).1.2 i _ (hg n hnT h)
      · rw [rval_succ_of_const N F i k n h (fun j => ((hσ n hnT).1.1 j).2)
          (fun s => (ih (n + 1) (by omega) _).2)]
        rfl
  have h1 := (key (T - n) n (by omega) h).1
  have h2 := (key (T - n) n (by omega) h).2
  rw [h2]
  exact h1

/-- **Figure 8.B.1** (MWG, p. 237), used in Proposition 9.B.4. The Prisoner's Dilemma has a
unique Nash equilibrium, pure or mixed: both prisoners confess (`1`), a strictly dominant
strategy. -/
theorem pd_unique_nash :
    IsMixedNash (bimatrix pdU₁ pdU₂) (pureProfile (pp (1 : Fin 2) (1 : Fin 2))) ∧
    ∀ τ, IsMixedNash (bimatrix pdU₁ pdU₂) τ → τ = pureProfile (pp (1 : Fin 2) (1 : Fin 2)) := by
  refine ⟨(corollary_8_D_1 _ _).1 ((bimatrix_isNash_iff _ _ _ _).2
    ⟨fun a' => by fin_cases a' <;> norm_num [pdU₁], fun b' => by fin_cases b' <;> norm_num [pdU₂]⟩),
    fun τ hτ => ?_⟩
  set x : Fin 2 → ℝ := τ 0 with hxdef
  set y : Fin 2 → ℝ := τ 1 with hydef
  have hx : IsMixedStrategy x := hτ.1 0
  have hy : IsMixedStrategy y := hτ.1 1
  have hτ' : IsMixedNash (bimatrix pdU₁ pdU₂) (mp x y) := (eq_mp τ) ▸ hτ
  obtain ⟨h1, h2⟩ := (bimatrix_isMixedNash_support _ _ hx hy).1 hτ'
  have hx2 : x 0 + x 1 = 1 := by simpa [Fin.sum_univ_two] using hx.2
  have hy2 : y 0 + y 1 = 1 := by simpa [Fin.sum_univ_two] using hy.2
  have hx0 : x 0 = 0 := by
    by_contra hne
    have := h1 0 (lt_of_le_of_ne (hx.1 0) (Ne.symm hne)) 1
    simp only [Fin.sum_univ_two, pdU₁] at this
    norm_num at this
    linarith [hy.1 0, hy.1 1]
  have hy0 : y 0 = 0 := by
    by_contra hne
    have := h2 0 (lt_of_le_of_ne (hy.1 0) (Ne.symm hne)) 1
    simp only [Fin.sum_univ_two, pdU₂] at this
    norm_num at this
    linarith [hx.1 0, hx.1 1]
  have hx1 : x 1 = 1 := by linarith
  have hy1 : y 1 = 1 := by linarith
  have ex : x = pureMixed (1 : Fin 2) := by
    funext a; fin_cases a <;> simp [pureMixed, hx0, hx1]
  have ey : y = pureMixed (1 : Fin 2) := by
    funext a; fin_cases a <;> simp [pureMixed, hy0, hy1]
  rw [eq_mp τ, eq_mp (pureProfile (pp (1 : Fin 2) (1 : Fin 2)))]
  change mp x y = mp (pureMixed (1 : Fin 2)) (pureMixed (1 : Fin 2))
  rw [ex, ey]

/-- **Proposition 9.B.4, an instance** (MWG, p. 279). In the `T`-fold repetition of the
Prisoner's Dilemma, confessing after every history is the unique subgame perfect Nash
equilibrium. -/
theorem proposition_9_B_4_instance (T : ℕ) :
    IsRSPNE (S := fun _ => S2 2 2) (fun _ => bimatrix pdU₁ pdU₂) T
      (fun i _ _ => pureProfile (pp (1 : Fin 2) (1 : Fin 2)) i) ∧
    ∀ F, IsRSPNE (S := fun _ => S2 2 2) (fun _ => bimatrix pdU₁ pdU₂) T F →
      ∀ n < T, ∀ h, rstage F n h = pureProfile (pp (1 : Fin 2) (1 : Fin 2)) := by
  obtain ⟨hE, hU⟩ := proposition_9_B_4 (S := fun _ => S2 2 2) (fun _ => bimatrix pdU₁ pdU₂) T
    (fun _ => pureProfile (pp (1 : Fin 2) (1 : Fin 2))) fun _ _ => pd_unique_nash
  exact ⟨hE, fun F hF => (hU F hF).1⟩

end MWG.DynamicGames
