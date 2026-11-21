/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGDynamicGames.Repeated

/-!
# A simultaneous-move game played twice

MWG, Exercise 9.B.9 (p. 302) and footnote 10 (p. 280), in the history model of
Proposition 9.B.4 (`MWGDynamicGames/Repeated.lean`).

* `augGame`, `isRSPNE_two_iff`: generalized backward induction for two periods. A behaviour
  profile `F` of the twice-played game is subgame perfect iff after every first-period profile
  it plays a (mixed) Nash equilibrium of `Γ¹_N`, and in the first period it plays a Nash
  equilibrium of `Γ⁰_N` augmented by the second-period equilibrium payoffs.
* `rpure`, `isRSPNE_two_pure_iff`: the same for pure strategy profiles.
* Exercise 9.B.9: the stage game has the pure Nash equilibria `(a₂, b₂)` and `(a₃, b₃)` only
  (`tw_nash_iff`). `exercise_9_B_9`: a pure profile is a pure SPNE iff after every first-period
  outcome it plays `(a₂, b₂)` or `(a₃, b₃)`, and no player gains by deviating in the first period
  given the second-period play this triggers. `exercise_9_B_9_first`: a first-period profile is
  played in some pure SPNE iff it is not `(a₂, b₃)` or `(a₃, b₂)` (a first-period deviation can
  be punished by at most `5 − 1 = 4`). `footnote_10`: ((a₁, b₁), then (a₂, b₂) after (a₁, b₁)
  and (a₃, b₃) otherwise) is a pure SPNE — history dependence with multiple stage equilibria.

Actions are numbered from `0`: `aₖ` and `bₖ` are `k − 1`.
-/

namespace MWG.DynamicGames

open MWG.NoncooperativeGames MWG.SimultaneousMoveGames

variable {I : Type*} [Fintype I] [DecidableEq I] {S : ℕ → I → Type*}
  [∀ t i, Fintype (S t i)] [∀ t i, DecidableEq (S t i)]

omit [∀ t i, DecidableEq (S t i)] in
/-- The payoff in the one period after a history is the stage game's mixed payoff. -/
theorem rval_one (N : (t : ℕ) → NormalForm I (S t))
    (F : (i : I) → (n : ℕ) → RHist S n → S n i → ℝ) (i : I) (n : ℕ) (h : RHist S n) :
    rval N F i 1 n h = (N n).mixedPayoff (rstage F n h) i := by
  simp only [rval, add_zero]
  rfl

/-- **Generalized backward induction, two periods** (MWG, pp. 277-280). The first-period game
`Γ⁰_N` with payoffs augmented by the second-period payoffs that `F` prescribes after each
first-period profile. -/
def augGame (N : (t : ℕ) → NormalForm I (S t)) (F : (i : I) → (n : ℕ) → RHist S n → S n i → ℝ)
    (h0 : RHist S 0) : NormalForm I (S 0) where
  payoff i s := (N 0).payoff i s + (N 1).mixedPayoff (rstage F 1 (rsnoc h0 s)) i

omit [∀ t i, DecidableEq (S t i)] in
/-- The payoff of the twice-played game is the augmented first-period game's mixed payoff. -/
theorem rval_two (N : (t : ℕ) → NormalForm I (S t))
    (F : (i : I) → (n : ℕ) → RHist S n → S n i → ℝ) (i : I) (h0 : RHist S 0) :
    rval N F i 2 0 h0 = (augGame N F h0).mixedPayoff (rstage F 0 h0) i := by
  simp only [rval, add_zero]
  rfl

omit [∀ t i, DecidableEq (S t i)] in
/-- **Generalized backward induction, two periods** (MWG, pp. 277-280). A behaviour profile `F`
of the game in which `Γ⁰_N` and then `Γ¹_N` are played (with the first-period profile observed)
is a subgame perfect Nash equilibrium iff after every first-period profile it plays a Nash
equilibrium of `Γ¹_N`, and in the first period it plays a Nash equilibrium of the augmented
game `augGame N F`. -/
theorem isRSPNE_two_iff (N : (t : ℕ) → NormalForm I (S t))
    (F : (i : I) → (n : ℕ) → RHist S n → S n i → ℝ) :
    IsRSPNE N 2 F ↔ IsRBehavior 2 F ∧ (∀ h : RHist S 1, IsMixedNash (N 1) (rstage F 1 h)) ∧
      ∀ h0 : RHist S 0, IsMixedNash (augGame N F h0) (rstage F 0 h0) := by
  constructor
  · intro hF
    refine ⟨hF.1, fun h => isMixedNash_rstage_of_isRSPNE hF (by norm_num) h (c := fun _ => 0)
      (fun _ _ => rfl), fun h0 => ⟨fun j => hF.1 j 0 (by norm_num) h0, fun i τ hτ => ?_⟩⟩
    set g : (n : ℕ) → RHist S n → S n i → ℝ := Function.update (F i) 0 (fun _ => τ) with hgd
    have hg : ∀ n' < 2, ∀ h', IsMixedStrategy (g n' h') := by
      intro n' hn' h'
      by_cases hnn : n' = 0
      · subst hnn
        simp only [g, Function.update_self]
        exact hτ
      · simp only [g, Function.update_of_ne hnn]
        exact hF.1 i n' hn' h'
    have hdev := hF.2 0 (by norm_num) h0 i g hg
    have h1 : ∀ h' : RHist S 1, rstage (Function.update F i g) 1 h' = rstage F 1 h' := by
      intro h'
      have hg1 : g 1 h' = rstage F 1 h' i := by
        simp only [g, Function.update_of_ne (by norm_num : (1 : ℕ) ≠ 0)]
        rfl
      rw [rstage_update, hg1, Function.update_eq_self]
    have haug : augGame N (Function.update F i g) h0 = augGame N F h0 := by
      simp only [augGame, h1]
    have hg0 : g 0 h0 = τ := by simp [g]
    rw [Nat.sub_zero, rval_two, rval_two, haug, rstage_update, hg0] at hdev
    exact hdev
  · rintro ⟨hB, h1, h0⟩
    refine ⟨hB, fun n hn h i g hg => ?_⟩
    have hupd : IsRBehavior 2 (Function.update F i g) := by
      intro j n' hn' h'
      by_cases hj : j = i
      · subst hj
        simp only [Function.update_self]
        exact hg n' hn' h'
      · simp only [Function.update_of_ne hj]
        exact hB j n' hn' h'
    rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl
    · rw [Nat.sub_zero, rval_two, rval_two]
      calc (augGame N (Function.update F i g) h).mixedPayoff
            (rstage (Function.update F i g) 0 h) i
          ≤ (augGame N F h).mixedPayoff (rstage (Function.update F i g) 0 h) i := by
            unfold NormalForm.mixedPayoff
            refine Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left ?_
              (Finset.prod_nonneg fun j _ => (hupd j 0 (by norm_num) h).1 _)
            simp only [augGame]
            rw [rstage_update]
            exact add_le_add le_rfl ((h1 _).2 i _ (hg 1 (by norm_num) _))
        _ ≤ _ := by
            rw [rstage_update]
            exact (h0 h).2 i _ (hg 0 (by norm_num) h)
    · rw [show 2 - 1 = 1 from rfl, rval_one, rval_one, rstage_update]
      exact (h1 h).2 i _ (hg 1 (by norm_num) h)

/-- A pure strategy profile of the successive game: after the history `h` of length `n` the
players play the pure profile `p n h`. -/
def rpure (p : (n : ℕ) → RHist S n → (i : I) → S n i) :
    (i : I) → (n : ℕ) → RHist S n → S n i → ℝ :=
  fun i n h => pureMixed (p n h i)

/-- **Generalized backward induction, two periods, pure strategies** (MWG, pp. 277-280). A pure
profile `p` is a subgame perfect Nash equilibrium of the twice-played game iff after every
first-period profile it plays a pure Nash equilibrium of `Γ¹_N`, and no player gains by a
unilateral first-period deviation, given the second-period play that the deviation
triggers. -/
theorem isRSPNE_two_pure_iff (N : (t : ℕ) → NormalForm I (S t))
    (p : (n : ℕ) → RHist S n → (i : I) → S n i) :
    IsRSPNE N 2 (rpure p) ↔ (∀ h : RHist S 1, IsNashEquilibrium (N 1) (p 1 h)) ∧
      ∀ (h0 : RHist S 0) (i : I) (t : S 0 i),
        (N 0).payoff i (Function.update (p 0 h0) i t) +
            (N 1).payoff i (p 1 (rsnoc h0 (Function.update (p 0 h0) i t))) ≤
          (N 0).payoff i (p 0 h0) + (N 1).payoff i (p 1 (rsnoc h0 (p 0 h0))) := by
  have hst : ∀ n (h : RHist S n), rstage (rpure p) n h = pureProfile (p n h) := fun _ _ => rfl
  have hB : IsRBehavior 2 (rpure p) := fun i n _ h => isMixedStrategy_pureMixed (p n h i)
  rw [isRSPNE_two_iff]
  simp only [hst, ← corollary_8_D_1, hB, true_and]
  refine and_congr Iff.rfl (forall_congr' fun h0 => ?_)
  simp only [IsNashEquilibrium, augGame, hst, mixedPayoff_pureProfile]

/-- Player 1's payoffs in the game of Exercise 9.B.9 (rows `a₁, a₂, a₃`, columns
`b₁, b₂, b₃`). -/
def twU₁ : Fin 3 → Fin 3 → ℝ := ![![10, 2, 0], ![12, 5, 0], ![13, 0, 1]]

/-- Player 2's payoffs in the game of Exercise 9.B.9. -/
def twU₂ : Fin 3 → Fin 3 → ℝ := ![![10, 12, 13], ![2, 5, 0], ![0, 0, 1]]

/-- The stage game of Exercise 9.B.9 in every period. -/
abbrev twS : ℕ → Fin 2 → Type := fun _ => S2 3 3

/-- **Exercise 9.B.9** (MWG, p. 302). The stage game has exactly two pure Nash equilibria,
`(a₂, b₂)` and `(a₃, b₃)`. -/
theorem tw_nash_iff (a b : Fin 3) :
    IsNashEquilibrium (bimatrix twU₁ twU₂) (pp a b) ↔ (a = 1 ∧ b = 1) ∨ (a = 2 ∧ b = 2) := by
  rw [bimatrix_isNash_iff]
  fin_cases a <;> fin_cases b <;> simp [Fin.forall_fin_succ, twU₁, twU₂] <;> norm_num

theorem pp_inj {m n : ℕ} (a a' : Fin m) (b b' : Fin n) : pp a b = pp a' b' ↔ a = a' ∧ b = b' :=
  ⟨fun h => ⟨congrFun h 0, congrFun h 1⟩, by rintro ⟨rfl, rfl⟩; rfl⟩

theorem tw_nash_iff' (s : (i : Fin 2) → S2 3 3 i) :
    IsNashEquilibrium (bimatrix twU₁ twU₂) s ↔ s = pp 1 1 ∨ s = pp 2 2 := by
  obtain ⟨a, b, rfl⟩ : ∃ a b : Fin 3, s = pp a b := ⟨s 0, s 1, eq_pp s⟩
  rw [tw_nash_iff, pp_inj, pp_inj]

/-- **Exercise 9.B.9** (MWG, p. 302). The pure strategy subgame perfect Nash equilibria of the
twice-played game: a pure profile `p` is an SPNE iff after every first-period outcome the
players play `(a₂, b₂)` or `(a₃, b₃)`, and no player gains by deviating in the first period,
given the second-period play that the deviation triggers. -/
theorem exercise_9_B_9 (p : (n : ℕ) → RHist twS n → (i : Fin 2) → S2 3 3 i) :
    IsRSPNE (S := twS) (fun _ => bimatrix twU₁ twU₂) 2 (rpure p) ↔
      (∀ h : RHist twS 1, p 1 h = pp 1 1 ∨ p 1 h = pp 2 2) ∧
      ∀ (h0 : RHist twS 0) (i : Fin 2) (t : S2 3 3 i),
        (bimatrix twU₁ twU₂).payoff i (Function.update (p 0 h0) i t) +
            (bimatrix twU₁ twU₂).payoff i (p 1 (rsnoc h0 (Function.update (p 0 h0) i t))) ≤
          (bimatrix twU₁ twU₂).payoff i (p 0 h0) +
            (bimatrix twU₁ twU₂).payoff i (p 1 (rsnoc h0 (p 0 h0))) := by
  rw [isRSPNE_two_pure_iff]
  simp only [tw_nash_iff']

/-- The pure profile of the existence part of Exercise 9.B.9: play `(a, b)` in the first period;
then `(a₂, b₂)` if `(a, b)` was played and `(a₃, b₃)` otherwise. -/
def twProfile (a b : Fin 3) : (n : ℕ) → RHist twS n → (i : Fin 2) → S2 3 3 i :=
  fun n h => if hn : 0 < n then (if h ⟨0, hn⟩ = pp a b then pp 1 1 else pp 2 2) else pp a b

theorem rsnoc_zero (h0 : RHist twS 0) (s : (i : Fin 2) → S2 3 3 i) :
    rsnoc h0 s ⟨0, Nat.one_pos⟩ = s := by
  simp [rsnoc, Fin.snoc]

theorem tw_payoff_cont (s : (i : Fin 2) → S2 3 3 i) (hs : s = pp 1 1 ∨ s = pp 2 2) (i : Fin 2) :
    1 ≤ (bimatrix twU₁ twU₂).payoff i s ∧ (bimatrix twU₁ twU₂).payoff i s ≤ 5 := by
  rcases hs with rfl | rfl <;> fin_cases i <;> norm_num [twU₁, twU₂]

/-- **Exercise 9.B.9, existence** (MWG, p. 302). If `(a, b)` is neither `(a₂, b₃)` nor
`(a₃, b₂)`, playing `(a, b)` and then `(a₂, b₂)` after `(a, b)` and `(a₃, b₃)` otherwise is a pure
strategy SPNE. -/
theorem twProfile_isRSPNE (a b : Fin 3) (hn1 : ¬ (a = 1 ∧ b = 2)) (hn2 : ¬ (a = 2 ∧ b = 1)) :
    IsRSPNE (S := twS) (fun _ => bimatrix twU₁ twU₂) 2 (rpure (twProfile a b)) := by
  refine (exercise_9_B_9 _).2 ⟨fun h => ?_, fun h0 i t => ?_⟩
  · simp only [twProfile, Nat.one_pos, ↓reduceDIte]
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  · have hp0 : twProfile a b 0 h0 = pp a b := by simp [twProfile]
    have hq : ∀ s, twProfile a b 1 (rsnoc h0 s) = if s = pp a b then pp 1 1 else pp 2 2 := by
      intro s
      simp only [twProfile, Nat.one_pos, ↓reduceDIte, rsnoc_zero]
    rw [hp0, hq, hq]
    simp only [↓reduceIte]
    have hgain0 : ∀ t : Fin 3, twU₁ t b ≤ twU₁ a b + 4 := by
      intro t
      fin_cases a <;> fin_cases b <;> fin_cases t <;> simp_all [twU₁] <;> norm_num
    have hgain1 : ∀ t : Fin 3, twU₂ a t ≤ twU₂ a b + 4 := by
      intro t
      fin_cases a <;> fin_cases b <;> fin_cases t <;> simp_all [twU₂] <;> norm_num
    rcases (by decide : ∀ k : Fin 2, k = 0 ∨ k = 1) i with rfl | rfl
    · simp only [Function.update_eq_self_iff, pp_zero, pp_one, bimatrix_payoff_zero]
      split_ifs with ht
      · rw [ht]
        exact le_rfl
      · have := hgain0 t
        norm_num [twU₁] at this ⊢
        linarith
    · simp only [Function.update_eq_self_iff, pp_zero, pp_one, bimatrix_payoff_one]
      split_ifs with ht
      · rw [ht]
        exact le_rfl
      · have := hgain1 t
        norm_num [twU₂] at this ⊢
        linarith

/-- **Exercise 9.B.9** (MWG, p. 302). A first-period profile `(a, b)` is played in some pure
strategy SPNE iff it is neither `(a₂, b₃)` nor `(a₃, b₂)`: every other first-period profile
leaves each player a deviation gain of at most `4 = 5 − 1`, which the switch from `(a₂, b₂)` to
`(a₃, b₃)` in the second period deters; at `(a₂, b₃)` player 2 gains `5`, at `(a₃, b₂)`
player 1 gains `5`. -/
theorem exercise_9_B_9_first (a b : Fin 3) :
    (∃ p : (n : ℕ) → RHist twS n → (i : Fin 2) → S2 3 3 i,
        IsRSPNE (S := twS) (fun _ => bimatrix twU₁ twU₂) 2 (rpure p) ∧
        ∀ h0 : RHist twS 0, p 0 h0 = pp a b) ↔
      ¬ (a = 1 ∧ b = 2) ∧ ¬ (a = 2 ∧ b = 1) := by
  constructor
  · rintro ⟨p, hp, hab⟩
    obtain ⟨h1, h0⟩ := (exercise_9_B_9 p).1 hp
    set e : RHist twS 0 := fun t => absurd t.2 (Nat.not_lt_zero _)
    have hdev0 : ∀ t : Fin 3, twU₁ t b ≤ twU₁ a b + 4 := by
      intro t
      have := h0 e 0 t
      have c1 := tw_payoff_cont _ (h1 (rsnoc e (Function.update (p 0 e) 0 t))) 0
      have c2 := tw_payoff_cont _ (h1 (rsnoc e (p 0 e))) 0
      rw [hab e] at this
      simp only [bimatrix_update_zero, bimatrix_payoff_zero, pp_zero, pp_one] at this
      simp only [bimatrix_payoff_zero] at c1 c2
      rw [hab e] at c1 c2
      simp only [↓reduceIte] at this
      linarith
    have hdev1 : ∀ t : Fin 3, twU₂ a t ≤ twU₂ a b + 4 := by
      intro t
      have := h0 e 1 t
      have c1 := tw_payoff_cont _ (h1 (rsnoc e (Function.update (p 0 e) 1 t))) 1
      have c2 := tw_payoff_cont _ (h1 (rsnoc e (p 0 e))) 1
      rw [hab e] at this
      simp only [bimatrix_update_one, bimatrix_payoff_one, pp_zero, pp_one] at this
      simp only [bimatrix_payoff_one] at c1 c2
      rw [hab e] at c1 c2
      simp only [Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, ↓reduceIte] at this
      linarith
    refine ⟨?_, ?_⟩
    · rintro ⟨rfl, rfl⟩
      have := hdev1 1
      norm_num [twU₂] at this
    · rintro ⟨rfl, rfl⟩
      have := hdev0 1
      norm_num [twU₁] at this
  · rintro ⟨hn1, hn2⟩
    exact ⟨twProfile a b, twProfile_isRSPNE a b hn1 hn2, fun h0 => by simp [twProfile]⟩

/-- **Footnote 10** (MWG, p. 280). With multiple stage equilibria the SPNE play can depend on
history: in the game of Exercise 9.B.9, playing `(a₁, b₁)` in the first period, then `(a₂, b₂)`
if `(a₁, b₁)` was played and `(a₃, b₃)` otherwise, is a pure strategy SPNE (although
`(a₁, b₁)` is not a Nash equilibrium of the stage game). -/
theorem footnote_10 :
    IsRSPNE (S := twS) (fun _ => bimatrix twU₁ twU₂) 2 (rpure (twProfile 0 0)) ∧
      ¬ IsNashEquilibrium (bimatrix twU₁ twU₂) (pp 0 0) := by
  refine ⟨twProfile_isRSPNE 0 0 (by decide) (by decide), fun h => ?_⟩
  rcases (tw_nash_iff 0 0).1 h with ⟨h0, -⟩ | ⟨h0, -⟩ <;> exact absurd h0 (by decide)

end MWG.DynamicGames
